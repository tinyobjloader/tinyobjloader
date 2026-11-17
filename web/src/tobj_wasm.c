/*
 * tobj_wasm.c -- C ABI shim exposing tiny_obj_c to WebAssembly.
 *
 * Flattens a parsed scene into non-indexed interleaved triangle corners
 * (TOBJ_W_STRIDE floats each: x y z nx ny nz u v), ordered into contiguous
 * per-material runs so JavaScript can build draw groups without any per-face
 * work. No embind, no C++: plain exported C functions and heap views.
 *
 * SPDX-License-Identifier: MIT
 */
#include "tobj_wasm.h"

#include "tiny_obj_c.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

#ifndef TOBJ_W_MESSAGE_CAP
#define TOBJ_W_MESSAGE_CAP 4096
#endif

typedef struct tobjw_group {
  uint32_t material; /* TOBJ_W_MATERIAL_NONE when absent or out of range */
  uint32_t start;    /* first triangle within the shape */
  uint32_t count;    /* number of triangles */
} tobjw_group;

typedef struct tobjw_shape_out {
  float *vertices;
  uint32_t vert_count;
  uint32_t tri_count;
  tobjw_group *groups;
  uint32_t group_count;
  const char *name; /* interned in the scene arena; valid until destroy */
} tobjw_shape_out;

typedef struct tobjw_model {
  tobj_scene_f scene;
  tobjw_shape_out *shapes;
  int num_shapes;
  int num_materials;
} tobjw_model;

static tobjw_model **tobjw_models;
static int tobjw_num_handles;
static int tobjw_cap_handles;

static char tobjw_message[TOBJ_W_MESSAGE_CAP];
static size_t tobjw_message_len;

/* ------------------------------------------------------------------------- */
/* Diagnostics                                                               */
/* ------------------------------------------------------------------------- */

static void tobjw_msg_reset(void) {
  tobjw_message_len = 0;
  tobjw_message[0] = '\0';
}

static void tobjw_msg_append(const char *s, size_t n) {
  size_t left = sizeof tobjw_message - 1u - tobjw_message_len;
  if (left == 0 || n == 0) return;
  if (n > left) n = left;
  memcpy(tobjw_message + tobjw_message_len, s, n);
  tobjw_message_len += n;
  tobjw_message[tobjw_message_len] = '\0';
}

static void tobjw_msg_append_size(size_t v) {
  char buf[24];
  size_t n = 0;
  if (v == 0) {
    tobjw_msg_append("0", 1);
    return;
  }
  while (v) {
    buf[n++] = (char)('0' + (int)(v % 10u));
    v /= 10u;
  }
  for (size_t i = 0; i < n / 2; i++) {
    char t = buf[i];
    buf[i] = buf[n - 1 - i];
    buf[n - 1 - i] = t;
  }
  tobjw_msg_append(buf, n);
}

static void tobjw_on_message(void *ud, tobj_severity sev, size_t line_no,
                             const char *msg, size_t msg_len) {
  (void)ud;
  if (sev == TOBJ_SEV_ERROR) {
    tobjw_msg_append("error: ", 7);
  } else {
    tobjw_msg_append("warning: ", 9);
  }
  if (line_no) {
    tobjw_msg_append("line ", 5);
    tobjw_msg_append_size(line_no);
    tobjw_msg_append(": ", 2);
  }
  tobjw_msg_append(msg ? msg : "", msg ? msg_len : 0);
  if (tobjw_message_len && tobjw_message[tobjw_message_len - 1] != '\n')
    tobjw_msg_append("\n", 1);
}

/* ------------------------------------------------------------------------- */
/* .mtl resolver                                                             */
/* ------------------------------------------------------------------------- */

static size_t tobjw_basename_off(const char *p) {
  size_t off = 0;
  for (size_t i = 0; p && p[i]; i++)
    if (p[i] == '/' || p[i] == '\\') off = i + 1u;
  return off;
}

static int tobjw_eq_ci(const char *a, const char *b) {
  for (size_t i = 0;; i++) {
    unsigned char ca = (unsigned char)a[i];
    unsigned char cb = (unsigned char)b[i];
    if (ca >= 'A' && ca <= 'Z') ca = (unsigned char)(ca - 'A' + 'a');
    if (cb >= 'A' && cb <= 'Z') cb = (unsigned char)(cb - 'A' + 'a');
    if (ca != cb) return 0;
    if (!ca) return 1;
  }
}

/* Resolver state: the single .mtl blob handed in from JavaScript. */
typedef struct tobjw_mtl_slot {
  const uint8_t *data;
  size_t len;
  const char *want; /* basename to match; NULL/"" accepts any mtllib */
} tobjw_mtl_slot;

static tobj_result tobjw_mtl_resolver(void *ud, const char *mtllib_name,
                                      tobj_mtl_source *out) {
  const tobjw_mtl_slot *slot = (const tobjw_mtl_slot *)ud;
  if (!slot || !slot->data) return TOBJ_ERR_NOT_FOUND;
  if (slot->want && slot->want[0]) {
    const char *got =
        mtllib_name ? mtllib_name + tobjw_basename_off(mtllib_name) : "";
    if (!tobjw_eq_ci(got, slot->want)) return TOBJ_ERR_NOT_FOUND;
  }
  out->data = slot->data;
  out->len = slot->len;
  out->release = NULL;
  out->release_ud = NULL;
  return TOBJ_OK;
}

/* ------------------------------------------------------------------------- */
/* Scene -> interleaved corners                                              */
/* ------------------------------------------------------------------------- */

static void tobjw_face_normal(const float *v0, const float *v1, const float *v2,
                              float out[3]) {
  float u[3], w[3];
  for (int i = 0; i < 3; i++) {
    u[i] = v1[i] - v0[i];
    w[i] = v2[i] - v0[i];
  }
  out[0] = u[1] * w[2] - u[2] * w[1];
  out[1] = u[2] * w[0] - u[0] * w[2];
  out[2] = u[0] * w[1] - u[1] * w[0];
  const float len2 = out[0] * out[0] + out[1] * out[1] + out[2] * out[2];
  if (len2 > 0.0f) {
    const float inv = 1.0f / sqrtf(len2);
    out[0] *= inv;
    out[1] *= inv;
    out[2] *= inv;
  }
}

static int tobjw_copy_buf(const tobj_real_buf_f *buf, size_t first, size_t n,
                          float *dst) {
  if (!buf->ptr || first + n > buf->count) return 0;
  for (size_t i = 0; i < n; i++) dst[i] = buf->ptr[first + i];
  return 1;
}

/* Writes one triangle (three corners) at `corner_base`. */
static void tobjw_emit_tri(const tobj_attrib_f *attrib, const tobj_mesh_f *mesh,
                           size_t face, float *corner_base) {
  const tobj_index *idx = &mesh->indices[3u * face];
  int have_normal = 1;

  for (int k = 0; k < 3; k++) {
    float *corner = corner_base + (size_t)k * TOBJ_W_STRIDE;
    corner[0] = corner[1] = corner[2] = 0.0f;
    corner[3] = corner[4] = corner[5] = 0.0f;
    corner[6] = corner[7] = 0.0f;

    if (idx[k].vertex_index >= 0)
      tobjw_copy_buf(&attrib->vertices, 3u * (size_t)idx[k].vertex_index, 3u,
                     corner);
    if (idx[k].normal_index >= 0) {
      if (!tobjw_copy_buf(&attrib->normals, 3u * (size_t)idx[k].normal_index,
                          3u, &corner[3]))
        have_normal = 0;
    } else {
      have_normal = 0;
    }
    if (idx[k].texcoord_index >= 0 &&
        tobjw_copy_buf(&attrib->texcoords, 2u * (size_t)idx[k].texcoord_index,
                       2u, &corner[6]))
      corner[7] = 1.0f - corner[7]; /* flip V, as the native viewer does */
  }

  if (!have_normal) {
    float fn[3];
    tobjw_face_normal(&corner_base[0], &corner_base[TOBJ_W_STRIDE],
                      &corner_base[2 * TOBJ_W_STRIDE], fn);
    for (int k = 0; k < 3; k++) {
      float *corner = corner_base + (size_t)k * TOBJ_W_STRIDE;
      corner[3] = fn[0];
      corner[4] = fn[1];
      corner[5] = fn[2];
    }
  }
}

static tobj_result tobjw_emit_shape(const tobj_scene_f *scene,
                                    const tobj_shape_f *shape,
                                    int num_materials, tobjw_shape_out *out) {
  const tobj_mesh_f *mesh = &shape->mesh;
  const size_t num_faces = mesh->num_faces;
  const uint32_t num_buckets = (uint32_t)num_materials + 2u;
  uint32_t *tri_bucket = NULL;
  uint32_t *tri_face = NULL;
  uint32_t *bucket_start = NULL;
  uint32_t *bucket_fill = NULL;
  uint32_t ntris = 0;
  tobj_result r = TOBJ_OK;

  out->vertices = NULL;
  out->vert_count = 0;
  out->tri_count = 0;
  out->groups = NULL;
  out->group_count = 0;
  out->name = shape->name ? shape->name : "";

  if (num_faces == 0) return TOBJ_OK;

  tri_bucket = (uint32_t *)malloc(num_faces * sizeof *tri_bucket);
  tri_face = (uint32_t *)malloc(num_faces * sizeof *tri_face);
  bucket_start = (uint32_t *)malloc(num_buckets * sizeof *bucket_start);
  bucket_fill = (uint32_t *)malloc(num_buckets * sizeof *bucket_fill);
  if (!tri_bucket || !tri_face || !bucket_start || !bucket_fill) {
    r = TOBJ_ERR_ALLOC;
    goto done;
  }

  /* Triangulation is on, so every face is a triangle; skip anything else. */
  for (size_t f = 0; f < num_faces; f++) {
    if (mesh->num_face_vertices[f] != 3u) continue;
    const int mid = mesh->material_ids ? mesh->material_ids[f] : -1;
    tri_bucket[ntris] =
        (mid < 0 || mid >= num_materials) ? (num_buckets - 1u) : (uint32_t)mid;
    tri_face[ntris] = (uint32_t)f;
    ntris++;
  }
  if (ntris == 0) goto done;

  for (uint32_t i = 0; i < num_buckets; i++) {
    bucket_start[i] = 0;
    bucket_fill[i] = 0;
  }
  for (uint32_t t = 0; t < ntris; t++) bucket_fill[tri_bucket[t]]++;
  {
    uint32_t acc = 0;
    for (uint32_t i = 0; i < num_buckets; i++) {
      bucket_start[i] = acc;
      acc += bucket_fill[i];
      bucket_fill[i] = bucket_start[i];
    }
  }

  out->vertices =
      (float *)malloc((size_t)ntris * 3u * TOBJ_W_STRIDE * sizeof(float));
  out->groups =
      (tobjw_group *)malloc((size_t)num_buckets * sizeof *out->groups);
  if (!out->vertices || !out->groups) {
    r = TOBJ_ERR_ALLOC;
    goto done;
  }

  for (uint32_t t = 0; t < ntris; t++) {
    const uint32_t slot = bucket_fill[tri_bucket[t]]++;
    tobjw_emit_tri(&scene->attrib, mesh, tri_face[t],
                   out->vertices + (size_t)slot * 3u * TOBJ_W_STRIDE);
  }

  for (uint32_t i = 0; i < num_buckets; i++) {
    const uint32_t count = bucket_fill[i] - bucket_start[i];
    if (!count) continue;
    out->groups[out->group_count].material =
        (i == num_buckets - 1u) ? TOBJ_W_MATERIAL_NONE : i;
    out->groups[out->group_count].start = bucket_start[i];
    out->groups[out->group_count].count = count;
    out->group_count++;
  }
  out->vert_count = ntris * 3u * TOBJ_W_STRIDE;
  out->tri_count = ntris;

done:
  free(tri_bucket);
  free(tri_face);
  free(bucket_start);
  free(bucket_fill);
  if (r != TOBJ_OK) {
    free(out->vertices);
    free(out->groups);
    out->vertices = NULL;
    out->groups = NULL;
    out->vert_count = 0;
    out->tri_count = 0;
    out->group_count = 0;
  }
  return r;
}

/* ------------------------------------------------------------------------- */
/* Handle table                                                              */
/* ------------------------------------------------------------------------- */

static int tobjw_handle_valid(int h) {
  return h > 0 && h <= tobjw_num_handles && tobjw_models[h - 1] != NULL;
}

static int tobjw_handle_push(tobjw_model *m) {
  for (int i = 0; i < tobjw_num_handles; i++) {
    if (!tobjw_models[i]) {
      tobjw_models[i] = m;
      return i + 1;
    }
  }
  if (tobjw_num_handles == tobjw_cap_handles) {
    const int cap = tobjw_cap_handles ? tobjw_cap_handles * 2 : 8;
    tobjw_model **grown =
        (tobjw_model **)realloc(tobjw_models, (size_t)cap * sizeof *grown);
    if (!grown) return 0;
    tobjw_models = grown;
    tobjw_cap_handles = cap;
  }
  tobjw_models[tobjw_num_handles] = m;
  return ++tobjw_num_handles;
}

static void tobjw_model_free(tobjw_model *m) {
  if (!m) return;
  if (m->shapes) {
    for (int i = 0; i < m->num_shapes; i++) {
      free(m->shapes[i].vertices);
      free(m->shapes[i].groups);
    }
    free(m->shapes);
  }
  tobj_scene_free_f(&m->scene);
  free(m);
}

/* ------------------------------------------------------------------------- */
/* Public ABI                                                                */
/* ------------------------------------------------------------------------- */

int tobjw_load_memory(const uint8_t *obj, size_t obj_len, const uint8_t *mtl,
                      size_t mtl_len, const char *mtl_name, uint32_t flags) {
  tobjw_model *m;
  tobj_load_config cfg;
  tobj_diag diag;
  tobjw_mtl_slot slot;
  tobj_result r;

  (void)flags;
  tobjw_msg_reset();
  if (!obj || obj_len == 0) {
    static const char msg[] = "error: empty .obj input\n";
    tobjw_msg_append(msg, sizeof msg - 1u);
    return -TOBJ_ERR_INVALID_ARG;
  }

  m = (tobjw_model *)calloc(1, sizeof *m);
  if (!m) return -TOBJ_ERR_ALLOC;

  cfg = tobj_default_config();
  if (mtl && mtl_len) {
    slot.data = mtl;
    slot.len = mtl_len;
    slot.want = mtl_name;
    cfg.mtl_resolver = tobjw_mtl_resolver;
    cfg.mtl_resolver_user_data = &slot;
  }

  memset(&diag, 0, sizeof diag);
  diag.on_message = tobjw_on_message;

  r = tobj_load_obj_from_memory_f(&m->scene, obj, obj_len, &cfg, &diag);
  if (r != TOBJ_OK) {
    if (diag.err && diag.err_len)
      tobjw_msg_append(diag.err, diag.err_len);
    else
      tobjw_msg_append(tobj_result_string(r), strlen(tobj_result_string(r)));
    tobjw_msg_append("\n", 1);
    tobj_scene_free_f(&m->scene);
    free(m);
    return -(int)r;
  }

  if (diag.warn && diag.warn_len) tobjw_msg_append(diag.warn, diag.warn_len);
  tobj_diag_free(&diag, NULL);

  m->num_shapes = (int)m->scene.num_shapes;
  m->num_materials = (int)m->scene.num_materials;
  if (m->num_shapes > 0) {
    m->shapes = (tobjw_shape_out *)calloc((size_t)m->num_shapes,
                                         sizeof *m->shapes);
    if (!m->shapes) {
      tobjw_model_free(m);
      return -TOBJ_ERR_ALLOC;
    }
    for (int i = 0; i < m->num_shapes; i++) {
      r = tobjw_emit_shape(&m->scene, &m->scene.shapes[i], m->num_materials,
                           &m->shapes[i]);
      if (r != TOBJ_OK) {
        tobjw_model_free(m);
        return -(int)r;
      }
    }
  }

  {
    const int h = tobjw_handle_push(m);
    if (!h) {
      tobjw_model_free(m);
      return -TOBJ_ERR_ALLOC;
    }
    return h;
  }
}

void tobjw_destroy(int handle) {
  if (!tobjw_handle_valid(handle)) return;
  tobjw_model_free(tobjw_models[handle - 1]);
  tobjw_models[handle - 1] = NULL;
  while (tobjw_num_handles > 0 && !tobjw_models[tobjw_num_handles - 1])
    tobjw_num_handles--;
}

const char *tobjw_last_message(void) { return tobjw_message; }

const char *tobjw_version(void) { return "tinyobj-c11"; }

int tobjw_num_shapes(int handle) {
  return tobjw_handle_valid(handle) ? tobjw_models[handle - 1]->num_shapes : 0;
}

int tobjw_num_materials(int handle) {
  return tobjw_handle_valid(handle) ? tobjw_models[handle - 1]->num_materials
                                    : 0;
}

int tobjw_shape_desc(int handle, int shape, uintptr_t *out) {
  const tobjw_model *m;
  const tobjw_shape_out *s;
  if (!out || !tobjw_handle_valid(handle)) return 0;
  m = tobjw_models[handle - 1];
  if (shape < 0 || shape >= m->num_shapes) return 0;
  s = &m->shapes[shape];
  out[0] = (uintptr_t)s->vertices;
  out[1] = (uintptr_t)s->vert_count;
  out[2] = (uintptr_t)s->tri_count;
  out[3] = (uintptr_t)s->groups;
  out[4] = (uintptr_t)s->group_count;
  out[5] = (uintptr_t)s->name;
  out[6] = (uintptr_t)TOBJ_W_STRIDE;
  out[7] = 0;
  return 1;
}

int tobjw_material(int handle, int material, float *out) {
  const tobjw_model *m;
  const tobj_material_f *mat;
  if (!out || !tobjw_handle_valid(handle)) return 0;
  m = tobjw_models[handle - 1];
  if (material < 0 || material >= m->num_materials) return 0;
  mat = &m->scene.materials[material];
  for (int i = 0; i < 3; i++) {
    out[0 + i] = mat->diffuse[i];
    out[3 + i] = mat->emission[i];
  }
  out[6] = mat->dissolve;
  out[7] = mat->shininess;
  out[8] = mat->ior;
  out[9] = (float)mat->illum;
  out[10] = mat->roughness;
  out[11] = mat->metallic;
  return 1;
}

const char *tobjw_material_name(int handle, int material) {
  const tobjw_model *m;
  if (!tobjw_handle_valid(handle)) return NULL;
  m = tobjw_models[handle - 1];
  if (material < 0 || material >= m->num_materials) return NULL;
  return m->scene.materials[material].name ? m->scene.materials[material].name
                                           : "";
}

/*
 * shim_native.c -- native oracle for web/src/tobj_wasm.c (no emscripten).
 *
 * Compile from web/:
 *   cc -std=c11 -Wall -Wextra -I./src -I.. \
 *      test/shim_native.c src/tobj_wasm.c ../tiny_obj_c.c ../tobj_tess.c \
 *      -lm -o /tmp/tobj_wasm_native
 *
 * Runs from the repo root (paths below are relative to it) and checks the
 * flattened geometry against known model facts.
 *
 * SPDX-License-Identifier: MIT
 */
#include "tobj_wasm.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;

#define CHECK(cond, ...)                    \
  do {                                      \
    if (!(cond)) {                          \
      failures++;                           \
      fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); \
      fprintf(stderr, __VA_ARGS__);         \
      fputc('\n', stderr);                  \
    }                                       \
  } while (0)

static uint8_t *read_file(const char *path, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  long n;
  uint8_t *buf;
  if (!f) return NULL;
  if (fseek(f, 0, SEEK_END) != 0) {
    fclose(f);
    return NULL;
  }
  n = ftell(f);
  if (n < 0 || fseek(f, 0, SEEK_SET) != 0) {
    fclose(f);
    return NULL;
  }
  buf = (uint8_t *)malloc((size_t)n ? (size_t)n : 1u);
  if (!buf) {
    fclose(f);
    return NULL;
  }
  if ((size_t)n != fread(buf, 1, (size_t)n, f)) {
    free(buf);
    fclose(f);
    return NULL;
  }
  fclose(f);
  *out_len = (size_t)n;
  return buf;
}

static void check_shape_sum(int h, int shape, const char *label) {
  uintptr_t desc[TOBJ_W_DESC_SLOTS];
  const uint32_t *groups;
  uint32_t ngroups;
  uint32_t tris = 0;

  CHECK(tobjw_shape_desc(h, shape, desc) == 1, "%s: desc of shape %d failed",
        label, shape);
  groups = (const uint32_t *)desc[3];
  ngroups = (uint32_t)desc[4];
  CHECK(desc[1] == (uintptr_t)desc[2] * 3u * TOBJ_W_STRIDE,
        "%s: vert_count %lu != tri_count %lu * 3 * stride", label,
        (unsigned long)desc[1], (unsigned long)desc[2]);
  for (uint32_t g = 0; g < ngroups; g++) {
    const uint32_t material = groups[3u * g + 0u];
    const uint32_t start = groups[3u * g + 1u];
    const uint32_t count = groups[3u * g + 2u];
    CHECK(start == tris, "%s: group %u start %u != %u", label, g, start, tris);
    CHECK(count > 0, "%s: group %u is empty", label, g);
    CHECK(material == TOBJ_W_MATERIAL_NONE ||
              (int)material < tobjw_num_materials(h),
          "%s: group %u material id %u out of range", label, g, material);
    tris += count;
  }
  CHECK(tris == (uint32_t)desc[2], "%s: groups cover %u of %u triangles", label,
        tris, (uint32_t)desc[2]);
}

static uint32_t total_tris(int h, const char *label) {
  uint32_t total = 0;
  for (int s = 0; s < tobjw_num_shapes(h); s++) {
    uintptr_t desc[TOBJ_W_DESC_SLOTS];
    check_shape_sum(h, s, label);
    if (tobjw_shape_desc(h, s, desc)) total += (uint32_t)desc[2];
  }
  return total;
}

static void test_cube(void) {
  size_t obj_len = 0, mtl_len = 0;
  uint8_t *obj = read_file("models/cube.obj", &obj_len);
  uint8_t *mtl = read_file("models/cube.mtl", &mtl_len);
  uintptr_t desc[TOBJ_W_DESC_SLOTS];
  float mat[TOBJ_W_MAT_SLOTS];
  int h;

  CHECK(obj && mtl, "cube.obj/cube.mtl missing (run from the repo root)");
  if (!obj || !mtl) return;

  h = tobjw_load_memory(obj, obj_len, mtl, mtl_len, "cube.mtl", 0);
  CHECK(h > 0, "cube: load failed: %s", tobjw_last_message());
  if (h <= 0) return;

  CHECK(tobjw_num_shapes(h) > 0, "cube: no shapes");
  CHECK(tobjw_num_materials(h) == 5, "cube: materials %d != 5",
        tobjw_num_materials(h));
  CHECK(total_tris(h, "cube") == 12, "cube: tris %u != 12",
        total_tris(h, "cube"));

  /* 3 white faces, then one red, one green. */
  CHECK(tobjw_material(h, 0, mat) == 1, "cube: material 0 missing");
  CHECK(strcmp(tobjw_material_name(h, 0), "white") == 0, "cube: material 0 name");
  CHECK(mat[0] == 1.0f && mat[1] == 1.0f && mat[2] == 1.0f,
        "cube: white Kd is not (1,1,1)");
  CHECK(strcmp(tobjw_material_name(h, 1), "red") == 0, "cube: material 1 name");
  CHECK(strcmp(tobjw_material_name(h, 2), "green") == 0,
        "cube: material 2 name");
  CHECK(strcmp(tobjw_material_name(h, 3), "blue") == 0, "cube: material 3 name");
  CHECK(strcmp(tobjw_material_name(h, 4), "light") == 0,
        "cube: material 4 name");

  /* Normals were absent in cube.obj, so every normal is a unit face normal. */
  for (int s = 0; s < tobjw_num_shapes(h); s++) {
    const float *v;
    uint32_t n;
    if (!tobjw_shape_desc(h, s, desc)) continue;
    CHECK(desc[6] == TOBJ_W_STRIDE, "cube: stride %lu", (unsigned long)desc[6]);
    v = (const float *)desc[0];
    n = (uint32_t)desc[1];
    for (uint32_t i = 0; i + TOBJ_W_STRIDE <= n; i += TOBJ_W_STRIDE) {
      const float *nrm = v + i + 3;
      const float len2 = nrm[0] * nrm[0] + nrm[1] * nrm[1] + nrm[2] * nrm[2];
      CHECK(len2 > 0.99f && len2 < 1.01f, "cube: corner %u bad normal len2 %f",
            i / TOBJ_W_STRIDE, (double)len2);
    }
  }

  tobjw_destroy(h);
  CHECK(tobjw_num_shapes(h) == 0, "cube: handle survived destroy");
  free(obj);
  free(mtl);
}

static void test_cornell(void) {
  size_t obj_len = 0, mtl_len = 0;
  uint8_t *obj = read_file("models/cornell_box.obj", &obj_len);
  uint8_t *mtl = read_file("models/cornell_box.mtl", &mtl_len);
  int h;

  CHECK(obj && mtl, "cornell_box files missing");
  if (!obj || !mtl) return;

  /* mtl_name is NULL, exercising the "accept any mtllib" fallback. */
  h = tobjw_load_memory(obj, obj_len, mtl, mtl_len, NULL, 0);
  CHECK(h > 0, "cornell: load failed: %s", tobjw_last_message());
  if (h <= 0) return;
  CHECK(total_tris(h, "cornell") == 36, "cornell: tris %u != 36",
        total_tris(h, "cornell"));
  tobjw_destroy(h);
  free(obj);
  free(mtl);
}

/* A 10-gon: exercises the ear-clipping tessellator on a face far beyond a quad. */
static void test_ngon(void) {
  size_t obj_len = 0;
  uint8_t *obj = read_file("models/issue-319-003.obj", &obj_len);
  int h;

  CHECK(obj, "issue-319-003.obj missing");
  if (!obj) return;

  h = tobjw_load_memory(obj, obj_len, NULL, 0, NULL, 0);
  CHECK(h > 0, "issue-319-003: load failed: %s", tobjw_last_message());
  if (h <= 0) return;
  /* One 10-gon must emit exactly n-2 = 8 triangles. */
  CHECK(total_tris(h, "issue-319-003") == 8, "issue-319-003: tris %u != 8",
        total_tris(h, "issue-319-003"));
  tobjw_destroy(h);
  free(obj);
}

/* Quads with texcoords: checks the de-indexed, V-flipped uv path. */
static void test_uv(void) {
  size_t obj_len = 0;
  uint8_t *obj = read_file("models/issue-295-trianguation-failure.obj", &obj_len);
  uintptr_t desc[TOBJ_W_DESC_SLOTS];
  int saw_nonzero_uv = 0;
  int h;

  CHECK(obj, "issue-295-trianguation-failure.obj missing");
  if (!obj) return;

  h = tobjw_load_memory(obj, obj_len, NULL, 0, NULL, 0);
  CHECK(h > 0, "issue-295: load failed: %s", tobjw_last_message());
  if (h <= 0) return;
  CHECK(total_tris(h, "issue-295") > 0, "issue-295: no triangles");

  for (int s = 0; s < tobjw_num_shapes(h); s++) {
    const float *v;
    uint32_t n;
    if (!tobjw_shape_desc(h, s, desc)) continue;
    v = (const float *)desc[0];
    n = (uint32_t)desc[1];
    for (uint32_t i = 0; i + TOBJ_W_STRIDE <= n; i += TOBJ_W_STRIDE) {
      CHECK(v[i + 6] >= -0.001f && v[i + 6] <= 1.001f, "issue-295: bad u %f",
            (double)v[i + 6]);
      CHECK(v[i + 7] >= -0.001f && v[i + 7] <= 1.001f, "issue-295: bad v %f",
            (double)v[i + 7]);
      if (v[i + 6] != 0.0f || v[i + 7] != 0.0f) saw_nonzero_uv = 1;
    }
  }
  CHECK(saw_nonzero_uv, "issue-295: texcoords were not decoded");
  tobjw_destroy(h);
  free(obj);
}

static void test_texture_names(void) {
  size_t obj_len = 0, mtl_len = 0;
  uint8_t *obj = read_file("models/issue-391.obj", &obj_len);
  uint8_t *mtl = read_file("models/issue-391.mtl", &mtl_len);
  int h;

  CHECK(obj && mtl, "issue-391 files missing");
  if (!obj || !mtl) return;

  h = tobjw_load_memory(obj, obj_len, mtl, mtl_len, "issue-391.mtl", 0);
  CHECK(h > 0, "issue-391: load failed: %s", tobjw_last_message());
  if (h <= 0) return;
  CHECK(tobjw_num_materials(h) == 2, "issue-391: materials != 2");
  CHECK(strcmp(tobjw_material_texname(h, 0, TOBJ_W_TEX_DIFFUSE), "") == 0,
        "issue-391: has_kd has a diffuse map");
  CHECK(strcmp(tobjw_material_texname(h, 1, TOBJ_W_TEX_DIFFUSE), "test.png") == 0,
        "issue-391: has_map diffuse map wrong");
  CHECK(tobjw_material_texname(h, 1, TOBJ_W_TEX_NORMAL) &&
            tobjw_material_texname(h, 1, TOBJ_W_TEX_NORMAL)[0] == '\0',
        "issue-391: has_map has an unexpected normal map");
  tobjw_destroy(h);
  free(obj);
  free(mtl);
}

static void test_corner_vertices(void) {
  size_t obj_len = 0;
  uint8_t *obj = read_file("models/skin-weight.obj", &obj_len);
  uint32_t corner = 99;
  int h;

  CHECK(obj, "skin-weight.obj missing");
  if (!obj) return;
  h = tobjw_load_memory(obj, obj_len, NULL, 0, NULL, 0);
  CHECK(h > 0, "skin: load failed: %s", tobjw_last_message());
  if (h <= 0) return;
  CHECK(tobjw_corner_vertex(h, 0, 0, &corner) == 1 && corner == 0,
        "skin: corner 0 vertex id %u", corner);
  CHECK(tobjw_corner_vertex(h, 0, 1, &corner) == 1 && corner == 1,
        "skin: corner 1 vertex id %u", corner);
  CHECK(tobjw_corner_vertex(h, 0, 99999, &corner) == 0,
        "skin: out-of-range corner accepted");
  tobjw_destroy(h);
  free(obj);
}

static void test_bad_input(void) {
  const uint8_t junk[] = "this is not an obj file\nf 1 2\nv \n###\n";
  const int h = tobjw_load_memory(junk, sizeof junk - 1u, NULL, 0, NULL, 0);
  CHECK(h > 0 || h < 0, "junk: unexpected handle 0");
  if (h > 0) {
    /* A parser that tolerates garbage must at least stay self-consistent. */
    total_tris(h, "junk");
    tobjw_destroy(h);
  } else {
    CHECK(tobjw_last_message()[0] != '\0', "junk: no diagnostic text");
  }
  CHECK(tobjw_load_memory(NULL, 0, NULL, 0, NULL, 0) < 0,
        "junk: NULL input accepted");
}

int main(void) {
  test_cube();
  test_cornell();
  test_ngon();
  test_uv();
  test_texture_names();
  test_corner_vertices();
  test_bad_input();
  if (failures) {
    fprintf(stderr, "%d check(s) failed\n", failures);
    return 1;
  }
  printf("shim_native: all checks passed\n");
  return 0;
}

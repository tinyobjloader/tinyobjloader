/* tobj_write.c -- see tobj_write.h.  Hosted C11.
 *
 * Floats are formatted by the allocation-free, libc-free formatter in
 * tobj_write_real.inc (shortest exact round-trip, 17 significant digits),
 * NOT by snprintf, so the numeric output is part of the verified core.
 */
#include "tobj_write.h"

#include <string.h>

#include "tobj_write_core.inc"
#include "tobj_write_real.inc"

typedef struct {
  char *buf;
  size_t cap;
  size_t len; /* total length that would have been written */
} wsink;

static void w_bytes(wsink *w, const char *s, size_t n) {
  if (w->buf && w->len < w->cap) {
    size_t room = w->cap - w->len;
    memcpy(w->buf + w->len, s, n < room ? n : room);
  }
  w->len += n;
}

static void w_str(wsink *w, const char *s) { w_bytes(w, s, strlen(s)); }

static void w_int(wsink *w, long long v) {
  unsigned char tmp[24];
  if (v < 0) {
    w_bytes(w, "-", 1);
    v = -v;
  }
  /* 20 digits hold any unsigned long long, so formatting cannot fail */
  size_t n = tobj_fmt_uint(tmp, sizeof tmp, (unsigned long long)v);
  w_bytes(w, (const char *)tmp, n);
}

static void w_real(wsink *w, double v, int is_double) {
  char tmp[48];
  size_t n;
  /* The formatter always emits 17 significant digits, which round-trips both
     binary64 and (promoted) binary32 exactly; `is_double` is therefore only
     kept for API symmetry with the scene types. */
  (void)is_double;
  n = tobj_fmt_real(tmp, sizeof tmp, v);
  if (n > sizeof tmp) n = sizeof tmp;
  w_bytes(w, tmp, n);
}

/* Read element i of a float or double array as double. */
static double w_get(const void *p, int is_double, size_t i) {
  return is_double ? ((const double *)p)[i] : (double)((const float *)p)[i];
}

static void w_rows(wsink *w, const char *kw, const void *p, size_t count,
                   size_t comps, int is_double) {
  for (size_t r = 0; r < count / comps; r++) {
    w_str(w, kw);
    for (size_t c = 0; c < comps; c++) {
      w_bytes(w, " ", 1);
      w_real(w, w_get(p, is_double, r * comps + c), is_double);
    }
    w_bytes(w, "\n", 1);
  }
}

static void w_corner(wsink *w, const tobj_index *ix) {
  w_int(w, (long long)ix->vertex_index + 1);
  if (ix->texcoord_index >= 0) {
    w_bytes(w, "/", 1);
    w_int(w, (long long)ix->texcoord_index + 1);
    if (ix->normal_index >= 0) {
      w_bytes(w, "/", 1);
      w_int(w, (long long)ix->normal_index + 1);
    }
  } else if (ix->normal_index >= 0) {
    w_bytes(w, "//", 2);
    w_int(w, (long long)ix->normal_index + 1);
  }
}

static void w_shape(wsink *w, const tobj_index *indices,
                    const unsigned *num_face_vertices, const int *material_ids,
                    const unsigned *smoothing_group_ids, size_t num_faces,
                    const char *name, const char *const *mat_names,
                    size_t num_mats, const char *const *tag_lines,
                    size_t num_tag_lines) {
  if (num_faces == 0) return;
  w_str(w, "g ");
  w_str(w, name ? name : "");
  w_bytes(w, "\n", 1);
  size_t at = 0;
  for (size_t f = 0; f < num_faces; f++) {
    int mid = material_ids ? material_ids[f] : -1;
    w_str(w, "usemtl");
    if (mid >= 0 && (size_t)mid < num_mats && mat_names[mid] &&
        mat_names[mid][0]) {
      w_bytes(w, " ", 1);
      w_str(w, mat_names[mid]);
    }
    w_bytes(w, "\ns ", 3);
    w_int(w, smoothing_group_ids ? (long long)smoothing_group_ids[f] : 0);
    w_str(w, "\nf");
    for (unsigned k = 0; k < num_face_vertices[f]; k++) {
      w_bytes(w, " ", 1);
      w_corner(w, &indices[at + k]);
    }
    w_bytes(w, "\n", 1);
    at += num_face_vertices[f];
  }
  /* `t` lines verbatim: vertex numbers are file-global and faces keep their
   * order, so the tags stay valid (subd-obj.md). */
  for (size_t i = 0; i < num_tag_lines; i++) {
    w_str(w, tag_lines[i]);
    w_bytes(w, "\n", 1);
  }
}

/* Shared body for the float and double writers. */
#define TOBJ_WRITE_BODY(SUF, IS_DOUBLE)                                      \
  wsink w = {buf, cap, 0};                                                   \
  if (!sc) return 0;                                                         \
  /* `skel_*` lines (file scope, skel-obj.md) verbatim */                    \
  for (size_t i = 0; i < sc->attrib.num_skel_lines; i++) {                   \
    w_str(&w, sc->attrib.skel_lines[i]);                                     \
    w_bytes(&w, "\n", 1);                                                    \
  }                                                                          \
  w_rows(&w, "v", sc->attrib.vertices.ptr, sc->attrib.vertices.count, 3,      \
         IS_DOUBLE);                                                          \
  w_rows(&w, "vt", sc->attrib.texcoords.ptr, sc->attrib.texcoords.count, 2,   \
         IS_DOUBLE);                                                          \
  w_rows(&w, "vn", sc->attrib.normals.ptr, sc->attrib.normals.count, 3,       \
         IS_DOUBLE);                                                          \
  const char *names[256];                                                    \
  size_t nm = sc->num_materials < 256 ? sc->num_materials : 256;             \
  for (size_t i = 0; i < nm; i++) names[i] = sc->materials[i].name;           \
  for (size_t s = 0; s < sc->num_shapes; s++) {                              \
    const tobj_mesh##SUF *m = &sc->shapes[s].mesh;                             \
    w_shape(&w, m->indices, m->num_face_vertices, m->material_ids,           \
            m->smoothing_group_ids, m->num_faces, sc->shapes[s].name, names, \
            nm, m->tag_lines, m->num_tag_lines);                             \
  }                                                                          \
  if (buf && cap) buf[w.len < cap ? w.len : cap - 1] = '\0';                  \
  return w.len;

size_t tobj_write_obj_f(const tobj_scene_f *sc, char *buf, size_t cap) {
  TOBJ_WRITE_BODY(_f, 0)
}

size_t tobj_write_obj_d(const tobj_scene_d *sc, char *buf, size_t cap) {
  TOBJ_WRITE_BODY(_d, 1)
}

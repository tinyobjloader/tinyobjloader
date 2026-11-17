/*
 * tobj_subd — subdivision-surface tags (`t` lines) for tinyobjloader (C11).
 *
 * Parses a mesh's `t` lines, checks them against the mesh's faces, and
 * writes them in canonical form. See subd-obj.md for the format.
 *
 * The normative specification is the Lean 4 model in formal/Subd
 * (TobjSubd.parseTags / check / print). `tobj_subd_dump` produces
 * byte-for-byte the output of the Lean reference executable `subdobj`; the
 * two are compared by formal/Subd/tools/diff.sh.
 *
 * Requires libc (malloc). MIT license, same as tinyobjloader.
 */
#ifndef TOBJ_SUBD_H_
#define TOBJ_SUBD_H_

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Scalar options; TOBJ_SUBD_UNSET when the tag is absent. */
#define TOBJ_SUBD_UNSET (-1)
enum { TOBJ_SUBD_CATMARK = 0, TOBJ_SUBD_LOOP = 1, TOBJ_SUBD_BILINEAR = 2 };
enum { TOBJ_SUBD_CREASE_NORMAL = 0, TOBJ_SUBD_CREASE_CHAIKIN = 1 };
enum { TOBJ_SUBD_TRI_CATMARK = 0, TOBJ_SUBD_TRI_SMOOTH = 1 };

typedef struct tobj_subd_crease {
  size_t v0, v1;     /* v0 < v1, 0-based file vertex numbers */
  char *sharpness;   /* decimal text; "0" for negative input */
} tobj_subd_crease;

typedef struct tobj_subd_corner {
  size_t v;
  char *sharpness;
} tobj_subd_corner;

typedef struct tobj_subd {
  int scheme;               /* TOBJ_SUBD_CATMARK/LOOP/BILINEAR or UNSET */
  int interp_boundary;      /* 0..2 or UNSET */
  int fvar_interp_boundary; /* 0..5 or UNSET */
  int crease_method;        /* TOBJ_SUBD_CREASE_* or UNSET */
  int smooth_triangles;     /* TOBJ_SUBD_TRI_* or UNSET */
  tobj_subd_crease *creases; size_t num_creases;
  tobj_subd_corner *corners; size_t num_corners;
  size_t *holes;             size_t num_holes;
  char **unknown;            size_t num_unknown; /* canonical lines */
  char **errors;             size_t num_errors;
  int ok; /* the tags are well-formed (Lean `check`) */
} tobj_subd;

/* Parse and check one mesh's tag lines (each the full line, `t ...`; other
 * lines are ignored). `face_vertex_counts[f]` vertices of face f are listed in
 * order in `vertex_indices` (0-based file vertex numbers), as in
 * tobj_mesh / tinyobj::mesh_t loaded with triangulate = false.
 * Returns 0, or -1 on allocation failure. */
int tobj_subd_parse_lines(const char *const *lines, size_t num_lines,
                          const unsigned int *face_vertex_counts,
                          size_t num_faces, const int *vertex_indices,
                          tobj_subd *out);
void tobj_subd_free(tobj_subd *s);

/* Sharpness as a number: >= 0; values >= 10 mean infinitely sharp. */
double tobj_subd_sharpness(const char *text);

/* Canonical `t` lines (subd-obj.md), each ending with '\n'. Writes nothing
 * for a mesh that is not ok. Returns a malloc'd NUL-terminated string (caller
 * frees) or NULL on allocation failure. */
char *tobj_subd_to_lines(const tobj_subd *s, size_t *out_len);

/* Text of a whole .obj (subset: v, f, o, g, t lines) split into meshes, each
 * dumped as in the Lean reference executable. For differential testing. */
char *tobj_subd_dump_obj(const char *text, size_t len, size_t *out_len);

#ifdef __cplusplus
}
#endif
#endif /* TOBJ_SUBD_H_ */

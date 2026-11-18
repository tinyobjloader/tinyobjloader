/*
 * tobj_skel — skeletons for the `vw` skin weights of tinyobjloader (C11).
 *
 * Parses the file's `skel_*` lines, checks them, and writes canonical form.
 * See skel-obj.md. The normative specification is the Lean 4 model in
 * formal/Skel; `tobj_skel_dump_obj` produces byte-for-byte the output of its
 * reference executable `skelobj` (compared by formal/Skel/tools/diff.sh).
 *
 * Requires libc (malloc). MIT license, same as tinyobjloader.
 */
#ifndef TOBJ_SKEL_H_
#define TOBJ_SKEL_H_

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct tobj_skel_joint {
  char *name;
  long parent;   /* index of the parent joint, or -1 for a root */
  char **bind;   /* 16 decimal texts (row-major world matrix), or NULL */
  char **rest;   /* 16 decimal texts (row-major local matrix), or NULL */
} tobj_skel_joint;

typedef struct tobj_skel {
  tobj_skel_joint *joints; size_t num_joints;
  char *lib, *lib_skeleton;     /* skel_lib path and optional name, or NULL */
  char *anim, *anim_name;       /* skel_anim path and optional name, or NULL */
  char **errors; size_t num_errors;
  int ext; /* some skel_* line was present */
  int ok;  /* ext && well-formed (Lean `check`) */
} tobj_skel;

/* Parse and check the `skel_*` lines (each a full line; other lines are
 * ignored). `max_joint_id` is the largest joint id used by `vw` records, or
 * -1 if there are none. Returns 0, or -1 on allocation failure. */
int tobj_skel_parse_lines(const char *const *lines, size_t num_lines, long max_joint_id,
                          tobj_skel *out);
void tobj_skel_free(tobj_skel *s);

/* A matrix entry as a number. */
double tobj_skel_number(const char *text);

/* Canonical `skel_*` lines, each ending with '\n'; empty when not ok.
 * Returns a malloc'd string (caller frees) or NULL on allocation failure. */
char *tobj_skel_to_lines(const tobj_skel *s, size_t *out_len);

/* Whole .obj text (subset: skel_* and vw lines): `skel none` when there are
 * no skel_* lines, else `skel ok=<0|1> joints=<n>` and the canonical lines.
 * For differential testing against the Lean reference. */
char *tobj_skel_dump_obj(const char *text, size_t len, size_t *out_len);

#ifdef __cplusplus
}
#endif
#endif /* TOBJ_SKEL_H_ */

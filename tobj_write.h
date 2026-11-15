/*
 * tobj_write.h -- canonical .obj writer for tiny_obj_c scenes.
 *
 * Output format (mirrors the Lean specification `Obj.writeObj` in
 * formal/Obj/Write.lean, whose round-trip theorem `Obj.parse_write`
 * proves that loading the text reproduces the shapes):
 *
 *   v x y z                  one line per vertex
 *   vt u v                   one line per texcoord
 *   vn x y z                 one line per normal
 *   g <shape name>           per shape that has at least one face
 *   usemtl [<material name>] per face (name omitted when the id is -1)
 *   s <smoothing group>      per face (0 = off)
 *   f a b c ...              per face, absolute 1-based indices, written as
 *                            v, v/vt, v//vn or v/vt/vn depending on which
 *                            indices are present
 *
 * Only mesh topology is written (lines/points/free-form and materials files
 * are not).
 *
 * Floats are formatted by `tobj_write_real.inc`: a libc-free, allocation-free
 * formatter that emits 17 significant digits, which round-trip binary64
 * exactly through the loader.  It does not use snprintf or any libm routine,
 * so the numeric output is part of the verified core.  (17 digits also
 * round-trips binary32 after the usual promotion, covering the float scene
 * type.)
 *
 * The return value is the full output length (excluding the terminating NUL),
 * like snprintf: if it is >= cap the output was truncated.  `buf` may be NULL
 * with cap == 0 to measure.
 */
#ifndef TOBJ_WRITE_H
#define TOBJ_WRITE_H

#include "tiny_obj_c.h"

#ifdef __cplusplus
extern "C" {
#endif

size_t tobj_write_obj_f(const tobj_scene_f *sc, char *buf, size_t cap);
size_t tobj_write_obj_d(const tobj_scene_d *sc, char *buf, size_t cap);

#ifdef __cplusplus
}
#endif

#endif /* TOBJ_WRITE_H */

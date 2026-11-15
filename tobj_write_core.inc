/*
 * tobj_write_core.inc -- allocation-free, libc-free building blocks of the
 * .obj writer.  Included by tobj_write.c and by tiny_obj_verified.c (the
 * translation unit that formal/tools/c2lean.py translates; the refinement
 * proof is formal/Obj/C/Proofs/ObjFmtUint.lean, whose pure counterpart is
 * `Obj.decDigits` in formal/Obj/Write.lean).
 */
#ifndef TOBJ_WRITE_CORE_INC
#define TOBJ_WRITE_CORE_INC

#include <stddef.h>

/* Write the decimal digits of `v` (most significant first, no terminator)
 * into buf[0 .. n) and return n.  Returns 0 and writes nothing when the digit
 * count exceeds `cap`. */
static size_t tobj_fmt_uint(unsigned char *buf, size_t cap,
                            unsigned long long v) {
  size_t n = 1;
  unsigned long long t = v;
  while (t >= 10u) {
    t = t / 10u;
    n++;
  }
  if (n > cap) return 0;
  size_t i = n;
  t = v;
  while (i > 0u) {
    i--;
    buf[i] = (unsigned char)(48u + (unsigned)(t % 10u));
    t = t / 10u;
  }
  return n;
}

#endif /* TOBJ_WRITE_CORE_INC */

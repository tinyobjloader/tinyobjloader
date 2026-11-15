/* SPDX-License-Identifier: MIT. MiniC-compatible arithmetic core.
   Included by exact.c, and translated independently by c2lean. */
#include <stdint.h>
static uint64_t tess_mag(int64_t a) {
  return a < 0 ? (uint64_t)(-(a + 1)) + UINT64_C(1) : (uint64_t)a;
}
/* All four inputs are limbs. The maximum result is 2^64-1. */
static uint64_t tess_limb_madd(uint32_t a, uint32_t b, uint32_t add,
                               uint32_t carry) {
  return (uint64_t)a * (uint64_t)b + (uint64_t)add + (uint64_t)carry;
}

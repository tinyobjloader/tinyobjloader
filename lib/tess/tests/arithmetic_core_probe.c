/* SPDX-License-Identifier: MIT. Exercise the actual MiniC-translated helpers. */
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

#include "../src/exact_core.c"
int main(void) {
  char operation[8];
  while (scanf("%7s", operation) == 1) {
    if (!strcmp(operation, "mag")) {
      int64_t a;
      if (scanf("%" SCNd64, &a) != 1) return 2;
      printf("%" PRIu64 "\n", tess_mag(a));
    } else if (!strcmp(operation, "madd")) {
      uint32_t a, b, add, carry;
      uint64_t result;
      if (scanf("%" SCNu32 " %" SCNu32 " %" SCNu32 " %" SCNu32,
                &a, &b, &add, &carry) != 4)
        return 2;
      result = tess_limb_madd(a, b, add, carry);
      printf("%" PRIu64 " %" PRIu32 " %" PRIu32 "\n", result,
             (uint32_t)result, (uint32_t)(result >> 32));
    } else
      return 2;
  }
  return ferror(stdin) ? 2 : 0;
}

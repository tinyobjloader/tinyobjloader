#include <stdint.h>
#include <stdio.h>

#include "tess.h"
#define CHECK(x)                                      \
  do {                                                \
    if (!(x)) {                                       \
      fprintf(stderr, "failure line %d\n", __LINE__); \
      return 1;                                       \
    }                                                 \
  } while (0)
int main(void) {
  int ax, ay, bx, by, cx, cy, s;
  for (ax = -2; ax <= 2; ax++)
    for (ay = -2; ay <= 2; ay++)
      for (bx = -2; bx <= 2; bx++)
        for (by = -2; by <= 2; by++)
          for (cx = -2; cx <= 2; cx++)
            for (cy = -2; cy <= 2; cy++) {
              long d =
                  (long)(bx - ax) * (cy - ay) - (long)(by - ay) * (cx - ax);
              CHECK(tess_orient2i((tess_point2i){ax, ay},
                                  (tess_point2i){bx, by},
                                  (tess_point2i){cx, cy}, &s) == TESS_OK);
              CHECK(s == ((d > 0) - (d < 0)));
            }
  s = 17;
  CHECK(tess_orient2i((tess_point2i){INT64_MIN, 0},
                      (tess_point2i){INT64_MAX, 0}, (tess_point2i){0, 1},
                      &s) == TESS_RESOURCE_LIMIT);
  CHECK(s == 17);
  return 0;
}

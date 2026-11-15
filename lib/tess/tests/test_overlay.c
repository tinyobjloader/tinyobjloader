#include <stdio.h>

#include "geometry.h"
int main(void) {
  tm seed, out;
  qr tolerance = {0}, a = {0}, b = {0};
  size_t i;
  const double p[4][3] = {{0, 0, 0}, {1, 0, 0}, {1, 1, 1}, {0, 1, 0}};
  int ok = 1;
  tm_init(&seed);
  tm_init(&out);
  seed.axis = out.axis = 2;
  seed.u = out.u = 0;
  seed.w = out.w = 1;
  for (i = 0; i < 4; i++) {
    tg_add_vertex(&seed, p[i], i);
    tg_add_vertex(&out, p[i], i);
  }
  tg_add_face(&seed, 0, 1, 2);
  tg_add_face(&seed, 0, 2, 3);
  tg_add_face(&out, 0, 1, 3);
  tg_add_face(&out, 1, 2, 3);
  qr_i64(&out.c, &tolerance, 0);
  if (tg_reference(&out, &seed, &tolerance)) ok = 0;
  qr_i64(&out.c, &a, 1);
  qr_i64(&out.c, &b, 2);
  qr_div(&out.c, &tolerance, &a, &b);
  if (!tg_reference(&out, &seed, &tolerance)) ok = 0;
  qr_i64(&out.c, &b, 3);
  qr_div(&out.c, &tolerance, &a, &b);
  if (tg_reference(&out, &seed, &tolerance)) ok = 0;
  out.f[0] = seed.f[0];
  out.f[1] = seed.f[1];
  qr_i64(&out.c, &tolerance, 0);
  if (!tg_reference(&out, &seed, &tolerance)) ok = 0;
  qr_clear(&out.c, &tolerance);
  qr_clear(&out.c, &a);
  qr_clear(&out.c, &b);
  if (out.c.status || seed.c.status) ok = 0;
  tm_clear(&seed);
  tm_clear(&out);
  if (seed.c.bytes || out.c.bytes) ok = 0;
  if (!ok) fprintf(stderr, "overlay/reference invariant failure\n");
  return !ok;
}

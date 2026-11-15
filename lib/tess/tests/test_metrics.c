#include <stdio.h>

#include "metrics.h"
static int bounds(void) {
  tx c;
  qr q = {0}, lo = {0}, hi = {0}, s = {0}, width = {0}, threshold = {0};
  int i, ok = 1;
  tx_init(&c);
  c.max_ops =
      1000000000; /* 40 independent extreme-exponent bracket fixtures. */
  for (i = -1074; i <= 1024; i += 53) {
    qr_i64(&c, &q, 3);
    qr_scale_pow2(&c, &q, &q, i);
    qr_sqrt_bounds(&c, &q, 80, &lo, &hi);
    qr_mul(&c, &s, &lo, &lo);
    if (qr_cmp(&c, &s, &q) > 0) ok = 0;
    qr_mul(&c, &s, &hi, &hi);
    if (qr_cmp(&c, &s, &q) < 0) ok = 0;
    qr_sub(&c, &width, &hi, &lo);
    qr_mul(&c, &width, &width, &width);
    qr_scale_pow2(&c, &threshold, &width, 150);
    if (qr_cmp(&c, &threshold, &q) > 0) ok = 0;
  }
  qr_clear(&c, &q);
  qr_clear(&c, &lo);
  qr_clear(&c, &hi);
  qr_clear(&c, &s);
  qr_clear(&c, &width);
  qr_clear(&c, &threshold);
  if (!ok || c.status || c.bytes)
    fprintf(stderr, "bounds ok=%d status=%d ops=%zu bytes=%zu\n", ok, c.status,
            c.ops, c.bytes);
  return ok && !c.status && !c.bytes;
}
int main(void) {
  tm m;
  qr target = {0}, want = {0}, n = {0}, d = {0};
  double p[4][3] = {{0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {0, 1, 0}};
  size_t i;
  int ok = bounds();
  tm_init(&m);
  for (i = 0; i < 4; i++) tg_add_vertex(&m, p[i], i);
  tg_add_face(&m, 0, 1, 2);
  tg_add_face(&m, 0, 2, 3);
  if (!tg_count_target(&m, &m, 128, &target)) ok = 0;
  qr_i64(&m.c, &n, 1);
  qr_i64(&m.c, &d, 128);
  qr_div(&m.c, &want, &n, &d);
  if (qr_cmp(&m.c, &target, &want)) ok = 0;
  qr_i64(&m.c, &n, 3);
  qr_i64(&m.c, &d, 2);
  qr_div(&m.c, &want, &n, &d);
  qr_round_dyadic(&m.c, &want, &want, 0);
  qr_i64(&m.c, &n, 2);
  if (qr_cmp(&m.c, &want, &n)) ok = 0;
  qr_clear(&m.c, &target);
  qr_clear(&m.c, &want);
  qr_clear(&m.c, &n);
  qr_clear(&m.c, &d);
  if (m.c.status) {
    fprintf(stderr, "target status %d\n", m.c.status);
    ok = 0;
  }
  tm_clear(&m);
  if (m.c.bytes) ok = 0;
  if (!ok) fprintf(stderr, "certified area/rounding test failed\n");
  return !ok;
}

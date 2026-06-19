/*
 * tess_tester.c -- unit + property tests for tobj_tess (pure C11).
 * Build via tests/Makefile (`tess_tester`) with ASan+UBSan.
 */
#include "acutest.h"
#include "tobj_tess.h"

#include <math.h>
#include <string.h>

#define MAXN 4096
static uint32_t g_out[3 * MAXN];
static unsigned char g_scratch[1 << 20];

/* Run the double tessellator on an xyz ring; returns the result. */
static tobj_tess_result run_d(const double *pts, uint32_t n) {
  tobj_tess_desc_d d;
  memset(&d, 0, sizeof d);
  d.points = pts;
  d.n = n;
  d.out_indices = g_out;
  d.out_cap = 3 * MAXN;
  d.scratch = g_scratch;
  d.scratch_size = sizeof g_scratch;
  tobj_tess_result r;
  tobj_tess_polygon_d(&d, &r);
  return r;
}

/* Shared invariant checks: count == n-2, all indices in [0,n), no repeats in a
 * triangle, status not OOM/INVALID for n>=3. */
static void check_invariants(const double *pts, uint32_t n) {
  tobj_tess_result r = run_d(pts, n);
  TEST_CHECK_(r.status != TOBJ_TESS_OOM, "n=%u not OOM", n);
  TEST_CHECK_(r.status != TOBJ_TESS_INVALID, "n=%u not INVALID", n);
  TEST_CHECK_(r.num_triangles == n - 2, "n=%u tris=%u expected %u", n,
              r.num_triangles, n - 2);
  for (uint32_t i = 0; i < r.num_triangles * 3; i++)
    TEST_CHECK_(g_out[i] < n, "idx %u in range (<%u)", g_out[i], n);
  for (uint32_t t = 0; t < r.num_triangles; t++) {
    uint32_t a = g_out[3 * t], b = g_out[3 * t + 1], c = g_out[3 * t + 2];
    TEST_CHECK_(a != b && b != c && a != c, "tri %u has distinct corners", t);
  }
}

static void test_n_too_small(void) {
  double p[] = {0, 0, 0, 1, 1, 1};
  tobj_tess_result r = run_d(p, 2);
  TEST_CHECK(r.status == TOBJ_TESS_INVALID);
  TEST_CHECK(r.num_triangles == 0);
}

static void test_triangle(void) {
  double p[] = {0, 0, 0, 1, 0, 0, 0, 1, 0};
  check_invariants(p, 3);
}

static void test_square(void) {
  double p[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0};
  check_invariants(p, 4);
}

static void test_concave_L(void) {
  double p[] = {0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 1, 0, 1, 2, 0, 0, 2, 0};
  check_invariants(p, 6);
}

static void test_collinear_spike(void) {
  double p[] = {0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0};
  check_invariants(p, 5);
}

static void test_bowtie(void) {
  double p[] = {0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 2, 0};
  tobj_tess_result r = run_d(p, 4);
  TEST_CHECK(r.num_triangles == 2);
  TEST_CHECK(r.status == TOBJ_TESS_DEGENERATE_BESTEFFORT);
}

static void test_big_coord_sliver(void) {
  /* regression for the absolute-epsilon bug: tiny sliver at magnitude ~14000 */
  double p[] = {14000, 14000, 0,        14000.001, 14000, 0,
                14000.0005, 14000.0008, 0, 14000,   14000.001, 0};
  check_invariants(p, 4);
}

static void test_coincident(void) {
  double p[] = {5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5};
  check_invariants(p, 5);
}

static void test_nonplanar(void) {
  double p[] = {0, 0, 0,    2, 0, 0.3, 3, 1, -0.2,
                2, 2, 0.1,  0, 2, 0.4, -1, 1, -0.3};
  check_invariants(p, 6);
}

static void test_newell_zero(void) {
  /* fully collinear: degenerate but must not crash, still n-2 tris */
  double p[] = {0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4};
  tobj_tess_result r = run_d(p, 5);
  TEST_CHECK(r.num_triangles == 3);
  for (uint32_t i = 0; i < 9; i++) TEST_CHECK(g_out[i] < 5);
}

static void test_big_convex_fan(void) {
  static double p[3 * 1000];
  for (int i = 0; i < 1000; i++) {
    double a = 2.0 * 3.14159265358979323846 * i / 1000.0;
    p[3 * i] = cos(a);
    p[3 * i + 1] = sin(a);
    p[3 * i + 2] = 0;
  }
  check_invariants(p, 1000);
}

static void test_star_concave(void) {
  static double p[3 * 12];
  for (int i = 0; i < 12; i++) {
    double a = 2.0 * 3.14159265358979323846 * i / 12.0;
    double rr = (i & 1) ? 0.4 : 1.0;
    p[3 * i] = rr * cos(a);
    p[3 * i + 1] = rr * sin(a);
    p[3 * i + 2] = 0;
  }
  check_invariants(p, 12);
}

/* Property: total triangle area ~= polygon area for a simple convex polygon. */
static double tri_area(const double *a, const double *b, const double *c) {
  return 0.5 * fabs((b[0] - a[0]) * (c[1] - a[1]) -
                    (b[1] - a[1]) * (c[0] - a[0]));
}
static void test_area_preservation(void) {
  /* planar (z=0) regular heptagon */
  uint32_t n = 7;
  static double p[3 * 7];
  for (uint32_t i = 0; i < n; i++) {
    double a = 2.0 * 3.14159265358979323846 * i / n;
    p[3 * i] = 3.0 * cos(a);
    p[3 * i + 1] = 3.0 * sin(a);
    p[3 * i + 2] = 0;
  }
  /* shoelace area */
  double poly = 0;
  for (uint32_t i = 0; i < n; i++) {
    uint32_t j = (i + 1) % n;
    poly += p[3 * i] * p[3 * j + 1] - p[3 * j] * p[3 * i + 1];
  }
  poly = fabs(poly) * 0.5;
  tobj_tess_result r = run_d(p, n);
  double sum = 0;
  for (uint32_t t = 0; t < r.num_triangles; t++)
    sum += tri_area(&p[3 * g_out[3 * t]], &p[3 * g_out[3 * t + 1]],
                    &p[3 * g_out[3 * t + 2]]);
  TEST_CHECK_(fabs(sum - poly) < 1e-6 * poly, "tri area %.6f vs poly %.6f", sum,
              poly);
}

/* Property: deterministic across two independent scratch buffers. */
static void test_determinism(void) {
  double p[] = {0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 1, 0, 1, 2, 0, 0, 2, 0};
  uint32_t n = 6;
  uint32_t out1[3 * 6], out2[3 * 6];
  unsigned char s1[4096], s2[4096];
  tobj_tess_desc_d d;
  memset(&d, 0, sizeof d);
  d.points = p;
  d.n = n;
  tobj_tess_result r1, r2;
  d.out_indices = out1;
  d.out_cap = 18;
  d.scratch = s1;
  d.scratch_size = sizeof s1;
  tobj_tess_polygon_d(&d, &r1);
  d.out_indices = out2;
  d.scratch = s2;
  d.scratch_size = sizeof s2;
  tobj_tess_polygon_d(&d, &r2);
  TEST_CHECK(r1.num_triangles == r2.num_triangles);
  for (uint32_t i = 0; i < r1.num_triangles * 3; i++)
    TEST_CHECK(out1[i] == out2[i]);
}

/* float variant smoke: must match counts. */
static void test_float_variant(void) {
  float p[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0.5f, 1.5f, 0};
  tobj_tess_desc_f d;
  memset(&d, 0, sizeof d);
  d.points = p;
  d.n = 5;
  d.out_indices = g_out;
  d.out_cap = 3 * MAXN;
  d.scratch = g_scratch;
  d.scratch_size = sizeof g_scratch;
  tobj_tess_result r;
  tobj_tess_polygon_f(&d, &r);
  TEST_CHECK(r.num_triangles == 3);
}

TEST_LIST = {
    {"n_too_small", test_n_too_small},
    {"triangle", test_triangle},
    {"square", test_square},
    {"concave_L", test_concave_L},
    {"collinear_spike", test_collinear_spike},
    {"bowtie", test_bowtie},
    {"big_coord_sliver", test_big_coord_sliver},
    {"coincident", test_coincident},
    {"nonplanar", test_nonplanar},
    {"newell_zero", test_newell_zero},
    {"big_convex_fan", test_big_convex_fan},
    {"star_concave", test_star_concave},
    {"area_preservation", test_area_preservation},
    {"determinism", test_determinism},
    {"float_variant", test_float_variant},
    {NULL, NULL}};

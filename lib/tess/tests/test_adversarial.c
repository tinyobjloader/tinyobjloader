#include <math.h>
#include <stdio.h>

#include "edits.h"
static int input_case(const char* name, const double* xyz, size_t n,
                      const size_t* rings, size_t nr, int axis, int strict,
                      tess_status expected, size_t nf) {
  tess_input in = {xyz, n, rings, nr};
  tess_options options = tess_default_options();
  tess_result* r = NULL;
  tess_status status;
  tess_diagnostic diagnostic;
  options.chart_axis = axis;
  options.strict_planar = strict;
  options.diagnostic = &diagnostic;
  status = tess_triangulate(&in, &options, &r);
  if (status != expected || (r && tess_triangle_count(r) != nf)) {
    fprintf(stderr, "%s: got %d/%zu expected %d/%zu reason %d axis %d\n", name,
            status, tess_triangle_count(r), expected, nf, diagnostic.reason,
            diagnostic.axis);
    tess_result_free(r);
    return 0;
  }
  tess_result_free(r);
  return 1;
}
static int constrained(void) {
  const double xyz[] = {0, 0, 0, 4, 0, 0, 4, 4, 0, 0, 4, 0,
                        1, 1, 0, 1, 3, 0, 3, 3, 0, 3, 1, 0};
  const size_t rings[] = {0, 4, 8};
  tess_input in = {xyz, 8, rings, 2};
  tess_result* r = NULL;
  tess_remesh_options options = tess_default_remesh_options();
  tess_run_report report;
  tess_status status;
  if (tess_triangulate(&in, NULL, &r) != TESS_OK) return 0;
  options.target_count = 128;
  options.max_passes = 1;
  options.max_edits = 1;
  options.max_candidates = 8;
  status = tess_remesh(r, &options, &report);
  if (status != TESS_VALID_TARGETS_UNMET ||
      report.termination == TESS_STOP_TARGETS_MET ||
      !tg_check_chains(&r->mesh, &r->seed, &r->remesh_options) ||
      !tg_validate(&r->mesh) || !tg_audit3(&r->mesh)) {
    fprintf(stderr, "infeasible hole outcome %d termination %d\n", status,
            report.termination);
    tess_result_free(r);
    return 0;
  }
  tess_result_free(r);
  return 1;
}
static int lawson(void) {
  const double p[][3] = {{0, 0, 0}, {2, 0, 0}, {2, 2, 0}, {0, 1, 0}};
  tm m;
  size_t i;
  int complete = 99, ok;
  tm_init(&m);
  for (i = 0; i < 4; i++) tg_add_vertex(&m, p[i], i);
  m.nr = 1;
  m.rings = tx_alloc(&m.c, 2, sizeof(size_t));
  m.rings[1] = 4;
  if (!tg_prepare(&m, 2, 0)) return 0;
  tg_add_face(&m, 0, 1, 2);
  tg_add_face(&m, 0, 2, 3);
  ok = tg_legalize(&m, 0, &complete) && !complete &&
       tg_legalize(&m, 10, &complete) && complete;
  tm_clear(&m);
  return ok;
}
int main(void) {
  const double col[] = {0, 0, 0, .5, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0};
  const double backtrack[] = {0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 2, 0, 0, 2, 0};
  const double closure[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0};
  const double hole[] = {0, 0, 0, 4, 0, 0, 4, 4, 0, 0, 4, 0,
                         1, 1, 0, 1, 3, 0, 3, 3, 0, 3, 1, 0};
  const double touch[] = {0, 0, 0, 4, 0, 0, 4, 4, 0, 0, 4, 0,
                          0, 1, 0, 0, 2, 0, 1, 2, 0, 1, 1, 0};
  const double outside[] = {0, 0, 0, 4, 0, 0, 4, 4, 0, 0, 4, 0,
                            5, 1, 0, 5, 2, 0, 6, 2, 0, 6, 1, 0};
  const double nested[] = {0, 0, 0, 8, 0, 0, 8, 8, 0, 0, 8, 0,
                           1, 1, 0, 1, 7, 0, 7, 7, 0, 7, 1, 0,
                           2, 2, 0, 2, 3, 0, 3, 3, 0, 3, 2, 0};
  const double wrongwind[] = {0, 0, 0, 4, 0, 0, 4, 4, 0, 0, 4, 0,
                              1, 1, 0, 3, 1, 0, 3, 3, 0, 1, 3, 0};
  const double overhang[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0,
                             0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1};
  const double vertical[] = {7, 0, 0, 7, 1, 0, 7, 1, 1, 7, 0, 1};
  const double tie[] = {0, 0, 0, 1, 0, 1, 0, 1, 1};
  const double warped[] = {0, 0, 0, 1, 0, 0, 1, 1, 0x1p-1000, 0, 1, 0};
  const size_t r5[] = {0, 5}, r4[] = {0, 4}, r3[] = {0, 3}, r8[] = {0, 8},
               rhole[] = {0, 4, 8}, rnest[] = {0, 4, 8, 12};
  double transformed[12];
  size_t i, axis;
  int ok = input_case("retained-collinear", col, 5, r5, 1, 2, 0, TESS_OK, 3) &&
           input_case("backtrack", backtrack, 5, r5, 1, 2, 0,
                      TESS_UNSUPPORTED_CHART, 0) &&
           input_case("closure", closure, 5, r5, 1, 2, 0,
                      TESS_UNSUPPORTED_CHART, 0) &&
           input_case("hole", hole, 8, rhole, 2, 2, 0, TESS_OK, 8) &&
           input_case("hole-touch", touch, 8, rhole, 2, 2, 0,
                      TESS_UNSUPPORTED_CHART, 0) &&
           input_case("hole-outside", outside, 8, rhole, 2, 2, 0,
                      TESS_UNSUPPORTED_CHART, 0) &&
           input_case("hole-nested", nested, 12, rnest, 3, 2, 0,
                      TESS_UNSUPPORTED_CHART, 0) &&
           input_case("hole-winding", wrongwind, 8, rhole, 2, 2, 0,
                      TESS_UNSUPPORTED_CHART, 0) &&
           input_case("overhang", overhang, 8, r8, 1, -1, 0,
                      TESS_UNSUPPORTED_CHART, 0) &&
           input_case("vertical-auto", vertical, 4, r4, 1, -1, 1, TESS_OK, 2) &&
           input_case("vertical-bad-chart", vertical, 4, r4, 1, 2, 1,
                      TESS_UNSUPPORTED_CHART, 0) &&
           input_case("tiny-warp-planar", warped, 4, r4, 1, 2, 1,
                      TESS_UNSUPPORTED_CHART, 0) &&
           input_case("tiny-warp-graph", warped, 4, r4, 1, 2, 0, TESS_OK, 2) &&
           constrained() && lawson();
  for (axis = 0; axis < 3; axis++)
    ok = ok && input_case("axis-tie", tie, 3, r3, 1, (int)axis, 0, TESS_OK, 1);
  {
    tess_input in = {tie, 3, r3, 1};
    tess_result* r = NULL;
    if (tess_triangulate(&in, NULL, &r) != TESS_OK || tess_chart_axis(r) != 0)
      ok = 0;
    tess_result_free(r);
  }
  for (i = 0; i < 4; i++) {
    transformed[3 * i] = 0x1p40 + (i == 1 || i == 2 ? 0x1p20 : 0);
    transformed[3 * i + 1] = -0x1p40 + (i >= 2 ? 0x1p20 : 0);
    transformed[3 * i + 2] = 0;
  }
  ok = ok && input_case("large-offset-scale", transformed, 4, r4, 1, 2, 1,
                        TESS_OK, 2);
  for (i = 0; i < 4; i++) transformed[3 * i] = -transformed[3 * i];
  ok = ok && input_case("reflected", transformed, 4, r4, 1, 2, 1, TESS_OK, 2);
  return !ok;
}

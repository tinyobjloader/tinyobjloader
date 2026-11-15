#include <math.h>

#include "tess.h"
int main(void) {
  double xyz[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0};
  size_t rings[] = {0, 5};
  tess_input in = {xyz, 5, rings, 1};
  tess_options options = tess_default_options();
  tess_result* r = NULL;
  tess_diagnostic d;
  options.chart_axis = 2;
  options.diagnostic = &d;
  if (tess_triangulate(&in, &options, &r) != TESS_UNSUPPORTED_CHART || r ||
      d.status != TESS_UNSUPPORTED_CHART ||
      d.reason != TESS_DIAG_PROJECTION_COLLISION || d.axis != 2 ||
      d.charts_tried != 4 || d.vertex_a != 1 || d.vertex_b != 4 || d.ring != 0)
    return 1;
  in.vertex_count = 4;
  rings[1] = 4;
  xyz[8] = NAN;
  if (tess_triangulate(&in, &options, &r) != TESS_INVALID_INPUT || r ||
      d.reason != TESS_DIAG_COORDINATE || d.vertex_a != 2)
    return 2;
  xyz[8] = 1;
  options.strict_planar = 1;
  if (tess_triangulate(&in, &options, &r) != TESS_UNSUPPORTED_CHART || r ||
      d.reason != TESS_DIAG_NONPLANAR || d.vertex_a == SIZE_MAX)
    return 3;
  xyz[8] = 0;
  options.strict_planar = 0;
  if (tess_triangulate(&in, &options, &r) != TESS_OK || d.status != TESS_OK ||
      d.reason != TESS_DIAG_NONE)
    return 4;
  {
    uint32_t one = 1;
    tess_rational invalid = {-1, &one, 1, &one, 1};
    tess_quality q;
    if (tess_measure(r, &invalid, &q) != TESS_INVALID_INPUT ||
        tess_measure(r, NULL, &q) != TESS_OK)
      return 5;
  }
  tess_result_free(r);
  r = NULL;
  {
    const double fallback[] = {0, 0, .75, 3, 3, .125, 0, 3, 0, 2, 0, .625};
    tess_input tie = {fallback, 4, rings, 1};
    options.chart_axis = -1;
    if (tess_triangulate(&tie, &options, &r) != TESS_OK ||
        tess_chart_axis(r) != 0 || d.charts_tried != 5)
      return 6;
  }
  tess_result_free(r);
  return 0;
}

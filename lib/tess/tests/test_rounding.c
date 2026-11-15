#include <math.h>
#include <stdio.h>
#include <string.h>

#include "tess.h"
static int centroid(int narrow) {
  double xyz[] = {1, 0, 0, 2, 0, 0, 1, 1, 0}, out[12];
  size_t rings[] = {0, 3};
  tess_input in = {xyz, 3, rings, 1};
  tess_result* r = NULL;
  tess_remesh_options options = tess_default_remesh_options();
  tess_run_report report;
  tess_status status;
  if (narrow) xyz[3] = nextafter(1., 2.);
  if (tess_triangulate(&in, NULL, &r) != TESS_OK) return 0;
  options.target_count = 6;
  options.max_passes = 1;
  options.max_edits = 1;
  options.max_candidates = 8;
  status = tess_remesh(r, &options, &report);
  if ((status != TESS_VALID_TARGETS_MET &&
       status != TESS_VALID_TARGETS_UNMET) ||
      tess_vertex_count(r) != 4 || tess_triangle_count(r) != 3) {
    fprintf(stderr, "centroid setup %d: %d vertices %zu faces %zu\n", narrow,
            status, tess_vertex_count(r), tess_triangle_count(r));
    tess_result_free(r);
    return 0;
  }
  status = tess_export_binary64(r, out, 12);
  if (status != (narrow ? TESS_EXPORT_FAILURE : TESS_OK)) {
    fprintf(stderr, "centroid rounding %d: %d\n", narrow, status);
    tess_result_free(r);
    return 0;
  }
  tess_result_free(r);
  return 1;
}
int main(void) {
  uint32_t zero = 0, one = 1, three = 3;
  tess_rational xyz[9];
  size_t rings[] = {0, 3}, i;
  tess_exact_input in = {xyz, 3, rings, 1};
  tess_result* r = NULL;
  double out[9];
  for (i = 0; i < 9; i++) xyz[i] = (tess_rational){0, &zero, 0, &one, 1};
  xyz[3] = (tess_rational){1, &one, 1, &three, 1};
  xyz[7] = (tess_rational){1, &one, 1, &one, 1};
  if (tess_triangulate_exact(&in, NULL, &r) != TESS_OK ||
      tess_export_binary64(r, out, 9) != TESS_EXPORT_FAILURE)
    return 1;
  tess_result_free(r);
  r = NULL;
  {
    uint32_t large[35] = {0};
    large[34] = 1u << 12;
    xyz[3] = (tess_rational){1, large, 35, &one, 1};
    if (tess_triangulate_exact(&in, NULL, &r) != TESS_OK ||
        tess_export_binary64(r, out, 9) != TESS_EXPORT_FAILURE)
      return 2;
    tess_result_free(r);
    r = NULL;
  }
  {
    double large[] = {0, 0, 0, 1e200, 0, 0, 0, 1e200, 0};
    tess_input input = {large, 3, rings, 1};
    tess_quality q;
    if (tess_triangulate(&input, NULL, &r) != TESS_OK ||
        tess_measure(r, NULL, &q) != TESS_RESOURCE_LIMIT ||
        tess_export_binary64(r, out, 9) != TESS_OK)
      return 3;
    tess_result_free(r);
  }
  return !(centroid(0) && centroid(1));
}

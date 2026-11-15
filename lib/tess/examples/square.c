/* SPDX-License-Identifier: MIT. Build/link using only the public header. */
#include <stdio.h>
#include <stdlib.h>

#include "tess.h"
static int save(tess_result* r, const char* prefix, const char* kind,
                const double* rounded, size_t count) {
  char path[4096];
  FILE* stream;
  int ok;
  if (snprintf(path, sizeof(path), "%s.%s.tess", prefix, kind) >=
      (int)sizeof(path))
    return 0;
  stream = fopen(path, "wb");
  if (!stream) return 0;
  ok = (rounded ? tess_write_export_certificate(r, rounded, count, stream)
                : tess_write_certificate(r, stream)) == TESS_OK;
  if (fclose(stream)) ok = 0;
  return ok;
}
int main(int argc, char** argv) {
  const double xyz[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0};
  const size_t offsets[] = {0, 4};
  tess_input input = {xyz, 4, offsets, 1};
  tess_result* r = NULL;
  tess_remesh_options options = tess_default_remesh_options();
  tess_run_report report;
  tess_quality quality;
  tess_status status;
  double* rounded = NULL;
  int result = 1;
  const char* prefix = argc > 1 ? argv[1] : "square";
  options.target_count = 128;
  options.subdivide_boundary = 1;
  status = tess_triangulate(&input, NULL, &r);
  if (status != TESS_OK) goto end;
  status = tess_prepare_remesh(r, &options);
  if (status != TESS_OK || !save(r, prefix, "request", NULL, 0)) goto end;
  status = tess_remesh(r, NULL, &report);
  if (status != TESS_VALID_TARGETS_MET && status != TESS_VALID_TARGETS_UNMET)
    goto end;
  if (!save(r, prefix, "exact", NULL, 0)) goto end;
  rounded = malloc(tess_vertex_count(r) * 3 * sizeof(double));
  if (!rounded) goto end;
  if (tess_export_binary64(r, rounded, tess_vertex_count(r) * 3) != TESS_OK ||
      !save(r, prefix, "rounded", rounded, tess_vertex_count(r) * 3) ||
      tess_result_quality(r, &quality) != TESS_OK)
    goto end;
  printf("%zu triangles; CV %.6g; band %.6g; angle05 %.6g; %s\n",
         quality.triangles, quality.area_cv, quality.fraction_target_band,
         quality.min_angle_p05, tess_status_string(status));
  result = status == TESS_VALID_TARGETS_MET ? 0 : 4;
end:
  if (result == 1)
    fprintf(stderr, "example failed: %s\n", tess_status_string(status));
  free(rounded);
  tess_result_free(r);
  return result;
}

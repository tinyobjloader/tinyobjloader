#include <stdio.h>
#include <stdlib.h>

#include "tess.h"
static int run(const char* name, const double* xyz, size_t n) {
  size_t rings[] = {0, n};
  tess_input in = {xyz, n, rings, 1};
  tess_result* r = NULL;
  tess_options options = tess_default_options();
  tess_remesh_options remesh = tess_default_remesh_options();
  tess_run_report run;
  tess_quality quality, baseline;
  tess_rational target;
  tess_status status;
  options.max_operations = 2000000000;
  remesh.subdivide_boundary = 1;
  if (tess_triangulate(&in, &options, &r) != TESS_OK) return 1;
  if (tess_prepare_remesh(r, &remesh) != TESS_OK ||
      tess_target_area(r, &target) != TESS_OK ||
      tess_measure(r, &target, &baseline) != TESS_OK)
    return 6;
  status = tess_remesh(r, NULL, &run);
  tess_result_quality(r, &quality);
  fprintf(stderr,
          "%s status=%d stop=%d faces=%zu cv=%g band=%g angle05=%g edits=%zu "
          "candidates=%zu ops=%zu peak=%zu\n",
          name, status, run.stop_reason, quality.triangles, quality.area_cv,
          quality.fraction_target_band, quality.min_angle_p05, run.edits,
          run.candidates, quality.operations, quality.peak_bytes);
  if (status != TESS_VALID_TARGETS_MET || quality.area_cv > .30 ||
      quality.fraction_target_band < .9 || quality.min_angle_p05 < 20) {
    tess_result_free(r);
    return 2;
  }
  if (n == 6 && (baseline.area_cv <= 0 ||
                 quality.mean_squared_log_area_error >
                     .75 * baseline.mean_squared_log_area_error)) {
    tess_result_free(r);
    return 7;
  }
  fprintf(stderr, "%s log-area MSE: %.9g -> %.9g, reference deviation %.9g\n",
          name, baseline.mean_squared_log_area_error,
          quality.mean_squared_log_area_error, quality.max_reference_deviation);
  {
    FILE* file = tmpfile();
    long length;
    char* bytes;
    if (!file || tess_write_certificate(r, file) != TESS_OK) {
      if (file) fclose(file);
      tess_result_free(r);
      return 3;
    }
    length = ftell(file);
    rewind(file);
    bytes = malloc((size_t)length + 1);
    if (!bytes || fread(bytes, 1, (size_t)length, file) != (size_t)length) {
      free(bytes);
      fclose(file);
      tess_result_free(r);
      return 4;
    }
    fclose(file);
    bytes[length] = 0;
    status = tess_check_certificate(r, bytes, (size_t)length);
    if (status == TESS_OK) {
      size_t mutation;
      for (mutation = 0; mutation < (size_t)length; mutation += 997) {
        char saved = bytes[mutation];
        bytes[mutation] = '!';
        tess_status corrupt = tess_check_certificate(r, bytes, (size_t)length);
        bytes[mutation] = saved;
        if (corrupt != TESS_CERTIFICATE_REJECTED) {
          status = TESS_INTERNAL_ERROR;
          break;
        }
      }
      if (tess_check_certificate(r, bytes, (size_t)length - 1) !=
          TESS_CERTIFICATE_REJECTED)
        status = TESS_INTERNAL_ERROR;
    }
    free(bytes);
    if (status != TESS_OK) {
      fprintf(stderr, "remesh certificate rejected: %s\n",
              tess_status_string(status));
      tess_result_free(r);
      return 5;
    }
  }
  tess_result_free(r);
  return 0;
}
static int interior_refinement(void) {
  const double xyz[] = {0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 1, 0, 1, 2, 0, 0, 2, 0};
  const size_t rings[] = {0, 6};
  tess_input input = {xyz, 6, rings, 1};
  tess_result* r = NULL;
  tess_remesh_options options = tess_default_remesh_options();
  tess_run_report report;
  tess_rational target;
  tess_quality before, after;
  tess_status status;
  options.target_count = 32;
  options.max_passes = 1;
  options.max_edits = 4;
  options.max_candidates = 64;
  if (tess_triangulate(&input, NULL, &r) != TESS_OK) return 1;
  {
    size_t counts[6][6] = {{0}}, i, j, k, n = 0;
    tess_seed_feature features[8];
    for (i = 0; i < tess_triangle_count(r); i++) {
      size_t face[3];
      tess_triangle(r, i, face);
      for (k = 0; k < 3; k++) counts[face[k]][face[(k + 1) % 3]]++;
    }
    for (i = 0; i < 6; i++)
      for (j = i + 1; j < 6; j++)
        if (counts[i][j] && counts[j][i])
          features[n++] = (tess_seed_feature){i, j, 100 + i * 6 + j};
    if (tess_set_seed_features(r, features, n, NULL, 0) != TESS_OK) return 1;
  }
  if (tess_prepare_remesh(r, &options) != TESS_OK ||
      tess_target_area(r, &target) != TESS_OK ||
      tess_measure(r, &target, &before) != TESS_OK)
    return 1;
  status = tess_remesh(r, NULL, &report);
  if (tess_result_quality(r, &after) != TESS_OK ||
      (status != TESS_VALID_TARGETS_MET &&
       status != TESS_VALID_TARGETS_UNMET) ||
      !report.face_splits || before.area_cv <= 0 ||
      after.mean_squared_log_area_error >
          .75 * before.mean_squared_log_area_error ||
      tess_constraint_count(r) != 9) {
    fprintf(stderr, "interior gate status %d face splits %zu MSE %g -> %g\n",
            status, report.face_splits, before.mean_squared_log_area_error,
            after.mean_squared_log_area_error);
    tess_result_free(r);
    return 2;
  }
  fprintf(
      stderr,
      "fixed-boundary interior refinement MSE %.9g -> %.9g face splits %zu\n",
      before.mean_squared_log_area_error, after.mean_squared_log_area_error,
      report.face_splits);
  tess_result_free(r);
  return 0;
}
int main(void) {
  const double square[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0};
  const double concave[] = {0, 0, 0, 2, 0, 0, 2, 1, 0,
                            1, 1, 0, 1, 2, 0, 0, 2, 0};
  return run("square", square, 4) || run("concave-L", concave, 6) ||
         interior_refinement();
}

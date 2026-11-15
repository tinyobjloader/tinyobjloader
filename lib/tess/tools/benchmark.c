/* SPDX-License-Identifier: MIT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "tess.h"
static int save(tess_result* r, const char* directory, const char* name,
                const char* suffix) {
  char path[4096];
  FILE* f;
  int ok;
  if (!directory) return 1;
  if (snprintf(path, sizeof(path), "%s/%s.%s.tess", directory, name, suffix) >=
      (int)sizeof(path))
    return 0;
  f = fopen(path, "wb");
  if (!f) return 0;
  ok = tess_write_certificate(r, f) == TESS_OK;
  if (fclose(f)) ok = 0;
  return ok;
}
static void quality(const tess_quality* q) {
  printf(
      "{\"triangles\":%zu,\"vertices\":%zu,\"target_area\":%.17g,\"physical_"
      "area\":%.17g,"
      "\"area_cv\":%.17g,\"area_ratio_p05\":%.17g,\"area_ratio_p50\":%.17g,"
      "\"area_ratio_p95\":%.17g,"
      "\"min_angle_p05\":%.17g,\"min_angle_min\":%.17g,\"mean_ratio\":%.17g,"
      "\"fraction_target_band\":%.17g,"
      "\"mean_squared_log_area_error\":%.17g,\"max_reference_deviation\":%.17g,"
      "\"operations\":%zu,\"peak_core_bytes\":%zu}",
      q->triangles, q->vertices, q->target_area, q->total_area, q->area_cv,
      q->area_ratio_p05, q->area_ratio_p50, q->area_ratio_p95, q->min_angle_p05,
      q->min_angle_min, q->mean_ratio, q->fraction_target_band,
      q->mean_squared_log_area_error, q->max_reference_deviation, q->operations,
      q->peak_bytes);
}
static int run(const char* name, const double* xyz, size_t nv,
               const size_t* offsets, size_t nr, int mode,
               const char* directory) {
  tess_input in = {xyz, nv, offsets, nr};
  tess_options library = tess_default_options();
  tess_remesh_options options = tess_default_remesh_options();
  tess_result* r = NULL;
  tess_run_report report;
  tess_quality before, after;
  tess_rational target;
  tess_status status, export_status;
  double* rounded;
  clock_t start;
  double seconds;
  library.max_operations = 2000000000;
  library.max_faces = 1000;
  options.subdivide_boundary = 1;
  if (mode >= 2) {
    options.target_count = 32;
    options.max_passes = 1;
    options.max_edits = 16;
    options.max_candidates = 128;
  }
  if (mode == 1) {
    options.target_count = 32;
    options.subdivide_boundary = 0;
    options.max_passes = 1;
    options.max_edits = 4;
    options.max_candidates = 64;
  }
  if (mode == 3) options.height_tolerance = .5;
  if (mode == 5) {
    options.target_count = 1;
    options.subdivide_boundary = 0;
    options.max_passes = 8;
    options.max_edits = 1000;
    options.max_candidates = 1000;
  }
  if (mode == 4) {
    options.subdivide_boundary = 0;
    options.max_edits = 4;
    options.max_candidates = 32;
    library.max_faces = 16;
  }
  if (tess_triangulate(&in, &library, &r) != TESS_OK) return 0;
  if (mode == 1) {
    size_t counts[16][16] = {{0}}, i, j, k, n = 0;
    tess_seed_feature features[32];
    if (nv > 16) return 0;
    for (i = 0; i < tess_triangle_count(r); i++) {
      size_t face[3];
      tess_triangle(r, i, face);
      for (k = 0; k < 3; k++) counts[face[k]][face[(k + 1) % 3]]++;
    }
    for (i = 0; i < nv; i++)
      for (j = i + 1; j < nv; j++)
        if (counts[i][j] && counts[j][i])
          features[n++] = (tess_seed_feature){i, j, 100 + i * nv + j};
    if (tess_set_seed_features(r, features, n, NULL, 0) != TESS_OK) return 0;
  }
  if (tess_prepare_remesh(r, &options) != TESS_OK ||
      tess_target_area(r, &target) != TESS_OK ||
      tess_measure(r, &target, &before) != TESS_OK ||
      !save(r, directory, name, "request"))
    return 0;
  start = clock();
  status = tess_remesh(r, NULL, &report);
  seconds = (double)clock() / CLOCKS_PER_SEC - (double)start / CLOCKS_PER_SEC;
  if (tess_result_quality(r, &after) != TESS_OK ||
      (status != TESS_VALID_TARGETS_MET &&
       status != TESS_VALID_TARGETS_UNMET)) {
    fprintf(stderr, "benchmark %s failed status %d\n", name, status);
    tess_result_free(r);
    return 0;
  }
  if (!save(r, directory, name, "exact")) return 0;
  rounded = malloc(tess_vertex_count(r) * 3 * sizeof(double));
  if (!rounded) return 0;
  export_status = tess_export_binary64(r, rounded, tess_vertex_count(r) * 3);
  if (export_status == TESS_OK && directory) {
    char path[4096];
    FILE* f;
    if (snprintf(path, sizeof(path), "%s/%s.rounded.tess", directory, name) >=
        (int)sizeof(path))
      return 0;
    f = fopen(path, "wb");
    if (!f) return 0;
    if (tess_write_export_certificate(r, rounded, tess_vertex_count(r) * 3,
                                      f) != TESS_OK ||
        fclose(f))
      return 0;
  }
  free(rounded);
  printf(
      "{\"fixture\":\"%s\",\"target_count\":%zu,\"subdivide_boundary\":%s,"
      "\"height_tolerance\":%.17g,"
      "\"max_passes\":%zu,\"max_edits\":%zu,\"max_candidates\":%zu,\"max_"
      "faces\":%zu,\"max_operations\":%zu,"
      "\"outcome\":%d,\"stop_reason\":%d,\"termination\":%d,\"binary64_export_"
      "status\":%d,\"cpu_seconds\":%.9g,"
      "\"edits\":%zu,\"candidates\":%zu,\"validity_rejections\":%zu,"
      "\"objective_rejections\":%zu,\"batches\":%zu,"
      "\"edge_splits\":%zu,\"face_splits\":%zu,\"collapses\":%zu,\"flips\":%zu,"
      "\"relocations\":%zu,\"before\":",
      name, options.target_count, options.subdivide_boundary ? "true" : "false",
      options.height_tolerance, options.max_passes, options.max_edits,
      options.max_candidates, library.max_faces, library.max_operations, status,
      report.stop_reason, report.termination, export_status, seconds,
      report.edits, report.candidates, report.validity_rejections,
      report.objective_rejections, report.batches, report.edge_splits,
      report.face_splits, report.collapses, report.flips, report.relocations);
  quality(&before);
  printf(",\"after\":");
  quality(&after);
  puts("}");
  tess_result_free(r);
  return 1;
}
int main(int argc, char** argv) {
  const double square[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0};
  const double concave[] = {0, 0, 0, 2, 0, 0, 2, 1, 0,
                            1, 1, 0, 1, 2, 0, 0, 2, 0};
  const double warped[] = {0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0};
  const double thin[] = {0,    0,     0,    4, 0,     0,    4, 4,
                         0,    3.875, 4,    0, 3.875, .125, 0, .125,
                         .125, 0,     .125, 4, 0,     0,    4, 0};
  const double hole[] = {0, 0, 0, 4, 0, 0, 4, 4, 0, 0, 4, 0,
                         1, 1, 0, 1, 3, 0, 3, 3, 0, 3, 1, 0};
  const double acute[] = {0, 0, 0, 10, 0, 0, 0, .01, 0};
  const size_t three[] = {0, 3};
  const size_t four[] = {0, 4}, six[] = {0, 6}, eight[] = {0, 8},
               holes[] = {0, 4, 8};
  const char* directory = argc > 1 ? argv[1] : NULL;
  return !(run("square", square, 4, four, 1, 0, directory) &&
           run("concave-L", concave, 6, six, 1, 0, directory) &&
           run("interior-fixed-features", concave, 6, six, 1, 1, directory) &&
           run("warped-exact", warped, 4, four, 1, 2, directory) &&
           run("warped-approx", warped, 4, four, 1, 3, directory) &&
           run("thin-fixed", thin, 8, eight, 1, 4, directory) &&
           run("hole-fixed", hole, 8, holes, 2, 4, directory) &&
           run("acute-stagnant", acute, 3, three, 1, 5, directory));
}

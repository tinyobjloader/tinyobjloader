#include <stdio.h>
#include <stdlib.h>

#include "tess.h"
static int certificate(tess_result* r) {
  FILE* f = tmpfile();
  long length;
  char* bytes;
  tess_status status;
  if (!f || tess_write_certificate(r, f) != TESS_OK) return 0;
  length = ftell(f);
  rewind(f);
  bytes = malloc((size_t)length);
  if (!bytes || fread(bytes, 1, (size_t)length, f) != (size_t)length) return 0;
  status = tess_check_certificate(r, bytes, (size_t)length);
  free(bytes);
  fclose(f);
  return status == TESS_OK;
}
int main(void) {
  const double xyz[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0};
  const size_t rings[] = {0, 4};
  tess_input in = {xyz, 4, rings, 1};
  tess_result* r = NULL;
  tess_seed_feature features[2] = {{0, 1, 42}, {0, 0, 99}};
  tess_remesh_options options = tess_default_remesh_options();
  tess_run_report report;
  size_t faces[2][3], i, j, k, counts[4][4] = {{0}};
  if (tess_triangulate(&in, NULL, &r) != TESS_OK) return 1;
  for (i = 0; i < 2; i++) {
    if (tess_triangle(r, i, faces[i]) != TESS_OK) return 2;
    for (j = 0; j < 3; j++) counts[faces[i][j]][faces[i][(j + 1) % 3]]++;
  }
  for (i = 0; i < 4; i++)
    for (j = i + 1; j < 4; j++)
      if (counts[i][j] && counts[j][i]) {
        features[1].a = i;
        features[1].b = j;
      }
  if (tess_set_seed_features(r, features, 2, NULL, 0) != TESS_OK ||
      tess_constraint_count(r) != 5)
    return 3;
  {
    tess_seed_feature bad = {0, 99, 0};
    if (tess_set_seed_features(r, &bad, 1, NULL, 0) != TESS_INVALID_INPUT ||
        tess_constraint_count(r) != 5)
      return 4;
  }
  options.subdivide_boundary = options.subdivide_features = 1;
  if (tess_prepare_remesh(r, &options) != TESS_OK || !certificate(r)) return 5;
  if (tess_remesh(r, NULL, &report) != TESS_VALID_TARGETS_MET ||
      !certificate(r))
    return 6;
  /* Every protected diagonal/boundary child remains represented and tagged in
     the canonical certificate; the independent checker checks their chains. */
  for (k = 0; k < tess_constraint_count(r); k++) {
    size_t endpoints[2], source;
    if (tess_constraint(r, k, endpoints, &source) != TESS_OK) return 7;
  }
  if (tess_set_seed_features(r, features, 2, NULL, 0) != TESS_INVALID_INPUT)
    return 8;
  tess_result_free(r);
  return 0;
}

/* SPDX-License-Identifier: MIT. Baseline complexity/budget evidence. */
#include <stdio.h>
#include <time.h>

#include "tess.h"
int main(void) {
  const size_t sizes[] = {8, 16, 32, 64, 96, 128, 160, 192};
  size_t sample;
  for (sample = 0; sample < sizeof(sizes) / sizeof(sizes[0]); sample++) {
    double xyz[192 * 3];
    size_t n = sizes[sample], offsets[] = {0, n}, i;
    tess_input input = {xyz, n, offsets, 1};
    tess_options options = tess_default_options();
    tess_result* r = NULL;
    tess_diagnostic diagnostic;
    tess_status status;
    clock_t start;
    options.diagnostic = &diagnostic;
    options.chart_axis = 2;
    for (i = 0; i < n; i++) {
      xyz[3 * i] = (double)i;
      xyz[3 * i + 1] = (double)(i * i);
      xyz[3 * i + 2] = 0;
    }
    start = clock();
    status = tess_triangulate(&input, &options, &r);
    if (status != TESS_OK && status != TESS_RESOURCE_LIMIT) {
      fprintf(stderr, "resource sweep unexpected %d\n", status);
      return 1;
    }
    printf(
        "{\"vertices\":%zu,\"triangles\":%zu,\"status\":%d,\"operation_cap\":%"
        "zu,\"operations\":%zu,\"peak_construction_bytes\":%zu,\"cpu_seconds\":"
        "%.9g}\n",
        n, tess_triangle_count(r), status, options.max_operations,
        diagnostic.operations, diagnostic.peak_bytes,
        (double)clock() / CLOCKS_PER_SEC - (double)start / CLOCKS_PER_SEC);
    tess_result_free(r);
  }
  return 0;
}

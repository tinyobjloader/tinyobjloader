#include <stdio.h>
#include <stdlib.h>

#include "geometry.h"
typedef struct {
  size_t live, calls, fail;
} heap;
static void* alloc(size_t n, void* u) {
  heap* h = u;
  void* p;
  if (h->calls++ == h->fail) return NULL;
  p = malloc(n);
  if (p) h->live++;
  return p;
}
static void release(void* p, void* u) {
  heap* h = u;
  if (p) {
    h->live--;
    free(p);
  }
}
static int feature_failures(void) {
  const double xyz[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0};
  const size_t offsets[] = {0, 4},
               samples[] = {0,   1,    2,    10,    50,   100,
                            500, 1000, 3000, 10000, 30000};
  const tess_seed_feature features[] = {{0, 1, 42}, {0, 2, 99}};
  tess_input input = {xyz, 4, offsets, 1};
  size_t i, j;
  for (i = 0; i < sizeof(samples) / sizeof(samples[0]); i++) {
    heap h = {0, 0, SIZE_MAX};
    tess_result* r = NULL;
    tess_options options = tess_default_options();
    tess_status status;
    double exported[12];
    options.allocator = (tess_allocator){&h, alloc, release};
    if (tess_triangulate(&input, &options, &r) != TESS_OK) return 0;
    h.fail = h.calls + samples[i];
    status = tess_set_seed_features(r, features, 2, NULL, 0);
    h.fail = SIZE_MAX;
    if (status != TESS_OK && status != TESS_ALLOCATION_FAILURE) return 0;
    if (tess_constraint_count(r) != (status == TESS_OK ? 5u : 4u)) return 0;
    if (status != TESS_OK)
      for (j = 0; j < tess_constraint_count(r); j++) {
        tess_constraint_info info;
        if (tess_constraint_details(r, j, &info) != TESS_OK || info.tag)
          return 0;
      }
    if (tess_export_binary64(r, exported, 12) != TESS_OK) return 0;
    tess_result_free(r);
    if (h.live) return 0;
  }
  return 1;
}
int main(void) {
  size_t fail;
  if (!feature_failures()) return 6;
  double xyz[] = {0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 0};
  size_t offsets[] = {0, 4};
  tess_input in = {xyz, 4, offsets, 1};
  size_t samples[] = {0,   1,   2,   3,    4,    5,    10,    20,    50,
                      100, 200, 500, 1000, 2000, 5000, 10000, 20000, 40000};
  for (fail = 0; fail < sizeof(samples) / sizeof(samples[0]); fail++) {
    heap h = {0, 0, samples[fail]};
    tess_result* r = NULL;
    tess_options o = tess_default_options();
    tess_status s;
    o.allocator = (tess_allocator){&h, alloc, release};
    s = tess_triangulate(&in, &o, &r);
    if (s != TESS_OK && s != TESS_ALLOCATION_FAILURE) {
      fprintf(stderr, "unexpected %d at %zu\n", s, h.fail);
      return 1;
    }
    if (s != TESS_OK && r) return 2;
    tess_result_free(r);
    if (h.live) {
      fprintf(stderr, "leaked %zu at allocation %zu\n", h.live, h.fail);
      return 3;
    }
  }
  {
    tess_options o = tess_default_options();
    tess_result* r = NULL;
    o.max_operations = 1;
    if (tess_triangulate(&in, &o, &r) != TESS_RESOURCE_LIMIT || r) return 4;
    o = tess_default_options();
    o.max_bytes = 16;
    if (tess_triangulate(&in, &o, &r) != TESS_RESOURCE_LIMIT || r) return 5;
  }
  return 0;
}

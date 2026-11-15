/* Allocation failures during remeshing must retain an independently valid
   checkpoint and release all staged arithmetic/topology storage. */
#include <stdio.h>
#include <stdlib.h>

#include "edits.h"

typedef struct {
  size_t calls, fail, live;
} heap;
static void* allocate(size_t bytes, void* user) {
  heap* h = user;
  void* p;
  if (h->calls++ == h->fail) return NULL;
  p = malloc(bytes);
  if (p) h->live++;
  return p;
}
static void release(void* p, void* user) {
  heap* h = user;
  if (p) {
    h->live--;
    free(p);
  }
}
int main(void) {
  const double xyz[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0};
  const size_t rings[] = {0, 4};
  const size_t offsets[] = {0,     1,      2,      3,       10,      20,
                            50,    100,    300,    1000,    3000,    10000,
                            30000, 100000, 300000, 1000000, 10000000};
  tess_input input = {xyz, 4, rings, 1};
  size_t i;
  int saw_failure = 0, saw_commit_failure = 0;
  for (i = 0; i < sizeof(offsets) / sizeof(offsets[0]); i++) {
    heap h = {0, SIZE_MAX, 0};
    tess_options options = tess_default_options();
    tess_remesh_options remesh = tess_default_remesh_options();
    tess_result* r = NULL;
    tess_run_report report;
    tess_status status;
    options.allocator = (tess_allocator){&h, allocate, release};
    remesh.subdivide_boundary = 1;
    remesh.max_passes = 1;
    remesh.max_edits = 2;
    remesh.max_candidates = 4;
    if (tess_triangulate(&input, &options, &r) != TESS_OK ||
        tess_prepare_remesh(r, &remesh) != TESS_OK)
      return 1;
    h.fail = h.calls + offsets[i];
    status = tess_remesh(r, NULL, &report);
    h.fail = SIZE_MAX;
    if (status == TESS_ALLOCATION_FAILURE ||
        report.stop_reason == TESS_ALLOCATION_FAILURE) {
      saw_failure = 1;
      if (report.edits) saw_commit_failure = 1;
    }
    fprintf(stderr, "fault offset %zu: calls %zu edits %zu status %d stop %d\n",
            offsets[i], h.calls, report.edits, status, report.stop_reason);
    if (status != TESS_VALID_TARGETS_MET &&
        status != TESS_VALID_TARGETS_UNMET &&
        status != TESS_ALLOCATION_FAILURE) {
      fprintf(stderr, "unexpected rollback status %d at %zu\n", status,
              offsets[i]);
      return 2;
    }
    /* The independent test audit gets fresh fuel after the failed run. */
    r->mesh.c.status = TESS_OK;
    r->mesh.c.ops = 0;
    r->mesh.c.max_ops = 100000000;
    if (!tg_check_chains(&r->mesh, &r->seed, &r->remesh_options) ||
        !tg_validate(&r->mesh) || !tg_audit3(&r->mesh) ||
        !tg_reference(&r->mesh, &r->seed, &r->tolerance)) {
      fprintf(stderr, "invalid rollback at %zu\n", offsets[i]);
      return 3;
    }
    tess_result_free(r);
    if (h.live) {
      fprintf(stderr, "rollback leaked %zu blocks at %zu\n", h.live,
              offsets[i]);
      return 4;
    }
  }
  return !(saw_failure && saw_commit_failure);
}

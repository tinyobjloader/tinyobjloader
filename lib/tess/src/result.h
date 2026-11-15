/* SPDX-License-Identifier: MIT */
#ifndef TESS_RESULT_H
#define TESS_RESULT_H
#include "geometry.h"
struct tess_result {
  tm mesh, seed;
  tess_options options;
  tx control;
  qr target, tolerance, split_threshold, batch_threshold, deviation;
  int remeshed;
  size_t *allowed_owners, allowed_count, control_ops_total, peak_bytes;
  tess_quality quality;
  tess_remesh_options remesh_options;
};
int tm_clone(tm* destination, const tm* source);
#endif

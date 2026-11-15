/* SPDX-License-Identifier: MIT */
#ifndef TESS_BOUNDS_H
#define TESS_BOUNDS_H
#include "geometry.h"
typedef struct {
  size_t low[3], high[3];
} tbounds;
tbounds* tg_bounds(tm* mesh);
int tg_boxes_separate(tm* mesh, const tbounds* a, const tbounds* b,
                      unsigned axes);
#endif

/* SPDX-License-Identifier: MIT */
#ifndef TESS_METRICS_H
#define TESS_METRICS_H
#include "geometry.h"
void tg_triangle_squared(tx* c, const tv* vertices, const tf* face, qr* out);
void tg_length_squared(tx* c, const tv* vertices, size_t a, size_t b, qr* out);
int tg_count_target(tm* work, const tm* reference, size_t count, qr* target);
int tg_face_objective(tx* c, const tv* vertices, const tf* face,
                      const qr* target, long double* value);
tess_status tg_quality(tm* mesh, const qr* target, tess_quality* report);
#endif

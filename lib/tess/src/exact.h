/* SPDX-License-Identifier: MIT */
#ifndef TESS_EXACT_H
#define TESS_EXACT_H
#include <stdio.h>

#include "tess.h"
typedef struct {
  size_t max_limbs, max_bytes, max_ops;
  size_t bytes, peak, ops;
  tess_status status;
  size_t fail_after, allocations;
  tess_allocator allocator;
} tx;
typedef struct {
  uint32_t* v;
  size_t n;
  int sign;
} zi;
typedef struct {
  zi n, d;
} qr;
void tx_init(tx* c);
int tx_binary64_supported(void);
int tx_report_double(long double value, double* out);
void* tx_alloc(tx* c, size_t n, size_t size);
void tx_free(tx* c, void* p, size_t bytes);
void zi_clear(tx* c, zi* a);
void zi_i64(tx* c, zi* a, int64_t v);
void zi_copy(tx* c, zi* r, const zi* a);
int zi_cmp(const zi* a, const zi* b);
void zi_add(tx* c, zi* r, const zi* a, const zi* b);
void zi_sub(tx* c, zi* r, const zi* a, const zi* b);
void zi_mul(tx* c, zi* r, const zi* a, const zi* b);
void zi_divrem(tx* c, zi* q, zi* r, const zi* a, const zi* b);
void qr_import(tx* c, qr* r, const tess_rational* input);
void qr_clear(tx* c, qr* a);
void qr_i64(tx* c, qr* r, int64_t n);
void qr_copy(tx* c, qr* r, const qr* a);
void qr_double(tx* c, qr* r, double d);
void qr_add(tx* c, qr* r, const qr* a, const qr* b);
void qr_sub(tx* c, qr* r, const qr* a, const qr* b);
void qr_mul(tx* c, qr* r, const qr* a, const qr* b);
void qr_div(tx* c, qr* r, const qr* a, const qr* b);
int qr_cmp(tx* c, const qr* a, const qr* b);
void qr_mid(tx* c, qr* r, const qr* a, const qr* b);
long double qr_approx(const qr* a);
void qr_write(FILE* f, const qr* a);
void qr_read(tx* c, qr* a, FILE* f);
/* Certified rational brackets; no floating-point decision is used. */
int qr_exponent(const qr* a);
void qr_scale_pow2(tx* c, qr* r, const qr* a, int exponent);
void qr_sqrt_bounds(tx* c, const qr* a, unsigned precision, qr* lower,
                    qr* upper);
void qr_round_dyadic(tx* c, qr* r, const qr* a, int step_exponent);
void qr_size(tx* c, qr* r, size_t value);

#endif

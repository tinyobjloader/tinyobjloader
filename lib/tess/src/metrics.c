/* SPDX-License-Identifier: MIT */
#include "metrics.h"
void tg_triangle_squared(tx* c, const tv* v, const tf* f, qr* out) {
  qr ab[3] = {0}, ac[3] = {0}, x = {0}, y = {0}, z = {0}, four = {0};
  size_t j;
  qr_i64(c, out, 0);
  for (j = 0; j < 3; j++) {
    qr_sub(c, &ab[j], &v[f->v[1]].p[j], &v[f->v[0]].p[j]);
    qr_sub(c, &ac[j], &v[f->v[2]].p[j], &v[f->v[0]].p[j]);
  }
  for (j = 0; j < 3; j++) {
    qr_mul(c, &x, &ab[(j + 1) % 3], &ac[(j + 2) % 3]);
    qr_mul(c, &y, &ab[(j + 2) % 3], &ac[(j + 1) % 3]);
    qr_sub(c, &z, &x, &y);
    qr_mul(c, &z, &z, &z);
    qr_add(c, out, out, &z);
  }
  qr_i64(c, &four, 4);
  qr_div(c, out, out, &four);
  for (j = 0; j < 3; j++) {
    qr_clear(c, &ab[j]);
    qr_clear(c, &ac[j]);
  }
  qr_clear(c, &x);
  qr_clear(c, &y);
  qr_clear(c, &z);
  qr_clear(c, &four);
}
void tg_length_squared(tx* c, const tv* v, size_t a, size_t b, qr* out) {
  qr delta = {0};
  size_t j;
  qr_i64(c, out, 0);
  for (j = 0; j < 3; j++) {
    qr_sub(c, &delta, &v[a].p[j], &v[b].p[j]);
    qr_mul(c, &delta, &delta, &delta);
    qr_add(c, out, out, &delta);
  }
  qr_clear(c, &delta);
}
/* Count targets use a single dyadic grid of approximately 40 significant
   bits. Round-to-nearest, ties upward. Refine certified area brackets until
   both endpoints round to the same positive rational. */
int tg_count_target(tm* work, const tm* reference, size_t count, qr* target) {
  tx* c = &work->c;
  qr low = {0}, high = {0}, lo = {0}, hi = {0}, squared = {0}, divisor = {0},
     roundedLo = {0}, roundedHi = {0};
  unsigned precision;
  size_t i;
  int exponent = 0, ok = 0, gridChosen = 0;
  if (!count) {
    c->status = TESS_INVALID_INPUT;
    return 0;
  }
  qr_size(c, &divisor, count);
  for (precision = 64; precision <= 4096 && !c->status; precision *= 2) {
    qr_i64(c, &low, 0);
    qr_i64(c, &high, 0);
    for (i = 0; i < reference->nf && !c->status; i++) {
      tg_triangle_squared(c, reference->v, &reference->f[i], &squared);
      qr_sqrt_bounds(c, &squared, precision, &lo, &hi);
      qr_add(c, &low, &low, &lo);
      qr_add(c, &high, &high, &hi);
    }
    qr_div(c, &low, &low, &divisor);
    qr_div(c, &high, &high, &divisor);
    if (!gridChosen) {
      exponent = qr_exponent(&high) - 40;
      gridChosen = 1;
    }
    qr_round_dyadic(c, &roundedLo, &low, exponent);
    qr_round_dyadic(c, &roundedHi, &high, exponent);
    if (roundedLo.n.sign > 0 && !qr_cmp(c, &roundedLo, &roundedHi)) {
      qr_copy(c, target, &roundedLo);
      ok = !c->status;
      break;
    }
  }
  qr_clear(c, &low);
  qr_clear(c, &high);
  qr_clear(c, &lo);
  qr_clear(c, &hi);
  qr_clear(c, &squared);
  qr_clear(c, &divisor);
  qr_clear(c, &roundedLo);
  qr_clear(c, &roundedHi);
  if (!ok && !c->status) c->status = TESS_RESOURCE_LIMIT;
  return ok;
}

#include <math.h>
#include <stdlib.h>
#include <string.h>
int tg_face_objective(tx* c, const tv* vertices, const tf* face,
                      const qr* target, long double* value) {
  qr squared = {0}, length = {0};
  long double area, sum = 0, ratio, shape, logarithm, t = qr_approx(target);
  size_t k;
  int ok = 0;
  tg_triangle_squared(c, vertices, face, &squared);
  area = sqrtl(qr_approx(&squared));
  for (k = 0; k < 3 && !c->status; k++) {
    tg_length_squared(c, vertices, face->v[k], face->v[(k + 1) % 3], &length);
    sum += qr_approx(&length);
  }
  if (!c->status && area > 0 && t > 0 && sum > 0 && isfinite(area) &&
      isfinite(t) && isfinite(sum)) {
    ratio = area / t;
    shape = 4 * sqrtl(3.L) * area / sum;
    logarithm = logl(ratio);
    *value = logarithm * logarithm + .02L * (1 - shape) * (1 - shape);
    ok = isfinite(*value);
  }
  qr_clear(c, &squared);
  qr_clear(c, &length);
  if (!ok && !c->status) c->status = TESS_RESOURCE_LIMIT;
  return ok && !c->status;
}
static int order_metric(const void* a, const void* b) {
  long double x = *(const long double*)a, y = *(const long double*)b;
  return x > y ? 1 : x < y ? -1 : 0;
}
static long double percentile(const long double* v, size_t n, long double p) {
  long double index = p * (n - 1), part;
  size_t low = (size_t)index, high = low + 1 < n ? low + 1 : low;
  part = index - low;
  return v[low] * (1 - part) + v[high] * part;
}
tess_status tg_quality(tm* m, const qr* target, tess_quality* out) {
  long double *areas = NULL, *angles = NULL, sum = 0, shape = 0, objective = 0,
              variance = 0, targetValue = target ? qr_approx(target) : 0,
              band = 0, minAngle = 180, meanRatio = 0;
  qr squared = {0}, length = {0};
  size_t i, k;
  int numeric = 1;
  tess_status status = TESS_OK;
  const long double pi = acosl(-1.0L);
  memset(out, 0, sizeof(*out));
  if (!m->nf || (target && target->n.sign <= 0)) return TESS_INVALID_INPUT;
  areas = tx_alloc(&m->c, m->nf, sizeof(long double));
  angles = tx_alloc(&m->c, m->nf, sizeof(long double));
  if (!areas || !angles) goto end;
  for (i = 0; i < m->nf && !m->c.status; i++) {
    long double l[3], area, smallest = 180, q;
    tg_triangle_squared(&m->c, m->v, &m->f[i], &squared);
    area = sqrtl(qr_approx(&squared));
    if (!(area > 0) || !isfinite(area)) {
      numeric = 0;
      break;
    }
    areas[i] = area;
    sum += area;
    for (k = 0; k < 3; k++) {
      tg_length_squared(&m->c, m->v, m->f[i].v[k], m->f[i].v[(k + 1) % 3],
                        &length);
      l[k] = qr_approx(&length);
      if (!(l[k] > 0) || !isfinite(l[k])) numeric = 0;
    }
    if (!numeric) break;
    for (k = 0; k < 3; k++) {
      long double cosine = (l[k] + l[(k + 2) % 3] - l[(k + 1) % 3]) /
                           (2 * sqrtl(l[k] * l[(k + 2) % 3]));
      long double angle;
      if (!isfinite(cosine)) {
        numeric = 0;
        break;
      }
      if (cosine > 1) cosine = 1;
      if (cosine < -1) cosine = -1;
      angle = acosl(cosine) * 180 / pi;
      if (angle < smallest) smallest = angle;
    }
    angles[i] = smallest;
    if (smallest < minAngle) minAngle = smallest;
    q = 4 * sqrtl(3.0L) * area / (l[0] + l[1] + l[2]);
    shape += (1 - q) * (1 - q);
    meanRatio += q;
  }
  if (m->c.status) goto end;
  if (!numeric || !isfinite(sum) || !(sum > 0)) {
    status = TESS_RESOURCE_LIMIT;
    goto end;
  }
  if (!target) targetValue = sum / m->nf;
  if (!(targetValue > 0) || !isfinite(targetValue)) {
    status = TESS_RESOURCE_LIMIT;
    goto end;
  }
  for (i = 0; i < m->nf; i++) {
    long double delta = areas[i] / (sum / m->nf) - 1,
                ratio = areas[i] / targetValue, logarithm = logl(ratio);
    variance += delta * delta;
    objective += logarithm * logarithm;
    if (ratio >= .5L && ratio <= 1.5L) band++;
    areas[i] = ratio;
  }
  qsort(areas, m->nf, sizeof(long double), order_metric);
  qsort(angles, m->nf, sizeof(long double), order_metric);
  out->vertices = m->nv;
  out->triangles = m->nf;
  if (!tx_report_double(targetValue, &out->target_area) ||
      !tx_report_double(sum, &out->total_area) ||
      !tx_report_double(sqrtl(variance / m->nf), &out->area_cv) ||
      !tx_report_double(percentile(areas, m->nf, .05L), &out->area_ratio_p05) ||
      !tx_report_double(percentile(areas, m->nf, .5L), &out->area_ratio_p50) ||
      !tx_report_double(percentile(areas, m->nf, .95L), &out->area_ratio_p95) ||
      !tx_report_double(percentile(angles, m->nf, .05L), &out->min_angle_p05) ||
      !tx_report_double(minAngle, &out->min_angle_min) ||
      !tx_report_double(meanRatio / m->nf, &out->mean_ratio) ||
      !tx_report_double(objective / m->nf, &out->mean_squared_log_area_error) ||
      !tx_report_double(band / m->nf, &out->fraction_target_band) ||
      !tx_report_double((objective + .02L * shape) / m->nf, &out->objective))
    status = TESS_RESOURCE_LIMIT;

end:
  qr_clear(&m->c, &squared);
  qr_clear(&m->c, &length);
  tx_free(&m->c, areas, m->nf * sizeof(long double));
  tx_free(&m->c, angles, m->nf * sizeof(long double));
  out->operations = m->c.ops;
  out->peak_bytes = m->c.peak;
  if (m->c.status) status = m->c.status;
  return status;
}

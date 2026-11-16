/* SPDX-License-Identifier: MIT */
#include "tess.h"

#include <limits.h>
static int sub(int64_t a, int64_t b, int64_t* r) {
  if ((b > 0 && a < INT64_MIN + b) || (b < 0 && a > INT64_MAX + b)) return 0;
  *r = a - b;
  return 1;
}
static uint64_t mag(int64_t a) {
  return a < 0 ? (uint64_t)(-(a + 1)) + UINT64_C(1) : (uint64_t)a;
}
static int mul(int64_t a, int64_t b, int64_t* r) {
  uint64_t x = mag(a), y = mag(b), z;
  int neg = (a < 0) != (b < 0);
  uint64_t cap = neg ? (uint64_t)INT64_MAX + 1 : (uint64_t)INT64_MAX;
  if (y && x > cap / y) return 0;
  z = x * y;
  if (neg && z == (uint64_t)INT64_MAX + 1)
    *r = INT64_MIN;
  else
    *r = neg ? -(int64_t)z : (int64_t)z;
  return 1;
}
/* Checked orientation determinant over int64 coordinates: returns 1 and stores the sign, or 0 when an
 * intermediate value overflows (statement-level calls so that it can be translated and proved). */
static int orient2i_core(int64_t ax, int64_t ay, int64_t bx, int64_t by, int64_t cx, int64_t cy,
                         int* sign) {
  int64_t x, y, u, v, p, q, d;
  int ok;
  ok = sub(bx, ax, &x);
  if (!ok) return 0;
  ok = sub(by, ay, &y);
  if (!ok) return 0;
  ok = sub(cx, ax, &u);
  if (!ok) return 0;
  ok = sub(cy, ay, &v);
  if (!ok) return 0;
  ok = mul(x, v, &p);
  if (!ok) return 0;
  ok = mul(y, u, &q);
  if (!ok) return 0;
  ok = sub(p, q, &d);
  if (!ok) return 0;
  *sign = (d > 0) - (d < 0);
  return 1;
}
tess_status tess_orient2i(tess_point2i a, tess_point2i b, tess_point2i c,
                          int* sign) {
  if (!sign) return TESS_INVALID_INPUT;
  if (!orient2i_core(a.x, a.y, b.x, b.y, c.x, c.y, sign)) return TESS_RESOURCE_LIMIT;
  return TESS_OK;
}
const char* tess_status_string(tess_status s) {
  switch (s) {
    case TESS_OK:
      return "ok";
    case TESS_INVALID_INPUT:
      return "invalid input";
    case TESS_UNSUPPORTED_CHART:
      return "unsupported chart";
    case TESS_RESOURCE_LIMIT:
      return "resource limit";
    case TESS_ALLOCATION_FAILURE:
      return "allocation failure";
    case TESS_INTERNAL_ERROR:
      return "internal error";
    case TESS_VALID_TARGETS_UNMET:
      return "valid; targets unmet";
    case TESS_VALID_TARGETS_MET:
      return "valid; targets met";
    case TESS_CERTIFICATE_REJECTED:
      return "certificate rejected";
    case TESS_IO_ERROR:
      return "I/O error";
    case TESS_EXPORT_FAILURE:
      return "export failure";
    default:
      return "unknown status";
  }
}

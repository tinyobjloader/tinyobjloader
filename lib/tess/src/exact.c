/* SPDX-License-Identifier: MIT */
#include "exact.h"

#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

#include "exact_core.c"
_Static_assert(CHAR_BIT == 8 && sizeof(uint32_t) == 4 && sizeof(uint64_t) == 8,
               "tess requires 8-bit bytes and exact 32/64-bit limbs");
void tx_init(tx* c) {
  memset(c, 0, sizeof(*c));
  c->max_limbs = 4096;
  c->max_bytes = 256 * 1024 * 1024;
  c->max_ops = 100000000;
  c->fail_after = SIZE_MAX;
}
static int tick(tx* c, size_t n) {
  if (c->status) return 0;
  if (n > c->max_ops - c->ops) {
    c->status = TESS_RESOURCE_LIMIT;
    return 0;
  }
  c->ops += n;
  return 1;
}
void* tx_alloc(tx* c, size_t n, size_t s) {
  void* p;
  size_t b;
  if (c->status) return NULL;
  if (s && n > SIZE_MAX / s) {
    c->status = TESS_RESOURCE_LIMIT;
    return NULL;
  }
  b = n * s;
  if (b > c->max_bytes - c->bytes) {
    c->status = TESS_RESOURCE_LIMIT;
    return NULL;
  }
  if (c->allocations++ >= c->fail_after) {
    c->status = TESS_ALLOCATION_FAILURE;
    return NULL;
  }
  p = c->allocator.allocate
          ? c->allocator.allocate(b ? b : 1, c->allocator.user)
          : malloc(b ? b : 1);
  if (!p) {
    c->status = TESS_ALLOCATION_FAILURE;
    return NULL;
  }
  memset(p, 0, b);
  c->bytes += b;
  if (c->bytes > c->peak) c->peak = c->bytes;
  return p;
}
void tx_free(tx* c, void* p, size_t b) {
  if (p) {
    if (c->allocator.release)
      c->allocator.release(p, c->allocator.user);
    else
      free(p);
    c->bytes -= b;
  }
}
void zi_clear(tx* c, zi* a) {
  tx_free(c, a->v, a->n * sizeof(uint32_t));
  memset(a, 0, sizeof(*a));
}
/* Allocated length equals n; normalization shrinks accounting only after a
 * copy. */
/* Number of limbs after dropping most-significant zero limbs. Pure; translated and proved
 * against the Lean `trimL` model. */
static size_t trim_len(const zi* a) {
  size_t n = a->n;
  while (n && !a->v[n - 1]) n--;
  return n;
}
static void norm(tx* c, zi* a) {
  size_t n = trim_len(a);
  if (n != a->n) {
    zi t = {0};
    if (n) {
      t.v = tx_alloc(c, n, 4);
      if (t.v) {
        memcpy(t.v, a->v, n * 4);
        t.n = n;
        t.sign = a->sign;
      }
    }
    zi_clear(c, a);
    *a = t;
  }
  if (!a->n) a->sign = 0;
}
static zi make(tx* c, size_t n) {
  zi z = {0};
  if (n > c->max_limbs) {
    if (!c->status) c->status = TESS_RESOURCE_LIMIT;
    return z;
  }
  if (n) {
    z.v = tx_alloc(c, n, 4);
    if (z.v) {
      z.n = n;
      z.sign = 1;
    }
  }
  return z;
}
static void move(tx* c, zi* r, zi* t) {
  zi_clear(c, r);
  *r = *t;
  memset(t, 0, sizeof(*t));
}
/* Limb count and limb/sign fill of an int64 magnitude (pure; translated and proved). */
static size_t i64_limb_count(uint64_t u) { return u > UINT32_MAX ? 2 : u ? 1 : 0; }
static void i64_fill(zi* t, int64_t x, uint64_t u) {
  if (t->n) {
    t->v[0] = (uint32_t)u;
    if (t->n == 2) t->v[1] = (uint32_t)(u >> 32);
    t->sign = x < 0 ? -1 : 1;
  }
}
void zi_i64(tx* c, zi* a, int64_t x) {
  uint64_t u = tess_mag(x);
  zi t = make(c, i64_limb_count(u));
  i64_fill(&t, x, u);
  move(c, a, &t);
}
void zi_copy(tx* c, zi* r, const zi* a) {
  zi t = make(c, a->n);
  if (t.n) {
    memcpy(t.v, a->v, a->n * 4);
    t.sign = a->sign;
  }
  move(c, r, &t);
}
/* Limb kernels split out for exact verification. These helpers carry no
   allocator state and are the translation boundary for the c2lean MiniC
   refinement. They perform exactly the bit arithmetic that used to be
   inlined in zi_add and zi_mul. */
static void zi_add_equisign(zi* t, const zi* a, const zi* b, size_t n) {
  size_t i;
  uint64_t carry = 0;
  for (i = 0; i < n; i++) {
    uint64_t v = carry + (i < a->n ? a->v[i] : 0) +
                 (uint64_t)(i < b->n ? b->v[i] : 0);
    t->v[i] = (uint32_t)v;
    carry = v >> 32;
  }
  t->v[n] = (uint32_t)carry;
}
static void zi_add_mixed(zi* t, const zi* x, const zi* y, size_t n) {
  size_t i;
  uint64_t carry = 0;
  for (i = 0; i < n; i++) {
    uint64_t xv = i < x->n ? x->v[i] : 0,
             yv = (uint64_t)(i < y->n ? y->v[i] : 0) + carry;
    t->v[i] = (uint32_t)(xv - yv);
    carry = xv < yv;
  }
}
static void zi_mul_accumulate(zi* t, const zi* a, const zi* b) {
  size_t i, j;
  for (i = 0; i < a->n; i++) {
    uint64_t k = 0;
    for (j = 0; j < b->n; j++) {
      uint64_t v = tess_limb_madd(a->v[i], b->v[j], t->v[i + j], (uint32_t)k);
      t->v[i + j] = (uint32_t)v;
      k = v >> 32;
    }
    t->v[i + b->n] = (uint32_t)k;
  }
}
static int acmp(const zi* a, const zi* b) {
  size_t i;
  if (a->n != b->n) return a->n > b->n ? 1 : -1;
  for (i = a->n; i; i--)
    if (a->v[i - 1] != b->v[i - 1]) return a->v[i - 1] > b->v[i - 1] ? 1 : -1;
  return 0;
}
int zi_cmp(const zi* a, const zi* b) {
  if (a->sign != b->sign) return a->sign > b->sign ? 1 : -1;
  return a->sign * acmp(a, b);
}
void zi_add(tx* c, zi* r, const zi* a, const zi* b) {
  zi t = {0};
  size_t n = a->n > b->n ? a->n : b->n;
  if (!tick(c, n)) return;
  if (!a->sign) {
    zi_copy(c, r, b);
    return;
  }
  if (!b->sign) {
    zi_copy(c, r, a);
    return;
  }
  if (a->sign == b->sign) {
    t = make(c, n + 1);
    if (t.v) {
      zi_add_equisign(&t, a, b, n);
      t.sign = a->sign;
    }
  } else {
    const zi *x = a, *y = b;
    if (acmp(a, b) < 0) {
      x = b;
      y = a;
    }
    t = make(c, n);
    if (t.v) {
      zi_add_mixed(&t, x, y, n);
      t.sign = x->sign;
    }
  }
  norm(c, &t);
  move(c, r, &t);
}
void zi_sub(tx* c, zi* r, const zi* a, const zi* b) {
  zi nb = *b;
  nb.sign = -nb.sign;
  zi_add(c, r, a, &nb);
}
void zi_mul(tx* c, zi* r, const zi* a, const zi* b) {
  zi t = {0};
  if (!a->n || !b->n) {
    move(c, r, &t);
    return;
  }
  if (a->n > SIZE_MAX / b->n) {
    if (!c->status) c->status = TESS_RESOURCE_LIMIT;
    return;
  }
  if (!tick(c, a->n * b->n)) return;
  t = make(c, a->n + b->n);
  if (t.v) {
    zi_mul_accumulate(&t, a, b);
    t.sign = a->sign * b->sign;
  }
  norm(c, &t);
  move(c, r, &t);
}
/* Radix-2^32 schoolbook division of `a` by the single limb `d` (pure; translated and proved
 * against the Lean `ldRun` model). Writes the quotient limbs into t and returns the remainder. */
static uint64_t div_single_fill(zi* t, const zi* a, uint32_t d) {
  uint64_t remainder = 0;
  size_t i;
  for (i = a->n; i; i--) {
    uint64_t value = (remainder << 32) | a->v[i - 1];
    t->v[i - 1] = (uint32_t)(value / d);
    remainder = value % d;
  }
  return remainder;
}
/* In-place `r = 2*r + k` over the limbs of r (k is 0 or 1); returns the carry out of the top limb
 * (pure; translated and proved against the Lean `siPrefix` model). */
static uint64_t div_shift_in(zi* r, uint64_t k) {
  size_t i;
  for (i = 0; i < r->n; i++) {
    uint64_t v = ((uint64_t)r->v[i] << 1) | k;
    r->v[i] = (uint32_t)v;
    k = v >> 32;
  }
  return k;
}
/* In-place `r -= b` over the limbs of r (b has no more limbs than r); returns the final borrow
 * (pure; translated and proved against the Lean `sbPrefix` model). */
static uint64_t div_sub_in(zi* r, const zi* b) {
  uint64_t borrow = 0;
  size_t i;
  for (i = 0; i < r->n; i++) {
    uint64_t x = r->v[i], y = (uint64_t)(i < b->n ? b->v[i] : 0) + borrow;
    r->v[i] = (uint32_t)(x - y);
    borrow = x < y;
  }
  return borrow;
}
/* Compare r (b->n + 1 limbs) with b: 1 if r > b, 0 if equal, -1 if r < b (pure; translated and proved
 * against the Lean `dcCmp` model). */
static int div_cmp(const zi* r, const zi* b) {
  size_t i;
  int cmp = r->v[b->n] ? 1 : 0;
  if (!cmp) {
    for (i = b->n; i; i--)
      if (r->v[i - 1] != b->v[i - 1]) {
        cmp = r->v[i - 1] > b->v[i - 1] ? 1 : -1;
        break;
      }
  }
  return cmp;
}
/* Binary long division; nonnegative remainder for nonnegative operands. */
void zi_divrem(tx* c, zi* q, zi* r, const zi* a, const zi* b) {
  zi qt = {0}, rt = {0};
  size_t bit;
  if (!b->n) {
    if (!c->status) c->status = TESS_INVALID_INPUT;
    return;
  }
  if (b->n == 1) {
    uint64_t remainder;
    if (!tick(c, a->n)) return;
    qt = make(c, a->n);
    if (a->n && !qt.v) goto done;
    remainder = div_single_fill(&qt, a, b->v[0]);
    qt.sign = a->sign * b->sign;
    if (remainder) {
      rt = make(c, 1);
      if (rt.v) {
        rt.v[0] = (uint32_t)remainder;
        rt.sign = a->sign;
      }
    }
    norm(c, &qt);
    goto done;
  }
  qt = make(c, a->n);
  rt = make(c, b->n + 1);
  if ((a->n && !qt.v) || !rt.v) goto done;
  for (bit = a->n * 32; bit && !c->status;) {
    uint64_t k;
    int cmp;
    bit--;
    if (!tick(c, rt.n)) break;
    k = (a->v[bit / 32] >> (bit % 32)) & 1u;
    (void)div_shift_in(&rt, k);
    cmp = div_cmp(&rt, b);
    if (cmp >= 0) {
      (void)div_sub_in(&rt, b);
      qt.v[bit / 32] |= UINT32_C(1) << (bit % 32);
    }
  }
  qt.sign = a->sign * b->sign;
  rt.sign = a->sign;
  norm(c, &qt);
  norm(c, &rt);
done:
  move(c, q, &qt);
  move(c, r, &rt);
}
void qr_clear(tx* c, qr* a) {
  zi_clear(c, &a->n);
  zi_clear(c, &a->d);
}
static void qm(tx* c, qr* r, qr* a) {
  qr_clear(c, r);
  *r = *a;
  memset(a, 0, sizeof(*a));
}
static void reduce(tx* c, qr* a) {
  zi x = {0}, y = {0}, q = {0}, r = {0};
  if (c->status) return;
  if (!a->d.n) {
    c->status = TESS_INVALID_INPUT;
    return;
  }
  if (a->d.sign < 0) {
    a->d.sign = 1;
    a->n.sign = -a->n.sign;
  }
  if (!a->n.n) {
    zi_i64(c, &a->d, 1);
    return;
  }
  if (a->d.n == 1 && a->d.v[0] == 1) return;
  zi_copy(c, &x, &a->n);
  x.sign = 1;
  zi_copy(c, &y, &a->d);
  while (y.n && !c->status) {
    zi_divrem(c, &q, &r, &x, &y);
    move(c, &x, &y);
    move(c, &y, &r);
  }
  if (!c->status) {
    zi_divrem(c, &q, &r, &a->n, &x);
    move(c, &a->n, &q);
    zi_divrem(c, &q, &r, &a->d, &x);
    move(c, &a->d, &q);
  }
  zi_clear(c, &x);
  zi_clear(c, &y);
  zi_clear(c, &q);
  zi_clear(c, &r);
}
void qr_i64(tx* c, qr* r, int64_t n) {
  qr t = {0};
  zi_i64(c, &t.n, n);
  zi_i64(c, &t.d, 1);
  qm(c, r, &t);
}
void qr_copy(tx* c, qr* r, const qr* a) {
  qr t = {0};
  zi_copy(c, &t.n, &a->n);
  zi_copy(c, &t.d, &a->d);
  qm(c, r, &t);
}
/* Limb carry chain of a left shift into a zeroed destination of a->n + bits/32 + 1
 * limbs (pure; translated and proved against the Lean `shiftLimbs` model). */
static void shift_fill(zi* t, const zi* a, unsigned bits) {
  size_t i;
  uint64_t carry = 0;
  for (i = 0; i < a->n; i++) {
    uint64_t v = ((uint64_t)a->v[i] << (bits % 32)) | carry;
    t->v[i + bits / 32] = (uint32_t)v;
    carry = v >> 32;
  }
  t->v[a->n + bits / 32] = (uint32_t)carry;
}
static void shift(tx* c, zi* r, const zi* a, unsigned bits) {
  zi t = make(c, a->n + bits / 32 + 1);
  if (t.v) {
    shift_fill(&t, a, bits);
    t.sign = a->sign;
  }
  norm(c, &t);
  move(c, r, &t);
}
int tx_binary64_supported(void) {
  if (sizeof(double) != 8 || FLT_RADIX != 2 || DBL_MANT_DIG != 53 ||
      DBL_MAX_EXP != 1024) {
    return 0;
  }
  {
    static const double samples[] = {
        1.0, -0.0, -1.5, 0x1p-1022, 0x1p-1074, 0x1.fffffffffffffp1023};
    static const uint64_t expected[] = {
        UINT64_C(0x3ff0000000000000), UINT64_C(0x8000000000000000),
        UINT64_C(0xbff8000000000000), UINT64_C(0x0010000000000000),
        UINT64_C(0x0000000000000001), UINT64_C(0x7fefffffffffffff)};
    size_t i;
    for (i = 0; i < sizeof(samples) / sizeof(samples[0]); i++) {
      uint64_t sample_bits;
      memcpy(&sample_bits, &samples[i], 8);
      if (sample_bits != expected[i]) {
        return 0;
      }
    }
  }
  return 1;
}
int tx_report_double(long double value, double* out) {
  if (!isfinite(value) || fabsl(value) > (long double)DBL_MAX) return 0;
  *out = (double)value;
  return 1;
}
/* binary64 field decode (pure; translated and proved against the Lean `dblMant`/`dblExp`
 * model). Returns 0 for infinities and NaNs. */
static int dbl_decode(uint64_t u, uint64_t* mant, int* exponent) {
  unsigned e = (unsigned)((u >> 52) & 2047);
  uint64_t m = u & UINT64_C(0xfffffffffffff);
  if (e == 2047) return 0;
  *exponent = e ? (int)e - 1023 - 52 : -1074;
  if (e) m |= UINT64_C(1) << 52;
  *mant = m;
  return 1;
}
void qr_double(tx* c, qr* r, double d) {
  uint64_t u, m;
  int exp;
  qr t = {0};
  if (!tx_binary64_supported()) {
    c->status = TESS_INVALID_INPUT;
    return;
  }
  memcpy(&u, &d, 8);
  if (!dbl_decode(u, &m, &exp)) {
    c->status = TESS_INVALID_INPUT;
    return;
  }
  zi_i64(c, &t.n, (int64_t)m);
  zi_i64(c, &t.d, 1);
  if (m) {
    if (exp > 0)
      shift(c, &t.n, &t.n, (unsigned)exp);
    else
      shift(c, &t.d, &t.d, (unsigned)-exp);
    if (u >> 63) t.n.sign = -1;
  }
  reduce(c, &t);
  qm(c, r, &t);
}
void qr_add(tx* c, qr* r, const qr* a, const qr* b) {
  qr t = {0};
  zi x = {0}, y = {0};
  if (!zi_cmp(&a->d, &b->d)) {
    zi_add(c, &t.n, &a->n, &b->n);
    zi_copy(c, &t.d, &a->d);
    reduce(c, &t);
    qm(c, r, &t);
    return;
  }
  zi_mul(c, &x, &a->n, &b->d);
  zi_mul(c, &y, &b->n, &a->d);
  zi_add(c, &t.n, &x, &y);
  zi_mul(c, &t.d, &a->d, &b->d);
  reduce(c, &t);
  zi_clear(c, &x);
  zi_clear(c, &y);
  qm(c, r, &t);
}
void qr_sub(tx* c, qr* r, const qr* a, const qr* b) {
  qr nb = *b;
  nb.n.sign = -nb.n.sign;
  qr_add(c, r, a, &nb);
}
void qr_mul(tx* c, qr* r, const qr* a, const qr* b) {
  qr t = {0};
  zi_mul(c, &t.n, &a->n, &b->n);
  zi_mul(c, &t.d, &a->d, &b->d);
  reduce(c, &t);
  qm(c, r, &t);
}
void qr_div(tx* c, qr* r, const qr* a, const qr* b) {
  qr t = {0};
  if (!b->n.n) {
    if (!c->status) c->status = TESS_INVALID_INPUT;
    return;
  }
  zi_mul(c, &t.n, &a->n, &b->d);
  zi_mul(c, &t.d, &a->d, &b->n);
  reduce(c, &t);
  qm(c, r, &t);
}
int qr_cmp(tx* c, const qr* a, const qr* b) {
  zi x = {0}, y = {0};
  if (!tick(c, a->d.n + b->d.n + a->n.n + b->n.n)) return 0;
  if (a->n.sign != b->n.sign) return a->n.sign > b->n.sign ? 1 : -1;
  if (!zi_cmp(&a->d, &b->d)) return zi_cmp(&a->n, &b->n);
  int s;
  zi_mul(c, &x, &a->n, &b->d);
  zi_mul(c, &y, &b->n, &a->d);
  s = zi_cmp(&x, &y);
  zi_clear(c, &x);
  zi_clear(c, &y);
  return s;
}
void qr_mid(tx* c, qr* r, const qr* a, const qr* b) {
  qr two = {0};
  qr_i64(c, &two, 2);
  qr_add(c, r, a, b);
  qr_div(c, r, r, &two);
  qr_clear(c, &two);
}
long double qr_approx(const qr* a) {
  long double n = 0, d = 0;
  size_t i; /* Scaling avoids overflowing on large denominators. */
  size_t ns = a->n.n > 3 ? a->n.n - 3 : 0, ds = a->d.n > 3 ? a->d.n - 3 : 0;
  for (i = a->n.n; i > ns; i--) n = ldexpl(n, 32) + a->n.v[i - 1];
  for (i = a->d.n; i > ds; i--) d = ldexpl(d, 32) + a->d.v[i - 1];
  if (!d) return NAN;
  return a->n.sign * ldexpl(n / d, 32 * ((int)ns - (int)ds));
}
static void zw(FILE* f, const zi* z) {
  size_t i;
  if (z->sign < 0) fputc('-', f);
  if (!z->n) fputc('0', f);
  for (i = z->n; i; i--) fprintf(f, "%08x", (unsigned)z->v[i - 1]);
}
void qr_write(FILE* f, const qr* a) {
  zw(f, &a->n);
  fputc('/', f);
  zw(f, &a->d);
}
/* Strict hexadecimal numerator/denominator format, bounded before allocating.
 */
static void zr(tx* c, zi* z, FILE* f, int delimiter) {
  zi t = {0};
  int ch, neg = 0;
  size_t n = 0, cap = c->max_limbs * 8;
  char* buf = tx_alloc(c, cap, 1);
  if (!buf) return;
  ch = fgetc(f);
  if (ch == '-') {
    neg = 1;
    ch = fgetc(f);
  }
  while (ch != delimiter && ch != EOF) {
    if (n == cap || !((ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f'))) {
      c->status = TESS_INVALID_INPUT;
      goto end;
    }
    buf[n++] = (char)ch;
    ch = fgetc(f);
  }
  if (!n || ch != delimiter) {
    c->status = TESS_INVALID_INPUT;
    goto end;
  }
  t = make(c, (n + 7) / 8);
  if (t.v) {
    size_t i;
    for (i = 0; i < n; i++) {
      char h = buf[n - 1 - i];
      unsigned v = h <= '9' ? (unsigned)(h - '0') : (unsigned)(h - 'a' + 10);
      t.v[i / 8] |= (uint32_t)v << (4 * (i % 8));
    }
    t.sign = neg ? -1 : 1;
    norm(c, &t);
  }
  move(c, z, &t);
end:
  zi_clear(c, &t);
  tx_free(c, buf, cap);
}
void qr_read(tx* c, qr* a, FILE* f) {
  qr t = {0};
  zr(c, &t.n, f, '/');
  zr(c, &t.d, f, '\n');
  if (!c->status) {
    if (t.d.sign != 1)
      c->status = TESS_INVALID_INPUT;
    else
      reduce(c, &t);
  }
  qm(c, a, &t);
}

void qr_import(tx* c, qr* r, const tess_rational* input) {
  qr t = {0};
  size_t i;
  if (input && (input->numerator_count > c->max_limbs ||
                input->denominator_count > c->max_limbs)) {
    if (!c->status) c->status = TESS_RESOURCE_LIMIT;
    return;
  }
  if (!input || input->sign < -1 || input->sign > 1 ||
      ((!input->sign) != (input->numerator_count == 0)) ||
      (input->numerator_count &&
       (!input->numerator || !input->numerator[input->numerator_count - 1])) ||
      !input->denominator_count || !input->denominator ||
      !input->denominator[input->denominator_count - 1]) {
    if (!c->status) c->status = TESS_INVALID_INPUT;
    return;
  }
  t.n = make(c, input->numerator_count);
  t.d = make(c, input->denominator_count);
  if (!c->status) {
    for (i = 0; i < t.n.n; i++) t.n.v[i] = input->numerator[i];
    for (i = 0; i < t.d.n; i++) t.d.v[i] = input->denominator[i];
    t.n.sign = input->sign;
    t.d.sign = 1;
    reduce(c, &t);
  }
  qm(c, r, &t);
}

/* Bit length of a 32-bit value (pure; translated and proved equal to the Lean `Nat.size`). */
static unsigned bit_len32(uint32_t x) {
  unsigned nb = 0;
  while (x) {
    nb++;
    x >>= 1;
  }
  return nb;
}
int qr_exponent(const qr* a) {
  uint32_t n, d;
  if (!a->n.n || !a->d.n) return 0;
  n = a->n.v[a->n.n - 1];
  d = a->d.v[a->d.n - 1];
  return (int)(a->n.n - 1) * 32 + (int)bit_len32(n) -
         ((int)(a->d.n - 1) * 32 + (int)bit_len32(d));
}
void qr_scale_pow2(tx* c, qr* r, const qr* a, int exponent) {
  qr t = {0};
  unsigned bits =
      exponent < 0 ? (unsigned)(-(exponent + 1)) + 1 : (unsigned)exponent;
  if (bits / 32 > c->max_limbs) {
    if (!c->status) c->status = TESS_RESOURCE_LIMIT;
    return;
  }
  qr_copy(c, &t, a);
  if (exponent > 0)
    shift(c, &t.n, &t.n, bits);
  else if (exponent < 0)
    shift(c, &t.d, &t.d, bits);
  reduce(c, &t);
  qm(c, r, &t);
}
void qr_sqrt_bounds(tx* c, const qr* a, unsigned precision, qr* lower,
                    qr* upper) {
  qr lo = {0}, hi = {0}, mid = {0}, squared = {0}, one = {0};
  unsigned i;
  int exponent;
  if (a->n.n > INT_MAX / 64 || a->d.n > INT_MAX / 64) {
    if (!c->status) c->status = TESS_RESOURCE_LIMIT;
    return;
  }
  if (a->n.sign < 0) {
    if (!c->status) c->status = TESS_INVALID_INPUT;
    return;
  }
  qr_i64(c, &lo, 0);
  qr_i64(c, &one, 1);
  if (!a->n.sign) {
    qr_i64(c, &hi, 0);
    goto end;
  }
  exponent = qr_exponent(a) / 2 + 1;
  qr_scale_pow2(c, &hi, &one, exponent);
  qr_mul(c, &squared, &hi, &hi);
  if (qr_cmp(c, &squared, a) < 0) {
    if (!c->status) c->status = TESS_INTERNAL_ERROR;
    goto end;
  }
  for (i = 0; i < precision && !c->status; i++) {
    int order;
    qr_mid(c, &mid, &lo, &hi);
    qr_mul(c, &squared, &mid, &mid);
    order = qr_cmp(c, &squared, a);
    if (order == 0) {
      qr_copy(c, &lo, &mid);
      qr_copy(c, &hi, &mid);
      break;
    }
    if (order < 0)
      qr_copy(c, &lo, &mid);
    else
      qr_copy(c, &hi, &mid);
  }
end:
  qm(c, lower, &lo);
  qm(c, upper, &hi);
  qr_clear(c, &mid);
  qr_clear(c, &squared);
  qr_clear(c, &one);
}
void qr_round_dyadic(tx* c, qr* r, const qr* a, int step_exponent) {
  qr scaled = {0}, t = {0};
  zi quotient = {0}, remainder = {0}, twice = {0}, two = {0}, one = {0};
  if (a->n.sign < 0 || step_exponent == INT_MIN) {
    if (!c->status) c->status = TESS_INVALID_INPUT;
    return;
  }
  qr_scale_pow2(c, &scaled, a, -step_exponent);
  zi_divrem(c, &quotient, &remainder, &scaled.n, &scaled.d);
  zi_i64(c, &two, 2);
  zi_mul(c, &twice, &remainder, &two);
  if (zi_cmp(&twice, &scaled.d) >= 0) {
    zi_i64(c, &one, 1);
    zi_add(c, &quotient, &quotient, &one);
  }
  zi_copy(c, &t.n, &quotient);
  zi_i64(c, &t.d, 1);
  qr_scale_pow2(c, r, &t, step_exponent);
  qr_clear(c, &scaled);
  qr_clear(c, &t);
  zi_clear(c, &quotient);
  zi_clear(c, &remainder);
  zi_clear(c, &twice);
  zi_clear(c, &two);
  zi_clear(c, &one);
}
void qr_size(tx* c, qr* r, size_t value) {
  uint64_t v = value;
  uint32_t n[2] = {(uint32_t)v, (uint32_t)(v >> 32)}, d = 1;
  tess_rational parts = {value ? 1 : 0, n, n[1] ? 2 : value ? 1 : 0, &d, 1};
  qr_import(c, r, &parts);
}

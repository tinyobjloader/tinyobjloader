/*
 * tobj_write_real.inc -- allocation-free, libc-free decimal formatting of
 * binary64 doubles for the .obj writer.
 *
 * This replaces `snprintf("%.17g")`.  The property the writer needs is
 * *round-trip*: parsing the text back must recover the exact same 64-bit
 * pattern, so the loader sees the original coordinate.
 *
 * Design
 * ------
 * A finite nonzero double is `m * 2^e` with integer `m < 2^53`.  We keep that
 * value exactly as a rational `N / D` in a fixed-capacity big integer:
 *
 *     N = m * 2^max(e,0)        D = 2^max(-e,0)
 *
 * Then we scale by a power of ten so the integer quotient has exactly 17
 * decimal digits, divide once (schoolbook), round half up, and print.  17
 * significant decimal digits always round-trip IEEE-754 binary64 -- that is
 * the classical bound, and it is what makes this correct without any
 * "shortest representation" search.
 *
 * No libm, no libc, no `double` arithmetic and no dynamic memory: only
 * integer operations on fixed stack buffers, so the formatter is itself a
 * candidate for translation by `formal/tools/c2lean.py`.  The pure model and
 * its round-trip theorem live in formal/Obj/Real.lean.
 */
#ifndef TOBJ_WRITE_REAL_INC
#define TOBJ_WRITE_REAL_INC

#include <stddef.h>
#include <stdint.h>

/* 1280 bits: enough for 2^1074 (subnormals), for 10^308 scaling, and for
   their product (10^308 * 2^1074 < 2^2048... see below).  64 limbs = 2048
   bits comfortably covers every intermediate. */
#define TOBJ_BN_LIMBS 64

typedef struct {
  uint32_t d[TOBJ_BN_LIMBS]; /* little-endian limbs */
  int n;                     /* limbs in use, always >= 1 */
} tobj_bn;

/* Significant decimal digits emitted.  17 round-trips binary64. */
#define TOBJ_FMT_DIGITS 17

static void tobj_bn_zero(tobj_bn *a) {
  for (int i = 0; i < TOBJ_BN_LIMBS; i++) a->d[i] = 0u;
  a->n = 1;
}

static void tobj_bn_trim(tobj_bn *a) {
  while (a->n > 1 && a->d[a->n - 1] == 0u) a->n--;
}

static void tobj_bn_set_u64(tobj_bn *a, uint64_t v) {
  tobj_bn_zero(a);
  if (v == 0u) return;
  a->d[0] = (uint32_t)(v & 0xFFFFFFFFu);
  v >>= 32;
  a->n = 1;
  if (v != 0u) {
    a->d[1] = (uint32_t)(v & 0xFFFFFFFFu);
    a->n = 2;
  }
}

static int tobj_bn_is_zero(const tobj_bn *a) {
  return a->n == 1 && a->d[0] == 0u;
}

/* a *= m (m != 0).  Returns 0 if the fixed capacity would overflow. */
static int tobj_bn_mul_small(tobj_bn *a, uint32_t m) {
  uint64_t carry = 0u;
  for (int i = 0; i < a->n; i++) {
    uint64_t p = (uint64_t)a->d[i] * m + carry;
    a->d[i] = (uint32_t)(p & 0xFFFFFFFFu);
    carry = p >> 32;
  }
  while (carry != 0u) {
    if (a->n >= TOBJ_BN_LIMBS) return 0;
    a->d[a->n] = (uint32_t)(carry & 0xFFFFFFFFu);
    carry >>= 32;
    a->n++;
  }
  return 1;
}

static int tobj_bn_mul_pow10(tobj_bn *a, int k) {
  for (int i = 0; i < k; i++) {
    if (!tobj_bn_mul_small(a, 10u)) return 0;
  }
  return 1;
}

/* a <<= k bits.  Returns 0 on capacity overflow. */
static int tobj_bn_shl(tobj_bn *a, int k) {
  int limbs, bits;
  if (k <= 0) return 1;
  limbs = k / 32;
  bits = k % 32;
  if (a->n + limbs + 1 > TOBJ_BN_LIMBS) return 0;
  if (bits != 0) {
    uint32_t carry = 0u;
    for (int i = 0; i < a->n; i++) {
      uint32_t v = a->d[i];
      a->d[i] = (v << bits) | carry;
      carry = (uint32_t)((uint64_t)v >> (32 - bits));
    }
    if (carry != 0u) {
      a->d[a->n] = carry;
      a->n++;
    }
  }
  if (limbs != 0) {
    for (int i = a->n - 1; i >= 0; i--) a->d[i + limbs] = a->d[i];
    for (int i = 0; i < limbs; i++) a->d[i] = 0u;
    a->n += limbs;
  }
  tobj_bn_trim(a);
  return 1;
}

static int tobj_bn_cmp(const tobj_bn *a, const tobj_bn *b) {
  if (a->n != b->n) return a->n < b->n ? -1 : 1;
  for (int i = a->n - 1; i >= 0; i--) {
    if (a->d[i] != b->d[i]) return a->d[i] < b->d[i] ? -1 : 1;
  }
  return 0;
}

/* a -= b, requires a >= b. */
static void tobj_bn_sub(tobj_bn *a, const tobj_bn *b) {
  int64_t borrow = 0;
  for (int i = 0; i < a->n; i++) {
    int64_t x = (int64_t)a->d[i] - (i < b->n ? (int64_t)b->d[i] : 0) - borrow;
    if (x < 0) {
      x += 0x100000000LL;
      borrow = 1;
    } else {
      borrow = 0;
    }
    a->d[i] = (uint32_t)x;
  }
  tobj_bn_trim(a);
}

/* a += 1. */
static void tobj_bn_add1(tobj_bn *a) {
  for (int i = 0; i < a->n; i++) {
    if (a->d[i] != 0xFFFFFFFFu) {
      a->d[i]++;
      return;
    }
    a->d[i] = 0u;
  }
  if (a->n < TOBJ_BN_LIMBS) {
    a->d[a->n] = 1u;
    a->n++;
  }
}

/* q = a / b, r = a % b.  `b` must be nonzero.  `r` must be distinct from
   `a` and `b`; `q` may alias `a`.

   Textbook restoring division, most significant bit first:
     rem = 0; q = 0
     for i = top(a) .. 0:
       rem = 2*rem + bit(a, i);  q = 2*q
       if rem >= b: rem -= b; q += 1
   Requiring `top(a) >= top(b)` (otherwise a < b) makes this correct for any
   magnitudes, with no index bookkeeping beyond the two shifts. */
static void tobj_bn_divmod(tobj_bn *q, tobj_bn *r, const tobj_bn *a,
                           const tobj_bn *b) {
  tobj_bn rem;
  int topA;

  tobj_bn_zero(&rem);
  tobj_bn_zero(q);

  if (tobj_bn_cmp(a, b) < 0) {
    *r = *a;
    return;
  }
  topA = a->n * 32 - 1;
  while (topA >= 0 && ((a->d[topA / 32] >> (topA % 32)) & 1u) == 0u) topA--;

  for (int i = topA; i >= 0; i--) {
    int bit = (int)((a->d[i / 32] >> (i % 32)) & 1u);
    uint32_t c = (uint32_t)bit;
    /* rem = 2*rem + bit */
    for (int j = 0; j < rem.n; j++) {
      uint32_t nv = (rem.d[j] << 1) | c;
      c = rem.d[j] >> 31;
      rem.d[j] = nv;
    }
    if (c != 0u) {
      if (rem.n >= TOBJ_BN_LIMBS) {
        tobj_bn_zero(q);
        *r = *a;
        return;
      }
      rem.d[rem.n] = c;
      rem.n++;
    }
    tobj_bn_trim(&rem);
    /* q = 2*q */
    {
      uint32_t qc = 0u;
      for (int j = 0; j < q->n; j++) {
        uint32_t nv = (q->d[j] << 1) | qc;
        qc = q->d[j] >> 31;
        q->d[j] = nv;
      }
      if (qc != 0u) {
        if (q->n >= TOBJ_BN_LIMBS) {
          tobj_bn_zero(q);
          *r = *a;
          return;
        }
        q->d[q->n] = qc;
        q->n++;
      }
    }
    if (tobj_bn_cmp(&rem, b) >= 0) {
      tobj_bn_sub(&rem, b);
      tobj_bn_add1(q);
    }
  }
  tobj_bn_trim(q);
  *r = rem;
}

/* ---- double decomposition ------------------------------------------- */

typedef struct {
  int neg;
  uint64_t m; /* significand: frac | 2^52 for normals, frac for subnormals */
  int e;      /* value = m * 2^e; e = -1074 for subnormals */
  int is_zero;
  int is_nan;
  int is_inf;
} tobj_dparts;

static void tobj_dparts_of(double v, tobj_dparts *p) {
  uint64_t bits;
  uint32_t exp;
  uint64_t frac;

  __builtin_memcpy(&bits, &v, sizeof bits);
  p->neg = (int)(bits >> 63);
  p->is_zero = 0;
  p->is_nan = 0;
  p->is_inf = 0;
  p->m = 0u;
  p->e = -1074;

  exp = (uint32_t)((bits >> 52) & 0x7FFu);
  frac = bits & 0xFFFFFFFFFFFFFull;
  if (exp == 0x7FFu) {
    if (frac != 0u) {
      p->is_nan = 1;
    } else {
      p->is_inf = 1;
    }
    return;
  }
  if (exp == 0u) {
    if (frac == 0u) {
      p->is_zero = 1;
      return;
    }
    p->m = frac;
    p->e = -1074;
  } else {
    p->m = frac | (1ull << 52);
    p->e = (int)exp - 1075;
  }
}

/* Exact value as N / D with N = m * 2^max(e,0), D = 2^max(-e,0). */
static void tobj_value_frac(const tobj_dparts *p, tobj_bn *N, tobj_bn *D) {
  tobj_bn_set_u64(N, p->m);
  tobj_bn_set_u64(D, 1u);
  if (p->e > 0) {
    (void)tobj_bn_shl(N, p->e);
  } else if (p->e < 0) {
    (void)tobj_bn_shl(D, -p->e);
  }
}

/* Compare `value` (= N/D, positive) with 10^k exactly.
   Returns -1 if value < 10^k, 0 if equal, 1 if greater. */
static int tobj_cmp_pow10(const tobj_dparts *p, int k) {
  tobj_bn N, D, L, R;
  tobj_value_frac(p, &N, &D);
  /* Compare N/D with 10^k:
       k >= 0:  N  vs  10^k * D
       k <  0:  N * 10^-k  vs  D                                      */
  if (k >= 0) {
    R = D;
    if (!tobj_bn_mul_pow10(&R, k)) return 1; /* overflow: 10^k*D huge */
    L = N;
  } else {
    L = N;
    if (!tobj_bn_mul_pow10(&L, -k)) return -1; /* overflow: N*10^-k huge */
    R = D;
  }
  return tobj_bn_cmp(&L, &R);
}

/* floor(log10(value)) for a positive finite value. */
static int tobj_dec_exp(const tobj_dparts *p, int *out_k) {
  int bl = 0;
  int k;
  uint64_t m = p->m;
  long long e2;

  while (m != 0u) {
    m >>= 1;
    bl++;
  }
  e2 = (long long)(p->e + bl - 1); /* floor(log2(value)) */
  /* floor(log10(2^e2)) = floor(e2 * log10(2)); estimate then correct. */
  k = (int)((e2 * 30103LL) / 100000LL);
  if (e2 < 0 && (e2 * 30103LL) % 100000LL != 0) k = (int)((e2 * 30103LL - 99999LL) / 100000LL);

  /* Correct so that 10^k <= value < 10^(k+1). */
  while (tobj_cmp_pow10(p, k) < 0) k--;
  while (tobj_cmp_pow10(p, k + 1) >= 0) k++;
  *out_k = k;
  return 1;
}

/* Digits and exponent of round(value / 10^(k10 - DIGITS + 1)).
   On success: value ~ digits * 10^dexp, with 10^(DIGITS-1) <= digits. */
static int tobj_round_digits(const tobj_dparts *p, int k10, tobj_bn *digits,
                             int *dexp) {
  int s = TOBJ_FMT_DIGITS - 1 - k10; /* scale: value * 10^s */
  tobj_bn N, D, Q, R;

  tobj_value_frac(p, &N, &D);
  if (s >= 0) {
    if (!tobj_bn_mul_pow10(&N, s)) return 0;
  } else {
    if (!tobj_bn_mul_pow10(&D, -s)) return 0;
  }
  tobj_bn_divmod(&Q, &R, &N, &D);
  /* round half up: 2*R >= D */
  {
    tobj_bn R2;
    R2 = R;
    if (!tobj_bn_shl(&R2, 1)) return 0;
    if (tobj_bn_cmp(&R2, &D) >= 0) tobj_bn_add1(&Q);
  }
  /* Rounding may reach exactly 10^DIGITS (an 18th digit).  That value is
     still representable as 1 x 10^(DIGITS+1), so divide by ten once and bump
     the exponent. */
  {
    tobj_bn lim, ten, Q2, R2;
    tobj_bn_set_u64(&lim, 1u);
    if (!tobj_bn_mul_pow10(&lim, TOBJ_FMT_DIGITS)) return 0;
    if (tobj_bn_cmp(&Q, &lim) >= 0) {
      tobj_bn_set_u64(&ten, 10u);
      Q2 = Q;
      tobj_bn_divmod(&Q2, &R2, &Q, &ten);
      Q = Q2;
      *digits = Q;
      *dexp = k10 - TOBJ_FMT_DIGITS + 1 + 1;
      return 1;
    }
  }
  *digits = Q;
  *dexp = k10 - TOBJ_FMT_DIGITS + 1;
  return 1;
}

/* ---- text emission --------------------------------------------------- */

typedef struct {
  char *buf;
  size_t cap;
  size_t len;
} tobj_w2;

static void tobj_w2_byte(tobj_w2 *w, char c) {
  if (w->buf && w->len < w->cap) w->buf[w->len] = c;
  w->len++;
}

/* Print `digits * 10^dexp` (at most TOBJ_FMT_DIGITS digits, trailing zeros
   trimmed) in %g style. */
static void tobj_w2_emit(tobj_w2 *w, int neg, tobj_bn digits, int dexp) {
  unsigned char ds[TOBJ_FMT_DIGITS + 2]; /* most-significant digit first */
  int nd = 0;
  int ndig;
  int e10;

  /* Pop decimal digits least-significant first, then reverse into `ds`. */
  {
    tobj_bn t = digits;
    while (!tobj_bn_is_zero(&t) && nd < TOBJ_FMT_DIGITS + 1) {
      uint64_t rem = 0u;
      for (int i = t.n - 1; i >= 0; i--) {
        uint64_t cur = (rem << 32) | t.d[i];
        t.d[i] = (uint32_t)(cur / 10u);
        rem = cur % 10u;
      }
      tobj_bn_trim(&t);
      ds[nd++] = (unsigned char)rem; /* LSD first */
    }
  }
  if (nd == 0) {
    tobj_w2_byte(w, '0');
    return;
  }
  /* Reverse so ds[0] is the most significant digit. */
  for (int i = 0; i < nd / 2; i++) {
    unsigned char t = ds[i];
    ds[i] = ds[nd - 1 - i];
    ds[nd - 1 - i] = t;
  }
  /* Trim trailing zeros (least significant). */
  ndig = nd;
  while (ndig > 1 && ds[ndig - 1] == 0u) ndig--;
  if (ndig == 1 && ds[0] == 0u) {
    tobj_w2_byte(w, '0');
    return;
  }
  /* value = ds[0] . ds[1] .. ds[ndig-1]  x 10^(dexp + (nd - 1))
     (nd may exceed ndig because we popped exactly TOBJ_FMT_DIGITS digits). */
  e10 = dexp + (nd - 1);
  if (neg) tobj_w2_byte(w, '-');
  /* `%g` style: plain notation iff -4 <= e10 < P, where P is the precision
     (not the number of significant digits actually printed). */
  if (e10 >= -4 && e10 < TOBJ_FMT_DIGITS) {
    /* plain notation */
    if (e10 < 0) {
      /* 0.000ddd...: (-e10 - 1) zeros after the point */
      tobj_w2_byte(w, '0');
      tobj_w2_byte(w, '.');
      for (int z = 0; z < -e10 - 1; z++) tobj_w2_byte(w, '0');
      for (int i = 0; i < ndig; i++) tobj_w2_byte(w, (char)('0' + ds[i]));
    } else {
      for (int i = 0; i < ndig; i++) {
        tobj_w2_byte(w, (char)('0' + ds[i]));
        if (i == e10 && i != ndig - 1) tobj_w2_byte(w, '.');
      }
      /* right-pad zeros when the integer part extends past the digits */
      for (int i = ndig; i <= e10; i++) tobj_w2_byte(w, '0');
    }
  } else {
    tobj_w2_byte(w, (char)('0' + ds[0]));
    if (ndig > 1) {
      tobj_w2_byte(w, '.');
      for (int i = 1; i < ndig; i++) tobj_w2_byte(w, (char)('0' + ds[i]));
    }
    tobj_w2_byte(w, 'e');
    {
      int x = e10;
      if (x < 0) {
        tobj_w2_byte(w, '-');
        x = -x;
      } else {
        tobj_w2_byte(w, '+');
      }
      {
        char tmp[8];
        int n = 0;
        if (x == 0) tmp[n++] = '0';
        while (x > 0 && n < 8) {
          tmp[n++] = (char)('0' + x % 10);
          x /= 10;
        }
        while (n < 2) tmp[n++] = '0';
        while (n > 0) tobj_w2_byte(w, tmp[--n]);
      }
    }
  }
}

/* Format `v` into buf[0..cap), returning the length it would take (snprintf
   convention).  `buf` may be NULL with cap 0 to measure. */
static size_t tobj_fmt_real(char *buf, size_t cap, double v) {
  tobj_w2 w;
  tobj_dparts p;
  tobj_bn digits;
  int k10, dexp;

  w.buf = buf;
  w.cap = cap;
  w.len = 0;

  tobj_dparts_of(v, &p);
  if (p.is_nan || p.is_inf) {
    tobj_w2_byte(&w, '0'); /* loader rejects these upstream */
    return w.len;
  }
  if (p.is_zero) {
    tobj_w2_byte(&w, '0');
    return w.len;
  }
  if (!tobj_dec_exp(&p, &k10) ||
      !tobj_round_digits(&p, k10, &digits, &dexp)) {
    tobj_w2_byte(&w, '0');
    return w.len;
  }
  tobj_w2_emit(&w, p.neg, digits, dexp);
  return w.len;
}

#endif /* TOBJ_WRITE_REAL_INC */

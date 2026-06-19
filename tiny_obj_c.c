/*
 * tiny_obj_c.c -- Pure C11 Wavefront .obj / .mtl loader implementation.
 *
 * SPDX-License-Identifier: MIT
 *
 * Layout:
 *   [1] platform / header includes
 *   [2] libc-independent mem helpers
 *   [3] overflow-safe size arithmetic
 *   [4] allocator + arena
 *   [5] generic growable vector
 *   [6] string interning
 *   [7] number scanners (int / double / float)
 *   [8] line index (scalar; SIMD in section [12])
 *   [9] token cursor / lexer primitives
 *   ... then tiny_obj_c_impl.inc is included once per precision.
 */

#include "tiny_obj_c.h"

#ifndef TOBJ_NO_LIBC
#include <stdlib.h> /* malloc/calloc/free */
#endif

#include <float.h>
#include <limits.h>

#if defined(TOBJ_ENABLE_SIMD)
#if defined(__AVX2__) || defined(__SSE2__) || \
    (defined(_MSC_VER) && (defined(_M_X64) || defined(_M_IX86)))
#include <immintrin.h>
#define TOBJ_SIMD_X86 1
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
#include <arm_neon.h>
#define TOBJ_SIMD_NEON 1
#endif
#endif

/* ======================================================================= */
/* [2] libc-independent mem helpers                                        */
/* ======================================================================= */

static void *tobj_memcpy(void *dst, const void *src, size_t n) {
  unsigned char *d = (unsigned char *)dst;
  const unsigned char *s = (const unsigned char *)src;
  for (size_t i = 0; i < n; i++) d[i] = s[i];
  return dst;
}

static void *tobj_memset(void *dst, int c, size_t n) {
  unsigned char *d = (unsigned char *)dst;
  for (size_t i = 0; i < n; i++) d[i] = (unsigned char)c;
  return dst;
}

static inline int tobj_memcmp(const void *a, const void *b, size_t n) {
  const unsigned char *pa = (const unsigned char *)a;
  const unsigned char *pb = (const unsigned char *)b;
  for (size_t i = 0; i < n; i++) {
    if (pa[i] != pb[i]) return (int)pa[i] - (int)pb[i];
  }
  return 0;
}

static size_t tobj_strlen(const char *s) {
  size_t n = 0;
  while (s[n]) n++;
  return n;
}

static int tobj_strcmp(const char *a, const char *b) {
  size_t i = 0;
  for (;; i++) {
    unsigned char ca = (unsigned char)a[i], cb = (unsigned char)b[i];
    if (ca != cb) return (int)ca - (int)cb;
    if (!ca) return 0;
  }
}

/* Compare a (ptr,len) slice against a NUL-terminated literal for equality. */
static bool tobj_slice_eq(const char *p, size_t len, const char *lit) {
  for (size_t i = 0; i < len; i++) {
    if (lit[i] == '\0' || p[i] != lit[i]) return false;
  }
  return lit[len] == '\0';
}

/* ======================================================================= */
/* [3] overflow-safe size arithmetic                                       */
/* ======================================================================= */

static bool tobj_size_mul(size_t a, size_t b, size_t *out) {
  if (a != 0 && b > (size_t)-1 / a) return false;
  *out = a * b;
  return true;
}

static bool tobj_size_add(size_t a, size_t b, size_t *out) {
  if (a > (size_t)-1 - b) return false;
  *out = a + b;
  return true;
}

/* Clamp a size_t count into a non-negative int (saturating at INT_MAX). */
static int tobj_size_to_int(size_t v) {
  return v > (size_t)INT_MAX ? INT_MAX : (int)v;
}

/* ======================================================================= */
/* [4] allocator + arena                                                   */
/* ======================================================================= */

#ifndef TOBJ_NO_LIBC
static void *tobj_libc_alloc(void *ud, size_t size, size_t align) {
  (void)ud;
  (void)align; /* malloc already returns max_align_t-aligned storage */
  return malloc(size ? size : 1);
}
static void *tobj_libc_calloc(void *ud, size_t count, size_t size,
                              size_t align) {
  (void)ud;
  (void)align; /* calloc already returns max_align_t-aligned storage */
  return calloc(count ? count : 1, size ? size : 1);
}
static void tobj_libc_free(void *ud, void *ptr, size_t size) {
  (void)ud;
  (void)size;
  free(ptr);
}
tobj_allocator tobj_default_allocator(void) {
  tobj_allocator a;
  a.alloc = tobj_libc_alloc;
  a.calloc = tobj_libc_calloc;
  a.realloc = NULL;
  a.free = tobj_libc_free;
  a.max_alloc_size = 0;
  a.user_data = NULL;
  return a;
}
#endif

static bool tobj_is_pow2(size_t x) { return x && ((x & (x - 1u)) == 0); }

static bool tobj_allocator_valid(const tobj_allocator *a) {
  return a && a->alloc && a->free;
}

static bool tobj_resolve_allocator(const tobj_allocator *src,
                                   tobj_allocator *out) {
  if (src && src->alloc) {
    if (!tobj_allocator_valid(src)) return false;
    *out = *src;
    return true;
  }
#ifndef TOBJ_NO_LIBC
  *out = tobj_default_allocator();
  return true;
#else
  (void)out;
  return false;
#endif
}

static bool tobj_alloc_request_valid(const tobj_allocator *a, size_t size,
                                     size_t align) {
  if (!tobj_allocator_valid(a)) return false;
  if (!tobj_is_pow2(align)) return false;
  if (a->max_alloc_size && size > a->max_alloc_size) return false;
  return true;
}

static void *tobj_alloc(const tobj_allocator *a, size_t size, size_t align) {
  if (size == 0) size = 1;
  if (!tobj_alloc_request_valid(a, size, align)) return NULL;
  return a->alloc(a->user_data, size, align);
}
static void *tobj_calloc(const tobj_allocator *a, size_t count, size_t size,
                         size_t align) {
  size_t bytes;
  if (!tobj_size_mul(count ? count : 1, size ? size : 1, &bytes)) return NULL;
  if (!tobj_alloc_request_valid(a, bytes, align)) return NULL;
  if (a->calloc) return a->calloc(a->user_data, count, size, align);
  void *p = a->alloc(a->user_data, bytes, align);
  if (p) tobj_memset(p, 0, bytes);
  return p;
}
static void tobj_free(const tobj_allocator *a, void *ptr, size_t size) {
  if (ptr && tobj_allocator_valid(a)) a->free(a->user_data, ptr, size);
}
static void *tobj_realloc(const tobj_allocator *a, void *ptr, size_t old_size,
                          size_t new_size, size_t align) {
  if (new_size == 0) new_size = 1;
  if (!tobj_alloc_request_valid(a, new_size, align)) return NULL;
  if (a->realloc)
    return a->realloc(a->user_data, ptr, old_size, new_size, align);
  void *p = tobj_alloc(a, new_size, align);
  if (!p) return NULL;
  if (ptr && old_size) {
    size_t n = old_size < new_size ? old_size : new_size;
    tobj_memcpy(p, ptr, n);
    tobj_free(a, ptr, old_size);
  }
  return p;
}

/* Arena: bump allocator over a linked list of blocks. Never frees one
 * element; the whole arena is destroyed at once with the scene. */
typedef struct tobj_arena_block {
  struct tobj_arena_block *next;
  size_t cap;
  size_t used;
  /* payload follows immediately after the header */
} tobj_arena_block;

typedef struct tobj_arena {
  tobj_allocator alloc;
  tobj_arena_block *head;
  size_t default_block;
} tobj_arena;

#define TOBJ_ARENA_HDR \
  ((sizeof(tobj_arena_block) + 15u) & ~(size_t)15u) /* 16-byte aligned hdr */

static void tobj_arena_init(tobj_arena *ar, const tobj_allocator *a,
                            size_t default_block) {
  ar->alloc = *a;
  ar->head = NULL;
  ar->default_block = default_block ? default_block : (size_t)(64 * 1024);
}

static unsigned char *tobj_arena_block_data(tobj_arena_block *b) {
  return (unsigned char *)b + TOBJ_ARENA_HDR;
}

static tobj_arena_block *tobj_arena_new_block(tobj_arena *ar, size_t min_bytes) {
  size_t cap = ar->default_block;
  if (cap < min_bytes) cap = min_bytes;
  size_t total;
  if (!tobj_size_add(TOBJ_ARENA_HDR, cap, &total)) return NULL;
  tobj_arena_block *b =
      (tobj_arena_block *)tobj_alloc(&ar->alloc, total, 16);
  if (!b) return NULL;
  b->cap = cap;
  b->used = 0;
  b->next = ar->head;
  ar->head = b;
  return b;
}

static void *tobj_arena_alloc(tobj_arena *ar, size_t size, size_t align) {
  if (align < 1) align = 1;
  if (size == 0) size = 1;
  tobj_arena_block *b = ar->head;
  if (b) {
    size_t base = (size_t)(tobj_arena_block_data(b) + b->used);
    size_t aligned = (base + (align - 1)) & ~(size_t)(align - 1);
    size_t pad = aligned - base;
    size_t need;
    if (tobj_size_add(pad, size, &need) && b->used + need <= b->cap) {
      b->used += need;
      return (void *)aligned;
    }
  }
  /* fresh block; over-allocate by alignment slack */
  size_t want;
  if (!tobj_size_add(size, align, &want)) return NULL;
  b = tobj_arena_new_block(ar, want);
  if (!b) return NULL;
  size_t base = (size_t)tobj_arena_block_data(b);
  size_t aligned = (base + (align - 1)) & ~(size_t)(align - 1);
  b->used = (aligned - base) + size;
  return (void *)aligned;
}

static void *tobj_arena_dup(tobj_arena *ar, const void *src, size_t size,
                            size_t align) {
  void *p = tobj_arena_alloc(ar, size, align);
  if (p && src) tobj_memcpy(p, src, size);
  return p;
}

static void tobj_arena_destroy(tobj_arena *ar) {
  tobj_arena_block *b = ar->head;
  while (b) {
    tobj_arena_block *next = b->next;
    tobj_free(&ar->alloc, b, TOBJ_ARENA_HDR + b->cap);
    b = next;
  }
  ar->head = NULL;
}

/* ======================================================================= */
/* [5] generic growable vector (type-erased, element-sized)                */
/* ======================================================================= */

typedef struct tobj_vec {
  void *data;
  size_t count; /* elements in use */
  size_t cap;   /* element capacity */
  size_t elem;  /* element size in bytes */
} tobj_vec;

static void tobj_vec_init(tobj_vec *v, size_t elem) {
  v->data = NULL;
  v->count = 0;
  v->cap = 0;
  v->elem = elem;
}

static void tobj_vec_free(tobj_vec *v, const tobj_allocator *a) {
  if (v->data) {
    size_t bytes;
    if (!tobj_size_mul(v->cap, v->elem, &bytes)) bytes = 0;
    tobj_free(a, v->data, bytes);
  }
  v->data = NULL;
  v->count = v->cap = 0;
}

static bool tobj_vec_reserve(tobj_vec *v, size_t want, const tobj_allocator *a) {
  if (want <= v->cap) return true;
  size_t newcap = v->cap ? v->cap + v->cap / 2 : 8;
  if (newcap < want) newcap = want;
  size_t old_bytes, new_bytes;
  if (!tobj_size_mul(v->cap, v->elem, &old_bytes)) return false;
  if (!tobj_size_mul(newcap, v->elem, &new_bytes)) return false;
  void *p = NULL;
  if (v->data) {
    p = tobj_realloc(a, v->data, old_bytes, new_bytes, 16);
  } else {
    p = tobj_calloc(a, newcap, v->elem, 16);
  }
  if (!p) return false;
  v->data = p;
  v->cap = newcap;
  return true;
}

/* Append one zeroed element; returns a pointer to it, or NULL on OOM. */
static void *tobj_vec_push(tobj_vec *v, const tobj_allocator *a) {
  if (!tobj_vec_reserve(v, v->count + 1, a)) return NULL;
  void *slot = (unsigned char *)v->data + v->count * v->elem;
  tobj_memset(slot, 0, v->elem);
  v->count++;
  return slot;
}

/* Append `n` raw elements from `src` (src may be NULL to leave uninit). */
static bool tobj_vec_append(tobj_vec *v, const void *src, size_t n,
                            const tobj_allocator *a) {
  size_t need;
  if (!tobj_size_add(v->count, n, &need)) return false;
  if (!tobj_vec_reserve(v, need, a)) return false;
  if (src) {
    size_t bytes;
    if (!tobj_size_mul(n, v->elem, &bytes)) return false;
    tobj_memcpy((unsigned char *)v->data + v->count * v->elem, src, bytes);
  }
  v->count += n;
  return true;
}

static void *tobj_vec_at(tobj_vec *v, size_t i) {
  return (unsigned char *)v->data + i * v->elem;
}

/* Copy a vector's used contents into freshly arena-allocated storage.
 * Returns NULL when count==0 (callers treat that as an empty buffer). */
static void *tobj_vec_finalize(tobj_vec *v, tobj_arena *ar, size_t align) {
  if (v->count == 0) return NULL;
  size_t bytes;
  if (!tobj_size_mul(v->count, v->elem, &bytes)) return NULL;
  return tobj_arena_dup(ar, v->data, bytes, align);
}

/* ======================================================================= */
/* [6] string interning                                                    */
/* ======================================================================= */

/* Copy a (ptr,len) slice into the arena as a NUL-terminated string.
 * Returns the empty string "" for len==0 (never NULL on success). */
static const char *tobj_intern(tobj_arena *ar, const char *p, size_t len) {
  char *s = (char *)tobj_arena_alloc(ar, len + 1, 1);
  if (!s) return NULL;
  if (len) tobj_memcpy(s, p, len);
  s[len] = '\0';
  return s;
}

/* ======================================================================= */
/* [7] number scanners (libc-free, slice-bounded)                          */
/* ======================================================================= */

static bool tobj_is_space(char c) { return c == ' ' || c == '\t'; }
static bool tobj_is_digit(char c) { return c >= '0' && c <= '9'; }

static void tobj_skip_space(const char **pp, const char *end) {
  const char *p = *pp;
  while (p < end && tobj_is_space(*p)) p++;
  *pp = p;
}

/* Exact powers of ten representable in IEEE-754 double (1e0 .. 1e22). */
static const double tobj_pow10_tab[23] = {
    1e0,  1e1,  1e2,  1e3,  1e4,  1e5,  1e6,  1e7,  1e8,  1e9,  1e10, 1e11,
    1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22};

static double tobj_scale_pow10(double mant, int exp10) {
  /* Fast, correctly-rounded path: mant exact, |exp10| <= 22. */
  if (exp10 == 0) return mant;
  if (exp10 > 0) {
    if (exp10 <= 22) return mant * tobj_pow10_tab[exp10];
  } else {
    if (exp10 >= -22) return mant / tobj_pow10_tab[-exp10];
  }
  /* Slow path: repeated multiply (slightly less precise, still finite). */
  double scale = 1.0;
  int e = exp10 < 0 ? -exp10 : exp10;
  double base = 10.0;
  while (e) {
    if (e & 1) scale *= base;
    base *= base;
    e >>= 1;
    if (scale == 0.0 || scale > 1e308) break;
  }
  return exp10 < 0 ? mant / scale : mant * scale;
}

static bool tobj_match_ci(const char **pp, const char *end, const char *word) {
  const char *p = *pp;
  size_t i = 0;
  while (word[i]) {
    if (p + i >= end) return false;
    char c = p[i];
    if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a');
    if (c != word[i]) return false;
    i++;
  }
  *pp = p + i;
  return true;
}

/* Parse a (possibly signed) floating point token. Maps non-finite words to
 * finite OBJ-friendly values (nan->0, +/-inf->+/-DBL_MAX). */
static bool tobj_scan_double(const char **pp, const char *end, double *out) {
  tobj_skip_space(pp, end);
  const char *p = *pp;
  if (p >= end) return false;

  int sign = 1;
  if (*p == '+' || *p == '-') {
    if (*p == '-') sign = -1;
    p++;
  }

  /* nan / inf / infinity */
  if (p < end && (*p == 'n' || *p == 'N')) {
    const char *q = p;
    if (tobj_match_ci(&q, end, "nan")) {
      *out = 0.0;
      *pp = q;
      return true;
    }
  }
  if (p < end && (*p == 'i' || *p == 'I')) {
    const char *q = p;
    if (tobj_match_ci(&q, end, "infinity") || tobj_match_ci(&q, end, "inf")) {
      *out = sign < 0 ? -DBL_MAX : DBL_MAX;
      *pp = q;
      return true;
    }
  }

  uint64_t mant = 0;
  int mant_digits = 0; /* significant digits accumulated into `mant` */
  int frac_digits = 0; /* digits after the decimal point */
  int extra_exp = 0;   /* integer digits dropped past 19 */
  bool any_digit = false;
  bool seen_dot = false;

  for (; p < end; p++) {
    char c = *p;
    if (tobj_is_digit(c)) {
      any_digit = true;
      if (mant_digits < 19) {
        mant = mant * 10u + (uint64_t)(c - '0');
        mant_digits++;
        if (seen_dot) frac_digits++;
      } else {
        /* too many significant digits: keep magnitude via exponent */
        if (!seen_dot) extra_exp++;
      }
    } else if (c == '.' && !seen_dot) {
      seen_dot = true;
    } else {
      break;
    }
  }
  if (!any_digit) return false;

  int exp10 = 0;
  if (p < end && (*p == 'e' || *p == 'E')) {
    const char *q = p + 1;
    int esign = 1;
    if (q < end && (*q == '+' || *q == '-')) {
      if (*q == '-') esign = -1;
      q++;
    }
    if (q < end && tobj_is_digit(*q)) {
      int e = 0;
      while (q < end && tobj_is_digit(*q)) {
        if (e < 100000) e = e * 10 + (*q - '0');
        q++;
      }
      exp10 = esign * e;
      p = q;
    }
    /* a lone 'e' with no digits is not part of the number; leave p as-is */
  }

  exp10 += extra_exp - frac_digits;
  double value = tobj_scale_pow10((double)mant, exp10);
  *out = sign < 0 ? -value : value;
  *pp = p;
  return true;
}

/* Parse a (possibly signed) integer token (saturating to int range). */
static bool tobj_scan_int(const char **pp, const char *end, int *out) {
  tobj_skip_space(pp, end);
  const char *p = *pp;
  if (p >= end) return false;
  int sign = 1;
  if (*p == '+' || *p == '-') {
    if (*p == '-') sign = -1;
    p++;
  }
  if (p >= end || !tobj_is_digit(*p)) return false;
  long long v = 0;
  bool sat = false;
  while (p < end && tobj_is_digit(*p)) {
    if (!sat) {
      v = v * 10 + (*p - '0');
      if (v > 2147483647LL) {
        v = 2147483647LL;
        sat = true;
      }
    }
    p++;
  }
  *out = (int)(sign < 0 ? -v : v);
  *pp = p;
  return true;
}

/* ======================================================================= */
/* [8] line index (scalar)                                                 */
/* ======================================================================= */

typedef struct tobj_line {
  size_t pos; /* byte offset of first char */
  size_t len; /* length excluding the line terminator */
} tobj_line;

/* Skip a leading UTF-8 BOM if present. */
static size_t tobj_skip_bom(const uint8_t *buf, size_t len) {
  if (len >= 3 && buf[0] == 0xEF && buf[1] == 0xBB && buf[2] == 0xBF) return 3;
  return 0;
}

/* Index of the next '\n' or '\r' at or after i, or len if none. SIMD when
 * available; the scalar tail and fallback are always correct. */
static size_t tobj_next_eol(const uint8_t *b, size_t i, size_t len) {
#if defined(TOBJ_SIMD_X86) && defined(__AVX2__)
  const __m256i nl = _mm256_set1_epi8('\n');
  const __m256i cr = _mm256_set1_epi8('\r');
  for (; i + 32 <= len; i += 32) {
    __m256i v = _mm256_loadu_si256((const __m256i *)(b + i));
    __m256i m = _mm256_or_si256(_mm256_cmpeq_epi8(v, nl),
                                _mm256_cmpeq_epi8(v, cr));
    unsigned mask = (unsigned)_mm256_movemask_epi8(m);
    if (mask) return i + (size_t)__builtin_ctz(mask);
  }
#elif defined(TOBJ_SIMD_X86) && (defined(__SSE2__) || defined(_MSC_VER))
  const __m128i nl = _mm_set1_epi8('\n');
  const __m128i cr = _mm_set1_epi8('\r');
  for (; i + 16 <= len; i += 16) {
    __m128i v = _mm_loadu_si128((const __m128i *)(b + i));
    __m128i m = _mm_or_si128(_mm_cmpeq_epi8(v, nl), _mm_cmpeq_epi8(v, cr));
    unsigned mask = (unsigned)_mm_movemask_epi8(m);
    if (mask) return i + (size_t)__builtin_ctz(mask);
  }
#elif defined(TOBJ_SIMD_NEON)
  const uint8x16_t nl = vdupq_n_u8('\n');
  const uint8x16_t cr = vdupq_n_u8('\r');
  for (; i + 16 <= len; i += 16) {
    uint8x16_t v = vld1q_u8(b + i);
    uint8x16_t m = vorrq_u8(vceqq_u8(v, nl), vceqq_u8(v, cr));
    if (vmaxvq_u8(m)) {
      for (size_t j = 0; j < 16; j++)
        if (b[i + j] == '\n' || b[i + j] == '\r') return i + j;
    }
  }
#endif
  while (i < len && b[i] != '\n' && b[i] != '\r') i++;
  return i;
}

static bool tobj_build_line_index(const uint8_t *buf, size_t len, tobj_vec *out,
                                  const tobj_allocator *a) {
  size_t i = tobj_skip_bom(buf, len);
  while (i < len) {
    size_t e = tobj_next_eol(buf, i, len);
    tobj_line *ln = (tobj_line *)tobj_vec_push(out, a);
    if (!ln) return false;
    ln->pos = i;
    ln->len = e - i;
    if (e >= len) break;
    if (buf[e] == '\r' && e + 1 < len && buf[e + 1] == '\n') e++; /* CRLF */
    i = e + 1;
  }
  return true;
}

/* ======================================================================= */
/* [9] token cursor / lexer primitives                                     */
/* ======================================================================= */

/* A read cursor over a single logical line [p, end). */
typedef struct tobj_cursor {
  const char *p;
  const char *end;
} tobj_cursor;

static void tobj_cur_init(tobj_cursor *c, const char *p, size_t len) {
  c->p = p;
  c->end = p + len;
}

/* Grab the next whitespace-delimited token. Returns false at end of line. */
static bool tobj_next_token(tobj_cursor *c, const char **tok, size_t *tok_len) {
  tobj_skip_space(&c->p, c->end);
  if (c->p >= c->end) return false;
  const char *start = c->p;
  while (c->p < c->end && !tobj_is_space(*c->p)) c->p++;
  *tok = start;
  *tok_len = (size_t)(c->p - start);
  return true;
}

/* ======================================================================= */
/* [10] diagnostics, config, result strings (precision-independent)        */
/* ======================================================================= */

/* Append a fixed message to the diag sink. `msg` is NUL-terminated; no
 * formatting is performed (freestanding-safe). */
static void tobj_diag_append(tobj_diag *d, const tobj_allocator *a,
                             tobj_severity sev, size_t line_no,
                             const char *msg) {
  if (!d) return;
  if (d->on_message) {
    d->on_message(d->user_data, sev, line_no, msg, tobj_strlen(msg));
    return;
  }
  char **buf = (sev == TOBJ_SEV_ERROR) ? &d->err : &d->warn;
  size_t *blen = (sev == TOBJ_SEV_ERROR) ? &d->err_len : &d->warn_len;
  size_t add = tobj_strlen(msg);
  size_t old = *blen;
  size_t need;
  if (!tobj_size_add(old, add, &need)) return;
  if (!tobj_size_add(need, 1, &need)) return;
  char *p = (char *)tobj_realloc(a, *buf, old ? old + 1 : 0, need, 1);
  if (!p) return;
  tobj_memcpy(p + old, msg, add);
  p[old + add] = '\0';
  *buf = p;
  *blen = old + add;
}

void tobj_diag_free(tobj_diag *diag, const tobj_allocator *alloc) {
  if (!diag) return;
#ifndef TOBJ_NO_LIBC
  tobj_allocator def = tobj_default_allocator();
  if (!alloc) alloc = &def;
#else
  if (!alloc) return; /* cannot free without an allocator */
#endif
  if (diag->warn) {
    tobj_free(alloc, diag->warn, diag->warn_len + 1);
    diag->warn = NULL;
    diag->warn_len = 0;
  }
  if (diag->err) {
    tobj_free(alloc, diag->err, diag->err_len + 1);
    diag->err = NULL;
    diag->err_len = 0;
  }
}

tobj_load_config tobj_default_config(void) {
  tobj_load_config c;
  tobj_memset(&c, 0, sizeof c);
  c.triangulate = true;
  c.store_vertex_colors = true;
  c.vertex_color_fallback = true;
  c.parse_freeform = false;
  c.use_arena = false;
  c.num_threads = -1;
  /* 0 caps select built-in defaults in the loader */
  return c;
}

const char *tobj_result_string(tobj_result r) {
  switch (r) {
    case TOBJ_OK: return "ok";
    case TOBJ_ERR_INVALID_ARG: return "invalid argument";
    case TOBJ_ERR_ALLOC: return "allocation failed";
    case TOBJ_ERR_OVERFLOW: return "size overflow";
    case TOBJ_ERR_PARSE: return "parse error";
    case TOBJ_ERR_IO: return "I/O error";
    case TOBJ_ERR_NOT_FOUND: return "not found";
    case TOBJ_ERR_LIMIT_EXCEEDED: return "limit exceeded";
    case TOBJ_ERR_UNSUPPORTED: return "unsupported";
  }
  return "unknown";
}

/* Unknown .mtl parameter pending finalization, tagged by material index. */
typedef struct tobj_pending_kv {
  size_t mat_index;
  const char *key;
  const char *value;
} tobj_pending_kv;

/* Resolve effective caps (0 => built-in default). */
typedef struct tobj_caps {
  size_t vertices, indices, faces, arity, materials, shapes, line_bytes;
  size_t input_bytes;
} tobj_caps;

static tobj_caps tobj_resolve_caps(const tobj_load_config *cfg) {
  tobj_caps c;
  size_t big = (size_t)-1 / 64u;
  c.vertices = cfg->max_vertices ? cfg->max_vertices : big;
  c.indices = cfg->max_indices ? cfg->max_indices : big;
  c.faces = cfg->max_faces ? cfg->max_faces : big;
  c.arity = cfg->max_face_arity ? cfg->max_face_arity : (size_t)(1u << 20);
  c.materials = cfg->max_materials ? cfg->max_materials : (size_t)(1u << 24);
  c.shapes = cfg->max_shapes ? cfg->max_shapes : (size_t)(1u << 24);
  c.line_bytes = cfg->max_line_bytes ? cfg->max_line_bytes : (size_t)(1u << 24);
  c.input_bytes = cfg->max_input_bytes ? cfg->max_input_bytes : big;
  return c;
}

/* ======================================================================= */
/* [11] optional file I/O layer (TOBJ_ENABLE_FILE_IO / TOBJ_ENABLE_MMAP)   */
/* ======================================================================= */

#ifdef TOBJ_ENABLE_FILE_IO
#include <stdio.h>
#if defined(TOBJ_ENABLE_MMAP) && !defined(_WIN32)
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#endif

typedef struct tobj_file_buf {
  const uint8_t *data;
  size_t len;
  int mode; /* 0 = allocator buffer, 1 = mmap */
  tobj_allocator alloc;
} tobj_file_buf;

static tobj_result tobj_file_open(tobj_file_buf *fb, const char *path,
                                  const tobj_allocator *a,
                                  size_t max_len) {
  fb->data = NULL;
  fb->len = 0;
  fb->mode = 0;
  fb->alloc = *a;

#if defined(TOBJ_ENABLE_MMAP) && !defined(_WIN32)
  {
    int fd = open(path, O_RDONLY);
    if (fd >= 0) {
      struct stat st;
      if (fstat(fd, &st) == 0 && st.st_size >= 0) {
        size_t sz = (size_t)st.st_size;
        if (sz > max_len) {
          close(fd);
          return TOBJ_ERR_LIMIT_EXCEEDED;
        }
        if (sz == 0) {
          close(fd);
          fb->data = (const uint8_t *)"";
          fb->len = 0;
          fb->mode = 0;
          return TOBJ_OK;
        }
        void *p = mmap(NULL, sz, PROT_READ, MAP_PRIVATE, fd, 0);
        close(fd);
        if (p != MAP_FAILED) {
          fb->data = (const uint8_t *)p;
          fb->len = sz;
          fb->mode = 1;
          return TOBJ_OK;
        }
      } else {
        close(fd);
      }
    }
    /* fall through to stdio on failure */
  }
#endif

  {
    FILE *f = fopen(path, "rb");
    if (!f) return TOBJ_ERR_IO;
    if (fseek(f, 0, SEEK_END) != 0) {
      fclose(f);
      return TOBJ_ERR_IO;
    }
    long sz = ftell(f);
    if (sz < 0) {
      fclose(f);
      return TOBJ_ERR_IO;
    }
    if ((size_t)sz > max_len) {
      fclose(f);
      return TOBJ_ERR_LIMIT_EXCEEDED;
    }
    if (fseek(f, 0, SEEK_SET) != 0) {
      fclose(f);
      return TOBJ_ERR_IO;
    }
    uint8_t *buf = (uint8_t *)tobj_alloc(a, (size_t)sz ? (size_t)sz : 1, 16);
    if (!buf) {
      fclose(f);
      return TOBJ_ERR_ALLOC;
    }
    size_t rd = fread(buf, 1, (size_t)sz, f);
    fclose(f);
    fb->data = buf;
    fb->len = rd;
    fb->mode = 0;
    return TOBJ_OK;
  }
}

static void tobj_file_close(tobj_file_buf *fb) {
  if (!fb->data) return;
#if defined(TOBJ_ENABLE_MMAP) && !defined(_WIN32)
  if (fb->mode == 1) {
    if (fb->len) munmap((void *)fb->data, fb->len);
    fb->data = NULL;
    return;
  }
#endif
  if (fb->mode == 0 && fb->len) tobj_free(&fb->alloc, (void *)fb->data, fb->len);
  fb->data = NULL;
}

typedef struct tobj_file_res_ctx {
  const char *basedir;
  tobj_allocator alloc;
  size_t max_bytes;
} tobj_file_res_ctx;

static void tobj_file_release(void *ud, const uint8_t *d, size_t n) {
  (void)d;
  (void)n;
  tobj_file_buf *fb = (tobj_file_buf *)ud;
  tobj_allocator a = fb->alloc;
  tobj_file_close(fb);
  tobj_free(&a, fb, sizeof *fb);
}

/* Default resolver: read "<basedir><name>" from disk. */
static tobj_result tobj_file_material_resolver(void *ud, const char *name,
                                               tobj_mtl_source *out) {
  tobj_file_res_ctx *ctx = (tobj_file_res_ctx *)ud;
  size_t bl = ctx->basedir ? tobj_strlen(ctx->basedir) : 0;
  size_t nl = tobj_strlen(name);
  size_t plen;
  if (!tobj_size_add(bl, nl, &plen) || !tobj_size_add(plen, 1, &plen))
    return TOBJ_ERR_OVERFLOW;
  char *path = (char *)tobj_alloc(&ctx->alloc, plen, 1);
  if (!path) return TOBJ_ERR_ALLOC;
  if (bl) tobj_memcpy(path, ctx->basedir, bl);
  tobj_memcpy(path + bl, name, nl);
  path[bl + nl] = '\0';

  tobj_file_buf *fb = (tobj_file_buf *)tobj_alloc(&ctx->alloc, sizeof *fb, 16);
  if (!fb) {
    tobj_free(&ctx->alloc, path, plen);
    return TOBJ_ERR_ALLOC;
  }
  tobj_result r = tobj_file_open(fb, path, &ctx->alloc, ctx->max_bytes);
  tobj_free(&ctx->alloc, path, plen);
  if (r != TOBJ_OK) {
    tobj_free(&ctx->alloc, fb, sizeof *fb);
    return r;
  }
  out->data = fb->data;
  out->len = fb->len;
  out->release = tobj_file_release;
  out->release_ud = fb;
  return TOBJ_OK;
}

/* Directory prefix of `path` (including trailing separator), interned-style
 * copy via allocator; returns "" when there is no separator. Caller frees. */
static char *tobj_dirname_dup(const char *path, const tobj_allocator *a,
                              size_t *out_len) {
  size_t n = tobj_strlen(path);
  size_t cut = 0;
  for (size_t i = 0; i < n; i++) {
    if (path[i] == '/' || path[i] == '\\') cut = i + 1;
  }
  char *d = (char *)tobj_alloc(a, cut + 1, 1);
  if (!d) return NULL;
  if (cut) tobj_memcpy(d, path, cut);
  d[cut] = '\0';
  *out_len = cut;
  return d;
}
#endif /* TOBJ_ENABLE_FILE_IO */

/* ======================================================================= */
/* [11b] threading shim (TOBJ_ENABLE_MULTITHREADING)                       */
/* ======================================================================= */

#ifdef TOBJ_ENABLE_MULTITHREADING
typedef struct tobj_thunk {
  void (*fn)(void *);
  void *arg;
} tobj_thunk;

#if defined(_WIN32)
#include <windows.h>
static DWORD WINAPI tobj_win_trampoline(LPVOID p) {
  tobj_thunk *t = (tobj_thunk *)p;
  t->fn(t->arg);
  return 0;
}
static unsigned tobj_hw_threads(void) {
  SYSTEM_INFO si;
  GetSystemInfo(&si);
  return si.dwNumberOfProcessors ? si.dwNumberOfProcessors : 1u;
}
static void tobj_run_parallel(tobj_thunk *thunks, int n) {
  HANDLE h[64];
  int started = 0;
  for (int i = 0; i < n && i < 64; i++) {
    h[i] = CreateThread(NULL, 0, tobj_win_trampoline, &thunks[i], 0, NULL);
    if (h[i]) started++; else thunks[i].fn(thunks[i].arg);
  }
  for (int i = 0; i < n && i < 64; i++)
    if (h[i]) {
      WaitForSingleObject(h[i], INFINITE);
      CloseHandle(h[i]);
    }
  (void)started;
}
#else
#include <pthread.h>
#include <unistd.h>
static void *tobj_pth_trampoline(void *p) {
  tobj_thunk *t = (tobj_thunk *)p;
  t->fn(t->arg);
  return NULL;
}
static unsigned tobj_hw_threads(void) {
  long n = sysconf(_SC_NPROCESSORS_ONLN);
  return n > 0 ? (unsigned)n : 1u;
}
static void tobj_run_parallel(tobj_thunk *thunks, int n) {
  pthread_t th[64];
  int ok[64];
  if (n > 64) n = 64;
  for (int i = 0; i < n; i++)
    ok[i] = (pthread_create(&th[i], NULL, tobj_pth_trampoline, &thunks[i]) == 0);
  for (int i = 0; i < n; i++) {
    if (ok[i])
      pthread_join(th[i], NULL);
    else
      thunks[i].fn(thunks[i].arg); /* fallback: run inline */
  }
}
#endif
#endif /* TOBJ_ENABLE_MULTITHREADING */

/* ======================================================================= */
/* [12] per-precision parser instantiations                                */
/* ======================================================================= */

#include "tobj_tess.h"

#define TOBJ_REAL float
#define TOBJ_SUF _f
#include "tiny_obj_c_impl.inc"
#undef TOBJ_REAL
#undef TOBJ_SUF

#define TOBJ_REAL double
#define TOBJ_SUF _d
#include "tiny_obj_c_impl.inc"
#undef TOBJ_REAL
#undef TOBJ_SUF

/* ======================================================================= */
/* [12] fuzz entry                                                         */
/* ======================================================================= */

int tobj_fuzz_one(const uint8_t *data, size_t size) {
  tobj_scene_f s;
  tobj_load_config cfg = tobj_default_config();
  if (tobj_load_obj_from_memory_f(&s, data, size, &cfg, NULL) == TOBJ_OK) {
    tobj_scene_free_f(&s);
  }
  return 0;
}

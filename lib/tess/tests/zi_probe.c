/* SPDX-License-Identifier: MIT. Direct big-integer probe: reads hex integers,
   applies the real zi_add/zi_sub/zi_mul/zi_cmp, prints signed hex. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "exact.h"
static int read_zi(tx* c, zi* r, const char* s) {
  int neg = *s == '-';
  size_t len, nl, i;
  zi t = {0};
  if (neg) s++;
  len = strlen(s);
  nl = (len + 7) / 8;
  if (nl) {
    t.v = tx_alloc(c, nl, 4);
    if (!t.v) return 0;
    t.n = nl;
    for (i = 0; i < nl; i++) {
      char buf[9];
      size_t hi = len - i * 8, lo = hi > 8 ? hi - 8 : 0;
      memcpy(buf, s + lo, hi - lo);
      buf[hi - lo] = 0;
      t.v[i] = (uint32_t)strtoul(buf, 0, 16);
    }
    while (t.n && !t.v[t.n - 1]) t.n--;
    if (t.n != nl) { /* keep allocation length == n */
      zi u = {0};
      if (t.n) {
        u.v = tx_alloc(c, t.n, 4);
        if (!u.v) return 0;
        memcpy(u.v, t.v, t.n * 4);
        u.n = t.n;
      }
      tx_free(c, t.v, nl * 4);
      t = u;
    }
    t.sign = t.n ? (neg ? -1 : 1) : 0;
  }
  zi_clear(c, r);
  *r = t;
  return 1;
}
static void write_zi(const zi* a) {
  size_t i;
  if (!a->n) {
    puts("0");
    return;
  }
  printf("%s%x", a->sign < 0 ? "-" : "", a->v[a->n - 1]);
  for (i = a->n - 1; i; i--) printf("%08x", a->v[i - 1]);
  putchar('\n');
}
int main(void) {
  char op[8], sa[1024], sb[1024];
  tx c;
  tx_init(&c);
  c.max_limbs = 4096;
  c.max_ops = (size_t)1 << 40;
  while (scanf("%7s %1023s %1023s", op, sa, sb) == 3) {
    zi a = {0}, b = {0}, r = {0};
    if (!strcmp(op, "i64")) { /* exact int64 import: decimal in sa */
      zi_i64(&c, &r, (int64_t)strtoll(sa, 0, 10));
      if (c.status) return 4;
      write_zi(&r);
      zi_clear(&c, &r);
      if (c.bytes) return 5;
      continue;
    }
    if (!read_zi(&c, &a, sa) || !read_zi(&c, &b, sb)) return 3;
    if (!strcmp(op, "add")) zi_add(&c, &r, &a, &b);
    else if (!strcmp(op, "sub")) zi_sub(&c, &r, &a, &b);
    else if (!strcmp(op, "mul")) zi_mul(&c, &r, &a, &b);
    else if (!strcmp(op, "cmp")) {
      printf("%d\n", zi_cmp(&a, &b));
      zi_clear(&c, &a);
      zi_clear(&c, &b);
      continue;
    } else return 2;
    if (c.status) return 4;
    write_zi(&r);
    zi_clear(&c, &a);
    zi_clear(&c, &b);
    zi_clear(&c, &r);
    if (c.bytes) return 5;
  }
  return 0;
}

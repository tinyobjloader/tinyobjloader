#include <string.h>

#include "exact.h"
int main(void) {
  char op[16];
  tx c;
  tx_init(&c);
  while (scanf("%15s", op) == 1) {
    qr a = {0}, b = {0}, r = {0};
    int ch;
    while ((ch = getchar()) != '\n' && ch != EOF) {
    }
    if (!strcmp(op, "double")) {
      double d;
      if (scanf("%la", &d) != 1) return 2;
      qr_double(&c, &r, d);
    } else {
      qr_read(&c, &a, stdin);
      qr_read(&c, &b, stdin);
      if (!strcmp(op, "add"))
        qr_add(&c, &r, &a, &b);
      else if (!strcmp(op, "sub"))
        qr_sub(&c, &r, &a, &b);
      else if (!strcmp(op, "mul"))
        qr_mul(&c, &r, &a, &b);
      else if (!strcmp(op, "div"))
        qr_div(&c, &r, &a, &b);
      else
        return 3;
    }
    if (c.status) {
      fprintf(stderr, "status %d\n", c.status);
      return 4;
    }
    qr_write(stdout, &r);
    putchar('\n');
    qr_clear(&c, &a);
    qr_clear(&c, &b);
    qr_clear(&c, &r);
    if (c.bytes) {
      fprintf(stderr, "leak %zu\n", c.bytes);
      return 5;
    }
    c.ops = 0;
  }
  return 0;
}

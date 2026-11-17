/* subd_dump FILE.obj: tobj_subd_dump_obj output (same as Lean `subdobj`). */
#include <stdio.h>
#include <stdlib.h>

#include "../tobj_subd.h"

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  FILE *f = fopen(argv[1], "rb");
  if (!f) return 2;
  size_t cap = 1 << 16, n = 0, r;
  char *buf = (char *)malloc(cap);
  while (buf && (r = fread(buf + n, 1, cap - n, f)) > 0) {
    n += r;
    if (n == cap) buf = (char *)realloc(buf, cap *= 2);
  }
  fclose(f);
  if (!buf) return 2;
  size_t len;
  char *out = tobj_subd_dump_obj(buf, n, &len);
  if (!out) return 1;
  fwrite(out, 1, len, stdout);
  free(out);
  free(buf);
  return 0;
}

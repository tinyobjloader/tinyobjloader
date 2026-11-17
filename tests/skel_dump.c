/* skel_dump FILE.obj: tobj_skel_dump_obj output (same as Lean `skelobj`). */
#include <stdio.h>
#include <stdlib.h>

#include "../tobj_skel.h"

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
  char *out = tobj_skel_dump_obj(buf, n, &len);
  if (!out) return 1;
  fwrite(out, 1, len, stdout);
  free(out);
  free(buf);
  return 0;
}

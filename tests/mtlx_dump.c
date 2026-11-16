/* Print tobj_mtlx_dump for one .mtl file (C side of the Lean differential). */
#include <stdio.h>
#include <stdlib.h>
#include "../tobj_mtlx.h"

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: %s FILE.mtl\n", argv[0]);
    return 2;
  }
  FILE *f = fopen(argv[1], "rb");
  if (!f) return 2;
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *buf = (char *)malloc((size_t)n + 1);
  if (!buf || fread(buf, 1, (size_t)n, f) != (size_t)n) return 2;
  fclose(f);
  tobj_mtlx_doc doc;
  if (tobj_mtlx_parse(buf, (size_t)n, &doc)) return 3;
  size_t len = 0;
  char *s = tobj_mtlx_dump(&doc, &len);
  if (!s) return 3;
  fwrite(s, 1, len, stdout);
  free(s);
  tobj_mtlx_free(&doc);
  free(buf);
  return 0;
}

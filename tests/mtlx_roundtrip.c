/* Round-trip check for tobj_mtlx_to_mtl: for each .mtl argument,
 * parse -> to_mtl -> parse gives the same XML, and to_mtl is a fixpoint. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../tobj_mtlx.h"

/* 0 = round-trips, 1 = mismatch, -1 = allocation failure */
int tobj_mtlx_roundtrip_check(const char *text, size_t len) {
  tobj_mtlx_doc a, b;
  if (tobj_mtlx_parse(text, len, &a)) return -1;
  size_t n1, n2, nx1, nx2;
  char *mtl1 = tobj_mtlx_to_mtl(&a, &n1), *x1 = tobj_mtlx_to_xml(&a, &nx1);
  int rc = -1;
  if (mtl1 && x1 && tobj_mtlx_parse(mtl1, n1, &b) == 0) {
    char *mtl2 = tobj_mtlx_to_mtl(&b, &n2), *x2 = tobj_mtlx_to_xml(&b, &nx2);
    if (mtl2 && x2)
      rc = (nx1 == nx2 && !memcmp(x1, x2, nx1) && n1 == n2 && !memcmp(mtl1, mtl2, n1))
               ? 0 : 1;
    free(mtl2);
    free(x2);
    tobj_mtlx_free(&b);
  }
  free(mtl1);
  free(x1);
  tobj_mtlx_free(&a);
  return rc;
}

#ifndef TOBJ_MTLX_ROUNDTRIP_NO_MAIN
int main(int argc, char **argv) {
  int fails = 0;
  for (int i = 1; i < argc; i++) {
    FILE *f = fopen(argv[i], "rb");
    if (!f) { fprintf(stderr, "cannot open %s\n", argv[i]); return 2; }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = (char *)malloc((size_t)n + 1);
    if (!buf || fread(buf, 1, (size_t)n, f) != (size_t)n) return 2;
    fclose(f);
    int rc = tobj_mtlx_roundtrip_check(buf, (size_t)n);
    if (rc) { fprintf(stderr, "round-trip %s: %s\n", rc < 0 ? "oom" : "MISMATCH", argv[i]); fails++; }
    free(buf);
  }
  printf("mtlx round-trip: %d/%d ok\n", argc - 1 - fails, argc - 1);
  return fails != 0;
}
#endif

/* Round-trip check for tobj_subd_to_lines: for each .obj argument and each
 * accepted mesh, parsing the canonical lines gives the same canonical lines
 * (and stays accepted). Meshes are split as in tobj_subd_dump_obj. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../tobj_subd.h"

/* 0 = round-trips, 1 = mismatch, -1 = allocation failure */
int tobj_subd_roundtrip_check(const char *text, size_t len) {
  /* dump(text) lists every mesh with its canonical lines; replacing each
   * mesh's `t` lines by its canonical lines must give the same dump. */
  size_t n1;
  char *d1 = tobj_subd_dump_obj(text, len, &n1);
  if (!d1) return -1;
  /* rebuild: original text without `t` lines, plus canonical lines appended
   * to the end of each mesh, i.e. right before the next o/g line */
  size_t cap = len + n1 + 16, o = 0;
  char *re = (char *)malloc(cap);
  if (!re) { free(d1); return -1; }
  const char *dp = d1;  /* cursor into the dump */
  size_t mesh = 0;
  /* emit canonical lines of mesh `mesh` from the dump, if present */
#define FLUSH()                                                              \
  do {                                                                       \
    char hdr[48];                                                            \
    int hl = snprintf(hdr, sizeof hdr, "mesh %zu ok=", mesh);               \
    if (!strncmp(dp, hdr, (size_t)hl)) {                                     \
      dp = strchr(dp, '\n') + 1;                                             \
      while (*dp == 't') {                                                   \
        const char *e = strchr(dp, '\n') + 1;                                \
        memcpy(re + o, dp, (size_t)(e - dp));                                \
        o += (size_t)(e - dp);                                               \
        dp = e;                                                              \
      }                                                                      \
    }                                                                        \
  } while (0)
  size_t pos = 0;
  for (;;) {
    size_t e = pos;
    while (e < len && text[e] != '\n') e++;
    /* first token, as tobj_subd tokenizes it (one trailing '\r' dropped) */
    size_t le = e > pos && text[e - 1] == '\r' ? e - 1 : e;
    size_t i = pos;
    while (i < le && (text[i] == ' ' || text[i] == '\t')) i++;
    size_t j = i;
    while (j < le && text[j] != ' ' && text[j] != '\t') j++;
    int is_t = j - i == 1 && text[i] == 't';
    int is_grp = j - i == 1 && (text[i] == 'o' || text[i] == 'g');
    if (is_grp) {
      FLUSH();
      mesh++;
    }
    if (!is_t) {
      memcpy(re + o, text + pos, e - pos);
      o += e - pos;
      re[o++] = '\n';
    }
    if (e >= len) break;
    pos = e + 1;
  }
  FLUSH();
#undef FLUSH
  size_t n2;
  char *d2 = tobj_subd_dump_obj(re, o, &n2);
  int rc = -1;
  if (d2) {
    /* rejected meshes lose their lines, so compare accepted meshes only:
     * every `mesh i ok=1` block of d1 must appear unchanged in d2 */
    rc = 0;
    const char *p = d1;
    while ((p = strstr(p, "ok=1\n"))) {
      const char *b = p;
      while (b > d1 && b[-1] != '\n') b--;
      const char *e = p + 5;
      while (*e == 't') e = strchr(e, '\n') + 1;
      size_t bl = (size_t)(e - b);
      /* an accepted mesh with empty canonical form and no faces is not
       * listed again (empty meshes are skipped): trivially round-trips */
      if (e == p + 5) { p = e; continue; }
      int found = 0;
      for (const char *q = d2; (q = strstr(q, "mesh ")); q++)
        if (!strncmp(q, b, bl) && (q[bl] == '\0' || q[bl] == 'm')) { found = 1; break; }
      if (!found) { rc = 1; break; }
      p = e;
    }
    free(d2);
  }
  free(re);
  free(d1);
  return rc;
}

#ifndef TOBJ_SUBD_ROUNDTRIP_NO_MAIN
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
    int rc = tobj_subd_roundtrip_check(buf, (size_t)n);
    if (rc) { fprintf(stderr, "round-trip %s: %s\n", rc < 0 ? "oom" : "MISMATCH", argv[i]); fails++; }
    free(buf);
  }
  printf("subd round-trip: %d/%d ok\n", argc - 1 - fails, argc - 1);
  return fails != 0;
}
#endif

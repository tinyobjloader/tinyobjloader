/* Round-trip check for tobj_skel_to_lines: an accepted skeleton, written in
 * canonical form and parsed again (same vw bound), gives the same canonical
 * lines. The property is proved in Lean (TobjSkel.roundtrip); this checks the
 * C implementation. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../tobj_skel.h"

/* Lines of `text` (NUL-separated in a copy); skel lines and the vw bound. */
static int collect(char *copy, size_t len, const char ***lines, size_t *n, long *max_id) {
  *lines = NULL;
  *n = 0;
  *max_id = -1;
  size_t pos = 0;
  for (;;) {
    size_t e = pos;
    while (e < len && copy[e] != '\n') e++;
    copy[e] = '\0';
    const char *l = copy + pos;
    while (*l == ' ' || *l == '\t') l++;
    if (!strncmp(l, "skel_", 5)) {
      const char **q = (const char **)realloc(*lines, (*n + 1) * sizeof(char *));
      if (!q) return -1;
      *lines = q;
      (*lines)[(*n)++] = copy + pos;
    } else if (l[0] == 'v' && l[1] == 'w' && (l[2] == ' ' || l[2] == '\t')) {
      char *p;
      strtol(l + 2, &p, 10);
      for (;;) {
        char *q;
        long j = strtol(p, &q, 10);
        if (q == p) break;
        if (j > *max_id) *max_id = j;
        strtod(q, &p);
        if (p == q) break;
      }
    }
    if (e >= len) break;
    pos = e + 1;
  }
  return 0;
}

/* 0 = round-trips (or not accepted), 1 = mismatch, -1 = allocation failure */
int tobj_skel_roundtrip_check(const char *text, size_t len) {
  char *copy = (char *)malloc(len + 1);
  if (!copy) return -1;
  memcpy(copy, text, len);
  copy[len] = '\0';
  const char **lines;
  size_t n;
  long max_id;
  int rc = -1;
  if (collect(copy, len, &lines, &n, &max_id) == 0) {
    tobj_skel a, b;
    if (tobj_skel_parse_lines(lines, n, max_id, &a) == 0) {
      rc = 0;
      if (a.ok) {
        size_t l1;
        char *c1 = tobj_skel_to_lines(&a, &l1);
        rc = -1;
        if (c1) {
          /* split the canonical text into lines */
          const char **cl = NULL;
          size_t cn = 0;
          char *p = c1;
          int bad_alloc = 0;
          while (*p) {
            char *e = strchr(p, '\n');
            *e = '\0';
            const char **q = (const char **)realloc(cl, (cn + 1) * sizeof(char *));
            if (!q) {
              bad_alloc = 1;
              break;
            }
            cl = q;
            cl[cn++] = p;
            p = e + 1;
          }
          if (!bad_alloc && tobj_skel_parse_lines(cl, cn, max_id, &b) == 0) {
            size_t l2;
            char *c2 = tobj_skel_to_lines(&b, &l2);
            char *c1b = tobj_skel_to_lines(&a, &l1);
            if (c2 && c1b) rc = (b.ok && l1 == l2 && !memcmp(c1b, c2, l1)) ? 0 : 1;
            free(c2);
            free(c1b);
            tobj_skel_free(&b);
          }
          free(cl);
          free(c1);
        }
      }
      tobj_skel_free(&a);
    }
    free(lines);
  }
  free(copy);
  return rc;
}

#ifndef TOBJ_SKEL_ROUNDTRIP_NO_MAIN
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
    int rc = tobj_skel_roundtrip_check(buf, (size_t)n);
    if (rc) { fprintf(stderr, "round-trip %s: %s\n", rc < 0 ? "oom" : "MISMATCH", argv[i]); fails++; }
    free(buf);
  }
  printf("skel round-trip: %d/%d ok\n", argc - 1 - fails, argc - 1);
  return fails != 0;
}
#endif

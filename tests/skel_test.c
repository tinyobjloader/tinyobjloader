/* skel_test FILE.obj: C11 loader + tobj_skel on attrib.skel_lines. The C11
 * loader does not parse `vw`, so the joint-id bound is read from the vw lines
 * here. Prints the verdict and canonical lines (compared to golden files). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../tiny_obj_c.h"
#include "../tobj_skel.h"

static long max_vw_joint(const char *text) {
  long m = -1;
  for (const char *p = text; p && *p;) {
    while (*p == ' ' || *p == '\t') p++;
    if (p[0] == 'v' && p[1] == 'w' && (p[2] == ' ' || p[2] == '\t')) {
      char *e;
      strtol(p + 2, &e, 10); /* vertex */
      for (;;) {
        char *e2;
        long j = strtol(e, &e2, 10);
        if (e2 == e) break;
        if (j > m) m = j;
        strtod(e2, &e); /* weight */
        if (e == e2) break;
      }
    }
    p = strchr(p, '\n');
    if (p) p++;
  }
  return m;
}

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  FILE *f = fopen(argv[1], "rb");
  if (!f) return 2;
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *buf = (char *)malloc((size_t)n + 1);
  if (!buf || fread(buf, 1, (size_t)n, f) != (size_t)n) return 2;
  fclose(f);
  buf[n] = 0;
  tobj_load_config cfg = tobj_default_config();
  tobj_scene_d sc;
  memset(&sc, 0, sizeof(sc));
  if (tobj_load_obj_from_memory_d(&sc, (const uint8_t *)buf, (size_t)n, &cfg, NULL) != TOBJ_OK) {
    printf("load failed\n");
    return 1;
  }
  tobj_skel s;
  if (tobj_skel_parse_lines(sc.attrib.skel_lines, sc.attrib.num_skel_lines, max_vw_joint(buf), &s))
    return 1;
  printf("skel ext=%d ok=%d joints=%zu lines=%zu\n", s.ext, s.ok, s.num_joints,
         sc.attrib.num_skel_lines);
  for (size_t e = 0; e < s.num_errors; e++) printf("  error: %s\n", s.errors[e]);
  char *t = tobj_skel_to_lines(&s, NULL);
  if (!t) return 1;
  fputs(t, stdout);
  free(t);
  tobj_skel_free(&s);
  tobj_scene_free_d(&sc);
  free(buf);
  return 0;
}

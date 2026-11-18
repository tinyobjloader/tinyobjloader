/* subd_test FILE.obj: C11 loader (triangulate = false) + tobj_subd per shape.
 * Prints `shape <name> faces=<n> tags=<generic>/<lines> ok=<0|1>` and the
 * canonical tag lines; compared against golden files by `make check_subd`. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../tiny_obj_c.h"
#include "../tobj_subd.h"

static char *slurp(const char *p, size_t *n) {
  FILE *f = fopen(p, "rb");
  if (!f) return NULL;
  fseek(f, 0, SEEK_END);
  long l = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *b = (char *)malloc((size_t)l + 1);
  if (b && fread(b, 1, (size_t)l, f) != (size_t)l) { free(b); b = NULL; }
  fclose(f);
  if (b) b[l] = 0;
  *n = (size_t)l;
  return b;
}

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  size_t n;
  char *buf = slurp(argv[1], &n);
  if (!buf) return 2;
  tobj_load_config cfg = tobj_default_config();
  cfg.triangulate = false;
  tobj_scene_d sc;
  memset(&sc, 0, sizeof(sc));
  if (tobj_load_obj_from_memory_d(&sc, (const uint8_t *)buf, n, &cfg, NULL) != TOBJ_OK) {
    printf("load failed\n");
    return 1;
  }
  for (size_t s = 0; s < sc.num_shapes; s++) {
    const tobj_mesh_d *m = &sc.shapes[s].mesh;
    int *vi = (int *)malloc((m->num_indices + 1) * sizeof(int));
    if (!vi) return 1;
    for (size_t i = 0; i < m->num_indices; i++) vi[i] = m->indices[i].vertex_index;
    tobj_subd sd;
    if (tobj_subd_parse_lines(m->tag_lines, m->num_tag_lines, m->num_face_vertices,
                              m->num_faces, vi, &sd))
      return 1;
    printf("shape %s faces=%zu tags=%zu/%zu ok=%d\n", sc.shapes[s].name, m->num_faces,
           m->num_tags, m->num_tag_lines, sd.ok);
    for (size_t e = 0; e < sd.num_errors; e++) printf("  error: %s\n", sd.errors[e]);
    char *t = tobj_subd_to_lines(&sd, NULL);
    if (!t) return 1;
    fputs(t, stdout);
    free(t);
    tobj_subd_free(&sd);
    free(vi);
  }
  tobj_scene_free_d(&sc);
  free(buf);
  return 0;
}

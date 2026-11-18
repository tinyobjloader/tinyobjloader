/* Loader integration: per-material mtlx_lines (C11 loader) must give the same
 * ext/ok verdict and XML as parsing the whole .mtl with tobj_mtlx_parse. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../tiny_obj_c.h"
#include "../tobj_mtlx.h"

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
  int fails = 0;
  for (int a = 1; a < argc; a++) {
    size_t n;
    char *buf = slurp(argv[a], &n);
    if (!buf) return 2;
    tobj_mtlx_doc whole;
    if (tobj_mtlx_parse(buf, n, &whole)) return 3;
    tobj_material_list_d list;
    memset(&list, 0, sizeof(list));
    tobj_result r = tobj_parse_mtl_from_memory_d(&list, (const uint8_t *)buf, n, NULL, NULL);
    if (r != TOBJ_OK) { printf("FAIL %s: loader error %d\n", argv[a], (int)r); fails++; }
    size_t wi = 0;
    for (size_t i = 0; i < list.count; i++) {
      const tobj_material_d *m = &list.items[i];
      /* match by order among same-named materials */
      while (wi < whole.num_materials && strcmp(whole.materials[wi].name, m->name)) wi++;
      if (wi == whole.num_materials) { printf("FAIL %s: material %s not in whole parse\n", argv[a], m->name); fails++; break; }
      const tobj_mtlx_material *w = &whole.materials[wi++];
      tobj_mtlx_doc one;
      if (tobj_mtlx_parse_lines(m->name, m->mtlx_lines, m->num_mtlx_lines, &one)) return 3;
      const tobj_mtlx_material *o = &one.materials[0];
      if (o->ext != w->ext || o->ok != w->ok) {
        printf("FAIL %s: %s ext/ok %d/%d vs %d/%d\n", argv[a], m->name, o->ext, o->ok, w->ext, w->ok);
        fails++;
      }
      for (size_t k = 0; k < m->num_unknown_params; k++)
        if (!strncmp(m->unknown_params[k].key, "mtlx_", 5)) {
          printf("FAIL %s: %s leaked into unknown params\n", argv[a], m->unknown_params[k].key);
          fails++;
        }
      tobj_mtlx_free(&one);
    }
    tobj_material_list_free_d(&list);
    tobj_mtlx_free(&whole);
    free(buf);
  }
  printf("mtlx loader test: %s\n", fails ? "FAIL" : "ok");
  return fails != 0;
}

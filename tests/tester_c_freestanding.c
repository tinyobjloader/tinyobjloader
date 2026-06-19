/*
 * tester_c_freestanding.c -- proves tiny_obj_c builds and runs with
 * -ffreestanding -DTOBJ_NO_LIBC, using a caller-supplied bump allocator and
 * no libc (no malloc / stdio / string.h). Returns 0 on success.
 */
#include "tiny_obj_c.h"

static unsigned char g_pool[4u * 1024u * 1024u];
static size_t g_used = 0;

static void *fs_alloc(void *ud, size_t size, size_t align) {
  (void)ud;
  if (align < 1) align = 1;
  size_t base = (size_t)(g_pool + g_used);
  size_t aligned = (base + (align - 1)) & ~(size_t)(align - 1);
  size_t off = aligned - (size_t)g_pool;
  if (off + size > sizeof g_pool) return (void *)0;
  g_used = off + size;
  return (void *)aligned;
}
static void *fs_realloc(void *ud, void *ptr, size_t old, size_t neu,
                        size_t align) {
  void *p = fs_alloc(ud, neu, align);
  if (p && ptr && old) {
    unsigned char *d = (unsigned char *)p;
    const unsigned char *s = (const unsigned char *)ptr;
    size_t n = old < neu ? old : neu;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
  }
  return p;
}
static void fs_free(void *ud, void *p, size_t s) {
  (void)ud;
  (void)p;
  (void)s;
}

static const char g_obj[] =
    "v 0 0 0\nv 1 0 0\nv 1 1 0\nv 0 1 0\nvn 0 0 1\nf 1 2 3 4\nl 1 2\np 3\n";

int main(void) {
  tobj_allocator a;
  a.alloc = fs_alloc;
  a.calloc = 0;
  a.realloc = fs_realloc;
  a.free = fs_free;
  a.max_alloc_size = 0;
  a.user_data = (void *)0;

  tobj_load_config cfg = tobj_default_config();
  cfg.allocator = a;

  size_t len = 0;
  while (g_obj[len]) len++;

  tobj_scene_f sc;
  tobj_result r =
      tobj_load_obj_from_memory_f(&sc, (const uint8_t *)g_obj, len, &cfg,
                                  (tobj_diag *)0);
  if (r != TOBJ_OK) return 1;
  /* quad -> 2 triangles -> 6 indices */
  int ok = (sc.num_shapes == 1 && sc.shapes[0].mesh.num_indices == 6 &&
            sc.shapes[0].lines.num_lines == 1 &&
            sc.shapes[0].points.num_indices == 1);
  tobj_scene_free_f(&sc);
  return ok ? 0 : 2;
}

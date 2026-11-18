/*
 * fuzz_tobj_subd.c -- libFuzzer/AFL entry for the subdivision-tag parser.
 *
 * Build (libFuzzer):
 *   clang -std=c11 -g -O1 -fsanitize=address,undefined,fuzzer -I.. \
 *     fuzz_tobj_subd.c ../tobj_subd.c ../tiny_obj_c.c ../tobj_tess.c -lm \
 *     -o fuzz_tobj_subd
 * Run with the seed corpus:
 *   ./fuzz_tobj_subd corpus/subd
 *
 * Exercises tobj_subd on the .obj subset (tobj_subd_dump_obj), the canonical
 * writer (which must round-trip), and the C11 loader's tag_lines fed back
 * through tobj_subd_parse_lines. Asserts no crash, hang, leak or UB.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "tiny_obj_c.h"
#include "tobj_subd.h"

#define TOBJ_SUBD_ROUNDTRIP_NO_MAIN
#include "../tests/subd_roundtrip.c"

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  /* Strings are NUL-terminated, so text with NUL bytes is out of scope. */
  if (memchr(data, 0, size)) return 0;
  if (tobj_subd_roundtrip_check((const char *)data, size) > 0) abort();

  tobj_load_config cfg = tobj_default_config();
  cfg.triangulate = false;
  tobj_scene_d sc;
  memset(&sc, 0, sizeof(sc));
  if (tobj_load_obj_from_memory_d(&sc, data, size, &cfg, NULL) == TOBJ_OK) {
    for (size_t s = 0; s < sc.num_shapes; s++) {
      const tobj_mesh_d *m = &sc.shapes[s].mesh;
      int *vi = (int *)malloc((m->num_indices + 1) * sizeof(int));
      if (!vi) break;
      for (size_t i = 0; i < m->num_indices; i++) vi[i] = m->indices[i].vertex_index;
      tobj_subd sd;
      if (tobj_subd_parse_lines(m->tag_lines, m->num_tag_lines, m->num_face_vertices,
                                m->num_faces, vi, &sd) == 0) {
        free(tobj_subd_to_lines(&sd, NULL));
        tobj_subd_free(&sd);
      }
      free(vi);
    }
  }
  tobj_scene_free_d(&sc);
  return 0;
}

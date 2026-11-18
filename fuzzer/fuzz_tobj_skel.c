/*
 * fuzz_tobj_skel.c -- libFuzzer/AFL entry for the skeleton lines (skel-obj.md).
 *
 * Build (libFuzzer):
 *   clang -std=c11 -g -O1 -fsanitize=address,undefined,fuzzer -I.. \
 *     fuzz_tobj_skel.c ../tobj_skel.c ../tiny_obj_c.c ../tobj_tess.c -lm \
 *     -o fuzz_tobj_skel
 *   ./fuzz_tobj_skel corpus/skel
 *
 * Exercises tobj_skel on the .obj subset (tobj_skel_dump_obj), the canonical
 * writer (which must round-trip), and the C11 loader's skel_lines.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "tiny_obj_c.h"
#include "tobj_skel.h"

#define TOBJ_SKEL_ROUNDTRIP_NO_MAIN
#include "../tests/skel_roundtrip.c"

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  /* Strings are NUL-terminated, so text with NUL bytes is out of scope. */
  if (memchr(data, 0, size)) return 0;
  free(tobj_skel_dump_obj((const char *)data, size, NULL));
  /* The round trip holds for lines without '\r' (TobjSkel.roundtrip's
   * hypothesis): a token ending in '\r' loses it when re-read. */
  if (!memchr(data, '\r', size) &&
      tobj_skel_roundtrip_check((const char *)data, size) > 0)
    abort();

  tobj_load_config cfg = tobj_default_config();
  tobj_scene_d sc;
  memset(&sc, 0, sizeof(sc));
  if (tobj_load_obj_from_memory_d(&sc, data, size, &cfg, NULL) == TOBJ_OK) {
    tobj_skel s;
    if (tobj_skel_parse_lines(sc.attrib.skel_lines, sc.attrib.num_skel_lines, -1, &s) == 0) {
      free(tobj_skel_to_lines(&s, NULL));
      tobj_skel_free(&s);
    }
  }
  tobj_scene_free_d(&sc);
  return 0;
}

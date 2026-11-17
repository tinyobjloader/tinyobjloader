/*
 * fuzz_tobj_mtlx.c -- libFuzzer/AFL entry for the MaterialX-in-MTL parser.
 *
 * Build (libFuzzer):
 *   clang -std=c11 -g -O1 -fsanitize=address,undefined,fuzzer -I.. \
 *     fuzz_tobj_mtlx.c ../tobj_mtlx.c -o fuzz_tobj_mtlx
 * Run with the seed corpus:
 *   ./fuzz_tobj_mtlx corpus/mtlx
 *
 * Exercises the whole-file parse, the per-material line API used by the
 * loaders, and both writers. The harness asserts only that nothing crashes,
 * hangs, leaks or hits UB.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "tobj_mtlx.h"

static void exercise(const tobj_mtlx_doc *doc) {
  size_t n = 0;
  free(tobj_mtlx_to_xml(doc, &n));
  free(tobj_mtlx_dump(doc, &n));
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  tobj_mtlx_doc doc;
  memset(&doc, 0, sizeof(doc));
  if (tobj_mtlx_parse((const char *)data, size, &doc) == 0) exercise(&doc);
  tobj_mtlx_free(&doc);

  /* Line API: first line is the material name, the rest are its lines. */
  char *buf = (char *)malloc(size + 1);
  if (!buf) return 0;
  memcpy(buf, data, size);
  buf[size] = '\0';
  size_t cap = 1;
  for (size_t i = 0; i < size; i++) cap += buf[i] == '\n';
  const char **lines = (const char **)malloc(cap * sizeof(*lines));
  if (lines) {
    size_t nl = 0;
    char *p = buf;
    for (;;) {
      lines[nl++] = p;
      char *e = strchr(p, '\n');
      if (!e) break;
      *e = '\0';
      p = e + 1;
    }
    memset(&doc, 0, sizeof(doc));
    if (tobj_mtlx_parse_lines(lines[0], lines + 1, nl - 1, &doc) == 0)
      exercise(&doc);
    tobj_mtlx_free(&doc);
    free(lines);
  }
  free(buf);
  return 0;
}

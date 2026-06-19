/*
 * fuzz_tobj_c.c -- libFuzzer/AFL entry for the pure C11 loader.
 *
 * Build (libFuzzer):
 *   clang -std=c11 -g -O1 -fsanitize=address,undefined,fuzzer \
 *     -DTOBJ_ENABLE_FILE_IO -I.. fuzz_tobj_c.c ../tiny_obj_c.c ../tobj_tess.c \
 *     -o fuzz_tobj_c
 *
 * tobj_fuzz_one parses the input from memory and frees the scene; the harness
 * asserts only that it returns (no crash / hang / leak / UB).
 */
#include "tiny_obj_c.h"

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  return tobj_fuzz_one(data, size);
}

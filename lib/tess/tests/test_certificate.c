#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tess.h"
static int fixture(const double* xyz, size_t n, const size_t* rings,
                   size_t nr) {
  tess_input in = {xyz, n, rings, nr};
  tess_result *mesh = NULL, *other = NULL;
  tess_options o = tess_default_options();
  FILE* f;
  long length;
  char* bytes;
  size_t i;
  tess_status s;
  int ok = 0;
  if (tess_triangulate(&in, &o, &mesh) != TESS_OK) return 0;
  f = tmpfile();
  if (!f) goto end;
  if (tess_write_certificate(mesh, f) != TESS_OK) {
    fclose(f);
    goto end;
  }
  length = ftell(f);
  if (length <= 0) {
    fclose(f);
    goto end;
  }
  rewind(f);
  bytes = malloc((size_t)length);
  if (!bytes) {
    fclose(f);
    goto end;
  }
  if (fread(bytes, 1, (size_t)length, f) != (size_t)length) {
    free(bytes);
    fclose(f);
    goto end;
  }
  fclose(f);
  s = tess_check_certificate(mesh, bytes, (size_t)length);
  if (s != TESS_OK) {
    fprintf(stderr, "valid certificate rejected: %s\n", tess_status_string(s));
    free(bytes);
    goto end;
  }
  for (i = 0; i < (size_t)length; i += 17) {
    char saved = bytes[i];
    bytes[i] = '!';
    s = tess_check_certificate(mesh, bytes, (size_t)length);
    bytes[i] = saved;
    if (s != TESS_CERTIFICATE_REJECTED) {
      fprintf(stderr, "corruption %zu accepted/status %d\n", i, s);
      free(bytes);
      goto end;
    }
  }
  if (tess_check_certificate(mesh, bytes, (size_t)length - 1) !=
      TESS_CERTIFICATE_REJECTED) {
    free(bytes);
    goto end;
  }
  o.strict_planar = 1;
  if (tess_triangulate(&in, &o, &other) == TESS_OK &&
      tess_check_certificate(other, bytes, (size_t)length) !=
          TESS_CERTIFICATE_REJECTED) {
    free(bytes);
    goto end;
  }
  free(bytes);
  ok = 1;
end:
  tess_result_free(mesh);
  tess_result_free(other);
  return ok;
}
int main(void) {
  const double square[] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0},
               warped[] = {0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0},
               hole[] = {0, 0, 0, 4, 0, 0, 4, 4, 0, 0, 4, 0,
                         1, 1, 0, 1, 2, 0, 2, 2, 0, 2, 1, 0};
  size_t r[] = {0, 4}, h[] = {0, 4, 8};
  const double reversed[] = {0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0};
  return !(fixture(reversed, 4, r, 1) && fixture(square, 4, r, 1) &&
           fixture(warped, 4, r, 1) && fixture(hole, 8, h, 2));
}

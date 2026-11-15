#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "edits.h"
static int write_cert(tess_result* r, const char* path) {
  FILE* f = fopen(path, "w+b");
  int status;
  if (!f) return 0;
  status = tess_write_certificate(r, f) == TESS_OK;
  if (status) {
    long length = ftell(f);
    char* bytes;
    rewind(f);
    bytes = malloc((size_t)length);
    if (!bytes || fread(bytes, 1, (size_t)length, f) != (size_t)length ||
        tess_check_certificate(r, bytes, (size_t)length) != TESS_OK)
      status = 0;
    free(bytes);
  }
  if (fclose(f)) status = 0;
  return status;
}
int main(int argc, char** argv) {
  double xyz[24] = {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0};
  size_t rings[] = {0, 4, 8};
  tess_input in = {xyz, 4, rings, 1};
  tess_result* r = NULL;
  int mode = 0;
  size_t i, j;
  tess_options options = tess_default_options();
  if (argc < 2) return 2;
  if (argc > 2) {
    if (!strcmp(argv[2], "remesh"))
      mode = 1;
    else if (!strcmp(argv[2], "remesh-features"))
      mode = 2;
    else if (!strcmp(argv[2], "approx")) {
      mode = 3;
      xyz[8] = 1;
      options.chart_axis = 2;
    } else if (!strcmp(argv[2], "hole")) {
      const double h[] = {0, 0, 0, 4, 0, 0, 4, 4, 0, 0, 4, 0,
                          1, 1, 0, 1, 3, 0, 3, 3, 0, 3, 1, 0};
      memcpy(xyz, h, sizeof(h));
      in.vertex_count = 8;
      in.ring_count = 2;
    } else if (!strcmp(argv[2], "concave")) {
      const double h[] = {0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 1, 0, 1, 2, 0, 0, 2, 0};
      memcpy(xyz, h, sizeof(h));
      in.vertex_count = 6;
      rings[1] = 6;
    } else
      xyz[8] = 1;
  }
  if (!mode && argc > 3)
    for (i = 0; i < 3; i++) {
      double t = xyz[i];
      xyz[i] = xyz[9 + i];
      xyz[9 + i] = t;
      t = xyz[3 + i];
      xyz[3 + i] = xyz[6 + i];
      xyz[6 + i] = t;
    }
  if (tess_triangulate(&in, &options, &r) != TESS_OK) return 3;
  if (mode) {
    tess_remesh_options remesh = tess_default_remesh_options();
    tess_run_report report;
    if (argc < 4) return 2;
    remesh.subdivide_boundary = 1;
    if (mode == 2) {
      tess_seed_feature features[2] = {{0, 1, 42}, {0, 0, 99}};
      remesh.subdivide_features = 1;
      for (i = 0; i < r->mesh.nf; i++)
        for (j = 0; j < 3; j++) {
          size_t a = r->mesh.f[i].v[j], b = r->mesh.f[i].v[(j + 1) % 3];
          if ((a + 1) % 4 != b && (b + 1) % 4 != a) {
            features[1].a = a;
            features[1].b = b;
          }
        }
      if (tess_set_seed_features(r, features, 2, NULL, 0) != TESS_OK) return 4;
    }
    if (mode == 3) remesh.height_tolerance = .5;
    if (tess_prepare_remesh(r, &remesh) != TESS_OK || !write_cert(r, argv[1]))
      return 5;
    if (mode == 3) {
      size_t n = 0;
      for (i = 0; i < r->mesh.ne; i++) {
        if (r->mesh.e[i].constraint == 2) {
          qr_clear(&r->mesh.c, &r->mesh.e[i].ta);
          qr_clear(&r->mesh.c, &r->mesh.e[i].tb);
          memset(&r->mesh.e[i], 0, sizeof(te));
        } else {
          if (n != i) {
            r->mesh.e[n] = r->mesh.e[i];
            memset(&r->mesh.e[i], 0, sizeof(te));
          }
          n++;
        }
      }
      r->mesh.ne = n;
      int diagonal02 = 0;
      for (i = 0; i < r->seed.nf; i++)
        for (j = 0; j < 3; j++)
          if ((r->seed.f[i].v[j] == 0 && r->seed.f[i].v[(j + 1) % 3] == 2) ||
              (r->seed.f[i].v[j] == 2 && r->seed.f[i].v[(j + 1) % 3] == 0))
            diagonal02 = 1;
      if (diagonal02) {
        r->mesh.f[0] = (tf){.v = {0, 1, 3}, .id = 0};
        r->mesh.f[1] = (tf){.v = {1, 2, 3}, .id = 1};
      } else {
        r->mesh.f[0] = (tf){.v = {0, 1, 2}, .id = 0};
        r->mesh.f[1] = (tf){.v = {0, 2, 3}, .id = 1};
      }
    } else if (tess_remesh(r, NULL, &report) != TESS_VALID_TARGETS_MET)
      return 6;
    if (!write_cert(r, argv[3])) return 7;
  } else if (!write_cert(r, argv[1]))
    return 8;
  tess_result_free(r);
  return 0;
}

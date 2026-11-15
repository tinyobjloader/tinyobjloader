/* SPDX-License-Identifier: MIT */
#ifndef TESS_OBJ_SUPPORT_H
#define TESS_OBJ_SUPPORT_H
#include "result.h"
typedef struct {
  tess_options library;
  tess_remesh_options remesh;
  size_t count;
  double area;
  int optimize;
  const char *input, *output, *lean;
} cli_options;
int cli_parse(cli_options* options, int argc, char** argv);
int bundle_record(FILE* f, const char* kind, const void* bytes, size_t length,
                  size_t limit);
int bundle_certificate(FILE* bundle, const char* kind, tess_result* result,
                       const double* rounded, size_t count, FILE* request,
                       const char* lean, size_t limit);
FILE* request_certificate(tess_result* result);
int bundle_json_map(FILE* bundle, const char* kind, size_t face_start,
                    size_t patch, const tm* input, const size_t* map,
                    const tess_result* result, const size_t* source_faces,
                    size_t source_count, size_t limit);
int bundle_stream(FILE* bundle, const char* kind, FILE* stream, size_t limit);
int bundle_options(FILE* bundle, const cli_options* options, const qr* target,
                   size_t limit);
int bundle_stats(FILE* bundle, const char* kind, size_t patch,
                 const tess_quality* quality, const tess_run_report* run,
                 double seconds, int lean_verified, size_t limit);
#endif

/* SPDX-License-Identifier: MIT */
#define _POSIX_C_SOURCE 200809L
#include "obj_support.h"

#include <errno.h>
#include <inttypes.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#ifndef _WIN32
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>
#endif
static int size_arg(const char* s, size_t* out) {
  char* end;
  uintmax_t n;
  if (!*s || *s == '-' || *s == '+') return 0;
  errno = 0;
  n = strtoumax(s, &end, 10);
  if (errno || *end || n > SIZE_MAX) return 0;
  *out = (size_t)n;
  return 1;
}
static int real_arg(const char* s, double* out) {
  char* end;
  errno = 0;
  *out = strtod(s, &end);
  return !errno && end != s && !*end && isfinite(*out) && *out >= 0;
}
int cli_parse(cli_options* o, int argc, char** argv) {
  int i;
  size_t positions = 0;
  memset(o, 0, sizeof(*o));
  o->library = tess_default_options();
  o->remesh = tess_default_remesh_options();
  for (i = 1; i < argc; i++) {
    const char* a = argv[i];
    if (!strcmp(a, "--planar"))
      o->library.strict_planar = 1;
    else if (!strcmp(a, "--graph"))
      o->library.strict_planar = 0;
    else if (!strcmp(a, "--subdivide-boundary"))
      o->remesh.subdivide_boundary = 1;
    else if (!strcmp(a, "--subdivide-features"))
      o->remesh.subdivide_features = 1;
    else if (!strcmp(a, "--target-count")) {
      if (++i == argc || !size_arg(argv[i], &o->count) || !o->count) return 0;
      o->optimize = 1;
    } else if (!strcmp(a, "--target-area")) {
      if (++i == argc || !real_arg(argv[i], &o->area) || !o->area) return 0;
      o->optimize = 1;
    } else if (!strcmp(a, "--height-tolerance")) {
      if (++i == argc || !real_arg(argv[i], &o->remesh.height_tolerance))
        return 0;
    } else if (!strcmp(a, "--chart-axis")) {
      size_t axis;
      if (++i == argc || !size_arg(argv[i], &axis) || axis > 2) return 0;
      o->library.chart_axis = (int)axis;
    } else if (!strcmp(a, "--max-area-cv")) {
      if (++i == argc || !real_arg(argv[i], &o->remesh.max_area_cv)) return 0;
    } else if (!strcmp(a, "--min-band-fraction")) {
      if (++i == argc ||
          !real_arg(argv[i], &o->remesh.min_fraction_target_band) ||
          o->remesh.min_fraction_target_band > 1)
        return 0;
    } else if (!strcmp(a, "--min-angle-p05")) {
      if (++i == argc || !real_arg(argv[i], &o->remesh.min_angle_p05) ||
          o->remesh.min_angle_p05 >= 180)
        return 0;
    } else if (!strcmp(a, "--max-limbs")) {
      if (++i == argc || !size_arg(argv[i], &o->library.max_limbs) ||
          !o->library.max_limbs)
        return 0;
    } else if (!strcmp(a, "--max-operations")) {
      if (++i == argc || !size_arg(argv[i], &o->library.max_operations) ||
          !o->library.max_operations)
        return 0;
    } else if (!strcmp(a, "--max-bytes")) {
      if (++i == argc || !size_arg(argv[i], &o->library.max_bytes) ||
          !o->library.max_bytes)
        return 0;
    } else if (!strcmp(a, "--max-vertices")) {
      if (++i == argc || !size_arg(argv[i], &o->library.max_vertices) ||
          !o->library.max_vertices)
        return 0;
    } else if (!strcmp(a, "--max-faces")) {
      if (++i == argc || !size_arg(argv[i], &o->library.max_faces) ||
          !o->library.max_faces)
        return 0;
    } else if (!strcmp(a, "--max-passes")) {
      if (++i == argc || !size_arg(argv[i], &o->remesh.max_passes)) return 0;
    } else if (!strcmp(a, "--max-edits")) {
      if (++i == argc || !size_arg(argv[i], &o->remesh.max_edits)) return 0;
    } else if (!strcmp(a, "--max-candidates")) {
      if (++i == argc || !size_arg(argv[i], &o->remesh.max_candidates))
        return 0;
    } else if (!strcmp(a, "--lean-checker")) {
      if (++i == argc) return 0;
      o->lean = argv[i];
    } else if (a[0] == '-')
      return 0;
    else if (positions++ == 0)
      o->input = a;
    else if (positions == 2)
      o->output = a;
    else
      return 0;
  }
  return positions == 2 && !(o->count && o->area);
}
int bundle_record(FILE* f, const char* kind, const void* bytes, size_t length,
                  size_t limit) {
  long position = ftell(f);
  size_t overhead = strlen(kind) + 32;
  if (position < 0 || (size_t)position > limit ||
      overhead > limit - (size_t)position ||
      length > limit - (size_t)position - overhead)
    return 0;
  if (fprintf(f, "%s\n%zu\n", kind, length) < 0) return 0;
  return fwrite(bytes, 1, length, f) == length;
}
static char* read_stream(FILE* f, size_t* length, size_t limit) {
  long n;
  char* bytes;
  if (fflush(f) || fseek(f, 0, SEEK_END)) return NULL;
  n = ftell(f);
  if (n < 0 || (uintmax_t)n > limit || fseek(f, 0, SEEK_SET)) return NULL;
  *length = (size_t)n;
  bytes = malloc(*length ? *length : 1);
  if (!bytes) return NULL;
  if (fread(bytes, 1, *length, f) != *length) {
    free(bytes);
    return NULL;
  }
  return bytes;
}
static int lean_pair(const char* checker, const char* request, size_t nr,
                     const char* result, size_t no) {
#ifndef _WIN32
  int pipes[2], status;
  pid_t pid;
  FILE* output;
  int ok = 1;
  if (pipe(pipes)) return 0;
  pid = fork();
  if (pid < 0) {
    close(pipes[0]);
    close(pipes[1]);
    return 0;
  }
  if (pid == 0) {
    if (dup2(pipes[0], STDIN_FILENO) < 0 ||
        dup2(STDERR_FILENO, STDOUT_FILENO) < 0)
      _exit(127);
    close(pipes[0]);
    close(pipes[1]);
    execl(checker, checker, "--stdin", (char*)NULL);
    _exit(127);
  }
  close(pipes[0]);
  signal(SIGPIPE, SIG_IGN);
  output = fdopen(pipes[1], "wb");
  if (!output) {
    close(pipes[1]);
    ok = 0;
  } else {
    if (fwrite(request, 1, nr, output) != nr || fputc(0, output) == EOF ||
        fwrite(result, 1, no, output) != no)
      ok = 0;
    if (fclose(output)) ok = 0;
  }
  while (waitpid(pid, &status, 0) < 0) {
    if (errno != EINTR) return 0;
  }
  return ok && WIFEXITED(status) && WEXITSTATUS(status) == 0;
#else
  (void)checker;
  (void)request;
  (void)nr;
  (void)result;
  (void)no;
  fprintf(stderr, "external Lean checks require the POSIX driver\n");
  return 0;
#endif
}
FILE* request_certificate(tess_result* r) {
  FILE* f = tmpfile();
  if (!f) return NULL;
  if (tess_write_certificate(r, f) != TESS_OK) {
    fclose(f);
    return NULL;
  }
  return f;
}
int bundle_certificate(FILE* bundle, const char* kind, tess_result* r,
                       const double* rounded, size_t count, FILE* request,
                       const char* lean, size_t limit) {
  FILE* f = tmpfile();
  char *bytes = NULL, *req = NULL;
  size_t length = 0, nr = 0;
  int ok = 0;
  tess_status status;
  if (!f) return 0;
  status = rounded ? tess_write_export_certificate(r, rounded, count, f)
                   : tess_write_certificate(r, f);
  if (status != TESS_OK) {
    fprintf(stderr, "certificate write: %s\n", tess_status_string(status));
    goto end;
  }
  bytes = read_stream(f, &length, limit);
  if (!bytes) goto end;
  status = tess_check_certificate(r, bytes, length);
  if (status != TESS_OK) {
    fprintf(stderr, "independent C certificate check: %s\n",
            tess_status_string(status));
    goto end;
  }
  if (lean) {
    if (!request) goto end;
    req = read_stream(request, &nr, limit);
    if (!req || !lean_pair(lean, req, nr, bytes, length)) {
      fprintf(stderr, "Lean certificate check failed\n");
      goto end;
    }
  }
  ok = bundle_record(bundle, kind, bytes, length, limit);
end:
  free(bytes);
  free(req);
  fclose(f);
  return ok;
}
int bundle_json_map(FILE* bundle, const char* kind, size_t face_start,
                    size_t patch, const tm* input, const size_t* map,
                    const tess_result* result, const size_t* source_faces,
                    size_t source_count, size_t limit) {
  FILE* f = tmpfile();
  char* bytes;
  size_t length = 0, i, n = tess_vertex_count(result);
  int ok;
  if (!f) return 0;
  fprintf(f,
          "{\"patch\":%zu,\"output_global_face_start\":%zu,\"source_faces\":[",
          patch, face_start);
  for (i = 0; i < source_count; i++)
    fprintf(f, "%s%zu", i ? "," : "", source_faces[i]);
  fputs("],\"input_global_vertices\":[", f);
  for (i = 0; i < input->nv; i++)
    fprintf(f, "%s%zu", i ? "," : "", input->v[i].source);
  fputs("],\"output_global_vertices\":[", f);
  for (i = 0; i < n; i++) fprintf(f, "%s%zu", i ? "," : "", map[i]);
  fputs("],\"output_stable_ids\":[", f);
  for (i = 0; i < n; i++)
    fprintf(f, "%s%zu", i ? "," : "", tess_vertex_id(result, i));
  fputs("]}\n", f);
  bytes = read_stream(f, &length, limit);
  fclose(f);
  if (!bytes) return 0;
  ok = bundle_record(bundle, kind, bytes, length, limit);
  free(bytes);
  return ok;
}

int bundle_stream(FILE* bundle, const char* kind, FILE* stream, size_t limit) {
  size_t length = 0;
  char* bytes = read_stream(stream, &length, limit);
  int ok;
  if (!bytes) return 0;
  ok = bundle_record(bundle, kind, bytes, length, limit);
  free(bytes);
  return ok;
}
int bundle_options(FILE* bundle, const cli_options* o, const qr* target,
                   size_t limit) {
  FILE* f = tmpfile();
  int ok;
  if (!f) return 0;
  fprintf(f, "{\"target_count\":%zu,\"target_area\":\"", o->count);
  if (target && target->d.n)
    qr_write(f, target);
  else
    fputs("0/00000001", f);
  fprintf(f,
          "\",\"height_tolerance\":%.17g,\"subdivide_boundary\":%s,\"subdivide_"
          "features\":%s,\"chart_axis\":%d,\"strict_planar\":%s,\"max_"
          "operations_per_patch\":%zu,\"max_bytes_per_context\":%zu}\n",
          o->remesh.height_tolerance,
          o->remesh.subdivide_boundary ? "true" : "false",
          o->remesh.subdivide_features ? "true" : "false",
          o->library.chart_axis, o->library.strict_planar ? "true" : "false",
          o->library.max_operations, o->library.max_bytes);
  ok = bundle_stream(bundle, "OPTIONS", f, limit);
  fclose(f);
  return ok;
}
int bundle_stats(FILE* bundle, const char* kind, size_t patch,
                 const tess_quality* q, const tess_run_report* run,
                 double seconds, int lean, size_t limit) {
  FILE* f = tmpfile();
  int ok;
  if (!f) return 0;
  fprintf(
      f,
      "{\"patch\":%zu,\"vertices\":%zu,\"triangles\":%zu,\"target_area\":%.17g,"
      "\"total_area\":%.17g,\"area_cv\":%.17g,\"area_ratio_p05\":%.17g,\"area_"
      "ratio_p50\":%.17g,\"area_ratio_p95\":%.17g,\"min_angle_p05\":%.17g,"
      "\"min_angle_min\":%.17g,\"fraction_target_band\":%.17g,\"mean_ratio\":%."
      "17g,\"mean_squared_log_area_error\":%.17g,\"max_reference_deviation\":%."
      "17g,\"operations\":%zu,\"peak_"
      "core_bytes\":%zu,\"cpu_seconds\":%.9g,\"lean_patch_checked\":%s",
      patch, q->vertices, q->triangles, q->target_area, q->total_area,
      q->area_cv, q->area_ratio_p05, q->area_ratio_p50, q->area_ratio_p95,
      q->min_angle_p05, q->min_angle_min, q->fraction_target_band,
      q->mean_ratio, q->mean_squared_log_area_error, q->max_reference_deviation,
      q->operations, q->peak_bytes, seconds, lean ? "true" : "false");
  if (run)
    fprintf(f,
            ",\"outcome\":%d,\"stop_reason\":%d,\"termination\":%d,\"edits\":%"
            "zu,\"candidates\":%zu,\"validity_rejections\":%zu,\"objective_"
            "rejections\":%zu",
            run->outcome, run->stop_reason, run->termination, run->edits,
            run->candidates, run->validity_rejections,
            run->objective_rejections);
  if (run)
    fprintf(f,
            ",\"passes\":%zu,\"constraint_rejections\":%zu,\"batches\":%zu,"
            "\"edge_splits\":%zu,\"face_splits\":%zu,\"collapses\":%zu,"
            "\"flips\":%zu,\"relocations\":%zu",
            run->passes, run->constraint_rejections, run->batches,
            run->edge_splits, run->face_splits, run->collapses, run->flips,
            run->relocations);
  fputs("}\n", f);
  ok = bundle_stream(bundle, kind, f, limit);
  fclose(f);
  return ok;
}

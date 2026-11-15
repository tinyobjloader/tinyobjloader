/* SPDX-License-Identifier: MIT. Repository OBJ adapter; not part of core. */
#include <inttypes.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "geometry.h"
#include "metrics.h"
#include "obj_number.h"
#include "obj_support.h"
#include "tiny_obj_c.h"
#include "tobj_write.h"
typedef struct {
  size_t *ids, n, parent;
  tm mesh;
} face;
typedef struct {
  size_t a, b, face;
  int used;
} boundary;
static size_t root(face* f, size_t i) {
  while (f[i].parent != i) i = f[i].parent;
  return i;
}
static int same_plane(tm* global, face* a, face* b) {
  size_t i, x, y, z;
  if (!a->mesh.planar || !b->mesh.planar) return 0;
  x = a->ids[a->mesh.f[0].v[0]];
  y = a->ids[a->mesh.f[0].v[1]];
  z = a->ids[a->mesh.f[0].v[2]];
  for (i = 0; i < b->n; i++)
    if (tg_orient3(global, x, y, z, b->ids[i])) return 0;
  return !global->c.status;
}
static int append_triangle(tx* c, tobj_index** ix, size_t* n, size_t* cap,
                           size_t a, size_t b, size_t d) {
  size_t ids[3] = {a, b, d}, i;
  if (*n > SIZE_MAX - 3) return 0;
  if (*n + 3 > *cap) {
    size_t nc = *cap ? *cap * 2 : 48;
    tobj_index* p;
    if (nc < *cap) return 0;
    p = tx_alloc(c, nc, sizeof(*p));
    if (!p) return 0;
    if (*ix) memcpy(p, *ix, *n * sizeof(*p));
    tx_free(c, *ix, *cap * sizeof(*p));
    *ix = p;
    *cap = nc;
  }
  for (i = 0; i < 3; i++) {
    if (ids[i] > INT_MAX) return 0;
    (*ix)[*n].vertex_index = (int)ids[i];
    (*ix)[*n].normal_index = -1;
    (*ix)[*n].texcoord_index = -1;
    (*n)++;
  }
  return 1;
}
static int process_patch(const cli_options* cli, const tobj_scene_d* input,
                         tm* patch, tm* global, face* faces, size_t nf,
                         const boundary* edges, size_t ne, size_t root_id,
                         const qr* target, tx* work, tobj_index** indices,
                         size_t* ni, size_t* icap, FILE* bundle, FILE* requests,
                         size_t* unmet) {
  tess_result* result = NULL;
  FILE* canonical = NULL;
  double *xyz = NULL, *rounded = NULL;
  size_t *map = NULL, *source_faces = NULL, *allowed = NULL;
  size_t i, j, k, n = 0, ns = 0, na = 0, face_start = *ni / 3;
  int ok = 0;
  tess_input rings;
  tess_options library = cli->library;
  tess_diagnostic diagnostic;
  library.diagnostic = &diagnostic;
  tess_remesh_options remesh = cli->remesh;
  tess_run_report run = {0};
  tess_quality quality = {0};
  tess_rational exact;
  tess_status status;
  clock_t started = clock();
  xyz = tx_alloc(work, patch->nv * 3, sizeof(double));
  source_faces = tx_alloc(work, nf, sizeof(size_t));
  allowed = tx_alloc(work, patch->nv, sizeof(size_t));
  if (!xyz || !source_faces || !allowed) goto end;
  for (i = 0; i < patch->nv; i++)
    for (j = 0; j < 3; j++)
      xyz[i * 3 + j] = input->attrib.vertices.ptr[patch->v[i].source * 3 + j];
  for (i = 0; i < nf; i++)
    if (root(faces, i) == root_id) source_faces[ns++] = i;
  rings = (tess_input){xyz, patch->nv, patch->rings, patch->nr};
  status = tess_triangulate(&rings, &library, &result);
  if (status != TESS_OK) {
    fprintf(stderr,
            "patch %zu: %s (reason %d, chart %d, tried %u, ring %zu, vertices "
            "%zu/%zu, edges %zu/%zu)\n",
            root_id, tess_status_string(status), diagnostic.reason,
            diagnostic.axis, diagnostic.charts_tried, diagnostic.ring,
            diagnostic.vertex_a, diagnostic.vertex_b, diagnostic.edge_a,
            diagnostic.edge_b);
    goto end;
  }
  if (cli->optimize) {
    exact = (tess_rational){target->n.sign, target->n.v, target->n.n,
                            target->d.v, target->d.n};
    remesh.target_count = 0;
    remesh.target_area = 0;
    remesh.exact_target_area = &exact;
    if (remesh.subdivide_boundary) {
      for (i = 0; i < patch->nr; i++)
        for (j = patch->rings[i]; j < patch->rings[i + 1]; j++) {
          size_t next = j + 1 == patch->rings[i + 1] ? patch->rings[i] : j + 1,
                 a = patch->v[j].source, b = patch->v[next].source;
          int shared = 0;
          for (k = 0; k < ne; k++)
            if (root(faces, edges[k].face) != root_id &&
                ((edges[k].a == a && edges[k].b == b) ||
                 (edges[k].a == b && edges[k].b == a))) {
              shared = 1;
              break;
            }
          if (!shared) allowed[na++] = j;
        }
      remesh.boundary_owners = allowed;
      remesh.boundary_owner_count = na;
    }
    status = tess_prepare_remesh(result, &remesh);
    if (status != TESS_OK) {
      fprintf(stderr, "patch %zu target: %s\n", root_id,
              tess_status_string(status));
      goto end;
    }
  }
  canonical = request_certificate(result);
  if (!canonical) goto end;
  if (!bundle_stream(requests, "PATCH_REQUEST", canonical, work->max_bytes) ||
      !bundle_stream(bundle, "PATCH_REQUEST", canonical, work->max_bytes))
    goto end;
  map = tx_alloc(work, patch->nv, sizeof(size_t));
  if (!map) goto end;
  for (i = 0; i < patch->nv; i++) map[i] = patch->v[i].source;
  if (!bundle_json_map(requests, "REQUEST_MAP", face_start, root_id, patch, map,
                       result, source_faces, ns, work->max_bytes))
    goto end;
  tx_free(work, map, patch->nv * sizeof(size_t));
  map = NULL;
  if (cli->optimize) {
    status = tess_remesh(result, NULL, &run);
    if (status != TESS_VALID_TARGETS_MET &&
        status != TESS_VALID_TARGETS_UNMET) {
      fprintf(stderr, "patch %zu remesh: %s\n", root_id,
              tess_status_string(status));
      goto end;
    }
    if (status == TESS_VALID_TARGETS_UNMET) (*unmet)++;
    tess_result_quality(result, &quality);
  } else {
    status = tess_measure(result, NULL, &quality);
    if (status != TESS_OK) {
      fprintf(stderr, "patch %zu metrics: %s\n", root_id,
              tess_status_string(status));
      goto end;
    }
  }
  n = tess_vertex_count(result);
  rounded = tx_alloc(work, n * 3, sizeof(double));
  map = tx_alloc(work, n, sizeof(size_t));
  if (!rounded || !map) goto end;
  if (!bundle_certificate(bundle, "PATCH_EXACT", result, NULL, 0, canonical,
                          cli->lean, work->max_bytes))
    goto end;
  status = tess_export_binary64(result, rounded, n * 3);
  if (status != TESS_OK) {
    fprintf(stderr, "patch %zu checked export: %s\n", root_id,
            tess_status_string(status));
    goto end;
  }
  if (!bundle_certificate(bundle, "PATCH_ROUNDED", result, rounded, n * 3,
                          canonical, cli->lean, work->max_bytes))
    goto end;
  for (i = 0; i < n; i++) {
    size_t source = tess_vertex_source(result, i);
    if (source != SIZE_MAX) {
      if (source >= patch->nv) goto end;
      map[i] = patch->v[source].source;
    } else {
      map[i] = global->nv;
      if (!tg_add_vertex(global, &rounded[i * 3], SIZE_MAX)) goto end;
    }
  }
  for (i = 0; i < tess_triangle_count(result); i++) {
    size_t triangle[3];
    if (tess_triangle(result, i, triangle) != TESS_OK ||
        !append_triangle(work, indices, ni, icap, map[triangle[0]],
                         map[triangle[1]], map[triangle[2]]))
      goto end;
  }
  if (!bundle_json_map(bundle, "PATCH_MAP", face_start, root_id, patch, map,
                       result, source_faces, ns, work->max_bytes) ||
      !bundle_stats(
          bundle, "PATCH_REPORT", root_id, &quality,
          cli->optimize ? &run : NULL,
          (double)clock() / CLOCKS_PER_SEC - (double)started / CLOCKS_PER_SEC,
          cli->lean != NULL, work->max_bytes))
    goto end;
  fprintf(stderr,
          "patch %zu: %zu triangles, CV %.6g, band %.4g, angle05 %.6g%s\n",
          root_id, quality.triangles, quality.area_cv,
          quality.fraction_target_band, quality.min_angle_p05,
          cli->optimize && run.outcome == TESS_VALID_TARGETS_UNMET
              ? " (targets unmet)"
              : "");
  ok = 1;
end:
  if (canonical) fclose(canonical);
  tess_result_free(result);
  tx_free(work, xyz, patch->nv * 3 * sizeof(double));
  tx_free(work, rounded, n * 3 * sizeof(double));
  tx_free(work, map, (n ? n : patch->nv) * sizeof(size_t));
  tx_free(work, source_faces, nf * sizeof(size_t));
  tx_free(work, allowed, patch->nv * sizeof(size_t));
  return ok;
}
int main(int argc, char** argv) {
  tobj_scene_d in = {0}, out = {0}, reload = {0};
  tobj_load_config cfg = tobj_default_config();
  tobj_result load;
  tm global;
  face* faces = NULL;
  boundary* edges = NULL;
  size_t nf = 0, ne = 0, i, j, k, fi = 0;
  tx work;
  int status = 1, strict = 0;
  size_t *cycle = NULL, *offset = NULL, *order = NULL;
  size_t cycle_cap = 0;
  tobj_index* indices = NULL;
  size_t ni = 0, icap = 0;
  unsigned int* arities = NULL;
  char *buf = NULL, *tmp = NULL;
  size_t buflen = 0;
  FILE* file = NULL;
  const char *input, *output;
  cli_options cli;
  FILE *bundle = NULL, *requests = NULL, *source_file = NULL;
  char *bundle_tmp = NULL, *bundle_path = NULL, *request_tmp = NULL,
       *request_path = NULL, *source_bytes = NULL;
  double* output_xyz = NULL;
  size_t source_length = 0, unmet = 0;
  int bundle_created = 0, request_created = 0;
  qr target = {0};
  clock_t started = clock();
  tess_quality assembled_quality;
  if (!cli_parse(&cli, argc, argv)) {
    fprintf(
        stderr,
        "usage: tess_obj [--planar|--graph] [--target-count N|--target-area A] "
        "[--subdivide-boundary] [--subdivide-features] [--height-tolerance H] "
        "[--chart-axis 0|1|2] [--max-operations N] [--max-bytes N] "
        "[--max-vertices N] [--max-faces N] [--max-passes N] [--max-edits N] "
        "[--max-candidates N] [--lean-checker PATH] input.obj output.obj\n");
    return 2;
  }
  input = cli.input;
  output = cli.output;
  strict = cli.library.strict_planar;
  tx_init(&work);
  tm_init(&global);
  work.max_bytes = cli.library.max_bytes;
  global.c.max_bytes = cli.library.max_bytes;
  global.c.max_ops = cli.library.max_operations;
  global.max_vertices = cli.library.max_vertices;
  global.max_faces = cli.library.max_faces;
  {
    size_t length = strlen(output);
    if (length > SIZE_MAX - 20) goto end;
    bundle_path = tx_alloc(&work, length + 6, 1);
    bundle_tmp = tx_alloc(&work, length + 10, 1);
    request_path = tx_alloc(&work, length + 14, 1);
    request_tmp = tx_alloc(&work, length + 18, 1);
    if (!bundle_path || !bundle_tmp || !request_path || !request_tmp) goto end;
    snprintf(bundle_path, length + 6, "%s.tess", output);
    snprintf(bundle_tmp, length + 10, "%s.tess.tmp", output);
    snprintf(request_path, length + 14, "%s.tess-request", output);
    snprintf(request_tmp, length + 18, "%s.tess-request.tmp", output);
    bundle = fopen(bundle_tmp, "wbx");
    if (!bundle) {
      perror(bundle_tmp);
      goto end;
    }
    bundle_created = 1;
    requests = fopen(request_tmp, "wbx");
    if (!requests) {
      perror(request_tmp);
      goto end;
    }
    request_created = 1;
    fputs("TESS-ASSET1\n", bundle);
    fputs("TESS-ASSET-REQUEST1\n", requests);
  }
  source_file = fopen(input, "rb");
  if (!source_file) {
    perror(input);
    goto end;
  }
  if (fseek(source_file, 0, SEEK_END)) goto end;
  {
    long n = ftell(source_file);
    if (n < 0 || (uintmax_t)n >= work.max_bytes) goto end;
    source_length = (size_t)n;
  }
  if (fseek(source_file, 0, SEEK_SET)) goto end;
  source_bytes = tx_alloc(&work, source_length + 1, 1);
  if (!source_bytes ||
      fread(source_bytes, 1, source_length, source_file) != source_length)
    goto end;
  fclose(source_file);
  source_file = NULL;
  if (!bundle_record(bundle, "SOURCE", source_bytes, source_length,
                     work.max_bytes) ||
      !bundle_record(requests, "SOURCE", source_bytes, source_length,
                     work.max_bytes))
    goto end;
  cfg.max_vertices = cli.library.max_vertices;
  cfg.max_faces = cli.library.max_faces;
  cfg.max_input_bytes = work.max_bytes;
  cfg.triangulate = false;
  cfg.store_vertex_colors = false;
  cfg.num_threads = 1;
  tess_obj_numbers_reset();
  load = tobj_load_obj_from_memory_d(&in, (const uint8_t*)source_bytes,
                                     source_length, &cfg, NULL);
  if (load == TOBJ_OK && tess_obj_numbers_error())
    load = tess_obj_numbers_error() == 2 ? TOBJ_ERR_LIMIT_EXCEEDED
                                         : TOBJ_ERR_PARSE;
  if (load != TOBJ_OK) {
    fprintf(stderr, "OBJ load failed: %d\n", load);
    goto end;
  }
  for (i = 0; i < in.num_shapes; i++) {
    if (nf > SIZE_MAX - in.shapes[i].mesh.num_faces) goto end;
    nf += in.shapes[i].mesh.num_faces;
  }
  if (!nf) {
    fprintf(stderr, "no polygon faces\n");
    goto end;
  }
  faces = tx_alloc(&work, nf, sizeof(*faces));
  if (!faces) goto end;
  for (i = 0; i < in.attrib.vertices.count / 3; i++)
    if (!tg_add_vertex(&global, &in.attrib.vertices.ptr[i * 3], i)) goto end;
  for (i = 0; i < in.num_shapes; i++) {
    tobj_mesh_d* mesh = &in.shapes[i].mesh;
    size_t pos = 0;
    for (j = 0; j < mesh->num_faces; j++, fi++) {
      face* f = &faces[fi];
      f->n = mesh->num_face_vertices[j];
      f->parent = fi;
      tm_init(&f->mesh);
      f->mesh.c.max_bytes = cli.library.max_bytes;
      f->mesh.c.max_ops = cli.library.max_operations;
      f->mesh.max_vertices = cli.library.max_vertices;
      f->mesh.max_faces = cli.library.max_faces;
      if (f->n < 3 || f->n > mesh->num_indices - pos) goto end;
      f->ids = tx_alloc(&work, f->n, sizeof(size_t));
      if (!f->ids) goto end;
      for (k = 0; k < f->n; k++) {
        int id = mesh->indices[pos++].vertex_index;
        if (id < 0 || (size_t)id >= global.nv) {
          fprintf(stderr, "face %zu: invalid vertex index\n", fi);
          goto end;
        }
        f->ids[k] = (size_t)id;
        if (!tg_add_vertex(&f->mesh, &in.attrib.vertices.ptr[(size_t)id * 3],
                           (size_t)id))
          goto end;
      }
      f->mesh.nr = 1;
      f->mesh.rings = tx_alloc(&f->mesh.c, 2, sizeof(size_t));
      if (!f->mesh.rings) goto end;
      f->mesh.rings[1] = f->n;
      if (!tg_prepare(&f->mesh, cli.library.chart_axis, strict) ||
          !tg_seed(&f->mesh)) {
        fprintf(stderr,
                "face %zu: %s (reason %d, chart %d, tried %u, corners %zu/%zu, "
                "edges %zu/%zu)\n",
                fi, tess_status_string(f->mesh.c.status),
                f->mesh.diagnostic.reason, f->mesh.diagnostic.axis,
                f->mesh.diagnostic.charts_tried, f->mesh.diagnostic.vertex_a,
                f->mesh.diagnostic.vertex_b, f->mesh.diagnostic.edge_a,
                f->mesh.diagnostic.edge_b);
        goto end;
      }
      if (ne > SIZE_MAX - f->n) goto end;
      ne += f->n;
    }
  }
  for (i = 0; i < nf; i++)
    for (j = 0; j < faces[i].mesh.nf; j++) {
      tf* f = &faces[i].mesh.f[j];
      if (!tg_add_face(&global, faces[i].ids[f->v[0]], faces[i].ids[f->v[1]],
                       faces[i].ids[f->v[2]]))
        goto end;
    }
  if (!tg_audit3(&global) || !tg_topology(&global, 0)) {
    fprintf(stderr, "source asset has forbidden 3D intersections\n");
    goto end;
  }
  if (cli.optimize) {
    if (cli.count) {
      if (!tg_count_target(&global, &global, cli.count, &target)) {
        fprintf(stderr, "global physical-area target: %s\n",
                tess_status_string(global.c.status));
        goto end;
      }
    } else
      qr_double(&global.c, &target, cli.area);
  }
  if (!bundle_options(bundle, &cli, &target, work.max_bytes) ||
      !bundle_options(requests, &cli, &target, work.max_bytes))
    goto end;
  edges = tx_alloc(&work, ne, sizeof(*edges));
  if (!edges) goto end;
  k = 0;
  for (i = 0; i < nf; i++)
    for (j = 0; j < faces[i].n; j++) {
      edges[k].a = faces[i].ids[j];
      edges[k].b = faces[i].ids[(j + 1) % faces[i].n];
      edges[k++].face = i;
    }
  /* Shared source-index edges alone define adjacency; no coordinate welding. */
  for (i = 0; i < ne; i++) {
    size_t incidents = 1;
    for (j = i + 1; j < ne; j++) {
      int same = edges[i].a == edges[j].a && edges[i].b == edges[j].b;
      int opposite = edges[i].a == edges[j].b && edges[i].b == edges[j].a;
      if (same || opposite) {
        size_t a, b;
        incidents++;
        if (same || incidents > 2) {
          fprintf(stderr, "inconsistent or nonmanifold source edge %zu-%zu\n",
                  edges[i].a, edges[i].b);
          goto end;
        }
        if (same_plane(&global, &faces[edges[i].face], &faces[edges[j].face])) {
          a = root(faces, edges[i].face);
          b = root(faces, edges[j].face);
          if (a != b) faces[b].parent = a;
        }
      }
    }
  }
  for (i = 0; i < ne; i++)
    for (j = i + 1; j < ne; j++)
      if (edges[i].a == edges[j].b && edges[i].b == edges[j].a &&
          root(faces, edges[i].face) == root(faces, edges[j].face))
        edges[i].used = edges[j].used = 1;
  cycle_cap = ne;
  cycle = tx_alloc(&work, ne, sizeof(size_t));
  offset = tx_alloc(&work, ne + 1, sizeof(size_t));
  order = tx_alloc(&work, ne, sizeof(size_t));
  if (!cycle || !offset || !order) goto end;
  for (fi = 0; fi < nf; fi++)
    if (root(faces, fi) == fi) {
      tm patch;
      size_t nc = 0, nr = 0, r, t;
      int patchok = 0;
      tm_init(&patch);
      for (i = 0; i < ne; i++)
        if (!edges[i].used && root(faces, edges[i].face) == fi) {
          size_t cur = i;
          offset[nr++] = nc;
          do {
            size_t next = SIZE_MAX;
            if (edges[cur].used || nc >= ne) goto patch_end;
            edges[cur].used = 1;
            cycle[nc++] = edges[cur].a;
            for (j = 0; j < ne; j++)
              if (root(faces, edges[j].face) == fi && !edges[j].used &&
                  edges[j].a == edges[cur].b) {
                if (next != SIZE_MAX) {
                  fprintf(stderr, "branching patch boundary\n");
                  goto patch_end;
                }
                next = j;
              }
            if (edges[cur].b == edges[i].a) break;
            if (next == SIZE_MAX) goto patch_end;
            cur = next;
          } while (1);
        }
      offset[nr] = nc;
      if (!nr) goto patch_end;
      /* Largest absolute projected cycle area is outer; verify all domain rules
       * afterwards. */
      {
        qr best = {0}, a = {0}, p = {0}, q = {0};
        size_t outer = 0;
        int u = faces[fi].mesh.u, w = faces[fi].mesh.w;
        for (r = 0; r < nr; r++) {
          qr_i64(&patch.c, &a, 0);
          for (j = offset[r]; j < offset[r + 1]; j++) {
            size_t v = cycle[j],
                   z = cycle[j + 1 == offset[r + 1] ? offset[r] : j + 1];
            qr_mul(&patch.c, &p, &global.v[v].p[u], &global.v[z].p[w]);
            qr_mul(&patch.c, &q, &global.v[z].p[u], &global.v[v].p[w]);
            qr_sub(&patch.c, &p, &p, &q);
            qr_add(&patch.c, &a, &a, &p);
          }
          a.n.sign = a.n.n ? 1 : 0;
          if (qr_cmp(&patch.c, &a, &best) > 0) {
            qr_copy(&patch.c, &best, &a);
            outer = r;
          }
        }
        order[0] = outer;
        t = 1;
        for (r = 0; r < nr; r++)
          if (r != outer) order[t++] = r;
        qr_clear(&patch.c, &best);
        qr_clear(&patch.c, &a);
        qr_clear(&patch.c, &p);
        qr_clear(&patch.c, &q);
      }
      patch.nr = nr;
      patch.rings = tx_alloc(&patch.c, nr + 1, sizeof(size_t));
      if (!patch.rings) goto patch_end;
      for (r = 0; r < nr; r++) {
        patch.rings[r] = patch.nv;
        for (j = offset[order[r]]; j < offset[order[r] + 1]; j++) {
          size_t id = cycle[j];
          if (!tg_add_vertex(&patch, &in.attrib.vertices.ptr[id * 3], id))
            goto patch_end;
        }
      }
      patch.rings[nr] = patch.nv;
      if (!process_patch(&cli, &in, &patch, &global, faces, nf, edges, ne, fi,
                         cli.optimize ? &target : NULL, &work, &indices, &ni,
                         &icap, bundle, requests, &unmet))
        goto patch_end;
      patchok = 1;
    patch_end:
      tm_clear(&patch);
      if (!patchok) goto end;
    }
  global.nf = 0;
  for (i = 0; i < ni; i += 3)
    if (!tg_add_face(&global, (size_t)indices[i].vertex_index,
                     (size_t)indices[i + 1].vertex_index,
                     (size_t)indices[i + 2].vertex_index))
      goto end;
  if (!tg_audit3(&global) || !tg_topology(&global, 0)) {
    fprintf(stderr, "assembled output has forbidden intersections\n");
    goto end;
  }
  output_xyz = tx_alloc(&work, global.nv * 3, sizeof(double));
  if (!output_xyz) goto end;
  for (i = 0; i < global.nv; i++)
    for (j = 0; j < 3; j++)
      if (!tx_report_double(qr_approx(&global.v[i].p[j]),
                            &output_xyz[i * 3 + j]))
        goto end;
  out.attrib.vertices.ptr = output_xyz;
  out.attrib.vertices.count = global.nv * 3;
  out.num_shapes = 1;
  out.shapes = tx_alloc(&work, 1, sizeof(tobj_shape_d));
  if (!out.shapes) goto end;
  out.shapes[0].mesh.indices = indices;
  out.shapes[0].mesh.num_indices = ni;
  out.shapes[0].mesh.num_faces = ni / 3;
  arities = tx_alloc(&work, ni / 3, sizeof(unsigned int));
  if (!arities) goto end;
  for (i = 0; i < ni / 3; i++) arities[i] = 3;
  out.shapes[0].mesh.num_face_vertices = arities;
  buflen = tobj_write_obj_d(&out, NULL, 0);
  if (buflen == SIZE_MAX) goto end;
  buf = tx_alloc(&work, buflen + 1, 1);
  if (!buf) goto end;
  if (tobj_write_obj_d(&out, buf, buflen + 1) != buflen) goto end;
  tess_obj_numbers_reset();
  load = tobj_load_obj_from_memory_d(&reload, (const uint8_t*)buf, buflen, &cfg,
                                     NULL);
  if (load != TOBJ_OK || tess_obj_numbers_error() ||
      reload.attrib.vertices.count != out.attrib.vertices.count)
    goto end;
  for (i = 0; i < out.attrib.vertices.count; i++)
    if (reload.attrib.vertices.ptr[i] != out.attrib.vertices.ptr[i]) {
      fprintf(stderr, "OBJ numeric roundtrip failed\n");
      goto end;
    }
  if (!bundle_record(bundle, "OBJ", buf, buflen, work.max_bytes)) goto end;
  if (tg_quality(&global, cli.optimize ? &target : NULL, &assembled_quality) !=
      TESS_OK)
    goto end;
  if (!bundle_stats(
          bundle, "REPORT", 0, &assembled_quality, NULL,
          (double)clock() / CLOCKS_PER_SEC - (double)started / CLOCKS_PER_SEC,
          cli.lean != NULL, work.max_bytes))
    goto end;
  if (fputs("END\n", bundle) == EOF || fputs("END\n", requests) == EOF)
    goto end;
  if (fclose(bundle)) {
    bundle = NULL;
    goto end;
  }
  bundle = NULL;
  if (fclose(requests)) {
    requests = NULL;
    goto end;
  }
  requests = NULL;
  {
    size_t len = strlen(output);
    if (len > SIZE_MAX - 5) goto end;
    tmp = tx_alloc(&work, len + 5, 1);
    if (!tmp) goto end;
    memcpy(tmp, output, len);
    memcpy(tmp + len, ".tmp", 5);
    file = fopen(tmp, "wbx");
    if (!file) {
      perror(tmp);
      goto end;
    }
    if (fwrite(buf, 1, buflen, file) != buflen) {
      fclose(file);
      file = NULL;
      remove(tmp);
      goto end;
    }
    if (fclose(file)) {
      file = NULL;
      remove(tmp);
      goto end;
    }
    file = NULL;
    if (rename(request_tmp, request_path)) {
      perror("request rename");
      remove(tmp);
      goto end;
    }
    request_created = 0;
    if (rename(bundle_tmp, bundle_path)) {
      perror("artifact rename");
      remove(tmp);
      goto end;
    }
    bundle_created = 0;
    if (rename(tmp, output)) {
      perror("rename");
      remove(tmp);
      goto end;
    }
  }
  fprintf(stderr,
          "processed %zu faces into %zu triangles (exact planar merging)\n", nf,
          ni / 3);
  printf(
      "{\"triangles\":%zu,\"target_count\":%zu,\"patches_with_targets_unmet\":%"
      "zu,\"area_cv\":%.17g,\"fraction_target_band\":%.17g,\"min_angle_p05\":%."
      "17g}\n",
      ni / 3, cli.count, unmet, assembled_quality.area_cv,
      assembled_quality.fraction_target_band, assembled_quality.min_angle_p05);
  status = unmet ? 4 : 0;
end:
  if (status && status != 4)
    fprintf(stderr, "processing failed (adapter=%s, geometry=%s)\n",
            tess_status_string(work.status),
            tess_status_string(global.c.status));
  if (file) fclose(file);
  if (source_file) fclose(source_file);
  if (bundle) fclose(bundle);
  if (requests) fclose(requests);
  if (bundle_created) remove(bundle_tmp);
  if (request_created) remove(request_tmp);
  if (faces)
    for (i = 0; i < nf; i++) {
      tx_free(&work, faces[i].ids, faces[i].n * sizeof(size_t));
      tm_clear(&faces[i].mesh);
    }
  tx_free(&work, faces, nf * sizeof(*faces));
  tx_free(&work, edges, ne * sizeof(*edges));
  tx_free(&work, cycle, cycle_cap * sizeof(size_t));
  tx_free(&work, offset, (cycle_cap + 1) * sizeof(size_t));
  tx_free(&work, order, cycle_cap * sizeof(size_t));
  tx_free(&work, indices, icap * sizeof(*indices));
  tx_free(&work, arities, (ni / 3) * sizeof(unsigned int));
  tx_free(&work, out.shapes, sizeof(tobj_shape_d));
  tx_free(&work, buf, buflen + 1);
  if (tmp) tx_free(&work, tmp, strlen(tmp) + 1);
  tx_free(&work, output_xyz, global.nv * 3 * sizeof(double));
  tx_free(&work, source_bytes, source_length + 1);
  if (bundle_tmp) tx_free(&work, bundle_tmp, strlen(output) + 10);
  if (bundle_path) tx_free(&work, bundle_path, strlen(output) + 6);
  if (request_tmp) tx_free(&work, request_tmp, strlen(output) + 18);
  if (request_path) tx_free(&work, request_path, strlen(output) + 14);
  qr_clear(&global.c, &target);
  tm_clear(&global);
  tobj_scene_free_d(&reload);
  tobj_scene_free_d(&in);
  return status;
}

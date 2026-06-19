/*
 * tester_c.c -- loader tests for tiny_obj_c (pure C11, acutest).
 * Run from the tests/ directory so that "../models/..." paths resolve.
 * Built with TOBJ_ENABLE_FILE_IO + TOBJ_ENABLE_MMAP under ASan+UBSan.
 */
#include "acutest.h"
#include "tiny_obj_c.h"

#include <string.h>

/* ---- helpers ----------------------------------------------------------- */

static tobj_result load_file_f(const char *path, tobj_scene_f *sc) {
  tobj_load_config cfg = tobj_default_config();
  return tobj_load_obj_from_file_f(sc, path, &cfg, NULL);
}

/* sum of per-face vertex counts must equal the index count */
static int mesh_consistent_f(const tobj_scene_f *sc) {
  for (size_t s = 0; s < sc->num_shapes; s++) {
    const tobj_mesh_f *m = &sc->shapes[s].mesh;
    size_t sum = 0;
    for (size_t f = 0; f < m->num_faces; f++) sum += m->num_face_vertices[f];
    if (sum != m->num_indices) return 0;
    /* every index that references a vertex must be in range */
    size_t numv = sc->attrib.vertices.count / 3;
    for (size_t i = 0; i < m->num_indices; i++) {
      int vi = m->indices[i].vertex_index;
      if (vi >= 0 && (size_t)vi >= numv) return 0;
    }
  }
  return 1;
}

static const char *load_string_f(const char *obj, tobj_scene_f *sc,
                                  bool triangulate) {
  tobj_load_config cfg = tobj_default_config();
  cfg.triangulate = triangulate;
  tobj_result r =
      tobj_load_obj_from_memory_f(sc, (const uint8_t *)obj, strlen(obj), &cfg,
                                  NULL);
  return tobj_result_string(r);
}

typedef struct mem_io {
  const uint8_t *data;
  size_t len;
  size_t pos;
  size_t chunk;
  int closed;
} mem_io;

static tobj_result mem_io_read(void *ud, uint8_t *dst, size_t dst_size,
                               size_t *bytes_read) {
  mem_io *m = (mem_io *)ud;
  size_t left = m->len - m->pos;
  size_t n = left < dst_size ? left : dst_size;
  if (m->chunk && n > m->chunk) n = m->chunk;
  if (n) memcpy(dst, m->data + m->pos, n);
  m->pos += n;
  *bytes_read = n;
  return TOBJ_OK;
}

static void mem_io_close(void *ud) { ((mem_io *)ud)->closed = 1; }

static tobj_result io_overreport_read(void *ud, uint8_t *dst, size_t dst_size,
                                      size_t *bytes_read) {
  (void)ud;
  if (dst_size) dst[0] = 'x';
  *bytes_read = dst_size + 1;
  return TOBJ_OK;
}

static tobj_result io_error_read(void *ud, uint8_t *dst, size_t dst_size,
                                 size_t *bytes_read) {
  (void)ud;
  (void)dst;
  (void)dst_size;
  *bytes_read = 0;
  return TOBJ_ERR_IO;
}

/* ---- corpus ------------------------------------------------------------ */

/* Only files committed to the repo (CI checks out a clean tree; sandbox files
 * are local scratch files and are intentionally not used here). The
 * pathological-geometry triangulation cases are covered directly by
 * tests/tess_tester.c. */
static const char *kCorpus[] = {
    "../models/cube.obj",
    "../models/cornell_box.obj",
    "../models/catmark_torus_creases0.obj",
    "../models/smoothing-group-two-squares.obj",
    "../models/issue-162-smoothing-group.obj",
    "../models/smoothing-normal.obj",
    "../models/issue-295-trianguation-failure.obj",
    NULL};

static void test_corpus_loads(void) {
  for (int i = 0; kCorpus[i]; i++) {
    tobj_scene_f sc;
    tobj_result r = load_file_f(kCorpus[i], &sc);
    TEST_CHECK_(r == TOBJ_OK, "%s -> %s", kCorpus[i], tobj_result_string(r));
    if (r == TOBJ_OK) {
      TEST_CHECK_(mesh_consistent_f(&sc), "%s mesh consistent", kCorpus[i]);
      tobj_scene_free_f(&sc);
    }
  }
}

static void test_both_precisions(void) {
  tobj_scene_f sf;
  tobj_scene_d sd;
  tobj_load_config cfg = tobj_default_config();
  TEST_CHECK(tobj_load_obj_from_file_f(&sf, "../models/cube.obj", &cfg, NULL) ==
             TOBJ_OK);
  TEST_CHECK(tobj_load_obj_from_file_d(&sd, "../models/cube.obj", &cfg, NULL) ==
             TOBJ_OK);
  /* identical topology across precision families */
  TEST_CHECK(sf.num_shapes == sd.num_shapes);
  TEST_CHECK(sf.attrib.vertices.count == sd.attrib.vertices.count);
  size_t fi = 0, di = 0;
  for (size_t s = 0; s < sf.num_shapes; s++) fi += sf.shapes[s].mesh.num_indices;
  for (size_t s = 0; s < sd.num_shapes; s++) di += sd.shapes[s].mesh.num_indices;
  TEST_CHECK(fi == di);
  tobj_scene_free_f(&sf);
  tobj_scene_free_d(&sd);
}

/* ---- targeted regressions --------------------------------------------- */

static void test_quad_triangulation(void) {
  tobj_scene_f sc;
  const char *obj = "v 0 0 0\nv 1 0 0\nv 1 1 0\nv 0 1 0\nf 1 2 3 4\n";
  load_string_f(obj, &sc, true);
  TEST_CHECK(sc.num_shapes == 1);
  TEST_CHECK(sc.shapes[0].mesh.num_faces == 2);   /* 2 triangles */
  TEST_CHECK(sc.shapes[0].mesh.num_indices == 6); /* 6 indices */
  tobj_scene_free_f(&sc);
}

static void test_no_triangulation(void) {
  tobj_scene_f sc;
  const char *obj = "v 0 0 0\nv 1 0 0\nv 1 1 0\nv 0 1 0\nf 1 2 3 4\n";
  load_string_f(obj, &sc, false);
  TEST_CHECK(sc.shapes[0].mesh.num_faces == 1);
  TEST_CHECK(sc.shapes[0].mesh.num_face_vertices[0] == 4);
  TEST_CHECK(sc.shapes[0].mesh.num_indices == 4);
  tobj_scene_free_f(&sc);
}

static void test_negative_relative_index(void) {
  tobj_scene_f sc;
  /* -1 -2 -3 refer to the three most recent vertices */
  const char *obj = "v 0 0 0\nv 1 0 0\nv 0 1 0\nf -3 -2 -1\n";
  load_string_f(obj, &sc, true);
  TEST_CHECK(sc.shapes[0].mesh.num_indices == 3);
  TEST_CHECK(sc.shapes[0].mesh.indices[0].vertex_index == 0);
  TEST_CHECK(sc.shapes[0].mesh.indices[1].vertex_index == 1);
  TEST_CHECK(sc.shapes[0].mesh.indices[2].vertex_index == 2);
  tobj_scene_free_f(&sc);
}

static void test_bom_and_crlf(void) {
  tobj_scene_f sc;
  const char obj[] = "\xEF\xBB\xBFv 0 0 0\r\nv 1 0 0\r\nv 0 1 0\r\nf 1 2 3\r\n";
  tobj_load_config cfg = tobj_default_config();
  tobj_result r = tobj_load_obj_from_memory_f(&sc, (const uint8_t *)obj,
                                              sizeof(obj) - 1, &cfg, NULL);
  TEST_CHECK(r == TOBJ_OK);
  TEST_CHECK(sc.attrib.vertices.count == 9);
  TEST_CHECK(sc.shapes[0].mesh.num_indices == 3);
  tobj_scene_free_f(&sc);
}

static void test_vertex_colors(void) {
  tobj_scene_f sc;
  const char *obj = "v 0 0 0 1 0 0\nv 1 0 0 0 1 0\nv 0 1 0 0 0 1\nf 1 2 3\n";
  load_string_f(obj, &sc, true);
  TEST_CHECK(sc.attrib.colors.count == 9);
  TEST_CHECK(sc.attrib.colors.ptr[0] == 1.0f); /* red on v0 */
  TEST_CHECK(sc.attrib.colors.ptr[4] == 1.0f); /* green on v1 */
  tobj_scene_free_f(&sc);
}

static void test_color_fallback_white(void) {
  tobj_scene_f sc;
  const char *obj = "v 0 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 3\n";
  load_string_f(obj, &sc, true);
  TEST_CHECK(sc.attrib.colors.count == 9);
  for (int i = 0; i < 9; i++) TEST_CHECK(sc.attrib.colors.ptr[i] == 1.0f);
  tobj_scene_free_f(&sc);
}

static void test_lines_and_points(void) {
  tobj_scene_f sc;
  const char *obj =
      "v 0 0 0\nv 1 0 0\nv 2 0 0\nv 3 0 0\nl 1 2 3\np 1 4\n";
  load_string_f(obj, &sc, true);
  TEST_CHECK(sc.shapes[0].lines.num_lines == 1);
  TEST_CHECK(sc.shapes[0].lines.num_indices == 3);
  TEST_CHECK(sc.shapes[0].lines.num_line_vertices[0] == 3);
  TEST_CHECK(sc.shapes[0].points.num_indices == 2);
  tobj_scene_free_f(&sc);
}

static void test_degenerate_face_skipped(void) {
  tobj_scene_f sc;
  const char *obj = "v 0 0 0\nv 1 0 0\nf 1 2\nf 1 2 1\n"; /* <3 verts skipped */
  load_string_f(obj, &sc, true);
  /* the 2-vertex face is skipped; the 3-"vertex" one is kept */
  TEST_CHECK(sc.num_shapes == 1);
  tobj_scene_free_f(&sc);
}

static void test_empty_and_garbage(void) {
  tobj_scene_f sc;
  tobj_load_config cfg = tobj_default_config();
  TEST_CHECK(tobj_load_obj_from_memory_f(&sc, (const uint8_t *)"", 0, &cfg,
                                         NULL) == TOBJ_OK);
  tobj_scene_free_f(&sc);
  const char *garbage = "\x00\x01\x02 random !!! f f f\n v v v\n 99999999999";
  TEST_CHECK(tobj_load_obj_from_memory_f(&sc, (const uint8_t *)garbage, 40,
                                         &cfg, NULL) == TOBJ_OK);
  tobj_scene_free_f(&sc);
}

static void test_mtl_standalone(void) {
  tobj_material_list_f ml;
  const char *mtl =
      "newmtl m\nKd 0.1 0.2 0.3\nNs 42\nmap_Kd -s 2 2 1 tex.png\nfoo bar baz\n";
  tobj_result r =
      tobj_parse_mtl_from_memory_f(&ml, (const uint8_t *)mtl, strlen(mtl), NULL,
                                   NULL);
  TEST_CHECK(r == TOBJ_OK);
  TEST_CHECK(ml.count == 1);
  TEST_CHECK(ml.items[0].diffuse[0] == 0.1f);
  TEST_CHECK(ml.items[0].shininess == 42.0f);
  TEST_CHECK(strcmp(ml.items[0].diffuse_texname, "tex.png") == 0);
  TEST_CHECK(ml.items[0].diffuse_texopt.scale[0] == 2.0f);
  const char *foo = tobj_material_get_param_f(&ml.items[0], "foo");
  TEST_CHECK(foo && strcmp(foo, "bar baz") == 0);
  tobj_material_list_free_f(&ml);
}

static void test_io_callbacks(void) {
  const char *obj = "v 0 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 3\n";
  mem_io mio;
  mio.data = (const uint8_t *)obj;
  mio.len = strlen(obj);
  mio.pos = 0;
  mio.chunk = 5;
  mio.closed = 0;
  tobj_io_callbacks io;
  io.read = mem_io_read;
  io.close = mem_io_close;
  io.user_data = &mio;
  tobj_load_config cfg = tobj_default_config();
  tobj_scene_f sc;
  tobj_result r = tobj_load_obj_from_io_f(&sc, &io, &cfg, NULL);
  TEST_CHECK(r == TOBJ_OK);
  TEST_CHECK(mio.closed == 1);
  TEST_CHECK(sc.num_shapes == 1);
  TEST_CHECK(sc.shapes[0].mesh.num_indices == 3);
  tobj_scene_free_f(&sc);
}

static void test_allocator_limit_failure(void) {
  const char *obj = "v 0 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 3\n";
  tobj_load_config cfg = tobj_default_config();
  cfg.allocator = tobj_default_allocator();
  cfg.allocator.max_alloc_size = 16;
  tobj_scene_f sc;
  tobj_result r =
      tobj_load_obj_from_memory_f(&sc, (const uint8_t *)obj, strlen(obj), &cfg,
                                  NULL);
  TEST_CHECK(r == TOBJ_ERR_ALLOC);
  TEST_CHECK(sc.num_shapes == 0);
}

static void test_input_limit_failure(void) {
  const char *obj = "v 0 0 0\n";
  tobj_load_config cfg = tobj_default_config();
  cfg.max_input_bytes = 4;
  tobj_scene_f sc;
  tobj_result r =
      tobj_load_obj_from_memory_f(&sc, (const uint8_t *)obj, strlen(obj), &cfg,
                                  NULL);
  TEST_CHECK(r == TOBJ_ERR_LIMIT_EXCEEDED);
}

static void test_io_input_limit_exact_and_over(void) {
  const char *obj = "v 0 0 0\n";
  tobj_load_config cfg = tobj_default_config();
  cfg.max_input_bytes = strlen(obj);

  mem_io exact;
  exact.data = (const uint8_t *)obj;
  exact.len = strlen(obj);
  exact.pos = 0;
  exact.chunk = 3;
  exact.closed = 0;
  tobj_io_callbacks io;
  io.read = mem_io_read;
  io.close = mem_io_close;
  io.user_data = &exact;
  tobj_scene_f sc;
  tobj_result r = tobj_load_obj_from_io_f(&sc, &io, &cfg, NULL);
  TEST_CHECK(r == TOBJ_OK);
  TEST_CHECK(exact.closed == 1);
  tobj_scene_free_f(&sc);

  const char *too_big = "v 0 0 0\n# extra\n";
  mem_io over;
  over.data = (const uint8_t *)too_big;
  over.len = strlen(too_big);
  over.pos = 0;
  over.chunk = 0;
  over.closed = 0;
  io.user_data = &over;
  r = tobj_load_obj_from_io_f(&sc, &io, &cfg, NULL);
  TEST_CHECK(r == TOBJ_ERR_LIMIT_EXCEEDED);
  TEST_CHECK(over.closed == 1);
  TEST_CHECK(sc.num_shapes == 0);
}

static void test_io_callback_errors(void) {
  tobj_io_callbacks io;
  io.close = mem_io_close;

  mem_io state;
  state.data = NULL;
  state.len = 0;
  state.pos = 0;
  state.chunk = 0;
  state.closed = 0;
  io.user_data = &state;
  io.read = io_overreport_read;
  tobj_scene_f sc;
  tobj_result r = tobj_load_obj_from_io_f(&sc, &io, NULL, NULL);
  TEST_CHECK(r == TOBJ_ERR_IO);
  TEST_CHECK(state.closed == 1);

  state.closed = 0;
  io.read = io_error_read;
  r = tobj_load_obj_from_io_f(&sc, &io, NULL, NULL);
  TEST_CHECK(r == TOBJ_ERR_IO);
  TEST_CHECK(state.closed == 1);
}

static void test_invalid_allocator_rejected(void) {
  const char *obj = "v 0 0 0\n";
  tobj_load_config cfg = tobj_default_config();
  cfg.allocator = tobj_default_allocator();
  cfg.allocator.free = NULL;
  tobj_scene_f sc;
  tobj_result r =
      tobj_load_obj_from_memory_f(&sc, (const uint8_t *)obj, strlen(obj), &cfg,
                                  NULL);
  TEST_CHECK(r == TOBJ_ERR_INVALID_ARG);
  TEST_CHECK(sc.num_shapes == 0);
}

static void test_allocator_without_calloc_or_realloc(void) {
  const char *obj =
      "v 0 0 0\nv 1 0 0\nv 2 0 0\nv 3 0 0\nv 4 0 0\n"
      "v 5 0 0\nv 6 0 0\nv 7 0 0\nv 8 0 0\n"
      "f 1 2 3\nf 4 5 6\nf 7 8 9\n";
  tobj_load_config cfg = tobj_default_config();
  cfg.allocator = tobj_default_allocator();
  cfg.allocator.calloc = NULL;
  cfg.allocator.realloc = NULL;
  tobj_scene_f sc;
  tobj_result r =
      tobj_load_obj_from_memory_f(&sc, (const uint8_t *)obj, strlen(obj), &cfg,
                                  NULL);
  TEST_CHECK(r == TOBJ_OK);
  TEST_CHECK(sc.attrib.vertices.count == 27);
  TEST_CHECK(sc.shapes[0].mesh.num_indices == 9);
  tobj_scene_free_f(&sc);
}

TEST_LIST = {
    {"corpus_loads", test_corpus_loads},
    {"both_precisions", test_both_precisions},
    {"quad_triangulation", test_quad_triangulation},
    {"no_triangulation", test_no_triangulation},
    {"negative_relative_index", test_negative_relative_index},
    {"bom_and_crlf", test_bom_and_crlf},
    {"vertex_colors", test_vertex_colors},
    {"color_fallback_white", test_color_fallback_white},
    {"lines_and_points", test_lines_and_points},
    {"degenerate_face_skipped", test_degenerate_face_skipped},
    {"empty_and_garbage", test_empty_and_garbage},
    {"mtl_standalone", test_mtl_standalone},
    {"io_callbacks", test_io_callbacks},
    {"allocator_limit_failure", test_allocator_limit_failure},
    {"input_limit_failure", test_input_limit_failure},
    {"io_input_limit_exact_and_over", test_io_input_limit_exact_and_over},
    {"io_callback_errors", test_io_callback_errors},
    {"invalid_allocator_rejected", test_invalid_allocator_rejected},
    {"allocator_without_calloc_or_realloc",
     test_allocator_without_calloc_or_realloc},
    {NULL, NULL}};

/*
 * tiny_obj_c.h -- Pure C11 Wavefront .obj / .mtl loader.
 *
 * A from-scratch C11 reimplementation of tinyobjloader. NOT header-only:
 * compile tiny_obj_c.c (and tobj_tess.c) and link against this header.
 *
 * Design goals: secure, portable, freestanding-capable, dependency-free,
 * fast, robust. Multithreading / SIMD / mmap / file I/O are opt-in behind
 * macros; the default build is scalar, single-threaded and libc-backed.
 *
 * Two precision families coexist in one build:
 *   - "_f" suffix : float positions/normals/texcoords/materials
 *   - "_d" suffix : double  ditto
 * Pick whichever you need at the call site, or define TOBJ_DEFAULT_DOUBLE to
 * make the unsuffixed convenience aliases map to the double family.
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef TINY_OBJ_C_H_
#define TINY_OBJ_C_H_

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* ------------------------------------------------------------------------- */
/* Configuration macros (see plan / README):                                 */
/*                                                                           */
/*   TOBJ_NO_LIBC / TOBJ_FREESTANDING : forbid libc; caller must supply an   */
/*                                      allocator; no default file I/O.      */
/*   TOBJ_ENABLE_FILE_IO              : tobj_load_obj_from_file_* helpers.   */
/*   TOBJ_ENABLE_MMAP                 : use mmap / MapViewOfFile in file I/O. */
/*   TOBJ_ENABLE_MULTITHREADING       : parallel chunked parse.             */
/*   TOBJ_ENABLE_SIMD                 : SIMD newline scan.                   */
/*   TOBJ_DISABLE_FAST_FLOAT          : scalar fallback float parser.        */
/*   TOBJ_DEFAULT_DOUBLE              : unsuffixed aliases -> double family.  */
/* ------------------------------------------------------------------------- */

#if defined(TOBJ_FREESTANDING) && !defined(TOBJ_NO_LIBC)
#define TOBJ_NO_LIBC 1
#endif

#if defined(TOBJ_NO_LIBC) && (defined(TOBJ_ENABLE_FILE_IO) || defined(TOBJ_ENABLE_MMAP))
#error "TOBJ_NO_LIBC is incompatible with TOBJ_ENABLE_FILE_IO / TOBJ_ENABLE_MMAP"
#endif

#ifndef TOBJ_API
#define TOBJ_API extern
#endif

#ifdef __cplusplus
extern "C" {
#endif

/* ======================================================================= */
/* Precision-independent types                                             */
/* ======================================================================= */

/* Result / status codes. TOBJ_OK is returned even when non-fatal warnings
 * were produced (parity with the C++ loader returning `true` plus a warn
 * string). Any non-zero code is a hard failure; the output object is zeroed. */
typedef enum tobj_result {
  TOBJ_OK = 0,
  TOBJ_ERR_INVALID_ARG,
  TOBJ_ERR_ALLOC,
  TOBJ_ERR_OVERFLOW,
  TOBJ_ERR_PARSE,
  TOBJ_ERR_IO,
  TOBJ_ERR_NOT_FOUND,
  TOBJ_ERR_LIMIT_EXCEEDED,
  TOBJ_ERR_UNSUPPORTED
} tobj_result;

typedef enum tobj_severity {
  TOBJ_SEV_WARNING = 0,
  TOBJ_SEV_ERROR = 1
} tobj_severity;

/* Injectable allocator. If a config's allocator.alloc is NULL the default
 * libc allocator is used (only available when !TOBJ_NO_LIBC). `align` is a
 * power of two. calloc/realloc are optional; alloc and free are required for
 * custom allocators. max_alloc_size == 0 means "unbounded". */
typedef struct tobj_allocator {
  void *(*alloc)(void *ud, size_t size, size_t align);
  void *(*calloc)(void *ud, size_t count, size_t size, size_t align);
  void *(*realloc)(void *ud, void *ptr, size_t old_size, size_t new_size,
                   size_t align);
  void (*free)(void *ud, void *ptr, size_t size);
  size_t max_alloc_size;
  void *user_data;
} tobj_allocator;

#ifndef TOBJ_NO_LIBC
TOBJ_API tobj_allocator tobj_default_allocator(void);
#endif

/* Diagnostics sink. If on_message is non-NULL it is invoked per message and
 * nothing is aggregated. Otherwise messages are appended to the `warn`/`err`
 * buffers (allocated via the load config's allocator); free with
 * tobj_diag_free. A NULL tobj_diag* passed to a loader silences diagnostics. */
typedef struct tobj_diag {
  void (*on_message)(void *ud, tobj_severity sev, size_t line_no,
                     const char *msg, size_t msg_len);
  void *user_data;
  char *warn;
  size_t warn_len;
  char *err;
  size_t err_len;
} tobj_diag;

TOBJ_API void tobj_diag_free(tobj_diag *diag, const tobj_allocator *alloc);

/* Per-corner index triple. -1 means "not present". Precision-independent. */
typedef struct tobj_index {
  int vertex_index;
  int normal_index;
  int texcoord_index;
} tobj_index;

/* Key/value pair for material unknown_parameter maps (interned strings). */
typedef struct tobj_kv {
  const char *key;
  const char *value;
} tobj_kv;

typedef enum tobj_texture_type {
  TOBJ_TEXTURE_TYPE_NONE = 0,
  TOBJ_TEXTURE_TYPE_SPHERE,
  TOBJ_TEXTURE_TYPE_CUBE_TOP,
  TOBJ_TEXTURE_TYPE_CUBE_BOTTOM,
  TOBJ_TEXTURE_TYPE_CUBE_FRONT,
  TOBJ_TEXTURE_TYPE_CUBE_BACK,
  TOBJ_TEXTURE_TYPE_CUBE_LEFT,
  TOBJ_TEXTURE_TYPE_CUBE_RIGHT
} tobj_texture_type;

/* Free-form curve/surface type (cstype). */
typedef enum tobj_cstype {
  TOBJ_CSTYPE_NONE = 0,
  TOBJ_CSTYPE_BMATRIX,
  TOBJ_CSTYPE_BEZIER,
  TOBJ_CSTYPE_BSPLINE,
  TOBJ_CSTYPE_CARDINAL,
  TOBJ_CSTYPE_TAYLOR
} tobj_cstype;

/* Raw bytes for one .mtl source, produced by a material resolver. If
 * `release` is set the loader calls it once it is done with the bytes. */
typedef struct tobj_mtl_source {
  const uint8_t *data;
  size_t len;
  void (*release)(void *ud, const uint8_t *data, size_t len);
  void *release_ud;
} tobj_mtl_source;

/* Resolve a `mtllib` name to bytes. Return TOBJ_OK and fill *out, or
 * TOBJ_ERR_NOT_FOUND (treated as a warning by the loader). Called once per
 * distinct name encountered. Replaces the C++ virtual MaterialReader. */
typedef tobj_result (*tobj_material_resolver)(void *ud, const char *mtllib_name,
                                              tobj_mtl_source *out);

/* Pull-style byte input. read returns TOBJ_OK and writes 0 bytes at EOF. The
 * loader owns neither callbacks nor user_data, but calls close when non-NULL. */
typedef struct tobj_io_callbacks {
  tobj_result (*read)(void *ud, uint8_t *dst, size_t dst_size,
                      size_t *bytes_read);
  void (*close)(void *ud);
  void *user_data;
} tobj_io_callbacks;

/* Load configuration (precision-independent: it has no real fields). */
typedef struct tobj_load_config {
  tobj_allocator allocator;     /* {0} -> default libc allocator */

  bool triangulate;             /* default true */
  bool store_vertex_colors;     /* default true */
  bool vertex_color_fallback;   /* fill missing colors with white; default true */
  bool parse_freeform;          /* parse cstype/curv/surf/...; default false */
  bool use_arena;               /* bulk-arena output; default false */

  int num_threads;              /* -1 auto, 0/1 single-threaded (MT builds) */

  /* Hard caps; 0 selects a built-in default. Exceeding -> LIMIT_EXCEEDED. */
  size_t max_vertices;
  size_t max_indices;
  size_t max_faces;
  size_t max_face_arity;
  size_t max_materials;
  size_t max_shapes;
  size_t max_line_bytes;
  size_t max_input_bytes;

  tobj_material_resolver mtl_resolver;
  void *mtl_resolver_user_data;
} tobj_load_config;

TOBJ_API tobj_load_config tobj_default_config(void);

/* ======================================================================= */
/* Per-precision types and API (generated for _f and _d)                   */
/* ======================================================================= */

#define TOBJ_CAT_(a, b) a##b
#define TOBJ_CAT(a, b) TOBJ_CAT_(a, b)
/* Paste the active precision suffix (TOBJ_SUF) onto an identifier. */
#define TOBJ_T(name) TOBJ_CAT(name, TOBJ_SUF)

/* float family */
#define TOBJ_REAL float
#define TOBJ_SUF _f
#include "tiny_obj_c_pub.inc"
#undef TOBJ_REAL
#undef TOBJ_SUF

/* double family */
#define TOBJ_REAL double
#define TOBJ_SUF _d
#include "tiny_obj_c_pub.inc"
#undef TOBJ_REAL
#undef TOBJ_SUF

/* Convenience aliases for the default precision.
 *
 * IMPORTANT: type aliases are typedefs and function aliases are *function-like*
 * macros. Object-like macros sharing these base names would be expanded inside
 * TOBJ_T()/TOBJ_CAT() token-pasting (which fully expands its arguments) and
 * corrupt the suffixed identifiers in the implementation. Typedef names and
 * unparenthesized function-like macro names are not expanded there, so both
 * forms are safe. */
#ifdef TOBJ_DEFAULT_DOUBLE
typedef double tobj_real;
typedef tobj_real_buf_d tobj_real_buf;
typedef tobj_texture_option_d tobj_texture_option;
typedef tobj_material_d tobj_material;
typedef tobj_attrib_d tobj_attrib;
typedef tobj_mesh_d tobj_mesh;
typedef tobj_lines_d tobj_lines;
typedef tobj_points_d tobj_points;
typedef tobj_shape_d tobj_shape;
typedef tobj_scene_d tobj_scene;
typedef tobj_callbacks_d tobj_callbacks;
typedef tobj_material_list_d tobj_material_list;

#define tobj_load_obj_from_memory(...) tobj_load_obj_from_memory_d(__VA_ARGS__)
#define tobj_load_obj_from_file(...) tobj_load_obj_from_file_d(__VA_ARGS__)
#define tobj_load_obj_with_callbacks(...) \
  tobj_load_obj_with_callbacks_d(__VA_ARGS__)
#define tobj_load_obj_from_io(...) tobj_load_obj_from_io_d(__VA_ARGS__)
#define tobj_scene_free(...) tobj_scene_free_d(__VA_ARGS__)
#define tobj_parse_mtl_from_memory(...) tobj_parse_mtl_from_memory_d(__VA_ARGS__)
#define tobj_material_list_free(...) tobj_material_list_free_d(__VA_ARGS__)
#define tobj_material_get_param(...) tobj_material_get_param_d(__VA_ARGS__)
#else
typedef float tobj_real;
typedef tobj_real_buf_f tobj_real_buf;
typedef tobj_texture_option_f tobj_texture_option;
typedef tobj_material_f tobj_material;
typedef tobj_attrib_f tobj_attrib;
typedef tobj_mesh_f tobj_mesh;
typedef tobj_lines_f tobj_lines;
typedef tobj_points_f tobj_points;
typedef tobj_shape_f tobj_shape;
typedef tobj_scene_f tobj_scene;
typedef tobj_callbacks_f tobj_callbacks;
typedef tobj_material_list_f tobj_material_list;

#define tobj_load_obj_from_memory(...) tobj_load_obj_from_memory_f(__VA_ARGS__)
#define tobj_load_obj_from_file(...) tobj_load_obj_from_file_f(__VA_ARGS__)
#define tobj_load_obj_with_callbacks(...) \
  tobj_load_obj_with_callbacks_f(__VA_ARGS__)
#define tobj_load_obj_from_io(...) tobj_load_obj_from_io_f(__VA_ARGS__)
#define tobj_scene_free(...) tobj_scene_free_f(__VA_ARGS__)
#define tobj_parse_mtl_from_memory(...) tobj_parse_mtl_from_memory_f(__VA_ARGS__)
#define tobj_material_list_free(...) tobj_material_list_free_f(__VA_ARGS__)
#define tobj_material_get_param(...) tobj_material_get_param_f(__VA_ARGS__)
#endif

/* Single fuzz entry (uses the float family internally). */
TOBJ_API int tobj_fuzz_one(const uint8_t *data, size_t size);

/* Human-readable name for a result code (static storage). */
TOBJ_API const char *tobj_result_string(tobj_result r);

#ifdef __cplusplus
}
#endif

#endif /* TINY_OBJ_C_H_ */

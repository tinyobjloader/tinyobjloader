/*
 * tobj_tess.h -- robust & fast polygon tessellation for tiny_obj_c.
 *
 * Triangulates a single polygon ring (the corner loop of an .obj face),
 * including pathological / degenerate input: concave, collinear, coincident,
 * zero-area, non-planar, and self-intersecting polygons. It never crashes or
 * loops forever and, for any n >= 3, always emits exactly n-2 triangles.
 *
 * Output indices are ring-local (0..n-1); the caller maps them back to its
 * own per-corner attribute records.
 *
 * Pure C11, no libc dependency (no malloc, no math.h). Reentrant: all state
 * lives on the stack or in caller-provided scratch, so it is safe to call
 * from worker threads concurrently.
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef TOBJ_TESS_H_
#define TOBJ_TESS_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum tobj_tess_status {
  TOBJ_TESS_OK = 0,                 /* clean triangulation */
  TOBJ_TESS_DEGENERATE_BESTEFFORT,  /* n-2 tris emitted, but input was bad */
  TOBJ_TESS_INVALID,                /* n<3 / bad args / non-finite: 0 tris */
  TOBJ_TESS_OOM                     /* needed allocation but none available */
} tobj_tess_status;

enum {
  TOBJ_TESS_FLAG_NONE = 0,
  TOBJ_TESS_FLAG_ASSUME_CONVEX = 1u << 0, /* skip convexity test, fan */
  TOBJ_TESS_FLAG_FORCE_FAN = 1u << 1,     /* always fan from corner 0 */
  TOBJ_TESS_FLAG_NORMAL_GIVEN = 1u << 2   /* use desc->normal, skip Newell */
};

/* Optional allocator (used only when scratch / out_indices are not supplied). */
typedef struct tobj_tess_allocator {
  void *(*alloc)(void *ud, size_t size);
  void (*free)(void *ud, void *ptr);
  void *ud;
} tobj_tess_allocator;

/* Worst-case scratch size (in bytes) needed to tessellate n vertices with no
 * dynamic allocation. Pure function. */
size_t tobj_tess_scratch_size(uint32_t n);

typedef struct tobj_tess_result {
  uint32_t *indices;      /* == desc->out_indices, or an allocated block */
  uint32_t num_triangles; /* n-2 on success */
  int indices_allocated;  /* 1 => free indices with the allocator */
  tobj_tess_status status;
} tobj_tess_result;

#define TOBJ_TESS_CAT_(a, b) a##b
#define TOBJ_TESS_CAT(a, b) TOBJ_TESS_CAT_(a, b)
#define TOBJ_TESS_T(name) TOBJ_TESS_CAT(name, TOBJ_TESS_SUF)

#define TOBJ_TESS_REAL float
#define TOBJ_TESS_SUF _f
#include "tobj_tess_pub.inc"
#undef TOBJ_TESS_REAL
#undef TOBJ_TESS_SUF

#define TOBJ_TESS_REAL double
#define TOBJ_TESS_SUF _d
#include "tobj_tess_pub.inc"
#undef TOBJ_TESS_REAL
#undef TOBJ_TESS_SUF

#ifdef __cplusplus
}
#endif

#endif /* TOBJ_TESS_H_ */

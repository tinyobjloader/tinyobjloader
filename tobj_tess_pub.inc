/*
 * tobj_tess_pub.inc -- per-precision tessellation descriptor + entry point.
 * Included twice from tobj_tess.h. Do not include directly.
 */

typedef struct TOBJ_TESS_T(tobj_tess_desc) {
  const TOBJ_TESS_REAL *points; /* n*3 xyz, stride 3 */
  uint32_t n;
  const TOBJ_TESS_REAL *normal; /* [3]; used iff FLAG_NORMAL_GIVEN */
  uint32_t flags;

  uint32_t *out_indices; /* caller buffer; cap >= 3*(n-2), or NULL to alloc */
  uint32_t out_cap;      /* capacity of out_indices in uint32 units */

  void *scratch;       /* >= tobj_tess_scratch_size(n), or NULL to alloc */
  size_t scratch_size; /* size of scratch in bytes */

  const tobj_tess_allocator *alloc; /* used only when buffers are missing */
} TOBJ_TESS_T(tobj_tess_desc);

/* Triangulate one polygon ring. Never crashes/loops for n >= 3. */
tobj_tess_status TOBJ_TESS_T(tobj_tess_polygon)(
    const TOBJ_TESS_T(tobj_tess_desc) * desc, tobj_tess_result *result);

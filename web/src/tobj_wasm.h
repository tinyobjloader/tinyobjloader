/*
 * tobj_wasm.h -- C ABI shim exposing the pure C11 tinyobjloader to WebAssembly.
 *
 * Hand-written direct binding: no embind, no C++, no protobuf-style structs.
 * The shim flattens a parsed scene into interleaved triangle corners on the
 * wasm heap, so JavaScript reads plain Float32Array views. Handles are opaque
 * small integers (>= 1).
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef TOBJ_WASM_H_
#define TOBJ_WASM_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Floats per corner: x y z  nx ny nz  u v */
#define TOBJ_W_STRIDE 8

/* Error return: negative tobj_result code (see tobj_result_string). */
#define TOBJ_W_MATERIAL_NONE 0xFFFFFFFFu

/* Parse .obj bytes (and optional .mtl bytes) from memory.
 *
 * `mtl`/`mtl_len` are only consulted for `mtllib` references found in the .obj.
 * `mtl_name` is the .mtl file name as the browser knows it; it is matched
 * against the basename of each `mtllib` token, ASCII case-insensitively.
 * Pass mtl_name = NULL or "" to accept the supplied .mtl for any mtllib.
 * `flags` is reserved and must be 0.
 *
 * Returns an opaque handle > 0, or -tobj_result on failure. On failure
 * tobjw_last_message() carries the parser's diagnostics.
 * The caller owns the returned handle: call tobjw_destroy() exactly once.
 */
int tobjw_load_memory(const uint8_t *obj, size_t obj_len, const uint8_t *mtl,
                      size_t mtl_len, const char *mtl_name, uint32_t flags);

/* Releases a handle and every buffer it owns. Safe for 0/unknown handles. */
void tobjw_destroy(int handle);

/* Diagnostics captured during the most recent load on this thread.
 * Static storage, valid until the next load. Never NULL. */
const char *tobjw_last_message(void);

/* Shim/loader version tag, e.g. "tinyobj-c11". */
const char *tobjw_version(void);

int tobjw_num_shapes(int handle);
int tobjw_num_materials(int handle);

/* Shape descriptor. `out` must have room for TOBJ_W_DESC_SLOTS entries of
 * uintptr_t (4 bytes each on wasm32). Slot meaning:
 *
 *   0  vertices       heap pointer to interleaved floats (TOBJ_W_STRIDE each)
 *   1  vert_count     number of floats in slot 0
 *   2  triangle_count number of triangles (vert_count / (3 * stride))
 *   3  groups         heap pointer to uint32_t triples {material, start, count}
 *   4  group_count    number of triples in slot 3; start/count are triangles
 *   5  name           heap pointer to a NUL-terminated UTF-8 shape name
 *   6  stride         TOBJ_W_STRIDE
 *   7  reserved       0
 *
 * Material id TOBJ_W_MATERIAL_NONE means "no usemtl / out of range".
 * Returns 1 on success, 0 on bad handle/shape.
 */
#define TOBJ_W_DESC_SLOTS 8
int tobjw_shape_desc(int handle, int shape, uintptr_t *out);

/* Flat material record, 12 floats:
 *   0-2 ambient/rgb of Kd, 3-5 emissive Ke, 6 dissolve, 7 shininess,
 *   8 ior, 9 illum, 10 roughness, 11 metallic
 * Returns 1 on success, 0 on bad handle/material. */
#define TOBJ_W_MAT_SLOTS 12
int tobjw_material(int handle, int material, float *out);

/* Material name; "" when unnamed. NULL on bad handle/material. */
const char *tobjw_material_name(int handle, int material);

/* Texture-file slots exposed by tobjw_material_texname(). Values match the
 * classic and PBR map names in tiny_obj_c.h. */
#define TOBJ_W_TEX_DIFFUSE 0            /* map_Kd */
#define TOBJ_W_TEX_AMBIENT 1            /* map_Ka */
#define TOBJ_W_TEX_SPECULAR 2           /* map_Ks */
#define TOBJ_W_TEX_SPECULAR_HIGHLIGHT 3 /* map_Ns */
#define TOBJ_W_TEX_EMISSIVE 4           /* map_Ke */
#define TOBJ_W_TEX_NORMAL 5             /* norm */
#define TOBJ_W_TEX_BUMP 6               /* map_bump / bump */
#define TOBJ_W_TEX_ALPHA 7              /* map_d */
#define TOBJ_W_TEX_ROUGHNESS 8          /* map_Pr */
#define TOBJ_W_TEX_METALLIC 9           /* map_Pm */
#define TOBJ_W_TEX_DISPLACEMENT 10      /* disp */
#define TOBJ_W_TEX_REFLECTION 11        /* refl */
#define TOBJ_W_TEX_COUNT 12

/* Interned texture filename for one slot; "" when unset, NULL on bad
 * handle/material/slot. Valid until the handle is destroyed. */
const char *tobjw_material_texname(int handle, int material, int slot);

/* Original file vertex id (0-based) of one emitted corner. */
int tobjw_corner_vertex(int handle, int shape, uint32_t corner, uint32_t *out);

/* Skin weights from `vw` records. tobjw_skin_weight writes up to max_joints
 * (joint id, weight) pairs and returns the total count for that vertex, or -1
 * on a bad handle/index. */
int tobjw_num_skin_weights(int handle);
int tobjw_skin_weight(int handle, int index, uint32_t *vertex_id,
                      int32_t *joint_ids, float *weights, int max_joints);

/* Verbatim `skel_*` lines and per-mesh subdivision `t` lines. */
int tobjw_num_skel_lines(int handle);
const char *tobjw_skel_line(int handle, int index);
int tobjw_num_tag_lines(int handle, int shape);
const char *tobjw_tag_line(int handle, int shape, int index);

#ifdef __cplusplus
}
#endif

#endif /* TOBJ_WASM_H_ */

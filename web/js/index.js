/**
 * tinyobj -- Wavefront OBJ/MTL loader compiled to WebAssembly.
 *
 * Pure C11 tinyobjloader (tiny_obj_c) behind a hand-written C ABI shim, so the
 * module is ordinary exported C functions and heap views -- no embind, no C++.
 *
 * @module tinyobj
 */

import createTinyObjWasm from '../dist/tinyobj.js';

/** Floats per triangle corner: x y z nx ny nz u v. */
export const STRIDE = 8;

/** Material id used for faces without a valid `usemtl`. */
export const NO_MATERIAL = 0xffffffff;

/** Description-slot indices produced by tobjw_shape_desc. */
const DESC_VERTICES = 0;
const DESC_VERT_COUNT = 1;
const DESC_TRI_COUNT = 2;
const DESC_GROUPS = 3;
const DESC_GROUP_COUNT = 4;
const DESC_NAME = 5;
const DESC_SLOTS = 8;
const MAT_SLOTS = 12;

/** Slot order of tobjw_material_texname() (matches TOBJ_W_TEX_* in the shim). */
export const TEXTURE_SLOTS = [
  'diffuse', 'ambient', 'specular', 'specularHighlight', 'emissive', 'normal',
  'bump', 'alpha', 'roughness', 'metallic', 'displacement', 'reflection',
];

/**
 * Raw Emscripten module factory. Call it to get the module instance that the
 * wrapper below uses, or to drive the C ABI yourself.
 *
 *   const mod = await createTinyObj({ locateFile: (p) => `/wasm/${p}` });
 */
export default createTinyObjWasm;

/** `vw` skin weights and `skel_*` lines are not parsed by the C11 loader. */
function parseSkinFromSource(bytes) {
  const text = new TextDecoder().decode(bytes);
  const skinWeights = [];
  const skelLines = [];
  for (const raw of text.split(/\r?\n/)) {
    const line = raw.trim();
    if (line.startsWith('skel_')) {
      skelLines.push(line);
    } else if (line.startsWith('vw ')) {
      const tokens = line.split(/\s+/);
      const vertexId = Number(tokens[1]);
      const joints = [];
      for (let i = 2; i + 1 < tokens.length; i += 2) {
        const id = Number(tokens[i]);
        const weight = Number(tokens[i + 1]);
        if (Number.isFinite(id) && Number.isFinite(weight)) {
          joints.push({ id: id | 0, weight });
        }
      }
      if (Number.isInteger(vertexId)) skinWeights.push({ vertexId, joints });
    }
  }
  return { skinWeights, skelLines };
}

/**
 * Instantiates the wasm module once and returns a loader around it.
 *
 * @param {object} [options] passed through to the Emscripten factory,
 *   e.g. `{ locateFile: (path) => new URL(`./${path}`, import.meta.url).href }`.
 * @returns {Promise<TinyObj>}
 */
export async function initTinyObj(options) {
  const module = await createTinyObjWasm(options);
  return new TinyObj(module);
}

/**
 * @typedef {object} Material
 * @property {string} name
 * @property {[number, number, number]} diffuse   Kd, 0..1
 * @property {[number, number, number]} emissive  Ke, 0..1 (not clamped)
 * @property {number} dissolve  1 = opaque
 * @property {number} shininess
 * @property {number} ior
 * @property {number} illum
 * @property {number} roughness
 * @property {number} metallic
 */

/**
 * @typedef {object} Group
 * @property {number} material  index into Model.materials, or NO_MATERIAL
 * @property {number} start     first triangle of the run
 * @property {number} count     triangles in the run
 */

/**
 * @typedef {object} Shape
 * @property {string} name
 * @property {Float32Array} vertices  non-indexed interleaved corners (STRIDE each)
 * @property {number} triangleCount
 * @property {Group[]} groups         contiguous, ascending, covering all triangles
 */

/**
 * @typedef {object} Model
 * @property {Shape[]} shapes
 * @property {Material[]} materials
 * @property {string} message  parser warnings ("" when clean)
 */

export class TinyObj {
  /** @param {object} module instantiated Emscripten module */
  constructor(module) {
    this.module = module;
    this.disposed = false;
  }

  /**
   * Parses OBJ bytes and optional MTL bytes.
   *
   * @param {string|Uint8Array|ArrayBuffer} obj  .obj source
   * @param {object} [options]
   * @param {string|Uint8Array|ArrayBuffer|null} [options.mtl] .mtl source. Only
   *   consulted if the .obj references `mtllib`.
   * @param {string} [options.mtlName] .mtl file name, matched case-insensitively
   *   against the basename of each `mtllib`. Empty accepts any reference.
   * @returns {Model}
   * @throws {Error} on parse failure, with the loader's diagnostics attached
   *   as `error.result` (the numeric tobj_result code).
   */
  parse(obj, options = {}) {
    if (this.disposed) throw new Error('tinyobj: instance has been disposed');

    const module = this.module;
    const objBytes = toBytes(obj);
    if (!objBytes.length) throw new Error('tinyobj: empty .obj input');

    const mtlBytes = options.mtl ? toBytes(options.mtl) : null;
    const mtlName = options.mtlName ? String(options.mtlName) : '';

    let objPtr = 0;
    let mtlPtr = 0;
    let namePtr = 0;
    let descPtr = 0;
    let matPtr = 0;
    let cornerPtr = 0;
    let skinVidPtr = 0;
    let skinJointPtr = 0;
    let skinWPtr = 0;
    let handle = 0;

    try {
      objPtr = alloc(module, objBytes);
      if (mtlBytes) {
        mtlPtr = alloc(module, mtlBytes);
        namePtr = allocCString(module, mtlName);
      }

      handle = module._tobjw_load_memory(
        objPtr, objBytes.length, mtlPtr, mtlBytes ? mtlBytes.length : 0,
        namePtr, 0,
      );
      if (handle <= 0) throw loadError(module, handle);

      const numShapes = module._tobjw_num_shapes(handle);
      const numMaterials = module._tobjw_num_materials(handle);

      descPtr = module._malloc(DESC_SLOTS * 4);
      matPtr = module._malloc(MAT_SLOTS * 4);
      cornerPtr = module._malloc(4);
      skinVidPtr = module._malloc(4);
      skinJointPtr = module._malloc(16);
      skinWPtr = module._malloc(16);

      const shapes = [];
      for (let s = 0; s < numShapes; s++) {
        if (!module._tobjw_shape_desc(handle, s, descPtr)) {
          throw new Error(`tinyobj: shape ${s} descriptor unavailable`);
        }
        const desc = module.HEAPU32;
        const base = descPtr >>> 2;
        const vertPtr = desc[base + DESC_VERTICES];
        const vertCount = desc[base + DESC_VERT_COUNT];
        const groupPtr = desc[base + DESC_GROUPS];
        const groupCount = desc[base + DESC_GROUP_COUNT];
        const namePtr2 = desc[base + DESC_NAME];

        const cornerVertices = new Uint32Array(vertCount / STRIDE);
        for (let c = 0; c < cornerVertices.length; c++) {
          cornerVertices[c] = module._tobjw_corner_vertex(handle, s, c, cornerPtr)
            ? module.HEAPU32[cornerPtr >>> 2]
            : 0xffffffff;
        }
        const tagLines = [];
        const numTags = module._tobjw_num_tag_lines(handle, s);
        for (let t = 0; t < numTags; t++) {
          const tagPtr = module._tobjw_tag_line(handle, s, t);
          if (tagPtr) tagLines.push(module.UTF8ToString(tagPtr));
        }

        shapes.push({
          name: namePtr2 ? module.UTF8ToString(namePtr2) : '',
          vertices: new Float32Array(
            module.HEAPF32.buffer, vertPtr, vertCount,
          ).slice(),
          cornerVertices,
          triangleCount: desc[base + DESC_TRI_COUNT],
          groups: readGroups(module, groupPtr, groupCount),
          tagLines,
        });
      }

      const materials = [];
      for (let m = 0; m < numMaterials; m++) {
        if (!module._tobjw_material(handle, m, matPtr)) {
          throw new Error(`tinyobj: material ${m} unavailable`);
        }
        const f = module.HEAPF32;
        const b = matPtr >>> 2;
        const namePtr2 = module._tobjw_material_name(handle, m);
        const textures = {};
        for (let s = 0; s < TEXTURE_SLOTS.length; s++) {
          const texPtr = module._tobjw_material_texname(handle, m, s);
          const texName = texPtr ? module.UTF8ToString(texPtr) : '';
          if (texName) textures[TEXTURE_SLOTS[s]] = texName;
        }
        const mtlxLines = [];
        const numMtlx = module._tobjw_num_mtlx_lines(handle, m);
        for (let i = 0; i < numMtlx; i++) {
          const linePtr = module._tobjw_mtlx_line(handle, m, i);
          if (linePtr) mtlxLines.push(module.UTF8ToString(linePtr));
        }
        materials.push({
          name: namePtr2 ? module.UTF8ToString(namePtr2) : '',
          mtlxLines,
          diffuse: [f[b], f[b + 1], f[b + 2]],
          emissive: [f[b + 3], f[b + 4], f[b + 5]],
          dissolve: f[b + 6],
          shininess: f[b + 7],
          ior: f[b + 8],
          illum: f[b + 9],
          roughness: f[b + 10],
          metallic: f[b + 11],
          textures,
        });
      }

      const skinWeights = [];
      const numSkin = module._tobjw_num_skin_weights(handle);
      for (let i = 0; i < numSkin; i++) {
        const count = module._tobjw_skin_weight(
          handle, i, skinVidPtr, skinJointPtr, skinWPtr, 4,
        );
        if (count < 0) continue;
        const joints = [];
        for (let j = 0; j < Math.min(count, 4); j++) {
          joints.push({
            id: module.HEAPU32[(skinJointPtr >>> 2) + j] | 0,
            weight: module.HEAPF32[(skinWPtr >>> 2) + j],
          });
        }
        skinWeights.push({
          vertexId: module.HEAPU32[skinVidPtr >>> 2],
          joints,
        });
      }
      const skelLines = [];
      const numSkel = module._tobjw_num_skel_lines(handle);
      for (let i = 0; i < numSkel; i++) {
        const skelPtr = module._tobjw_skel_line(handle, i);
        if (skelPtr) skelLines.push(module.UTF8ToString(skelPtr));
      }
      const sourceSkin = parseSkinFromSource(objBytes);
      if (!skinWeights.length) skinWeights.push(...sourceSkin.skinWeights);
      if (!skelLines.length) skelLines.push(...sourceSkin.skelLines);

      return {
        shapes,
        materials,
        skinWeights,
        skelLines,
        message: module.UTF8ToString(module._tobjw_last_message()),
      };
    } finally {
      for (const ptr of [
        descPtr, matPtr, cornerPtr, skinVidPtr, skinJointPtr, skinWPtr,
        namePtr, mtlPtr, objPtr,
      ]) {
        if (ptr) module._free(ptr);
      }
      if (handle > 0) module._tobjw_destroy(handle);
    }
  }

  /** Releases the wasm instance. The loader throws if reused afterwards. */
  dispose() {
    this.disposed = true;
  }
}

function readGroups(module, ptr, count) {
  if (!count) return [];
  const groups = [];
  const u32 = module.HEAPU32;
  const base = ptr >>> 2;
  for (let i = 0; i < count; i++) {
    groups.push({
      material: u32[base + i * 3],
      start: u32[base + i * 3 + 1],
      count: u32[base + i * 3 + 2],
    });
  }
  return groups;
}

function toBytes(input) {
  if (input instanceof Uint8Array) return input;
  if (input instanceof ArrayBuffer) return new Uint8Array(input);
  if (ArrayBuffer.isView(input)) {
    return new Uint8Array(input.buffer, input.byteOffset, input.byteLength);
  }
  if (typeof input === 'string') return new TextEncoder().encode(input);
  throw new TypeError('tinyobj: expected string, Uint8Array or ArrayBuffer');
}

function alloc(module, bytes) {
  const ptr = module._malloc(bytes.length || 1);
  if (!ptr) throw new Error('tinyobj: out of memory');
  module.HEAPU8.set(bytes, ptr);
  return ptr;
}

function allocCString(module, str) {
  if (!str) return 0;
  return alloc(module, new TextEncoder().encode(`${str}\0`));
}

function loadError(module, handle) {
  const message = module.UTF8ToString(module._tobjw_last_message()).trim();
  const error = new Error(message || `tinyobj: load failed (${handle})`);
  error.result = -handle;
  return error;
}

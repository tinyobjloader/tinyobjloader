/** Floats per triangle corner: x y z nx ny nz u v. */
export declare const STRIDE: 8;

/** Material id for faces without a valid `usemtl`. */
export declare const NO_MATERIAL: number;

/** Emscripten module instance produced by the factory. */
export interface TinyObjModule {
  _malloc(size: number): number;
  _free(ptr: number): void;
  HEAPU8: Uint8Array;
  HEAPU32: Uint32Array;
  HEAPF32: Float32Array;
  UTF8ToString(ptr: number): string;
  _tobjw_load_memory(
    obj: number,
    objLen: number,
    mtl: number,
    mtlLen: number,
    mtlName: number,
    flags: number,
  ): number;
  _tobjw_destroy(handle: number): void;
  _tobjw_last_message(): number;
  _tobjw_version(): number;
  _tobjw_num_shapes(handle: number): number;
  _tobjw_num_materials(handle: number): number;
  _tobjw_shape_desc(handle: number, shape: number, out: number): number;
  _tobjw_material(handle: number, material: number, out: number): number;
  _tobjw_material_name(handle: number, material: number): number;
}

/** Options forwarded to the Emscripten factory. */
export interface TinyObjInitOptions {
  /** Resolve `tinyobj.wasm` when it is not next to the JS glue. */
  locateFile?: (path: string, prefix: string) => string;
  /** Copy of the wasm binary, e.g. when bundling with `?url` imports. */
  wasmBinary?: ArrayBuffer | Uint8Array;
  print?: (text: string) => void;
  printErr?: (text: string) => void;
}

export type Source = string | Uint8Array | ArrayBuffer | ArrayBufferView;

export interface ParseOptions {
  /** `.mtl` source. Only consulted when the `.obj` references `mtllib`. */
  mtl?: Source | null;
  /**
   * `.mtl` file name, compared case-insensitively against the basename of each
   * `mtllib` reference. Empty (default) accepts any reference.
   */
  mtlName?: string;
}

export interface Group {
  /** Index into `Model.materials`, or `NO_MATERIAL`. */
  material: number;
  /** First triangle of the run. */
  start: number;
  /** Triangles in the run; always > 0. */
  count: number;
}

export interface Shape {
  name: string;
  /** Non-indexed interleaved corners, `STRIDE` floats each. */
  vertices: Float32Array;
  triangleCount: number;
  /** Contiguous, ascending, covering every triangle exactly once. */
  groups: Group[];
}

export interface Material {
  name: string;
  diffuse: [number, number, number];
  emissive: [number, number, number];
  dissolve: number;
  shininess: number;
  ior: number;
  illum: number;
  roughness: number;
  metallic: number;
}

export interface Model {
  shapes: Shape[];
  materials: Material[];
  /** Parser warnings, "" when the load was clean. */
  message: string;
}

export class TinyObj {
  constructor(module: TinyObjModule);
  readonly module: TinyObjModule;
  readonly disposed: boolean;
  parse(source: Source, options?: ParseOptions): Model;
  dispose(): void;
}

export declare function initTinyObj(
  options?: TinyObjInitOptions,
): Promise<TinyObj>;

declare const createTinyObj: (
  options?: TinyObjInitOptions,
) => Promise<TinyObjModule>;

export default createTinyObj;

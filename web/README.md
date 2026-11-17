# tinyobj

Wavefront `.obj` / `.mtl` loader for the web: the **pure C11** tinyobjloader
compiled to WebAssembly.

- No C++, no embind — a hand-written C ABI shim exported with
  `-sEXPORTED_FUNCTIONS`. JavaScript talks to plain exported C functions and
  reads results through `Float32Array` / `Uint32Array` heap views.
- Loads from memory, so it works with `File`, `fetch`, `Blob`, drag-and-drop or
  a Node buffer without a virtual filesystem.
- Returns render-ready geometry: non-indexed interleaved triangle corners
  (`x y z nx ny nz u v`) split into contiguous per-material runs, which map
  straight onto Three.js `InterleavedBuffer` + `geometry.addGroup()`.

The same C sources (`tiny_obj_c.c`, `tobj_tess.c`) build natively; see the root
README for the C/C++ APIs. Only the float (`_f`) family is exposed here.

## Install

Not published yet — build from this repository:

```sh
git clone <repo> && cd <repo>/web
./build.sh                 # needs emcc (Emscripten) in PATH
npm pack --dry-run         # inspect the tarball
```

Maintainers: see [PUBLISHING.md](PUBLISHING.md) for the npm release procedure
(auth, dist-tags, verification), including why an RC must not be published
under the default `latest` tag.

## Use

```js
import { initTinyObj } from 'tinyobj';

const tinyobj = await initTinyObj();          // loads tinyobj.wasm next to the JS

const objBytes = await (await fetch('/model.obj')).arrayBuffer();
const mtlBytes = await (await fetch('/model.mtl')).arrayBuffer();

const model = tinyobj.parse(objBytes, { mtl: mtlBytes, mtlName: 'model.mtl' });

for (const shape of model.shapes) {
  console.log(shape.name, shape.triangleCount, shape.groups);
}
```

`parse()` returns

```js
{
  shapes: [{
    name: 'cube',
    vertices: Float32Array,   // triangleCount * 3 corners * 8 floats
    triangleCount: 12,
    groups: [{ material: 0, start: 0, count: 3 }, ...],
  }],
  materials: [{
    name: 'white',
    diffuse: [1, 1, 1],       // Kd
    emissive: [0, 0, 0],      // Ke
    dissolve: 1, shininess: 0, ior: 1, illum: 2, roughness: 1, metallic: 0,
  }],
  message: '',                // loader warnings, "" when clean
}
```

Corners are `x y z nx ny nz u v`. Missing normals are replaced by the geometric
face normal; missing UVs are `0 0`; V is flipped (`1 - v`) for image-space UVs.
Every triangle belongs to exactly one group, and `group.material` is
`NO_MATERIAL` (`0xffffffff`) when the face had no valid `usemtl`.

`parse()` throws an `Error` on hard failures; the message is the loader's
diagnostics and `error.result` is the numeric `tobj_result` code. Non-fatal
warnings are returned in `model.message`.

By default the wasm binary is fetched from the URL of the JS glue, so the two
`dist/` files must be served together. In a bundler or when hosting assets
elsewhere, override it:

```js
const tinyobj = await initTinyObj({ locateFile: (p) => `/static/${p}` });
```

Three.js geometry construction:

```js
const buffer = new THREE.InterleavedBuffer(shape.vertices, 8);
geometry.setAttribute('position', new THREE.InterleavedBufferAttribute(buffer, 3, 0));
geometry.setAttribute('normal',   new THREE.InterleavedBufferAttribute(buffer, 3, 3));
geometry.setAttribute('uv',       new THREE.InterleavedBufferAttribute(buffer, 2, 6));
for (const run of shape.groups) {
  geometry.addGroup(run.start * 3, run.count * 3, run.material);
}
```

## Demo

```sh
cd web
./build.sh
python3 -m http.server 8000
# open http://localhost:8000/demo/
```

The demo pulls Three.js from a CDN via an import map. Drop an `.obj` (and its
`.mtl`) onto the page, or use “Choose .obj”. Rotate with the mouse.

## Raw ABI

`import createTinyObj from 'tinyobj/raw'` gives the Emscripten factory for
driving the C shim yourself. The ABI lives in `src/tobj_wasm.h`:

| export | purpose |
| --- | --- |
| `tobjw_load_memory` | parse `.obj` (+ optional `.mtl`) bytes → handle (>0) or negative `tobj_result` |
| `tobjw_destroy` | free a handle |
| `tobjw_num_shapes` / `tobjw_num_materials` | counts |
| `tobjw_shape_desc` | 8 `uintptr_t` slots: vertices ptr/count, triangle count, groups ptr/count, name ptr, stride |
| `tobjw_material` | 12 floats: `Kd`, `Ke`, dissolve, shininess, ior, illum, roughness, metallic |
| `tobjw_material_name` | interned name pointer |
| `tobjw_last_message` | diagnostics of the last load |
| `tobjw_version` | binding tag |

## Building details

`build.sh` compiles `tiny_obj_c.c`, `tobj_tess.c` and `src/tobj_wasm.c` with
`emcc -std=c11` and these settings:

| flag | why |
| --- | --- |
| `MODULARIZE` + `EXPORT_ES6` | ES module factory, no globals |
| `ENVIRONMENT=web,worker,node` | browser, web worker and Node |
| `ALLOW_MEMORY_GROWTH` | the scene arena grows with model size |
| `FILESYSTEM=0` | inputs come from memory, no emscripten FS |
| `--no-entry` | library build |

`TOBJ_ENABLE_FILE_IO`, `TOBJ_ENABLE_MMAP`, `TOBJ_ENABLE_MULTITHREADING` and
`TOBJ_ENABLE_SIMD` are deliberately **not** defined: the wasm build is the
default scalar, single-threaded, libc-backed configuration. `.mtl` sidecars are
resolved through `tobj_load_config.mtl_resolver` instead of file I/O.

Tests:

```sh
npm run test:native   # native cc build of the shim + model assertions
npm test              # node, against the built wasm
```

## License

MIT, same as tinyobjloader. See `LICENSE`.

Copyright (c) 2012-Present, Syoyo Fujita and many contributors.

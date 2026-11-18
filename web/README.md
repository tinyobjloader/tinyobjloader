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
    textures: { diffuse: 'wood.png' },  // filenames from map_Kd, map_Ka, ...
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

The Three.js viewer in `demo/` can be developed with Vite (hot reload) or served
statically without any bundler.

Live development (recommended):

```sh
cd web
./build.sh            # once, to produce dist/tinyobj.{js,wasm}
npm install           # installs the Vite + Three.js dev dependencies
npm run dev           # http://localhost:5173/ (hot reload)
```

`npm run dev` resolves `three` from `node_modules` and rewrites the Emscripten
wasm path automatically. `npm run dev:build` emits a bundled, static copy to
`.vite-demo-dist/` and `npm run preview` serves that build.

Static (no Vite, no install):

```sh
cd web
./build.sh
python3 -m http.server 8000
# open http://localhost:8000/demo/
```

This path relies on the import map in `demo/index.html`, which pulls Three.js
from a CDN. The demo supports:

- **Multiple files and folders** — drop several files, a whole folder, or use
  “Choose folder”. `.obj`, `.mtl` and images (`.png/.jpg/.webp/.gif/.bmp`) are
  recognised; multiple `.mtl` files are combined.
- **Texturing** — texture filenames from `map_Kd`, `map_Ka`, `map_Ks`, `map_Ke`,
  `norm`, `map_bump`, `map_d`, `map_Pr`, `map_Pm`, … are matched (by basename,
  case-insensitively) against uploaded images.
- **Shading** — smooth/flat/wireframe selector, a texture on/off toggle, and a
  material panel showing Kd, Ke, Ns, d, Ni, illum, Pr/Pm and texture maps.
- **Shape selection** — click a shape in the 3D view or in the Shapes list to
  highlight it (wireframe + bounding box) and see its name, triangle count,
  bounds and the materials it uses. Ctrl/Cmd/Shift-click adds to the selection;
  the detail panel then shows combined bounds, triangle counts and materials. Hover shows a tooltip; the Shapes tab has a
  filter plus hide/isolate controls, and the View tab has camera presets,
  exposure/env/tone-map sliders, material overrides and live render stats.
- **Subdivision** — a level selector (0–2) applies Loop refinement on vertices
  welded by their original file ids, honouring crease and corner `t` tags;
  sharp edges stay sharp and skin weights are interpolated across new vertices.
  The shape detail shows the scheme and crease count. Large meshes are capped.
- **Skinning** — `vw` weights (parsed in JS; the C11 loader does not decode them)
  and `skel_*` joints drive a `SkinnedMesh`. Pick a bone in the Heatmap selector
  to colour vertices by that bone's weight (blue → red). Play/pause or scrub the
  timeline to preview a procedural bone animation. A `.anim.json` sidecar with
  keyframed bone rotations can replace the procedural pose; a Bones checkbox
  draws the joint hierarchy, and the timeline supports loop / ping-pong / once.
- **MaterialX / OpenPBR** — `mtlx_*` lines are exposed by the loader and resolved
  into a small subset of `MeshPhysicalMaterial` inputs (base colour, metallic,
  roughness, clearcoat, sheen, transmission, ior, image connections), with the
  classic MTL/PBR keys as fallback. The material panel shows the surface
  category.
- **Export & share** — the View tab exports the displayed scene as glTF/OBJ,
  saves a PNG screenshot, and copies a URL carrying the current viewer settings
  (the model itself is not embedded).
- **Background parsing** — OBJ/MTL parsing runs in a Web Worker with a fallback
  to the main thread, so large models keep the UI responsive. The View tab
  reports parse time, wasm heap, draw calls, loaded/missing textures and an
  estimated GPU texture budget.
- **Environment map** — a bundled 1k Radiance HDR from Poly Haven
  (`ferndale_studio_06`, CC0; see `demo/assets/README.md`) is loaded with
  `RGBELoader` into a `PMREMGenerator` for image-based lighting. Toggle it with
  the Envmap checkbox; nothing is fetched at runtime.
- **Large scenes** — the wasm build starts with 512 MB of memory (2 GB maximum)
  and the loader caps are raised, so `models/dragon.obj` (~71 MB, 871k triangles)
  loads in the browser.

Rotate with the mouse; “Reset view” re-frames the model.

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
| `INITIAL_MEMORY=512MB`, `MAXIMUM_MEMORY=2GB` | large scenes (e.g. `dragon.obj`) start without repeated growth |
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

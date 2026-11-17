# Blender add-on: OBJ with subdivision tags and MaterialX-in-MTL

`io_scene_obj_ext` imports and exports `.obj`/`.mtl` with two tinyobjloader
extensions:

- [subd-obj.md](../subd-obj.md): OpenSubdiv subdivision tags (`t` lines).
- [mtlx-mtl.md](../mtlx-mtl.md): MaterialX node graphs (`mtlx_*` lines).

It is pure Python (tested with Blender 5.3). `subd.py` and `mtlx.py` are ports
of `tobj_subd.c` and `tobj_mtlx.c`, and the tests check them against the C
code.

## Install

Zip the `io_scene_obj_ext` folder and install it under *Edit > Preferences >
Add-ons > Install from Disk*. You can also copy the folder into Blender's
`scripts/addons`. The add-on adds *File > Import / Export > OBJ with subd +
MaterialX (.obj)*. From scripts, use `bpy.ops.import_scene.obj_ext` and
`bpy.ops.export_scene.obj_ext`.

## Mapping

**Subdivision tags ↔ the Subdivision Surface modifier and crease attributes**

| Tag | Blender |
| --- | --- |
| `scheme catmark` / `bilinear` | `subdivision_type` `CATMULL_CLARK` / `SIMPLE` |
| `scheme loop` | Catmull-Clark, plus the property `obj_subd_scheme = "loop"` (Blender has no Loop) |
| `interpolateboundary 1` / `2` | `boundary_smooth` `PRESERVE_CORNERS` / `ALL` |
| `interpolateboundary 0` | `ALL`, plus the property `obj_subd_boundary = 0` |
| `facevaryinginterpolateboundary 0..5` | `uv_smooth` `SMOOTH_ALL`, `PRESERVE_CORNERS`, `…_AND_JUNCTIONS`, `…_JUNCTIONS_AND_CONCAVE`, `PRESERVE_BOUNDARIES`, `NONE` |
| `crease` | the `crease_edge` attribute |
| `corner` | the `crease_vert` attribute |
| `hole` | the face attribute `obj_subd_hole` (Blender does not render holes) |
| `creasemethod`, `smoothtriangles` | the properties `obj_subd_creasemethod` and `obj_subd_smoothtriangles` |
| unknown tags | the property `obj_subd_unknown`, written back verbatim |

Blender's OpenSubdiv bridge uses **sharpness = 10 · crease²**. I measured this:
at subdivision level L, a crease value of √(L/10) or more gives exactly the
same surface as an infinite crease, and anything less does not. Import
therefore sets crease = √(min(s, 10) / 10), and export writes s = 10 · crease².

Export writes the tags in canonical form after checking them with `subd.py`.
For meshes made in Blender, it writes `scheme`, `interpolateboundary` and
`facevaryinginterpolateboundary` explicitly, because OpenSubdiv's defaults
differ from Blender's.

**MaterialX ↔ node trees**

The surface shader (`open_pbr_surface`, `standard_surface`, `gltf_pbr` or
`UsdPreviewSurface`) becomes a Principled BSDF, and its category is kept for
export. These nodes are converted:

| MaterialX | Blender |
| --- | --- |
| `image`, `tiledimage` | Image Texture (`float` adds Separate Color, red) |
| `normalmap` | Normal Map |
| `constant` | RGB / Value |
| `multiply`, `add`, `subtract` | Math / Mix |
| `mix` | Mix |
| `texcoord` | UV Map |

On import, every mapped input starts at the MaterialX default, so export
writes only values that differ from it. Anything else is reported and falls
back to the classic keys. Export always writes the classic keys too (`Kd`,
`Pr`, `Pm`, `d`, `Ke`, `map_Kd`).

Texture paths are written relative to the `.mtl` when the texture is under the
export folder, and absolute otherwise.

## Tests

```
blender -b --factory-startup --python-exit-code 1 \
    --python blender/tests/run.py -- /path/to/workdir
```

The tests need `cc` to build the C checkers. They cover:
- import of the `formal/Subd` fixtures;
- export, checking the result with the C `tobj_subd`/`tobj_mtlx`;
- re-import, comparing the subdivided surfaces Blender evaluates;
- creases authored in Blender;
- rejected tags;
- the Python port against C on random files;
- MaterialX node trees through export and re-import;
- the registered operators;
- an OpenSubdiv cross-check (below).

### OpenSubdiv cross-check

Set `OSD_ROOT` to an OpenSubdiv install prefix. The CPU backend is enough:
`include/` and `lib/libosdCPU`. For example, build OpenSubdiv 3.8 with every
`NO_*` option on (OpenGL, CUDA, OpenCL, Metal, DX, TBB, OpenMP, Ptex, examples,
tutorials, regression, docs).

```
OSD_ROOT=/path/to/osd/install blender -b --factory-startup --python-exit-code 1 \
    --python blender/tests/run.py -- /path/to/workdir
```

`tests/osd_refine.cc` is the reference. It loads the OBJ with tinyobjloader,
checks the tags with `tobj_subd`, and builds an OpenSubdiv `Far` refiner with
the same scheme, boundary rule, creases, corners and holes. For limit points it
refines until every finite sharpness has decayed, then applies `Far` limit
masks, which are exact there.

The test compares Blender's evaluated Subdivision Surface with these points at
levels 1–3, with "Use Limit Surface" off and on (quality 10). The fixtures are
`tests/osd_cross.obj` and the creased torus:
- open grids with both boundary rules;
- semi-sharp and infinite creases;
- corners;
- bilinear;
- a cube with semi-sharp creases and a corner.

Results:
- Refined points match to 1e-5 or better.
- Limit points match to 1e-6, except near an infinitely sharp crease that ends
  at a boundary. There, Blender's adaptive patch evaluation is approximate:
  3.4e-3 at level 1 and 1.1e-3 at levels 2–3, even at quality 10.
- At Blender's default quality (3), limit points near semi-sharp creases are
  off by up to about 1e-2.

Tag values follow OpenSubdiv's OBJ reader (`regression/common/far_utils.h`),
which is not the `Sdc` enum order: `interpolateboundary 1` is edge-and-corner
and `2` is edge-only.

When a file has tags but no `interpolateboundary`, OpenSubdiv uses "none".
Blender has no equivalent, so the importer warns and uses edge-only for meshes
that have a boundary.

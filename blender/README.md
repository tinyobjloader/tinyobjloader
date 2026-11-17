# Blender add-on: OBJ with subdivision tags, MaterialX-in-MTL and skeletons

`io_scene_obj_ext` imports and exports `.obj`/`.mtl` with three tinyobjloader
extensions:

- [subd-obj.md](../subd-obj.md): OpenSubdiv subdivision tags (`t` lines).
- [mtlx-mtl.md](../mtlx-mtl.md): MaterialX node graphs (`mtlx_*` lines).
- [skel-obj.md](../skel-obj.md): skeletons for the `vw` skin weights
  (`skel_*` lines), with an optional `.fbx` sidecar for the animation.

It is pure Python (tested with Blender 5.3). `subd.py`, `mtlx.py` and
`skel.py` are ports of `tobj_subd.c`, `tobj_mtlx.c` and `tobj_skel.c`, and the
tests check them against the C code.

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

**Skeletons ↔ armatures**

| skel-obj.md | Blender |
| --- | --- |
| `skel_joint` with a bind matrix | a bone whose rest transform is the bind (scale dropped) |
| `skel_rest` | the pose (rest transforms that differ from the bind) |
| `vw` | vertex groups named after the joints, plus an Armature modifier |
| `skel_lib x.fbx` / `x.usd*` (joints without bind) | the armature of the sidecar (Blender's FBX or USD importer), joints matched by name |
| `skel_anim x.fbx [take]` / `x.usd*` | the action of the sidecar, baked onto the armature frame by frame |

Export writes the armature of the first Armature modifier: the joints
parents-first, each with its rest transform in OBJ world space as the bind
matrix plus `skel_rest`, and `vw` from the vertex groups named after bones.
Bone names that are not identifiers are made into identifiers (with a
warning). If the armature has an action and *Animation sidecar* is on (the
default), the armature and its action are also written to a sidecar, and
the OBJ gets `skel_anim`. *Sidecar format* chooses `<name>_skel.fbx` (Blender's
FBX exporter) or `<name>_skel.usda`. The add-on writes the USD sidecar itself,
in OBJ space: a `Skeleton` and a `SkelAnimation` sampled per frame, with no
transform above them. Blender's USD exporter puts the axis conversion and the
armature transform on parent Xforms, which skel-obj.md does not apply.

Frames: frame f is FBX time f / fps, on import and export. This is also how
LightUSD maps the sidecar to USD time codes. Blender's FBX importer adds one
frame by default, so the add-on imports with `anim_offset=0`.

When the joints have inline binds, the importer builds its own armature, and
the sidecar's animation is baked onto it: each frame, every joint follows the
same-named sidecar bone in world space, keeping its own rest orientation. This
works whatever bone axes the sidecar's importer chose. USD sidecars are
imported without unit conversion, because they share the OBJ's units.

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
- skeletons: the Python `skel.py` against C on the fixtures and 300 random
  files; a rig exported (inline skeleton plus animation sidecar), checked by
  the C `tobj_skel` and re-imported with the same deformation at 5 frames;
  names only plus `skel_lib`; `skel_rest` against a reference linear blend
  skinning; an ill-formed skeleton;
- the same round trip and names-only tests with a USD sidecar;
- LightUSD cross-check: with `LIGHTUSD_SKIN_COMPARE` set to LightUSD's
  `skin_compare` (tests/obj-skel), the exported OBJ (FBX and USD sidecars) is
  loaded by LightUSD and its UsdSkel skinning is compared with Blender's at 5
  frames (about 5e-7 with FBX; about 2e-6 with USD, whose text keeps 6
  significant digits);
- an OpenSubdiv cross-check (below).

### OpenSubdiv cross-check

Set `OSD_ROOT` to an OpenSubdiv install prefix. The CPU backend is enough:
`include/` and `lib/libosdCPU`. For example, build OpenSubdiv 3.8 with every
`NO_*` option on (OpenGL, CUDA, OpenCL, Metal, DX, TBB, OpenMP, Ptex, examples,
tutorials, regression, docs).

With the scripts in `tests/`, from the repository root:

```
sh blender/tests/build_osd.sh [OSD_SRC] [PREFIX]   # CPU-only build; clones v3_8_0 if OSD_SRC is absent
sh blender/tests/run_cross_check.sh /path/to/blender [PREFIX/install] [WORKDIR]
```

`PREFIX` defaults to `build-osd`. Or by hand:

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

When a file has tags but no `interpolateboundary`, OpenSubdiv's OBJ reader
uses edge-only (`2`), and so does the importer. An explicit
`interpolateboundary 0` ("none") has no Blender equivalent: the importer warns
and keeps the value in the property `obj_subd_boundary`.

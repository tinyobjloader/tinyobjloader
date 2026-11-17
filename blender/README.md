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
- the registered operators.

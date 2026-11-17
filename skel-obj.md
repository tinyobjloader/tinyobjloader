# Skeletons in .obj

`skel_*` lines give the skin weights of the `vw` extension a skeleton: joint
names, hierarchy and bind pose. The skeleton and its animation can also come
from a sidecar file such as an `.fbx` or a USD file. A loader that knows UsdSkel
can then build `Skeleton`, `SkelAnimation` and the skin binding. Readers that
don't know the extension ignore the lines, as they do any unknown keyword.

The normative specification is the Lean 4 model in
[`formal/Skel`](formal/Skel/README.md). This document is a readable summary of
it.

## Example

```
skel_joint hips -   1 0 0 0  0 1 0 0  0 0 1 0  0 1 0 1
skel_joint spine hips 1 0 0 0  0 1 0 0  0 0 1 0  0 1.5 0 1
skel_joint head spine
skel_rest  head 1 0 0 0  0 1 0 0  0 0 1 0  0 0.5 0 1
skel_lib   rig.fbx
skel_anim  rig.fbx walk
v ...
vw 0 0 1
vw 1 0 0.5 1 0.5
```

## Lines

All `skel_*` lines apply to the whole file, wherever they appear, because the
joint ids of `vw` are file-global. Tokens are separated by blanks, and there
is no quoting.

| Line | Meaning |
| --- | --- |
| `skel_joint <name> <parent> [<16 decimals>]` | A joint. The n-th `skel_joint` line is joint id n-1 in `vw`. `<parent>` is `-` for a root, or the name of a joint declared earlier. The optional matrix is the joint's bind transform in world space. |
| `skel_rest <name> <16 decimals>` | Rest transform of a joint, relative to its parent. |
| `skel_lib <path> [<skeleton>]` | Sidecar file for the skeleton (`.fbx`, or a USD layer with an optional `Skeleton` prim path). Joints are matched by name. Bind and rest transforms missing from the OBJ come from it. |
| `skel_anim <path> [<animation>]` | Sidecar file for the animation (an `.fbx` take, or a `SkelAnimation` prim path in a USD layer). |

Matrices are 4×4 and row-major, as in USD's `matrix4d`: the translation is in
the last row. Decimals use the grammar of [subd-obj.md](subd-obj.md).

## Well-formedness

The skeleton is accepted only if:

1. Every `skel_*` line has the right number of arguments, and every matrix
   entry is a decimal.
2. Joint names are valid identifiers (`[A-Za-z_][A-Za-z0-9_]*`) and are all
   distinct.
3. Every parent is `-` or a joint declared on an earlier line. The hierarchy is
   therefore a forest.
4. Every `skel_rest` names a joint declared on an earlier line, and no joint
   has two.
5. `skel_lib` and `skel_anim` appear at most once each.
6. If some joint has no bind matrix, there is a `skel_lib`.
7. Every joint id used by `vw` names a declared joint.

If the skeleton is not accepted, the skin weights are kept and the skeleton is
dropped. Loaders report this as a warning.

The checks against the sidecar file itself are left to the consumer: that the
joints exist there, and that an animation can be resolved.

## Design note: no geomBindTransform line

UsdSkel's `geomBindTransform` maps a mesh's points into skeleton space at bind
time. OBJ positions are already in world space, and the skeleton lives in the
same space (bind matrices are world matrices), so that transform is always
the identity. The extension therefore has no per-mesh bind line. To skin a
mesh authored in another space, transform its `v` positions to world space when
writing the OBJ.

## Sidecar files

`<path>` is relative to the `.obj`. A sidecar shares the OBJ's units and axes
(OBJ declares neither), so readers apply no unit or up-axis conversion to it.

- **`.fbx`**: `skel_lib` takes the skeleton's bind and rest transforms; joints
  are matched by node name. `skel_anim` takes the named take (animation
  stack), or the first one when no name is given. Frame f is FBX time f / fps.
- **USD** (`.usd`, `.usda`, `.usdc`, `.usdz`): `skel_lib` takes the
  `Skeleton` prim at the given path, or the layer's first `Skeleton`. Joints
  are matched by the last component of their joint path. `skel_anim` takes the
  `SkelAnimation` prim at the given path, or the first one. Its joints are
  matched by joint path, built from the OBJ's hierarchy (`root/spine/head`).

In both cases the animation is applied in the OBJ's skeleton space: a root
joint's transform is relative to the OBJ's world. Transforms of the sidecar's
nodes or prims above the skeleton are not applied, and readers warn when a USD
sidecar has them.

## Canonical form

The canonical writer emits:
- the joints in declaration order, each with its bind matrix if it has one;
- the rest transforms in joint order;
- `skel_lib`, then `skel_anim`.

Blanks between tokens are single. Parsing canonical form gives back the same
model.

## API

- **`tobj_skel.h`** (C11):
  - `tobj_skel_parse_lines` takes the `skel_*` lines and the largest joint id
    used by `vw`.
  - `tobj_skel_to_lines` writes canonical form.
  - `tobj_skel_dump_obj` writes the model for differential testing.
- **Loaders:** the `skel_*` lines are kept verbatim, in file order:
  - C11: `tobj_attrib.skel_lines` / `num_skel_lines`.
  - C++: `attrib_t::skel_lines`.

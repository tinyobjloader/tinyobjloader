# Subdivision-surface tags in .obj

OpenSubdiv's "enhanced OBJ" `t` tag lines, fully specified. A mesh carrying
them describes a subdivision surface: its scheme, boundary rules, creases,
corners and holes. The syntax and meaning follow OpenSubdiv's OBJ reader and
the OSD-Lite Maya exporter, so files written by those tools load unchanged.
One tag, `scheme`, is new.

The normative specification is the Lean 4 model in
[`formal/Subd`](formal/Subd/README.md). This document is a readable summary of
it.

## Example

```
o box
v -1 -1  1
...
f 1 2 3 4
...
t scheme 0/0/1 catmark
t interpolateboundary 1/0/0 2
t facevaryinginterpolateboundary 1/0/0 1
t crease 2/1/0 0 1 2.5
t crease 4/2/0 1 2 2 3 10 1.5
t corner 1/1/0 0 3
t hole 1/0/0 5
```

## Lines

A tag line is `t <name> <ni>/<nf>/<ns>` followed by `ni` integers, `nf`
decimals and `ns` strings. Tokens are separated by blanks. Each tag belongs to
the mesh of the current `o`/`g` group.

**Numbering.** Vertex numbers in tags are 0-based and count over the whole
file: the first `v` line in the file is vertex 0, as OpenSubdiv writes them.
`f` lines stay 1-based. Face numbers in `hole` are 0-based and count the
mesh's own faces, in file order.

| Tag | Counts | Meaning |
| --- | --- | --- |
| `scheme` | `0/0/1` | `catmark` (default), `loop` or `bilinear`. New; OpenSubdiv has no such tag. |
| `interpolateboundary` | `1/0/0` | Vertex boundary: `0` none, `1` edge and corner, `2` edge only. |
| `facevaryinginterpolateboundary` | `1/0/0` | Face-varying (UV) boundary: `0` none, `1` corners only, `2` corners plus 1, `3` corners plus 2, `4` boundaries, `5` all. |
| `facevaryingpropagatecorners` | `1/0/0` | Obsolete. Accepted and ignored. |
| `creasemethod` | `0/0/1` | `normal` or `chaikin`. |
| `smoothtriangles` | `0/0/1` | `catmark` or `smooth`. Catmark scheme only. |
| `crease` | `2k/1/0` or `2k/k/0` | `k` edges, given as vertex pairs, with one shared sharpness or one sharpness each. |
| `corner` | `k/1/0` or `k/k/0` | `k` vertices with one shared sharpness or one sharpness each. |
| `hole` | `k/0/0` | `k` faces that are holes. |

Any other tag name is kept as is and has no meaning. Loaders report it as a
warning.

A tag that is absent means the consumer's default. For OpenSubdiv
(`Sdc::Options`) the defaults are vertex boundary none, face-varying linear
all, uniform creasing and catmark triangles.

### Tokens and numbers

- Counts are unsigned decimal integers, at most 8192 each. The line must have
  exactly `ni + nf + ns` arguments after the counts.
- An integer is `[+-]?[0-9]+`.
- A decimal is `[+-]?([0-9]+(\.[0-9]*)?|\.[0-9]+)([eE][+-]?[0-9]+)?`.
  `inf` and `nan` are not decimals.
- Strings are single tokens.

### Sharpness

A sharpness is a decimal. A negative sharpness counts as `0`, as in OpenSubdiv
(written `0` in canonical form). Values of 10 or more are infinitely sharp
(`Sdc::Crease::SHARPNESS_INFINITE`). An edge or vertex that is listed more
than once takes the last sharpness given.

## Well-formedness

The tags of a mesh are accepted only if:

1. Every tag line has valid counts, the right number of arguments, and
   arguments of the right kinds.
2. Each of `scheme`, `interpolateboundary`, `facevaryinginterpolateboundary`,
   `creasemethod` and `smoothtriangles` appears at most once, with a value from
   the table.
3. Every crease edge joins two distinct vertices and is an edge of one of the
   mesh's faces. Edges are unordered, so `0 1` and `1 0` are the same edge.
4. Every corner vertex is used by a face of the mesh.
5. Every hole is a face number of the mesh.
6. `smoothtriangles` is used only with the catmark scheme, and `loop` is used
   only on meshes whose faces are all triangles.

A mesh whose tags are not accepted keeps its geometry but has no subdivision
data. Loaders report this as a warning, never as a load failure.

Tags refer to the faces as written. Triangulating on load changes the faces,
so check the tags against untriangulated faces (`triangulate = false`).

## Canonical form

The canonical writer emits, in this order:
- `scheme`, `interpolateboundary`, `facevaryinginterpolateboundary`,
  `creasemethod`, `smoothtriangles` (those that are set);
- one `t crease 2/1/0 a b s` per edge, with `a < b`, in order of first mention;
- one `t corner 1/1/0 v s` per vertex, in order of first mention;
- one `t hole k/0/0 ...` line with the holes in order of first mention, without
  repeats;
- the unknown tags, as they were written, with single blanks between tokens.

Parsing canonical form gives back the same model.

## API

- **`tobj_subd.h`** (C11):
  - `tobj_subd_parse_lines` checks a mesh's tag lines against its faces.
  - `tobj_subd_to_lines` writes canonical form.
  - `tobj_subd_dump` writes the model for differential testing.
- **C11 loader**: `tobj_mesh.tag_lines` / `num_tag_lines` hold the mesh's `t`
  lines verbatim. `tobj_mesh.tags` holds them parsed as generic tags.
- **C++ loader**: `mesh_t::tag_lines`, and `mesh_t::tags` as before.
- **Python**: `mesh_t.tags`, `mesh_t.tag_lines`, and `tinyobjloader.subd(mesh)`.

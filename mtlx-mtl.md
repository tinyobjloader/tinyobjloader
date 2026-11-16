# MaterialX-in-MTL extension

A plain-ASCII extension of Wavefront `.mtl` that describes a
[MaterialX](https://materialx.org) shading network per material: a surface
shader, any number of single-output nodes, constant inputs, and connections.
Classic MTL keys (`Kd`, `map_Kd`, `Pr`, ... and the [PBR extension](pbr-mtl.md))
stay as the fallback for readers that do not know the extension. Such readers
ignore unknown keywords.

The normative specification is the Lean 4 model in
[`formal/Mtlx`](formal/Mtlx/README.md). This document is a readable summary of
it.

## Example

```
newmtl painted_metal
Kd 0.8 0.2 0.1                                # fallback for classic readers
mtlx_version 1.39
mtlx_surface shader open_pbr_surface
mtlx_node    tex  image color3
mtlx_node    rgh  image float
mtlx_input   tex.file filename "paint 01.png"
mtlx_input   rgh.file filename rough.png
mtlx_input   shader.base_metalness float 1.0
connectmtl   tex shader.base_color
connectmtl   rgh shader.specular_roughness
```

## Lines

Each keyword applies to the current `newmtl`. Extension lines before the first
`newmtl` are ignored.

| Line | Meaning |
| --- | --- |
| `mtlx_version <major>.<minor>` | MaterialX version of the material. Optional, at most once. |
| `mtlx_surface <name> <category>` | The surface shader node, for example `standard_surface`, `open_pbr_surface`, `gltf_pbr` or `UsdPreviewSurface`. Exactly once. |
| `mtlx_node <name> <category> <type>` | A single-output node of a MaterialX value type. |
| `mtlx_input <node>.<input> <type> <value...>` | A constant input. |
| `connectmtl <src>[.out] <dst>.<input>` | Connects the output of `src` to an input of `dst`. |
| `mtlx_include <path>` | A nodedef library, emitted as `xi:include`. |

### Tokens

Tokens are separated by spaces and tabs. A token that starts with `"` runs to
the next `"`. The quotes are removed and the token may contain blanks. There
are no escapes, and a missing closing quote is an error. A line whose first
non-blank character is `#` is a comment. Trailing `\r` is ignored.

### Values

- `string` and `filename` take exactly one token, used verbatim.
- Every other type joins its tokens with `", "`, which is the MaterialX value
  syntax. The result must parse as the type, using the MaterialX value grammar
  (`MtlxSpec.parseValue`). Examples:
  - `color3 0.8 0.2 0.1`
  - `vector2 2 2`
  - `floatarray 1 2 3`
  - `boolean true`
- Types are the MaterialX value types: `integer`, `boolean`, `float`,
  `color3/4`, `vector2/3/4`, `matrix33/44`, `string`, `filename`, and the
  `*array` forms.

## Well-formedness

A material that uses the extension is accepted only if it meets every rule
below:

1. No line has an arity error or an unterminated quote.
2. There is exactly one `mtlx_surface`, and at most one valid `mtlx_version`.
3. The surface and node names are valid MaterialX names (`[A-Za-z_][A-Za-z0-9_]*`)
   and all distinct. Categories are valid names, and node types are built-in
   value types.
4. Every `mtlx_input` names a declared node, has a valid input name, and has a
   value that parses as its type. No input is set twice.
5. Every connection source is a declared non-surface node, and its output, if
   given, is `out`. The destination is declared. No input is connected twice.
   If the same input also has a constant, the constant's type must equal the
   source's type. The connection replaces the constant.
6. The node graph is acyclic.

A material that breaks a rule keeps its classic keys and gets no MaterialX
network. Loaders report this as a warning, never as a load failure.

Types of inputs that are only connected are not checked against nodedefs.
That check is left to the MaterialX consumer.

## Mapping to a MaterialX document

The mapping is defined by Lean `toDoc`. `tobj_mtlx_to_xml` produces it byte for
byte. For each accepted material with name `M` (made into a valid name with
`sanitize`, and made unique with `_2`, `_3`, ...), the document contains:

- `<nodegraph name="NG_M">`, which holds:
  - the nodes;
  - one `<output name="o_<node>">` per node that feeds the surface.
- `<category name="SR_M" type="surfaceshader">`. Its inputs connect to the node
  graph through `nodegraph` and `output`.
- `<surfacematerial name="M">`.

The root version is the first declared `mtlx_version`, or `1.39` if there is
none.

## API

- **C11** (`tiny_obj_c.h`): each `tobj_material` has
  `mtlx_lines`/`num_mtlx_lines`. The lines are verbatim and in file order.
- **C++** (`tiny_obj_loader.h`): `material_t::mtlx_lines`.
- **`tobj_mtlx.h`**:
  - `tobj_mtlx_parse` parses a whole `.mtl`.
  - `tobj_mtlx_parse_lines` parses one material from a loader's lines.
  - `tobj_mtlx_to_xml` writes the `.mtlx` document.
  - `tobj_mtlx_dump` writes the verdicts plus the XML, for differential testing.

## Verification

- `formal/Mtlx` (Lean 4, reuses the MaterialX model `MtlxSpec`). It proves:
  - `check_sound`: an accepted material is well-formed, and its graph is
    bound and acyclic (through `MtlxSpec.discoverGraphRanking_iff_acyclic`);
  - `check_graph_complete`;
  - `wellFormed_order`: a dependency-first order exists;
  - `tokenize_joinTokens`: tokenizing the canonical join gives back the tokens;
  - `sanitize_valid`.

  There is no `sorry`, and only the standard axioms are used.
- `formal/Mtlx/tools/diff.sh N` compares the Lean reference executable with the C
  implementation on the fixtures plus N random files, under ASan and UBSan.
- `tests/mtlx_loader_test.c` and `tests/mtlx_loader_test_cxx.cc` check that the
  per-material lines from the C11 and C++ loaders give the same verdicts as the
  whole-file parse.
- LightUSD validation: see `formal/Mtlx/README.md`.

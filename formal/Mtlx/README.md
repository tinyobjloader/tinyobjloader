# MaterialX-in-MTL: Lean 4 specification

The normative specification of the `.mtl` MaterialX extension
([`mtlx-mtl.md`](../../mtlx-mtl.md)). The C implementation is
`tobj_mtlx.{h,c}` in the repository root.

| Module | Contents |
| --- | --- |
| `TobjMtlx/Syntax.lean` | The line lexer: `tokenize`, comments, `\r`. Proves `tokenize_joinTokens` (canonical printing round-trips). |
| `TobjMtlx/Model.lean` | The material record, `step`/`parseMtl`, the executable `check`, the `WellFormed` predicate, `lower` to the MaterialX graph model, and `sanitize`. Proves `sanitize_valid`. |
| `TobjMtlx/Sound.lean` | `check_sound` (`check m = true → WellFormed m`), `check_graph_complete` and `wellFormed_order`. |
| `TobjMtlx/Doc.lean` | `toDoc`, the normative mapping to a MaterialX document. |
| `TobjMtlx/Tests.lean` | Kernel-checked examples (`decide +kernel`). |
| `TobjMtlx/Audit.lean` | Axiom audit. |
| `Main.lean` | The `mtlxmtl` reference executable, which prints the same dump as `tobj_mtlx_dump`. |

## Reuse of the MaterialX model

The package depends on `MtlxSpec`, the Lean model of the MaterialX
specification in `materialx-conformance/verif/lean`. It reuses:

- `GNode`/`Src`, the graph model;
- `discoverGraphRanking_iff_acyclic`, which gives the acyclicity half of
  `check_sound`;
- `validNameChars`, for names;
- `parseValue`, the value grammar;
- `parseVersion`;
- `Elem`/`printXml`, the XML tree and printer.

Both packages pin Lean `v4.35.0` and Mathlib `56a00585`. The package shares
`../.lake/packages`, so Mathlib is not rebuilt.

## Build and check

```sh
cd formal/Mtlx
tools/setup-mtlxspec.sh /path/to/materialx-conformance/verif/lean
lake build                               # spec, proofs, tests, mtlxmtl
lake env lean TobjMtlx/Audit.lean        # propext / Classical.choice / Quot.sound only
sh tools/diff.sh 3000                    # Lean vs C (ASan+UBSan): fixtures + 3000 random files
```

`tools/diff.sh` compiles `tests/mtlx_dump.c` with `tobj_mtlx.c`. It compares
`mtlxmtl FILE` with the C dump byte for byte, on `tests/*.mtl` and on random
files from `tools/gen.py`.

## Validation with LightUSD

LightUSD's `tests/mtlx-mtl/run_mtlx_mtl.py` runs three checks on reference
`.mtlx` documents (the MaterialX example corpus):

1. It converts each document with `tools/mtlx2mtl.py`, then regenerates the
   `.mtlx` with `tobj_mtlx`. It checks that the Lean output is identical, and
   that `lusdrender --mtlx` gives pixel-identical renders of the original and
   the regenerated document.
2. With `--usd`, it imports an `.obj` with the MaterialX-in-MTL `.mtl` into
   USD, which builds a UsdShade MaterialX network. It renders that against the
   same mesh bound to the original `.mtlx`, and the images must be identical.
   As a control, a render identical to the classic-only fallback is reported
   as non-discriminating.

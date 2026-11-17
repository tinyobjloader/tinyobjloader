# formal/Subd — subdivision-surface tags in .obj

Lean 4 model of [`subd-obj.md`](../../subd-obj.md). It is the normative
specification; `tobj_subd.c` mirrors it definition by definition.
No dependencies beyond the Lean core (toolchain in `lean-toolchain`).

| Module | Contents |
| --- | --- |
| `TobjSubd/Model.lean` | Tokens, number grammars, topology, `step`/`stepTag`, `parseLines`, `finish`, canonical `print`, the `.obj` subset used by the differential (`parseObj`, `dumpObj`). |
| `TobjSubd/Sound.lean` | `Valid` (per-tag rules) and `MeshRules` (whole-mesh rules); `parseLines_valid`, `check_sound`. |
| `TobjSubd/Audit.lean` | `#print axioms` for the main theorems. |
| `Main.lean` | Exe `subdobj`: dump (for the C differential) and `--roundtrip`. |

## Results

- `parseLines_valid`: for any lines, the model satisfies the per-tag rules.
  Creases are edges `a < b` of the mesh and listed once; corners are mesh
  vertices listed once; holes are face numbers listed once; sharpness is never
  negative; scalar options are in range.
- `check_sound`: an accepted model also satisfies the whole-mesh rules
  (`smoothtriangles` only with catmark, `loop` only on triangles).
- Only the standard axioms are used (`propext`, `Classical.choice`,
  `Quot.sound`), and there is no `sorry`.
- The canonical round trip (`parseLines (print s) = s` for accepted `s`) is
  **checked, not proved**. `subdobj --roundtrip` checks it on the fixtures and
  on random files.

## Running

```
lake build
lake env lean TobjSubd/Audit.lean
sh tools/diff.sh 3000                    # Lean vs C, ASan/UBSan
.lake/build/bin/subdobj --roundtrip tests/*.obj
```

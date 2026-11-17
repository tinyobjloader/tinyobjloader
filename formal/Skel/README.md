# formal/Skel — skeletons in .obj

Lean 4 model of [`skel-obj.md`](../../skel-obj.md). It is the normative
specification, and `tobj_skel.c` mirrors it definition by definition. It
depends only on [`formal/Subd`](../Subd/README.md), which supplies the tokens,
the decimal grammar and the lexical lemmas.

| Module | Contents |
| --- | --- |
| `TobjSkel/Model.lean` | Joints, `step` (`stepJoint`, `stepRest`, `stepSlot`), `parseLines`, `finish`, canonical `printLines`/`print`, the `.obj` subset used by the differential (`dumpObj`). |
| `TobjSkel/Sound.lean` | `Valid` and `FileRules`; the theorems `parseLines_valid` and `check_sound`. |
| `TobjSkel/Roundtrip.lean` | The canonical round trip, `roundtrip`. |
| `TobjSkel/Audit.lean` | `#print axioms` for the main theorems. |
| `Main.lean` | The executable `skelobj`: dump for the C differential, and `--roundtrip`. |

## Results

- **`parseLines_valid`:** for any lines, the model satisfies:
  - joint names are valid identifiers and distinct;
  - every parent index is smaller than its joint's own index, so the hierarchy
    is a forest with parents declared first;
  - bind and rest transforms are 16 decimals each.
- **`check_sound`:** an accepted skeleton also satisfies the whole-file rules:
  - a joint without a bind matrix requires `skel_lib`;
  - every `vw` joint id names a joint.
- **`roundtrip`:** if the lines contain no `\n` or `\r`, then an accepted
  `s = parseLines lines maxId` satisfies
  `parseLines (splitOn '\n' (print s)) maxId = s`.
- Only the standard axioms are used (`propext`, `Classical.choice`,
  `Quot.sound`), and there is no `sorry`.

## Running

```
lake build
lake env lean TobjSkel/Audit.lean
sh tools/diff.sh 3000                     # Lean vs C, ASan/UBSan
.lake/build/bin/skelobj --roundtrip tests/*.obj
```

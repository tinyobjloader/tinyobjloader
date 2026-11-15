import Lake
open Lake DSL

-- Mathlib v4.35.0, matching the existing Lean pin; used by Tess geometry proofs.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

package «obj» where
  leanOptions := #[]

@[default_target]
lean_lib «Obj» where
  srcDir := "."

-- The inherited glTF three-way driver `CDiff.lean` (tools/cdiff*.{py,c}) refers
-- to `tg3_*` functions that no longer exist in `Obj.C.Gen`; it is kept for
-- reference but is not a build target.  The OBJ differential check is
-- `objdiff` below (tools/objdiff.sh).

/-- Differential driver: pure Lean parse model vs the C loader (tests/obj_dump.c). -/
lean_exe «objdiff» where
  root := `ObjDiff

lean_lib «Tess» where
  srcDir := "."

lean_exe «tesscheck» where
  root := `TessCheck

/-- Bounded exact predicate probe for independent C/Lean/Python validation. -/
lean_exe «tesspredicates» where
  root := `TessPredicateProbe

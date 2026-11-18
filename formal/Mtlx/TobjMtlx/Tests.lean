import TobjMtlx.Doc

/-! Kernel-checked examples of the MaterialX-in-MTL specification. -/
namespace TobjMtlx.Tests
open TobjMtlx

def okSrc : String := "newmtl m\nmtlx_surface s standard_surface\nmtlx_node t image color3\n" ++
  "mtlx_input t.file filename \"a b.png\"\nmtlx_input s.base_color color3 @t\n"
def cycSrc : String := "newmtl m\nmtlx_surface s standard_surface\nmtlx_node a add float\n" ++
  "mtlx_node b add float\nmtlx_input b.in1 float @a\nmtlx_input a.in1 float @b\n"

theorem tokenize_quoted :
    tokenize "mtlx_input t.file filename \"a b.png\"".toList =
      some ["mtlx_input".toList, "t.file".toList, "filename".toList, "a b.png".toList] := by
  decide +kernel

theorem tokenize_unterminated : tokenize "x \"ab".toList = none := by decide +kernel

theorem ok_accepted : (parseMtl okSrc.toList).map check = [true] := by decide +kernel
theorem cycle_rejected : (parseMtl cycSrc.toList).map check = [false] := by decide +kernel

theorem ok_wellFormed : ∀ m ∈ parseMtl okSrc.toList, WellFormed m := by
  intro m hm
  have h : parseMtl okSrc.toList = [m] := by
    have : (parseMtl okSrc.toList).length = 1 := by decide +kernel
    match hp : parseMtl okSrc.toList, this with
    | [x], _ => simp [hp] at hm; rw [hm]
  apply check_sound
  have := ok_accepted; rw [h] at this; simpa using this

theorem sanitize_example : sanitize "1 Mat.001".toList = "_1_Mat_001".toList := by decide +kernel

end TobjMtlx.Tests

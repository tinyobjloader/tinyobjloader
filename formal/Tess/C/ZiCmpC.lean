/-
  MiniC refinement of the translated `zi_cmp` (`lib/tess/src/exact.c`):
  returns `1`/`-1` by the sign order when the signs differ, otherwise `sign * acmp(a, b)`.
  The call to `acmp` is hypothesized through its read-only-frame execution (`C/Acmp.lean`
  proves that execution for every outcome); no claim about allocation.
-/
import Tess.C.Acmp
import Mathlib.Tactic.IntervalCases
import Tess.C.ZiCmp

namespace Tess.C
open Obj.C

abbrev i32t : IntTy := ⟨32, true⟩

theorem load_ziBlock_sign (m : Mem) (zb vblk n : Nat) (sign : Int)
    (hm : m zb = some (ziBlock vblk n sign)) :
    load m (.int i32t) (.ptr zb 16) = .ok (.int i32t (IntTy.wrap IntTy.i32 sign % 2 ^ 32)) := by
  have hpre : ((ziBlock vblk n sign).drop 16).take 4 = encodeLE 4 (IntTy.wrap IntTy.i32 sign) := by
    have e : ziBlock vblk n sign = (encodeLE 8 (ptrPack (.ptr vblk 0)) ++ encodeLE 8 n) ++
        (encodeLE 4 (IntTy.wrap IntTy.i32 sign) ++ [0, 0, 0, 0]) := by
      simp [ziBlock, List.append_assoc]
    have h16 : 16 = (encodeLE 8 (ptrPack (.ptr vblk 0)) ++ encodeLE 8 n).length := by
      simp [encodeLE_length]
    rw [e, h16, List.drop_left]
    simp [encodeLE_length]
  have hrb : readBytes m zb 16 4 = .ok (encodeLE 4 (IntTy.wrap IntTy.i32 sign)) := by
    simp only [readBytes, hm, if_pos (show 16 + 4 ≤ (ziBlock vblk n sign).length by
      simp [ziBlock_length]), hpre]
  have hsize : Ty.size (.int i32t) = 4 := rfl
  simp only [load, hsize, hrb, Res.bind_eq, Res.bind_ok]
  rw [decodeLE_encodeLE, show (256 : Nat) ^ 4 = 2 ^ 32 from rfl]
  rfl

theorem wrap_small (x : Int) (hx : -1 ≤ x) (hx2 : x ≤ 1) : IntTy.wrap IntTy.i32 x % 2 ^ 32 = IntTy.wrap IntTy.i32 x := by
  interval_cases x <;> rfl

theorem evGtI32 (x y : Int) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) :
    evalBin .gt (some i32t) (.int i32t (IntTy.wrap IntTy.i32 x)) (.int i32t (IntTy.wrap IntTy.i32 y)) =
      .ok (boolVal (decide (x > y))) := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  interval_cases x <;> interval_cases y <;> rfl

theorem evNeI32 (x y : Int) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) :
    evalBin .ne (some i32t) (.int i32t (IntTy.wrap IntTy.i32 x)) (.int i32t (IntTy.wrap IntTy.i32 y)) =
      .ok (boolVal (decide (x ≠ y))) := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  interval_cases x <;> interval_cases y <;> rfl

theorem evMulI32 (x y : Int) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) :
    evalBin .mul (some i32t) (.int i32t (IntTy.wrap IntTy.i32 x)) (.int i32t (IntTy.wrap IntTy.i32 y)) =
      .ok (.int i32t (IntTy.wrap IntTy.i32 (x * y))) := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  interval_cases x <;> interval_cases y <;> rfl

/-- `zi_cmp` refinement: signs in `{-1,0,1}`; `acmp` returns `r ∈ {-1,0,1}` when run in a
read-only frame on the same operands. -/
theorem zi_cmp_exs (za zb avblk bvblk na nb : Nat) (sa sb r : Int) (m : Mem)
    (hza : m za = some (ziBlock avblk na sa)) (hzb : m zb = some (ziBlock bvblk nb sb))
    (hsa : -1 ≤ sa ∧ sa ≤ 1) (hsb : -1 ≤ sb ∧ sb ≤ 1) (hr : -1 ≤ r ∧ r ≤ 1)
    (hacmp : ∃ s', ExS LimbGen.prog
      ⟨frameLocals LimbGen.acmp.params [.ptr za 0, .ptr zb 0], m, true⟩ LimbGen.acmp.body
      (.ret (some (.int i32t (IntTy.wrap IntTy.i32 r)))) s')
    (ro : Bool) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.zi_cmp.params [.ptr za 0, .ptr zb 0], m, ro⟩) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.zi_cmp.body
      (.ret (some (.int i32t (IntTy.wrap IntTy.i32
        (if sa ≠ sb then (if sb < sa then 1 else -1) else sa * r))))) sf := by
  have hmem : s0.mem = m := by rw [h0]
  have l0 : s0.locals 0 = some (.ptr za 0) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.ptr zb 0) := by rw [h0]; rfl
  have hza' : s0.mem za = some (ziBlock avblk na sa) := by rw [hmem]; exact hza
  have hzb' : s0.mem zb = some (ziBlock bvblk nb sb) := by rw [hmem]; exact hzb
  have loadS : ∀ (v : Nat) (zbk : Nat) (sg : Int) (nn vbk : Nat),
      s0.locals v = some (.ptr zbk 0) → s0.mem zbk = some (ziBlock vbk nn sg) →
      EvE LimbGen.prog s0 (.load (.int ⟨32, true⟩) (.field (.var v) 16))
        (.int i32t (IntTy.wrap IntTy.i32 sg % 2 ^ 32)) := by
    intro v zbk sg nn vbk hl hm
    have hfield : EvE LimbGen.prog s0 (.field (.var v) 16) (.ptr zbk 16) :=
      EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
    exact EvE.load hfield (load_ziBlock_sign s0.mem zbk vbk nn sg hm)
  have lA := loadS 0 za sa na avblk l0 hza'
  have lB := loadS 1 zb sb nb bvblk l1 hzb'
  rw [wrap_small sa hsa.1 hsa.2] at lA
  rw [wrap_small sb hsb.1 hsb.2] at lB
  have hne := EvE.bin lA lB (evNeI32 sa sb hsa hsb)
  have hgt := EvE.bin lA lB (evGtI32 sa sb hsa hsb)
  by_cases hsame : sa = sb
  · subst hsame
    have hfalse : truthy (boolVal (decide (sa ≠ sa))) = .ok false := by simp [truthy, boolVal]
    have hif : ExS LimbGen.prog s0
        (.ite (.bin .ne (some ⟨32, true⟩) (.load (.int ⟨32, true⟩) (.field (.var 0) 16))
          (.load (.int ⟨32, true⟩) (.field (.var 1) 16)))
          (.ret (some (.cond (.bin .gt (some ⟨32, true⟩) (.load (.int ⟨32, true⟩) (.field (.var 0) 16))
            (.load (.int ⟨32, true⟩) (.field (.var 1) 16))) (.const (.int ⟨32, true⟩ 1))
            (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))))) .skip) .normal s0 :=
      ExS.ite hne hfalse (by simpa using ExS.skip)
    obtain ⟨s', hs'⟩ := hacmp
    have hcall : EvE LimbGen.prog s0 (.call 1 [(.var 0), (.var 1)]) (.int i32t (IntTy.wrap IntTy.i32 r)) := by
      refine EvE.call (vs := [.ptr za 0, .ptr zb 0]) (s' := s') ?_ rfl rfl ?_
      · exact EvArgs.cons (EvE.var l0) (EvArgs.cons (EvE.var l1) EvArgs.nil)
      · rw [hmem]; exact hs'
    have hmul := EvE.bin lA hcall (evMulI32 sa r hsa hr)
    refine ⟨s0, ExS.seq hif (ExS.ret ?_)⟩
    simp only [ne_eq, not_true_eq_false, if_false]
    exact hmul
  · have hdec : truthy (boolVal (decide (sa ≠ sb))) = .ok true := by simp [truthy, boolVal, hsame]
    by_cases hlt : sb < sa
    · have htrue : truthy (boolVal (decide (sa > sb))) = .ok true := by
        have h : decide (sa > sb) = true := by simpa using hlt
        rw [h]; rfl
      have hcond : EvE LimbGen.prog s0 (.cond (.bin .gt (some ⟨32, true⟩)
          (.load (.int ⟨32, true⟩) (.field (.var 0) 16)) (.load (.int ⟨32, true⟩) (.field (.var 1) 16)))
          (.const (.int ⟨32, true⟩ 1)) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))
          (.int i32t (IntTy.wrap IntTy.i32 1)) :=
        EvE.cond hgt htrue (EvE.const _)
      refine ⟨s0, ExS.seq_ret (ExS.ite hne hdec (ExS.ret ?_))⟩
      simp only [hsame, hlt, if_true, if_false, ne_eq, not_false_eq_true]
      exact hcond
    · have hfalse2 : truthy (boolVal (decide (sa > sb))) = .ok false := by
        have h : decide (sa > sb) = false := by simp; omega
        rw [h]; rfl
      have hcond : EvE LimbGen.prog s0 (.cond (.bin .gt (some ⟨32, true⟩)
          (.load (.int ⟨32, true⟩) (.field (.var 0) 16)) (.load (.int ⟨32, true⟩) (.field (.var 1) 16)))
          (.const (.int ⟨32, true⟩ 1)) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))
          (.int i32t (IntTy.wrap IntTy.i32 (-1))) :=
        EvE.cond hgt hfalse2
          (EvE.un (va := Val.int ⟨32, true⟩ 1) (EvE.const _) (by rfl))
      refine ⟨s0, ExS.seq_ret (ExS.ite hne hdec (ExS.ret ?_))⟩
      simp only [hsame, hlt, if_true, if_false, ne_eq, not_false_eq_true]
      exact hcond

/-- The translated `zi_cmp` returns exactly the model `ziCmpM` for well-formed operands whose
limb arrays are laid out as the C structs describe. Signs are `-1/0/1`; limbs are normalized
and bounded. -/
theorem zi_cmp_refines (za zb avblk bvblk : Nat) (aLimbs bLimbs : List Nat) (sa sb : Int) (m : Mem)
    (hsa : -1 ≤ sa ∧ sa ≤ 1) (hsb : -1 ≤ sb ∧ sb ≤ 1)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (hna : Normalized aLimbs) (hnb : Normalized bLimbs)
    (hna64 : aLimbs.length < 18446744073709551616) (hnb64 : bLimbs.length < 18446744073709551616)
    (hza : m za = some (ziBlock avblk aLimbs.length sa))
    (hzb : m zb = some (ziBlock bvblk bLimbs.length sb))
    (havblk : m avblk = some (limbBytes aLimbs)) (hbvblk : m bvblk = some (limbBytes bLimbs))
    (hnad : za < 4294967296) (hnad2 : zb < 4294967296)
    (hav : avblk < 4294967296) (hbv : bvblk < 4294967296)
    (ro : Bool) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.zi_cmp.params [.ptr za 0, .ptr zb 0], m, ro⟩) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.zi_cmp.body
      (.ret (some (.int i32t (IntTy.wrap IntTy.i32 (ziCmpM ⟨sa, aLimbs⟩ ⟨sb, bLimbs⟩))))) sf := by
  -- the callee outcome `r` and its relation to the model comparison
  have key : ∃ r : Int, (-1 ≤ r ∧ r ≤ 1) ∧ r = acmpM aLimbs bLimbs ∧
      ∃ s', ExS LimbGen.prog ⟨frameLocals LimbGen.acmp.params [.ptr za 0, .ptr zb 0], m, true⟩
        LimbGen.acmp.body (.ret (some (.int i32t (IntTy.wrap IntTy.i32 r)))) s' := by
    have S := acmpM_spec aLimbs bLimbs hna hnb hlla hllb
    have W := acmpM_swap aLimbs bLimbs
    have R := acmpM_range aLimbs bLimbs
    by_cases hlen : aLimbs.length = bLimbs.length
    · have hnb' : bLimbs.length = aLimbs.length := hlen.symm
      rcases acmp_exs za avblk zb bvblk sa sb m aLimbs bLimbs aLimbs.length rfl hnb' hna64 hlla hllb hza
        (by rw [← hlen] at hzb; exact hzb) havblk hbvblk hnad hnad2 hav hbv true _ rfl with
        ⟨sf, he, heq, _⟩ | ⟨⟨sf, he, j, hj, ht, hgt⟩⟩ | ⟨⟨sf, he, j, hj, ht, hgt⟩⟩
      · subst heq
        refine ⟨0, by norm_num, ?_, sf, he⟩
        have := (S.1.mpr rfl); omega
      · refine ⟨1, by norm_num, ?_, sf, he⟩
        have hl : lv bLimbs < lv aLimbs :=
          lv_gt_of_mismatch aLimbs bLimbs hllb hlen j (by omega) ht (by simpa using hgt)
        have := S.2.1.mpr hl; omega
      · refine ⟨-1, by norm_num, ?_, sf, he⟩
        have hl : lv aLimbs < lv bLimbs :=
          lv_gt_of_mismatch bLimbs aLimbs hlla hnb' j (by omega) (ht.symm) (by simpa using hgt)
        have h1 := S.2.2.mpr hl
        have := W.mpr h1; omega
    · have hzb' : m zb = some (ziBlock bvblk bLimbs.length sb) := hzb
      have U := acmp_exs_unequal za avblk zb bvblk sa sb m aLimbs bLimbs aLimbs.length bLimbs.length
        rfl rfl hna64 hnb64 hlen hza hzb' true _ rfl
      rcases lt_or_gt_of_ne hlen with hlt | hgt
      · obtain ⟨sf, he, _⟩ := U.2 hlt
        refine ⟨-1, by norm_num, ?_, sf, he⟩
        have hl : lv aLimbs < lv bLimbs := lv_gt_of_longer bLimbs aLimbs hlla hnb hlt
        have h1 := S.2.2.mpr hl
        have := W.mpr h1; omega
      · obtain ⟨sf, he, _⟩ := U.1 hgt
        refine ⟨1, by norm_num, ?_, sf, he⟩
        have hl : lv bLimbs < lv aLimbs := lv_gt_of_longer aLimbs bLimbs hllb hna hgt
        have := S.2.1.mpr hl; omega
  obtain ⟨r, hr, hreq, hacmp⟩ := key
  obtain ⟨sf, hs⟩ := zi_cmp_exs za zb avblk bvblk aLimbs.length bLimbs.length sa sb r m hza hzb hsa hsb hr
    hacmp ro s0 h0
  refine ⟨sf, ?_⟩
  have : ziCmpM ⟨sa, aLimbs⟩ ⟨sb, bLimbs⟩ = (if sa ≠ sb then (if sb < sa then 1 else -1) else sa * r) := by
    unfold ziCmpM
    simp only [hreq]
  rw [this]
  exact hs

end Tess.C

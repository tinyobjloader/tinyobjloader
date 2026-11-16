/-
  Value-level models of the overflow-checked int64 helpers of the public exact predicate
  `tess_orient2i` (`lib/tess/src/tess.c`: `sub`, `mul`, with `mag` as proved in `C/Magnitude`):
  `subChk`/`mulChk` succeed exactly when the true result is representable and then return it
  (`subChk_spec`, `mulChk_spec`), so `orient2iChk` returns the sign of the exact determinant whenever it
  does not report `TESS_RESOURCE_LIMIT` (`orient2iChk_spec`). The C code itself is not refined (signed
  64-bit semantics with out-pointers); the models follow its statements one for one.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Int

namespace Tess.C

def i64min : Int := -(2 ^ 63)
def i64max : Int := 2 ^ 63 - 1
def InI64 (z : Int) : Prop := i64min ≤ z ∧ z ≤ i64max

/-- C `sub`: `a - b` unless the guard `(b > 0 && a < INT64_MIN + b) || (b < 0 && a > INT64_MAX + b)` fires. -/
def subChk (a b : Int) : Option Int :=
  if (0 < b ∧ a < i64min + b) ∨ (b < 0 ∧ i64max + b < a) then none else some (a - b)

theorem subChk_spec (a b : Int) (ha : InI64 a) (hb : InI64 b) :
    (∃ r, subChk a b = some r ∧ r = a - b ∧ InI64 r) ∨ (subChk a b = none ∧ ¬ InI64 (a - b)) := by
  unfold subChk InI64 i64min i64max at *
  by_cases h : (0 < b ∧ a < -(2 ^ 63) + b) ∨ (b < 0 ∧ 2 ^ 63 - 1 + b < a)
  · right; rw [if_pos h]; refine ⟨rfl, ?_⟩; rintro ⟨h1, h2⟩; omega
  · left; rw [if_neg h]; refine ⟨a - b, rfl, rfl, ?_, ?_⟩ <;> omega

/-- C `mul` with `mag`: magnitude product guarded by `x > cap / y`. -/
def mulChk (a b : Int) : Option Int :=
  let x := a.natAbs
  let y := b.natAbs
  let neg := decide (a < 0) != decide (b < 0)
  let cap : Nat := if neg then 2 ^ 63 else 2 ^ 63 - 1
  if y ≠ 0 ∧ cap / y < x then none else
    let z := x * y
    some (if neg = true ∧ z = 2 ^ 63 then i64min else if neg then -(z : Int) else (z : Int))

theorem mulChk_spec (a b : Int) (ha : InI64 a) (hb : InI64 b) :
    (∃ r, mulChk a b = some r ∧ r = a * b ∧ InI64 r) ∨ (mulChk a b = none ∧ ¬ InI64 (a * b)) := by
  have hx : (a.natAbs : Int) = |a| := Int.natCast_natAbs a
  have hy : (b.natAbs : Int) = |b| := Int.natCast_natAbs b
  unfold mulChk
  simp only []
  by_cases hy0 : b.natAbs = 0
  · have hb0 : b = 0 := by omega
    subst hb0
    left
    refine ⟨0, ?_, by simp, ?_⟩
    · simp [Int.natAbs_zero]
    · unfold InI64 i64min i64max; omega
  · have hypos : 0 < b.natAbs := Nat.pos_of_ne_zero hy0
    by_cases hx0 : a.natAbs = 0
    · have ha0 : a = 0 := by omega
      subst ha0
      left
      have : (0:Nat) = 0 := rfl
      refine ⟨0, ?_, by simp, ?_⟩
      · simp [Int.natAbs_zero]
      · unfold InI64 i64min i64max; omega
    · have hxpos : 0 < a.natAbs := Nat.pos_of_ne_zero hx0
      have hapos : a ≠ 0 := by omega
      have hbpos : b ≠ 0 := by omega
      by_cases hneg : (decide (a < 0) != decide (b < 0)) = true
      · -- opposite signs: product is -(x*y), cap = 2^63
        have hopp : (a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0) := by
          simp only [bne_iff_ne, ne_eq, decide_eq_decide] at hneg; omega
        have hprod : a * b = -((a.natAbs * b.natAbs : Nat) : Int) := by
          push_cast; rcases hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            simp [abs_of_neg, abs_of_pos, h1, h2] <;> ring
        simp only [hneg, if_true, ne_eq, hy0, not_false_eq_true, true_and]
        by_cases hc : 2 ^ 63 / b.natAbs < a.natAbs
        · right
          rw [if_pos hc]
          refine ⟨rfl, ?_⟩
          rw [Nat.div_lt_iff_lt_mul hypos] at hc
          rintro ⟨h1, -⟩
          unfold i64min at h1
          rw [hprod] at h1
          push_cast at h1
          nlinarith
        · left
          rw [if_neg hc]
          have hc' : a.natAbs * b.natAbs ≤ 2 ^ 63 := by
            rw [Nat.not_lt, Nat.le_div_iff_mul_le hypos] at hc; linarith
          by_cases hz : a.natAbs * b.natAbs = 2 ^ 63
          · refine ⟨i64min, ?_, ?_, ?_⟩
            · simp [hz, hneg]
            · rw [hprod, hz]; simp [i64min]
            · unfold InI64 i64min i64max; omega
          · refine ⟨-((a.natAbs * b.natAbs : Nat) : Int), ?_, hprod.symm, ?_⟩
            · simp [hz, hneg]
              intro h; exact absurd h hz
            · unfold InI64 i64min i64max
              have : ((a.natAbs * b.natAbs : Nat) : Int) ≤ 2 ^ 63 := by exact_mod_cast hc'
              have hp : 0 ≤ ((a.natAbs * b.natAbs : Nat) : Int) := by positivity
              constructor <;> omega
      · have hsame : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
          simp only [bne_iff_ne, ne_eq, decide_eq_decide, not_not] at hneg; omega
        have hprod : a * b = ((a.natAbs * b.natAbs : Nat) : Int) := by
          push_cast; rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            simp [abs_of_neg, abs_of_pos, h1, h2] <;> ring
        have hneg' : (decide (a < 0) != decide (b < 0)) = false := by simpa using hneg
        simp only [hneg', Bool.false_eq_true, if_false, ne_eq, hy0, not_false_eq_true, true_and]
        by_cases hc : (2 ^ 63 - 1) / b.natAbs < a.natAbs
        · right
          rw [if_pos hc]
          refine ⟨rfl, ?_⟩
          rw [Nat.div_lt_iff_lt_mul hypos] at hc
          rintro ⟨-, h2⟩
          unfold i64max at h2
          rw [hprod] at h2
          push_cast at h2
          have : ((2 ^ 63 - 1 : Nat) : Int) < (a.natAbs : Int) * b.natAbs := by exact_mod_cast hc
          push_cast at this
          nlinarith
        · left
          rw [if_neg hc]
          have hc' : a.natAbs * b.natAbs ≤ 2 ^ 63 - 1 := by
            rw [Nat.not_lt, Nat.le_div_iff_mul_le hypos] at hc; linarith
          refine ⟨((a.natAbs * b.natAbs : Nat) : Int), ?_, hprod.symm, ?_⟩
          · simp [hneg']
          · unfold InI64 i64min i64max
            have h1 : a.natAbs * b.natAbs + 1 ≤ 2 ^ 63 := by
              have : 0 < 2 ^ 63 := by positivity
              omega
            have h2 : ((a.natAbs * b.natAbs : Nat) : Int) + 1 ≤ 2 ^ 63 := by exact_mod_cast h1
            have : ((a.natAbs * b.natAbs : Nat) : Int) ≤ 2 ^ 63 - 1 := by omega
            have hp : 0 ≤ ((a.natAbs * b.natAbs : Nat) : Int) := by positivity
            constructor <;> omega

/-- C `tess_orient2i`: `none` is `TESS_RESOURCE_LIMIT`, `some s` the reported sign. -/
def orient2iChk (ax ay bx bY cx cy : Int) : Option Int :=
  (subChk bx ax).bind fun x => (subChk bY ay).bind fun y => (subChk cx ax).bind fun u =>
  (subChk cy ay).bind fun v => (mulChk x v).bind fun p => (mulChk y u).bind fun q =>
  (subChk p q).bind fun d => some (Int.sign d)

theorem orient2iChk_spec (ax ay bx bY cx cy : Int) (h1 : InI64 ax) (h2 : InI64 ay) (h3 : InI64 bx)
    (h4 : InI64 bY) (h5 : InI64 cx) (h6 : InI64 cy) (s : Int)
    (h : orient2iChk ax ay bx bY cx cy = some s) :
    s = Int.sign ((bx - ax) * (cy - ay) - (bY - ay) * (cx - ax)) := by
  unfold orient2iChk at h
  rcases subChk_spec bx ax h3 h1 with ⟨x, hx, hxe, hxi⟩ | ⟨hx, -⟩
  swap; · simp [hx] at h
  rcases subChk_spec bY ay h4 h2 with ⟨y, hy, hye, hyi⟩ | ⟨hy, -⟩
  swap; · simp [hx, hy] at h
  rcases subChk_spec cx ax h5 h1 with ⟨u, hu, hue, hui⟩ | ⟨hu, -⟩
  swap; · simp [hx, hy, hu] at h
  rcases subChk_spec cy ay h6 h2 with ⟨v, hv, hve, hvi⟩ | ⟨hv, -⟩
  swap; · simp [hx, hy, hu, hv] at h
  rcases mulChk_spec x v hxi hvi with ⟨p, hp, hpe, hpi⟩ | ⟨hp, -⟩
  swap; · simp [hx, hy, hu, hv, hp] at h
  rcases mulChk_spec y u hyi hui with ⟨q, hq, hqe, hqi⟩ | ⟨hq, -⟩
  swap; · simp [hx, hy, hu, hv, hp, hq] at h
  rcases subChk_spec p q hpi hqi with ⟨d, hd, hde, hdi⟩ | ⟨hd, -⟩
  swap; · simp [hx, hy, hu, hv, hp, hq, hd] at h
  simp [hx, hy, hu, hv, hp, hq, hd] at h
  rw [← h, hde, hpe, hqe, hxe, hye, hue, hve]

end Tess.C

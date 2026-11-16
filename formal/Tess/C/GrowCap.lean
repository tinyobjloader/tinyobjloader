/-
  Value-level model of the capacity computation of `grow` (`lib/tess/src/geometry.c`): doubling from
  `cap` (or 8) until `n ≤ nc`, failing with `TESS_RESOURCE_LIMIT` when the next doubling could exceed
  `SIZE_MAX`. `growCap_spec`: on success `n ≤ nc ≤ SIZE_MAX`, `nc` is the base times a power of two and
  (when it doubled) `nc < 2n`, and the doubling never wraps; on failure `n > SIZE_MAX / 2`.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Tess.C

def SZMAX : Nat := 2 ^ 64 - 1

/-- The `while (nc < n)` loop with fuel. -/
def growLoop (n : Nat) : Nat → Nat → Option Nat
  | 0, nc => if nc < n then none else some nc
  | f + 1, nc =>
      if nc < n then (if SZMAX / 2 < nc then none else growLoop n f (nc * 2)) else some nc

theorem growLoop_spec (n : Nat) :
    ∀ f nc, 0 < nc → nc ≤ SZMAX → n ≤ nc * 2 ^ f →
      (∀ r, growLoop n f nc = some r →
        n ≤ r ∧ r ≤ SZMAX ∧ ∃ k, r = nc * 2 ^ k ∧ (k = 0 ∨ r < 2 * n)) ∧
      (growLoop n f nc = none → SZMAX / 2 < n) := by
  intro f
  induction f with
  | zero =>
      intro nc h0 hm hf
      simp only [growLoop]
      by_cases h : nc < n
      · simp only [h, ite_true]
        refine ⟨?_, ?_⟩
        · intro r hr; cases hr
        · intro _; simp at hf; omega
      · simp only [h, ite_false]
        refine ⟨?_, ?_⟩
        · intro r hr; cases hr
          exact ⟨by omega, hm, 0, by simp, Or.inl rfl⟩
        · intro hr; cases hr
  | succ f ih =>
      intro nc h0 hm hf
      simp only [growLoop]
      by_cases h : nc < n
      · simp only [h, ite_true]
        by_cases hb : SZMAX / 2 < nc
        · simp only [hb, ite_true]
          refine ⟨?_, ?_⟩
          · intro r hr; cases hr
          · intro _; omega
        · simp only [hb, ite_false]
          have h2 : nc * 2 ≤ SZMAX := by unfold SZMAX at *; omega
          have hf' : n ≤ nc * 2 * 2 ^ f := by rw [pow_succ] at hf; linarith
          obtain ⟨i1, i2⟩ := ih (nc * 2) (by omega) h2 hf'
          refine ⟨?_, i2⟩
          intro r hr
          obtain ⟨a1, a2, k, a3, a4⟩ := i1 r hr
          refine ⟨a1, a2, k + 1, by rw [a3, pow_succ]; ring, Or.inr ?_⟩
          rcases a4 with rfl | a4
          · simp at a3; omega
          · exact a4
      · simp only [h, ite_false]
        refine ⟨?_, ?_⟩
        · intro r hr; cases hr
          exact ⟨by omega, hm, 0, by simp, Or.inl rfl⟩
        · intro hr; cases hr

/-- C `grow` capacity: `cap` (or 8) doubled until it reaches `n`, for `cap < n`. -/
def growCap (cap n : Nat) : Option Nat :=
  growLoop n (64 + 1) (if cap = 0 then 8 else cap)

theorem growCap_spec (cap n : Nat) (hn : n ≤ SZMAX) (hc : cap ≤ SZMAX) :
    (∀ r, growCap cap n = some r → n ≤ r ∧ r ≤ SZMAX) ∧ (growCap cap n = none → SZMAX / 2 < n) := by
  have h0 : 0 < (if cap = 0 then 8 else cap) := by split <;> omega
  have hm : (if cap = 0 then 8 else cap) ≤ SZMAX := by unfold SZMAX; split <;> unfold SZMAX at hc <;> omega
  have hf : n ≤ (if cap = 0 then 8 else cap) * 2 ^ (64 + 1) := by
    have : (1 : Nat) ≤ (if cap = 0 then 8 else cap) := h0
    have h2 : 2 ^ 64 ≤ 2 ^ (64 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hn' : n < 2 ^ 64 := by unfold SZMAX at hn; have := Nat.one_le_two_pow (n := 64); omega
    calc n ≤ 2 ^ 64 := hn'.le
      _ ≤ 2 ^ (64 + 1) := h2
      _ = 1 * 2 ^ (64 + 1) := (Nat.one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ this
  obtain ⟨a, b⟩ := growLoop_spec n (64 + 1) _ h0 hm hf
  refine ⟨fun r hr => ?_, b⟩
  obtain ⟨x, y, -⟩ := a r hr
  exact ⟨x, y⟩

end Tess.C

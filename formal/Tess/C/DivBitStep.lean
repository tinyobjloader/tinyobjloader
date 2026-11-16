/-
  One bit of the binary path of `zi_divrem`, composed from the proved limb kernels: `div_shift_in`
  (`siPrefix`) followed, when the remainder reaches the divisor, by `div_sub_in` (`sbPrefix`) denotes
  the number-level step `DivModel.binStep` on remainder `< lv b`. (The compare step `div_cmp` is the
  only part of the bit step not refined from C.)
-/
import Tess.C.DivSubC
import Tess.C.DivModel

namespace Tess.C

theorem si_limbs_bound (r : List Nat) (k : Nat) : ∀ x ∈ siPrefix r k r.length, x < 2 ^ 32 :=
  siPrefix_lt r k r.length

theorem bit_shift_step (r b : List Nat) (k : Nat) (hr : ∀ x ∈ r, x < 2 ^ 32)
    (hb : ∀ x ∈ b, x < 2 ^ 32) (hrl : r.length = b.length + 1) (hk : k ≤ 1) (hlt : lv r < lv b) :
    lv (siPrefix r k r.length) = 2 * lv r + k ∧ siCarry r k r.length = 0 ∧
      (siPrefix r k r.length).length = r.length := by
  have hv := si_value r k hr hk r.length
  rw [tv_len] at hv
  have hbl := lv_lt b hb
  have hpow : 2 ^ (32 * r.length) = 2 ^ (32 * b.length) * 2 ^ 32 := by
    rw [hrl, show 32 * (b.length + 1) = 32 * b.length + 32 from by ring, pow_add]
  have h2 : 2 * lv r + k < 2 ^ (32 * r.length) := by
    rw [hpow]
    have : (2:Nat) ≤ 2 ^ 32 := by norm_num
    nlinarith
  have hc0 : siCarry r k r.length = 0 := by
    by_contra hne
    have : 2 ^ (32 * r.length) ≤ siCarry r k r.length * 2 ^ (32 * r.length) :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
    omega
  refine ⟨?_, hc0, siPrefix_length r k _⟩
  rw [hc0] at hv
  omega

theorem bit_sub_step (r1 b : List Nat) (hr : ∀ x ∈ r1, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32)
    (hl : b.length ≤ r1.length) (hle : lv b ≤ lv r1) :
    lv (sbPrefix r1 b r1.length) = lv r1 - lv b ∧ sbBorrow r1 b r1.length = 0 ∧
      (sbPrefix r1 b r1.length).length = r1.length := by
  have hv := sb_value r1 b hr hb r1.length
  rw [tv_len, tv_len_le b r1.length hl] at hv
  have hlt := lv_lt (sbPrefix r1 b r1.length)
    (sbPrefix_lt r1 b r1.length)
  rw [sbPrefix_length] at hlt
  have hbr0 : sbBorrow r1 b r1.length = 0 := by
    by_contra hne
    have h1 : sbBorrow r1 b r1.length = 1 := by
      have := sbBorrow_le r1 b r1.length; omega
    rw [h1] at hv
    omega
  refine ⟨?_, hbr0, sbPrefix_length _ _ _⟩
  rw [hbr0] at hv
  omega

/-- Remainder limbs after one bit step of the C loop (shift in, then subtract when `rem ≥ b`). -/
def bitStepLimbs (r b : List Nat) (k : Nat) : List Nat :=
  if lv b ≤ lv (siPrefix r k r.length) then sbPrefix (siPrefix r k r.length) b r.length
  else siPrefix r k r.length

/-- The limb-level bit step denotes the remainder of `binStep`, stays `< lv b`, and keeps the length. -/
theorem bitStepLimbs_denotes (r b : List Nat) (k q : Nat) (hr : ∀ x ∈ r, x < 2 ^ 32)
    (hb : ∀ x ∈ b, x < 2 ^ 32) (hrl : r.length = b.length + 1) (hk : k ≤ 1) (hlt : lv r < lv b) :
    lv (bitStepLimbs r b k) = (binStep (lv b) (q, lv r) k).2 ∧
      (bitStepLimbs r b k).length = r.length ∧ (∀ x ∈ bitStepLimbs r b k, x < 2 ^ 32) ∧
      lv (bitStepLimbs r b k) < lv b := by
  obtain ⟨h1, -, h3⟩ := bit_shift_step r b k hr hb hrl hk hlt
  unfold bitStepLimbs binStep
  by_cases hge : lv b ≤ lv (siPrefix r k r.length)
  · obtain ⟨s1, -, s3⟩ := bit_sub_step (siPrefix r k r.length) b (siPrefix_lt r k r.length) hb
      (by omega) hge
    have hge' : lv b ≤ 2 * lv r + k := by omega
    rw [h3] at s1 s3
    simp only [if_pos hge, if_pos hge']
    refine ⟨by omega, s3, sbPrefix_lt _ _ _, ?_⟩
    omega
  · have hge' : ¬ lv b ≤ 2 * lv r + k := by omega
    simp only [if_neg hge, if_neg hge']
    refine ⟨by omega, h3, siPrefix_lt r k _, by omega⟩

end Tess.C

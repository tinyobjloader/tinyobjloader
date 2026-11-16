/-
  Model of `zi_divrem` (`lib/tess/src/exact.c`): both the single-limb path
  (radix 2^32 schoolbook step) and the multi-limb path (binary long division
  with compare/subtract) compute the floor quotient and remainder of the
  magnitudes. Statements are about functional models of the loops; the MiniC
  refinement of the C loops, allocation and `norm` are out of scope.
-/
import Tess.C.ZiModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Tess.C

/-- Digit `i` (radix `B`) of `A`. -/
def digit (B A i : Nat) : Nat := A / B ^ i % B

/-- One long-division step: bring down digit `d`, emit a quotient digit. -/
def ldStep (B b : Nat) (s : Nat × Nat) (d : Nat) : Nat × Nat :=
  (B * s.1 + (B * s.2 + d) / b, (B * s.2 + d) % b)

/-- State after processing the top `j` of `L` digits. -/
def ldRun (B b A L : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | j + 1 => ldStep B b (ldRun B b A L j) (digit B A (L - 1 - j))

theorem div_succ_digit (B A i : Nat) (hB : 0 < B) :
    A / B ^ i = B * (A / B ^ (i + 1)) + digit B A i := by
  unfold digit
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (A / B ^ i) B
  omega

theorem ldRun_inv (B b A L : Nat) (hB : 0 < B) (hb : 0 < b) (hA : A < B ^ L) (j : Nat) (hj : j ≤ L) :
    (ldRun B b A L j).1 * b + (ldRun B b A L j).2 = A / B ^ (L - j) ∧
      (ldRun B b A L j).2 < b := by
  induction j with
  | zero => simp [ldRun, Nat.div_eq_of_lt hA, hb]
  | succ j ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      set q := (ldRun B b A L j).1
      set R := (ldRun B b A L j).2
      have hd := div_succ_digit B A (L - 1 - j) hB
      rw [show L - 1 - j + 1 = L - j from by omega] at hd
      have hs : A / B ^ (L - (j + 1)) = B * (A / B ^ (L - j)) + digit B A (L - 1 - j) := by
        rw [show L - (j + 1) = L - 1 - j from by omega]; exact hd
      show (B * q + (B * R + digit B A (L - 1 - j)) / b) * b +
          (B * R + digit B A (L - 1 - j)) % b = _ ∧ _
      rw [hs]
      refine ⟨?_, Nat.mod_lt _ hb⟩
      have := Nat.div_add_mod (B * R + digit B A (L - 1 - j)) b
      nlinarith [h1, this]

/-- Radix-`B` long division computes floor quotient and remainder. -/
theorem ldRun_final (B b A L : Nat) (hB : 0 < B) (hb : 0 < b) (hA : A < B ^ L) :
    (ldRun B b A L L).1 = A / b ∧ (ldRun B b A L L).2 = A % b := by
  obtain ⟨h1, h2⟩ := ldRun_inv B b A L hB hb hA L le_rfl
  simp only [Nat.sub_self, pow_zero, Nat.div_one] at h1
  have hq : A / b = (ldRun B b A L L).1 ∧ A % b = (ldRun B b A L L).2 :=
    Nat.div_mod_unique hb |>.mpr ⟨by linarith, h2⟩
  exact ⟨hq.1.symm, hq.2.symm⟩

/-- The C binary step (`shift in bit; if rem ≥ b then rem -= b, q bit = 1`). -/
def binStep (b : Nat) (s : Nat × Nat) (bit : Nat) : Nat × Nat :=
  if b ≤ 2 * s.2 + bit then (2 * s.1 + 1, 2 * s.2 + bit - b) else (2 * s.1, 2 * s.2 + bit)

/-- With remainder `< b` and a bit, the compare/subtract step equals the radix-2 digit step. -/
theorem binStep_eq (b : Nat) (s : Nat × Nat) (bit : Nat) (hb : 0 < b) (hs : s.2 < b)
    (hbit : bit < 2) : binStep b s bit = ldStep 2 b s bit := by
  unfold binStep ldStep
  have hlt : 2 * s.2 + bit < 2 * b := by omega
  by_cases h : b ≤ 2 * s.2 + bit
  · rw [if_pos h]
    have hdiv : (2 * s.2 + bit) / b = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hmod : (2 * s.2 + bit) % b = 2 * s.2 + bit - b := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hdiv, hmod]
  · rw [if_neg h]
    have hdiv : (2 * s.2 + bit) / b = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv, Nat.mod_eq_of_lt (by omega)]
    simp

/-- The C multi-limb loop: process bits top-down with compare/subtract. -/
def binRun (b A L : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | j + 1 => binStep b (binRun b A L j) (digit 2 A (L - 1 - j))

theorem binRun_eq (b A L : Nat) (hb : 0 < b) (hA : A < 2 ^ L) (j : Nat) (hj : j ≤ L) :
    binRun b A L j = ldRun 2 b A L j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have ih := ih (by omega)
      have hinv := (ldRun_inv 2 b A L (by norm_num) hb hA j (by omega)).2
      show binStep b (binRun b A L j) _ = ldStep 2 b (ldRun 2 b A L j) _
      rw [ih]
      exact binStep_eq b _ _ hb hinv (Nat.mod_lt _ (by norm_num))

/-- Binary long division (multi-limb path of `zi_divrem`) is floor division. -/
theorem binRun_final (b A L : Nat) (hb : 0 < b) (hA : A < 2 ^ L) :
    (binRun b A L L).1 = A / b ∧ (binRun b A L L).2 = A % b := by
  rw [binRun_eq b A L hb hA L le_rfl]
  exact ldRun_final 2 b A L (by norm_num) hb hA

theorem lv_div_pow (l : List Nat) (hb : ∀ x ∈ l, x < 2 ^ 32) (m : Nat) :
    lv l / 2 ^ (32 * m) = lv (l.drop m) := by
  have hsplit : lv l = lv (l.take m) + 2 ^ (32 * (l.take m).length) * lv (l.drop m) := by
    conv_lhs => rw [← List.take_append_drop m l]
    exact lv_append _ _
  have hlt := lv_lt (l.take m) (fun x hx => hb x (List.mem_of_mem_take hx))
  by_cases hm : m ≤ l.length
  · rw [List.length_take_of_le hm] at hsplit hlt
    rw [hsplit, Nat.add_comm, Nat.mul_add_div (pow_pos (by norm_num) _),
      Nat.div_eq_of_lt hlt, Nat.add_zero]
  · have hd : l.drop m = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd]
    have h1 := lv_lt l hb
    have : 2 ^ (32 * l.length) ≤ 2 ^ (32 * m) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.div_eq_of_lt (by omega)

/-- The C bit read `(v[i/32] >> (i%32)) & 1` is binary digit `i` of the denoted integer. -/
theorem digit2_aux (l : List Nat) (hb : ∀ x ∈ l, x < 2 ^ 32) (m r : Nat) (hr : r < 32)
    (hm : m < l.length) : lv l / 2 ^ (32 * m + r) % 2 = (l[m]'hm) / 2 ^ r % 2 := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, lv_div_pow l hb, List.drop_eq_getElem_cons hm]
  show (l[m] + 2 ^ 32 * lv (l.drop (m + 1))) / 2 ^ r % 2 = _
  set H := lv (l.drop (m + 1))
  have h32 : 2 ^ 32 = 2 ^ r * (2 * 2 ^ (31 - r)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [h32, mul_assoc, Nat.add_mul_div_left _ _ (pow_pos (by norm_num) _)]
  rw [Nat.add_mod]
  have : 2 * 2 ^ (31 - r) * H % 2 = 0 := by
    rw [mul_assoc]; exact Nat.mul_mod_right _ _
  rw [this]; simp

theorem digit2_lv (l : List Nat) (hb : ∀ x ∈ l, x < 2 ^ 32) (i : Nat) (hi : i / 32 < l.length) :
    digit 2 (lv l) i = (l[i / 32]'hi) / 2 ^ (i % 32) % 2 := by
  have := digit2_aux l hb (i / 32) (i % 32) (Nat.mod_lt _ (by norm_num)) hi
  have hi' : 32 * (i / 32) + i % 32 = i := Nat.div_add_mod i 32
  rw [hi'] at this
  exact this

/-- Multi-limb path: the bit loop over `32 * |a|` bits yields floor quotient/remainder. -/
theorem divrem_multi (a b : List Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hb : b ≠ []) (hbn : Normalized b) :
    (binRun (lv b) (lv a) (32 * a.length) (32 * a.length)).1 = lv a / lv b ∧
    (binRun (lv b) (lv a) (32 * a.length) (32 * a.length)).2 = lv a % lv b := by
  have hpos : 0 < lv b := by
    have := lv_normalized_ge b hb hbn
    have : 0 < 2 ^ (32 * (b.length - 1)) := pow_pos (by norm_num) _
    omega
  exact binRun_final _ _ _ hpos (lv_lt a ha)

/-- Single-limb path: radix-2^32 schoolbook division yields floor quotient/remainder. -/
theorem divrem_single (a : List Nat) (b0 : Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hb0 : 0 < b0) :
    (ldRun (2 ^ 32) b0 (lv a) a.length a.length).1 = lv a / b0 ∧
    (ldRun (2 ^ 32) b0 (lv a) a.length a.length).2 = lv a % b0 := by
  apply ldRun_final _ _ _ _ (by positivity) hb0
  have := lv_lt a ha
  have h2 : (2 ^ 32) ^ a.length = 2 ^ (32 * a.length) := (pow_mul 2 32 a.length).symm
  rw [h2]; exact this

/-- Signed truncated division as in `zi_divrem`: `a = q*b + r`, `|r| < |b|`, `r` has `a`'s sign. -/
theorem divrem_signed (sa sb : Int) (A B : Nat) (hsa : sa = 1 ∨ sa = -1) (hsb : sb = 1 ∨ sb = -1)
    (hB : 0 < B) :
    sa * A = (sa * sb * (A / B : Nat)) * (sb * B) + sa * (A % B : Nat) ∧
      (A % B : Nat) < B := by
  refine ⟨?_, Nat.mod_lt _ hB⟩
  have h := Nat.div_add_mod A B
  have h' : (A : Int) = B * (A / B : Nat) + (A % B : Nat) := by exact_mod_cast h.symm
  have hs : sb * sb = 1 := by rcases hsb with rfl | rfl <;> norm_num
  calc sa * (A : Int) = sa * (B * (A / B : Nat) + (A % B : Nat)) := by rw [← h']
    _ = _ := by
      have : sa * sb * (A / B : Nat) * (sb * B) = sa * (sb * sb) * (B * (A / B : Nat)) := by ring
      rw [this, hs]; ring

end Tess.C

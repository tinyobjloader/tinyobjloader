/-
  Model of `qr_exponent` (`lib/tess/src/exact.c`): for a positive normalized rational `n/d` with limb
  lists `n`, `d`, `E = bitlen n - bitlen d` bounds the value: `n/d < 2^(E+1)` (`qrExp_lt`). Consequently
  the starting upper bound `hi = 2^(E/2+1)` of `qr_sqrt_bounds` satisfies `hi^2 ≥ n/d`, so its
  internal-error branch `qr_cmp(hi², a) < 0` is unreachable (`sqrt_hi_ge`).
-/
import Tess.C.DivModel
import Mathlib.Data.Nat.Size

namespace Tess.C

/-- Bit length of the number denoted by limbs whose top limb is `t` (`len` limbs). -/
def limbBits (len t : Nat) : Nat := 32 * (len - 1) + Nat.size t

theorem lv_bits (l : List Nat) (hl : ∀ x ∈ l, x < 2 ^ 32) (hne : l ≠ [])
    (hn : Normalized l) : lv l < 2 ^ limbBits l.length (l.getLast hne) ∧
      2 ^ (limbBits l.length (l.getLast hne) - 1) ≤ lv l := by
  set t := l.getLast hne with ht
  have htpos : 0 < t := Nat.pos_of_ne_zero (hn hne)
  have hsplit : l = l.dropLast ++ [t] := (List.dropLast_concat_getLast hne).symm
  have hlen : l.dropLast.length = l.length - 1 := List.length_dropLast
  have hv : lv l = lv l.dropLast + 2 ^ (32 * (l.length - 1)) * t := by
    have := lv_append l.dropLast [t]
    rw [← hsplit, hlen] at this
    simp only [lv] at this
    rw [this]; ring
  have hdl : lv l.dropLast < 2 ^ (32 * (l.length - 1)) := by
    have := lv_lt l.dropLast (fun x hx => hl x (List.dropLast_subset _ hx))
    rwa [hlen] at this
  have ht1 : t < 2 ^ Nat.size t := Nat.lt_size_self t
  have ht2 : 2 ^ (Nat.size t - 1) ≤ t := by
    by_contra hc
    have := Nat.size_le.mpr (not_le.mp hc)
    have : 0 < Nat.size t := Nat.size_pos.mpr htpos
    omega
  have hs : 1 ≤ Nat.size t := Nat.size_pos.mpr htpos
  unfold limbBits
  constructor
  · rw [hv, pow_add]
    nlinarith [pow_pos (by norm_num : 0 < 2) (32 * (l.length - 1))]
  · have : 32 * (l.length - 1) + Nat.size t - 1 = 32 * (l.length - 1) + (Nat.size t - 1) := by omega
    rw [this, pow_add, hv]
    nlinarith [Nat.zero_le (lv l.dropLast), pow_pos (by norm_num : 0 < 2) (32 * (l.length - 1))]

/-- The C exponent estimate `(n.n-1)*32 + nb - ((d.n-1)*32 + db)` as an integer. -/
def qrExp (n d : List Nat) (tn td : Nat) : Int :=
  (limbBits n.length tn : Int) - (limbBits d.length td : Int)

theorem qrExp_lt (n d : List Nat) (hn : ∀ x ∈ n, x < 2 ^ 32) (hd : ∀ x ∈ d, x < 2 ^ 32)
    (hne : n ≠ []) (hde : d ≠ []) (hnn : Normalized n) (hdn : Normalized d) :
    ((lv n : Nat) : ℚ) / ((lv d : Nat) : ℚ) <
      (2 : ℚ) ^ (qrExp n d (n.getLast hne) (d.getLast hde) + 1) := by
  obtain ⟨hn1, -⟩ := lv_bits n hn hne hnn
  obtain ⟨-, hd2⟩ := lv_bits d hd hde hdn
  have hbd1 : 1 ≤ limbBits d.length (d.getLast hde) := by
    unfold limbBits
    have := Nat.size_pos.mpr (Nat.pos_of_ne_zero (hdn hde)); omega
  have hexp : (qrExp n d (n.getLast hne) (d.getLast hde) + 1) =
      (limbBits n.length (n.getLast hne) : Int) - ((limbBits d.length (d.getLast hde) - 1 : Nat) : Int) := by
    unfold qrExp; omega
  generalize limbBits n.length (n.getLast hne) = bn at hn1 hexp
  generalize limbBits d.length (d.getLast hde) = bd at hd2 hexp hbd1
  have hdpos : 0 < lv d := lt_of_lt_of_le (by positivity) hd2
  have hdq : (0 : ℚ) < (lv d : ℚ) := by exact_mod_cast hdpos
  rw [div_lt_iff₀ hdq]
  rw [hexp, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  have h1 : ((lv n : Nat) : ℚ) < (2:ℚ) ^ bn := by exact_mod_cast hn1
  have h2 : (2:ℚ) ^ (bd - 1) ≤ (lv d : ℚ) := by exact_mod_cast hd2
  have hp : (0:ℚ) < 2 ^ (bd - 1) := by positivity
  calc ((lv n : Nat) : ℚ) < 2 ^ bn := h1
    _ = 2 ^ bn / 2 ^ (bd - 1) * 2 ^ (bd - 1) := (div_mul_cancel₀ _ hp.ne').symm
    _ ≤ 2 ^ bn / 2 ^ (bd - 1) * (lv d : ℚ) := mul_le_mul_of_nonneg_left h2 (div_nonneg (by positivity) hp.le)

/-- The starting upper bound of `qr_sqrt_bounds` squares to at least the value. -/
theorem sqrt_hi_ge (a : ℚ) (E : Int) (ha : a < (2 : ℚ) ^ (E + 1)) :
    a ≤ (2 : ℚ) ^ (E.tdiv 2 + 1) * (2 : ℚ) ^ (E.tdiv 2 + 1) := by
  rw [← zpow_add₀ (by norm_num)]
  have : E + 1 ≤ (E.tdiv 2 + 1) + (E.tdiv 2 + 1) := by
    rcases le_or_gt 0 E with h | h
    · rw [Int.tdiv_eq_ediv_of_nonneg h]; omega
    · have h2 : E.tdiv 2 = -((-E).tdiv 2) := by
        rw [← Int.neg_tdiv]; simp
      rw [h2, Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  exact le_of_lt (lt_of_lt_of_le ha (zpow_le_zpow_right₀ (by norm_num) this))

/-- The sqrt-bound start `hi = 2^(E/2+1)` (C truncating division) squares to at least `n/d`. -/
theorem sqrt_start_ok (n d : List Nat) (hn : ∀ x ∈ n, x < 2 ^ 32) (hd : ∀ x ∈ d, x < 2 ^ 32)
    (hne : n ≠ []) (hde : d ≠ []) (hnn : Normalized n) (hdn : Normalized d) :
    ((lv n : Nat) : ℚ) / ((lv d : Nat) : ℚ) ≤
      (2 : ℚ) ^ ((qrExp n d (n.getLast hne) (d.getLast hde)).tdiv 2 + 1) *
      (2 : ℚ) ^ ((qrExp n d (n.getLast hne) (d.getLast hde)).tdiv 2 + 1) :=
  sqrt_hi_ge _ _ (qrExp_lt n d hn hd hne hde hnn hdn)

end Tess.C

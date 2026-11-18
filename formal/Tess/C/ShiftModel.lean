/-
  Model of `shift` (left shift by `bits`) from `lib/tess/src/exact.c`, used by
  `qr_double`: limbs are shifted by `bits % 32` with a carry chain, placed
  above `bits / 32` zero limbs, with the final carry limb. The denoted integer
  is `a * 2^bits`. Value-level model; allocation/`norm` are not refined.
-/
import Tess.C.ZiModel

namespace Tess.C

/-- Carry out of position `i` for the within-limb shift `r`. -/
def shCarry (a : List Nat) (r : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => ((ziAddTerm a k <<< r) ||| shCarry a r k) / 2 ^ 32

def shLimb (a : List Nat) (r k : Nat) : Nat :=
  ((ziAddTerm a k <<< r) ||| shCarry a r k) % 2 ^ 32

def shPrefix (a : List Nat) (r : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => shPrefix a r k ++ [shLimb a r k]

theorem shPrefix_length (a : List Nat) (r k : Nat) : (shPrefix a r k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [shPrefix, ih]

/-- The OR in the C code is a sum: the shifted limb has zero low `r` bits. -/
theorem sh_or_add (x r c : Nat) (hc : c < 2 ^ r) : (x <<< r) ||| c = x * 2 ^ r + c := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hc, Nat.shiftLeft_eq]

theorem shCarry_lt (a : List Nat) (r : Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hr : r < 32) (k : Nat) :
    shCarry a r k < 2 ^ r := by
  induction k with
  | zero => simp [shCarry]
  | succ k ih =>
      have hx := ziAddTerm_bound a ha k
      simp only [shCarry]
      rw [sh_or_add _ _ _ ih, Nat.div_lt_iff_lt_mul (by positivity)]
      have h32 : 2 ^ 32 * 2 ^ r = 2 ^ 32 * 2 ^ r := rfl
      have : ziAddTerm a k * 2 ^ r + shCarry a r k < 2 ^ 32 * 2 ^ r := by
        have : (ziAddTerm a k + 1) * 2 ^ r ≤ 2 ^ 32 * 2 ^ r := Nat.mul_le_mul_right _ hx
        nlinarith
      rw [Nat.mul_comm (2 ^ r)]
      exact this

theorem shift_prefix_value (a : List Nat) (r : Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hr : r < 32) (k : Nat) :
    lv (shPrefix a r k) + shCarry a r k * 2 ^ (32 * k) = tv a k * 2 ^ r := by
  induction k with
  | zero => simp [shPrefix, shCarry, lv, tv]
  | succ k ih =>
      have hc := shCarry_lt a r ha hr k
      have hstep : shLimb a r k + 2 ^ 32 * shCarry a r (k + 1) =
          ziAddTerm a k * 2 ^ r + shCarry a r k := by
        unfold shLimb
        simp only [shCarry]
        rw [sh_or_add _ _ _ hc]
        have := Nat.mod_add_div (ziAddTerm a k * 2 ^ r + shCarry a r k) (2 ^ 32)
        omega
      have hp : lv (shPrefix a r (k + 1)) = lv (shPrefix a r k) + shLimb a r k * 2 ^ (32 * k) := by
        show lv (shPrefix a r k ++ [_]) = _
        rw [lv_append_single, shPrefix_length]
      rw [hp, show 32 * (k + 1) = 32 * k + 32 from by omega, pow_add]
      have := congrArg (· * 2 ^ (32 * k)) hstep
      show _ = (tv a k + ziAddTerm a k * 2 ^ (32 * k)) * 2 ^ r
      nlinarith [ih, this]

/-- `shift`: `bits/32` zero limbs, then the shifted limbs, then the final carry. -/
def shiftLimbs (a : List Nat) (bits : Nat) : List Nat :=
  List.replicate (bits / 32) 0 ++ (shPrefix a (bits % 32) a.length ++ [shCarry a (bits % 32) a.length])

theorem shiftLimbs_value (a : List Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (bits : Nat) :
    lv (shiftLimbs a bits) = lv a * 2 ^ bits := by
  have hr : bits % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have h := shift_prefix_value a (bits % 32) ha hr a.length
  rw [tv_len] at h
  unfold shiftLimbs
  rw [lv_append, lv_replicate_zero, lv_append_single, shPrefix_length]
  have hlen' : (List.replicate (bits / 32) 0).length = bits / 32 := List.length_replicate ..
  rw [hlen']
  have e : bits = 32 * (bits / 32) + bits % 32 := (Nat.div_add_mod bits 32).symm
  have hlen : (List.replicate (bits / 32) 0).length = bits / 32 := List.length_replicate ..
  rw [h]
  conv_rhs => rw [e, pow_add]
  ring

end Tess.C

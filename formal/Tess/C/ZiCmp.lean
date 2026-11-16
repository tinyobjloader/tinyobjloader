/-
  Model of `acmp`/`zi_cmp` (`lib/tess/src/exact.c`): length first, then limbs
  from the most significant down; sign comparison first in `zi_cmp`. For
  normalized well-formed operands the result is exactly the comparison of the
  denoted integers. Value-level model; the C `acmp` loop is refined separately
  in `C/Acmp.lean`.
-/
import Tess.C.ZiModel
import Tess.C.PredModel

namespace Tess.C

/-- Value of a most-significant-first limb list. -/
def rv : List Nat → Nat
  | [] => 0
  | x :: xs => x * 2 ^ (32 * xs.length) + rv xs

theorem rv_append_single (ys : List Nat) (x : Nat) : rv (ys ++ [x]) = x + 2 ^ 32 * rv ys := by
  induction ys with
  | nil => simp [rv]
  | cons y ys ih =>
      simp only [List.cons_append, rv, ih, List.length_append, List.length_cons, List.length_nil]
      rw [show 32 * (ys.length + (0 + 1)) = 32 * ys.length + 32 from by omega, pow_add]
      ring

theorem lv_eq_rv (l : List Nat) : lv l = rv l.reverse := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.reverse_cons, lv, ih, rv_append_single]

theorem rv_lt (l : List Nat) (h : ∀ x ∈ l, x < 2 ^ 32) : rv l < 2 ^ (32 * l.length) := by
  have := lv_lt l.reverse (fun x hx => h x (List.mem_reverse.mp hx))
  rw [lv_eq_rv, List.reverse_reverse, List.length_reverse] at this
  exact this

/-- Most-significant-first compare of equal-length lists (the C `acmp` loop). -/
def acmpTop : List Nat → List Nat → Int
  | x :: xs, y :: ys => if x = y then acmpTop xs ys else if y < x then 1 else -1
  | _, _ => 0

theorem acmpTop_gt (xs ys : List Nat) (hx : ∀ x ∈ xs, x < 2 ^ 32) (hy : ∀ x ∈ ys, x < 2 ^ 32)
    (hl : xs.length = ys.length) (h : acmpTop xs ys = 1) : rv ys < rv xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [acmpTop]
  | cons x xs ih =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          simp only [acmpTop] at h
          by_cases hxy : x = y
          · subst hxy
            simp only [if_true] at h
            have := ih ys (fun z hz => hx z (by simp [hz])) (fun z hz => hy z (by simp [hz])) hl h
            simp only [rv, hl]
            omega
          · simp only [hxy, if_false] at h
            by_cases hyx : y < x
            · have hb := rv_lt ys (fun z hz => hy z (by simp [hz]))
              simp only [rv, hl]
              have : (y + 1) * 2 ^ (32 * ys.length) ≤ x * 2 ^ (32 * ys.length) :=
                Nat.mul_le_mul_right _ hyx
              nlinarith [Nat.zero_le (rv xs)]
            · simp [hyx] at h

theorem acmpTop_cases (xs ys : List Nat) (hl : xs.length = ys.length) :
    acmpTop xs ys = 0 ∧ xs = ys ∨ acmpTop xs ys = 1 ∨ acmpTop ys xs = 1 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [acmpTop]
  | cons x xs ih =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          by_cases hxy : x = y
          · subst hxy
            rcases ih ys hl with ⟨h0, rfl⟩ | h | h
            · left; simp [acmpTop, h0]
            · right; left; simp [acmpTop, h]
            · right; right; simp [acmpTop, h]
          · by_cases hyx : y < x
            · right; left; simp [acmpTop, hxy, hyx]
            · right; right
              have : x < y := by omega
              simp [acmpTop, Ne.symm hxy, this]

/-- `acmp`: longer limb list is larger, else compare from the top. -/
def acmpM (a b : List Nat) : Int :=
  if a.length ≠ b.length then (if b.length < a.length then 1 else -1)
  else acmpTop a.reverse b.reverse

/-- For normalized limb lists `acmp` is exactly the order of the denoted integers. -/
theorem acmpM_gt (a b : List Nat) (ha : Normalized a) (hb : Normalized b)
    (hba : ∀ x ∈ a, x < 2 ^ 32) (hbb : ∀ x ∈ b, x < 2 ^ 32) (h : acmpM a b = 1) : lv b < lv a := by
  unfold acmpM at h
  by_cases hl : a.length ≠ b.length
  · rw [if_pos hl] at h
    by_cases hlt : b.length < a.length
    · exact lv_gt_of_longer a b hbb ha hlt
    · simp [hlt] at h
  · rw [if_neg hl] at h
    have hl' : a.length = b.length := by simpa using hl
    rw [lv_eq_rv, lv_eq_rv]
    exact acmpTop_gt _ _ (fun x hx => hba x (List.mem_reverse.mp hx))
      (fun x hx => hbb x (List.mem_reverse.mp hx)) (by simp [hl']) h

theorem acmpM_cases (a b : List Nat) :
    acmpM a b = 0 ∧ a = b ∨ acmpM a b = 1 ∨ acmpM b a = 1 := by
  unfold acmpM
  by_cases hl : a.length = b.length
  · simp only [hl, ne_eq, not_true_eq_false, if_false, eq_comm (a := b.length)]
    rcases acmpTop_cases a.reverse b.reverse (by simp [hl]) with ⟨h0, h⟩ | h | h
    · left; exact ⟨h0, List.reverse_inj.mp h⟩
    · right; left; exact h
    · right; right; exact h
  · by_cases hlt : b.length < a.length
    · right; left; simp [hl, hlt]
    · right; right; have : a.length < b.length := by omega
      simp [Ne.symm hl, this]

theorem acmpTop_zero (xs ys : List Nat) (hl : xs.length = ys.length) (h : acmpTop xs ys = 0) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          simp only [acmpTop] at h
          by_cases hxy : x = y
          · subst hxy; rw [if_pos rfl] at h; rw [ih ys hl h]
          · rw [if_neg hxy] at h; split at h <;> omega

theorem acmpM_zero (a b : List Nat) (h : acmpM a b = 0) : a = b := by
  unfold acmpM at h
  by_cases hl : a.length ≠ b.length
  · rw [if_pos hl] at h; split at h <;> omega
  · rw [if_neg hl] at h
    have hl' : a.length = b.length := by simpa using hl
    exact List.reverse_inj.mp (acmpTop_zero _ _ (by simp [hl']) h)

theorem acmpM_spec (a b : List Nat) (ha : Normalized a) (hb : Normalized b)
    (hba : ∀ x ∈ a, x < 2 ^ 32) (hbb : ∀ x ∈ b, x < 2 ^ 32) :
    (acmpM a b = 0 ↔ lv a = lv b) ∧ (acmpM a b = 1 ↔ lv b < lv a) ∧ (acmpM b a = 1 ↔ lv a < lv b) := by
  have g1 := acmpM_gt a b ha hb hba hbb
  have g2 := acmpM_gt b a hb ha hbb hba
  rcases acmpM_cases a b with ⟨h0, rfl⟩ | h | h
  · refine ⟨⟨fun _ => rfl, fun _ => h0⟩, ⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩⟩
  · have t1 := g1 h
    refine ⟨⟨fun h' => by omega, fun h' => by omega⟩, ⟨fun _ => t1, fun _ => h⟩, ⟨fun h' => ?_, fun h' => by omega⟩⟩
    have t2 := g2 h'; omega
  · have t2 := g2 h
    refine ⟨⟨fun h' => ?_, fun h' => by omega⟩, ⟨fun h' => ?_, fun h' => by omega⟩, ⟨fun _ => t2, fun _ => h⟩⟩
    · have := acmpM_zero a b h'; subst this; omega
    · have t1 := g1 h'; omega

/-- `zi_cmp`: sign order first, then `sign * acmp`. -/
def ziCmpM (a b : ZiM) : Int :=
  if a.sign ≠ b.sign then (if b.sign < a.sign then 1 else -1) else a.sign * acmpM a.limbs b.limbs

theorem acmpTop_range (xs ys : List Nat) : acmpTop xs ys = 0 ∨ acmpTop xs ys = 1 ∨ acmpTop xs ys = -1 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [acmpTop]
  | cons x xs ih =>
      cases ys with
      | nil => simp [acmpTop]
      | cons y ys =>
          simp only [acmpTop]
          split
          · exact ih ys
          · split <;> simp

theorem acmpM_range (a b : List Nat) :
    acmpM a b = 0 ∨ acmpM a b = 1 ∨ acmpM a b = -1 := by
  unfold acmpM
  split
  · split <;> simp
  · exact acmpTop_range _ _

theorem acmpTop_swap (xs ys : List Nat) : acmpTop xs ys = -1 ↔ acmpTop ys xs = 1 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [acmpTop]
  | cons x xs ih =>
      cases ys with
      | nil => simp [acmpTop]
      | cons y ys =>
          simp only [acmpTop]
          by_cases hxy : x = y
          · subst hxy; simpa using ih ys
          · rw [if_neg hxy, if_neg (Ne.symm hxy)]
            by_cases hyx : y < x
            · have : ¬ x < y := by omega
              simp [hyx, this]
            · have : x < y := by omega
              simp [hyx, this]

theorem acmpM_swap (a b : List Nat) : acmpM a b = -1 ↔ acmpM b a = 1 := by
  unfold acmpM
  by_cases hl : a.length = b.length
  · simp only [hl, ne_eq, not_true_eq_false, ite_false]
    exact acmpTop_swap _ _
  · by_cases hlt : b.length < a.length
    · have : ¬ a.length < b.length := by omega
      simp [hl, Ne.symm hl, hlt, this]
    · have : a.length < b.length := by omega
      simp [hl, Ne.symm hl, hlt, this]

theorem lv_pos_of_sign (z : ZiM) (h : z.WF) (hs : z.sign ≠ 0) : 0 < lv z.limbs := by
  have hne : z.limbs ≠ [] := by intro e; exact hs (h.nz e)
  have := lv_normalized_ge z.limbs hne h.norm
  have : 0 < 2 ^ (32 * (z.limbs.length - 1)) := pow_pos (by norm_num) _
  omega

theorem ziCmpM_spec (a b : ZiM) (ha : a.WF) (hb : b.WF) :
    (ziCmpM a b = 1 ↔ b.val < a.val) ∧ (ziCmpM a b = 0 ↔ a.val = b.val) ∧
      (ziCmpM a b = -1 ↔ a.val < b.val) := by
  have pa := lv_pos_of_sign a ha
  have pb := lv_pos_of_sign b hb
  have va : a.val = a.sign * (lv a.limbs : Int) := rfl
  have vb : b.val = b.sign * (lv b.limbs : Int) := rfl
  have S := acmpM_spec a.limbs b.limbs ha.norm hb.norm ha.bound hb.bound
  have R := acmpM_range a.limbs b.limbs
  have W := acmpM_swap a.limbs b.limbs
  have hs := ha.sign
  have ht := hb.sign
  have za := ha.zero
  have zb := hb.zero
  unfold ziCmpM
  rcases hs with h1 | h1 | h1 <;> rcases ht with h2 | h2 | h2 <;>
    simp only [h1, h2, va, vb] at pa pb ⊢ <;> simp <;> omega
end Tess.C

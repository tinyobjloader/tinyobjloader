/-
  Order and normalization facts for little-endian limb lists: the pieces that
  turn the proved `acmp` mismatch outcomes and the `norm` trimming into
  statements about the denoted integers (`lv`). Pure arithmetic over the
  models; no claim about allocation or the C `zi_add` dispatch itself.
-/
import Tess.C.ZiValue
import Mathlib.Data.List.TakeWhile

namespace Tess.C

theorem lv_append (l1 l2 : List Nat) :
    lv (l1 ++ l2) = lv l1 + 2 ^ (32 * l1.length) * lv l2 := by
  induction l1 with
  | nil => simp [lv]
  | cons x xs ih =>
      simp only [List.cons_append, lv, ih, List.length_cons]
      rw [show 32 * (xs.length + 1) = 32 * xs.length + 32 from by omega, pow_add]
      ring

/-- Normalized: no most-significant zero limb. -/
def Normalized (l : List Nat) : Prop := ∀ h : l ≠ [], l.getLast h ≠ 0

theorem lv_normalized_ge (l : List Nat) (hl : l ≠ []) (hn : Normalized l) :
    2 ^ (32 * (l.length - 1)) ≤ lv l := by
  have hne : l = l.dropLast ++ [l.getLast hl] := (List.dropLast_concat_getLast hl).symm
  have hlast := hn hl
  have hlen : l.dropLast.length = l.length - 1 := List.length_dropLast
  have := lv_append l.dropLast [l.getLast hl]
  rw [← hne, hlen] at this
  simp only [lv] at this
  have hpos : 1 ≤ l.getLast hl := Nat.one_le_iff_ne_zero.mpr hlast
  nlinarith [Nat.zero_le (lv l.dropLast), pow_pos (by norm_num : 0 < 2) (32 * (l.length - 1))]

/-- A longer normalized list denotes a strictly larger number. -/
theorem lv_gt_of_longer (a b : List Nat) (hb : ∀ x ∈ b, x < 2 ^ 32)
    (ha : Normalized a) (hlen : b.length < a.length) : lv b < lv a := by
  have h1 := lv_lt b hb
  have h2 := lv_normalized_ge a (by intro h; simp [h] at hlen) ha
  have : 2 ^ (32 * b.length) ≤ 2 ^ (32 * (a.length - 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Equal length, first (top-down) mismatch at `j` with `b_j < a_j`. -/
theorem lv_gt_of_mismatch (a b : List Nat) (hb : ∀ x ∈ b, x < 2 ^ 32)
    (hlen : a.length = b.length) (j : Nat) (hj : j < b.length)
    (htail : a.drop (j + 1) = b.drop (j + 1))
    (hgt : b[j]'hj < a[j]'(by omega)) : lv b < lv a := by
  have hsplit : ∀ l : List Nat, ∀ hjl : j < l.length,
      lv l = lv (l.take j) + 2 ^ (32 * j) * (l[j]'hjl + 2 ^ 32 * lv (l.drop (j + 1))) := by
    intro l hjl
    have : l = l.take j ++ (l[j]'hjl :: l.drop (j + 1)) := by
      rw [← List.drop_eq_getElem_cons hjl, List.take_append_drop]
    conv_lhs => rw [this]
    rw [lv_append, List.length_take_of_le (by omega)]
    rfl
  have hbt : lv (b.take j) < 2 ^ (32 * j) := by
    have := lv_lt (b.take j) (fun x hx => hb x (List.mem_of_mem_take hx))
    rwa [List.length_take_of_le (by omega)] at this
  rw [hsplit a (by omega), hsplit b hj, htail]
  set H := lv (b.drop (j + 1))
  set P := 2 ^ (32 * j)
  have hP : 0 < P := pow_pos (by norm_num) _
  have hbj := hb _ (List.getElem_mem hj)
  nlinarith [Nat.zero_le (lv (a.take j)), Nat.mul_le_mul_left P (show b[j]'hj + 1 + 2 ^ 32 * H ≤ a[j]'(by omega) + 2 ^ 32 * H by omega)]

/-- Removing most-significant zero limbs (model of `norm`'s length scan). -/
def trimL (l : List Nat) : List Nat := (l.reverse.dropWhile (· == 0)).reverse

theorem lv_zeros (l : List Nat) (h : ∀ x ∈ l, x = 0) : lv l = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [lv]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
      rfl

theorem lv_trimL (l : List Nat) : lv (trimL l) = lv l := by
  have hsplit : l = trimL l ++ (l.reverse.takeWhile (· == 0)).reverse := by
    have := List.takeWhile_append_dropWhile (p := (· == 0)) (l := l.reverse)
    unfold trimL
    conv_lhs => rw [← List.reverse_reverse l]
    rw [← this, List.reverse_append]
    simp
  have hz : lv (l.reverse.takeWhile (· == 0)).reverse = 0 := by
    apply lv_zeros
    intro x hx
    rw [List.mem_reverse] at hx
    simpa using List.mem_takeWhile_imp (p := (· == 0)) hx
  conv_rhs => rw [hsplit]
  rw [lv_append, hz]; simp

theorem trimL_normalized (l : List Nat) : Normalized (trimL l) := by
  intro h
  unfold trimL at h ⊢
  have hne : l.reverse.dropWhile (· == 0) ≠ [] := by
    intro e; apply h; rw [e]; rfl
  rw [List.getLast_reverse]
  have := List.head_dropWhile_not (fun x => x == 0) hne
  simpa using this

/-- Signed value of a sign/limb pair. -/
def sval (s : Int) (l : List Nat) : Int := s * (lv l : Int)

/-- Outcomes of the proved `acmp` (equal / longer / top mismatch) imply `lv b ≤ lv a`. -/
theorem lv_le_of_acmp (a b : List Nat) (ha : Normalized a) (hb : ∀ x ∈ b, x < 2 ^ 32)
    (h : a = b ∨ b.length < a.length ∨
      (a.length = b.length ∧ ∃ j, ∃ hj : j < b.length, a.drop (j + 1) = b.drop (j + 1) ∧
        ∃ hja : j < a.length, b[j]'hj < a[j]'hja)) : lv b ≤ lv a := by
  rcases h with rfl | h | ⟨hlen, j, hj, ht, hja, hg⟩
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (lv_gt_of_longer a b hb ha h)
  · exact Nat.le_of_lt (lv_gt_of_mismatch a b hb hlen j hj ht hg)

/-- Mixed-sign addition `sx*x + sy*y` with `sy = -sx`, `y ≤ x`, as computed by
`zi_add_mixed` (result sign `sx`). -/
theorem ziMixed_signed (sx sy : Int) (hs : sy = -sx) (x y : List Nat)
    (hx : ∀ v ∈ x, v < 2 ^ 32) (hy : ∀ v ∈ y, v < 2 ^ 32) (n : Nat)
    (hxl : x.length ≤ n) (hyl : y.length ≤ n) (hle : lv y ≤ lv x) :
    sval sx (trimL (ziMixedPrefix x y n)) = sval sx x + sval sy y := by
  obtain ⟨-, h⟩ := ziMixed_value x y hx hy n hxl hyl hle
  unfold sval
  rw [lv_trimL, hs]
  have : (lv (ziMixedPrefix x y n) : Int) = lv x - lv y := by omega
  rw [this]; ring

/-- Same-sign addition as computed by `zi_add_equisign` (overflow limb included). -/
theorem ziAdd_signed (s : Int) (a b : List Nat) (n : Nat) (ha : a.length ≤ n) (hb : b.length ≤ n) :
    sval s (trimL (ziAddPrefix a b n ++ [ziAddCarryPrefix a b n])) = sval s a + sval s b := by
  unfold sval
  rw [lv_trimL, ziAdd_value a b n ha hb]
  push_cast; ring

end Tess.C

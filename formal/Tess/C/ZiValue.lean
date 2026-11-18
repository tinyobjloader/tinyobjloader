/-
  Integer semantics of the limb models used by the MiniC loop refinements.

  `lv l` is the natural number denoted by little-endian base-2^32 limbs `l`.
  These are pure arithmetic facts about the models `ziAddPrefix` and
  `ziMixedPrefix` (the values the proved loops compute): equisign addition
  denotes `a + b`; mixed subtraction denotes `a - b` when `a ≥ b`.
  No claim about the C allocator, `norm`, `zi_add` dispatch or signs.
-/
import Tess.C.ZiAdd
import Tess.C.ZiAddMixed
import Tess.C.ZiMul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Tess.C

def lv : List Nat → Nat
  | [] => 0
  | x :: xs => x + 2 ^ 32 * lv xs

/-- Positional value of the first `k` limbs (missing limbs are zero). -/
def tv (l : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => tv l k + ziAddTerm l k * 2 ^ (32 * k)

theorem lv_append_single (l : List Nat) (x : Nat) :
    lv (l ++ [x]) = lv l + x * 2 ^ (32 * l.length) := by
  induction l with
  | nil => simp [lv]
  | cons y ys ih =>
      simp only [List.cons_append, lv, ih, List.length_cons]
      rw [show 32 * (ys.length + 1) = 32 * ys.length + 32 from by omega, pow_add]
      ring

theorem ziAddTerm_ge (l : List Nat) (i : Nat) (h : l.length ≤ i) : ziAddTerm l i = 0 := by
  unfold ziAddTerm
  rw [dif_neg (by omega)]

theorem ziAddTerm_cons_succ (x : Nat) (xs : List Nat) (k : Nat) :
    ziAddTerm (x :: xs) (k + 1) = ziAddTerm xs k := by
  unfold ziAddTerm
  by_cases h : k < xs.length
  · rw [dif_pos (by simpa using h), dif_pos h]; rfl
  · rw [dif_neg (by simpa using h), dif_neg h]

theorem tv_cons (x : Nat) (xs : List Nat) (k : Nat) :
    tv (x :: xs) (k + 1) = x + 2 ^ 32 * tv xs k := by
  induction k with
  | zero => simp [tv, ziAddTerm]
  | succ k ih =>
      show tv (x :: xs) (k + 1) + ziAddTerm (x :: xs) (k + 1) * 2 ^ (32 * (k + 1)) = _
      rw [ih, ziAddTerm_cons_succ]
      show _ = x + 2 ^ 32 * (tv xs k + ziAddTerm xs k * 2 ^ (32 * k))
      rw [show 32 * (k + 1) = 32 * k + 32 from by omega, pow_add]
      ring

theorem tv_len (l : List Nat) : tv l l.length = lv l := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.length_cons, tv_cons, ih]; rfl

theorem tv_eq_lv (l : List Nat) (j : Nat) : tv l (l.length + j) = lv l := by
  induction j with
  | zero => exact tv_len l
  | succ j ih =>
      show tv l (l.length + j) + ziAddTerm l (l.length + j) * _ = _
      rw [ziAddTerm_ge l _ (by omega), ih]; simp

theorem lv_lt (l : List Nat) (h : ∀ x ∈ l, x < 2 ^ 32) : lv l < 2 ^ (32 * l.length) := by
  induction l with
  | nil => simp [lv]
  | cons x xs ih =>
      have hx := h x (by simp)
      have := ih (fun y hy => h y (by simp [hy]))
      simp only [lv, List.length_cons]
      rw [show 32 * (xs.length + 1) = 32 * xs.length + 32 from by omega, pow_add]
      nlinarith

theorem ziAdd_prefix_value (a b : List Nat) (k : Nat) :
    lv (ziAddPrefix a b k) + ziAddCarryPrefix a b k * 2 ^ (32 * k) = tv a k + tv b k := by
  induction k with
  | zero => simp [ziAddPrefix, ziAddCarryPrefix, lv, tv]
  | succ k ih =>
      have hstep : ziAddLimb a b k (ziAddCarryPrefix a b k) +
          2 ^ 32 * ziAddCarry a b k (ziAddCarryPrefix a b k) =
          ziAddTerm a k + ziAddTerm b k + ziAddCarryPrefix a b k := by
        unfold ziAddLimb ziAddCarry ziAddStep
        have := Nat.mod_add_div (ziAddTerm a k + ziAddTerm b k + ziAddCarryPrefix a b k) (2 ^ 32)
        omega
      have hc : ziAddCarryPrefix a b (k + 1) = ziAddCarry a b k (ziAddCarryPrefix a b k) := rfl
      rw [hc]
      have hp : lv (ziAddPrefix a b (k + 1)) = lv (ziAddPrefix a b k) +
          ziAddLimb a b k (ziAddCarryPrefix a b k) * 2 ^ (32 * k) := by
        show lv (ziAddPrefix a b k ++ [_]) = _
        rw [lv_append_single, ziAddPrefix_length]
      rw [hp, show 32 * (k + 1) = 32 * k + 32 from by omega, pow_add]
      have := congrArg (· * 2 ^ (32 * k)) hstep
      show _ = tv a k + ziAddTerm a k * 2 ^ (32 * k) + (tv b k + ziAddTerm b k * 2 ^ (32 * k))
      nlinarith [ih, this]

theorem tv_len_le (l : List Nat) (n : Nat) (h : l.length ≤ n) : tv l n = lv l := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  exact tv_eq_lv l j

/-- Equisign addition: the limbs written by `zi_add_equisign` (low `n` limbs
plus the overflow limb at index `n`) denote exactly `a + b`. -/
theorem ziAdd_value (a b : List Nat) (n : Nat) (ha : a.length ≤ n) (hb : b.length ≤ n) :
    lv (ziAddPrefix a b n ++ [ziAddCarryPrefix a b n]) = lv a + lv b := by
  rw [lv_append_single, ziAddPrefix_length]
  have := ziAdd_prefix_value a b n
  rw [tv_len_le a n ha, tv_len_le b n hb] at this
  exact this

theorem ziMixed_prefix_value (a b : List Nat) (hb : ∀ x ∈ b, x < 2 ^ 32) (k : Nat) :
    lv (ziMixedPrefix a b k) + tv b k = tv a k + ziMixedBorrowPrefix a b k * 2 ^ (32 * k) := by
  induction k with
  | zero => simp [ziMixedPrefix, ziMixedBorrowPrefix, lv, tv]
  | succ k ih =>
      have hbt := ziAddTerm_bound b hb k
      have hbr := ziMixedBorrowPrefix_bound a b k
      have hstep : ziMixedLimb a b k (ziMixedBorrowPrefix a b k) + ziAddTerm b k +
          ziMixedBorrowPrefix a b k = ziAddTerm a k +
          2 ^ 32 * ziMixedBorrow a b k (ziMixedBorrowPrefix a b k) := by
        unfold ziMixedLimb ziMixedBorrow
        split <;> split <;> omega
      have hp : lv (ziMixedPrefix a b (k + 1)) = lv (ziMixedPrefix a b k) +
          ziMixedLimb a b k (ziMixedBorrowPrefix a b k) * 2 ^ (32 * k) := by
        show lv (ziMixedPrefix a b k ++ [_]) = _
        rw [lv_append_single, ziMixedPrefix_length]
      have hc : ziMixedBorrowPrefix a b (k + 1) =
          ziMixedBorrow a b k (ziMixedBorrowPrefix a b k) := rfl
      rw [hp, hc, show 32 * (k + 1) = 32 * k + 32 from by omega, pow_add]
      have := congrArg (· * 2 ^ (32 * k)) hstep
      show _ = tv a k + ziAddTerm a k * 2 ^ (32 * k) + _
      show _ + (tv b k + ziAddTerm b k * 2 ^ (32 * k)) = _
      nlinarith [ih, this]

theorem ziMixedPrefix_mem (a b : List Nat) (ha : ∀ x ∈ a, x < 2 ^ 32)
    (hb : ∀ x ∈ b, x < 2 ^ 32) (k : Nat) : ∀ x ∈ ziMixedPrefix a b k, x < 2 ^ 32 := by
  induction k with
  | zero => simp [ziMixedPrefix]
  | succ k ih =>
      intro x hx
      simp only [ziMixedPrefix, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih x hx
      · exact ziMixedLimb_bound a b ha hb k _ (ziMixedBorrowPrefix_bound a b k)

/-- Mixed-sign subtraction: when `b ≤ a` the final borrow is zero and the
limbs written by `zi_add_mixed` denote exactly `a - b`. -/
theorem ziMixed_value (a b : List Nat) (ha : ∀ x ∈ a, x < 2 ^ 32)
    (hb : ∀ x ∈ b, x < 2 ^ 32) (n : Nat) (hal : a.length ≤ n) (hbl : b.length ≤ n)
    (hle : lv b ≤ lv a) :
    ziMixedBorrowPrefix a b n = 0 ∧ lv (ziMixedPrefix a b n) + lv b = lv a := by
  have h := ziMixed_prefix_value a b hb n
  rw [tv_len_le a n hal, tv_len_le b n hbl] at h
  have hlt := lv_lt (ziMixedPrefix a b n) (ziMixedPrefix_mem a b ha hb n)
  rw [ziMixedPrefix_length] at hlt
  have hbr := ziMixedBorrowPrefix_bound a b n
  have hz : ziMixedBorrowPrefix a b n = 0 := by
    by_contra hne
    have h1 : ziMixedBorrowPrefix a b n = 1 := by omega
    rw [h1] at h
    omega
  refine ⟨hz, ?_⟩
  rw [hz] at h
  omega

theorem lv_set (l : List Nat) (i v : Nat) (h : i < l.length) :
    lv (l.set i v) + (l[i]?).getD 0 * 2 ^ (32 * i) = lv l + v * 2 ^ (32 * i) := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
      cases i with
      | zero => simp [lv]; ring
      | succ i =>
          have := ih i (by simpa using h)
          show x + 2 ^ 32 * lv (xs.set i v) + ((x :: xs)[i + 1]?).getD 0 * _ = x + 2 ^ 32 * lv xs + v * _
          rw [show ((x :: xs)[i + 1]?) = xs[i]? from rfl,
            show 32 * (i + 1) = 32 * i + 32 from by omega, pow_add]
          nlinarith [this]

/-- Inner multiply row: value accounting after `j ≤ |b|` limb products. -/
theorem ziMulAcc_value (a b : List Nat) (i : Nat) (t : List Nat) (hlen : i + b.length ≤ t.length)
    (j : Nat) (hj : j ≤ b.length) :
    lv (ziMulAcc a b i t 0 j).1 + (ziMulAcc a b i t 0 j).2 * 2 ^ (32 * (i + j)) =
      lv t + ziAddTerm a i * tv b j * 2 ^ (32 * i) := by
  induction j with
  | zero => simp [ziMulAcc, tv]
  | succ j ih =>
      have ih := ih (by omega)
      have hl : (ziMulAcc a b i t 0 j).1.length = t.length := ziMulAcc_length a b i t 0 j
      have hs := lv_set (ziMulAcc a b i t 0 j).1 (i + j)
        ((ziAddTerm a i * ziAddTerm b j + ((ziMulAcc a b i t 0 j).1[i + j]?).getD 0 +
          (ziMulAcc a b i t 0 j).2) % 2 ^ 32) (by omega)
      rw [ziMulAcc_succ]
      simp only [ziMulAccStep]
      set T := (ziMulAcc a b i t 0 j).1
      set c := (ziMulAcc a b i t 0 j).2
      set old := (T[i + j]?).getD 0
      have hx := Nat.mod_add_div (ziAddTerm a i * ziAddTerm b j + old + c) (2 ^ 32)
      have hP : 2 ^ (32 * (i + (j + 1))) = 2 ^ (32 * (i + j)) * 2 ^ 32 := by
        rw [show 32 * (i + (j + 1)) = 32 * (i + j) + 32 from by omega, pow_add]
      have hQ : 2 ^ (32 * (i + j)) = 2 ^ (32 * i) * 2 ^ (32 * j) := by
        rw [show 32 * (i + j) = 32 * i + 32 * j from by omega, pow_add]
      show _ + _ * 2 ^ (32 * (i + (j + 1))) = lv t + ziAddTerm a i * (tv b j + ziAddTerm b j * 2 ^ (32 * j)) * 2 ^ (32 * i)
      rw [hP]
      have h1 := congrArg (· * 2 ^ (32 * (i + j))) hx
      rw [hQ] at h1 ih hs ⊢
      nlinarith [hs, ih, h1]

/-- A row only writes positions `i .. i+|b|-1`; higher positions are untouched. -/
theorem lv_replicate_zero (n : Nat) : lv (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, lv, ih]

theorem ziMulAcc_getD_high (a b : List Nat) (i : Nat) (t : List Nat) (c : Nat) (j : Nat)
    (hj : j ≤ b.length) (idx : Nat) (hidx : i + b.length ≤ idx) :
    ((ziMulAcc a b i t c j).1[idx]?).getD 0 = (t[idx]?).getD 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [ziMulAcc_succ]
      simp only [ziMulAccStep]
      rw [List.getElem?_set, if_neg (by omega)]
      exact ih (by omega)

theorem getD_set_ne (l : List Nat) (k v idx : Nat) (h : k ≠ idx) :
    ((l.set k v)[idx]?).getD 0 = (l[idx]?).getD 0 := by
  rw [List.getElem?_set, if_neg h]

/-- Product of the first `k` rows, starting from an all-zero buffer. -/
theorem ziMulRows_value (a b : List Nat) (hla : ∀ x ∈ a, x < 2 ^ 32)
    (hlb : ∀ x ∈ b, x < 2 ^ 32) (L : Nat) (hL : a.length + b.length ≤ L) (k : Nat)
    (hk : k ≤ a.length) :
    lv (ziMulRows a b (List.replicate L 0) k) = tv a k * lv b ∧
      (∀ idx, k + b.length ≤ idx → ((ziMulRows a b (List.replicate L 0) k)[idx]?).getD 0 = 0) ∧
      (ziMulRows a b (List.replicate L 0) k).length = L := by
  induction k with
  | zero =>
      refine ⟨by simp [ziMulRows, tv, lv_replicate_zero], ?_, by simp [ziMulRows]⟩
      intro idx _
      simp [ziMulRows, List.getElem?_replicate]
      split <;> rfl
  | succ k ih =>
      obtain ⟨hv, hz, hlen⟩ := ih (by omega)
      set T := ziMulRows a b (List.replicate L 0) k with hT
      have hmem : ∀ x ∈ T, x < 2 ^ 32 := ziMulRows_mem_bound a b _ hla hlb
        (by intro x hx; simp at hx; omega) k
      have hrow := ziMulAcc_value a b k T (by omega) b.length le_rfl
      have hcar := ziMulAcc_carry_bound a b k T 0 hla hlb hmem (by decide) b.length
      have hacl : (ziMulAcc a b k T 0 b.length).1.length = L := by
        rw [ziMulAcc_length, hlen]
      have hset := lv_set (ziMulAcc a b k T 0 b.length).1 (k + b.length)
        ((ziMulAcc a b k T 0 b.length).2 % 2 ^ 32) (by omega)
      have hold : (((ziMulAcc a b k T 0 b.length).1)[k + b.length]?).getD 0 = 0 := by
        rw [ziMulAcc_getD_high a b k T 0 b.length le_rfl _ le_rfl]
        exact hz _ le_rfl
      rw [hold, Nat.mod_eq_of_lt hcar] at hset
      have hfin : ziMulRows a b (List.replicate L 0) (k + 1) =
          (ziMulAcc a b k T 0 b.length).1.set (k + b.length)
            ((ziMulAcc a b k T 0 b.length).2 % 2 ^ 32) := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hfin]
        rw [tv_len b] at hrow
        show _ = (tv a k + ziAddTerm a k * 2 ^ (32 * k)) * lv b
        rw [hv] at hrow
        rw [Nat.mod_eq_of_lt hcar]
        simp only [zero_mul, add_zero] at hset
        rw [hset, hrow]
        ring
      · intro idx hidx
        rw [hfin, getD_set_ne _ _ _ _ (by omega),
          ziMulAcc_getD_high a b k T 0 b.length le_rfl _ (by omega)]
        exact hz idx (by omega)
      · rw [hfin, List.length_set, hacl]

/-- The schoolbook rows over a zero buffer of capacity `≥ |a|+|b|` denote `a * b`. -/
theorem ziMul_value (a b : List Nat) (hla : ∀ x ∈ a, x < 2 ^ 32)
    (hlb : ∀ x ∈ b, x < 2 ^ 32) (L : Nat) (hL : a.length + b.length ≤ L) :
    lv (ziMulRows a b (List.replicate L 0) a.length) = lv a * lv b := by
  rw [(ziMulRows_value a b hla hlb L hL a.length le_rfl).1, tv_len]

end Tess.C

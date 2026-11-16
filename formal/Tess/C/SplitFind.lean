/-
  Value-level model of the binary search `split_find` (`lib/tess/src/edits.c`) over the lexicographically
  sorted edge records: `lb` is the loop with fuel, `lb_spec` shows its result `i` is the lower bound
  (every earlier record is `< key`, every record from `i` on is `≥ key`), and `splitFind_spec` that the
  function returns an index exactly when the record at the lower bound equals the key.
-/
import Mathlib.Tactic.Linarith

namespace Tess.C

/-- C comparison of edge keys `(a, b)`: lexicographic `<`. -/
def ltk (x y : Nat × Nat) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

instance (x y : Nat × Nat) : Decidable (ltk x y) := by unfold ltk; infer_instance

theorem ltk_trans {x y z : Nat × Nat} (h1 : ltk x y) (h2 : ltk y z) : ltk x z := by
  unfold ltk at *; omega

theorem ltk_irrefl (x : Nat × Nat) : ¬ ltk x x := by unfold ltk; omega

theorem ltk_total (x y : Nat × Nat) : ltk x y ∨ x = y ∨ ltk y x := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  unfold ltk; simp only [Prod.mk.injEq]; omega

/-- The loop of `split_find` with fuel. -/
def lb (f : Nat → Nat × Nat) (key : Nat × Nat) : Nat → Nat → Nat → Nat
  | 0, low, _ => low
  | fuel + 1, low, high =>
      if low < high then
        if ltk (f (low + (high - low) / 2)) key then lb f key fuel (low + (high - low) / 2 + 1) high
        else lb f key fuel low (low + (high - low) / 2)
      else low

theorem lb_spec (f : Nat → Nat × Nat) (key : Nat × Nat) (n : Nat)
    (hs : ∀ i j, i ≤ j → j < n → ¬ ltk (f j) (f i)) :
    ∀ fuel low high, high - low ≤ fuel → low ≤ high → high ≤ n →
      (∀ j, j < low → ltk (f j) key) → (∀ j, high ≤ j → j < n → ¬ ltk (f j) key) →
      (∀ j, j < lb f key fuel low high → ltk (f j) key) ∧
      (∀ j, lb f key fuel low high ≤ j → j < n → ¬ ltk (f j) key) := by
  intro fuel
  induction fuel with
  | zero =>
      intro low high hf hl hh h1 h2
      have : low = high := by omega
      subst this
      exact ⟨h1, h2⟩
  | succ fuel ih =>
      intro low high hf hl hh h1 h2
      unfold lb
      by_cases hlt : low < high
      · simp only [hlt, if_true]
        have hmid1 : low ≤ low + (high - low) / 2 := by omega
        have hmid2 : low + (high - low) / 2 < high := by omega
        by_cases hk : ltk (f (low + (high - low) / 2)) key
        · simp only [hk, if_true]
          apply ih _ _ (by omega) (by omega) hh _ h2
          intro j hj
          by_cases hj' : j < low
          · exact h1 j hj'
          · have : j ≤ low + (high - low) / 2 := by omega
            by_contra hnk
            have hl2 : ltk (f j) (f (low + (high - low) / 2)) ∨ f j = f (low + (high - low) / 2) := by
              rcases ltk_total (f j) (f (low + (high - low) / 2)) with h | h | h
              · exact Or.inl h
              · exact Or.inr h
              · exact absurd h (hs j _ this (by omega))
            rcases hl2 with h | h
            · exact hnk (ltk_trans h hk)
            · rw [h] at hnk; exact hnk hk
        · simp only [hk, if_false]
          refine ih low (low + (high - low) / 2) (by omega) (by omega) (by omega) h1 ?_
          intro j hj hjn
          by_cases hj' : high ≤ j
          · exact h2 j hj' hjn
          · have : low + (high - low) / 2 ≤ j := hj
            intro hjk
            -- f j ≥ f mid, f mid ≥ key; so f j ≥ key
            rcases ltk_total (f (low + (high - low) / 2)) (f j) with h | h | h
            · exact hk (by
                rcases ltk_total (f (low + (high - low) / 2)) key with h' | h' | h'
                · exact h'
                · rw [h'] at h; exact absurd (ltk_trans h hjk) (ltk_irrefl _)
                · exact absurd (ltk_trans h' (ltk_trans h hjk)) (ltk_irrefl _))
            · rw [← h] at hjk; exact hk hjk
            · exact hs _ _ this hjn h
      · simp only [hlt, if_false]
        have : low = high := by omega
        subst this
        exact ⟨h1, h2⟩

/-- C `split_find`: the key is the sorted endpoint pair; `none` is `SIZE_MAX`. -/
def splitFind (f : Nat → Nat × Nat) (n a b : Nat) : Option Nat :=
  let key := (min a b, max a b)
  let i := lb f key n 0 n
  if i < n ∧ f i = key then some i else none

theorem splitFind_spec (f : Nat → Nat × Nat) (n a b : Nat)
    (hs : ∀ i j, i ≤ j → j < n → ¬ ltk (f j) (f i)) :
    (∀ i, splitFind f n a b = some i → i < n ∧ f i = (min a b, max a b)) ∧
    (splitFind f n a b = none → ∀ j, j < n → f j ≠ (min a b, max a b)) := by
  set key := (min a b, max a b) with hk
  obtain ⟨hlo, hhi⟩ := lb_spec f key n hs n 0 n (by omega) (by omega) le_rfl
    (fun j hj => absurd hj (Nat.not_lt_zero _)) (fun j hj hjn => absurd hjn (by omega))
  set r := lb f key n 0 n with hr
  unfold splitFind
  simp only [← hk, ← hr]
  constructor
  · intro i hi
    by_cases h : r < n ∧ f r = key
    · simp only [h, and_self, if_true] at hi
      cases hi; exact h
    · simp only [h, if_false] at hi; cases hi
  · intro hn j hj
    by_cases h : r < n ∧ f r = key
    · simp only [h, and_self, if_true] at hn; cases hn
    · intro hjk
      by_cases hjr : j < r
      · have := hlo j hjr
        rw [hjk] at this; exact ltk_irrefl _ this
      · have hrn : r < n := by
          by_contra hc
          have := hlo j (by omega)
          rw [hjk] at this; exact ltk_irrefl _ this
        have hfr : f r ≠ key := fun e => h ⟨hrn, e⟩
        have h1 : ¬ ltk (f r) key := hhi r le_rfl hrn
        have h2 : ltk key (f r) := by
          rcases ltk_total (f r) key with c | c | c
          · exact absurd c h1
          · exact absurd c hfr
          · exact c
        rcases Nat.eq_or_lt_of_le (not_lt.mp hjr) with e | e
        · exact hfr (by rw [e]; exact hjk)
        · have := hs r j e.le hj
          rw [hjk] at this; exact this h2

end Tess.C

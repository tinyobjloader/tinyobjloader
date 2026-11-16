/-
  Value-level model of the union-find used by `tess_topology` (`lib/tess/src/topology.c`) to count
  face components: `parent[x] != x` chains are followed without path compression and a union sets
  `parent[b] = a` for distinct roots. `Reach` (every element reaches a root) is established initially,
  preserved by the union (`union_reach`), and makes the `find` loop terminate with a root
  (`find_spec`).
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Basic

namespace Tess.C

/-- Every element reaches a fixed point (root) of `p`. -/
def Reach (p : Nat → Nat) : Prop := ∀ x, ∃ k, p (p^[k] x) = p^[k] x

theorem reach_init : Reach id := fun x => ⟨0, rfl⟩

/-- The C loop `while (parent[a] != a) a = parent[a]`, with fuel. -/
def find (p : Nat → Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | x, f + 1 => if p x = x then some x else find p (p x) f

theorem find_spec (p : Nat → Nat) : ∀ k x, p (p^[k] x) = p^[k] x →
    ∃ r, find p x (k + 1) = some r ∧ p r = r := by
  intro k
  induction k with
  | zero => intro x h; exact ⟨x, by simpa [find] using h, by simpa using h⟩
  | succ k ih =>
      intro x h
      by_cases hx : p x = x
      · exact ⟨x, by simp [find, hx], hx⟩
      · have h' : p (p^[k] (p x)) = p^[k] (p x) := by
          rw [← Function.iterate_succ_apply]; exact h
        obtain ⟨r, hr, hroot⟩ := ih (p x) h'
        refine ⟨r, ?_, hroot⟩
        rw [find, if_neg hx]; exact hr

theorem find_total (p : Nat → Nat) (h : Reach p) (x : Nat) : ∃ r f, find p x f = some r ∧ p r = r := by
  obtain ⟨k, hk⟩ := h x
  obtain ⟨r, hr, hroot⟩ := find_spec p k x hk
  exact ⟨r, k + 1, hr, hroot⟩

/-- `parent[b] = a`. -/
def link (p : Nat → Nat) (a b : Nat) : Nat → Nat := Function.update p b a

/-- Linking two distinct roots (`parent[b] = a`) keeps every element reaching a root. -/
theorem union_reach (p : Nat → Nat) (a b : Nat) (hr : Reach p) (ha : p a = a) (hb : p b = b)
    (hab : a ≠ b) : Reach (link p a b) := by
  have key : ∀ k x, p (p^[k] x) = p^[k] x → ∃ j, link p a b ((link p a b)^[j] x) = (link p a b)^[j] x := by
    intro k
    induction k with
    | zero =>
        intro x h
        simp only [Function.iterate_zero, id] at h
        by_cases hx : x = b
        · subst hx
          refine ⟨1, ?_⟩
          simp [link, Function.update_self, Function.update_of_ne hab, ha]
        · refine ⟨0, ?_⟩
          simp [link, Function.update_of_ne hx, h]
    | succ k ih =>
        intro x h
        by_cases hx : x = b
        · subst hx
          refine ⟨1, ?_⟩
          simp [link, Function.update_self, Function.update_of_ne hab, ha]
        · have h' : p (p^[k] (p x)) = p^[k] (p x) := by
            rw [← Function.iterate_succ_apply]; exact h
          obtain ⟨j, hj⟩ := ih (p x) h'
          refine ⟨j + 1, ?_⟩
          rw [Function.iterate_succ_apply]
          have e : link p a b x = p x := by simp [link, Function.update_of_ne hx]
          rw [e]
          exact hj
  intro x
  obtain ⟨k, hk⟩ := hr x
  exact key k x hk

end Tess.C

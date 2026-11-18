/-
  Limb-level model of the single-limb schoolbook division loop `div_single_fill`
  (`lib/tess/src/exact.c`): processing the limbs of `a` from the most significant end, each step
  emits the quotient limb `(2^32 R + x) / d` and carries the remainder `(2^32 R + x) % d`.
  `dsRun` returns the quotient limbs (little-endian) and the remainder after `j` steps; the final
  quotient limb list denotes `lv a / d` and the remainder `lv a % d`.
-/
import Tess.C.ZiOrder
import Tess.C.DivModel

namespace Tess.C

def dsStep (d x : Nat) (s : List Nat × Nat) : List Nat × Nat :=
  ((2 ^ 32 * s.2 + x) / d :: s.1, (2 ^ 32 * s.2 + x) % d)

def dsRun (a : List Nat) (d : Nat) : Nat → List Nat × Nat
  | 0 => ([], 0)
  | j + 1 => dsStep d (ziAddTerm a (a.length - 1 - j)) (dsRun a d j)

theorem dsStep_lt (d x R : Nat) (hd : 0 < d) (hx : x < 2 ^ 32) (hR : R < d) :
    (2 ^ 32 * R + x) / d < 2 ^ 32 := by
  rw [Nat.div_lt_iff_lt_mul hd]
  nlinarith

theorem dsRun_props (a : List Nat) (d : Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hd : 0 < d) :
    ∀ j, j ≤ a.length →
      (dsRun a d j).2 < d ∧ (dsRun a d j).1.length = j ∧ (∀ x ∈ (dsRun a d j).1, x < 2 ^ 32) ∧
      lv (dsRun a d j).1 * d + (dsRun a d j).2 = lv (a.drop (a.length - j)) := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [dsRun, lv, hd]
  | succ j ih =>
      intro hj
      obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
      have hk : a.length - 1 - j < a.length := by omega
      have hx : ziAddTerm a (a.length - 1 - j) = a[a.length - 1 - j]'hk := by
        unfold ziAddTerm; rw [dif_pos hk]
      have hxlt : a[a.length - 1 - j]'hk < 2 ^ 32 := ha _ (List.getElem_mem hk)
      simp only [dsRun, dsStep, hx]
      refine ⟨Nat.mod_lt _ hd, by simp [h2], ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact dsStep_lt d _ _ hd hxlt h1
        · exact h3 y hy
      · have hdrop : a.drop (a.length - (j + 1)) =
            a[a.length - 1 - j]'hk :: a.drop (a.length - j) := by
          rw [show a.length - (j + 1) = a.length - 1 - j by omega,
            List.drop_eq_getElem_cons hk]
          congr 2; omega
        rw [hdrop]
        simp only [lv]
        rw [← h4]
        have := Nat.div_add_mod (2 ^ 32 * (dsRun a d j).2 + a[a.length - 1 - j]'hk) d
        nlinarith [this]

theorem dsRun_final (a : List Nat) (d : Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hd : 0 < d) :
    lv (dsRun a d a.length).1 = lv a / d ∧ (dsRun a d a.length).2 = lv a % d := by
  obtain ⟨h1, -, -, h4⟩ := dsRun_props a d ha hd a.length le_rfl
  simp only [Nat.sub_self, List.drop_zero] at h4
  have hq : lv a / d = lv (dsRun a d a.length).1 ∧ lv a % d = (dsRun a d a.length).2 :=
    Nat.div_mod_unique hd |>.mpr ⟨by linarith, h1⟩
  exact ⟨hq.1.symm, hq.2.symm⟩

end Tess.C

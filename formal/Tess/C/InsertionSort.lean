/-
  Value-level model of the insertion sort of constraint edges in the V2 certificate writer
  (`lib/tess/src/certificate.c`): the inner `while` shifts every element `> value` to the right and
  `insRev` is that loop on the reversed prefix (last element first). For a strict weak order `gt`
  (asymmetric, with transitive complement) `insRev` preserves sortedness and permutes the input
  (`insRev_sorted`, `insRev_perm`), hence the whole sort yields a sorted permutation (`sortRev_spec`).
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Pairwise

namespace Tess.C

variable {α : Type} (gt : α → α → Prop) [DecidableRel gt]

/-- The inner loop on the reversed sorted prefix. -/
def insRev (v : α) : List α → List α
  | [] => [v]
  | x :: xs => if gt x v then x :: insRev v xs else v :: x :: xs

/-- Sortedness of a reversed prefix: later (in `r`) elements are `≤` earlier ones. -/
def SortedRev (r : List α) : Prop := r.Pairwise (fun a b => ¬ gt b a)

theorem insRev_perm (v : α) (r : List α) : (insRev gt v r).Perm (v :: r) := by
  induction r with
  | nil => simp [insRev]
  | cons x xs ih =>
      unfold insRev
      split_ifs
      · exact ((List.Perm.cons x ih).trans (List.Perm.swap v x xs)).symm.symm.trans
          (List.Perm.refl _) |>.trans (List.Perm.refl _)
      · exact List.Perm.refl _

theorem insRev_sorted (hasym : ∀ a b, gt a b → ¬ gt b a)
    (htrans : ∀ a b c, ¬ gt a b → ¬ gt b c → ¬ gt a c) :
    ∀ (v : α) (r : List α), SortedRev gt r → SortedRev gt (insRev gt v r) := by
  intro v r
  induction r with
  | nil => intro _; simp [insRev, SortedRev]
  | cons x xs ih =>
      intro h
      unfold SortedRev at h
      obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp h
      unfold insRev
      split_ifs with hg
      · unfold SortedRev
        refine List.pairwise_cons.mpr ⟨?_, ih hxs⟩
        intro y hy
        have hperm := (insRev_perm gt v xs).mem_iff.mp hy
        rcases List.mem_cons.mp hperm with rfl | hy'
        · exact hasym _ _ hg
        · exact hx y hy'
      · unfold SortedRev
        refine List.pairwise_cons.mpr ⟨?_, h⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hg
        · exact htrans _ _ _ (hx y hy') hg

/-- The whole sort: insert each element in turn into the (reversed) sorted prefix. -/
def sortRev (l : List α) : List α := l.foldl (fun r v => insRev gt v r) []

theorem sortRev_spec (hasym : ∀ a b, gt a b → ¬ gt b a)
    (htrans : ∀ a b c, ¬ gt a b → ¬ gt b c → ¬ gt a c) (l : List α) :
    SortedRev gt (sortRev gt l) ∧ (sortRev gt l).Perm l := by
  suffices h : ∀ (l r : List α), SortedRev gt r →
      SortedRev gt (l.foldl (fun r v => insRev gt v r) r) ∧
      (l.foldl (fun r v => insRev gt v r) r).Perm (r ++ l) by
    simpa [sortRev] using h l [] (by simp [SortedRev])
  intro l
  induction l with
  | nil => intro r hr; exact ⟨hr, by simp⟩
  | cons v l ih =>
      intro r hr
      simp only [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (insRev gt v r) (insRev_sorted gt hasym htrans v r hr)
      refine ⟨h1, h2.trans ?_⟩
      have := (insRev_perm gt v r)
      exact (List.Perm.append_right l this).trans (List.perm_middle.symm)

end Tess.C

import TobjMtlx.Model

/-!
# Soundness and completeness of `check`

`check m = true ↔ WellFormed m ∧ <the remaining decidable side conditions>`; the graph part
reuses `MtlxSpec.discoverGraphRanking_iff_acyclic` from the MaterialX formalization.
-/
namespace TobjMtlx
open MtlxSpec

theorem lower_names (m : Mat) (h : m.surface.length = 1) :
    (lower m).map GNode.name = m.names := by
  obtain ⟨s, hs⟩ : ∃ s, m.surface = [s] := by
    match hm : m.surface, h with
    | [s], _ => exact ⟨s, rfl⟩
  simp [lower, Mat.names, Mat.surfName, hs, Function.comp_def]

theorem lower_unique (m : Mat) (h : m.surface.length = 1) (hn : m.names.Nodup) :
    UniqueNodeDefinitions (lower m) :=
  uniqueNodeDefinitions_of_nodup_names _ (by rw [lower_names m h]; exact hn)

/-- **Soundness**: an accepted material is well-formed; in particular its node graph is bound
and acyclic, so by `MtlxSpec` it has a dependency-first evaluation order. -/
theorem check_sound (m : Mat) (h : check m = true) : WellFormed m := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.isEmpty_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨herr, hsurf⟩, _⟩, _⟩, hnv⟩, hnu⟩, _⟩, _⟩, hin⟩, hinu⟩, hc⟩, hcu⟩, hcs⟩, hcsu⟩, hg⟩ := h
  have hu := lower_unique m hsurf hnu
  have hga := (discoverGraphRanking_iff_acyclic (lower m) noIface hu).mp hg
  exact ⟨herr, hsurf, hnv, hnu, hin, hinu, hc, hcu, hcs, hcsu, hga.1, hga.2⟩

/-- **Completeness for the graph part**: a material meeting every local condition is rejected
only if its graph has a dangling edge or a cycle. -/
theorem check_graph_complete (m : Mat) (hsurf : m.surface.length = 1) (hnu : m.names.Nodup)
    (hb : GraphSourcesBound (lower m) noIface) (ha : ∀ n, ¬ GraphUpstream (lower m) n n) :
    (discoverGraphRanking (lower m) noIface).isSome = true :=
  (discoverGraphRanking_iff_acyclic (lower m) noIface (lower_unique m hsurf hnu)).mpr ⟨hb, ha⟩

/-- Well-formed materials have an executable dependency-first node order. -/
theorem wellFormed_order (m : Mat) (h : WellFormed m) :
    (discoverGraphOrder (lower m) noIface).isSome = true :=
  discoverGraphOrder_complete_acyclic (lower m) noIface
    (lower_unique m h.oneSurface h.namesUnique) h.bound h.acyclic

end TobjMtlx

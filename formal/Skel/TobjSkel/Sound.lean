import TobjSkel.Model

/-!
# Soundness of the skeleton model

`Valid s`: joint names are valid identifiers and distinct; every parent index is
smaller than the joint's own index (so the hierarchy is a forest, parents
declared first); bind and rest transforms are 16 decimals.

`parseLines_valid`: whatever the lines, the model is `Valid`.
`check_sound`: an accepted model also satisfies the whole-file rules (a joint
without bind matrix needs `skel_lib`; every `vw` joint id names a joint).
-/
namespace TobjSkel
open TobjSubd

structure Valid (s : Skel) : Prop where
  names : ∀ j ∈ s.joints, validName j.name = true
  nodup : (s.joints.map (·.name)).Nodup
  parent : ∀ (i : Nat) (h : i < s.joints.length) (p : Nat), s.joints[i].parent = some p → p < i
  bind : ∀ j ∈ s.joints, ∀ m, j.bind = some m → isMatrix m = true
  rest : ∀ j ∈ s.joints, ∀ m, j.rest = some m → isMatrix m = true

theorem Valid.err {s : Skel} (h : Valid s) : Valid s.err := by
  cases h; constructor <;> assumption

theorem valid_empty : Valid ({} : Skel) := by constructor <;> simp

theorem findJoint_lt {js : List Joint} {n : S} {i : Nat} (h : findJoint js n = some i) :
    i < js.length := by
  unfold findJoint at h
  exact (List.findIdx?_eq_some_iff_getElem.mp h).1

theorem findJoint_none {js : List Joint} {n : S} (h : findJoint js n = none) :
    n ∉ js.map (·.name) := by
  unfold findJoint at h
  rw [List.findIdx?_eq_none_iff] at h
  intro hm
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  simpa using h j hj

theorem findJoint_get {js : List Joint} {n : S} {i : Nat} (h : findJoint js n = some i) :
    ∃ hi : i < js.length, js[i].name = n := by
  unfold findJoint at h
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hi, by simpa using hp⟩

theorem valid_addJoint {s : Skel} (h : Valid s) (j : Joint) (hn : validName j.name = true)
    (hd : findJoint s.joints j.name = none) (hp : ∀ q, j.parent = some q → q < s.joints.length)
    (hb : ∀ m, j.bind = some m → isMatrix m = true) (hr : j.rest = none) :
    Valid (s.addJoint j) := by
  unfold Skel.addJoint
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h.names x hx
    · exact hn
  · rw [List.map_append, List.nodup_append]
    refine ⟨h.nodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    intro hab; subst hab
    exact findJoint_none hd ha
  · intro i hi q hq
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < s.joints.length
    · rw [List.getElem_append_left hlt] at hq
      exact h.parent i hlt q hq
    · have e : i = s.joints.length := by omega
      subst e
      rw [List.getElem_append_right (by omega)] at hq
      simp only [Nat.sub_self, List.getElem_cons_zero] at hq
      exact hp q hq
  · intro x hx m hm
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h.bind x hx m hm
    · exact hb m hm
  · intro x hx m hm
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h.rest x hx m hm
    · rw [hr] at hm; simp at hm

theorem parentOf_lt {js : List Joint} {par : S} {p : Option Nat} (h : parentOf? js par = some p) :
    ∀ q, p = some q → q < js.length := by
  intro q hq
  subst hq
  unfold parentOf? at h
  split at h
  · simp at h
  · simp only [Option.map_eq_some_iff, Option.some.injEq] at h
    obtain ⟨k, hk, rfl⟩ := h
    exact findJoint_lt hk

theorem valid_stepJoint {s : Skel} (h : Valid s) (args : List S) : Valid (stepJoint s args) := by
  unfold stepJoint
  split
  · rename_i name par m
    split
    · exact h.err
    rename_i hlen
    split
    · exact h.err
    rename_i hname
    split
    · exact h.err
    rename_i hdup
    split
    · exact h.err
    rename_i p hpar
    split
    · exact h.err
    rename_i hm
    refine valid_addJoint h _ (by simpa using hname) (by simpa using hdup) (parentOf_lt hpar) ?_ rfl
    intro mm hmm
    unfold bindOf at hmm
    split at hmm
    · simp at hmm
    · rename_i hne
      simp only [Option.some.injEq] at hmm
      rw [← hmm]
      have h16 : m.length = 16 := by
        simp at hlen
        exact hlen (by simpa using hne)
      unfold isMatrix
      simp only [h16, beq_self_eq_true, Bool.true_and]
      simpa [h16] using hm
  · exact h.err

theorem valid_stepRest {s : Skel} (h : Valid s) (args : List S) : Valid (stepRest s args) := by
  unfold stepRest
  split
  · rename_i name m
    split
    · exact h.err
    rename_i hlen
    split
    · exact h.err
    rename_i i hi
    split
    · exact h.err
    rename_i j hj
    split
    · exact h.err
    split
    · exact h.err
    rename_i hdec
    have hil := findJoint_lt hi
    have hj' : s.joints[i] = j := by
      rw [List.getElem?_eq_getElem hil] at hj; simpa using hj
    unfold setAt
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact h.names x hx
      · simpa [← hj'] using h.names _ (List.getElem_mem hil)
    · have : (s.joints.set i { j with rest := some m }).map (·.name) = s.joints.map (·.name) := by
        rw [List.map_set]
        have e : j.name = (s.joints.map (·.name))[i]'(by simpa using hil) := by simp [← hj']
        rw [e, List.set_getElem_self]
      rw [this]; exact h.nodup
    · intro k hk q hq
      simp only [List.length_set] at hk
      rw [List.getElem_set] at hq
      split at hq
      · rename_i e; subst e
        exact h.parent i hk q (by rw [hj']; simpa using hq)
      · exact h.parent k hk q hq
    · intro x hx mm hmm
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact h.bind x hx mm hmm
      · exact h.bind _ (List.getElem_mem hil) mm (by rw [hj']; simpa using hmm)
    · intro x hx mm hmm
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact h.rest x hx mm hmm
      · simp only [Option.some.injEq] at hmm
        subst hmm
        unfold isMatrix
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hdec
        simp [hlen, hdec]
  · exact h.err

theorem valid_of_joints {s t : Skel} (h : Valid s) (e : t.joints = s.joints) : Valid t := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨e ▸ h1, e ▸ h2, e ▸ h3, e ▸ h4, e ▸ h5⟩

theorem stepSlot_joints (s : Skel) (lib : Bool) (args : List S) :
    (stepSlot s lib args).joints = s.joints := by
  cases lib <;> simp only [stepSlot, Bool.false_eq_true, ite_false, ite_true] <;>
    split <;> (try split) <;> rfl

theorem valid_stepSlot {s : Skel} (h : Valid s) (lib : Bool) (args : List S) :
    Valid (stepSlot s lib args) := valid_of_joints h (stepSlot_joints s lib args)

theorem valid_step {s : Skel} (h : Valid s) (kw : S) (args : List S) : Valid (step s kw args) := by
  unfold step
  split
  · exact valid_stepJoint h args
  split
  · exact valid_stepRest h args
  · exact valid_stepSlot h _ args

theorem valid_lineStep {s : Skel} (h : Valid s) (l : S) : Valid (lineStep s l) := by
  unfold lineStep
  split
  · split
    · exact valid_step (by cases h; constructor <;> assumption) _ _
    · exact h
  · exact h

theorem valid_finish {s : Skel} (h : Valid s) (maxId : Int) : Valid (finish maxId s) := by
  unfold finish
  split
  · exact h
  · dsimp only
    split
    · split <;> first | exact h.err.err | exact h.err
    · split <;> first | exact h.err | exact h

theorem parseLines_valid (lines : List S) (maxId : Int) : Valid (parseLines lines maxId) := by
  unfold parseLines
  apply valid_finish
  suffices ∀ s, Valid s → Valid (lines.foldl lineStep s) from this _ valid_empty
  intro s hs
  induction lines generalizing s with
  | nil => exact hs
  | cons l r ih => exact ih _ (valid_lineStep hs l)

/-- Whole-file rules of an accepted skeleton. -/
structure FileRules (maxId : Int) (s : Skel) : Prop where
  lib : (∃ j ∈ s.joints, j.bind = none) → s.lib.isSome
  ids : 0 ≤ maxId → maxId < s.joints.length

theorem finish_ok {s : Skel} {maxId : Int} (h : ok (finish maxId s) = true) :
    finish maxId s = s ∧ FileRules maxId s := by
  unfold ok finish at *
  by_cases he : s.ext = true
  · simp only [he, Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
    by_cases h1 : (s.joints.any (·.bind.isNone) && s.lib.isNone) = true
    · exfalso
      rw [if_pos h1] at h
      split at h <;> simp [Skel.err] at h
    · rw [if_neg h1] at h ⊢
      by_cases h2 : (decide (maxId ≥ 0) && decide (maxId ≥ s.joints.length)) = true
      · exfalso; rw [if_pos h2] at h; simp [Skel.err] at h
      · rw [if_neg h2]
        refine ⟨rfl, ?_, ?_⟩
        · intro ⟨j, hj, hb⟩
          simp only [Bool.and_eq_true, List.any_eq_true, Option.isNone_iff_eq_none,
            not_and] at h1
          exact Option.isSome_iff_ne_none.mpr (h1 ⟨j, hj, hb⟩)
        · intro h0
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Int.not_le] at h2
          exact h2 h0
  · simp [he] at h

/-- An accepted skeleton satisfies every rule of `skel-obj.md`. -/
theorem check_sound (lines : List S) (maxId : Int) (h : ok (parseLines lines maxId) = true) :
    Valid (parseLines lines maxId) ∧ FileRules maxId (parseLines lines maxId) := by
  refine ⟨parseLines_valid lines maxId, ?_⟩
  unfold parseLines at h ⊢
  have := finish_ok h
  rw [this.1]
  exact this.2

end TobjSkel

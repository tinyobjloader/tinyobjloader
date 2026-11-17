import TobjSubd.Model

/-!
# Soundness of the subdivision-tag model

`Valid t s` collects the rules of `subd-obj.md` that the model must satisfy for
the mesh topology `t`:

* each crease is a pair `a < b` that is an edge of a face, listed once;
* each corner is a vertex of a face, listed once;
* each hole is a face number, listed once;
* every sharpness is non-negative (does not start with `-`);
* scalar options are in range.

`parseLines_valid`: the model built from *any* lines is `Valid` (rule violations
only set `bad`). `check_sound`: an accepted model additionally satisfies the
whole-mesh rules (smooth triangles only with catmark, loop only on triangles).
-/
namespace TobjSubd

def NonNeg (v : S) : Prop := v.head? ≠ some '-'

structure Valid (t : Topo) (s : Subd) : Prop where
  crease_edge : ∀ c ∈ s.creases, c.1.1 < c.1.2 ∧ t.hasEdge c.1.1 c.1.2 = true
  crease_nodup : (s.creases.map (·.1)).Nodup
  crease_sharp : ∀ c ∈ s.creases, NonNeg c.2
  corner_vert : ∀ c ∈ s.corners, t.hasVert c.1 = true
  corner_nodup : (s.corners.map (·.1)).Nodup
  corner_sharp : ∀ c ∈ s.corners, NonNeg c.2
  hole_face : ∀ h ∈ s.holes, h < t.numFaces
  hole_nodup : s.holes.Nodup
  scheme_range : ∀ x, s.scheme = some x → x ≤ 2
  ib_range : ∀ x, s.ib = some x → x ≤ 2
  fvar_range : ∀ x, s.fvar = some x → x ≤ 5
  cm_range : ∀ x, s.cm = some x → x ≤ 1
  st_range : ∀ x, s.st = some x → x ≤ 1

theorem sharp_nonneg (v : S) : NonNeg (sharp v) := by
  unfold sharp NonNeg
  split
  · simp
  · rename_i h; simpa using h

/-! ## `upsert` -/

theorem mem_upsert {κ : Type} [BEq κ] [LawfulBEq κ] (k : κ) (v : S) :
    ∀ (l : List (κ × S)) (p : κ × S), p ∈ upsert k v l → p = (k, v) ∨ p ∈ l
  | [], p, h => by simp [upsert] at h; exact Or.inl h
  | (k', v') :: r, p, h => by
    simp only [upsert] at h
    split at h
    · rename_i hk
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (by simp [h])
      · rcases mem_upsert k v r p h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem keys_upsert {κ : Type} [BEq κ] [LawfulBEq κ] (k : κ) (v : S) :
    ∀ (l : List (κ × S)), (upsert k v l).map (·.1) =
      if l.map (·.1) |>.contains k then l.map (·.1) else l.map (·.1) ++ [k]
  | [] => by simp [upsert]
  | (k', v') :: r => by
    simp only [upsert]
    by_cases hk : k' = k
    · subst hk; simp
    · have hb : (k' == k) = false := by simpa using hk
      have hc : ((k' :: r.map (·.1)).contains k) = (r.map (·.1)).contains k := by
        simp [Ne.symm hk]
      simp only [hb, Bool.false_eq_true, ite_false, List.map_cons]
      rw [keys_upsert k v r, hc]
      split <;> simp

theorem nodup_keys_upsert {κ : Type} [BEq κ] [LawfulBEq κ] (k : κ) (v : S)
    (l : List (κ × S)) (h : (l.map (·.1)).Nodup) : ((upsert k v l).map (·.1)).Nodup := by
  rw [keys_upsert]
  split
  · exact h
  · rename_i hc
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    intro hab; subst hab
    exact hc (by simpa using ha)

/-! ## Primitive updates preserve `Valid` -/

variable {t : Topo}

theorem Valid.err {s : Subd} (h : Valid t s) : Valid t s.err := by
  cases h; constructor <;> assumption

theorem Valid.setCrease {s : Subd} (h : Valid t s) (a b : Nat) (v : S)
    (hab : a < b) (he : t.hasEdge a b = true) : Valid t (s.setCrease a b v) := by
  refine { h with crease_edge := ?_, crease_nodup := ?_, crease_sharp := ?_ }
  · intro c hc
    rcases mem_upsert _ _ _ _ hc with hc | hc
    · subst hc; exact ⟨hab, he⟩
    · exact h.crease_edge c hc
  · exact nodup_keys_upsert _ _ _ h.crease_nodup
  · intro c hc
    rcases mem_upsert _ _ _ _ hc with hc | hc
    · subst hc; exact sharp_nonneg v
    · exact h.crease_sharp c hc

theorem Valid.setCorner {s : Subd} (h : Valid t s) (x : Nat) (v : S)
    (hv : t.hasVert x = true) : Valid t (s.setCorner x v) := by
  refine { h with corner_vert := ?_, corner_nodup := ?_, corner_sharp := ?_ }
  · intro c hc
    rcases mem_upsert _ _ _ _ hc with hc | hc
    · subst hc; exact hv
    · exact h.corner_vert c hc
  · exact nodup_keys_upsert _ _ _ h.corner_nodup
  · intro c hc
    rcases mem_upsert _ _ _ _ hc with hc | hc
    · subst hc; exact sharp_nonneg v
    · exact h.corner_sharp c hc

theorem Valid.addHole {s : Subd} (h : Valid t s) (f : Nat) (hf : f < t.numFaces) :
    Valid t (s.addHole f) := by
  unfold Subd.addHole
  split
  · exact h
  · rename_i hc
    refine { h with hole_face := ?_, hole_nodup := ?_ }
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact h.hole_face x hx
      · subst hx; exact hf
    · rw [List.nodup_append]
      refine ⟨h.hole_nodup, by simp, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      intro hab; subst hab
      exact hc (by simpa using ha)

/-! ## Tag steps -/

theorem valid_stepCrease {s : Subd} (h : Valid t s) (ps : List (Int × Int)) (vals : List S)
    (shared : Bool) : Valid t (stepCrease t s ps vals shared) := by
  unfold TobjSubd.stepCrease
  generalize ps.zipIdx = l
  induction l generalizing s with
  | nil => exact h
  | cons p r ih =>
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨⟨x, y⟩, k⟩ := p
    dsimp only
    split
    · exact h.err
    · rename_i hxy
      split
      · exact h.err
      · rename_i he
        simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or] at hxy
        obtain ⟨⟨hx, hy⟩, hne⟩ := hxy
        refine h.setCrease _ _ _ ?_ (by simpa using he)
        have : min x y < max x y := by omega
        omega

theorem valid_stepCorner {s : Subd} (h : Valid t s) (vs : List Int) (vals : List S)
    (shared : Bool) : Valid t (stepCorner t s vs vals shared) := by
  unfold TobjSubd.stepCorner
  generalize vs.zipIdx = l
  induction l generalizing s with
  | nil => exact h
  | cons p r ih =>
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨x, k⟩ := p
    dsimp only
    split
    · exact h.err
    · rename_i hx
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
        not_or, Bool.not_eq_false] at hx
      exact h.setCorner _ _ (by simpa using hx.2)

theorem valid_stepHole {s : Subd} (h : Valid t s) (vs : List Int) :
    Valid t (stepHole t s vs) := by
  unfold TobjSubd.stepHole
  induction vs generalizing s with
  | nil => exact h
  | cons x r ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h.err
    · rename_i hx
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hx
      exact h.addHole _ hx.2

theorem lookup_lt (v : S) (names : List String) (x : Nat) (h : lookup v names = some x) :
    x < names.length := by
  unfold lookup at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨n, i⟩, hf, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hf
  have := (List.mem_zipIdx hm).2.1
  simpa using this

theorem Valid.unknown {s : Subd} (h : Valid t s) (u : List S) :
    Valid t { s with unknown := u } := by
  cases h; constructor <;> assumption

theorem valid_stepBoundary {s : Subd} (h : Valid t s) (fv : Bool) (x : Int) :
    Valid t (stepBoundary s fv x) := by
  unfold stepBoundary setScalar
  by_cases hx : (x < 0 || x > (if fv then 5 else 2)) = true
  · simp only [hx, ite_true]; exact h.err
  · simp only [hx]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at hx
    cases fv <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hx ⊢ <;> split
    all_goals first
      | exact h.err
      | exact { h with ib_range := fun y hy => by simp at hy; omega }
      | exact { h with fvar_range := fun y hy => by simp at hy; omega }

theorem valid_stepName {s : Subd} (h : Valid t s) (which : Nat) (v : S) :
    Valid t (stepName s which v) := by
  unfold stepName setScalar
  split
  all_goals
    split
    · exact h.err
    · rename_i x hx
      have := lookup_lt _ _ _ hx
      split
      · exact h.err
      · first
          | exact { h with scheme_range := fun y hy => by simp at hy this; omega }
          | exact { h with cm_range := fun y hy => by simp at hy this; omega }
          | exact { h with st_range := fun y hy => by simp at hy this; omega }

theorem valid_stepTag {s : Subd} (h : Valid t s) (args : List S) (n : String)
    (ni nf ns : Nat) (ints : List Int) (flts strs : List S) :
    Valid t (stepTag t s args n ni nf ns ints flts strs) := by
  unfold stepTag
  repeat' split
  all_goals first
    | exact h.err
    | exact h
    | exact valid_stepCrease h _ _ _
    | exact valid_stepCorner h _ _ _
    | exact valid_stepHole h _
    | exact valid_stepBoundary h _ _
    | exact valid_stepName h _ _
    | exact h.unknown _

theorem valid_step {s : Subd} (h : Valid t s) (args : List S) : Valid t (step t s args) := by
  unfold TobjSubd.step
  match args with
  | name :: cnt :: rest =>
    dsimp only
    cases parseCounts? cnt with
    | none => exact h.err
    | some c =>
      obtain ⟨ni, nf, ns⟩ := c
      dsimp only
      by_cases hl : (rest.length != ni + nf + ns) = true
      · simp only [hl, ite_true]; exact h.err
      · simp only [hl]
        cases (rest.take ni).mapM parseInt? with
        | none => exact h.err
        | some ints =>
          dsimp only
          by_cases hd : (!((rest.drop ni).take nf).all isDecimal) = true
          · simp only [hd, ite_true]; exact h.err
          · simp only [hd]; exact valid_stepTag h _ _ _ _ _ _ _ _
  | [] => exact h.err
  | [_] => exact h.err

theorem valid_empty : Valid t ({} : Subd) := by
  constructor <;> simp

theorem Valid.finish {s : Subd} (h : Valid t s) : Valid t (finish t s) := by
  unfold TobjSubd.finish
  have h1 : Valid t (if (s.st.isSome && s.scheme.isSome && s.scheme != some 0) = true
      then s.err else s) := by split; exact h.err; exact h
  dsimp only
  generalize (if (s.st.isSome && s.scheme.isSome && s.scheme != some 0) = true
      then s.err else s) = s' at h1
  split; exact h1.err; exact h1

/-- Whatever the lines, the model satisfies the per-tag rules. -/
theorem parseLines_valid (t : Topo) (lines : List S) : Valid t (parseLines t lines) := by
  unfold parseLines
  apply Valid.finish
  suffices ∀ s, Valid t s → Valid t (lines.foldl (fun s l =>
      match lineTokens (dropCR l) with
      | ['t'] :: args => step t s args
      | _ => s) s) from this _ valid_empty
  intro s hs
  induction lines generalizing s with
  | nil => exact hs
  | cons l r ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact valid_step hs _
    · exact hs

/-- The whole-mesh rules of an accepted model. -/
structure MeshRules (t : Topo) (s : Subd) : Prop where
  smooth_catmark : s.st.isSome → s.scheme = none ∨ s.scheme = some 0
  loop_tris : s.scheme = some 1 → t.allTris = true

theorem finish_ok {s : Subd} (h : ok (finish t s) = true) :
    finish t s = s ∧ MeshRules t s := by
  unfold TobjSubd.finish ok at *
  dsimp only at *
  by_cases h1 : (s.st.isSome && s.scheme.isSome && s.scheme != some 0) = true
  · exfalso
    rw [if_pos h1] at h
    split at h <;> simp [Subd.err] at h
  · rw [if_neg h1] at h ⊢
    by_cases h2 : (s.scheme == some 1 && !t.allTris) = true
    · exfalso; rw [if_pos h2] at h; simp [Subd.err] at h
    · rw [if_neg h2]
      refine ⟨rfl, ?_, ?_⟩
      · intro hst
        cases hs : s.scheme with
        | none => exact Or.inl rfl
        | some x =>
          right
          rw [hs] at h1
          simp [hst] at h1
          simp [h1]
      · intro hs
        rw [hs] at h2
        simpa using h2

/-- An accepted model satisfies every rule of `subd-obj.md`. -/
theorem check_sound (t : Topo) (lines : List S) (h : ok (parseLines t lines) = true) :
    Valid t (parseLines t lines) ∧ MeshRules t (parseLines t lines) := by
  refine ⟨parseLines_valid t lines, ?_⟩
  unfold parseLines at h ⊢
  have := (finish_ok h)
  rw [this.1]
  exact this.2

end TobjSubd

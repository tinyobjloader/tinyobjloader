import TobjSubd.Sound
import TobjSubd.Text

/-!
# The canonical round trip

`roundtrip`: for mesh lines without line-break characters, an accepted model
`s = parseLines t lines` is reproduced by parsing its canonical form:

    parseLines t (splitOn '\n' (print s)) = s

The proof replays the printed lines one by one: scalar tags, then creases,
corners, holes and unknown tags. Each kind of line has a lemma giving its
effect on the model; `Inv` collects what the original parse guarantees about
the stored values (decimal sharpness, unknown lines that re-parse as unknown
tags).
-/
namespace TobjSubd

variable {t : Topo}

/-! ## One line of a mesh -/

/-- The per-line function folded by `parseLines`. -/
def lineStep (t : Topo) (s : Subd) (l : S) : Subd :=
  match lineTokens (dropCR l) with
  | ['t'] :: args => step t s args
  | _ => s

theorem parseLines_eq (t : Topo) (lines : List S) :
    parseLines t lines = finish t (lines.foldl (lineStep t) {}) := rfl

theorem lineStep_t {s : Subd} (args : List S) (h : ∀ w ∈ args, GoodTok w) :
    lineStep t s (joinSp (['t'] :: args)) = step t s args := by
  have hg : ∀ w ∈ ['t'] :: args, GoodTok w := by
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨by simp, by decide⟩
    · exact h w hw
  unfold lineStep
  rw [dropCR_of_noCR _ (fun c hc => (joinSp_noBreak _ hg c hc).2),
    lineTokens_joinSp _ (by simp) hg]
  rfl

theorem lineStep_nil (s : Subd) : lineStep t s [] = s := rfl

theorem step_of_classify {s : Subd} {args : List S} {g : Tag} (h : classify args = some g) :
    step t s args = stepTag t s args g.name g.ni g.nf g.ns g.ints g.flts g.strs := by
  unfold step; rw [h]

/-! ## `classify` on printed lines -/

theorem mapM_parseInt?_nat (hs : List Nat) :
    (hs.map nat).mapM parseInt? = some (hs.map Int.ofNat) := by
  induction hs with
  | nil => rfl
  | cons h hs ih => simp [List.mapM_cons, parseInt?_nat, ih]

theorem classify_001 (n x : S) :
    classify [n, "0/0/1".toList, x] = some ⟨String.ofList n, 0, 0, 1, [], [], [x]⟩ := by
  have : parseCounts? "0/0/1".toList = some (0, 0, 1) := rfl
  unfold classify; dsimp only; rw [this]; simp

theorem classify_100 (n : S) (v : Nat) :
    classify [n, "1/0/0".toList, nat v] = some ⟨String.ofList n, 1, 0, 0, [(v : Int)], [], []⟩ := by
  have : parseCounts? "1/0/0".toList = some (1, 0, 0) := rfl
  unfold classify; dsimp only; rw [this]; simp [parseInt?_nat]

theorem classify_crease (a b : Nat) (v : S) (hv : isDecimal v = true) :
    classify ["crease".toList, "2/1/0".toList, nat a, nat b, v] =
      some ⟨"crease", 2, 1, 0, [(a : Int), b], [v], []⟩ := by
  have : parseCounts? "2/1/0".toList = some (2, 1, 0) := rfl
  unfold classify; dsimp only; rw [this]; simp [parseInt?_nat, hv]

theorem classify_corner (a : Nat) (v : S) (hv : isDecimal v = true) :
    classify ["corner".toList, "1/1/0".toList, nat a, v] =
      some ⟨"corner", 1, 1, 0, [(a : Int)], [v], []⟩ := by
  have : parseCounts? "1/1/0".toList = some (1, 1, 0) := rfl
  unfold classify; dsimp only; rw [this]; simp [parseInt?_nat, hv]

theorem classify_hole (hs : List Nat) (h : hs.length ≤ maxCount) :
    classify (["hole".toList, nat hs.length ++ "/0/0".toList] ++ hs.map nat) =
      some ⟨"hole", hs.length, 0, 0, hs.map Int.ofNat, [], []⟩ := by
  unfold classify
  simp only [List.cons_append, List.nil_append]
  rw [parseCounts?_hole _ h]
  dsimp only
  rw [List.take_of_length_le (by simp), mapM_parseInt?_nat]
  simp

theorem classify_flts {args : List S} {g : Tag} (h : classify args = some g) :
    ∀ v ∈ g.flts, isDecimal v = true := by
  unfold classify at h
  split at h
  · rename_i name cnt rest
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i hd
            simp only [Option.some.injEq] at h
            subst h
            simpa using hd
  · simp at h

/-! ## Invariants of an accepted parse -/

def isKnown (n : String) : Bool :=
  n == "crease" || n == "corner" || n == "hole" || n == "interpolateboundary" ||
  n == "facevaryinginterpolateboundary" || n == "facevaryingpropagatecorners" ||
  n == "scheme" || n == "creasemethod" || n == "smoothtriangles"

/-- An unknown-tag line that re-parses as the same unknown tag. -/
def UnknownLine (u : S) : Prop :=
  ∃ args, u = joinSp (['t'] :: args) ∧ (∀ w ∈ args, GoodTok w) ∧
    ∃ g, classify args = some g ∧ isKnown g.name = false

structure Inv (t : Topo) (s : Subd) : Prop where
  valid : Valid t s
  cdec : ∀ c ∈ s.creases, isDecimal c.2 = true
  kdec : ∀ c ∈ s.corners, isDecimal c.2 = true
  unk : ∀ u ∈ s.unknown, UnknownLine u

theorem Inv.err {s : Subd} (h : Inv t s) : Inv t s.err := ⟨h.valid.err, h.cdec, h.kdec, h.unk⟩

theorem inv_empty : Inv t ({} : Subd) := ⟨valid_empty, by simp, by simp, by simp⟩

/-- The non-`Valid` parts of `Inv`. -/
structure Inv' (s : Subd) : Prop where
  cdec : ∀ c ∈ s.creases, isDecimal c.2 = true
  kdec : ∀ c ∈ s.corners, isDecimal c.2 = true
  unk : ∀ u ∈ s.unknown, UnknownLine u

theorem inv'_stepCrease {s : Subd} (h : Inv' s) (ps : List (Int × Int)) (vals : List S)
    (hv : ∀ v ∈ vals, isDecimal v = true) (shared : Bool) :
    Inv' (stepCrease t s ps vals shared) := by
  unfold stepCrease
  generalize ps.zipIdx = l
  induction l generalizing s with
  | nil => exact h
  | cons p r ih =>
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨⟨x, y⟩, k⟩ := p
    dsimp only
    split
    · exact ⟨h.cdec, h.kdec, h.unk⟩
    · split
      · exact ⟨h.cdec, h.kdec, h.unk⟩
      · refine ⟨?_, h.kdec, h.unk⟩
        intro c hc
        rcases mem_upsert _ _ _ _ hc with hc | hc
        · subst hc
          apply sharp_decimal
          rw [List.getD_eq_getElem?_getD]
          cases hk : vals[if shared = true then 0 else k]? with
          | none => decide
          | some w => exact hv w (List.mem_of_getElem? hk)
        · exact h.cdec c hc

theorem inv'_stepCorner {s : Subd} (h : Inv' s) (vs : List Int) (vals : List S)
    (hv : ∀ v ∈ vals, isDecimal v = true) (shared : Bool) :
    Inv' (stepCorner t s vs vals shared) := by
  unfold stepCorner
  generalize vs.zipIdx = l
  induction l generalizing s with
  | nil => exact h
  | cons p r ih =>
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨x, k⟩ := p
    dsimp only
    split
    · exact ⟨h.cdec, h.kdec, h.unk⟩
    · refine ⟨h.cdec, ?_, h.unk⟩
      intro c hc
      rcases mem_upsert _ _ _ _ hc with hc | hc
      · subst hc
        apply sharp_decimal
        rw [List.getD_eq_getElem?_getD]
        cases hk : vals[if shared = true then 0 else k]? with
        | none => decide
        | some w => exact hv w (List.mem_of_getElem? hk)
      · exact h.kdec c hc

theorem inv'_stepHole {s : Subd} (h : Inv' s) (vs : List Int) : Inv' (stepHole t s vs) := by
  unfold stepHole
  induction vs generalizing s with
  | nil => exact h
  | cons x r ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold holeStep
    split
    · exact ⟨h.cdec, h.kdec, h.unk⟩
    · unfold Subd.addHole; split <;> exact ⟨h.cdec, h.kdec, h.unk⟩

theorem inv'_stepBoundary {s : Subd} (h : Inv' s) (fv : Bool) (x : Int) :
    Inv' (stepBoundary s fv x) := by
  unfold stepBoundary setScalar
  repeat' split
  all_goals exact ⟨h.cdec, h.kdec, h.unk⟩

theorem inv'_stepName {s : Subd} (h : Inv' s) (which : Nat) (v : S) :
    Inv' (stepName s which v) := by
  unfold stepName setScalar
  repeat' split
  all_goals exact ⟨h.cdec, h.kdec, h.unk⟩

theorem inv'_step {s : Subd} (h : Inv' s) (args : List S) (hargs : ∀ w ∈ args, GoodTok w) :
    Inv' (step t s args) := by
  unfold step
  cases hc : classify args with
  | none => exact ⟨h.cdec, h.kdec, h.unk⟩
  | some g =>
    have hf := classify_flts hc
    dsimp only
    unfold stepTag
    repeat' split
    all_goals first
      | exact ⟨h.cdec, h.kdec, h.unk⟩
      | exact inv'_stepCrease h _ _ hf _
      | exact inv'_stepCorner h _ _ hf _
      | exact inv'_stepHole h _
      | exact inv'_stepBoundary h _ _
      | exact inv'_stepName h _ _
      | skip
    -- the unknown-tag branch
    refine ⟨h.cdec, h.kdec, ?_⟩
    intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact h.unk u hu
    · refine ⟨args, rfl, hargs, g, hc, ?_⟩
      simp_all [isKnown]

theorem inv_step {s : Subd} (h : Inv t s) (args : List S) (hargs : ∀ w ∈ args, GoodTok w) :
    Inv t (step t s args) :=
  have h' := inv'_step (t := t) ⟨h.cdec, h.kdec, h.unk⟩ args hargs
  ⟨valid_step h.valid args, h'.cdec, h'.kdec, h'.unk⟩

/-! ## Tokens of the input lines -/

theorem mem_splitBlank : ∀ {l : S} {w : S}, w ∈ splitBlank l → ∀ c ∈ w, isBlank c = false ∧ c ∈ l
  | [], w, hw, c, hc => by simp [splitBlank] at hw; subst hw; simp at hc
  | d :: l, w, hw, c, hc => by
    unfold splitBlank at hw
    split at hw
    · simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · simp at hc
      · have := mem_splitBlank hw c hc; exact ⟨this.1, List.mem_cons_of_mem _ this.2⟩
    · rename_i hb
      split at hw
      · rename_i heq
        simp only [List.mem_singleton] at hw; subst hw
        simp only [List.mem_singleton] at hc; subst hc
        exact ⟨by simpa using hb, by simp⟩
      · rename_i w' ws heq
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ⟨by simpa using hb, by simp⟩
          · have := mem_splitBlank (l := l) (w := w') (by rw [heq]; simp) c hc
            exact ⟨this.1, List.mem_cons_of_mem _ this.2⟩
        · have := mem_splitBlank (l := l) (w := w) (by rw [heq]; simp [hw]) c hc
          exact ⟨this.1, List.mem_cons_of_mem _ this.2⟩

theorem mem_dropCR {l : S} {c : Char} (h : c ∈ dropCR l) : c ∈ l := by
  unfold dropCR at h
  split at h
  · exact List.dropLast_subset _ h
  · exact h

theorem lineTokens_good (l : S) (hl : ∀ c ∈ l, c ≠ '\n' ∧ c ≠ '\r') :
    ∀ w ∈ lineTokens (dropCR l), GoodTok w := by
  intro w hw
  unfold lineTokens at hw
  rw [List.mem_filter] at hw
  refine ⟨by simpa [List.isEmpty_iff] using hw.2, fun c hc => ?_⟩
  have := mem_splitBlank hw.1 c hc
  exact ⟨this.1, hl c (mem_dropCR this.2)⟩

theorem inv_fold (t : Topo) (lines : List S) (hl : ∀ l ∈ lines, ∀ c ∈ l, c ≠ '\n' ∧ c ≠ '\r')
    (s : Subd) (hs : Inv t s) : Inv t (lines.foldl (lineStep t) s) := by
  induction lines generalizing s with
  | nil => exact hs
  | cons l r ih =>
    simp only [List.foldl_cons]
    apply ih (fun x hx => hl x (by simp [hx]))
    unfold lineStep
    split
    · rename_i args heq
      have hg := lineTokens_good l (hl l (by simp))
      rw [heq] at hg
      exact inv_step hs args (fun w hw => hg w (by simp [hw]))
    · exact hs

theorem inv_finish {s : Subd} (h : Inv t s) : Inv t (finish t s) := by
  unfold TobjSubd.finish
  dsimp only
  have h1 : Inv t (if (s.st.isSome && s.scheme.isSome && s.scheme != some 0) = true
      then s.err else s) := by split; exact h.err; exact h
  generalize (if (s.st.isSome && s.scheme.isSome && s.scheme != some 0) = true
      then s.err else s) = s' at h1
  split; exact h1.err; exact h1

/-! ## Re-parsing the printed lines -/

theorem good_lit (s : String) (h : (s.toList != []) = true)
    (h2 : s.toList.all (fun c => isBlank c == false && c != '\n' && c != '\r') = true) :
    GoodTok s.toList := by
  refine ⟨by simpa using h, fun c hc => ?_⟩
  have := List.all_eq_true.mp h2 c hc
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

macro "lit_good" : tactic => `(tactic| exact good_lit _ (by decide) (by decide))

/-- Lookup of a printed name in one of the three fixed name lists. -/
theorem lookup3 (i : Nat) (hi : i < 3) :
    lookup (["catmark", "loop", "bilinear"].getD i "").toList ["catmark", "loop", "bilinear"] = some i ∧
    GoodTok (["catmark", "loop", "bilinear"].getD i "").toList := by
  match i, hi with
  | 0, _ => exact ⟨rfl, by lit_good⟩
  | 1, _ => exact ⟨rfl, by lit_good⟩
  | 2, _ => exact ⟨rfl, by lit_good⟩

theorem lookup2a (i : Nat) (hi : i < 2) :
    lookup (["normal", "chaikin"].getD i "").toList ["normal", "chaikin"] = some i ∧
    GoodTok (["normal", "chaikin"].getD i "").toList := by
  match i, hi with
  | 0, _ => exact ⟨rfl, by lit_good⟩
  | 1, _ => exact ⟨rfl, by lit_good⟩

theorem lookup2b (i : Nat) (hi : i < 2) :
    lookup (["catmark", "smooth"].getD i "").toList ["catmark", "smooth"] = some i ∧
    GoodTok (["catmark", "smooth"].getD i "").toList := by
  match i, hi with
  | 0, _ => exact ⟨rfl, by lit_good⟩
  | 1, _ => exact ⟨rfl, by lit_good⟩

/-- Replaying a scalar line on a model whose slot is empty. -/
theorem fold_scalLine (s : Subd) (tag cnt : String) (v : Option S) (s' : Subd)
    (hgood : ∀ x, v = some x → ∀ w ∈ [tag.toList, cnt.toList, x], GoodTok w)
    (heff : ∀ x, v = some x → step t s [tag.toList, cnt.toList, x] = s')
    (hnone : v = none → s' = s) :
    (scalLine tag cnt v).foldl (lineStep t) s = s' := by
  unfold scalLine
  cases v with
  | none => exact (hnone rfl).symm
  | some x =>
    simp only [List.foldl_cons, List.foldl_nil]
    have ht : "t".toList = ['t'] := rfl
    rw [ht, lineStep_t _ (hgood x rfl), heff x rfl]

theorem str_ofList (s : String) : String.ofList s.toList = s := by simp

theorem good3 (a b : String) (x : S) (ha : GoodTok a.toList) (hb : GoodTok b.toList)
    (hx : GoodTok x) : ∀ w ∈ [a.toList, b.toList, x], GoodTok w := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> assumption

theorem eff_scheme (b : Subd) (hb : b.scheme = none) (o : Option Nat) (ho : ∀ x, o = some x → x ≤ 2) :
    (scalLine "scheme" "0/0/1" (nameOf ["catmark", "loop", "bilinear"] o)).foldl (lineStep t) b =
      { b with scheme := o } := by
  apply fold_scalLine
  · intro x hx
    cases o with
    | none => simp [nameOf] at hx
    | some i =>
      simp only [nameOf, Option.map_some, Option.some.injEq] at hx; subst hx
      exact good3 _ _ _ (by lit_good) (by lit_good) (lookup3 i (by have := ho i rfl; omega)).2
  · intro x hx
    cases o with
    | none => simp [nameOf] at hx
    | some i =>
      simp only [nameOf, Option.map_some, Option.some.injEq] at hx; subst hx
      have hl := (lookup3 i (by have := ho i rfl; omega)).1
      rw [List.getD_eq_getElem?_getD] at hl
      rw [step_of_classify (classify_001 _ _)]
      simp [stepTag, stepName, setScalar, hl, hb]
  · intro hv
    cases o with
    | some _ => simp [nameOf] at hv
    | none => cases b; simp_all

theorem eff_cm (b : Subd) (hb : b.cm = none) (o : Option Nat) (ho : ∀ x, o = some x → x ≤ 1) :
    (scalLine "creasemethod" "0/0/1" (nameOf ["normal", "chaikin"] o)).foldl (lineStep t) b =
      { b with cm := o } := by
  apply fold_scalLine
  · intro x hx
    cases o with
    | none => simp [nameOf] at hx
    | some i =>
      simp only [nameOf, Option.map_some, Option.some.injEq] at hx; subst hx
      exact good3 _ _ _ (by lit_good) (by lit_good) (lookup2a i (by have := ho i rfl; omega)).2
  · intro x hx
    cases o with
    | none => simp [nameOf] at hx
    | some i =>
      simp only [nameOf, Option.map_some, Option.some.injEq] at hx; subst hx
      have hl := (lookup2a i (by have := ho i rfl; omega)).1
      rw [List.getD_eq_getElem?_getD] at hl
      rw [step_of_classify (classify_001 _ _)]
      simp [stepTag, stepName, setScalar, hl, hb]
  · intro hv
    cases o with
    | some _ => simp [nameOf] at hv
    | none => cases b; simp_all

theorem eff_st (b : Subd) (hb : b.st = none) (o : Option Nat) (ho : ∀ x, o = some x → x ≤ 1) :
    (scalLine "smoothtriangles" "0/0/1" (nameOf ["catmark", "smooth"] o)).foldl (lineStep t) b =
      { b with st := o } := by
  apply fold_scalLine
  · intro x hx
    cases o with
    | none => simp [nameOf] at hx
    | some i =>
      simp only [nameOf, Option.map_some, Option.some.injEq] at hx; subst hx
      exact good3 _ _ _ (by lit_good) (by lit_good) (lookup2b i (by have := ho i rfl; omega)).2
  · intro x hx
    cases o with
    | none => simp [nameOf] at hx
    | some i =>
      simp only [nameOf, Option.map_some, Option.some.injEq] at hx; subst hx
      have hl := (lookup2b i (by have := ho i rfl; omega)).1
      rw [List.getD_eq_getElem?_getD] at hl
      rw [step_of_classify (classify_001 _ _)]
      simp [stepTag, stepName, setScalar, hl, hb]
  · intro hv
    cases o with
    | some _ => simp [nameOf] at hv
    | none => cases b; simp_all

theorem eff_ib (b : Subd) (hb : b.ib = none) (o : Option Nat) (ho : ∀ x, o = some x → x ≤ 2) :
    (scalLine "interpolateboundary" "1/0/0" (o.map nat)).foldl (lineStep t) b =
      { b with ib := o } := by
  apply fold_scalLine
  · intro x hx
    cases o with
    | none => simp at hx
    | some i =>
      simp only [Option.map_some, Option.some.injEq] at hx; subst hx
      exact good3 _ _ _ (by lit_good) (by lit_good) (nat_good i)
  · intro x hx
    cases o with
    | none => simp at hx
    | some i =>
      simp only [Option.map_some, Option.some.injEq] at hx; subst hx
      have := ho i rfl
      rw [step_of_classify (classify_100 _ _)]
      simp [stepTag, stepBoundary, setScalar, hb]
      omega
  · intro hv
    cases o with
    | some _ => simp [nameOf] at hv
    | none => cases b; simp_all

theorem eff_fvar (b : Subd) (hb : b.fvar = none) (o : Option Nat) (ho : ∀ x, o = some x → x ≤ 5) :
    (scalLine "facevaryinginterpolateboundary" "1/0/0" (o.map nat)).foldl (lineStep t) b =
      { b with fvar := o } := by
  apply fold_scalLine
  · intro x hx
    cases o with
    | none => simp at hx
    | some i =>
      simp only [Option.map_some, Option.some.injEq] at hx; subst hx
      exact good3 _ _ _ (by lit_good) (by lit_good) (nat_good i)
  · intro x hx
    cases o with
    | none => simp at hx
    | some i =>
      simp only [Option.map_some, Option.some.injEq] at hx; subst hx
      have := ho i rfl
      rw [step_of_classify (classify_100 _ _)]
      simp [stepTag, stepBoundary, setScalar, hb]
      omega
  · intro hv
    cases o with
    | some _ => simp [nameOf] at hv
    | none => cases b; simp_all

theorem scalars_fold (s : Subd) (h : Valid t s) :
    (scalarLines s).foldl (lineStep t) {} =
      { scheme := s.scheme, ib := s.ib, fvar := s.fvar, cm := s.cm, st := s.st } := by
  unfold scalarLines
  simp only [List.foldl_append]
  rw [eff_scheme _ rfl _ h.scheme_range, eff_ib _ rfl _ h.ib_range, eff_fvar _ rfl _ h.fvar_range,
    eff_cm _ rfl _ h.cm_range, eff_st _ rfl _ h.st_range]

/-! ## Creases, corners, holes, unknown tags -/

theorem upsert_absent {κ : Type} [BEq κ] [LawfulBEq κ] (k : κ) (v : S) :
    ∀ (l : List (κ × S)), k ∉ l.map (·.1) → upsert k v l = l ++ [(k, v)]
  | [], _ => rfl
  | (k', v') :: r, h => by
    have hn : ¬(k = k') ∧ k ∉ r.map (·.1) := by
      simpa only [List.map_cons, List.mem_cons, not_or] using h
    have hk : (k' == k) = false := beq_eq_false_iff_ne.mpr (fun e => hn.1 e.symm)
    simp only [upsert, hk, Bool.false_eq_true, ite_false, List.cons_append]
    rw [upsert_absent k v r hn.2]

theorem sharp_of_nonneg {v : S} (h : NonNeg v) : sharp v = v := by
  unfold sharp NonNeg at *
  have : (v.head? == some '-') = false := by simpa using h
  rw [this]; rfl

theorem good_all (ts : List S) (h : ∀ w ∈ ts, GoodTok w) (w : S) (hw : w ∈ ts) : GoodTok w := h w hw

theorem t_toList : "t".toList = ['t'] := rfl

theorem crease_args_good (a b : Nat) (v : S) (hv : isDecimal v = true) :
    ∀ w ∈ ["crease".toList, "2/1/0".toList, nat a, nat b, v], GoodTok w := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · lit_good
  · lit_good
  · exact nat_good a
  · exact nat_good b
  · exact decimal_good hv

theorem eff_crease (b : Subd) (a c : Nat) (v : S) (hac : a < c) (he : t.hasEdge a c = true)
    (hv : isDecimal v = true) (hn : NonNeg v) (hk : (a, c) ∉ b.creases.map (·.1)) :
    lineStep t b (creaseLine ((a, c), v)) = { b with creases := b.creases ++ [((a, c), v)] } := by
  unfold creaseLine
  simp only [t_toList]
  rw [lineStep_t _ (crease_args_good a c v hv), step_of_classify (classify_crease a c v hv)]
  have h1 : ¬((a : Int) < 0 ∨ (c : Int) < 0 ∨ (a : Int) = c) := by omega
  have h2 : (min (a : Int) c).toNat = a := by omega
  have h3 : (max (a : Int) c).toNat = c := by omega
  simp [stepTag, stepCrease, pairs, h2, h3, he, Subd.setCrease, sharp_of_nonneg hn,
    upsert_absent _ _ _ hk]
  intro hh; exact absurd hh (by omega)

theorem corner_args_good (a : Nat) (v : S) (hv : isDecimal v = true) :
    ∀ w ∈ ["corner".toList, "1/1/0".toList, nat a, v], GoodTok w := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · lit_good
  · lit_good
  · exact nat_good a
  · exact decimal_good hv

theorem eff_corner (b : Subd) (a : Nat) (v : S) (hva : t.hasVert a = true)
    (hv : isDecimal v = true) (hn : NonNeg v) (hk : a ∉ b.corners.map (·.1)) :
    lineStep t b (cornerLine (a, v)) = { b with corners := b.corners ++ [(a, v)] } := by
  unfold cornerLine
  simp only [t_toList]
  rw [lineStep_t _ (corner_args_good a v hv), step_of_classify (classify_corner a v hv)]
  simp [stepTag, stepCorner, hva, Subd.setCorner, sharp_of_nonneg hn, upsert_absent _ _ _ hk]
  intro hh; exact absurd hh (by omega)

theorem creases_fold (cs : List ((Nat × Nat) × S)) (b : Subd)
    (hc : ∀ c ∈ cs, c.1.1 < c.1.2 ∧ t.hasEdge c.1.1 c.1.2 = true ∧ isDecimal c.2 = true ∧ NonNeg c.2)
    (hnd : ((b.creases ++ cs).map (·.1)).Nodup) :
    (cs.map creaseLine).foldl (lineStep t) b = { b with creases := b.creases ++ cs } := by
  induction cs generalizing b with
  | nil => cases b; simp
  | cons c cs ih =>
    obtain ⟨⟨x, y⟩, v⟩ := c
    have ⟨h1, h2, h3, h4⟩ := hc ((x, y), v) (by simp)
    simp only [List.map_cons, List.foldl_cons]
    have hk : (x, y) ∉ b.creases.map (·.1) := by
      intro hm
      rw [List.map_append, List.nodup_append] at hnd
      exact hnd.2.2 _ hm _ (by simp) rfl
    rw [eff_crease b x y v h1 h2 h3 h4 hk, ih _ (fun c hc' => hc c (by simp [hc']))
      (by simpa using hnd)]
    simp

theorem corners_fold (cs : List (Nat × S)) (b : Subd)
    (hc : ∀ c ∈ cs, t.hasVert c.1 = true ∧ isDecimal c.2 = true ∧ NonNeg c.2)
    (hnd : ((b.corners ++ cs).map (·.1)).Nodup) :
    (cs.map cornerLine).foldl (lineStep t) b = { b with corners := b.corners ++ cs } := by
  induction cs generalizing b with
  | nil => cases b; simp
  | cons c cs ih =>
    obtain ⟨x, v⟩ := c
    have ⟨h1, h2, h3⟩ := hc (x, v) (by simp)
    simp only [List.map_cons, List.foldl_cons]
    have hk : x ∉ b.corners.map (·.1) := by
      intro hm
      rw [List.map_append, List.nodup_append] at hnd
      exact hnd.2.2 _ hm _ (by simp) rfl
    rw [eff_corner b x v h1 h2 h3 hk, ih _ (fun c hc' => hc c (by simp [hc']))
      (by simpa using hnd)]
    simp

theorem stepHole_absent (b : Subd) (hs : List Nat) (hf : ∀ h ∈ hs, h < t.numFaces)
    (hnd : (b.holes ++ hs).Nodup) :
    stepHole t b (hs.map Int.ofNat) = { b with holes := b.holes ++ hs } := by
  unfold stepHole
  induction hs generalizing b with
  | nil => cases b; simp
  | cons h hs ih =>
    rw [List.map_cons, List.foldl_cons]
    have hlt := hf h (by simp)
    have hc : b.holes.contains h = false := by
      rw [List.nodup_append] at hnd
      simpa using fun hm => hnd.2.2 _ hm _ (by simp) rfl
    have e : holeStep t b (Int.ofNat h) = { b with holes := b.holes ++ [h] } := by
      unfold holeStep Subd.addHole
      simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, Bool.or_eq_true, decide_eq_true_eq,
        ge_iff_le]
      have h1 : ¬((h : Int) < 0 ∨ t.numFaces ≤ h) := by omega
      rw [if_neg h1, hc]
      rfl
    rw [e, ih _ (fun x hx => hf x (by simp [hx])) (by simpa using hnd)]
    simp

theorem hole_args_good (hs : List Nat) :
    ∀ w ∈ ["hole".toList, nat hs.length ++ "/0/0".toList] ++ hs.map nat, GoodTok w := by
  intro w hw
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hw
  rcases hw with rfl | rfl | ⟨n, -, rfl⟩
  · lit_good
  · exact nat_hole_good _
  · exact nat_good n

theorem eff_hole (b : Subd) (hs : List Nat) (hne : hs ≠ []) (hlen : hs.length ≤ maxCount)
    (hf : ∀ h ∈ hs, h < t.numFaces) (hnd : (b.holes ++ hs).Nodup) :
    lineStep t b (holeLine hs) = { b with holes := b.holes ++ hs } := by
  unfold holeLine
  have e : ["t".toList, "hole".toList, nat hs.length ++ "/0/0".toList] ++ hs.map nat =
      ['t'] :: (["hole".toList, nat hs.length ++ "/0/0".toList] ++ hs.map nat) := rfl
  rw [e, lineStep_t _ (hole_args_good hs), step_of_classify (classify_hole hs hlen)]
  have hl : hs.length ≥ 1 := List.length_pos_iff.mpr hne
  have : ¬(hs.length = 0) := by omega
  simp [stepTag, this, stepHole_absent b hs hf hnd]

theorem chunks_spec (k : Nat) (hk : 0 < k) (l : List Nat) :
    (chunks k l).flatten = l ∧ ∀ c ∈ chunks k l, c ≠ [] ∧ c.length ≤ k := by
  unfold chunks
  simp only [Nat.ne_of_gt hk, ite_false]
  suffices ∀ fuel (l : List Nat), l.length ≤ fuel →
      (chunks.go k fuel l).flatten = l ∧ ∀ c ∈ chunks.go k fuel l, c ≠ [] ∧ c.length ≤ k from
    this _ l (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero => intro l hl; cases l <;> simp_all [chunks.go]
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp [chunks.go]
    | cons x xs =>
      have ⟨h1, h2⟩ := ih ((x :: xs).drop k)
        (by simp only [List.length_drop, List.length_cons] at hl ⊢; omega)
      simp only [chunks.go, List.flatten_cons, h1, List.take_append_drop, List.mem_cons,
        true_and]
      refine fun c hc => ?_
      rcases hc with rfl | hc
      · exact ⟨by cases k <;> simp_all, List.length_take_le _ _⟩
      · exact h2 c hc

theorem holes_fold (cks : List (List Nat)) (b : Subd)
    (hc : ∀ c ∈ cks, c ≠ [] ∧ c.length ≤ maxCount) (hf : ∀ h ∈ cks.flatten, h < t.numFaces)
    (hnd : (b.holes ++ cks.flatten).Nodup) :
    (cks.map holeLine).foldl (lineStep t) b = { b with holes := b.holes ++ cks.flatten } := by
  induction cks generalizing b with
  | nil => cases b; simp
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons, List.flatten_cons] at *
    have hnd1 : (b.holes ++ c).Nodup := by
      rw [← List.append_assoc] at hnd; exact hnd.sublist (List.sublist_append_left _ _)
    rw [eff_hole b c (hc c (by simp)).1 (hc c (by simp)).2 (fun x hx => hf x (by simp [hx])) hnd1,
      ih _ (fun x hx => hc x (by simp [hx])) (fun x hx => hf x (by simp [hx]))
        (by simpa [List.append_assoc] using hnd)]
    simp [List.append_assoc]

theorem stepTag_unknown (b : Subd) (args : List S) (g : Tag) (hk : isKnown g.name = false) :
    stepTag t b args g.name g.ni g.nf g.ns g.ints g.flts g.strs =
      { b with unknown := b.unknown ++ [joinSp (['t'] :: args)] } := by
  simp only [isKnown, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hk
  unfold stepTag
  simp [hk]

theorem unknown_fold (us : List S) (b : Subd) (hu : ∀ u ∈ us, UnknownLine u) :
    us.foldl (lineStep t) b = { b with unknown := b.unknown ++ us } := by
  induction us generalizing b with
  | nil => cases b; simp
  | cons u us ih =>
    simp only [List.foldl_cons]
    obtain ⟨args, rfl, hg, g, hc, hk⟩ := hu u (by simp)
    rw [lineStep_t _ hg, step_of_classify hc, stepTag_unknown b args g hk,
      ih _ (fun x hx => hu x (by simp [hx]))]
    simp

/-! ## The theorem -/

theorem t_good : GoodTok ['t'] := ⟨by simp, by decide⟩

theorem noNL_of_join (ts : List S) (h : ∀ w ∈ ts, GoodTok w) : ∀ c ∈ joinSp ts, c ≠ '\n' :=
  fun c hc => (joinSp_noBreak ts h c hc).1

theorem scal_noNL (tag cnt : String) (v : Option S) (ht : GoodTok tag.toList)
    (hc : GoodTok cnt.toList) (hv : ∀ x, v = some x → GoodTok x) :
    ∀ l ∈ scalLine tag cnt v, ∀ c ∈ l, c ≠ '\n' := by
  intro l hl
  unfold scalLine at hl
  cases hvx : v with
  | none => simp [hvx] at hl
  | some x =>
    simp only [hvx, List.mem_singleton] at hl
    subst hl
    apply noNL_of_join
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact t_good
    · exact ht
    · exact hc
    · exact hv _ hvx

theorem printed_noNL (s : Subd) (inv : Inv t s) : ∀ l ∈ printLines s, ∀ c ∈ l, c ≠ '\n' := by
  have hv := inv.valid
  intro l hl
  unfold printLines scalarLines at hl
  simp only [List.mem_append, List.mem_map] at hl
  rcases hl with (((((((hl | hl) | hl) | hl) | hl) | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩) | ⟨hs, hhs, rfl⟩) | hl
  · refine scal_noNL _ _ _ (by lit_good) (by lit_good) (fun x hx => ?_) l hl
    cases h : s.scheme with
    | none => simp [nameOf, h] at hx
    | some i =>
      simp only [nameOf, h, Option.map_some, Option.some.injEq] at hx; subst hx
      exact (lookup3 i (by have := hv.scheme_range i h; omega)).2
  · refine scal_noNL _ _ _ (by lit_good) (by lit_good) (fun x hx => ?_) l hl
    cases h : s.ib with
    | none => simp [h] at hx
    | some i => simp only [h, Option.map_some, Option.some.injEq] at hx; subst hx; exact nat_good i
  · refine scal_noNL _ _ _ (by lit_good) (by lit_good) (fun x hx => ?_) l hl
    cases h : s.fvar with
    | none => simp [h] at hx
    | some i => simp only [h, Option.map_some, Option.some.injEq] at hx; subst hx; exact nat_good i
  · refine scal_noNL _ _ _ (by lit_good) (by lit_good) (fun x hx => ?_) l hl
    cases h : s.cm with
    | none => simp [nameOf, h] at hx
    | some i =>
      simp only [nameOf, h, Option.map_some, Option.some.injEq] at hx; subst hx
      exact (lookup2a i (by have := hv.cm_range i h; omega)).2
  · refine scal_noNL _ _ _ (by lit_good) (by lit_good) (fun x hx => ?_) l hl
    cases h : s.st with
    | none => simp [nameOf, h] at hx
    | some i =>
      simp only [nameOf, h, Option.map_some, Option.some.injEq] at hx; subst hx
      exact (lookup2b i (by have := hv.st_range i h; omega)).2
  · unfold creaseLine
    simp only [t_toList]
    apply noNL_of_join
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact t_good
    · exact crease_args_good _ _ _ (inv.cdec c hc) w (by simpa using hw)
  · unfold cornerLine
    simp only [t_toList]
    apply noNL_of_join
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact t_good
    · exact corner_args_good _ _ (inv.kdec c hc) w (by simpa using hw)
  · unfold holeLine
    apply noNL_of_join
    intro w hw
    simp only [List.cons_append, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact t_good
    · exact hole_args_good hs w (by simpa using hw)
  · obtain ⟨args, rfl, hg, -⟩ := inv.unk l hl
    apply noNL_of_join
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact t_good
    · exact hg w hw

/-- **Canonical round trip.** For mesh lines without line-break characters, an accepted
model is reproduced by parsing its canonical form. -/
theorem roundtrip (t : Topo) (lines : List S) (hl : ∀ l ∈ lines, ∀ c ∈ l, c ≠ '\n' ∧ c ≠ '\r')
    (hok : ok (parseLines t lines) = true) :
    parseLines t (splitOn '\n' (print (parseLines t lines))) = parseLines t lines := by
  have inv : Inv t (parseLines t lines) := by
    rw [parseLines_eq]; exact inv_finish (inv_fold t lines hl {} inv_empty)
  have hfin : finish t (parseLines t lines) = parseLines t lines := by
    rw [parseLines_eq] at hok ⊢
    have := (finish_ok hok).1
    simp only [this]
  generalize parseLines t lines = s at inv hfin hok ⊢
  have hbad : s.bad = false := by simpa [ok] using hok
  have hv := inv.valid
  unfold print
  rw [hbad]
  simp only [Bool.false_eq_true, ite_false]
  rw [splitOn_lines _ _ (printed_noNL s inv), parseLines_eq, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, lineStep_nil]
  unfold printLines
  simp only [List.foldl_append]
  have hck := chunks_spec maxCount (by decide) s.holes
  rw [scalars_fold s hv]
  rw [creases_fold s.creases _
    (fun c hc => ⟨(hv.crease_edge c hc).1, (hv.crease_edge c hc).2, inv.cdec c hc,
      hv.crease_sharp c hc⟩) (by simpa using hv.crease_nodup)]
  rw [corners_fold s.corners _
    (fun c hc => ⟨hv.corner_vert c hc, inv.kdec c hc, hv.corner_sharp c hc⟩)
    (by simpa using hv.corner_nodup)]
  rw [holes_fold (chunks maxCount s.holes) _ (fun c hc => hck.2 c hc)
    (by rw [hck.1]; exact hv.hole_face) (by simpa [hck.1] using hv.hole_nodup)]
  rw [unknown_fold s.unknown _ inv.unk]
  rw [hck.1]
  obtain ⟨sc, ib, fv, cm, st, cr, co, ho, un, bad⟩ := s
  simp only at hbad
  subst hbad
  simpa using hfin

end TobjSubd

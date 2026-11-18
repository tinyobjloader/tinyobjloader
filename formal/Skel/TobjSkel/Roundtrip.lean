import TobjSkel.Sound
import TobjSubd.Roundtrip

/-!
# Canonical round trip for skeletons

`roundtrip`: for lines without line-break characters, an accepted skeleton
`s = parseLines lines maxId` is reproduced by parsing its canonical form.
-/
namespace TobjSkel
open TobjSubd

/-! ## Invariants of a parse -/

def SlotGood : Option (S × Option S) → Prop
  | none => True
  | some (p, n) => GoodTok p ∧ ∀ x, n = some x → GoodTok x

structure Inv (s : Skel) : Prop where
  valid : Valid s
  bdec : ∀ j ∈ s.joints, ∀ m, j.bind = some m → ∀ v ∈ m, isDecimal v = true
  rdec : ∀ j ∈ s.joints, ∀ m, j.rest = some m → ∀ v ∈ m, isDecimal v = true
  lib : SlotGood s.lib
  anim : SlotGood s.anim

/-- Something prints, or the parse failed. -/
def Prints (s : Skel) : Prop := s.bad = true ∨ s.joints ≠ [] ∨ s.lib.isSome ∨ s.anim.isSome

theorem isMatrix_dec {m : List S} (h : isMatrix m = true) : ∀ v ∈ m, isDecimal v = true := by
  unfold isMatrix at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact h.2

theorem inv_of_valid_parts {s : Skel} (h : Valid s) (hl : SlotGood s.lib) (ha : SlotGood s.anim) :
    Inv s :=
  ⟨h, fun j hj m hm => isMatrix_dec (h.bind j hj m hm), fun j hj m hm => isMatrix_dec (h.rest j hj m hm),
    hl, ha⟩

theorem inv_empty : Inv ({} : Skel) := inv_of_valid_parts valid_empty trivial trivial

theorem inv_err {s : Skel} (h : Inv s) : Inv s.err := inv_of_valid_parts h.valid.err h.lib h.anim

theorem stepJoint_slots (s : Skel) (args : List S) :
    (stepJoint s args).lib = s.lib ∧ (stepJoint s args).anim = s.anim := by
  unfold stepJoint
  split
  · repeat' split
    all_goals simp [Skel.err, Skel.addJoint]
  · simp [Skel.err]

theorem stepRest_slots (s : Skel) (args : List S) :
    (stepRest s args).lib = s.lib ∧ (stepRest s args).anim = s.anim ∧
      (stepRest s args).joints.length = s.joints.length := by
  unfold stepRest
  split
  · repeat' split
    all_goals simp [Skel.err, setAt]
  · simp [Skel.err]

/-- Either an error, or the step added something that prints. -/
theorem stepJoint_some (s : Skel) (args : List S) :
    (stepJoint s args).bad = true ∨ (stepJoint s args).joints ≠ [] := by
  unfold stepJoint
  split
  · repeat' split
    all_goals simp [Skel.err, Skel.addJoint]
  · simp [Skel.err]

theorem stepRest_some (s : Skel) (args : List S) :
    (stepRest s args).bad = true ∨ (stepRest s args).joints ≠ [] := by
  unfold stepRest
  split
  · repeat' split
    all_goals first
      | (left; simp [Skel.err]; done)
      | (right; simp only [setAt, ne_eq, List.set_eq_nil_iff]; intro he; simp_all)
  · simp [Skel.err]

theorem stepSlot_some (s : Skel) (lib : Bool) (args : List S) :
    (stepSlot s lib args).bad = true ∨ (stepSlot s lib args).lib.isSome ∨
      (stepSlot s lib args).anim.isSome := by
  cases lib <;> simp only [stepSlot, Bool.false_eq_true, ite_false, ite_true] <;>
    split <;> (try split) <;> simp [Skel.err]

theorem stepSlot_good {s : Skel} (hl : SlotGood s.lib) (ha : SlotGood s.anim) (lib : Bool)
    (args : List S) (hg : ∀ w ∈ args, GoodTok w) :
    SlotGood (stepSlot s lib args).lib ∧ SlotGood (stepSlot s lib args).anim := by
  have one : ∀ p, p ∈ args → GoodTok p := hg
  rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨q, r⟩⟩⟩
  all_goals cases lib <;> simp only [stepSlot, Bool.false_eq_true, ite_false, ite_true]
  all_goals first
    | exact ⟨by simp only [Skel.err]; exact hl, by simp only [Skel.err]; exact ha⟩
    | (split
       · exact ⟨by simp only [Skel.err]; exact hl, by simp only [Skel.err]; exact ha⟩
       · refine ⟨?_, ?_⟩ <;> first
           | exact hl
           | exact ha
           | exact ⟨one p (by simp), fun x hx => by
               simp only [Option.some.injEq] at hx; subst hx; exact one _ (by simp)⟩
           | exact ⟨one p (by simp), fun x hx => by simp at hx⟩)

theorem prints_step (s : Skel) (kw : S) (args : List S) : Prints (step s kw args) := by
  unfold step Prints
  split
  · rcases stepJoint_some s args with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  split
  · rcases stepRest_some s args with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases stepSlot_some s (kw == kwLib) args with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem inv_step {s : Skel} (h : Inv s) (kw : S) (args : List S) (hg : ∀ w ∈ args, GoodTok w) :
    Inv (step s kw args) := by
  unfold step
  split
  · have ⟨hl, ha⟩ := stepJoint_slots s args
    exact inv_of_valid_parts (valid_stepJoint h.valid args) (hl ▸ h.lib) (ha ▸ h.anim)
  split
  · obtain ⟨hl, ha, -⟩ := stepRest_slots s args
    exact inv_of_valid_parts (valid_stepRest h.valid args) (hl ▸ h.lib) (ha ▸ h.anim)
  · have ⟨hl, ha⟩ := stepSlot_good h.lib h.anim (kw == kwLib) args hg
    exact inv_of_valid_parts (valid_stepSlot h.valid (kw == kwLib) args) hl ha

theorem inv_lineStep {s : Skel} (h : Inv s) (l : S) (hl : ∀ c ∈ l, c ≠ '\n' ∧ c ≠ '\r') :
    Inv (lineStep s l) := by
  unfold lineStep
  split
  · rename_i kw args heq
    split
    · have hg := lineTokens_good l hl
      rw [heq] at hg
      exact inv_step (inv_of_valid_parts (s := { s with ext := true })
        (valid_of_joints h.valid rfl) h.lib h.anim) kw args
        (fun w hw => hg w (by simp [hw]))
    · exact h
  · exact h

/-- After any `skel_*` line, something prints or the parse failed. -/
theorem prints_lineStep {s : Skel} (h : s.ext = true → Prints s) (l : S) :
    (lineStep s l).ext = true → Prints (lineStep s l) := by
  unfold lineStep
  split
  · split
    · intro _; exact prints_step _ _ _
    · exact h
  · exact h

/-! ## Re-parsing the printed lines -/

theorem validName_good {n : S} (h : validName n = true) : GoodTok n := by
  cases n with
  | nil => simp [validName] at h
  | cons c r =>
    refine ⟨by simp, ?_⟩
    simp only [validName, Bool.and_eq_true, List.all_eq_true] at h
    have ok : ∀ d, (isAlpha d || isDigit d || d == '_') = true →
        isBlank d = false ∧ d ≠ '\n' ∧ d ≠ '\r' := by
      intro d hd
      refine ⟨?_, ?_, ?_⟩
      · cases hb : isBlank d
        · rfl
        · simp only [isBlank, Bool.or_eq_true, beq_iff_eq] at hb
          rcases hb with rfl | rfl <;> simp_all [isAlpha, isDigit]
      all_goals (rintro rfl; simp [isAlpha, isDigit] at hd)
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ok d (by simp only [Bool.or_eq_true] at h ⊢; rcases h.1 with h1 | h1 <;> simp [h1])
    · exact ok d (h.2 d hd)

theorem kw_good : ∀ k ∈ [kwJoint, kwRest, kwLib, kwAnim], GoodTok k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem lineStep_kw (s : Skel) (kw : S) (args : List S) (hk : kw ∈ [kwJoint, kwRest, kwLib, kwAnim])
    (hg : ∀ w ∈ args, GoodTok w) :
    lineStep s (joinSp (kw :: args)) = step { s with ext := true } kw args := by
  have hall : ∀ w ∈ kw :: args, GoodTok w := by
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact kw_good w hk
    · exact hg w hw
  unfold lineStep
  rw [dropCR_of_noCR _ (fun c hc => (joinSp_noBreak _ hall c hc).2),
    lineTokens_joinSp _ (by simp) hall]
  have : isSkelKw kw = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> decide
  simp only [this, ite_true]

/-! ### `findJoint` depends only on names -/

theorem findJoint_eq_names (l : List Joint) (n : S) :
    findJoint l n = (l.map (·.name)).findIdx? (· == n) := by
  unfold findJoint; rw [List.findIdx?_map]; rfl

theorem findJoint_congr {l1 l2 : List Joint} (h : l1.map (·.name) = l2.map (·.name)) (n : S) :
    findJoint l1 n = findJoint l2 n := by
  rw [findJoint_eq_names, findJoint_eq_names, h]

theorem findJoint_nodup {js : List Joint} (hnd : (js.map (·.name)).Nodup) {i : Nat}
    (hi : i < js.length) : findJoint js js[i].name = some i := by
  rw [findJoint_eq_names, List.findIdx?_eq_some_iff_getElem]
  refine ⟨by simpa using hi, by simp, ?_⟩
  intro j hj
  have hjl : j < js.length := by omega
  have : (js.map (·.name))[j]'(by simpa using hjl) ≠ (js.map (·.name))[i]'(by simpa using hi) := by
    intro e
    have := (List.Nodup.getElem_inj hnd).mp e
    omega
  simpa using this

theorem findJoint_take {js : List Joint} (hnd : (js.map (·.name)).Nodup) {i k : Nat}
    (hi : i < js.length) : findJoint (js.take k) js[i].name = if i < k then some i else none := by
  have h := findJoint_nodup hnd hi
  unfold findJoint at h ⊢
  rw [List.findIdx?_take, h]
  by_cases hik : i < k <;> simp [hik, Option.guard]

def clear (j : Joint) : Joint := { j with rest := none }

theorem names_clear (l : List Joint) : (l.map clear).map (·.name) = l.map (·.name) := by
  simp [clear, Function.comp_def]

theorem validName_ne_dash {n : S} (h : validName n = true) : n ≠ ['-'] := by
  rintro rfl; simp [validName, isAlpha] at h

theorem bindOf_getD {j : Joint} (h : ∀ m, j.bind = some m → isMatrix m = true) :
    bindOf (j.bind.getD []) = j.bind := by
  cases hb : j.bind with
  | none => rfl
  | some m =>
    have := h m hb
    unfold isMatrix at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    unfold bindOf
    have : m.isEmpty = false := by
      cases m with
      | nil => simp at this
      | cons => rfl
    simp [this]

/-! ### Joint lines -/

theorem joints_fold (js : List Joint) (hv : ∀ s : Skel, s.joints = js → Valid s)
    (hdec : ∀ j ∈ js, ∀ m, j.bind = some m → ∀ v ∈ m, isDecimal v = true) :
    ∀ (pre post : List Joint), pre ++ post = js → ∀ (b : Skel), b.ext = true →
      b.joints = pre.map clear →
      (post.map (jointLine js)).foldl lineStep b = { b with joints := (pre ++ post).map clear } := by
  have hV := hv { joints := js } rfl
  intro pre post
  induction post generalizing pre with
  | nil => intro _ b _ hb; simp [← hb]
  | cons j post ih =>
    intro hjs b he hb
    simp only [List.map_cons, List.foldl_cons]
    have hk : pre.length < js.length := by rw [← hjs]; simp
    have hj : js[pre.length] = j := by simp [← hjs]
    have hpre : pre = js.take pre.length := by rw [← hjs]; simp
    have hjm : j ∈ js := by rw [← hjs]; simp
    have hname := hV.names j hjm
    -- the line re-adds `clear j`
    have hstep : lineStep b (jointLine js j) = b.addJoint (clear j) := by
      unfold jointLine
      have hbind := fun m hm => hV.bind j hjm m hm
      have hgood : ∀ w ∈ [j.name, parentName js j.parent] ++ j.bind.getD [], GoodTok w := by
        intro w hw
        simp only [List.cons_append, List.nil_append, List.mem_cons] at hw
        rcases hw with rfl | rfl | hw
        · exact validName_good hname
        · cases hpq : j.parent with
          | none => simp only [parentName]; exact ⟨by simp, by decide⟩
          | some q =>
            simp only [parentName]
            cases hq : js[q]? with
            | none => exact ⟨by simp, by decide⟩
            | some jq =>
              simp only [Option.map_some, Option.getD_some]
              exact validName_good (hV.names jq (List.mem_of_getElem? hq))
        · cases hb' : j.bind with
          | none => simp [hb'] at hw
          | some m =>
            simp only [hb', Option.getD_some] at hw
            exact decimal_good (hdec j hjm m hb' w hw)
      have e : [kwJoint, j.name, parentName js j.parent] ++ j.bind.getD [] =
          kwJoint :: ([j.name, parentName js j.parent] ++ j.bind.getD []) := rfl
      rw [e, lineStep_kw _ _ _ (by simp) hgood]
      have hb2 : ({ b with ext := true } : Skel) = b := by
        cases b with
        | mk jj ll aa ee bb => simp only at he; subst he; rfl
      rw [hb2]
      unfold step
      simp only [show (kwJoint == kwJoint) = true from by decide, ite_true]
      rw [show [j.name, parentName js j.parent] ++ j.bind.getD [] =
          j.name :: parentName js j.parent :: j.bind.getD [] from rfl]
      unfold stepJoint
      -- m: no matrix or 16 decimals
      have hlen : ((j.bind.getD []).length == 0 || (j.bind.getD []).length == 16) = true := by
        cases hb' : j.bind with
        | none => simp
        | some m =>
          have := hbind m hb'
          unfold isMatrix at this
          simp only [Bool.and_eq_true, beq_iff_eq] at this
          simp [this.1]
      have hdupn : findJoint b.joints j.name = none := by
        rw [hb, findJoint_congr (names_clear pre), hpre, ← hj, findJoint_take hV.nodup hk]
        simp
      have hpar : parentOf? b.joints (parentName js j.parent) = some j.parent := by
        unfold parentOf?
        cases hp : j.parent with
        | none => simp [parentName]
        | some q =>
          have hq : q < pre.length := hV.parent pre.length hk q (by rw [hj]; exact hp)
          have hql : q < js.length := by omega
          have pn : parentName js (some q) = js[q].name := by
            simp [parentName, List.getElem?_eq_getElem hql]
          rw [pn]
          have hnd := validName_ne_dash (hV.names js[q] (List.getElem_mem hql))
          simp only [beq_iff_eq, hnd, ite_false]
          rw [hb, findJoint_congr (names_clear pre), hpre, findJoint_take hV.nodup hql]
          simp [hq]
      have hmat : ((j.bind.getD []).length == 16 && !(j.bind.getD []).all isDecimal) = false := by
        cases hb' : j.bind with
        | none => simp
        | some m =>
          have := hdec j hjm m hb'
          simp [List.all_eq_true.mpr this]
      simp only [hlen, Bool.not_true, Bool.false_eq_true, ite_false, hname, hdupn,
        Option.isSome_none, hpar, hmat]
      rw [bindOf_getD hbind]
      rfl
    rw [hstep]
    have := ih (pre ++ [j]) (by simp [← hjs]) (b.addJoint (clear j)) he (by
      simp [Skel.addJoint, hb])
    rw [this]
    simp [Skel.addJoint]

/-! ### Rest lines -/

def restLines (js : List Joint) : List S := js.filterMap fun j => j.rest.map (restLine j)

theorem rests_fold (js : List Joint) (hV : Valid { joints := js })
    (hdec : ∀ j ∈ js, ∀ m, j.rest = some m → ∀ v ∈ m, isDecimal v = true) :
    ∀ (pre post : List Joint), pre ++ post = js → ∀ (b : Skel), b.ext = true →
      b.joints = pre ++ post.map clear →
      (restLines post).foldl lineStep b = { b with joints := pre ++ post } := by
  intro pre post
  induction post generalizing pre with
  | nil => intro _ b _ hb; cases b; simp_all [restLines]
  | cons j post ih =>
    intro hjs b he hb
    have hjm : j ∈ js := by rw [← hjs]; simp
    have hk : pre.length < js.length := by rw [← hjs]; simp
    have hj : js[pre.length] = j := by simp [← hjs]
    have hnames : b.joints.map (·.name) = js.map (·.name) := by
      rw [hb, ← hjs]; simp [clear, Function.comp_def]
    cases hr : j.rest with
    | none =>
      have hc : clear j = j := by cases j; simp_all [clear]
      simp only [restLines, List.filterMap_cons, hr, Option.map_none]
      have := ih (pre ++ [j]) (by simp [← hjs]) b he (by rw [hb]; simp [hc])
      simpa [restLines] using this
    | some m =>
      simp only [restLines, List.filterMap_cons, hr, Option.map_some, List.foldl_cons]
      have hmat := hV.rest j hjm m hr
      have hgood : ∀ w ∈ j.name :: m, GoodTok w := by
        intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact validName_good (hV.names j hjm)
        · exact decimal_good (hdec j hjm m hr w hw)
      have hstep : lineStep b (restLine j m) =
          { b with joints := pre ++ j :: post.map clear } := by
        unfold restLine
        rw [show [kwRest, j.name] ++ m = kwRest :: j.name :: m from rfl,
          lineStep_kw _ _ _ (by simp) hgood]
        have hb2 : ({ b with ext := true } : Skel) = b := by
          cases b with
          | mk jj ll aa ee bb => simp only at he; subst he; rfl
        rw [hb2]
        unfold step
        simp only [show (kwRest == kwJoint) = false from by decide,
          show (kwRest == kwRest) = true from by decide, Bool.false_eq_true, ite_false, ite_true]
        unfold stepRest
        have h16 : (m.length != 16) = false := by
          unfold isMatrix at hmat
          simp only [Bool.and_eq_true, beq_iff_eq] at hmat
          simp [hmat.1]
        have hfind : findJoint b.joints j.name = some pre.length := by
          rw [findJoint_congr hnames, ← hj]; exact findJoint_nodup hV.nodup hk
        have hget : b.joints[pre.length]? = some (clear j) := by rw [hb]; simp
        have hdec' : m.all isDecimal = true := List.all_eq_true.mpr (hdec j hjm m hr)
        simp only [h16, Bool.false_eq_true, ite_false, hfind, hget, clear, Option.isSome_none,
          hdec', Bool.not_true]
        rw [hb]
        simp only [setAt]
        congr 1
        rw [List.set_append_right _ _ (by simp)]
        simp only [Nat.sub_self, List.map_cons, List.set_cons_zero]
        cases j; simp_all
      rw [hstep]
      have := ih (pre ++ [j]) (by simp [← hjs]) { b with joints := pre ++ j :: post.map clear } he
        (by simp)
      simp only [restLines] at this
      rw [this]
      simp

/-! ### `skel_lib` / `skel_anim` lines -/

theorem slot_line (b : Skel) (he : b.ext = true) (lib : Bool) (v : S × Option S)
    (hg : SlotGood (some v)) (hnone : (if lib then b.lib else b.anim) = none) :
    (slotLine (if lib then kwLib else kwAnim) (some v)).foldl lineStep b =
      if lib then { b with lib := some v } else { b with anim := some v } := by
  obtain ⟨p, n⟩ := v
  obtain ⟨hp, hn⟩ := hg
  have hgood : ∀ w ∈ p :: n.toList, GoodTok w := by
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hp
    · cases n with
      | none => simp at hw
      | some x => simp at hw; subst hw; exact hn _ rfl
  simp only [slotLine, List.foldl_cons, List.foldl_nil]
  rw [show [if lib then kwLib else kwAnim, p] ++ n.toList =
      (if lib then kwLib else kwAnim) :: (p :: n.toList) from rfl,
    lineStep_kw _ _ _ (by cases lib <;> simp) hgood]
  have hb2 : ({ b with ext := true } : Skel) = b := by
    cases b with
    | mk jj ll aa ee bb => simp only at he; subst he; rfl
  rw [hb2]
  cases lib <;> cases n <;>
    simp_all [step, stepSlot, show (kwAnim == kwJoint) = false from by decide,
      show (kwAnim == kwRest) = false from by decide, show (kwAnim == kwLib) = false from by decide,
      show (kwLib == kwJoint) = false from by decide, show (kwLib == kwRest) = false from by decide,
      show (kwLib == kwLib) = true from by decide]

theorem slot_none (b : Skel) (kw : S) : (slotLine kw none).foldl lineStep b = b := rfl

/-! ## The theorem -/

/-- A printed line: a `skel_*` keyword and clean tokens. -/
def SkelLine (l : S) : Prop :=
  ∃ kw ∈ [kwJoint, kwRest, kwLib, kwAnim], ∃ args, (∀ w ∈ args, GoodTok w) ∧ l = joinSp (kw :: args)

theorem printed_skel (s : Skel) (inv : Inv s) : ∀ l ∈ printLines s, SkelLine l := by
  have hV := inv.valid
  intro l hl
  unfold printLines at hl
  simp only [List.mem_append, List.mem_map, List.mem_filterMap] at hl
  rcases hl with (((⟨j, hj, rfl⟩ | ⟨j, hj, hr⟩) | hl) | hl)
  · refine ⟨kwJoint, by simp, [j.name, parentName s.joints j.parent] ++ j.bind.getD [], ?_, rfl⟩
    intro w hw
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · exact validName_good (hV.names j hj)
    · cases hp : j.parent with
      | none => simp only [parentName]; exact ⟨by simp, by decide⟩
      | some q =>
        simp only [parentName]
        cases hq : s.joints[q]? with
        | none => exact ⟨by simp, by decide⟩
        | some jq =>
          simp only [Option.map_some, Option.getD_some]
          exact validName_good (hV.names jq (List.mem_of_getElem? hq))
    · cases hb : j.bind with
      | none => simp [hb] at hw
      | some m => simp only [hb, Option.getD_some] at hw; exact decimal_good (inv.bdec j hj m hb w hw)
  · cases hrj : j.rest with
    | none => simp [hrj] at hr
    | some m =>
      simp only [hrj, Option.map_some, Option.some.injEq] at hr
      subst hr
      refine ⟨kwRest, by simp, j.name :: m, ?_, rfl⟩
      intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact validName_good (hV.names j hj)
      · exact decimal_good (inv.rdec j hj m hrj w hw)
  all_goals
    first
      | (cases hs : s.lib with
          | none => simp [hs, slotLine] at hl
          | some v =>
            obtain ⟨p, n⟩ := v
            simp only [hs, slotLine, List.mem_singleton] at hl
            subst hl
            have hg := inv.lib; rw [hs] at hg
            refine ⟨kwLib, by simp, p :: n.toList, ?_, rfl⟩
            intro w hw; simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact hg.1
            · cases n with
              | none => simp at hw
              | some x => simp at hw; subst hw; exact hg.2 _ rfl)
      | (cases hs : s.anim with
          | none => simp [hs, slotLine] at hl
          | some v =>
            obtain ⟨p, n⟩ := v
            simp only [hs, slotLine, List.mem_singleton] at hl
            subst hl
            have hg := inv.anim; rw [hs] at hg
            refine ⟨kwAnim, by simp, p :: n.toList, ?_, rfl⟩
            intro w hw; simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact hg.1
            · cases n with
              | none => simp at hw
              | some x => simp at hw; subst hw; exact hg.2 _ rfl)

theorem skelLine_noNL {l : S} (h : SkelLine l) : ∀ c ∈ l, c ≠ '\n' := by
  obtain ⟨kw, hk, args, hg, rfl⟩ := h
  intro c hc
  refine (joinSp_noBreak (kw :: args) ?_ c hc).1
  intro w hw
  simp only [List.mem_cons] at hw
  rcases hw with rfl | hw
  · exact kw_good w hk
  · exact hg w hw

/-- The first `skel_*` line sets `ext`; starting with it set changes nothing. -/
theorem foldl_ext (L : List S) (hL : ∀ l ∈ L, SkelLine l) (b : Skel) :
    L ≠ [] → L.foldl lineStep b = L.foldl lineStep { b with ext := true } := by
  intro hne
  cases L with
  | nil => exact absurd rfl hne
  | cons l r =>
    obtain ⟨kw, hk, args, hg, rfl⟩ := hL l (by simp)
    simp only [List.foldl_cons]
    rw [lineStep_kw _ _ _ hk hg, lineStep_kw _ _ _ hk hg]

theorem inv_fold (lines : List S) (hl : ∀ l ∈ lines, ∀ c ∈ l, c ≠ '\n' ∧ c ≠ '\r') (s : Skel)
    (hs : Inv s) : Inv (lines.foldl lineStep s) := by
  induction lines generalizing s with
  | nil => exact hs
  | cons l r ih => exact ih (fun x hx => hl x (by simp [hx])) _ (inv_lineStep hs l (hl l (by simp)))

theorem prints_fold (lines : List S) (s : Skel) (hs : s.ext = true → Prints s) :
    (lines.foldl lineStep s).ext = true → Prints (lines.foldl lineStep s) := by
  induction lines generalizing s with
  | nil => exact hs
  | cons l r ih => exact ih _ (prints_lineStep hs l)

theorem finish_inv {s : Skel} (h : Inv s) (maxId : Int) : Inv (finish maxId s) := by
  unfold finish
  split
  · exact h
  · dsimp only
    split
    · split <;> first | exact inv_err (inv_err h) | exact inv_err h
    · split <;> first | exact inv_err h | exact h

/-- **Canonical round trip.** For lines without line-break characters, an accepted
skeleton is reproduced by parsing its canonical form. -/
theorem roundtrip (lines : List S) (maxId : Int)
    (hl : ∀ l ∈ lines, ∀ c ∈ l, c ≠ '\n' ∧ c ≠ '\r') (hok : ok (parseLines lines maxId) = true) :
    parseLines (splitOn '\n' (print (parseLines lines maxId))) maxId = parseLines lines maxId := by
  have inv : Inv (parseLines lines maxId) :=
    finish_inv (inv_fold lines hl {} inv_empty) maxId
  have hfin : finish maxId (parseLines lines maxId) = parseLines lines maxId := by
    unfold parseLines at hok ⊢
    simp only [(finish_ok hok).1]
  have hpr : Prints (parseLines lines maxId) := by
    have hok' := hok
    unfold parseLines at hok' ⊢
    have e := (finish_ok hok').1
    rw [e] at hok' ⊢
    unfold ok at hok'
    simp only [Bool.and_eq_true] at hok'
    exact prints_fold lines {} (by simp) hok'.1
  generalize parseLines lines maxId = s at inv hfin hok hpr ⊢
  have hext : s.ext = true := by unfold ok at hok; simp only [Bool.and_eq_true] at hok; exact hok.1
  have hbad : s.bad = false := by
    unfold ok at hok; simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hok
    exact hok.2
  have hV := inv.valid
  unfold print
  rw [hok]
  simp only [ite_true]
  have hsk := printed_skel s inv
  rw [splitOn_lines _ _ (fun l hl => skelLine_noNL (hsk l hl)), parseLines, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hnil : lineStep ((printLines s).foldl lineStep {}) [] =
      (printLines s).foldl lineStep {} := rfl
  rw [hnil]
  have hne : printLines s ≠ [] := by
    unfold Prints at hpr
    unfold printLines
    rcases hpr with h | h | h | h
    · simp [hbad] at h
    · cases hj : s.joints with
      | nil => exact absurd hj h
      | cons => simp
    · cases hs : s.lib with
      | none => simp [hs] at h
      | some v => simp [hs, slotLine]
    · cases hs : s.anim with
      | none => simp [hs] at h
      | some v => simp [hs, slotLine]
  rw [foldl_ext _ hsk _ hne]
  unfold printLines
  simp only [List.foldl_append]
  -- joints, then rest transforms
  have h1 := joints_fold s.joints (fun t ht => valid_of_joints hV ht) inv.bdec [] s.joints
    (by simp) { ext := true } rfl (by simp)
  rw [h1]
  simp only [List.nil_append]
  have h2 := rests_fold s.joints (valid_of_joints hV rfl) inv.rdec [] s.joints (by simp)
    { joints := s.joints.map clear, ext := true } rfl (by simp)
  simp only [restLines] at h2
  rw [h2]
  -- the slot lines
  have hlib : (slotLine kwLib s.lib).foldl lineStep ({ joints := s.joints, ext := true } : Skel) =
      { joints := s.joints, lib := s.lib, ext := true } := by
    cases hs : s.lib with
    | none => rfl
    | some v =>
      have hg := inv.lib; rw [hs] at hg
      have := slot_line ({ joints := s.joints, ext := true } : Skel) rfl true v hg rfl
      simpa using this
  simp only [List.nil_append]
  rw [hlib]
  have hanim : (slotLine kwAnim s.anim).foldl lineStep
      ({ joints := s.joints, lib := s.lib, ext := true } : Skel) =
      { joints := s.joints, lib := s.lib, anim := s.anim, ext := true } := by
    cases hs : s.anim with
    | none => rfl
    | some v =>
      have hg := inv.anim; rw [hs] at hg
      have := slot_line ({ joints := s.joints, lib := s.lib, ext := true } : Skel) rfl false v hg rfl
      simpa using this
  rw [hanim]
  have hs : ({ joints := s.joints, lib := s.lib, anim := s.anim, ext := true } : Skel) = s := by
    cases s; simp_all
  rw [hs, hfin]

end TobjSkel

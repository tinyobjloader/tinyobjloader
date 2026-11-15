/-
  Pure specification of an `.obj` writer for the mesh topology, and its
  round-trip with the parse model of `Obj/Mesh.lean`.

  Coordinates are abstract raw token text (see `Obj/Mesh.lean`); the writer
  never formats floating-point numbers, so the round-trip theorems have no
  float-formatting assumption.
-/
import Obj.Mesh
import Obj.Real
namespace Obj

/-! ### Decimal formatting of naturals -/

/-- Decimal digits (as ASCII codes) of `n`, most significant first. -/
def decDigits (n : Nat) : List Nat :=
  if h : n < 10 then [48 + n] else decDigits (n / 10) ++ [48 + n % 10]
termination_by n
decreasing_by omega

theorem decDigits_all (n : Nat) : ∀ d ∈ decDigits n, 48 ≤ d ∧ d ≤ 57 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decDigits]
    split
    · intro d hd; simp at hd; omega
    · rename_i h
      intro d hd
      simp at hd
      rcases hd with hd | hd
      · exact ih (n / 10) (by omega) d hd
      · omega

theorem decDigits_ne_nil (n : Nat) : decDigits n ≠ [] := by
  rw [decDigits]; split <;> simp

theorem scanDigit_of_digit {d : Nat} (h : 48 ≤ d ∧ d ≤ 57) : scanDigit d = true := by
  simp [scanDigit, h]

theorem takeWhile_digits_self (l : List Nat) (h : ∀ d ∈ l, 48 ≤ d ∧ d ≤ 57) :
    l.takeWhile scanDigit = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    simp only [List.takeWhile_cons, scanDigit_of_digit (h d (by simp)), ite_true]
    rw [ih (fun x hx => h x (by simp [hx]))]

theorem decDigits_fold (n : Nat) (hn : n ≤ 2147483647) :
    scanIntFold (decDigits n) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold scanIntFold
    rw [takeWhile_digits_self _ (decDigits_all n)]
    rw [decDigits]
    split
    · simp [scanIntStep]; omega
    · rename_i h
      have ih' := ih (n / 10) (by omega) (by omega)
      unfold scanIntFold at ih'
      rw [takeWhile_digits_self _ (decDigits_all (n / 10))] at ih'
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih', scanIntStep]
      have : n / 10 * 10 + (48 + n % 10 - 48) = n := by omega
      rw [this]; omega

/-- `scanInt` reads back a formatted natural from any position, provided the
    following byte (if any) is not a digit. -/
theorem scanInt_decDigits (pre post : List Nat) (n : Nat) (hn : n ≤ 2147483647)
    (hpre : True)
    (hpost : ∀ b, post.head? = some b → scanDigit b = false) :
    scanInt (pre ++ decDigits n ++ post) pre.length =
      (true, (n : Int), pre.length + (decDigits n).length) := by
  have hall := decDigits_all n
  have hdrop : (pre ++ decDigits n ++ post).drop pre.length = decDigits n ++ post := by
    simp
  have hfirst : ∃ d ds, decDigits n = d :: ds := by
    cases h : decDigits n with
    | nil => exact absurd h (decDigits_ne_nil n)
    | cons d ds => exact ⟨d, ds, rfl⟩
  obtain ⟨d, ds, hd⟩ := hfirst
  have hdd : 48 ≤ d ∧ d ≤ 57 := hall d (by rw [hd]; simp)
  have hdsp : scanSpace d = false := by simp [scanSpace]; omega
  have hd43 : (d == 43) = false := by simp; omega
  have hd45 : (d == 45) = false := by simp; omega
  have htw : (decDigits n ++ post).takeWhile scanDigit = decDigits n := by
    apply takeWhile_append_stops scanDigit _ _ (takeWhile_digits_self _ hall) hpost
  have hcount : (scanDigits (decDigits n ++ post) 0).1 = (decDigits n).length := by
    rw [scanDigits_count_exact, htw]
  have hval : (scanDigits (decDigits n ++ post) 0).2 = n := by
    rw [scanDigits_value_exact]
    unfold scanIntFold
    rw [htw]
    have := decDigits_fold n hn
    unfold scanIntFold at this
    rwa [takeWhile_digits_self _ hall] at this
  have hhead : (decDigits n ++ post).head? = some d := by rw [hd]; simp
  have htwsp : (decDigits n ++ post).takeWhile scanSpace = [] := by
    rw [hd]; simp [hdsp]
  have hsign : ((decDigits n ++ post).head? == some 43 ||
      (decDigits n ++ post).head? == some 45) = false := by
    rw [hhead]; simp [hd43, hd45]
  have hneg : ((decDigits n ++ post).head? == some 45) = false := by
    rw [hhead]; simp; omega
  unfold scanInt
  rw [hdrop]
  dsimp only
  rw [htwsp]
  simp only [List.length_nil, List.drop_zero]
  rw [hsign, hneg]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
  have hne : decDigits n ++ post = d :: (ds ++ post) := by rw [hd]; rfl
  rw [hne]
  unfold scanIntDigits
  simp only [scanDigit_of_digit hdd, ite_true]
  rw [← hne]
  simp [scanIntSignedValue, hcount, hval]


/-! ### Corners -/

theorem storedIndex_succ (x : Int) (h : 0 ≤ x) (n : Nat) :
    storedIndex ((x.toNat + 1 : Nat) : Int) n = x := by
  unfold storedIndex
  rw [resolveIndex_pos (by omega)]
  simp; omega

/-- Write one corner using absolute 1-based indices. -/
def fmtCorner (i : Idx) : RawBytes :=
  let v := decDigits (i.v.toNat + 1)
  if 0 ≤ i.t then
    if 0 ≤ i.n then v ++ 47 :: (decDigits (i.t.toNat + 1) ++ 47 :: decDigits (i.n.toNat + 1))
    else v ++ 47 :: decDigits (i.t.toNat + 1)
  else if 0 ≤ i.n then v ++ 47 :: 47 :: decDigits (i.n.toNat + 1)
  else v

/-- Corners the writer can represent: absolute indices below the scanner cap. -/
def Idx.Writable (i : Idx) : Prop :=
  0 ≤ i.v ∧ i.v < 2147483647 ∧ -1 ≤ i.t ∧ i.t < 2147483647 ∧ -1 ≤ i.n ∧ i.n < 2147483647

private theorem not_digit_slash : scanDigit 47 = false := by decide

private theorem scanInt_dec_at (pre post : List Nat) (x : Int) (hx0 : 0 ≤ x)
    (hx : x < 2147483647)
    (hpost : ∀ b, post.head? = some b → scanDigit b = false) :
    scanInt (pre ++ decDigits (x.toNat + 1) ++ post) pre.length =
      (true, ((x.toNat + 1 : Nat) : Int), pre.length + (decDigits (x.toNat + 1)).length) :=
  scanInt_decDigits pre post (x.toNat + 1) (by omega) trivial hpost

private theorem hp_slash (rest : List Nat) :
    ∀ b, (47 :: rest).head? = some b → scanDigit b = false := by
  intro b hb; simp at hb; subst hb; exact not_digit_slash

private theorem hp_nil : ∀ b, ([] : List Nat).head? = some b → scanDigit b = false := by
  intro b hb; simp at hb

theorem decDigits_head (n : Nat) : ∃ d ds, decDigits n = d :: ds ∧ d ≠ 47 := by
  cases h : decDigits n with
  | nil => exact absurd h (decDigits_ne_nil n)
  | cons d ds =>
    refine ⟨d, ds, rfl, ?_⟩
    have := decDigits_all n d (by rw [h]; simp)
    omega

theorem getElem?_append_cons (pre rest : List Nat) (x : Nat) :
    (pre ++ x :: rest)[pre.length]? = some x := by simp

theorem getElem?_after_sep (pre rest : List Nat) (x : Nat) :
    (pre ++ x :: rest)[pre.length + 1]? = rest[0]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

private theorem scanIdx_dec (pre post : List Nat) (x : Int) (hx0 : 0 ≤ x)
    (hx : x < 2147483647) (m : Nat)
    (hpost : ∀ b, post.head? = some b → scanDigit b = false) :
    scanIdx (pre ++ decDigits (x.toNat + 1) ++ post) pre.length m =
      (x, pre.length + (decDigits (x.toNat + 1)).length) := by
  unfold scanIdx
  rw [scanInt_dec_at pre post x hx0 hx hpost]
  dsimp only
  rw [if_pos rfl, storedIndex_succ x hx0]

theorem parseCornerN_fmt (i : Idx) (hw : i.Writable) (a b c : Nat) :
    parseCornerN (fmtCorner i) a b c = (i, true) := by
  obtain ⟨v, t, n⟩ := i
  rcases hw with ⟨hv0, hv1, ht0, ht1, hn0, hn1⟩
  simp only at hv0 hv1 ht0 ht1 hn0 hn1
  obtain ⟨dt0, dts, hdt, hdt47⟩ := decDigits_head (t.toNat + 1)
  have hok : (resolveIndex ((v.toNat + 1 : Nat) : Int) a).isSome = true := by
    rw [resolveIndex_pos (by omega)]; rfl
  have hstoredV := storedIndex_succ v hv0 a
  have hscanV : ∀ post : List Nat, (∀ b, post.head? = some b → scanDigit b = false) →
      scanInt (decDigits (v.toNat + 1) ++ post) 0 =
        (true, ((v.toNat + 1 : Nat) : Int), (decDigits (v.toNat + 1)).length) := by
    intro post hp
    simpa using scanInt_dec_at [] post v hv0 hv1 hp
  unfold fmtCorner
  simp only
  by_cases ht : 0 ≤ t <;> by_cases hn : 0 ≤ n <;> simp only [ht, hn, ite_true, ite_false]
  · -- v/t/n
    unfold parseCornerN
    rw [hscanV (47 :: (decDigits (t.toNat + 1) ++ 47 :: decDigits (n.toNat + 1)))
      (hp_slash _)]
    simp only [hok, hstoredV]
    rw [getElem?_append_cons]
    simp only [beq_self_eq_true, ite_true]
    have h2 : scanIdx (decDigits (v.toNat + 1) ++ 47 :: (decDigits (t.toNat + 1) ++ 47 ::
        decDigits (n.toNat + 1))) ((decDigits (v.toNat + 1)).length + 1) b =
        (t, (decDigits (v.toNat + 1)).length + 1 + (decDigits (t.toNat + 1)).length) := by
      have := scanIdx_dec (decDigits (v.toNat + 1) ++ [47]) (47 :: decDigits (n.toNat + 1))
        t ht (by omega) b (hp_slash _)
      simpa [List.append_assoc] using this
    have hc2 : (decDigits (v.toNat + 1) ++ 47 :: (decDigits (t.toNat + 1) ++ 47 ::
        decDigits (n.toNat + 1)))[(decDigits (v.toNat + 1)).length + 1]? ≠ some 47 := by
      rw [getElem?_after_sep, hdt]; simp [hdt47]
    have hlt : (decDigits (v.toNat + 1)).length + 1 <
        (decDigits (v.toNat + 1) ++ 47 :: (decDigits (t.toNat + 1) ++ 47 ::
        decDigits (n.toNat + 1))).length := by
      simp only [List.length_append, List.length_cons]
      have : 0 < (decDigits (t.toNat + 1)).length := by
        rw [hdt]; simp
      omega
    simp only [hlt, hc2, decide_true, Bool.true_and, bne_iff_ne, ne_eq, not_false_eq_true,
      ite_true]
    rw [h2]
    simp only
    have h3 : (decDigits (v.toNat + 1) ++ 47 :: (decDigits (t.toNat + 1) ++ 47 ::
        decDigits (n.toNat + 1)))[(decDigits (v.toNat + 1)).length + 1 +
        (decDigits (t.toNat + 1)).length]? = some 47 := by
      have e : decDigits (v.toNat + 1) ++ 47 :: (decDigits (t.toNat + 1) ++ 47 ::
          decDigits (n.toNat + 1)) = (decDigits (v.toNat + 1) ++ 47 :: decDigits (t.toNat + 1))
          ++ 47 :: decDigits (n.toNat + 1) := by simp
      have hl : (decDigits (v.toNat + 1) ++ 47 :: decDigits (t.toNat + 1)).length =
          (decDigits (v.toNat + 1)).length + 1 + (decDigits (t.toNat + 1)).length := by
        simp; omega
      rw [e, ← hl]
      exact getElem?_append_cons _ _ _
    rw [h3]
    simp only [beq_self_eq_true, ite_true]
    have h4 : scanIdx (decDigits (v.toNat + 1) ++ 47 :: (decDigits (t.toNat + 1) ++ 47 ::
        decDigits (n.toNat + 1))) ((decDigits (v.toNat + 1)).length + 1 +
        (decDigits (t.toNat + 1)).length + 1) c = (n, (decDigits (v.toNat + 1)).length + 1 +
        (decDigits (t.toNat + 1)).length + 1 + (decDigits (n.toNat + 1)).length) := by
      have h4 := scanIdx_dec (decDigits (v.toNat + 1) ++ 47 :: (decDigits (t.toNat + 1) ++ [47]))
        [] n hn (by omega) c hp_nil
      have hL : decDigits (v.toNat + 1) ++ 47 :: (decDigits (t.toNat + 1) ++ [47]) ++
          decDigits (n.toNat + 1) ++ [] = decDigits (v.toNat + 1) ++ 47 ::
          (decDigits (t.toNat + 1) ++ 47 :: decDigits (n.toNat + 1)) := by simp
      have hlen : (decDigits (v.toNat + 1) ++ 47 :: (decDigits (t.toNat + 1) ++ [47])).length =
          (decDigits (v.toNat + 1)).length + 1 + (decDigits (t.toNat + 1)).length + 1 := by
        simp; omega
      rw [hL, hlen] at h4
      exact h4
    rw [h4]
  · -- v/t
    have hn' : n = -1 := by omega
    subst hn'
    unfold parseCornerN
    rw [hscanV (47 :: decDigits (t.toNat + 1)) (hp_slash _)]
    simp only [hok, hstoredV]
    rw [getElem?_append_cons]
    simp only [beq_self_eq_true, ite_true]
    have h2 : scanIdx (decDigits (v.toNat + 1) ++ 47 :: decDigits (t.toNat + 1))
        ((decDigits (v.toNat + 1)).length + 1) b =
        (t, (decDigits (v.toNat + 1)).length + 1 + (decDigits (t.toNat + 1)).length) := by
      have := scanIdx_dec (decDigits (v.toNat + 1) ++ [47]) [] t ht (by omega) b hp_nil
      simpa [List.append_assoc] using this
    have hc2 : (decDigits (v.toNat + 1) ++ 47 :: decDigits (t.toNat + 1)  )[(decDigits (v.toNat + 1)).length + 1]? ≠ some 47 := by
      rw [getElem?_after_sep, hdt]; simp [hdt47]
    have hlt : (decDigits (v.toNat + 1)).length + 1 <
        (decDigits (v.toNat + 1) ++ 47 :: decDigits (t.toNat + 1)).length := by
      simp only [List.length_append, List.length_cons]
      have : 0 < (decDigits (t.toNat + 1)).length := by rw [hdt]; simp
      omega
    simp only [hlt, hc2, decide_true, Bool.true_and, bne_iff_ne, ne_eq, not_false_eq_true,
      ite_true]
    rw [h2]
    have hnone : (decDigits (v.toNat + 1) ++ 47 :: decDigits (t.toNat + 1)  )[(decDigits (v.toNat + 1)).length + 1 + (decDigits (t.toNat + 1)).length]? = none := by
      apply List.getElem?_eq_none
      simp
      omega
    simp only [hnone]
    simp
  · -- v//n
    have ht' : t = -1 := by omega
    subst ht'
    unfold parseCornerN
    rw [hscanV (47 :: 47 :: decDigits (n.toNat + 1)) (hp_slash _)]
    simp only [hok, hstoredV]
    rw [getElem?_append_cons]
    simp only [beq_self_eq_true, ite_true]
    have hc2 : (decDigits (v.toNat + 1) ++ 47 :: 47 :: decDigits (n.toNat + 1)  )[(decDigits (v.toNat + 1)).length + 1]? = some 47 := by
      rw [getElem?_after_sep]; simp
    have hc2' : ((decDigits (v.toNat + 1) ++ 47 :: 47 :: decDigits (n.toNat + 1)  )[(decDigits (v.toNat + 1)).length + 1]? != some 47) = false := by
      rw [hc2]; simp
    simp only [hc2', Bool.and_false, Bool.false_eq_true, ite_false]
    simp only [hc2, beq_self_eq_true, ite_true]
    have h4 := scanIdx_dec (decDigits (v.toNat + 1) ++ [47, 47]) [] n hn (by omega) c hp_nil
    have hL : decDigits (v.toNat + 1) ++ [47, 47] ++ decDigits (n.toNat + 1) ++ [] =
        decDigits (v.toNat + 1) ++ 47 :: 47 :: decDigits (n.toNat + 1) := by simp
    have hlen : (decDigits (v.toNat + 1) ++ [47, 47]).length =
        (decDigits (v.toNat + 1)).length + 1 + 1 := by simp
    rw [hL, hlen] at h4
    rw [h4]
  · -- v
    have ht' : t = -1 := by omega
    have hn' : n = -1 := by omega
    subst ht' hn'
    unfold parseCornerN
    have h0 := hscanV [] hp_nil
    rw [List.append_nil] at h0
    rw [h0]
    simp only [hok, hstoredV]
    have hnone : (decDigits (v.toNat + 1))[(decDigits (v.toNat + 1)).length]? = none := by
      apply List.getElem?_eq_none
      simp
    simp only [hnone]
    simp


/-! ### Tokens and lines round-trip -/

/-- A token the writer may emit: nonempty, no space/tab, no line break. -/
def Tok (t : RawBytes) : Prop :=
  t ≠ [] ∧ ∀ c ∈ t, scanSpace c = false ∧ c ≠ 10 ∧ c ≠ 13

theorem tokens_nil : tokens [] = [] := by decide

theorem tokens_single (t : RawBytes) (ht : Tok t) : tokens t = [t] := by
  have h := splitBy_nosep scanSpace t [] [] (fun c hc => (ht.2 c hc).1)
  have e : splitBy scanSpace t = [t] := by
    unfold splitBy
    simpa using h
  unfold tokens
  rw [e]
  simp [ht.1]

theorem tokens_cons_sep (t rest : RawBytes) (ht : Tok t) :
    tokens (t ++ 32 :: rest) = t :: tokens rest := by
  unfold tokens
  rw [splitBy_append_sep scanSpace t rest 32 (fun c hc => (ht.2 c hc).1) (by decide)]
  simp [ht.1]

theorem tokens_intercalate (ts : List RawBytes) (h : ∀ t ∈ ts, Tok t) :
    tokens (List.intercalate [32] ts) = ts := by
  induction ts with
  | nil => simpa using tokens_nil
  | cons t ts ih =>
    cases ts with
    | nil => simpa using tokens_single t (h t (by simp))
    | cons t' ts' =>
      have e : List.intercalate [32] (t :: t' :: ts') =
          t ++ 32 :: List.intercalate [32] (t' :: ts') := by simp [List.intercalate]
      rw [e, tokens_cons_sep t _ (h t (by simp)),
        ih (fun x hx => h x (by simp [hx]))]

def LineOk (l : RawBytes) : Prop := ∀ c ∈ l, c ≠ 10 ∧ c ≠ 13

theorem stripCR_of_ok (l : RawBytes) (h : LineOk l) : stripCR l = l := by
  unfold stripCR
  have : l.getLast? ≠ some 13 := by
    intro hl
    have := List.mem_of_getLast? hl
    exact (h 13 this).2 rfl
  simp [this]

theorem tok_lineOk (ts : List RawBytes) (h : ∀ t ∈ ts, Tok t) :
    LineOk (List.intercalate [32] ts) := by
  induction ts with
  | nil => intro c hc; simp [List.intercalate] at hc
  | cons t ts ih =>
    cases ts with
    | nil =>
      intro c hc
      simp only [List.intercalate_singleton] at hc
      exact ⟨(h t (by simp)).2 c hc |>.2.1, (h t (by simp)).2 c hc |>.2.2⟩
    | cons t' ts' =>
      have e : List.intercalate [32] (t :: t' :: ts') =
          t ++ 32 :: List.intercalate [32] (t' :: ts') := by simp [List.intercalate]
      rw [e]
      have ih' := ih (fun x hx => h x (by simp [hx]))
      intro c hc
      simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | hc | hc
      · exact ⟨((h t (by simp)).2 c hc).2.1, ((h t (by simp)).2 c hc).2.2⟩
      · subst hc; decide
      · exact ih' c hc


def joinLines (ls : List RawBytes) : RawBytes := ls.flatMap (· ++ [10])

theorem splitLines_join (ls : List RawBytes) (h : ∀ l ∈ ls, LineOk l) :
    splitLines (joinLines ls) = ls ++ [[]] := by
  induction ls with
  | nil => decide
  | cons l ls ih =>
    have hl := h l (by simp)
    have e : joinLines (l :: ls) = l ++ 10 :: joinLines ls := by simp [joinLines]
    unfold splitLines at *
    rw [e, splitBy_append_sep (fun c => c == 10) l _ 10 (fun c hc => by simpa using (hl c hc).1)
      (by decide)]
    simp only [List.map_cons, stripCR_of_ok l hl]
    rw [ih (fun x hx => h x (by simp [hx]))]
    rfl

/-! ### Faces as lists -/

def faceList : List Idx → List Nat → List (List Idx)
  | _, [] => []
  | idx, k :: ks => idx.take k :: faceList (idx.drop k) ks

theorem faceList_flatten (idx : List Idx) (fv : List Nat) (h : fv.sum = idx.length) :
    (faceList idx fv).flatten = idx := by
  induction fv generalizing idx with
  | nil => simp at h; simp [faceList]; exact List.length_eq_zero_iff.mp h.symm
  | cons k ks ih =>
    simp only [List.sum_cons] at h
    simp only [faceList, List.flatten_cons]
    rw [ih (idx.drop k) (by simp; omega)]
    simp

theorem faceList_lengths (idx : List Idx) (fv : List Nat) (h : fv.sum = idx.length) :
    (faceList idx fv).map List.length = fv := by
  induction fv generalizing idx with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.sum_cons] at h
    simp only [faceList, List.map_cons]
    rw [ih (idx.drop k) (by simp; omega)]
    simp; omega

theorem faceList_length (idx : List Idx) (fv : List Nat) :
    (faceList idx fv).length = fv.length := by
  induction fv generalizing idx with
  | nil => rfl
  | cons k ks ih => simp [faceList, ih]

theorem faceList_mem (idx : List Idx) (fv : List Nat) :
    ∀ f ∈ faceList idx fv, ∀ i ∈ f, i ∈ idx := by
  induction fv generalizing idx with
  | nil => intro f hf; simp [faceList] at hf
  | cons k ks ih =>
    intro f hf i hi
    simp only [faceList, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact List.mem_of_mem_take hi
    · exact List.mem_of_mem_drop (ih _ f hf i hi)


/-! ### Token facts -/

theorem tok_of_digits_slash (t : RawBytes) (hne : t ≠ [])
    (h : ∀ c ∈ t, (48 ≤ c ∧ c ≤ 57) ∨ c = 47) : Tok t := by
  refine ⟨hne, ?_⟩
  intro c hc
  have := h c hc
  refine ⟨?_, ?_, ?_⟩
  · simp [scanSpace]; omega
  · omega
  · omega

theorem tok_decDigits (n : Nat) : Tok (decDigits n) :=
  tok_of_digits_slash _ (decDigits_ne_nil n) (fun c hc => Or.inl (decDigits_all n c hc))

theorem tok_fmtCorner (i : Idx) : Tok (fmtCorner i) := by
  have hd := fun n => decDigits_all n
  apply tok_of_digits_slash
  · unfold fmtCorner
    by_cases ht : 0 ≤ i.t <;> by_cases hn : 0 ≤ i.n <;> simp [ht, hn, decDigits_ne_nil]
  · intro c hc
    unfold fmtCorner at hc
    by_cases ht : 0 ≤ i.t <;> by_cases hn : 0 ≤ i.n <;>
      simp only [ht, hn, ite_true, ite_false, List.mem_append, List.mem_cons] at hc
    · rcases hc with hc | hc | hc | hc | hc
      · exact Or.inl (hd _ c hc)
      · exact Or.inr hc
      · exact Or.inl (hd _ c hc)
      · exact Or.inr hc
      · exact Or.inl (hd _ c hc)
    · rcases hc with hc | hc | hc
      · exact Or.inl (hd _ c hc)
      · exact Or.inr hc
      · exact Or.inl (hd _ c hc)
    · rcases hc with hc | hc | hc | hc
      · exact Or.inl (hd _ c hc)
      · exact Or.inr hc
      · exact Or.inr hc
      · exact Or.inl (hd _ c hc)
    · exact Or.inl (hd _ c hc)

theorem tok_kw : Tok (kw "v") ∧ Tok (kw "vt") ∧ Tok (kw "vn") ∧ Tok (kw "f") ∧
    Tok (kw "g") ∧ Tok (kw "s") ∧ Tok (kw "usemtl") := by
  unfold Tok; decide


/-! ### Per-directive parse equations -/

section
variable (tess : List Idx → List Tri) (b : Builder) (rest : List RawBytes)

theorem pt_v : parseTokens tess b (kw "v" :: rest) = { b with vs := b.vs ++ [rest] } := by
  simp [parseTokens, kw]

theorem pt_vt : parseTokens tess b (kw "vt" :: rest) = { b with vts := b.vts ++ [rest] } := by
  simp [parseTokens, kw]

theorem pt_vn : parseTokens tess b (kw "vn" :: rest) = { b with vns := b.vns ++ [rest] } := by
  simp [parseTokens, kw]

theorem pt_f : parseTokens tess b (kw "f" :: rest) = handleF tess b rest := by
  simp [parseTokens, kw]

theorem pt_g : parseTokens tess b (kw "g" :: rest) =
    { finalize b with cur := { (finalize b).cur with name := List.intercalate [32] rest } } := by
  simp [parseTokens, kw]

theorem pt_s : parseTokens tess b (kw "s" :: rest) = { b with curSg := parseSg rest } := by
  simp [parseTokens, kw]

theorem pt_usemtl : parseTokens tess b (kw "usemtl" :: rest) =
    { b with curMat :=
      ((b.mats.findIdx? (· = List.intercalate [32] rest)).map Int.ofNat).getD (-1) } := by
  simp [parseTokens, kw]

end


theorem parseSg_dec (g : Nat) (hg : g ≤ 2147483647) : parseSg [decDigits g] = g := by
  obtain ⟨d, ds, hd, _⟩ := decDigits_head g
  have hdd := decDigits_all g d (by rw [hd]; simp)
  have hoff : decDigits g ≠ kw "off" := by
    rw [hd]; simp [kw]; omega
  have hs := scanInt_decDigits [] [] g hg trivial (by intro b hb; simp at hb)
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hs
  unfold parseSg
  simp only [hoff, if_false]
  rw [hs]
  by_cases h0 : g = 0
  · subst h0; simp
  · have : (0 : Int) < g := by omega
    simp [this]
    intro h; omega

/-! ### Writer -/

def nameTok (mats : List RawBytes) (m : Int) : List RawBytes :=
  if m < 0 then [] else [mats.getD m.toNat []]

def faceLines (mats : List RawBytes) :
    List (List Idx) → List Int → List Nat → List (List RawBytes)
  | f :: fs, m :: ms, g :: gs =>
    (kw "usemtl" :: nameTok mats m) :: [kw "s", decDigits g] ::
      (kw "f" :: f.map fmtCorner) :: faceLines mats fs ms gs
  | _, _, _ => []

def shapeLines (mats : List RawBytes) (s : Shape) : List (List RawBytes) :=
  (kw "g" :: [s.name]) :: faceLines mats (faceList s.idx s.fv) s.mid s.sg

def writeTokens (mats : List RawBytes) (vs vts vns : List (List RawBytes))
    (shapes : List Shape) : List (List RawBytes) :=
  vs.map (kw "v" :: ·) ++ vts.map (kw "vt" :: ·) ++ vns.map (kw "vn" :: ·) ++
    shapes.flatMap (shapeLines mats)

def writeObj (mats : List RawBytes) (vs vts vns : List (List RawBytes))
    (shapes : List Shape) : RawBytes :=
  joinLines ((writeTokens mats vs vts vns shapes).map (List.intercalate [32]))

example : writeObj [] [[kw "0", kw "0", kw "0"]] [] []
    [⟨kw "a", [⟨0, -1, -1⟩, ⟨0, -1, -1⟩, ⟨0, -1, -1⟩], [3], [-1], [0]⟩] =
    kw "v 0 0 0\ng a\nusemtl\ns 0\nf 1 1 1\n" := by decide +kernel

/-- Material lookup consistency required for the round-trip. -/
def MatOk (mats : List RawBytes) (m : Int) : Prop :=
  (m < 0 ∧ m = -1 ∧ mats.findIdx? (· = []) = none) ∨
  (0 ≤ m ∧ Tok (mats.getD m.toNat []) ∧
    mats.findIdx? (· = mats.getD m.toNat []) = some m.toNat)

theorem block_parse (tess : List Idx → List Tri) (mats : List RawBytes) (b : Builder)
    (hb : b.triangulate = false) (hm : b.mats = mats)
    (f : List Idx) (m : Int) (g : Nat)
    (hf3 : 3 ≤ f.length) (hfw : ∀ i ∈ f, i.Writable) (hg : g ≤ 2147483647)
    (hmo : MatOk mats m) :
    [kw "usemtl" :: nameTok mats m, [kw "s", decDigits g], kw "f" :: f.map fmtCorner].foldl
      (parseTokens tess) b = addFace { b with curMat := m, curSg := g } f := by
  simp only [List.foldl_cons, List.foldl_nil]
  rw [pt_usemtl, pt_s, pt_f, parseSg_dec g hg]
  have hcs : f.map (fun tok => tok) = f := by simp
  have hcorners : (f.map fmtCorner).map (fun tok =>
      (parseCornerN tok b.vs.length b.vts.length b.vns.length).1) = f := by
    rw [List.map_map]
    rw [List.map_congr_left (g := id) (fun i hi => by
      simp [Function.comp, parseCornerN_fmt i (hfw i hi)])]
    exact List.map_id f
  unfold handleF
  dsimp only
  rw [hcorners]
  have hlen : ¬ f.length < 3 := by omega
  simp only [hlen, if_false]
  unfold emitFace
  simp only [hb, Bool.false_and, if_false]
  have hmat : ((b.mats.findIdx? (· = List.intercalate [32] (nameTok mats m))).map
      Int.ofNat).getD (-1) = m := by
    rw [hm]
    rcases hmo with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have : nameTok mats m = [] := by simp [nameTok, h1]
      rw [this]
      show ((mats.findIdx? (· = [])).map Int.ofNat).getD (-1) = m
      rw [h3]; simp [h2]
    · have : nameTok mats m = [mats.getD m.toNat []] := by
        simp [nameTok]; omega
      rw [this, List.intercalate_singleton, h3]
      simp; omega
  rw [hmat]
  rfl


theorem faces_parse (tess : List Idx → List Tri) (mats : List RawBytes) :
    ∀ (fs : List (List Idx)) (ms : List Int) (gs : List Nat) (b : Builder),
    b.triangulate = false → b.mats = mats →
    ms.length = fs.length → gs.length = fs.length →
    (∀ f ∈ fs, 3 ≤ f.length ∧ ∀ i ∈ f, i.Writable) →
    (∀ m ∈ ms, MatOk mats m) → (∀ g ∈ gs, g ≤ 2147483647) →
    ∃ m' g', (faceLines mats fs ms gs).foldl (parseTokens tess) b =
      { b with cur := { b.cur with
          idx := b.cur.idx ++ fs.flatten
          fv := b.cur.fv ++ fs.map List.length
          mid := b.cur.mid ++ ms
          sg := b.cur.sg ++ gs }, curMat := m', curSg := g' } := by
  intro fs
  induction fs with
  | nil =>
    intro ms gs b hb hm h1 h2 hf hmo hg
    have hms : ms = [] := List.length_eq_zero_iff.mp h1
    have hgs : gs = [] := List.length_eq_zero_iff.mp h2
    subst hms hgs
    exact ⟨b.curMat, b.curSg, by simp [faceLines]⟩
  | cons f fs ih =>
    intro ms gs b hb hm h1 h2 hf hmo hg
    cases ms with
    | nil => simp at h1
    | cons m ms =>
      cases gs with
      | nil => simp at h2
      | cons g gs =>
        have e : faceLines mats (f :: fs) (m :: ms) (g :: gs) =
            [kw "usemtl" :: nameTok mats m, [kw "s", decDigits g],
              kw "f" :: f.map fmtCorner] ++ faceLines mats fs ms gs := rfl
        rw [e, List.foldl_append]
        have hf' := hf f (by simp)
        rw [block_parse tess mats b hb hm f m g hf'.1 hf'.2 (hg g (by simp))
          (hmo m (by simp))]
        obtain ⟨m', g', h⟩ := ih ms gs (addFace { b with curMat := m, curSg := g } f)
          hb hm (by simpa using h1) (by simpa using h2)
          (fun x hx => hf x (by simp [hx])) (fun x hx => hmo x (by simp [hx]))
          (fun x hx => hg x (by simp [hx]))
        refine ⟨m', g', ?_⟩
        rw [h]
        simp [addFace, List.append_assoc]


/-! ### Shapes -/

def ShapeOk (mats : List RawBytes) (s : Shape) : Prop :=
  s.WF ∧ s.fv ≠ [] ∧ Tok s.name ∧ (∀ i ∈ s.idx, i.Writable) ∧
  (∀ g ∈ s.sg, g ≤ 2147483647) ∧ (∀ m ∈ s.mid, MatOk mats m)

def Shape.IsEmpty (s : Shape) : Prop := s.idx = [] ∧ s.fv = [] ∧ s.mid = [] ∧ s.sg = []

theorem finalize_cur_empty (b : Builder) (hb : b.WF) : (finalize b).cur.IsEmpty := by
  unfold finalize
  split
  · rename_i h
    obtain ⟨a1, a2, a3, _, _⟩ := hb.2
    have hfv : b.cur.fv = [] := by simpa using h
    rw [hfv] at a1 a2 a3
    simp at a1 a2 a3
    refine ⟨?_, hfv, ?_, ?_⟩
    · exact List.length_eq_zero_iff.mp a3.symm
    · exact List.length_eq_zero_iff.mp a1.symm
    · exact List.length_eq_zero_iff.mp a2.symm
  · simp [Shape.IsEmpty, Shape.empty]

theorem shape_parse (tess : List Idx → List Tri) (mats : List RawBytes) (b : Builder)
    (hwf : b.WF) (hb : b.triangulate = false) (hm : b.mats = mats)
    (s : Shape) (hs : ShapeOk mats s) :
    ∃ m' g', (shapeLines mats s).foldl (parseTokens tess) b =
      { finalize b with cur := s, curMat := m', curSg := g' } := by
  obtain ⟨hwfs, hne, hname, hw, hg, hmo⟩ := hs
  obtain ⟨w1, w2, w3, w4, w5⟩ := hwfs
  have hemp := finalize_cur_empty b hwf
  obtain ⟨e1, e2, e3, e4⟩ := hemp
  have hfin_tri : (finalize b).triangulate = false := by
    unfold finalize; split <;> simpa using hb
  have hfin_mats : (finalize b).mats = mats := by
    unfold finalize; split <;> simpa using hm
  have hnm : List.intercalate [32] [s.name] = s.name := by simp
  have e : shapeLines mats s = (kw "g" :: [s.name]) ::
      faceLines mats (faceList s.idx s.fv) s.mid s.sg := rfl
  rw [e, List.foldl_cons, pt_g, hnm]
  have hfl := faceList_flatten s.idx s.fv w3
  have hll := faceList_lengths s.idx s.fv w3
  have hlen := faceList_length s.idx s.fv
  obtain ⟨m', g', h⟩ := faces_parse tess mats (faceList s.idx s.fv) s.mid s.sg
    { finalize b with cur := { (finalize b).cur with name := s.name } }
    hfin_tri hfin_mats (by omega) (by omega)
    (by
      intro f hf
      refine ⟨?_, fun i hi => hw i (faceList_mem s.idx s.fv f hf i hi)⟩
      have : f.length ∈ s.fv := by
        rw [← hll]; exact List.mem_map_of_mem hf
      exact w4 _ this)
    hmo hg
  refine ⟨m', g', ?_⟩
  rw [h]
  simp only [e1, e2, e3, e4, List.nil_append, hfl, hll]


theorem finalize_shapes_cur (b : Builder) (h : b.cur.fv ≠ []) :
    (finalize b).shapes = b.shapes ++ [b.cur] := by
  unfold finalize
  simp [h]

theorem shapes_parse (tess : List Idx → List Tri) (mats : List RawBytes) :
    ∀ (ss : List Shape) (b : Builder), b.WF → b.triangulate = false → b.mats = mats →
    (∀ s ∈ ss, ShapeOk mats s) →
    (finalize ((ss.flatMap (shapeLines mats)).foldl (parseTokens tess) b)).shapes =
      (finalize b).shapes ++ ss := by
  intro ss
  induction ss with
  | nil => intro b _ _ _ _; simp
  | cons s ss ih =>
    intro b hwf hb hm hall
    have hs := hall s (by simp)
    obtain ⟨m', g', h1⟩ := shape_parse tess mats b hwf hb hm s hs
    rw [List.flatMap_cons, List.foldl_append, h1]
    have hfinwf := finalize_wf b hwf
    have hwf1 : ({ finalize b with cur := s, curMat := m', curSg := g' } : Builder).WF :=
      ⟨hfinwf.1, hs.1⟩
    have hfin_tri : (finalize b).triangulate = false := by
      unfold finalize; split <;> simpa using hb
    have hfin_mats : (finalize b).mats = mats := by
      unfold finalize; split <;> simpa using hm
    rw [ih _ hwf1 hfin_tri hfin_mats (fun x hx => hall x (by simp [hx]))]
    rw [finalize_shapes_cur ({ finalize b with cur := s, curMat := m', curSg := g' })
      hs.2.1]
    simp

theorem foldl_vs (tess : List Idx → List Tri) (vs : List (List RawBytes)) (b : Builder) :
    (vs.map (kw "v" :: ·)).foldl (parseTokens tess) b = { b with vs := b.vs ++ vs } := by
  induction vs generalizing b with
  | nil => simp
  | cons v vs ih => simp [pt_v, ih, List.append_assoc]

theorem foldl_vts (tess : List Idx → List Tri) (vs : List (List RawBytes)) (b : Builder) :
    (vs.map (kw "vt" :: ·)).foldl (parseTokens tess) b = { b with vts := b.vts ++ vs } := by
  induction vs generalizing b with
  | nil => simp
  | cons v vs ih => simp [pt_vt, ih, List.append_assoc]

theorem foldl_vns (tess : List Idx → List Tri) (vs : List (List RawBytes)) (b : Builder) :
    (vs.map (kw "vn" :: ·)).foldl (parseTokens tess) b = { b with vns := b.vns ++ vs } := by
  induction vs generalizing b with
  | nil => simp
  | cons v vs ih => simp [pt_vn, ih, List.append_assoc]


theorem nameTok_tok (mats : List RawBytes) (m : Int) (h : MatOk mats m) :
    ∀ t ∈ nameTok mats m, Tok t := by
  intro t ht
  unfold nameTok at ht
  split at ht
  · simp at ht
  · rename_i hm
    simp at ht
    subst ht
    rcases h with ⟨h1, _, _⟩ | ⟨_, h2, _⟩
    · omega
    · exact h2

theorem faceLines_tok (mats : List RawBytes) :
    ∀ (fs : List (List Idx)) (ms : List Int) (gs : List Nat),
    (∀ m ∈ ms, MatOk mats m) →
    ∀ ts ∈ faceLines mats fs ms gs, ∀ t ∈ ts, Tok t := by
  intro fs
  induction fs with
  | nil => intro ms gs _ ts hts; cases ms <;> cases gs <;> simp [faceLines] at hts
  | cons f fs ih =>
    intro ms gs hm ts hts
    cases ms with
    | nil => simp [faceLines] at hts
    | cons m ms =>
      cases gs with
      | nil => simp [faceLines] at hts
      | cons g gs =>
        have e : faceLines mats (f :: fs) (m :: ms) (g :: gs) =
            [kw "usemtl" :: nameTok mats m, [kw "s", decDigits g],
              kw "f" :: f.map fmtCorner] ++ faceLines mats fs ms gs := rfl
        rw [e] at hts
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hts
        have hk := tok_kw
        rcases hts with (rfl | rfl | rfl) | hts
        · intro t ht
          simp only [List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact hk.2.2.2.2.2.2
          · exact nameTok_tok mats m (hm m (by simp)) t ht
        · intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hk.2.2.2.2.2.1
          · exact tok_decDigits g
        · intro t ht
          simp only [List.mem_cons, List.mem_map] at ht
          rcases ht with rfl | ⟨i, _, rfl⟩
          · exact hk.2.2.2.1
          · exact tok_fmtCorner i
        · exact ih ms gs (fun x hx => hm x (by simp [hx])) ts hts

theorem writeTokens_tok (mats : List RawBytes) (vs vts vns : List (List RawBytes))
    (shapes : List Shape)
    (hv : ∀ v ∈ vs, ∀ t ∈ v, Tok t) (hvt : ∀ v ∈ vts, ∀ t ∈ v, Tok t)
    (hvn : ∀ v ∈ vns, ∀ t ∈ v, Tok t) (hs : ∀ s ∈ shapes, ShapeOk mats s) :
    ∀ ts ∈ writeTokens mats vs vts vns shapes, ∀ t ∈ ts, Tok t := by
  have hk := tok_kw
  intro ts hts
  unfold writeTokens at hts
  simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hts
  rcases hts with ((⟨v, hv', rfl⟩ | ⟨v, hv', rfl⟩) | ⟨v, hv', rfl⟩) | ⟨s, hs', hts⟩
  · intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hk.1
    · exact hv v hv' t ht
  · intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hk.2.1
    · exact hvt v hv' t ht
  · intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hk.2.2.1
    · exact hvn v hv' t ht
  · have hso := hs s hs'
    unfold shapeLines at hts
    simp only [List.mem_cons] at hts
    rcases hts with rfl | hts
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hk.2.2.2.2.1
      · exact hso.2.2.1
    · exact faceLines_tok mats _ _ _ hso.2.2.2.2.2 ts hts


theorem Builder.init_vs_wf (m : List RawBytes) (t : Bool) (a b c : List (List RawBytes)) :
    ({ Builder.init m t with vs := a, vts := b, vns := c } : Builder).WF :=
  Builder.init_wf m t

/-- **Round-trip.** Writing a scene's topology and parsing it back without
    triangulation yields exactly the same shapes. -/
theorem parse_write (tess : List Idx → List Tri) (mats : List RawBytes)
    (vs vts vns : List (List RawBytes)) (shapes : List Shape)
    (hv : ∀ v ∈ vs, ∀ t ∈ v, Tok t) (hvt : ∀ v ∈ vts, ∀ t ∈ v, Tok t)
    (hvn : ∀ v ∈ vns, ∀ t ∈ v, Tok t) (hs : ∀ s ∈ shapes, ShapeOk mats s) :
    parseObj tess mats false (writeObj mats vs vts vns shapes) = shapes := by
  have htok := writeTokens_tok mats vs vts vns shapes hv hvt hvn hs
  have hlines : ∀ l ∈ (writeTokens mats vs vts vns shapes).map (List.intercalate [32]),
      LineOk l := by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨ts, hts, rfl⟩ := hl
    exact tok_lineOk ts (htok ts hts)
  unfold parseObj writeObj
  rw [splitLines_join _ hlines, List.map_append, List.map_map]
  have hT : (writeTokens mats vs vts vns shapes).map (tokens ∘ List.intercalate [32]) =
      writeTokens mats vs vts vns shapes := by
    rw [List.map_congr_left (g := id) (fun ts hts => by
      simp only [Function.comp, id]
      exact tokens_intercalate ts (htok ts hts))]
    exact List.map_id _
  rw [hT]
  simp only [List.map_cons, List.map_nil, tokens_nil]
  unfold writeTokens
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_vs, foldl_vts, foldl_vns]
  have hparse : ∀ b : Builder, parseTokens tess b [] = b := fun b => rfl
  rw [hparse]
  have key := shapes_parse tess mats shapes
  rw [key _ ?hwf rfl rfl hs]
  · simp [finalize, Builder.init, Shape.empty]
  · exact Builder.init_wf mats false

end Obj

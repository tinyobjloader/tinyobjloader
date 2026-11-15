/-
  Pure model of the OBJ loader's parse and mesh-construction pipeline:
  lines -> tokens -> corners -> faces (optionally triangulated) -> shapes.

  Abstractions (each is allocation/IO/float detail that the topology does not
  depend on):
  * `v`/`vt`/`vn` payloads are kept as raw token text; only their *count*
    matters for relative-index resolution.
  * Allocator, arena, caps/limits and the multithreaded prepass are omitted.
  * The geometric tessellator is a parameter `tess` constrained by
    `TessValid` (see `Obj/Tess.lean`).
  * Lines/points, mtl parsing and free-form geometry are not modelled.
-/
import Obj.Spec
import Obj.Tess
namespace Obj

abbrev RawBytes := List Nat

/-- ASCII keyword as a byte list. -/
def kw (s : String) : RawBytes := s.toList.map Char.toNat

/-- One corner of a face: stored vertex / texcoord / normal indices (-1 = absent). -/
structure Idx where
  v : Int
  t : Int
  n : Int
  deriving DecidableEq, Repr

def Idx.none : Idx := ⟨-1, -1, -1⟩

def Idx.Ok (i : Idx) : Prop := -1 ≤ i.v ∧ -1 ≤ i.t ∧ -1 ≤ i.n

theorem Idx.none_ok : Idx.none.Ok := by simp [Idx.none, Idx.Ok]

theorem storedIndex_ge (idx : Int) (n : Nat) : -1 ≤ storedIndex idx n := by
  unfold storedIndex
  cases h : resolveIndex idx n with
  | none => simp
  | some r => have := resolved_nonneg h; simp; omega

/-- Scan an optional texcoord/normal index: stored index (or -1) and cursor. -/
def scanIdx (tok : RawBytes) (pos num : Nat) : Int × Nat :=
  match scanInt tok pos with
  | (g, x, c) => (if g then storedIndex x num else -1, c)

theorem scanIdx_ge (tok : RawBytes) (pos num : Nat) : -1 ≤ (scanIdx tok pos num).1 := by
  unfold scanIdx
  split
  split
  · exact storedIndex_ge _ _
  · omega

/-- `parse_corner_n`: parse one `v[/[vt][/vn]]` token against explicit counts.
    Returns the stored corner and the C return flag (vertex index in range). -/
def parseCornerN (tok : RawBytes) (numv numvt numvn : Nat) : Idx × Bool :=
  match scanInt tok 0 with
  | (false, _, _) => (Idx.none, false)
  | (true, vi, c1) =>
    let ok := (resolveIndex vi numv).isSome
    let v := storedIndex vi numv
    if tok[c1]? == some 47 then
      let c2 := c1 + 1
      let tc : Int × Nat :=
        if c2 < tok.length && tok[c2]? != some 47 then scanIdx tok c2 numvt
        else (-1, c2)
      let n : Int :=
        if tok[tc.2]? == some 47 then (scanIdx tok (tc.2 + 1) numvn).1 else -1
      (⟨v, tc.1, n⟩, ok)
    else (⟨v, -1, -1⟩, ok)

theorem parseCornerN_ok (tok : RawBytes) (a b c : Nat) :
    (parseCornerN tok a b c).1.Ok := by
  unfold parseCornerN
  split
  · exact Idx.none_ok
  · rename_i vi c1 _
    have hv := storedIndex_ge vi a
    split
    · simp only [Idx.Ok]
      have h1 : ∀ c2 : Nat, -1 ≤ (if c2 < tok.length && tok[c2]? != some 47
          then scanIdx tok c2 b else ((-1 : Int), c2)).1 := by
        intro c2
        split
        · exact scanIdx_ge _ _ _
        · simp
      have h2 : ∀ tc : Int × Nat, -1 ≤ (if tok[tc.2]? == some 47
          then (scanIdx tok (tc.2 + 1) c).1 else (-1 : Int)) := by
        intro tc
        split
        · exact scanIdx_ge _ _ _
        · omega
      exact ⟨hv, h1 _, h2 _⟩
    · simp only [Idx.Ok]; omega

/-- A token without a slash resolves only the vertex component. -/
example : (parseCornerN (kw "7") 10 0 0) = (⟨6, -1, -1⟩, true) := by decide
example : (parseCornerN (kw "7/2/3") 10 5 4) = (⟨6, 1, 2⟩, true) := by decide
example : (parseCornerN (kw "7//3") 10 5 4) = (⟨6, -1, 2⟩, true) := by decide
example : (parseCornerN (kw "-1") 10 0 0) = (⟨9, -1, -1⟩, true) := by decide
example : (parseCornerN (kw "-11") 10 0 0) = (⟨-1, -1, -1⟩, false) := by decide
example : (parseCornerN (kw "0") 10 0 0) = (⟨-1, -1, -1⟩, false) := by decide
example : (parseCornerN (kw "x") 10 0 0) = (Idx.none, false) := by decide

/-- Relative negative vertex index inside range resolves to `n + idx < n`. -/
theorem parseCornerN_neg_vertex (tok : RawBytes) (numv a b : Nat) (vi : Int) (c : Nat)
    (hs : scanInt tok 0 = (true, vi, c)) (hneg : vi < 0) (hn : 0 ≤ (numv : Int) + vi) :
    (parseCornerN tok numv a b).1.v = (numv : Int) + vi ∧
      (parseCornerN tok numv a b).2 = true := by
  have hr := resolveIndex_neg_in hneg hn
  unfold parseCornerN
  rw [hs]
  simp only [hr, storedIndex, Option.getD_some, Option.isSome_some]
  split <;> simp

/-! ### Tokens and lines -/

/-- Split a byte list at every byte satisfying `p` (always returns ≥ 1 piece). -/
def splitBy (p : Nat → Bool) (bs : List Nat) : List (List Nat) :=
  bs.foldr (fun c acc =>
    if p c then [] :: acc
    else match acc with
      | cur :: a => (c :: cur) :: a
      | [] => [[c]]) [[]]

/-- Space/tab separated tokens (empty pieces dropped). -/
def tokens (bs : RawBytes) : List RawBytes :=
  (splitBy scanSpace bs).filter fun t => !t.isEmpty

def stripCR (l : RawBytes) : RawBytes := if l.getLast? == some 13 then l.dropLast else l

def splitLines (bs : RawBytes) : List RawBytes :=
  (splitBy (fun c => c == 10) bs).map stripCR

theorem splitBy_nosep (p : Nat → Bool) (l cur : List Nat) (a : List (List Nat))
    (hl : ∀ c ∈ l, p c = false) :
    l.foldr (fun c acc =>
      if p c then [] :: acc
      else match acc with
        | cur :: a => (c :: cur) :: a
        | [] => [[c]]) (cur :: a) = (l ++ cur) :: a := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : p c = false := hl c (by simp)
    have := ih (fun x hx => hl x (by simp [hx]))
    simp only [List.foldr_cons, this, hc]
    simp

/-- Splitting at a separator after a separator-free prefix peels one piece. -/
theorem splitBy_append_sep (p : Nat → Bool) (l rest : List Nat) (s : Nat)
    (hl : ∀ c ∈ l, p c = false) (hs : p s = true) :
    splitBy p (l ++ s :: rest) = l :: splitBy p rest := by
  unfold splitBy
  rw [List.foldr_append, List.foldr_cons, if_pos hs]
  have := splitBy_nosep p l [] (List.foldr (fun c acc =>
      if p c then [] :: acc
      else match acc with
        | cur :: a => (c :: cur) :: a
        | [] => [[c]]) [[]] rest) hl
  simpa using this

example : tokens (kw "  f 1/2  3//4\t5") = [kw "f", kw "1/2", kw "3//4", kw "5"] := by decide
example : splitLines (kw "a\r\nb\n") = [kw "a", kw "b", []] := by decide

/-! ### Builder -/

structure Shape where
  name : RawBytes
  idx : List Idx
  fv : List Nat
  mid : List Int
  sg : List Nat
  deriving Repr

def Shape.empty (name : RawBytes) : Shape := ⟨name, [], [], [], []⟩

structure Builder where
  vs : List (List RawBytes)
  vts : List (List RawBytes)
  vns : List (List RawBytes)
  shapes : List Shape
  cur : Shape
  curMat : Int
  curSg : Nat
  mats : List RawBytes
  triangulate : Bool

def Builder.init (mats : List RawBytes) (triangulate : Bool) : Builder :=
  ⟨[], [], [], [], Shape.empty [], -1, 0, mats, triangulate⟩

/-- Append one face (`f.length` corners) to the current shape. -/
def addFace (b : Builder) (f : List Idx) : Builder :=
  { b with cur := { b.cur with
      idx := b.cur.idx ++ f
      fv := b.cur.fv ++ [f.length]
      mid := b.cur.mid ++ [b.curMat]
      sg := b.cur.sg ++ [b.curSg] } }

def triFace (cs : List Idx) (t : Tri) : List Idx :=
  [cs.getD t.1 Idx.none, cs.getD t.2.1 Idx.none, cs.getD t.2.2 Idx.none]

/-- `emit_face`: raw polygon when not triangulating or arity ≤ 3; otherwise
    triangulate with `tess` (fan fallback when any vertex index is invalid). -/
def emitFace (tess : List Idx → List Tri) (b : Builder) (cs : List Idx) : Builder :=
  if b.triangulate && decide (3 < cs.length) then
    let posOk := cs.all fun c => decide (0 ≤ c.v ∧ c.v < (b.vs.length : Int))
    let tris := if posOk then tess cs else fanTris cs.length
    (tris.map (triFace cs)).foldl addFace b
  else addFace b cs

def handleF (tess : List Idx → List Tri) (b : Builder) (ts : List RawBytes) : Builder :=
  let cs := ts.map fun tok =>
    (parseCornerN tok b.vs.length b.vts.length b.vns.length).1
  if cs.length < 3 then b else emitFace tess b cs

/-- `finalize_shape`: emit the current shape unless it has no faces. -/
def finalize (b : Builder) : Builder :=
  if b.cur.fv.isEmpty then b
  else { b with shapes := b.shapes ++ [b.cur], cur := Shape.empty b.cur.name }

def parseSg (rest : List RawBytes) : Nat :=
  match rest with
  | [] => 0
  | tk :: _ =>
    if tk = kw "off" then 0
    else match scanInt tk 0 with
      | (true, v, _) => if 0 < v then v.toNat else 0
      | _ => 0

def parseTokens (tess : List Idx → List Tri) (b : Builder) (ts : List RawBytes) : Builder :=
  match ts with
  | [] => b
  | k :: rest =>
    if k = kw "v" then { b with vs := b.vs ++ [rest] }
    else if k = kw "vn" then { b with vns := b.vns ++ [rest] }
    else if k = kw "vt" then { b with vts := b.vts ++ [rest] }
    else if k = kw "f" then handleF tess b rest
    else if k = kw "g" || k = kw "o" then
      let b' := finalize b
      { b' with cur := { b'.cur with name := List.intercalate [32] rest } }
    else if k = kw "s" then { b with curSg := parseSg rest }
    else if k = kw "usemtl" then
      { b with curMat :=
        ((b.mats.findIdx? (· = List.intercalate [32] rest)).map Int.ofNat).getD (-1) }
    else b

def parseObj (tess : List Idx → List Tri) (mats : List RawBytes) (triangulate : Bool)
    (input : RawBytes) : List Shape :=
  let b := ((splitLines input).map tokens).foldl (parseTokens tess) (Builder.init mats triangulate)
  (finalize b).shapes

/-! ### Concrete examples -/

def tessFan : List Idx → List Tri := fun cs => fanTris cs.length

example : (parseObj tessFan [] true (kw "v 0 0 0\nv 1 0 0\nv 1 1 0\nv 0 1 0\nf 1 2 3 4\n")).map
    (fun s => (s.fv, s.idx.map Idx.v)) = [([3, 3], [0, 1, 2, 0, 2, 3])] := by decide

example : (parseObj tessFan [] false (kw "v 0 0 0\nv 1 0 0\nv 1 1 0\nv 0 1 0\nf 1 2 3 4\nf -1 -2 -3\n")).map
    (fun s => (s.fv, s.idx.map Idx.v)) = [([4, 3], [0, 1, 2, 3, 3, 2, 1])] := by decide

example : (parseObj tessFan [kw "red"] false
    (kw "v 0 0 0\nv 1 0 0\nv 0 1 0\ng a\nusemtl red\ns 2\nf 1 2 3\ng b\nf 1 2 3\n")).map
    (fun s => (s.name, s.mid, s.sg)) = [(kw "a", [0], [2]), (kw "b", [0], [2])] := by decide +kernel

/-! ### Well-formedness invariants -/

def Shape.WF (s : Shape) : Prop :=
  s.fv.length = s.mid.length ∧ s.fv.length = s.sg.length ∧
  s.fv.sum = s.idx.length ∧ (∀ k ∈ s.fv, 3 ≤ k) ∧ (∀ i ∈ s.idx, i.Ok)

def Builder.WF (b : Builder) : Prop := (∀ s ∈ b.shapes, s.WF) ∧ b.cur.WF

theorem Shape.empty_wf (n : RawBytes) : (Shape.empty n).WF := by
  simp [Shape.empty, Shape.WF]

theorem Builder.init_wf (m : List RawBytes) (t : Bool) : (Builder.init m t).WF := by
  simp [Builder.init, Builder.WF, Shape.empty_wf]

theorem addFace_wf (b : Builder) (f : List Idx) (hb : b.WF)
    (h3 : 3 ≤ f.length) (hok : ∀ i ∈ f, i.Ok) : (addFace b f).WF := by
  obtain ⟨hs, hc⟩ := hb
  obtain ⟨a1, a2, a3, a4, a5⟩ := hc
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [addFace]
  · simp [a1]
  · simp [a2]
  · simp [a3]
  · intro k hk
    simp at hk
    rcases hk with hk | hk
    · exact a4 k hk
    · omega
  · intro i hi
    simp at hi
    rcases hi with hi | hi
    · exact a5 i hi
    · exact hok i hi

theorem addFace_shapes (b : Builder) (f : List Idx) : (addFace b f).shapes = b.shapes := rfl
theorem addFace_vs (b : Builder) (f : List Idx) : (addFace b f).vs = b.vs := rfl

theorem finalize_wf (b : Builder) (hb : b.WF) : (finalize b).WF := by
  unfold finalize
  split
  · exact hb
  · refine ⟨?_, Shape.empty_wf _⟩
    intro s hs
    simp at hs
    rcases hs with hs | hs
    · exact hb.1 s hs
    · subst hs; exact hb.2

theorem foldl_addFace_wf (b : Builder) (fs : List (List Idx)) (hb : b.WF)
    (h : ∀ f ∈ fs, 3 ≤ f.length ∧ ∀ i ∈ f, i.Ok) : (fs.foldl addFace b).WF := by
  induction fs generalizing b with
  | nil => exact hb
  | cons f fs ih =>
    apply ih
    · exact addFace_wf b f hb (h f (by simp)).1 (h f (by simp)).2
    · intro g hg; exact h g (by simp [hg])

theorem triFace_ok (cs : List Idx) (hok : ∀ i ∈ cs, i.Ok) (t : Tri) :
    (triFace cs t).length = 3 ∧ ∀ i ∈ triFace cs t, i.Ok := by
  refine ⟨rfl, ?_⟩
  intro i hi
  simp only [triFace, List.mem_cons, List.not_mem_nil, or_false] at hi
  have hd : ∀ k : Nat, (cs.getD k Idx.none).Ok := by
    intro k
    by_cases hk : k < cs.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact hok _ (List.getElem_mem hk)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : cs.length ≤ k)]
      exact Idx.none_ok
  rcases hi with rfl | rfl | rfl <;> exact hd _

theorem emitFace_wf (tess : List Idx → List Tri) (b : Builder) (cs : List Idx)
    (hb : b.WF) (h3 : 3 ≤ cs.length) (hok : ∀ i ∈ cs, i.Ok) :
    (emitFace tess b cs).WF := by
  unfold emitFace
  split
  · apply foldl_addFace_wf _ _ hb
    intro f hf
    simp only [List.mem_map] at hf
    obtain ⟨t, _, rfl⟩ := hf
    have := triFace_ok cs hok t
    exact ⟨by omega, this.2⟩
  · exact addFace_wf b cs hb h3 hok

theorem handleF_wf (tess : List Idx → List Tri) (b : Builder) (ts : List RawBytes)
    (hb : b.WF) : (handleF tess b ts).WF := by
  unfold handleF
  dsimp only
  split
  · exact hb
  · rename_i h
    apply emitFace_wf tess b _ hb (by omega)
    intro i hi
    simp only [List.mem_map] at hi
    obtain ⟨tok, _, rfl⟩ := hi
    exact parseCornerN_ok tok _ _ _

theorem parseTokens_wf (tess : List Idx → List Tri) (b : Builder) (ts : List RawBytes)
    (hb : b.WF) : (parseTokens tess b ts).WF := by
  unfold parseTokens
  split
  · exact hb
  · rename_i k rest
    split
    · exact hb
    · split
      · exact hb
      · split
        · exact hb
        · split
          · exact handleF_wf tess b rest hb
          · split
            · have := finalize_wf b hb
              exact ⟨this.1, by simpa [Shape.WF] using this.2⟩
            · split
              · exact hb
              · split
                · exact hb
                · exact hb

theorem parseObj_wf (tess : List Idx → List Tri) (mats : List RawBytes) (tri : Bool)
    (input : RawBytes) : ∀ s ∈ parseObj tess mats tri input, s.WF := by
  unfold parseObj
  have key : ∀ (ls : List (List RawBytes)) (b : Builder), b.WF →
      (ls.foldl (parseTokens tess) b).WF := by
    intro ls
    induction ls with
    | nil => intro b hb; exact hb
    | cons l ls ih => intro b hb; exact ih _ (parseTokens_wf tess b l hb)
  exact (finalize_wf _ (key _ _ (Builder.init_wf mats tri))).1


/-! ### Triangulation link -/

theorem foldl_addFace_cur (fs : List (List Idx)) (b : Builder) :
    (fs.foldl addFace b).cur.fv = b.cur.fv ++ fs.map List.length ∧
    (fs.foldl addFace b).cur.idx = b.cur.idx ++ fs.flatten := by
  induction fs generalizing b with
  | nil => simp
  | cons f fs ih =>
    obtain ⟨h1, h2⟩ := ih (addFace b f)
    refine ⟨?_, ?_⟩
    · rw [List.foldl_cons, h1]; simp [addFace, List.append_assoc]
    · rw [List.foldl_cons, h2]; simp [addFace, List.append_assoc]

/-- With a structurally valid tessellator, an `n`-corner face (n > 3) with
    triangulation enabled becomes exactly `n - 2` triangle faces. -/
theorem emitFace_triangulates (tess : List Idx → List Tri)
    (hs : ∀ cs : List Idx, 3 ≤ cs.length → TessValid cs.length (tess cs))
    (b : Builder) (cs : List Idx) (htri : b.triangulate = true) (h : 3 < cs.length) :
    (emitFace tess b cs).cur.fv = b.cur.fv ++ List.replicate (cs.length - 2) 3 ∧
    (emitFace tess b cs).cur.idx.length = b.cur.idx.length + 3 * (cs.length - 2) := by
  unfold emitFace
  simp only [htri, h, decide_true, Bool.and_self, if_true]
  have hl : ∀ tris : List Tri, tris.length = cs.length - 2 →
      ((tris.map (triFace cs)).foldl addFace b).cur.fv =
        b.cur.fv ++ List.replicate (cs.length - 2) 3 ∧
      ((tris.map (triFace cs)).foldl addFace b).cur.idx.length =
        b.cur.idx.length + 3 * (cs.length - 2) := by
    intro tris htl
    obtain ⟨h1, h2⟩ := foldl_addFace_cur (tris.map (triFace cs)) b
    have hm : (tris.map (triFace cs)).map List.length = List.replicate (cs.length - 2) 3 := by
      rw [List.map_map, ← htl]
      have : (List.length ∘ triFace cs) = fun _ => 3 := by funext t; rfl
      rw [this]; exact List.map_const'
    have hfl : ((tris.map (triFace cs)).flatten).length = 3 * (cs.length - 2) := by
      rw [List.length_flatten, hm]; simp; omega
    exact ⟨by rw [h1, hm], by rw [h2, List.length_append, hfl]⟩
  split
  · exact hl _ (hs cs (by omega)).1
  · exact hl _ (fanTris_length _)

end Obj

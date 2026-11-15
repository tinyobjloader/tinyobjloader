import Tess.RealTopology
import Tess.Check
noncomputable section
namespace Tess.RealGeometry
open Set
abbrev Line := ℝ × ℝ × ℝ
def lineValue (l : Line) (p : P2) : ℝ := affineValue l.1 l.2.1 l.2.2 p
def nonconstant (l : Line) : Prop := l.1≠0 ∨ l.2.1≠0
def horizontal (a : P2) : Line := (0,1,-a.2)
def edgeLine (a b : P2) : Line := (a.2-b.2,b.1-a.1,a.1*b.2-a.2*b.1)
def faceLines (points : Nat → P2) (f : Tess.Face) : List Line :=
  [horizontal (points f.a),horizontal (points f.b),horizontal (points f.c),
   edgeLine (points f.a) (points f.b),edgeLine (points f.b) (points f.c),edgeLine (points f.c) (points f.a)]
def arrangement (points : Nat → P2) (faces : List Tess.Face) : List Line := faces.flatMap (faceLines points)
def genericSet (lines : List Line) : Set P2 := {p | ∀ l ∈ lines, lineValue l p ≠ 0}

theorem edgeLine_value (a b p : P2) : lineValue (edgeLine a b) p = orient a b p := by
  unfold lineValue edgeLine affineValue orient
  dsimp only
  ring

theorem edgeLine_nonconstant (a b : P2) (h : a≠b) : nonconstant (edgeLine a b) := by
  change a.2-b.2≠0 ∨ b.1-a.1≠0
  by_cases hy : a.2-b.2=0
  · right
    intro hx
    apply h
    apply Prod.ext <;> linarith
  · exact Or.inl hy

theorem generic_open (lines : List Line) : IsOpen (genericSet lines) := by
  induction lines with
  | nil => simpa [genericSet] using isOpen_univ (X := P2)
  | cons l tail ih =>
    have hs : genericSet (l::tail) = {p | lineValue l p ≠ 0} ∩ genericSet tail := by
      ext p; simp [genericSet]
    rw [hs]
    exact (affineComplement_open l.1 l.2.1 l.2.2).inter ih

theorem generic_dense (lines : List Line) (h : ∀ l ∈ lines, nonconstant l) : Dense (genericSet lines) := by
  induction lines with
  | nil => simpa [genericSet] using dense_univ (X := P2)
  | cons l tail ih =>
    have hs : genericSet (l::tail) = {p | lineValue l p ≠ 0} ∩ genericSet tail := by
      ext p; simp [genericSet]
    rw [hs]
    exact (affineComplement_dense l.1 l.2.1 l.2.2 (h l (by simp))).inter_of_isOpen_left
      (ih (fun x hx => h x (by simp [hx]))) (affineComplement_open l.1 l.2.1 l.2.2)

theorem orient_cycle (a b c : P2) : orient b c a = orient a b c := by unfold orient; ring

theorem faceLines_nonconstant (points : Nat → P2) (f : Tess.Face)
    (h : 0 < orient (points f.a) (points f.b) (points f.c)) :
    ∀ l ∈ faceLines points f, nonconstant l := by
  have hab : points f.a ≠ points f.b := by intro he; rw [he] at h; simpa [orient] using h
  have hbc : points f.b ≠ points f.c := by intro he; rw [he] at h; simp only [orient] at h; nlinarith
  have hca : points f.c ≠ points f.a := by intro he; rw [he] at h; simpa [orient] using h
  intro l hl
  simp only [faceLines,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl|rfl|rfl|rfl|rfl
  · simp [nonconstant,horizontal]
  · simp [nonconstant,horizontal]
  · simp [nonconstant,horizontal]
  · exact edgeLine_nonconstant _ _ hab
  · exact edgeLine_nonconstant _ _ hbc
  · exact edgeLine_nonconstant _ _ hca

theorem arrangement_dense (points : Nat → P2) (faces : List Tess.Face)
    (h : ∀ f ∈ faces, 0 < orient (points f.a) (points f.b) (points f.c)) :
    Dense (genericSet (arrangement points faces)) := by
  apply generic_dense
  intro l hl
  obtain ⟨f,hf,hl⟩ := List.mem_flatMap.mp hl
  exact faceLines_nonconstant points f (h f hf) l hl

theorem generic_face (points : Nat → P2) (faces : List Tess.Face) (f : Tess.Face)
    (hf : f ∈ faces) (p : P2) (generic : p ∈ genericSet (arrangement points faces)) :
    (points f.a).2 ≠ p.2 ∧ (points f.b).2 ≠ p.2 ∧ (points f.c).2 ≠ p.2 ∧
    orient (points f.a) (points f.b) p ≠ 0 ∧ orient (points f.b) (points f.c) p ≠ 0 ∧
    orient (points f.c) (points f.a) p ≠ 0 := by
  have every : ∀ l ∈ faceLines points f, lineValue l p ≠ 0 := by
    intro l hl
    exact generic l (List.mem_flatMap.mpr ⟨f,hf,hl⟩)
  have ha := every (horizontal (points f.a)) (by simp [faceLines])
  have hb := every (horizontal (points f.b)) (by simp [faceLines])
  have hc := every (horizontal (points f.c)) (by simp [faceLines])
  have hab := every (edgeLine (points f.a) (points f.b)) (by simp [faceLines])
  have hbc := every (edgeLine (points f.b) (points f.c)) (by simp [faceLines])
  have hca := every (edgeLine (points f.c) (points f.a)) (by simp [faceLines])
  rw [edgeLine_value] at hab hbc hca
  simp only [lineValue,horizontal,affineValue,zero_mul,one_mul,zero_add,← sub_eq_add_neg] at ha hb hc
  exact ⟨Ne.symm (sub_ne_zero.mp ha),Ne.symm (sub_ne_zero.mp hb),Ne.symm (sub_ne_zero.mp hc),hab,hbc,hca⟩
end Tess.RealGeometry

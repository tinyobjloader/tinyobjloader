/-
  Pure specification of polygon triangulation as used by the OBJ loader.

  The geometric ear-clipping algorithm itself is not specified here; the
  loader-level contract is structural: for a polygon with `n >= 3` corners the
  tessellator emits exactly `n - 2` triangles whose corner references are all
  `< n` (`TessValid`).  The fan triangulation `(0, t+1, t+2)` is the concrete
  fallback used by the C loader for faces with an invalid vertex index, and it
  is also the `ASSUME_CONVEX` / reflex-free fast path.
-/
namespace Obj

/-- A triangle is a triple of ring-local corner positions. -/
abbrev Tri := Nat × Nat × Nat

/-- Fan triangulation of an `n`-gon rooted at corner 0. -/
def fanTris (n : Nat) : List Tri :=
  (List.range (n - 2)).map fun t => (0, t + 1, t + 2)

/-- Structural contract of any triangulation of an `n`-corner ring. -/
def TessValid (n : Nat) (ts : List Tri) : Prop :=
  ts.length = n - 2 ∧ ∀ t ∈ ts, t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n

theorem fanTris_length (n : Nat) : (fanTris n).length = n - 2 := by
  simp [fanTris]

theorem fanTris_valid (n : Nat) (h : 3 ≤ n) : TessValid n (fanTris n) := by
  refine ⟨fanTris_length n, ?_⟩
  intro t ht
  simp only [fanTris, List.mem_map, List.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  simp only
  omega

theorem fanTris_three : fanTris 3 = [(0, 1, 2)] := by decide

theorem fanTris_four : fanTris 4 = [(0, 1, 2), (0, 2, 3)] := by decide

/-- Fan triangles are non-degenerate as index triples (pairwise distinct). -/
theorem fanTris_distinct (n : Nat) :
    ∀ t ∈ fanTris n, t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 := by
  intro t ht
  simp only [fanTris, List.mem_map, List.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  simp only
  omega

/-! ## Polygon-core triangulations (`tobj_tess_polygon_core`, n = 3 and n = 4)

The polygon core in `tobj_tess_impl.inc` special-cases small polygons before
falling back to the general 2-D ear-clipping path.  A triangle (`n = 3`) is
emitted as the single triple `(0, 1, 2)`; a quad (`n = 4`) is split along one of
its two diagonals.  The choice *which* diagonal is decided by floating-point
orientation tests, so it is left as an explicit `split02` input here: the
specification covers both admissible triangulations and the C side is
responsible for picking one.  The geometry (whether the split is degenerate)
does not affect the structural contract, which is `TessValid`. -/

/-- Triangulation of a triangle: the single corner triple. -/
def polyTri : List Tri := [(0, 1, 2)]

/-- Triangulation of a quad.  `split02 = true` cuts along the 0–2 diagonal,
    `split02 = false` along the 1–3 diagonal. -/
def quadTris (split02 : Bool) : List Tri :=
  if split02 then [(0, 1, 2), (0, 2, 3)] else [(0, 1, 3), (1, 2, 3)]

/-- Triangulation selected by the polygon core for `n = 3` and `n = 4`.
    Every larger polygon uses the general 2-D path, whose structural contract is
    `TessValid`; the pure fallback shape is the fan. -/
def polyTris (n : Nat) (split02 : Bool) : List Tri :=
  if n = 3 then polyTri else if n = 4 then quadTris split02 else fanTris n

theorem polyTri_valid : TessValid 3 polyTri := by
  refine ⟨rfl, ?_⟩
  intro t ht
  simp only [polyTri, List.mem_cons, List.not_mem_nil, or_false] at ht
  obtain rfl := ht
  simp

theorem quadTris_valid (split02 : Bool) : TessValid 4 (quadTris split02) := by
  cases split02
  · refine ⟨rfl, ?_⟩
    intro t ht
    simp only [quadTris, Bool.false_eq_true, if_false, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp
    · simp
  · refine ⟨rfl, ?_⟩
    intro t ht
    simp only [quadTris, if_true, List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl
    · simp
    · simp

/-- The polygon-core triangulation is structurally valid for every `n` it
    handles (3 or 4); the general path is covered by `fanTris_valid`. -/
theorem polyTris_valid (n : Nat) (split02 : Bool) (h3 : 3 ≤ n) (h4 : n ≤ 4) :
    TessValid n (polyTris n split02) := by
  by_cases hn3 : n = 3
  · subst hn3
    simpa [polyTris] using polyTri_valid
  · have hn4 : n = 4 := by omega
    subst hn4
    simpa [polyTris, show (4 : Nat) ≠ 3 by decide] using quadTris_valid split02

/-- For a triangle the polygon core agrees with the fan triangulation. -/
theorem polyTris_three (split02 : Bool) : polyTris 3 split02 = fanTris 3 := by
  simp [polyTris, polyTri, fanTris]

/-- Both quad splits emit `n - 2 = 2` triangles. -/
theorem quadTris_length (split02 : Bool) : (quadTris split02).length = 2 := by
  cases split02 <;> rfl

/-- The polygon core writes `3*(n-2)` index slots for every `n` it handles,
    matching the C `need_out = tri * 3` capacity check. -/
theorem polyTris_length (n : Nat) (split02 : Bool) (h3 : 3 ≤ n) (h4 : n ≤ 4) :
    (polyTris n split02).length = n - 2 := by
  by_cases hn3 : n = 3
  · subst hn3; rfl
  · have hn4 : n = 4 := by omega
    subst hn4
    simpa [polyTris, show (4 : Nat) ≠ 3 by decide] using quadTris_length split02

/-- Corner references of the polygon-core triangulation all lie in the ring:
    every triangle satisfies `TessValid`'s in-range clause. -/
theorem polyTris_corners (n : Nat) (split02 : Bool) (h3 : 3 ≤ n) (h4 : n ≤ 4) :
    ∀ t ∈ polyTris n split02, t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n :=
  (polyTris_valid n split02 h3 h4).2

/-- Map ring-local triangles through the polygon's corner list. -/
def emitTris {α : Type} (cs : List α) (d : α) (ts : List Tri) : List α :=
  ts.flatMap fun t => [cs.getD t.1 d, cs.getD t.2.1 d, cs.getD t.2.2 d]

theorem emitTris_length {α : Type} (cs : List α) (d : α) (ts : List Tri) :
    (emitTris cs d ts).length = 3 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [emitTris] at *; omega

theorem emitTris_append {α : Type} (cs : List α) (d : α) (a b : List Tri) :
    emitTris cs d (a ++ b) = emitTris cs d a ++ emitTris cs d b := by
  simp [emitTris, List.flatMap_append]

/-- Every emitted corner is drawn from the input polygon when triangles are valid. -/
theorem emitTris_mem {α : Type} (cs : List α) (d : α) (ts : List Tri)
    (hv : ∀ t ∈ ts, t.1 < cs.length ∧ t.2.1 < cs.length ∧ t.2.2 < cs.length) :
    ∀ x ∈ emitTris cs d ts, x ∈ cs := by
  intro x hx
  simp only [emitTris, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨t, ht, hx⟩ := hx
  obtain ⟨h1, h2, h3⟩ := hv t ht
  rcases hx with rfl | rfl | rfl
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h3]

/-- The triangle branch of the polygon core, mapped through the corner list,
    emits exactly the first three corners in order. -/
theorem emitTris_polyTri {α : Type} (cs : List α) (d : α) (x y z : α)
    (h0 : cs[0]? = some x) (h1 : cs[1]? = some y) (h2 : cs[2]? = some z) :
    emitTris cs d polyTri = [x, y, z] := by
  simp only [polyTri, emitTris, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [show cs.getD 0 d = x from by simp [List.getD_eq_getElem?_getD, h0],
      show cs.getD 1 d = y from by simp [List.getD_eq_getElem?_getD, h1],
      show cs.getD 2 d = z from by simp [List.getD_eq_getElem?_getD, h2]]

/-- A quad split along the 0–2 diagonal emits its two triangles in order. -/
theorem emitTris_quad02 {α : Type} (cs : List α) (d : α) (a b c e : α)
    (h0 : cs[0]? = some a) (h1 : cs[1]? = some b) (h2 : cs[2]? = some c)
    (h3 : cs[3]? = some e) :
    emitTris cs d (quadTris true) = [a, b, c, a, c, e] := by
  simp only [quadTris, if_true, emitTris, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [show cs.getD 0 d = a from by simp [List.getD_eq_getElem?_getD, h0],
      show cs.getD 1 d = b from by simp [List.getD_eq_getElem?_getD, h1],
      show cs.getD 2 d = c from by simp [List.getD_eq_getElem?_getD, h2],
      show cs.getD 3 d = e from by simp [List.getD_eq_getElem?_getD, h3]]
  rfl

/-- A quad split along the 1–3 diagonal emits its two triangles in order. -/
theorem emitTris_quad13 {α : Type} (cs : List α) (d : α) (a b c e : α)
    (h0 : cs[0]? = some a) (h1 : cs[1]? = some b) (h2 : cs[2]? = some c)
    (h3 : cs[3]? = some e) :
    emitTris cs d (quadTris false) = [a, b, e, b, c, e] := by
  simp only [quadTris, Bool.false_eq_true, if_false, emitTris,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show cs.getD 0 d = a from by simp [List.getD_eq_getElem?_getD, h0],
      show cs.getD 1 d = b from by simp [List.getD_eq_getElem?_getD, h1],
      show cs.getD 2 d = c from by simp [List.getD_eq_getElem?_getD, h2],
      show cs.getD 3 d = e from by simp [List.getD_eq_getElem?_getD, h3]]
  rfl

end Obj

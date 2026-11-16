import MtlxSpec.Doc

/-!
# MaterialX-in-MTL: lexical layer

Normative reference for `doc/mtlx-mtl.md`.  A `.mtl` file is a sequence of lines; each line
is split into tokens. The C implementation (`tiny_obj_c_impl.inc`, `tobj_mtlx_*`) must agree
with `tokenize` on every line (checked differentially by `mtlxmtl` vs `tests/mtlx_dump`).

* Lines are separated by `\n`; a trailing `\r` is dropped.
* A line whose first non-blank character is `#` is a comment.
* Blanks are space and tab. A token is a maximal run of non-blank characters, except that a
  token starting with `"` extends to the next `"`; the quotes are removed and the content may
  contain blanks. A quote with no closing quote makes the line malformed (`none`).
-/
namespace TobjMtlx
open MtlxSpec

def isBlank (c : Char) : Bool := c == ' ' || c == '\t'

/-- Read the rest of a plain (unquoted) token. -/
def plainTok : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if isBlank c then ([], c :: cs) else
      let (t, r) := plainTok cs
      (c :: t, r)

/-- Read the content of a quoted token after the opening quote. -/
def quotedTok : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs => if c == '"' then some ([], cs) else
      (quotedTok cs).map fun (t, r) => (c :: t, r)

theorem plainTok_length (cs : List Char) : (plainTok cs).2.length ≤ cs.length := by
  induction cs with
  | nil => simp [plainTok]
  | cons c cs ih => unfold plainTok; split <;> simp; omega

theorem quotedTok_length (cs : List Char) (t r : List Char) (h : quotedTok cs = some (t, r)) :
    r.length < cs.length + 1 := by
  induction cs generalizing t r with
  | nil => simp [quotedTok] at h
  | cons c cs ih =>
    unfold quotedTok at h
    split at h
    · simp at h; obtain ⟨_, rfl⟩ := h; simp
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨t', r'⟩, h1, h2⟩ := h
      simp at h2; obtain ⟨_, rfl⟩ := h2
      have := ih t' r' h1; simp; omega

/-- Split one line into tokens. -/
def tokenize (cs : List Char) : Option (List (List Char)) :=
  match cs with
  | [] => some []
  | c :: rest =>
    if isBlank c then tokenize rest
    else if c == '"' then
      match h : quotedTok rest with
      | none => none
      | some (t, r) =>
        have : r.length < rest.length + 1 := quotedTok_length rest t r h
        (tokenize r).map (t :: ·)
    else
      have : (plainTok rest).2.length < rest.length + 1 := by
        have := plainTok_length rest; omega
      (tokenize (plainTok rest).2).map ((c :: (plainTok rest).1) :: ·)
termination_by cs.length

/-- Remove a trailing carriage return. -/
def dropCR (cs : List Char) : List Char :=
  match cs.getLast? with
  | some '\r' => cs.dropLast
  | _ => cs

def isComment (cs : List Char) : Bool :=
  match cs.dropWhile isBlank with
  | '#' :: _ => true
  | _ => false

def lines (text : List Char) : List (List Char) := (splitOn '\n' text).map dropCR

/-- The text after the first token, with surrounding blanks removed. `newmtl` names are the
whole remainder, as in tinyobjloader. -/
def restAfterKeyword (cs : List Char) : List Char :=
  let s := cs.dropWhile isBlank
  let s := s.dropWhile (fun c => !isBlank c)
  let s := s.dropWhile isBlank
  (s.reverse.dropWhile isBlank).reverse

/-! ## Lexical theorems -/

/-- A plain token followed by a blank is read back exactly. -/
theorem plainTok_append (t rest : List Char) (ht : ∀ c ∈ t, isBlank c = false)
    (b : Char) (hb : isBlank b = true) :
    plainTok (t ++ b :: rest) = (t, b :: rest) := by
  induction t with
  | nil => simp [plainTok, hb]
  | cons c t ih =>
    have hc := ht c List.mem_cons_self
    have ih := ih (fun x hx => ht x (List.mem_cons_of_mem _ hx))
    simp [plainTok, hc, ih]

theorem plainTok_all (t : List Char) (ht : ∀ c ∈ t, isBlank c = false) :
    plainTok t = (t, []) := by
  induction t with
  | nil => simp [plainTok]
  | cons c t ih =>
    have hc := ht c List.mem_cons_self
    have ih := ih (fun x hx => ht x (List.mem_cons_of_mem _ hx))
    simp [plainTok, hc, ih]

/-- A token is *plain* when it is non-empty, contains no blank, and does not start with a
quote. Plain tokens are printed unquoted by the canonical writer. -/
def plainToken (t : List Char) : Bool :=
  match t with
  | [] => false
  | c :: _ => c != '"' && t.all (fun x => !isBlank x)

/-- Canonical join: tokens separated by one space. -/
def joinTokens : List (List Char) → List Char
  | [] => []
  | [t] => t
  | t :: ts => t ++ ' ' :: joinTokens ts

/-- **Round trip**: the canonical join of plain tokens tokenizes back to the same tokens. -/
theorem tokenize_joinTokens (ts : List (List Char)) (h : ∀ t ∈ ts, plainToken t = true) :
    tokenize (joinTokens ts) = some ts := by
  induction ts with
  | nil => simp [joinTokens, tokenize]
  | cons t ts ih =>
    have ht := h t List.mem_cons_self
    have ih := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    match t, ht with
    | c :: t', ht =>
      simp only [plainToken, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true] at ht
      obtain ⟨hq, hall⟩ := ht
      have hc : isBlank c = false := hall c List.mem_cons_self
      have ht' : ∀ x ∈ t', isBlank x = false := fun x hx => hall x (List.mem_cons_of_mem _ hx)
      have hq' : (c == '"') = false := by simpa using hq
      cases ts with
      | nil =>
        rw [joinTokens, tokenize]
        simp [hc, hq', plainTok_all t' ht', tokenize]
      | cons u us =>
        have hj : joinTokens ((c :: t') :: u :: us) = c :: (t' ++ ' ' :: joinTokens (u :: us)) :=
          rfl
        rw [hj, tokenize]
        simp only [hc, hq', Bool.false_eq_true, ite_false]
        rw [plainTok_append t' _ ht' ' ' (by decide)]
        simp only [tokenize, isBlank, beq_self_eq_true, Bool.true_or, ite_true]
        rw [ih]; rfl

end TobjMtlx

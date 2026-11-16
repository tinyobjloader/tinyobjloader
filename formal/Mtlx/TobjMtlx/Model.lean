import TobjMtlx.Syntax
import MtlxSpec.GraphAcyclic

/-!
# MaterialX-in-MTL: material model, well-formedness and lowering

Grammar of the extension lines (keyword = first token, scoped to the current `newmtl`):

```
mtlx_version  <major.minor>
mtlx_surface  <name> <category>                 -- surface shader node
mtlx_node     <name> <category> <type>          -- single-output node
mtlx_input    <node>.<input> <type> <value...>  -- constant input
connectmtl    <src>[.out] <dst>.<input>         -- connection
mtlx_include  <path>                            -- XInclude of a nodedef library
mtlx_colorspace <node>.<input> <colorspace>     -- colorspace of a constant input
```

Any other keyword is ignored here (classic MTL keys are the fallback for old readers).
A material that uses the extension and fails `check` is *dropped from the extension*: the
loader reports a warning and keeps only its classic keys.
-/
namespace TobjMtlx
open MtlxSpec

abbrev S := List Char

structure NodeDecl where
  name : S
  cat : S
  ty : S
  deriving Repr, DecidableEq

structure InDecl where
  node : S
  port : S
  ty : S
  value : S        -- canonical value text (numbers joined by ", ")
  deriving Repr, DecidableEq

structure Conn where
  src : S
  srcOut : Option S
  dst : S
  port : S
  deriving Repr, DecidableEq

structure Mat where
  name : S
  version : List S := []
  surface : List (S × S) := []
  nodes : List NodeDecl := []
  inputs : List InDecl := []
  conns : List Conn := []
  includes : List S := []
  colorspaces : List (S × S × S) := []   -- node, input, colorspace
  errors : List S := []
  deriving Repr, DecidableEq

def Mat.ext (m : Mat) : Bool :=
  !(m.version.isEmpty && m.surface.isEmpty && m.nodes.isEmpty && m.inputs.isEmpty &&
    m.conns.isEmpty && m.includes.isEmpty && m.colorspaces.isEmpty && m.errors.isEmpty)

/-- Split `a.b` at the first dot. -/
def splitDot (t : S) : S × Option S :=
  match t.idxOf? '.' with
  | some i => (t.take i, some (t.drop (i + 1)))
  | none => (t, none)

/-- Value text of `mtlx_input`: string-like types take the single (possibly quoted) token
verbatim; every other type joins its tokens with `", "`, the MaterialX array/vector syntax. -/
def valueText (ty : S) (vs : List S) : Option S :=
  if ty == "string".toList || ty == "filename".toList then
    match vs with
    | [v] => some v
    | _ => none
  else if vs.isEmpty then none
  else some (List.intercalate ", ".toList vs)

def addErr (m : Mat) (e : String) : Mat := { m with errors := m.errors ++ [e.toList] }

/-- Apply one tokenized extension line to the current material. -/
def step (m : Mat) (toks : List S) : Mat :=
  match toks with
  | kw :: args =>
    if kw == "mtlx_version".toList then
      match args with
      | [v] => { m with version := m.version ++ [v] }
      | _ => addErr m "mtlx_version: expected 1 argument"
    else if kw == "mtlx_surface".toList then
      match args with
      | [n, c] => { m with surface := m.surface ++ [(n, c)] }
      | _ => addErr m "mtlx_surface: expected <name> <category>"
    else if kw == "mtlx_node".toList then
      match args with
      | [n, c, t] => { m with nodes := m.nodes ++ [⟨n, c, t⟩] }
      | _ => addErr m "mtlx_node: expected <name> <category> <type>"
    else if kw == "mtlx_input".toList then
      match args with
      | ep :: t :: vs =>
        match splitDot ep, valueText t vs with
        | (n, some p), some v => { m with inputs := m.inputs ++ [⟨n, p, t, v⟩] }
        | _, _ => addErr m "mtlx_input: expected <node>.<input> <type> <value>"
      | _ => addErr m "mtlx_input: expected <node>.<input> <type> <value>"
    else if kw == "connectmtl".toList then
      match args with
      | [a, b] =>
        match splitDot a, splitDot b with
        | (s, o), (d, some p) => { m with conns := m.conns ++ [⟨s, o, d, p⟩] }
        | _, _ => addErr m "connectmtl: destination must be <node>.<input>"
      | _ => addErr m "connectmtl: expected <src>[.<output>] <dst>.<input>"
    else if kw == "mtlx_include".toList then
      match args with
      | [p] => { m with includes := m.includes ++ [p] }
      | _ => addErr m "mtlx_include: expected 1 argument"
    else if kw == "mtlx_colorspace".toList then
      match args with
      | [ep, cs] =>
        match splitDot ep with
        | (n, some p) => { m with colorspaces := m.colorspaces ++ [(n, p, cs)] }
        | _ => addErr m "mtlx_colorspace: expected <node>.<input> <colorspace>"
      | _ => addErr m "mtlx_colorspace: expected <node>.<input> <colorspace>"
    else m
  | [] => m

def isExtKeyword (kw : S) : Bool :=
  kw == "mtlx_version".toList || kw == "mtlx_surface".toList || kw == "mtlx_node".toList ||
  kw == "mtlx_input".toList || kw == "connectmtl".toList || kw == "mtlx_include".toList ||
  kw == "mtlx_colorspace".toList

/-- Parse a whole `.mtl` text into its materials (in definition order). Extension lines before
the first `newmtl` are ignored. A malformed (unterminated-quote) extension line records an
error in the current material. -/
def parseMtl (text : S) : List Mat :=
  let rec go : List S → List Mat → List Mat
    | [], acc => acc.reverse
    | l :: ls, acc =>
      if isComment l then go ls acc else
      let kw := (plainTok (l.dropWhile isBlank)).1
      if kw == "newmtl".toList then go ls ({ name := restAfterKeyword l } :: acc)
      else if isExtKeyword kw then
        match acc with
        | [] => go ls acc
        | m :: ms =>
          match tokenize l with
          | some toks => go ls (step m toks :: ms)
          | none => go ls (addErr m "unterminated quote" :: ms)
      else go ls acc
  go (lines text) []

/-! ## Well-formedness -/

/-- Built-in single-output value types accepted for `mtlx_node` and `mtlx_input`. -/
def builtinTy (t : S) : Bool := (Ty.ofString (String.ofList t)).isBuiltin

def Mat.surfName (m : Mat) : S := (m.surface.head?.map (·.1)).getD []
def Mat.names (m : Mat) : List S := m.surfName :: m.nodes.map (·.name)
def Mat.nodeTy? (m : Mat) (n : S) : Option S := (m.nodes.find? (·.name == n)).map (·.ty)

def inputOk (m : Mat) (i : InDecl) : Bool :=
  m.names.contains i.node && validNameChars i.port && builtinTy i.ty &&
  (parseValue (Ty.ofString (String.ofList i.ty)) i.value).isSome

def connOk (m : Mat) (c : Conn) : Bool :=
  (m.nodeTy? c.src).isSome &&
  (c.srcOut.isNone || c.srcOut == some "out".toList) &&
  m.names.contains c.dst && validNameChars c.port &&
  -- a declared constant on the same port must agree with the source type
  (m.inputs.all fun i => !(i.node == c.dst && i.port == c.port) || m.nodeTy? c.src == some i.ty)

/-- Ports bound by constants and by connections. -/
def Mat.inPorts (m : Mat) : List (S × S) := m.inputs.map fun i => (i.node, i.port)
def Mat.connPorts (m : Mat) : List (S × S) := m.conns.map fun c => (c.dst, c.port)

/-- A colorspace annotates a declared constant input. -/
def csOk (m : Mat) (c : S × S × S) : Bool :=
  m.inPorts.contains (c.1, c.2.1) && validNameChars c.2.2

def Mat.csPorts (m : Mat) : List (S × S) := m.colorspaces.map fun c => (c.1, c.2.1)

/-! ### Lowering to the MaterialX graph model -/

/-- Constant inputs not overridden by a connection, then connections, of node `n`. -/
def lowerIns (m : Mat) (n : S) : List (S × Src Val) :=
  (m.inputs.filter fun i => i.node == n && !(m.connPorts.contains (i.node, i.port))).filterMap
      (fun i => (parseValue (Ty.ofString (String.ofList i.ty)) i.value).map fun v => (i.port, .val v)) ++
  (m.conns.filter (·.dst == n)).map fun c => (c.port, .node c.src "out".toList)

def lower (m : Mat) : List (GNode Val) :=
  (m.surface.take 1).map (fun (n, c) => ⟨n, c, lowerIns m n⟩) ++
  m.nodes.map fun d => ⟨d.name, d.cat, lowerIns m d.name⟩

def noIface : Str → Option Val := fun _ => none

/-- The executable check (what the C loader implements). -/
def check (m : Mat) : Bool :=
  m.errors.isEmpty &&
  m.surface.length == 1 &&
  m.version.length ≤ 1 && m.version.all (fun v => (parseVersion v).isSome) &&
  m.names.all validNameChars && m.names.Nodup &&
  m.surface.all (fun s => validNameChars s.2) &&
  m.nodes.all (fun d => validNameChars d.cat && builtinTy d.ty) &&
  m.inputs.all (inputOk m) && m.inPorts.Nodup &&
  m.conns.all (connOk m) && m.connPorts.Nodup &&
  m.colorspaces.all (csOk m) && m.csPorts.Nodup &&
  (discoverGraphRanking (lower m) noIface).isSome

/-- The specification of a well-formed extended material. -/
structure WellFormed (m : Mat) : Prop where
  noErrors : m.errors = []
  oneSurface : m.surface.length = 1
  namesValid : ∀ n ∈ m.names, validNameChars n = true
  namesUnique : m.names.Nodup
  inputs : ∀ i ∈ m.inputs, inputOk m i = true
  inputsUnique : m.inPorts.Nodup
  conns : ∀ c ∈ m.conns, connOk m c = true
  connsUnique : m.connPorts.Nodup
  colorspaces : ∀ c ∈ m.colorspaces, csOk m c = true
  colorspacesUnique : m.csPorts.Nodup
  /-- Every connection source is declared (no dangling edges). -/
  bound : GraphSourcesBound (lower m) noIface
  /-- No node is upstream of itself. -/
  acyclic : ∀ n, ¬ GraphUpstream (lower m) n n

/-! ### Names in the emitted document -/

/-- Map an arbitrary `newmtl` name to a MaterialX identifier. -/
def sanitizeHead : S → S
  | [] => "_".toList
  | c :: cs => if isNameStart c then c :: cs else '_' :: c :: cs

def sanitize (n : S) : S :=
  sanitizeHead (n.map fun c => if isNameChar c then c else '_')

theorem sanitizeHead_valid (b : S) (hb : ∀ c ∈ b, isNameChar c = true) :
    validNameChars (sanitizeHead b) = true := by
  cases b with
  | nil => decide
  | cons c cs =>
    have hc : isNameChar c = true := hb c List.mem_cons_self
    have hcs : ∀ x ∈ cs, isNameChar x = true := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    by_cases hs : isNameStart c = true
    · simp only [sanitizeHead, hs, ite_true, validNameChars, Bool.true_and, List.all_eq_true]
      exact hcs
    · simp only [sanitizeHead, hs, Bool.false_eq_true, ite_false, validNameChars,
        List.all_cons, hc, Bool.true_and]
      refine Bool.and_eq_true_iff.mpr ⟨by decide, ?_⟩
      exact List.all_eq_true.mpr hcs

theorem sanitize_valid (n : S) : validNameChars (sanitize n) = true := by
  apply sanitizeHead_valid
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨x, _, rfl⟩ := hc
  split
  · assumption
  · decide

end TobjMtlx

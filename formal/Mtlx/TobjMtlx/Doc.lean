import TobjMtlx.Sound

/-!
# MaterialX-in-MTL: normative mapping to a MaterialX document

For every material accepted by `check`, in definition order:

```
<nodegraph name="NG_<M>">                         -- only if the material has nodes
  <cat name="n" type="ty"> <input .../> ... </cat> -- each mtlx_node, in order
  <output name="o_<n>" type="ty" nodename="n"/>   -- each node feeding the surface
</nodegraph>
<cat name="SR_<M>" type="surfaceshader"> inputs </cat>
<surfacematerial name="<M>" type="material">
  <input name="surfaceshader" type="surfaceshader" nodename="SR_<M>"/>
</surfacematerial>
```

`<M>` is `sanitize name`, made unique with a `_<k>` suffix. Inputs of a node: its constants
in file order (a constant whose port is connected is replaced in place by the connection), then
the remaining connections in file order. A connection between two non-surface nodes uses
`nodename`; a connection into the surface uses `nodegraph` + `output`.
The root is `<materialx version="V">`, `V` being the first declared `mtlx_version` of an
accepted material, else `1.39`; `mtlx_include`s become `<xi:include href>` (deduplicated).
-/
namespace TobjMtlx
open MtlxSpec

/-- Remove duplicates, keeping the first occurrence of each element. -/
def _root_.List.dedupFirst {α : Type} [BEq α] (l : List α) : List α :=
  (l.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

def el (tag : String) (attrs : List (String × S)) (kids : List Elem := []) : Elem :=
  .mk tag.toList (attrs.map fun (k, v) => (k.toList, v)) kids

def ngName (M : S) : S := "NG_".toList ++ M
def srName (M : S) : S := "SR_".toList ++ M
def outName (n : S) : S := "o_".toList ++ n

/-- The `<input>` for a connection `c` into a node (`intoSurface` selects the nodegraph form). -/
def connInput (m : Mat) (M : S) (intoSurface : Bool) (c : Conn) : Elem :=
  let ty := (m.nodeTy? c.src).getD []
  if intoSurface then
    el "input" [("name", c.port), ("type", ty), ("nodegraph", ngName M), ("output", outName c.src)]
  else
    el "input" [("name", c.port), ("type", ty), ("nodename", c.src)]

def nodeInputs (m : Mat) (M : S) (n : S) (intoSurface : Bool) : List Elem :=
  let consts := m.inputs.filter (·.node == n)
  let conns := m.conns.filter (·.dst == n)
  consts.map (fun i =>
      match conns.find? (·.port == i.port) with
      | some c => connInput m M intoSurface c
      | none =>
        el "input" ([("name", i.port), ("type", i.ty), ("value", i.value)] ++
          ((m.colorspaces.find? fun c => c.1 == n && c.2.1 == i.port).map
            (fun c => ("colorspace", c.2.2))).toList)) ++
    (conns.filter fun c => !consts.any (·.port == c.port)).map (connInput m M intoSurface)

/-- Nodes read by the surface, in first-connection order without duplicates. -/
def surfaceSources (m : Mat) : List S :=
  ((m.conns.filter (·.dst == m.surfName)).map (·.src)).dedupFirst

def matElems (m : Mat) (M : S) : List Elem :=
  let ng :=
    if m.nodes.isEmpty then []
    else [el "nodegraph" [("name", ngName M)]
      (m.nodes.map (fun d => el (String.ofList d.cat) [("name", d.name), ("type", d.ty)]
          (nodeInputs m M d.name false)) ++
        (surfaceSources m).map fun n =>
          el "output" [("name", outName n), ("type", (m.nodeTy? n).getD []), ("nodename", n)])]
  let cat := ((m.surface.head?.map (·.2)).getD [])
  ng ++
  [el (String.ofList cat) [("name", srName M), ("type", "surfaceshader".toList)]
      (nodeInputs m M m.surfName true),
   el "surfacematerial" [("name", M), ("type", "material".toList)]
      [el "input" [("name", "surfaceshader".toList), ("type", "surfaceshader".toList),
        ("nodename", srName M)]]]

/-- Choose `sanitize name`, or the first free `_<k>` (k = 2, 3, ...) variant. -/
def uniqueName (used : List S) (base : S) : S :=
  let rec go : Nat → Nat → S
    | 0, _ => base   -- unreachable: `used.length + 1` candidates cannot all be taken
    | fuel + 1, k =>
      let c := base ++ '_' :: (toString k).toList
      if used.contains c then go fuel (k + 1) else c
  if used.contains base then go (used.length + 1) 2 else base

def accepted (ms : List Mat) : List Mat := ms.filter fun m => m.ext && check m

def assignNames (ms : List Mat) : List (Mat × S) :=
  (ms.foldl (fun (acc : List (Mat × S)) m =>
      acc ++ [(m, uniqueName (acc.map (·.2)) (sanitize m.name))]) [])

def toDoc (ms : List Mat) : Elem :=
  let acc := accepted ms
  let ver := ((acc.findSome? (·.version.head?)).getD "1.39".toList)
  let incs := (acc.flatMap (·.includes)).dedupFirst
  el "materialx" [("version", ver)]
    (incs.map (fun p => el "xi:include" [("href", p)]) ++
      (assignNames acc).flatMap fun (m, M) => matElems m M)

end TobjMtlx

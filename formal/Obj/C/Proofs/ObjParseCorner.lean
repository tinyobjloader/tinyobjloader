/-
  Refinement of the translated `parse_corner_n_f` to the pure corner parser
  `Obj.parseCornerN` (Obj/Mesh.lean).

  `parse_corner_n_f_refines`: for every token held in the first `e ≤ bytes.length`
  bytes of a block (starting at offset 0; a dedicated block is the `e = length`
  case) and every set of counts below 2^31, the C function returns the pure `ok`
  flag and leaves in the 12-byte output record exactly the pure
  `(vertex, normal, texcoord)` indices `gflat`, with no undefined behaviour. The
  pure spec reads `(bytes.take e)`; all memory bounds stay on `bytes.length`
  because one-past-the-end pointers are legal in the model.
  It composes `tobj_cur_init`, the cursor-layout scanner
  (`scan_int_cursor_*`), `fix_index_f_refines`, and the optional `/vt` and `/vn`
  scans.  Memory-model facts about the cursor cell and the three temporary
  `int` blocks (1006, 1007, 1010, 1012) are tracked by `PCF`/`PCD`.
-/
import Obj.C.Proofs.ObjScanIntCursor
import Obj.C.Proofs.FixIndexRefines
import Obj.Mesh
namespace Obj.C.Proofs
open Obj.C Obj

theorem store_ptr_gen (m : Mem) (b o : Nat) (blk : Block) (b' o' : Nat) (hm : m b = some blk)
    (h : o + 8 ≤ blk.length) :
    store m .ptr (.ptr b o) (.ptr b' o') =
      .ok (m.upd b (splice blk o (encodeLE 8 (ptrPack (.ptr b' o'))))) := by
  have hlen' : (encodeLE 8 (ptrPack (.ptr b' o'))).length = 8 := encodeLE_length 8 _
  simp only [store, writeBytes, hm, hlen']
  rw [if_pos (by omega)]
  rfl

theorem load_i32_at (m : Mem) (b o : Nat) (blk : Block) (x : Nat) (hm : m b = some blk)
    (hl : o + 4 ≤ blk.length) (hx : (blk.drop o).take 4 = encodeLE 4 x) (hlt : x < 4294967296) :
    load m (.int ⟨32, true⟩) (.ptr b o) = .ok (.int ⟨32, true⟩ x) := by
  have hrb : readBytes m b o 4 = .ok (encodeLE 4 x) := by
    simp only [readBytes, hm]
    rw [if_pos hl, hx]
  have hsz : Ty.size (.int ⟨32, true⟩) = 4 := rfl
  simp only [load, hsz, hrb, Res.bind_eq, Res.bind_ok]
  have : (256 : Nat) ^ 4 = 4294967296 := by decide
  rw [decodeLE_encodeLE, this, Nat.mod_eq_of_lt hlt]
  rfl


/-- Memory after a `tobj_scan_int` call through the cursor cell `cc`. -/
def scanMemAfter (m : Mem) (cc bb ob : Nat) (len : Nat) (oblk : Block) (flag : Bool)
    (value : Int) (cursor : Nat) : Mem :=
  if flag then (m.upd cc (curCell bb len cursor)).upd ob
    (splice oblk 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value)))
  else m.upd cc (curCell bb len cursor)

theorem call_scan (s : State) (d cc bb ob : Nat) (bytes : Block) (q e : Nat) (oblk : Block)
    (hne : cc ≠ bb) (hne2 : ob ≠ cc) (hne3 : ob ≠ bb) (hbb : s.mem bb = some bytes)
    (hcc : s.mem cc = some (curCell bb e q))
    (hob : s.mem ob = some oblk) (hol : 4 ≤ oblk.length) (hro : s.ro = false)
    (hq : q ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296)
    {flag : Bool} {value : Int} {cursor : Nat}
    (hpure : scanInt ((bytes.take e).map UInt8.toNat) q = (flag, value, cursor)) :
    ExS Gen.prog s (.call (some d) 24 [(.field (.const (.ptr cc 0)) 0),
        (.load .ptr (.field (.const (.ptr cc 0)) 8)), (.const (.ptr ob 0))]) .normal
      { s with mem := scanMemAfter s.mem cc bb ob e oblk flag value cursor,
               locals := s.locals.upd d (.int ⟨8, false⟩ (if flag then 1 else 0)) } := by
  have hl : (curCell bb e q).length = 16 := by simp [curCell, encodeLE_length]
  have h0 : EvE Gen.prog s (.field (.const (.ptr cc 0)) 0) (.ptr cc 0) :=
    EvE.field (r := .ptr cc 0) (EvE.const _) (by simp [ptrAddN, hcc, hl])
  have h1 : EvE Gen.prog s (.load .ptr (.field (.const (.ptr cc 0)) 8)) (.ptr bb e) := by
    refine EvE.load (EvE.field (r := .ptr cc 8) (EvE.const _) (by simp [ptrAddN, hcc, hl])) ?_
    have := load_ptr_at s.mem cc bb e (encodeLE 8 (ptrPack (.ptr bb q))) [] (by
      rw [hcc]; simp [curCell]) hb32 hlen32
    simpa [encodeLE_length] using this
  have hargs := EvArgs.cons h0 (EvArgs.cons h1 (EvArgs.cons (EvE.const (.ptr ob 0)) EvArgs.nil))
  cases flag with
  | false =>
    obtain ⟨sf, hb, hm⟩ := scan_int_cursor_failure s.mem cc bb ob bytes q e
      (encodeLE 8 (ptrPack (.ptr bb e))) hne hbb (by simpa [curCell] using hcc) hq he hb32
      hlen32 hpure
    have := ExS.call_dst (p := Gen.prog) (s := s) (d := d) (f := 24) (fn := Gen.tobj_scan_int)
      (vs := [.ptr cc 0, .ptr bb e, .ptr ob 0]) (v := .int ⟨8, false⟩ 0) (s' := sf)
      hargs (by rfl) (by rfl) (by rw [hro]; exact hb)
    simpa [scanMemAfter, hm, curCell] using this
  | true =>
    obtain ⟨sf, hb, hm⟩ := scan_int_cursor_success s.mem cc bb ob bytes q e
      (encodeLE 8 (ptrPack (.ptr bb e))) oblk hne hne2 hne3 hbb
      (by simpa [curCell] using hcc) hob hol hq he hb32 hlen32 hpure
    have := ExS.call_dst (p := Gen.prog) (s := s) (d := d) (f := 24) (fn := Gen.tobj_scan_int)
      (vs := [.ptr cc 0, .ptr bb e, .ptr ob 0]) (v := .int ⟨8, false⟩ 1) (s' := sf)
      hargs (by rfl) (by rfl) (by rw [hro]; exact hb)
    simpa [scanMemAfter, hm, curCell] using this


/-- Arguments of a `fix_index_f` call from a cursor-scan temp block. -/
theorem fix_args (s : State) (vb ob nl off : Nat) (vblk oblk : Block) (idx : Int) (n : Nat)
    (hn : n < 2147483648) (hvb : s.mem vb = some vblk) (hvl : 4 ≤ vblk.length)
    (hvx : vblk.take 4 = encodeLE 4 (IntTy.wrap IntTy.i32 idx))
    (hrange : IntTy.inRange IntTy.i32 idx = true)
    (hl5 : s.locals 5 = some (.ptr ob 0)) (hln : s.locals nl = some (.int u64 n))
    (hob : s.mem ob = some oblk) (hoff : off + 4 ≤ oblk.length) :
    EvArgs Gen.prog s [(.load (.int ⟨32, true⟩) (.const (.ptr vb 0))), (.var nl),
      (.field (.var 5) off)]
      [.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx), .int u64 n, .ptr ob off] := by
  have hld : EvE Gen.prog s (.load (.int ⟨32, true⟩) (.const (.ptr vb 0)))
      (.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx)) := by
    apply EvE.load (EvE.const _)
    have hlt : IntTy.wrap IntTy.i32 idx < 4294967296 := by
      simp only [IntTy.wrap, IntTy.modulus, IntTy.i32]; omega
    exact load_i32_at s.mem vb 0 vblk _ hvb hvl (by simpa using hvx) hlt
  exact EvArgs.cons hld (EvArgs.cons (EvE.var hln) (EvArgs.cons
    (EvE.field (r := .ptr ob off) (EvE.var hl5) (by simp [ptrAddN, hob]; omega)) EvArgs.nil))


theorem call_fix (s : State) (d vb ob nl off : Nat) (vblk oblk : Block) (idx : Int) (n : Nat)
    (hn : n < 2147483648) (hvb : s.mem vb = some vblk) (hvl : 4 ≤ vblk.length)
    (hvx : vblk.take 4 = encodeLE 4 (IntTy.wrap IntTy.i32 idx))
    (hrange : IntTy.inRange IntTy.i32 idx = true)
    (hl5 : s.locals 5 = some (.ptr ob 0)) (hln : s.locals nl = some (.int u64 n))
    (hob : s.mem ob = some oblk) (hoff : off + 4 ≤ oblk.length) (hro : s.ro = false) :
    ExS Gen.prog s (.call (some d) 3 [(.load (.int ⟨32, true⟩) (.const (.ptr vb 0))), (.var nl),
      (.field (.var 5) off)]) .normal
      { s with mem := s.mem.upd ob (splice oblk off (encodeLE 4 (IntTy.wrap IntTy.i32 (storedIndex idx n)))),
               locals := s.locals.upd d (.int ⟨8, false⟩ (if (resolveIndex idx n).isSome then 1 else 0)) } := by
  have hargs := fix_args s vb ob nl off vblk oblk idx n hn hvb hvl hvx hrange hl5 hln hob hoff
  have l0 : (frameLocals Gen.fix_index_f.params [.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx),
      .int u64 n, .ptr ob off]) 0 = some (.int IntTy.i32 (IntTy.wrap IntTy.i32 idx)) := by
    simp [frameLocals, Gen.fix_index_f, List.idxOf?, List.findIdx?, List.findIdx?.go]; rfl
  have l1 : (frameLocals Gen.fix_index_f.params [.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx),
      .int u64 n, .ptr ob off]) 1 = some (.int IntTy.u64 n) := by
    simp [frameLocals, Gen.fix_index_f, List.idxOf?, List.findIdx?, List.findIdx?.go]; rfl
  have l2 : (frameLocals Gen.fix_index_f.params [.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx),
      .int u64 n, .ptr ob off]) 2 = some (.ptr ob off) := by
    simp [frameLocals, Gen.fix_index_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  obtain ⟨sf, hb, hm⟩ := fix_index_f_refines _ s.mem ob off oblk idx n hrange hn hob hoff l0 l1 l2
  have := ExS.call_dst (p := Gen.prog) (s := s) (d := d) (f := 3) (fn := Gen.fix_index_f)
    (vs := [.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx), .int u64 n, .ptr ob off])
    (v := .int ⟨8, false⟩ (if (resolveIndex idx n).isSome then 1 else 0)) (s' := sf)
    hargs (by rfl) (by rfl) (by rw [hro]; exact hb)
  rw [hm] at this
  exact this

theorem call_fix_none (s : State) (vb ob nl off : Nat) (vblk oblk : Block) (idx : Int) (n : Nat)
    (hn : n < 2147483648) (hvb : s.mem vb = some vblk) (hvl : 4 ≤ vblk.length)
    (hvx : vblk.take 4 = encodeLE 4 (IntTy.wrap IntTy.i32 idx))
    (hrange : IntTy.inRange IntTy.i32 idx = true)
    (hl5 : s.locals 5 = some (.ptr ob 0)) (hln : s.locals nl = some (.int u64 n))
    (hob : s.mem ob = some oblk) (hoff : off + 4 ≤ oblk.length) (hro : s.ro = false) :
    ExS Gen.prog s (.call none 3 [(.load (.int ⟨32, true⟩) (.const (.ptr vb 0))), (.var nl),
      (.field (.var 5) off)]) .normal
      { s with mem := s.mem.upd ob (splice oblk off (encodeLE 4 (IntTy.wrap IntTy.i32 (storedIndex idx n)))) } := by
  have hargs := fix_args s vb ob nl off vblk oblk idx n hn hvb hvl hvx hrange hl5 hln hob hoff
  have l0 : (frameLocals Gen.fix_index_f.params [.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx),
      .int u64 n, .ptr ob off]) 0 = some (.int IntTy.i32 (IntTy.wrap IntTy.i32 idx)) := by
    simp [frameLocals, Gen.fix_index_f, List.idxOf?, List.findIdx?, List.findIdx?.go]; rfl
  have l1 : (frameLocals Gen.fix_index_f.params [.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx),
      .int u64 n, .ptr ob off]) 1 = some (.int IntTy.u64 n) := by
    simp [frameLocals, Gen.fix_index_f, List.idxOf?, List.findIdx?, List.findIdx?.go]; rfl
  have l2 : (frameLocals Gen.fix_index_f.params [.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx),
      .int u64 n, .ptr ob off]) 2 = some (.ptr ob off) := by
    simp [frameLocals, Gen.fix_index_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  obtain ⟨sf, hb, hm⟩ := fix_index_f_refines _ s.mem ob off oblk idx n hrange hn hob hoff l0 l1 l2
  have := ExS_call_discard (p := Gen.prog) (s := s) (f := 3) (fn := Gen.fix_index_f)
    (vs := [.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 idx), .int u64 n, .ptr ob off])
    (v := .int ⟨8, false⟩ (if (resolveIndex idx n).isSome then 1 else 0)) (s' := sf)
    hargs (by rfl) (by rfl) (by rw [hro]; exact hb)
  rw [hm] at this
  exact this


/-- The 12-byte output corner record. -/
def gflat (oblk : Block) (v n t : Int) : Block :=
  encodeLE 4 (IntTy.wrap IntTy.i32 v) ++ encodeLE 4 (IntTy.wrap IntTy.i32 n) ++
    encodeLE 4 (IntTy.wrap IntTy.i32 t) ++ oblk.drop 12

theorem gflat_len (oblk : Block) (v n t : Int) (h : 12 ≤ oblk.length) :
    (gflat oblk v n t).length = oblk.length := by
  simp [gflat, encodeLE_length]; omega

theorem gflat_set0 (oblk : Block) (v n t v' : Int) (h : 12 ≤ oblk.length) :
    splice (gflat oblk v n t) 0 (encodeLE 4 (IntTy.wrap IntTy.i32 v')) = gflat oblk v' n t := by
  simp [splice, gflat, encodeLE_length, List.drop_append, List.take_append]

theorem gflat_set4 (oblk : Block) (v n t n' : Int) (h : 12 ≤ oblk.length) :
    splice (gflat oblk v n t) 4 (encodeLE 4 (IntTy.wrap IntTy.i32 n')) = gflat oblk v n' t := by
  simp [splice, gflat, encodeLE_length, List.drop_append, List.take_append]

theorem gflat_set8 (oblk : Block) (v n t t' : Int) (h : 12 ≤ oblk.length) :
    splice (gflat oblk v n t) 8 (encodeLE 4 (IntTy.wrap IntTy.i32 t')) = gflat oblk v n t' := by
  have t8 : ∀ x, (encodeLE 4 x).take 8 = encodeLE 4 x := fun x => List.take_of_length_le (by simp)
  have d8 : ∀ x, (encodeLE 4 x).drop 8 = [] := fun x => List.drop_eq_nil_of_le (by simp)
  have d12 : ∀ x, (encodeLE 4 x).drop 12 = [] := fun x => List.drop_eq_nil_of_le (by simp)
  simp [splice, gflat, encodeLE_length, List.drop_append, List.take_append, t8, d8, d12]

theorem splice_front (blk : Block) (xs : Block) (h : xs.length ≤ blk.length) :
    (splice blk 0 xs).take xs.length = xs := by
  simp [splice, List.take_append]


theorem byte_ne_eval (s : State) (e : Expr) (b o : Nat) (blk : Block) (byte : UInt8) (k : Nat)
    (hk : k < 128) (he : EvE Gen.prog s e (.ptr b o)) (hm : s.mem b = some blk)
    (hlt : o < blk.length) (ho : blk[o]? = some byte) :
    EvE Gen.prog s (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) e))
      (.const (.int ⟨32, true⟩ k))) (boolVal (decide (byte.toNat ≠ k))) := by
  have hbyte : blk[o]'hlt = byte := by
    have := List.getElem?_eq_getElem hlt
    rw [this] at ho; exact Option.some.inj ho
  have hload : EvE Gen.prog s (.load (.int ⟨8, true⟩) e) (.int ⟨8, true⟩ byte.toNat) := by
    apply EvE.load he
    have := load_i8_at s.mem b o blk hm hlt
    rw [hbyte] at this; exact this
  obtain ⟨hr, hw, hs, hn⟩ := i8_signed byte
  have hc : evalCast ⟨32, true⟩ (.int ⟨8, true⟩ byte.toNat) =
      .ok (.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 (IntTy.toInt IntTy.i8 byte.toNat))) := by
    simp [evalCast]; rfl
  have hcast := EvE.cast hload hc
  apply EvE.bin hcast (EvE.const _)
  have hbd : -2147483648 ≤ IntTy.toInt IntTy.i8 byte.toNat ∧
      IntTy.toInt IntTy.i8 byte.toNat ≤ 2147483647 := by
    have hlt256 : byte.toNat < 256 := byte.toNat_lt
    by_cases h : byte.toNat < 128
    · rw [hs h]; omega
    · have := hn (by omega)
      simp only [IntTy.toInt, IntTy.modulus, IntTy.i8] at this ⊢
      have : (128 ≤ byte.toNat) := by omega
      simp [this]; omega
  have hti := toInt_i32_wrap _ hbd
  have hk' : IntTy.toInt ⟨32, true⟩ k = k := by
    have : ¬ 2147483648 ≤ k := by omega
    simp [IntTy.toInt, IntTy.modulus, this]
  have key : decide (IntTy.toInt IntTy.i8 byte.toNat = (k : Int)) = decide (byte.toNat = k) := by
    by_cases hb : byte.toNat < 128
    · rw [hs hb]; exact decide_eq_decide.mpr (by omega)
    · have := hn (by omega)
      have h2 : ¬ (IntTy.toInt IntTy.i8 byte.toNat = (k : Int)) := by omega
      have h3 : ¬ byte.toNat = k := by omega
      simp [h2, h3]
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, hk', Res.bind]
  have hti' : IntTy.toInt ⟨32, true⟩ (IntTy.wrap IntTy.i32 (IntTy.toInt IntTy.i8 byte.toNat)) =
      IntTy.toInt IntTy.i8 byte.toNat := hti
  rw [hti', key]



theorem cc_p_eval (st : State) (cc bb len q : Nat) (hm : st.mem cc = some (curCell bb len q))
    (hb : bb < 4294967295) (hq : q < 4294967296) :
    EvE Gen.prog st (.load .ptr (.field (.const (.ptr cc 0)) 0)) (.ptr bb q) := by
  have hl : (curCell bb len q).length = 16 := by simp [curCell, encodeLE_length]
  refine EvE.load (EvE.field (r := .ptr cc 0) (EvE.const _) (by simp [ptrAddN, hm, hl])) ?_
  exact load_ptr_cell st.mem cc bb q _ hm hb hq

theorem cc_end_eval (st : State) (cc bb len q : Nat) (hm : st.mem cc = some (curCell bb len q))
    (hb : bb < 4294967295) (hlen : len < 4294967296) :
    EvE Gen.prog st (.load .ptr (.field (.const (.ptr cc 0)) 8)) (.ptr bb len) := by
  have hl : (curCell bb len q).length = 16 := by simp [curCell, encodeLE_length]
  refine EvE.load (EvE.field (r := .ptr cc 8) (EvE.const _) (by simp [ptrAddN, hm, hl])) ?_
  have := load_ptr_at st.mem cc bb len (encodeLE 8 (ptrPack (.ptr bb q))) [] (by
    rw [hm]; simp [curCell]) hb hlen
  simpa [encodeLE_length] using this


def pcA : Block := encodeLE 4 4294967295

theorem pcA_len : pcA.length = 4 := by simp [pcA, encodeLE_length]

theorem wrap_neg_one : IntTy.wrap IntTy.i32 (-1) = 4294967295 := by
  simp [IntTy.wrap, IntTy.modulus, IntTy.i32]

theorem init_block (oblk : Block) (h12 : 12 ≤ oblk.length) :
    splice (splice (splice oblk 0 pcA) 4 pcA) 8 pcA = gflat oblk (-1) (-1) (-1) := by
  have s1 := splice_append oblk 0 pcA pcA (by simp [pcA_len]; omega)
  have s2 := splice_append oblk 0 (pcA ++ pcA) pcA (by simp [pcA_len]; omega)
  have e1 : splice (splice oblk 0 pcA) 4 pcA = splice oblk 0 (pcA ++ pcA) := by
    simpa [pcA_len] using s1
  have e2 : splice (splice oblk 0 (pcA ++ pcA)) 8 pcA = splice oblk 0 (pcA ++ pcA ++ pcA) := by
    simpa [pcA_len] using s2
  rw [e1, e2]
  simp [splice, gflat, wrap_neg_one, pcA, List.take_append, List.drop_append, encodeLE_length]

/-- Initial three `-1` stores of `parse_corner_n`. -/
theorem pc_init_stores (s : State) (ob : Nat) (oblk : Block) (hl5 : s.locals 5 = some (.ptr ob 0))
    (hob : s.mem ob = some oblk) (h12 : 12 ≤ oblk.length) (hro : s.ro = false) :
    ∃ s1 : State, (∀ (rest : Stmt) (o : Outcome) (s' : State), ExS Gen.prog s1 rest o s' →
      ExS Gen.prog s (.seq (.store (.int ⟨32, true⟩) (.field (.var 5) 0)
        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))
      (.seq (.store (.int ⟨32, true⟩) (.field (.var 5) 4)
        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))
      (.seq (.store (.int ⟨32, true⟩) (.field (.var 5) 8)
        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) rest))) o s') ∧
      s1.locals = s.locals ∧ s1.ro = false ∧
      s1.mem = s.mem.upd ob (gflat oblk (-1) (-1) (-1)) := by
  have hneg := EvE.un (p := Gen.prog) (s := s) (EvE.const (.int ⟨32, true⟩ 1)) neg_one_eval
  have hA : ∀ k, k = 0 ∨ k = 4 ∨ k = 8 → ∀ blk : Block, blk.length = oblk.length →
      s.mem ob = s.mem ob → True := fun _ _ _ _ _ => trivial
  have hf : ∀ (st : State) (off : Nat) (blk : Block), st.locals 5 = some (.ptr ob 0) →
      st.mem ob = some blk → off + 4 ≤ blk.length → st.ro = false →
      ExS Gen.prog st (.store (.int ⟨32, true⟩) (.field (.var 5) off)
        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) .normal
        { st with mem := st.mem.upd ob (splice blk off pcA) } := by
    intro st off blk hl hm hlen hr
    have hn := EvE.un (p := Gen.prog) (s := st) (EvE.const (.int ⟨32, true⟩ 1)) neg_one_eval
    have haddr : EvE Gen.prog st (.field (.var 5) off) (.ptr ob off) :=
      EvE.field (r := .ptr ob off) (EvE.var hl) (by simp [ptrAddN, hm]; omega)
    have hst := store_int st.mem ob off blk hm ⟨32, true⟩ 4294967295 (by simp [IntTy.bytes]; omega)
    exact ExS.store haddr hn hr (by simpa [IntTy.bytes, pcA, i32] using hst)
  have e1 := hf s 0 oblk hl5 hob (by omega) hro
  let s1 : State := { s with mem := s.mem.upd ob (splice oblk 0 pcA) }
  have hl1 : (splice oblk 0 pcA).length = oblk.length := by
    apply splice_length; rw [pcA_len]; omega
  have e2 := hf s1 4 _ hl5 (Mem.upd_same _ _ _) (by omega) hro
  let s2 : State := { s1 with mem := s1.mem.upd ob (splice (splice oblk 0 pcA) 4 pcA) }
  have hl2 : (splice (splice oblk 0 pcA) 4 pcA).length = oblk.length := by
    rw [splice_length _ _ _ (by rw [pcA_len]; omega), hl1]
  have e3 := hf s2 8 _ hl5 (Mem.upd_same _ _ _) (by omega) hro
  refine ⟨{ s2 with mem := s2.mem.upd ob (splice (splice (splice oblk 0 pcA) 4 pcA) 8 pcA) },
    fun rest o s' hr => ExS.seq e1 (ExS.seq e2 (ExS.seq e3 hr)), rfl, hro, ?_⟩
  show ((s.mem.upd ob _).upd ob _).upd ob _ = _
  simp only [Mem.upd_upd]
  rw [init_block oblk h12]


theorem cur_init_exs (m : Mem) (cc bb : Nat) (bytes cblk : Block) (e : Nat)
    (hbb : m bb = some bytes)
    (hcc : m cc = some cblk) (hl : cblk.length = 16) (hne : cc ≠ bb)
    (he : e ≤ bytes.length) (hlen32 : e < 4294967296) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tobj_cur_init.params
        [.ptr cc 0, .ptr bb 0, .int u64 e], m, false⟩ Gen.tobj_cur_init.body .normal s' ∧
      s'.mem = m.upd cc (curCell bb e 0) := by
  let s0 : State := ⟨frameLocals Gen.tobj_cur_init.params
    [.ptr cc 0, .ptr bb 0, .int u64 e], m, false⟩
  have l0 : s0.locals 0 = some (.ptr cc 0) := by
    simp [s0, frameLocals, Gen.tobj_cur_init, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.ptr bb 0) := by
    simp [s0, frameLocals, Gen.tobj_cur_init, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s0.locals 2 = some (.int u64 e) := by
    simp [s0, frameLocals, Gen.tobj_cur_init, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hf0 : EvE Gen.prog s0 (.field (.var 0) 0) (.ptr cc 0) :=
    EvE.field (r := .ptr cc 0) (EvE.var l0) (by simp [ptrAddN, s0, hcc])
  have hst1 := store_ptr_gen s0.mem cc 0 cblk bb 0 hcc (by omega)
  have e1 := ExS.store (p := Gen.prog) (s := s0) (ty := .ptr) hf0 (EvE.var l1) rfl hst1
  let s1 : State := { s0 with mem := s0.mem.upd cc (splice cblk 0 (encodeLE 8 (ptrPack (.ptr bb 0)))) }
  have hl1 : (splice cblk 0 (encodeLE 8 (ptrPack (.ptr bb 0)))).length = 16 := by
    rw [splice_length _ _ _ (by simp [encodeLE_length]; omega), hl]
  have hmc : s1.mem cc = some (splice cblk 0 (encodeLE 8 (ptrPack (.ptr bb 0)))) :=
    Mem.upd_same _ _ _
  have hmb : s1.mem bb = some bytes := by
    show (m.upd cc _) bb = _
    rw [Mem.upd_ne _ _ (Ne.symm hne)]; exact hbb
  have hf8 : EvE Gen.prog s1 (.field (.var 0) 8) (.ptr cc 8) :=
    EvE.field (r := .ptr cc 8) (EvE.var l0) (by simp [ptrAddN, hmc, hl1])
  have hv1 : EvE Gen.prog s1 (.var 1) (.ptr bb 0) := EvE.var l1
  have hv2 : EvE Gen.prog s1 (.var 2) (.int u64 e) := EvE.var l2
  have hidx : EvE Gen.prog s1 (.index (.var 1) (.var 2) 1) (.ptr bb e) := by
    apply EvE.index hv1 hv2
    simp [u64, ptrAddN, hmb]
    omega
  have hst2 := store_ptr_gen s1.mem cc 8 _ bb e hmc (by omega)
  have e2 := ExS.store (p := Gen.prog) (s := s1) (ty := .ptr) hf8 hidx rfl hst2
  refine ⟨_, ExS.seq e1 e2, ?_⟩
  show ((m.upd cc _).upd cc _) = _
  rw [Mem.upd_upd]
  congr 1
  simp [splice, curCell, encodeLE_length, hl, List.take_append, List.drop_append]


/-- Memory facts maintained through `parse_corner_n_f`. -/
structure PCF (s : State) (bb ob : Nat) (bytes : Block) (e q : Nat) : Prop where
  mbb : s.mem bb = some bytes
  he : e ≤ bytes.length
  mc : s.mem 1006 = some (curCell bb e q)
  tmp : ∀ t, (t = 1007 ∨ t = 1010 ∨ t = 1012) → ∃ blk, s.mem t = some blk ∧ 4 ≤ blk.length
  ro : s.ro = false

structure PCD (bb ob : Nat) : Prop where
  b6 : bb ≠ 1006
  b7 : bb ≠ 1007
  b10 : bb ≠ 1010
  b12 : bb ≠ 1012
  o6 : ob ≠ 1006
  o7 : ob ≠ 1007
  o10 : ob ≠ 1010
  o12 : ob ≠ 1012
  bo : ob ≠ bb

def scanSt (s : State) (d t bb len : Nat) (blk : Block) (flag : Bool) (value : Int) (cursor : Nat) : State :=
  { s with mem := scanMemAfter s.mem 1006 bb t len blk flag value cursor, locals := s.locals.upd d (.int ⟨8, false⟩ (if flag then 1 else 0)) }

theorem pcf_scan (s : State) (d t bb ob : Nat) (bytes : Block) (q e : Nat) (hD : PCD bb ob)
    (ht : t = 1007 ∨ t = 1010 ∨ t = 1012) (hF : PCF s bb ob bytes e q)
    (hq : q ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296)
    {flag : Bool} {value : Int} {cursor : Nat}
    (hpure : scanInt ((bytes.take e).map UInt8.toNat) q = (flag, value, cursor)) :
    ∃ blk : Block, s.mem t = some blk ∧ 4 ≤ blk.length ∧
    ExS Gen.prog s (.call (some d) 24 [(.field (.const (.ptr 1006 0)) 0),
        (.load .ptr (.field (.const (.ptr 1006 0)) 8)), (.const (.ptr t 0))]) .normal
      (scanSt s d t bb e blk flag value cursor) ∧
    PCF (scanSt s d t bb e blk flag value cursor) bb ob bytes e cursor ∧
    (∀ b, b ≠ 1006 → b ≠ t → (scanMemAfter s.mem 1006 bb t e blk flag value cursor) b = s.mem b) ∧
    (flag = true → (scanMemAfter s.mem 1006 bb t e blk flag value cursor) t =
      some (splice blk 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value)))) := by
  obtain ⟨blk, hblk, hlen⟩ := hF.tmp t ht
  have ht6 : t ≠ 1006 := by rcases ht with h | h | h <;> omega
  have htb : t ≠ bb := by
    rcases ht with h | h | h
    · subst h; exact fun e => hD.b7 e.symm
    · subst h; exact fun e => hD.b10 e.symm
    · subst h; exact fun e => hD.b12 e.symm
  have hto : ob ≠ t := by
    rcases ht with h | h | h
    · subst h; exact hD.o7
    · subst h; exact hD.o10
    · subst h; exact hD.o12
  refine ⟨blk, hblk, hlen, ?_, ?_, ?_, ?_⟩
  · exact call_scan s d 1006 bb t bytes q e blk hD.b6.symm ht6 htb hF.mbb hF.mc hblk
      hlen hF.ro hq he hb32 hlen32 hpure
  · have hl16 : bytes.length = bytes.length := rfl
    refine ⟨?_, he, ?_, ?_, hF.ro⟩
    · show (scanMemAfter s.mem 1006 bb t e blk flag value cursor) bb = _
      cases flag <;> simp [scanMemAfter, Mem.upd_ne _ _ hD.b6, Mem.upd_ne _ _ (Ne.symm htb), hF.mbb]
    · show (scanMemAfter s.mem 1006 bb t e blk flag value cursor) 1006 = _
      cases flag <;> simp [scanMemAfter, Mem.upd_ne _ _ (Ne.symm ht6)]
    · intro t' ht'
      obtain ⟨blk', hb', hl'⟩ := hF.tmp t' ht'
      show ∃ b, (scanMemAfter s.mem 1006 bb t e blk flag value cursor) t' = some b ∧ _
      have h6' : t' ≠ 1006 := by rcases ht' with h | h | h <;> omega
      by_cases htt : t' = t
      · subst htt
        cases flag
        · exact ⟨blk, by simp [scanMemAfter, Mem.upd_ne _ _ h6', hblk], hlen⟩
        · refine ⟨splice blk 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value)), by simp [scanMemAfter, Mem.upd_ne _ _ h6'], ?_⟩
          rw [splice_length _ _ _ (by simp [encodeLE_length]; omega)]; exact hlen
      · cases flag
        · exact ⟨blk', by simp [scanMemAfter, Mem.upd_ne _ _ h6', hb'], hl'⟩
        · exact ⟨blk', by simp [scanMemAfter, Mem.upd_ne _ _ h6', Mem.upd_ne _ _ htt, hb'], hl'⟩
  · intro b h1 h2
    cases flag <;> simp [scanMemAfter, Mem.upd_ne _ _ h1, Mem.upd_ne _ _ h2]
  · intro hf
    subst hf
    simp [scanMemAfter]


/-- State after the prefix of `parse_corner_n`: `-1` stores, cursor init, first scan. -/
theorem pc_prefix (m : Mem) (bb ob : Nat) (bytes oblk cblk b7 b10 b12 : Block) (a b c e : Nat)
    (hD : PCD bb ob) (hbb : m bb = some bytes) (hob : m ob = some oblk) (h12 : 12 ≤ oblk.length)
    (hcc : m 1006 = some cblk) (hcl : cblk.length = 16)
    (h7 : m 1007 = some b7) (h7l : 4 ≤ b7.length) (h10 : m 1010 = some b10) (h10l : 4 ≤ b10.length)
    (h12' : m 1012 = some b12) (h12l : 4 ≤ b12.length)
    (hb32 : bb < 4294967295) (he : e ≤ bytes.length) (hlen32 : e < 4294967296)
    {flag : Bool} {value : Int} {c1 : Nat}
    (hs : scanInt ((bytes.take e).map UInt8.toNat) 0 = (flag, value, c1)) :
    let s0 : State := ⟨frameLocals Gen.parse_corner_n_f.params
      [.ptr bb 0, .int u64 e, .int u64 a, .int u64 b, .int u64 c, .ptr ob 0], m, false⟩
    ∃ blk7 : Block, m 1007 = some blk7 ∧ 4 ≤ blk7.length ∧ ∃ s2 : State,
      (∀ (rest : Stmt) (o : Outcome) (s' : State), ExS Gen.prog s2 rest o s' →
      ExS Gen.prog s0 (.seq (.store (.int ⟨32, true⟩) (.field (.var 5) 0)
        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))
      (.seq (.store (.int ⟨32, true⟩) (.field (.var 5) 4)
        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))
      (.seq (.store (.int ⟨32, true⟩) (.field (.var 5) 8)
        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))
      (.seq (.call none 14 [(.const (.ptr 1006 0)), (.var 0), (.var 1)])
      (.seq (.call (some 8) 24 [(.field (.const (.ptr 1006 0)) 0),
          (.load .ptr (.field (.const (.ptr 1006 0)) 8)), (.const (.ptr 1007 0))]) rest))))) o s') ∧
      PCF s2 bb ob bytes e c1 ∧ s2.mem ob = some (gflat oblk (-1) (-1) (-1)) ∧
      (∀ i, i ≠ 8 → s2.locals i = s0.locals i) ∧
      s2.locals 8 = some (.int ⟨8, false⟩ (if flag then 1 else 0)) ∧
      (flag = true → s2.mem 1007 = some (splice blk7 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value)))) := by
  intro s0
  have l5 : s0.locals 5 = some (.ptr ob 0) := by
    simp [s0, frameLocals, Gen.parse_corner_n_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l0 : s0.locals 0 = some (.ptr bb 0) := by
    simp [s0, frameLocals, Gen.parse_corner_n_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.int u64 e) := by
    simp [s0, frameLocals, Gen.parse_corner_n_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  obtain ⟨s1, e1, hl1, hro1, hm1⟩ := pc_init_stores s0 ob oblk l5 hob h12 rfl
  have hne6 : (1006 : Nat) ≠ bb := fun e => hD.b6 e.symm
  have hm1c : s1.mem 1006 = some cblk := by
    rw [hm1]; show (m.upd ob _) 1006 = _
    rw [Mem.upd_ne _ _ (Ne.symm hD.o6)]; exact hcc
  have hm1b : s1.mem bb = some bytes := by
    rw [hm1]; show (m.upd ob _) bb = _
    rw [Mem.upd_ne _ _ hD.bo.symm]; exact hbb
  obtain ⟨sc, ec, hmc⟩ := cur_init_exs s1.mem 1006 bb bytes cblk e hm1b hm1c hcl hne6 he hlen32
  have l0' : s1.locals 0 = some (.ptr bb 0) := by rw [hl1]; exact l0
  have l1' : s1.locals 1 = some (.int u64 e) := by rw [hl1]; exact l1
  have hargs := EvArgs.cons (p := Gen.prog) (s := s1) (EvE.const (.ptr 1006 0))
    (EvArgs.cons (EvE.var l0') (EvArgs.cons (EvE.var l1') EvArgs.nil))
  have hcall := ExS.call (p := Gen.prog) (s := s1) (f := 14) (fn := Gen.tobj_cur_init)
    (vs := [.ptr 1006 0, .ptr bb 0, .int u64 e]) (o := .normal) (s' := sc) hargs
    (by rfl) (by rfl) (by rw [hro1]; exact ec) (Or.inl rfl)
  let s2' : State := { s1 with mem := sc.mem }
  have hF : PCF s2' bb ob bytes e 0 := by
    refine ⟨?_, he, ?_, ?_, hro1⟩
    · show sc.mem bb = _
      rw [hmc]; show (s1.mem.upd 1006 _) bb = _
      rw [Mem.upd_ne _ _ hD.b6]; exact hm1b
    · show sc.mem 1006 = _
      rw [hmc]; exact Mem.upd_same _ _ _
    · intro t ht
      have h6' : t ≠ 1006 := by rcases ht with h | h | h <;> omega
      have hot : ob ≠ t := by
        rcases ht with h | h | h
        · subst h; exact hD.o7
        · subst h; exact hD.o10
        · subst h; exact hD.o12
      show ∃ blk, sc.mem t = some blk ∧ _
      rw [hmc]
      have hm : m t = some (if t = 1007 then b7 else if t = 1010 then b10 else b12) := by
        rcases ht with h | h | h <;> subst h <;> simp [h7, h10, h12']
      refine ⟨if t = 1007 then b7 else if t = 1010 then b10 else b12, ?_, ?_⟩
      · show (s1.mem.upd 1006 _) t = _
        rw [Mem.upd_ne _ _ h6', hm1]; show (m.upd ob _) t = _
        rw [Mem.upd_ne _ _ (Ne.symm hot)]; exact hm
      · rcases ht with h | h | h <;> subst h <;> simp [h7l, h10l, h12l]
  have hs' : scanInt ((bytes.take e).map UInt8.toNat) 0 = (flag, value, c1) := hs
  obtain ⟨blk, hblk, hblk4, hscan, hFs, hrest, hval⟩ := pcf_scan s2' 8 1007 bb ob bytes 0 e hD
    (Or.inl rfl) hF (by omega) he hb32 hlen32 hs'
  have hblk7 : s2'.mem 1007 = some b7 := by
    show sc.mem 1007 = _
    rw [hmc]; show (s1.mem.upd 1006 _) 1007 = _
    rw [Mem.upd_ne _ _ (by omega), hm1]; show (m.upd ob _) 1007 = _
    rw [Mem.upd_ne _ _ (Ne.symm hD.o7)]; exact h7
  rw [hblk7] at hblk
  have hbb' : blk = b7 := (Option.some.inj hblk).symm
  subst hbb'
  refine ⟨blk, h7, hblk4, scanSt s2' 8 1007 bb e blk flag value c1, ?_, hFs, ?_, ?_, ?_, ?_⟩
  · exact fun rest o s' hr => e1 _ _ _ (ExS.seq hcall (ExS.seq hscan hr))
  · show (scanMemAfter s2'.mem 1006 bb 1007 e blk flag value c1) ob = _
    rw [hrest ob hD.o6 hD.o7]
    show sc.mem ob = _
    rw [hmc]; show (s1.mem.upd 1006 _) ob = _
    rw [Mem.upd_ne _ _ hD.o6, hm1]; exact Mem.upd_same _ _ _
  · intro i hi
    show (s2'.locals.upd 8 _) i = _
    simp [Locals.upd, hi]
    show s1.locals i = _
    rw [hl1]
  · show (s2'.locals.upd 8 _) 8 = _
    simp [Locals.upd]
  · intro hf
    exact hval hf


theorem truthy_boolVal (b : Bool) : truthy (boolVal b) = .ok b := by
  cases b <;> simp [truthy, boolVal]

def pcP : Expr := .load .ptr (.field (.const (.ptr 1006 0)) 0)
def pcE : Expr := .load .ptr (.field (.const (.ptr 1006 0)) 8)

def pcG1 : Expr :=
  (.land (.bin .lt (some IntTy.u64) pcP pcE)
    (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) pcP))
      (.const (.int ⟨32, true⟩ 47))))

def pcG2 : Expr :=
  (.land (.bin .lt (some IntTy.u64) pcP pcE)
    (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) pcP))
      (.const (.int ⟨32, true⟩ 47))))

theorem pc_p_eval (st : State) (bb ob : Nat) (bytes : Block) (e q : Nat)
    (hF : PCF st bb ob bytes e q)
    (hb32 : bb < 4294967295) (hq : q ≤ e) (hlen32 : e < 4294967296) :
    EvE Gen.prog st pcP (.ptr bb q) ∧ EvE Gen.prog st pcE (.ptr bb e) :=
  ⟨cc_p_eval st 1006 bb e q hF.mc hb32 (by omega),
   cc_end_eval st 1006 bb e q hF.mc hb32 hlen32⟩

theorem g1_eval (st : State) (bb ob : Nat) (bytes : Block) (e q : Nat)
    (hF : PCF st bb ob bytes e q)
    (hb32 : bb < 4294967295) (hq : q ≤ e) (hlen32 : e < 4294967296) :
    EvE Gen.prog st pcG1
      (boolVal (decide (q < e ∧ ((bytes.take e)[q]?).map UInt8.toNat = some 47))) := by
  have heB : e ≤ bytes.length := hF.he
  obtain ⟨hp, hpe⟩ := pc_p_eval st bb ob bytes e q hF hb32 hq hlen32
  by_cases hlt : q < e
  · obtain ⟨x, hx0⟩ : ∃ x, bytes[q]? = some x := by
      have hlt' : q < bytes.length := by omega
      exact ⟨bytes[q]'hlt', List.getElem?_eq_getElem hlt'⟩
    have hx : (bytes.take e)[q]? = some x := by
      rw [List.getElem?_take_of_lt hlt]; exact hx0
    have hl : EvE Gen.prog st (.bin .lt (some IntTy.u64) pcP pcE) (boolVal true) := by
      apply EvE.bin hp hpe; simp [evalBin, isPtr, boolVal, hlt]
    have heq := byte_eq_eval st pcP bb q bytes x 47 (by omega) hp hF.mbb (by omega) hx0
    have := EvE.land_true (bb := decide (x.toNat = 47)) hl (by simp [truthy, boolVal]) heq
      (truthy_boolVal _)
    have e2 : decide (q < e ∧ ((bytes.take e)[q]?).map UInt8.toNat = some 47) =
        decide (x.toNat = 47) := by rw [hx]; simp [hlt]
    unfold pcG1
    rw [e2]; exact this
  · have hl : EvE Gen.prog st (.bin .lt (some IntTy.u64) pcP pcE) (boolVal false) := by
      apply EvE.bin hp hpe; simp [evalBin, isPtr, boolVal, hlt]
    have := EvE.land_false (b := (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩
      (.load (.int ⟨8, true⟩) pcP)) (.const (.int ⟨32, true⟩ 47)))) hl (by simp [truthy, boolVal])
    unfold pcG1
    simpa [hlt] using this

theorem g2_eval (st : State) (bb ob : Nat) (bytes : Block) (e q : Nat)
    (hF : PCF st bb ob bytes e q)
    (hb32 : bb < 4294967295) (hq : q ≤ e) (hlen32 : e < 4294967296) :
    EvE Gen.prog st pcG2
      (boolVal (decide (q < e ∧ ((bytes.take e)[q]?).map UInt8.toNat ≠ some 47))) := by
  have heB : e ≤ bytes.length := hF.he
  obtain ⟨hp, hpe⟩ := pc_p_eval st bb ob bytes e q hF hb32 hq hlen32
  by_cases hlt : q < e
  · obtain ⟨x, hx0⟩ : ∃ x, bytes[q]? = some x := by
      have hlt' : q < bytes.length := by omega
      exact ⟨bytes[q]'hlt', List.getElem?_eq_getElem hlt'⟩
    have hx : (bytes.take e)[q]? = some x := by
      rw [List.getElem?_take_of_lt hlt]; exact hx0
    have hl : EvE Gen.prog st (.bin .lt (some IntTy.u64) pcP pcE) (boolVal true) := by
      apply EvE.bin hp hpe; simp [evalBin, isPtr, boolVal, hlt]
    have heq := byte_ne_eval st pcP bb q bytes x 47 (by omega) hp hF.mbb (by omega) hx0
    have := EvE.land_true (bb := decide (x.toNat ≠ 47)) hl (by simp [truthy, boolVal]) heq
      (truthy_boolVal _)
    have e2 : decide (q < e ∧ ((bytes.take e)[q]?).map UInt8.toNat ≠ some 47) =
        decide (x.toNat ≠ 47) := by rw [hx]; simp [hlt]
    unfold pcG2
    rw [e2]
    simpa using this
  · have hl : EvE Gen.prog st (.bin .lt (some IntTy.u64) pcP pcE) (boolVal false) := by
      apply EvE.bin hp hpe; simp [evalBin, isPtr, boolVal, hlt]
    have := EvE.land_false (b := (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
      (.load (.int ⟨8, true⟩) pcP)) (.const (.int ⟨32, true⟩ 47)))) hl (by simp [truthy, boolVal])
    unfold pcG2
    simpa [hlt] using this


def pcStp : Stmt :=
  (.store .ptr (.field (.const (.ptr 1006 0)) 0) (.index pcP (.const (.int ⟨64, true⟩ 1)) 1))

def stpSt (st : State) (bb len q : Nat) : State :=
  { st with mem := st.mem.upd 1006 (curCell bb len (q + 1)) }

theorem stp_exs (st : State) (bb ob : Nat) (bytes : Block) (e q : Nat) (hD : PCD bb ob)
    (hF : PCF st bb ob bytes e q) (hb32 : bb < 4294967295) (hlt : q < e)
    (hlen32 : e < 4294967296) :
    ExS Gen.prog st pcStp .normal (stpSt st bb e q) ∧
    PCF (stpSt st bb e q) bb ob bytes e (q + 1) := by
  have heB0 : e ≤ bytes.length := hF.he
  have hlt' : q < bytes.length := by omega
  obtain ⟨hp, he⟩ := pc_p_eval st bb ob bytes e q hF hb32 (by omega) hlen32
  have hl : (curCell bb e q).length = 16 := by simp [curCell, encodeLE_length]
  have haddr : EvE Gen.prog st (.field (.const (.ptr 1006 0)) 0) (.ptr 1006 0) :=
    EvE.field (r := .ptr 1006 0) (EvE.const _) (by simp [ptrAddN, hF.mc, hl])
  have heB : e ≤ bytes.length := hF.he
  have hq1e : q + 1 ≤ bytes.length := by omega
  have hidx : EvE Gen.prog st (.index pcP (.const (.int ⟨64, true⟩ 1)) 1) (.ptr bb (q + 1)) := by
    apply EvE.index hp (EvE.const _)
    have h1 : IntTy.toInt ⟨64, true⟩ 1 = 1 := by simp [IntTy.toInt, IntTy.modulus]
    simp [IntTy.signed, ptrAdd, hF.mbb, h1]
    omega
  have hst := store_ptr_cell st.mem 1006 bb q bb (q + 1) (encodeLE 8 (ptrPack (.ptr bb e)))
    (by rw [hF.mc]; simp [curCell])
  have hex := ExS.store (p := Gen.prog) (s := st) (ty := .ptr) haddr hidx hF.ro hst
  refine ⟨by unfold pcStp; exact hex, ?_, ?_, ?_, ?_, hF.ro⟩
  · show (st.mem.upd 1006 _) bb = _
    rw [Mem.upd_ne _ _ hD.b6]; exact hF.mbb
  · exact hF.he
  · show (st.mem.upd 1006 _) 1006 = _
    exact Mem.upd_same _ _ _
  · intro t ht
    obtain ⟨blk, hb, hl4⟩ := hF.tmp t ht
    refine ⟨blk, ?_, hl4⟩
    have h6' : t ≠ 1006 := by rcases ht with h | h | h <;> omega
    show (st.mem.upd 1006 _) t = _
    rw [Mem.upd_ne _ _ h6']; exact hb

theorem pcf_ob_update (st : State) (bb ob : Nat) (bytes : Block) (e q : Nat) (hD : PCD bb ob)
    (hF : PCF st bb ob bytes e q) (X : Block) (L : Locals) :
    PCF { st with mem := st.mem.upd ob X, locals := L } bb ob bytes e q := by
  refine ⟨?_, hF.he, ?_, ?_, hF.ro⟩
  · show (st.mem.upd ob X) bb = _
    rw [Mem.upd_ne _ _ hD.bo.symm]; exact hF.mbb
  · show (st.mem.upd ob X) 1006 = _
    rw [Mem.upd_ne _ _ (Ne.symm hD.o6)]; exact hF.mc
  · intro t ht
    obtain ⟨blk, hb, hl4⟩ := hF.tmp t ht
    refine ⟨blk, ?_, hl4⟩
    have hot : t ≠ ob := by
      rcases ht with h | h | h
      · subst h; exact fun e => hD.o7 e.symm
      · subst h; exact fun e => hD.o10 e.symm
      · subst h; exact fun e => hD.o12 e.symm
    show (st.mem.upd ob X) t = _
    rw [Mem.upd_ne _ _ hot]; exact hb

theorem pcf_locals (st : State) (bb ob : Nat) (bytes : Block) (e q : Nat)
    (hF : PCF st bb ob bytes e q) (L : Locals) : PCF { st with locals := L } bb ob bytes e q :=
  ⟨hF.mbb, hF.he, hF.mc, hF.tmp, hF.ro⟩


theorem inRange_of_scan (value : Int) (h : -2147483647 ≤ value ∧ value ≤ 2147483647) :
    IntTy.inRange IntTy.i32 value = true := by
  simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i32]; omega

theorem mem_gflat (oblk : Block) (v n t : Int) (h : 12 ≤ oblk.length) :
    (gflat oblk v n t).length = oblk.length := gflat_len oblk v n t h


theorem opt_scan (s : State) (d t nl off bb ob : Nat) (bytes obc : Block) (q n e : Nat)
    (hD : PCD bb ob) (ht : t = 1007 ∨ t = 1010 ∨ t = 1012) (hF : PCF s bb ob bytes e q)
    (hq : q ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296)
    (hn : n < 2147483648) (hd5 : d ≠ 5) (hdn : d ≠ nl) (hl5 : s.locals 5 = some (.ptr ob 0))
    (hln : s.locals nl = some (.int u64 n)) (hob : s.mem ob = some obc) (hoff : off + 4 ≤ obc.length)
    {flag : Bool} {value : Int} {cursor : Nat}
    (hpure : scanInt ((bytes.take e).map UInt8.toNat) q = (flag, value, cursor)) :
    ∃ s' : State, ExS Gen.prog s (.seq (.call (some d) 24 [(.field (.const (.ptr 1006 0)) 0), pcE,
        (.const (.ptr t 0))]) (.ite (.var d) (.call none 3 [(.load (.int ⟨32, true⟩) (.const (.ptr t 0))),
        (.var nl), (.field (.var 5) off)]) .skip)) .normal s' ∧
      PCF s' bb ob bytes e cursor ∧ (∀ i, i ≠ d → s'.locals i = s.locals i) ∧
      s'.mem ob = some (if flag then splice obc off (encodeLE 4 (IntTy.wrap IntTy.i32 (storedIndex value n))) else obc) := by
  obtain ⟨blk, hblk, hl4, hscan, hFs, hrest, hval⟩ := pcf_scan s d t bb ob bytes q e hD ht hF hq he
    hb32 hlen32 hpure
  have hot : ob ≠ t := by
    rcases ht with h | h | h
    · subst h; exact hD.o7
    · subst h; exact hD.o10
    · subst h; exact hD.o12
  have ho6 : ob ≠ 1006 := hD.o6
  have hobs : (scanSt s d t bb e blk flag value cursor).mem ob = some obc := by
    show (scanMemAfter s.mem 1006 bb t e blk flag value cursor) ob = _
    rw [hrest ob ho6 hot]; exact hob
  have hl5s : (scanSt s d t bb e blk flag value cursor).locals 5 = some (.ptr ob 0) := by
    show (s.locals.upd d _) 5 = _
    simp [Locals.upd, Ne.symm hd5, hl5]
  have hld : (scanSt s d t bb e blk flag value cursor).locals d =
      some (.int ⟨8, false⟩ (if flag then 1 else 0)) := by
    show (s.locals.upd d _) d = _
    simp [Locals.upd]
  have hv : EvE Gen.prog (scanSt s d t bb e blk flag value cursor) (.var d)
      (.int ⟨8, false⟩ (if flag then 1 else 0)) := EvE.var hld
  have hlocs : ∀ i, i ≠ d → (scanSt s d t bb e blk flag value cursor).locals i = s.locals i := by
    intro i hi; show (s.locals.upd d _) i = _; simp [Locals.upd, hi]
  cases flag with
  | false =>
    have hite : ExS Gen.prog (scanSt s d t bb e blk false value cursor)
        (.ite (.var d) (.call none 3 [(.load (.int ⟨32, true⟩) (.const (.ptr t 0))), (.var nl),
          (.field (.var 5) off)]) .skip) .normal
        (scanSt s d t bb e blk false value cursor) :=
      ExS.ite hv (bc := false) (by simp [truthy])
        (by simpa using (ExS.skip (p := Gen.prog) (s := scanSt s d t bb e blk false value cursor)))
    exact ⟨_, ExS.seq hscan hite, hFs, hlocs, by simpa using hobs⟩
  | true =>
    have hvt := hval rfl
    have hvt' : (scanSt s d t bb e blk true value cursor).mem t =
        some (splice blk 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value))) := hvt
    have hrng := inRange_of_scan value (scanInt_success_value_range _ _ hpure)
    have hvl : 4 ≤ (splice blk 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value))).length := by
      rw [splice_length _ _ _ (by simp [encodeLE_length]; omega)]; exact hl4
    have hvx : (splice blk 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value))).take 4 =
        encodeLE 4 (IntTy.wrap IntTy.i32 value) := by
      have := splice_front blk (encodeLE 4 (IntTy.wrap IntTy.i32 value)) (by simp [encodeLE_length]; omega)
      simpa [encodeLE_length] using this
    have hl5' : (scanSt s d t bb e blk true value cursor).locals 5 = some (.ptr ob 0) := hl5s
    have hln' : (scanSt s d t bb e blk true value cursor).locals nl = some (.int u64 n) := by
      rw [hlocs nl (Ne.symm hdn)]; exact hln
    have hcall := call_fix_none (scanSt s d t bb e blk true value cursor) t ob nl off _ obc
      value n hn hvt' hvl hvx hrng hl5' hln' hobs hoff hFs.ro
    have hv1 : EvE Gen.prog (scanSt s d t bb e blk true value cursor) (.var d)
        (.int ⟨8, false⟩ 1) := by simpa using hv
    have hite := ExS.ite (p := Gen.prog) hv1 (bc := true) (by simp [truthy])
      (a := (.call none 3 [(.load (.int ⟨32, true⟩) (.const (.ptr t 0))), (.var nl),
          (.field (.var 5) off)])) (b := .skip) (by simpa using hcall)
    refine ⟨_, ExS.seq hscan hite, ?_, ?_, ?_⟩
    · exact pcf_ob_update _ bb ob bytes e cursor hD hFs _ _
    · intro i hi; exact hlocs i hi
    · show (_ : Mem) ob = _
      simp [Mem.upd_same]


theorem spec_g1 (bytes : Block) (q : Nat) :
    ((bytes.map UInt8.toNat)[q]? == some 47) =
      decide (q < bytes.length ∧ bytes[q]?.map UInt8.toNat = some 47) := by
  by_cases h : q < bytes.length
  · simp [List.getElem?_map, h]
    rw [Bool.eq_iff_iff]; simp
  · have : bytes[q]? = none := List.getElem?_eq_none (by omega)
    simp [List.getElem?_map, this, h]

theorem spec_g2 (bytes : Block) (q : Nat) :
    (decide (q < (bytes.map UInt8.toNat).length) && ((bytes.map UInt8.toNat)[q]? != some 47)) =
      decide (q < bytes.length ∧ bytes[q]?.map UInt8.toNat ≠ some 47) := by
  by_cases h : q < bytes.length
  · simp [List.getElem?_map, h]
    rw [Bool.eq_iff_iff]; simp
  · simp [h]

def pcOpt (d t nl off : Nat) : Stmt :=
  (.seq (.call (some d) 24 [(.field (.const (.ptr 1006 0)) 0), pcE, (.const (.ptr t 0))])
    (.ite (.var d) (.call none 3 [(.load (.int ⟨32, true⟩) (.const (.ptr t 0))),
      (.var nl), (.field (.var 5) off)]) .skip))

def pcSlash : Stmt :=
  (.ite pcG1 (.seq pcStp (.seq (.ite pcG2 (pcOpt 11 1010 3 8) .skip)
    (.ite pcG1 (.seq pcStp (pcOpt 13 1012 4 4)) .skip))) .skip)

/-- Spec of the optional texture-coordinate scan at offset `c2`. -/
def tcSpec (bytes : Block) (c2 b : Nat) : Int × Nat :=
  if decide (c2 < (bytes.map UInt8.toNat).length) && ((bytes.map UInt8.toNat)[c2]? != some 47)
  then scanIdx (bytes.map UInt8.toNat) c2 b else (-1, c2)

theorem pc_if2 (sB : State) (bb ob : Nat) (bytes oblk : Block) (b : Nat) (v0 : Int)
    (c2 e : Nat)
    (hD : PCD bb ob) (hF : PCF sB bb ob bytes e c2) (hb32 : bb < 4294967295)
    (hc2 : c2 ≤ e) (he : e ≤ bytes.length) (hlen32 : e < 4294967296) (hb : b < 2147483648)
    (l3 : sB.locals 3 = some (.int u64 b)) (l5 : sB.locals 5 = some (.ptr ob 0))
    (h12 : 12 ≤ oblk.length) (hob : sB.mem ob = some (gflat oblk v0 (-1) (-1))) :
    ∃ sC : State, ExS Gen.prog sB (.ite pcG2 (pcOpt 11 1010 3 8) .skip) .normal sC ∧
      PCF sC bb ob bytes e (tcSpec (bytes.take e) c2 b).2 ∧ (∀ i, i ≠ 11 → sC.locals i = sB.locals i) ∧
      sC.mem ob = some (gflat oblk v0 (-1) (tcSpec (bytes.take e) c2 b).1) := by
  have hg2 := g2_eval sB bb ob bytes e c2 hF hb32 hc2 hlen32
  by_cases hG : decide (c2 < e ∧ (bytes.take e)[c2]?.map UInt8.toNat ≠ some 47) = true
  · have hts : tcSpec (bytes.take e) c2 b = scanIdx ((bytes.take e).map UInt8.toNat) c2 b := by
      unfold tcSpec
      rw [spec_g2]
      rw [show (bytes.take e).length = e from by simp [List.length_take, hF.he]]
      rw [if_pos hG]
    rcases hT : scanInt ((bytes.take e).map UInt8.toNat) c2 with ⟨fT, vT, cT⟩
    have hgl : (gflat oblk v0 (-1) (-1)).length = oblk.length := gflat_len _ _ _ _ h12
    obtain ⟨sC, hopt, hFC, hloc, hmemC⟩ := opt_scan sB 11 1010 3 8 bb ob bytes
      (gflat oblk v0 (-1) (-1)) c2 b e hD (Or.inr (Or.inl rfl)) hF hc2 he hb32 hlen32 hb (by decide)
      (by decide) l5 l3 hob (by omega) hT
    have hg2t : EvE Gen.prog sB pcG2 (boolVal true) := by
      have := hg2; rw [hG] at this; simpa using this
    have hite := ExS.ite (p := Gen.prog) hg2t (bc := true) (by simp [truthy, boolVal])
      (a := pcOpt 11 1010 3 8) (b := .skip) (by exact hopt)
    refine ⟨sC, hite, ?_, hloc, ?_⟩
    · rw [hts]; unfold scanIdx; rw [hT]; exact hFC
    · rw [hts]; unfold scanIdx; rw [hT]
      cases fT
      · simpa using hmemC
      · simp at hmemC ⊢
        rw [hmemC, gflat_set8 oblk v0 (-1) (-1) _ h12]
  · have hG' : ¬ (decide (c2 < e ∧ (bytes.take e)[c2]?.map UInt8.toNat ≠ some 47) = true) := hG
    have hts : tcSpec (bytes.take e) c2 b = (-1, c2) := by
      unfold tcSpec
      rw [spec_g2]
      rw [show (bytes.take e).length = e from by simp [List.length_take, hF.he]]
      rw [if_neg hG']
    have hg2f : EvE Gen.prog sB pcG2 (boolVal false) := by
      have := hg2
      have hf : decide (c2 < e ∧ (bytes.take e)[c2]?.map UInt8.toNat ≠ some 47) = false := by
        simpa using hG'
      rw [hf] at this; exact this
    have hite := ExS.ite (p := Gen.prog) hg2f (bc := false) (by simp [truthy, boolVal])
      (a := pcOpt 11 1010 3 8) (b := .skip) (by simpa using (ExS.skip (p := Gen.prog) (s := sB)))
    refine ⟨sB, hite, ?_, fun _ _ => rfl, ?_⟩
    · rw [hts]; exact hF
    · rw [hts]; exact hob

/-- Spec of the optional normal-index scan after the (optional) texture coordinate. -/
def nSpec (bytes : Block) (cur c : Nat) : Int :=
  if ((bytes.map UInt8.toNat)[cur]? == some 47) then
    (scanIdx (bytes.map UInt8.toNat) (cur + 1) c).1 else -1

theorem pc_if3 (sC : State) (bb ob : Nat) (bytes oblk : Block) (c : Nat) (v0 tt : Int)
    (cur e : Nat)
    (hD : PCD bb ob) (hF : PCF sC bb ob bytes e cur) (hb32 : bb < 4294967295)
    (hcur : cur ≤ e) (he : e ≤ bytes.length) (hlen32 : e < 4294967296) (hc : c < 2147483648)
    (l4 : sC.locals 4 = some (.int u64 c)) (l5 : sC.locals 5 = some (.ptr ob 0))
    (h12 : 12 ≤ oblk.length) (hob : sC.mem ob = some (gflat oblk v0 (-1) tt)) :
    ∃ sD : State, ExS Gen.prog sC (.ite pcG1 (.seq pcStp (pcOpt 13 1012 4 4)) .skip) .normal sD ∧
      (∀ i, i ≠ 13 → sD.locals i = sC.locals i) ∧
      sD.mem ob = some (gflat oblk v0 (nSpec (bytes.take e) cur c) tt) := by
  have hg1 := g1_eval sC bb ob bytes e cur hF hb32 hcur hlen32
  have hgl : (gflat oblk v0 (-1) tt).length = oblk.length := gflat_len _ _ _ _ h12
  by_cases hG : decide (cur < e ∧ (bytes.take e)[cur]?.map UInt8.toNat = some 47) = true
  · have hns : nSpec (bytes.take e) cur c = (scanIdx ((bytes.take e).map UInt8.toNat) (cur + 1) c).1 := by
      unfold nSpec
      rw [spec_g1]
      rw [show (bytes.take e).length = e from by simp [List.length_take, hF.he]]
      rw [if_pos hG]
    have hlt : cur < e := by simpa using (decide_eq_true_iff.mp hG).1
    obtain ⟨hexs, hFB⟩ := stp_exs sC bb ob bytes e cur hD hF hb32 hlt hlen32
    rcases hT : scanInt ((bytes.take e).map UInt8.toNat) (cur + 1) with ⟨fT, vT, cT⟩
    have hobB : (stpSt sC bb e cur).mem ob = some (gflat oblk v0 (-1) tt) := by
      show (sC.mem.upd 1006 _) ob = _
      rw [Mem.upd_ne _ _ hD.o6]; exact hob
    obtain ⟨sD, hopt, hFD, hloc, hmemD⟩ := opt_scan (stpSt sC bb e cur) 13 1012 4 4 bb ob
      bytes (gflat oblk v0 (-1) tt) (cur + 1) c e hD (Or.inr (Or.inr rfl)) hFB (by omega) he hb32 hlen32
      hc (by decide) (by decide) (by simpa [stpSt] using l5) (by simpa [stpSt] using l4) hobB
      (by omega) hT
    have hg1t : EvE Gen.prog sC pcG1 (boolVal true) := by
      have := hg1; rw [hG] at this; simpa using this
    have hite := ExS.ite (p := Gen.prog) hg1t (bc := true) (by simp [truthy, boolVal])
      (a := .seq pcStp (pcOpt 13 1012 4 4)) (b := .skip)
      (by exact ExS.seq hexs hopt)
    refine ⟨sD, hite, fun i hi => ?_, ?_⟩
    · rw [hloc i hi]; rfl
    · rw [hns]; unfold scanIdx; rw [hT]
      cases fT
      · simpa using hmemD
      · simp at hmemD ⊢
        rw [hmemD, gflat_set4 oblk v0 (-1) tt _ h12]
  · have hG' : ¬ (decide (cur < e ∧ (bytes.take e)[cur]?.map UInt8.toNat = some 47) = true) := hG
    have hns : nSpec (bytes.take e) cur c = -1 := by
      unfold nSpec
      rw [spec_g1]
      rw [show (bytes.take e).length = e from by simp [List.length_take, hF.he]]
      rw [if_neg hG']
    have hf : decide (cur < e ∧ (bytes.take e)[cur]?.map UInt8.toNat = some 47) = false := by
      simpa using hG'
    have hg1f : EvE Gen.prog sC pcG1 (boolVal false) := by
      have := hg1; rw [hf] at this; exact this
    have hite := ExS.ite (p := Gen.prog) hg1f (bc := false) (by simp [truthy, boolVal])
      (a := .seq pcStp (pcOpt 13 1012 4 4)) (b := .skip)
      (by simpa using (ExS.skip (p := Gen.prog) (s := sC)))
    refine ⟨sC, hite, fun _ _ => rfl, ?_⟩
    rw [hns]; exact hob

theorem scanInt_cursor_le (bytes : Block) (pos : Nat) (hpos : pos ≤ bytes.length)
    {f : Bool} {v : Int} {c : Nat} (h : scanInt (bytes.map UInt8.toNat) pos = (f, v, c)) :
    c ≤ bytes.length := by
  rw [scanInt_eq2] at h
  have hs := skipStop_le bytes pos hpos
  generalize hL : bytes.drop (p1Of bytes (skipStop bytes pos)) = L at h
  have hp1 : p1Of bytes (skipStop bytes pos) ≤ bytes.length ∨ L = [] := by
    by_cases hle : p1Of bytes (skipStop bytes pos) ≤ bytes.length
    · exact Or.inl hle
    · right; rw [← hL]; exact List.drop_eq_nil_of_le (by omega)
  cases L with
  | nil => simp [scanIntDigits] at h; omega
  | cons x tl =>
    have hp : p1Of bytes (skipStop bytes pos) ≤ bytes.length := by
      rcases hp1 with h1 | h1
      · exact h1
      · simp at h1
    by_cases hd : scanDigit x.toNat = true
    · simp [scanIntDigits, hd] at h
      obtain ⟨_, _, hc⟩ := h
      rw [← hc]
      have hlen : (bytes.drop (p1Of bytes (skipStop bytes pos))).length = bytes.length - p1Of bytes (skipStop bytes pos) := List.length_drop ..
      rw [hL] at hlen
      have hcnt : (scanDigits (x.toNat :: tl.map UInt8.toNat) 0).1 ≤ (x :: tl).length := by
        rw [scanDigits_count_exact]
        have := (List.takeWhile_prefix scanDigit (l := x.toNat :: tl.map UInt8.toNat)).length_le
        simpa using this
      simp at hcnt hlen
      omega
    · simp [scanIntDigits, hd] at h
      omega

theorem pc_tail (sA : State) (bb ob : Nat) (bytes oblk : Block) (e a b c : Nat)
    (value : Int) (c1 : Nat)
    (hD : PCD bb ob) (hF : PCF sA bb ob bytes e c1) (hb32 : bb < 4294967295)
    (hc1 : c1 ≤ e) (he : e ≤ bytes.length) (hlen32 : e < 4294967296)
    (hb : b < 2147483648) (hc : c < 2147483648)
    (l3 : sA.locals 3 = some (.int u64 b)) (l4 : sA.locals 4 = some (.int u64 c))
    (l5 : sA.locals 5 = some (.ptr ob 0)) (h12 : 12 ≤ oblk.length)
    (hob : sA.mem ob = some (gflat oblk (storedIndex value a) (-1) (-1)))
    (hs1 : scanInt ((bytes.take e).map UInt8.toNat) 0 = (true, value, c1)) :
    ∃ sf : State, ExS Gen.prog sA pcSlash .normal sf ∧ (∀ i, i ≠ 11 → i ≠ 13 → sf.locals i = sA.locals i) ∧
      sf.mem ob = some (gflat oblk (storedIndex value a)
        (parseCornerN ((bytes.take e).map UInt8.toNat) a b c).1.n
        (parseCornerN ((bytes.take e).map UInt8.toNat) a b c).1.t) := by
  have hmain : parseCornerN ((bytes.take e).map UInt8.toNat) a b c =
      (let c2 := c1 + 1
       let tc : Int × Nat := if decide (c2 < ((bytes.take e).map UInt8.toNat).length) &&
          (((bytes.take e).map UInt8.toNat)[c2]? != some 47)
          then scanIdx ((bytes.take e).map UInt8.toNat) c2 b
          else (-1, c2)
       let n : Int := if (((bytes.take e).map UInt8.toNat)[tc.2]? == some 47) then
          (scanIdx ((bytes.take e).map UInt8.toNat) (tc.2 + 1) c).1 else -1
       if (((bytes.take e).map UInt8.toNat)[c1]? == some 47) then
         (⟨storedIndex value a, tc.1, n⟩, (resolveIndex value a).isSome)
       else (⟨storedIndex value a, -1, -1⟩, (resolveIndex value a).isSome)) := by
    unfold parseCornerN
    rw [hs1]
  rw [hmain]
  have hg1 := g1_eval sA bb ob bytes e c1 hF hb32 hc1 hlen32
  have hgl : (gflat oblk (storedIndex value a) (-1) (-1)).length = oblk.length := gflat_len _ _ _ _ h12
  by_cases hG : decide (c1 < e ∧ (bytes.take e)[c1]?.map UInt8.toNat = some 47) = true
  · have hlt : c1 < e := by simpa using (decide_eq_true_iff.mp hG).1
    obtain ⟨hexs, hFB⟩ := stp_exs sA bb ob bytes e c1 hD hF hb32 hlt hlen32
    have hobB : (stpSt sA bb e c1).mem ob = some (gflat oblk (storedIndex value a) (-1) (-1)) := by
      show (sA.mem.upd 1006 _) ob = _
      rw [Mem.upd_ne _ _ hD.o6]; exact hob
    obtain ⟨sC, hif2, hFC, hloc2, hmem2⟩ := pc_if2 (stpSt sA bb e c1) bb ob bytes oblk b
      (storedIndex value a) (c1 + 1) e hD hFB hb32 (by omega) he hlen32 hb (by simpa [stpSt] using l3)
      (by simpa [stpSt] using l5) h12 hobB
    have hcur : (tcSpec (bytes.take e) (c1 + 1) b).2 ≤ e := by
      unfold tcSpec
      split
      · unfold scanIdx
        rcases hT : scanInt ((bytes.take e).map UInt8.toNat) (c1 + 1) with ⟨fT, vT, cT⟩
        simp only []
        have hpos : c1 + 1 ≤ (bytes.take e).length := by
          simp [List.length_take, he]; omega
        have := scanInt_cursor_le (bytes.take e) (c1 + 1) hpos hT
        rwa [show (bytes.take e).length = e from by simp [List.length_take, he]] at this
      · simp; omega
    obtain ⟨sD, hif3, hloc3, hmem3⟩ := pc_if3 sC bb ob bytes oblk c (storedIndex value a)
      (tcSpec (bytes.take e) (c1 + 1) b).1 (tcSpec (bytes.take e) (c1 + 1) b).2 e hD hFC hb32 hcur he hlen32 hc
      (by rw [hloc2 4 (by omega)]; simpa [stpSt] using l4)
      (by rw [hloc2 5 (by omega)]; simpa [stpSt] using l5) h12 hmem2
    have hg1t : EvE Gen.prog sA pcG1 (boolVal true) := by
      have := hg1; rw [hG] at this; simpa using this
    have hite := ExS.ite (p := Gen.prog) hg1t (bc := true) (by simp [truthy, boolVal])
      (a := .seq pcStp (.seq (.ite pcG2 (pcOpt 11 1010 3 8) .skip)
        (.ite pcG1 (.seq pcStp (pcOpt 13 1012 4 4)) .skip))) (b := .skip)
      (by exact ExS.seq hexs (ExS.seq hif2 hif3))
    refine ⟨sD, hite, fun i h11 h13 => ?_, ?_⟩
    · rw [hloc3 i h13, hloc2 i h11]; rfl
    · rw [spec_g1] at *
      rw [show (bytes.take e).length = e from by simp [List.length_take, he]]
      rw [if_pos hG]
      exact hmem3
  · have hG' : ¬ (decide (c1 < e ∧ (bytes.take e)[c1]?.map UInt8.toNat = some 47) = true) := hG
    have hf : decide (c1 < e ∧ (bytes.take e)[c1]?.map UInt8.toNat = some 47) = false := by
      simpa using hG'
    have hg1f : EvE Gen.prog sA pcG1 (boolVal false) := by
      have := hg1; rw [hf] at this; exact this
    have hite := ExS.ite (p := Gen.prog) hg1f (bc := false) (by simp [truthy, boolVal])
      (a := .seq pcStp (.seq (.ite pcG2 (pcOpt 11 1010 3 8) .skip)
        (.ite pcG1 (.seq pcStp (pcOpt 13 1012 4 4)) .skip))) (b := .skip)
      (by simpa using (ExS.skip (p := Gen.prog) (s := sA)))
    refine ⟨sA, hite, fun _ _ _ => rfl, ?_⟩
    rw [spec_g1] at *
    rw [show (bytes.take e).length = e from by simp [List.length_take, he]]
    rw [if_neg hG']
    exact hob


/-- **`parse_corner_n_f` refines `Obj.parseCornerN`** (token in its own block `bb`,
    starting at offset 0): the return flag is the pure `ok` flag, and the 12-byte
    output record holds the pure `(vertex, normal, texcoord)` indices. -/
theorem parse_corner_n_f_refines (m : Mem) (bb ob : Nat) (bytes oblk cblk b7 b10 b12 : Block)
    (a b c e : Nat) (hD : PCD bb ob) (hbb : m bb = some bytes) (hob : m ob = some oblk)
    (h12 : 12 ≤ oblk.length) (hcc : m 1006 = some cblk) (hcl : cblk.length = 16)
    (h7 : m 1007 = some b7) (h7l : 4 ≤ b7.length) (h10 : m 1010 = some b10) (h10l : 4 ≤ b10.length)
    (h12' : m 1012 = some b12) (h12l : 4 ≤ b12.length)
    (hb32 : bb < 4294967295) (he : e ≤ bytes.length) (hlen32 : e < 4294967296)
    (ha : a < 2147483648) (hb : b < 2147483648) (hc : c < 2147483648) :
    ∃ s' : State, ExS Gen.prog ⟨frameLocals Gen.parse_corner_n_f.params
        [.ptr bb 0, .int u64 e, .int u64 a, .int u64 b, .int u64 c, .ptr ob 0], m, false⟩
        Gen.parse_corner_n_f.body
        (.ret (some (.int ⟨8, false⟩
          (if (parseCornerN ((bytes.take e).map UInt8.toNat) a b c).2 then 1 else 0)))) s' ∧
      s'.mem ob = some (gflat oblk (parseCornerN ((bytes.take e).map UInt8.toNat) a b c).1.v
        (parseCornerN ((bytes.take e).map UInt8.toNat) a b c).1.n
        (parseCornerN ((bytes.take e).map UInt8.toNat) a b c).1.t) := by
  rcases hs : scanInt ((bytes.take e).map UInt8.toNat) 0 with ⟨flag, value, c1⟩
  obtain ⟨blk7, h7', h7l', s2, hpre, hF, hobs, hl, l8, hval⟩ := pc_prefix m bb ob bytes oblk cblk b7 b10
    b12 a b c e hD hbb hob h12 hcc hcl h7 h7l h10 h10l h12' h12l hb32 he hlen32 hs
  have l5 : s2.locals 5 = some (.ptr ob 0) := by
    rw [hl 5 (by omega)]
    simp [frameLocals, Gen.parse_corner_n_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s2.locals 2 = some (.int u64 a) := by
    rw [hl 2 (by omega)]
    simp [frameLocals, Gen.parse_corner_n_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l3 : s2.locals 3 = some (.int u64 b) := by
    rw [hl 3 (by omega)]
    simp [frameLocals, Gen.parse_corner_n_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l4 : s2.locals 4 = some (.int u64 c) := by
    rw [hl 4 (by omega)]
    simp [frameLocals, Gen.parse_corner_n_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hv8 : EvE Gen.prog s2 (.var 8) (.int ⟨8, false⟩ (if flag then 1 else 0)) := EvE.var l8
  cases flag with
  | false =>
    have hpc : parseCornerN ((bytes.take e).map UInt8.toNat) a b c = (Idx.none, false) := by
      unfold parseCornerN; rw [hs]
    have hnot : EvE Gen.prog s2 (.un .lnot ⟨32, true⟩ (.var 8)) (boolVal true) :=
      EvE.un (by simpa using hv8) (by simp [evalUn, truthy, boolVal])
    have hret : EvE Gen.prog s2 (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
        (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 0) :=
      EvE.cond (EvE.const _) (bc := false) (by simp [truthy]) (EvE.const _)
    have hif1 : ExS Gen.prog s2 (.ite (.un .lnot ⟨32, true⟩ (.var 8))
        (.ret (some (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
          (.const (.int ⟨8, false⟩ 0))))) .skip) (.ret (some (.int ⟨8, false⟩ 0))) s2 :=
      ExS.ite hnot (bc := true) (by simp [truthy, boolVal]) (ExS.ret hret)
    rw [hpc]
    refine ⟨s2, hpre _ _ _ (ExS.seq_ret (by simpa using hif1)), ?_⟩
    simpa [Idx.none] using hobs
  | true =>
    have hok : (parseCornerN ((bytes.take e).map UInt8.toNat) a b c).2 = (resolveIndex value a).isSome ∧
        (parseCornerN ((bytes.take e).map UInt8.toNat) a b c).1.v = storedIndex value a := by
      unfold parseCornerN; rw [hs]
      simp only []
      split <;> simp
    rw [hok.1, hok.2]
    have hnot : EvE Gen.prog s2 (.un .lnot ⟨32, true⟩ (.var 8)) (boolVal false) :=
      EvE.un (by simpa using hv8) (by simp [evalUn, truthy, boolVal])
    have hif1 : ExS Gen.prog s2 (.ite (.un .lnot ⟨32, true⟩ (.var 8))
        (.ret (some (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
          (.const (.int ⟨8, false⟩ 0))))) .skip) .normal s2 :=
      ExS.ite hnot (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.skip (p := Gen.prog) (s := s2)))
    have hvt := hval rfl
    have hrng := inRange_of_scan value (scanInt_success_value_range _ _ hs)
    have hvl : 4 ≤ (splice blk7 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value))).length := by
      rw [splice_length _ _ _ (by simp [encodeLE_length]; omega)]; exact h7l'
    have hvx : (splice blk7 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value))).take 4 =
        encodeLE 4 (IntTy.wrap IntTy.i32 value) := by
      have := splice_front blk7 (encodeLE 4 (IntTy.wrap IntTy.i32 value)) (by simp [encodeLE_length]; omega)
      simpa [encodeLE_length] using this
    have hgl : (gflat oblk (-1) (-1) (-1)).length = oblk.length := gflat_len _ _ _ _ h12
    have hcall := call_fix s2 9 1007 ob 2 0 _ _ value a ha hvt hvl hvx hrng l5 l2 hobs (by omega) hF.ro
    let s3 : State := { s2 with mem := (s2.mem.upd ob (splice (gflat oblk (-1) (-1) (-1)) 0 (encodeLE 4 (IntTy.wrap IntTy.i32 (storedIndex value a))))), locals := (s2.locals.upd 9 (.int ⟨8, false⟩ (if (resolveIndex value a).isSome then 1 else 0))) }
    have hF3 : PCF s3 bb ob bytes e c1 := pcf_ob_update s2 bb ob bytes e c1 hD hF _ _
    have hob3 : s3.mem ob = some (gflat oblk (storedIndex value a) (-1) (-1)) := by
      show (s2.mem.upd ob _) ob = _
      rw [Mem.upd_same, gflat_set0 oblk (-1) (-1) (-1) _ h12]
    have l3_3 : s3.locals 3 = some (.int u64 b) := by simpa [s3, Locals.upd] using l3
    have l4_3 : s3.locals 4 = some (.int u64 c) := by simpa [s3, Locals.upd] using l4
    have l5_3 : s3.locals 5 = some (.ptr ob 0) := by simpa [s3, Locals.upd] using l5
    have hc1 : c1 ≤ e := by
      have := scanInt_cursor_le (bytes.take e) 0 (by simp [List.length_take, he]) hs
      rwa [show (bytes.take e).length = e from by simp [List.length_take, he]] at this
    obtain ⟨sf, htail, hloc, hmemf⟩ := pc_tail s3 bb ob bytes oblk e a b c value c1 hD hF3 hb32 hc1 he hlen32 hb hc
      l3_3 l4_3 l5_3 h12 hob3 hs
    have hv9 : EvE Gen.prog sf (.var 9) (.int ⟨8, false⟩ (if (resolveIndex value a).isSome then 1 else 0)) := by
      apply EvE.var
      rw [hloc 9 (by omega) (by omega)]
      simp [s3, Locals.upd]
    refine ⟨sf, hpre _ _ _ (ExS.seq hif1 (ExS.seq hcall (ExS.seq htail (ExS.ret hv9)))), ?_⟩
    exact hmemf

end Obj.C.Proofs

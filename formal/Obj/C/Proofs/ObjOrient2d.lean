import Obj.C.Proofs.ObjTessEmit
namespace Obj.C.Proofs
open Obj.C Obj

/-! ### Loading a `double` out of a byte block -/

/-- A `double` at byte offset `o` reads back as its bit pattern, given the eight
    bytes there are `encodeLE 8 bits` and `bits` fits in 64 bits. -/
theorem load_f64_at (m : Mem) (b o : Nat) (blk : Block) (bits : Nat)
    (hm : m b = some blk) (hbits : bits < 2 ^ 64)
    (hbytes : (blk.drop o).take 8 = encodeLE 8 bits) :
    load m .f64 (.ptr b o) = .ok (.f64 bits) := by
  have hlen : (encodeLE 8 bits).length = 8 := encodeLE_length 8 bits
  have ho : o + 8 ≤ blk.length := by
    have h2 : (blk.drop o).length = blk.length - o := List.length_drop
    have h4 : 8 ≤ (blk.drop o).length := by
      have h5 : (List.take 8 (blk.drop o)).length = 8 := by rw [hbytes, hlen]
      have h6 : (List.take 8 (blk.drop o)).length ≤ (blk.drop o).length :=
        List.length_take_le' 8 (blk.drop o)
      omega
    omega
  have hrb : readBytes m b o 8 = .ok (encodeLE 8 bits) := by
    simp only [readBytes, hm]
    rw [if_pos ho, hbytes]
  have hsz : Ty.size .f64 = 8 := rfl
  simp only [load, hsz, hrb, Res.bind_eq, Res.bind_ok]
  rw [decodeLE_encodeLE, Nat.mod_eq_of_lt hbits]
  rfl

/-- If the block is the concatenation of the chunks leading up to `pre`, the
    double at `pre.length` reads back as `bits`. -/
theorem load_f64_splice (m : Mem) (b : Nat) (pre post : Block) (bits : Nat)
    (hm : m b = some (pre ++ encodeLE 8 bits ++ post)) (hbits : bits < 2 ^ 64) :
    load m .f64 (.ptr b pre.length) = .ok (.f64 bits) := by
  have hlen : (encodeLE 8 bits).length = 8 := encodeLE_length 8 bits
  refine load_f64_at m b pre.length _ bits hm hbits ?_
  simp [List.drop_append, hlen]

/-! ### Indexing a `double` array -/

/-- `p[0]` where `p` is a `double *`: the address is `p` itself. -/
theorem index_const0 (s : State) (b : Nat) (blk : Block) (v : Nat)
    (hv : EvE Gen.prog s (.var v) (.ptr b 0)) (hm : s.mem b = some blk) :
    EvE Gen.prog s (.index (.var v) (.const (.int ⟨32, true⟩ 0)) 8) (.ptr b 0) := by
  apply EvE.index hv (EvE.const _)
  have h1 : IntTy.toInt ⟨32, true⟩ 0 = 0 := by simp [IntTy.toInt]
  simp [ptrAdd, hm, h1]

/-- `p[1]` where `p` is a `double *`: the address is `p + 8`. -/
theorem index_const1 (s : State) (b : Nat) (blk : Block) (v : Nat)
    (hv : EvE Gen.prog s (.var v) (.ptr b 0)) (hm : s.mem b = some blk)
    (hb : 8 ≤ blk.length) :
    EvE Gen.prog s (.index (.var v) (.const (.int ⟨32, true⟩ 1)) 8) (.ptr b 8) := by
  apply EvE.index hv (EvE.const _)
  have h1 : IntTy.toInt ⟨32, true⟩ 1 = 1 := by simp [IntTy.toInt]
  simp [ptrAdd, hm, h1]
  omega

/-! ### The pure model of `orient2d` -/

/-- Bit-level model of `(b0-a0)*(c1-a1) - (b1-a1)*(c0-a0)`, matching the
    generated body's `add(mul(...), neg(mul(...)))` shape. -/
def orient2dGen (a0 a1 b0 b1 c0 c1 : Nat) : Nat :=
  F64.addBits (F64.mulBits (F64.subBits b0 a0) (F64.subBits c1 a1))
    (F64.negBits (F64.mulBits (F64.subBits b1 a1) (F64.subBits c0 a0)))

/-- The plain mathematical reading of the same expression. -/
def orient2dVal (a0 a1 b0 b1 c0 c1 : Nat) : Nat :=
  F64.subBits (F64.mulBits (F64.subBits b0 a0) (F64.subBits c1 a1))
    (F64.mulBits (F64.subBits b1 a1) (F64.subBits c0 a0))

theorem orient2dGen_eq (a0 a1 b0 b1 c0 c1 : Nat) :
    orient2dGen a0 a1 b0 b1 c0 c1 = orient2dVal a0 a1 b0 b1 c0 c1 := by
  unfold orient2dGen orient2dVal
  simp only [F64.subBits]

/-! ### Float operation evaluation -/

theorem evalBin_f64_sub (a b : Nat) :
    evalBin .sub (some ⟨64, false⟩) (.f64 a) (.f64 b) = .ok (.f64 (F64.subBits a b)) := by
  simp [evalBin, isPtr, evalBinInt, binF64]

theorem evalBin_f64_mul (a b : Nat) :
    evalBin .mul (some ⟨64, false⟩) (.f64 a) (.f64 b) = .ok (.f64 (F64.mulBits a b)) := by
  simp [evalBin, isPtr, evalBinInt, binF64]

theorem evalBin_f64_add (a b : Nat) :
    evalBin .add (some ⟨64, false⟩) (.f64 a) (.f64 b) = .ok (.f64 (F64.addBits a b)) := by
  simp [evalBin, isPtr, evalBinInt, binF64]

theorem evalUn_f64_neg (a : Nat) :
    evalUn .neg ⟨64, false⟩ (.f64 a) = .ok (.f64 (F64.negBits a)) := by
  simp [evalUn]

/-! ### The refinement of `tobj_orient2d` -/

/-- **`tobj_orient2d` refines `orient2dVal`.**  For any three `double[2]`
    points held as 16-byte records in blocks `ab`, `bb`, `cb`, the translated
    body returns exactly the pure bit-level value of
    `(b0-a0)*(c1-a1) - (b1-a1)*(c0-a0)`, using the correctly-rounded IEEE-754
    model (`F64`).  The function is a single `return`, so the body proof is
    just evaluation of the expression tree.

    Each block is given as `double[2]` followed by an arbitrary tail, which is
    what a caller inside `tobj_tess_polygon_core` has: `&w->p2d[2*i]` points
    into the `p2d` array. -/
theorem tobj_orient2d_refines (m : Mem) (ab bb cb : Nat) (a0 a1 b0 b1 c0 c1 : Nat)
    (atail btail ctail : Block)
    (hmab : m ab = some (encodeLE 8 a0 ++ encodeLE 8 a1 ++ atail))
    (hmbb : m bb = some (encodeLE 8 b0 ++ encodeLE 8 b1 ++ btail))
    (hmcb : m cb = some (encodeLE 8 c0 ++ encodeLE 8 c1 ++ ctail))
    (hbits : a0 < 2 ^ 64 ∧ a1 < 2 ^ 64 ∧ b0 < 2 ^ 64 ∧ b1 < 2 ^ 64 ∧
      c0 < 2 ^ 64 ∧ c1 < 2 ^ 64) :
    ExS Gen.prog
      ⟨frameLocals Gen.tobj_orient2d.params [.ptr ab 0, .ptr bb 0, .ptr cb 0], m, false⟩
      Gen.tobj_orient2d.body (.ret (some (.f64 (orient2dGen a0 a1 b0 b1 c0 c1))))
      ⟨frameLocals Gen.tobj_orient2d.params [.ptr ab 0, .ptr bb 0, .ptr cb 0], m, false⟩ := by
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1⟩ := hbits
  let s0 : State := ⟨frameLocals Gen.tobj_orient2d.params [.ptr ab 0, .ptr bb 0, .ptr cb 0], m, false⟩
  change ExS Gen.prog s0 Gen.tobj_orient2d.body
    (.ret (some (.f64 (orient2dGen a0 a1 b0 b1 c0 c1)))) s0
  -- locals
  have l0 : s0.locals 0 = some (.ptr ab 0) := by
    simp [s0, frameLocals, Gen.tobj_orient2d, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.ptr bb 0) := by
    simp [s0, frameLocals, Gen.tobj_orient2d, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s0.locals 2 = some (.ptr cb 0) := by
    simp [s0, frameLocals, Gen.tobj_orient2d, List.idxOf?, List.findIdx?, List.findIdx?.go]
  -- addresses p[0] and p[1] for each point
  have hv0 : EvE Gen.prog s0 (.var 0) (.ptr ab 0) := EvE.var l0
  have hv1 : EvE Gen.prog s0 (.var 1) (.ptr bb 0) := EvE.var l1
  have hv2 : EvE Gen.prog s0 (.var 2) (.ptr cb 0) := EvE.var l2
  -- loads: a0 at ab+0, a1 at ab+8, etc.
  have la0 : EvE Gen.prog s0 (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8))
      (.f64 a0) :=
    EvE.load (index_const0 s0 ab _ 0 hv0 hmab) (load_f64_splice m ab [] (encodeLE 8 a1 ++ atail) a0 hmab ha0)
  have la1 : EvE Gen.prog s0 (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8))
      (.f64 a1) := by
    have hidx : EvE Gen.prog s0
        (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8) (.ptr ab 8) :=
      index_const1 s0 ab _ 0 hv0 hmab (by simp [List.length_append, encodeLE_length])
    exact EvE.load hidx (load_f64_splice m ab (encodeLE 8 a0) atail a1 (by simp [hmab]) ha1)
  have lb0 : EvE Gen.prog s0 (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 0)) 8))
      (.f64 b0) :=
    EvE.load (index_const0 s0 bb _ 1 hv1 hmbb) (load_f64_splice m bb [] (encodeLE 8 b1 ++ btail) b0 hmbb hb0)
  have lb1 : EvE Gen.prog s0 (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 1)) 8))
      (.f64 b1) := by
    have hidx : EvE Gen.prog s0
        (.index (.var 1) (.const (.int ⟨32, true⟩ 1)) 8) (.ptr bb 8) :=
      index_const1 s0 bb _ 1 hv1 hmbb (by simp [List.length_append, encodeLE_length])
    exact EvE.load hidx (load_f64_splice m bb (encodeLE 8 b0) btail b1 (by simp [hmbb]) hb1)
  have lc0 : EvE Gen.prog s0 (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 0)) 8))
      (.f64 c0) :=
    EvE.load (index_const0 s0 cb _ 2 hv2 hmcb) (load_f64_splice m cb [] (encodeLE 8 c1 ++ ctail) c0 hmcb hc0)
  have lc1 : EvE Gen.prog s0 (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 1)) 8))
      (.f64 c1) := by
    have hidx : EvE Gen.prog s0
        (.index (.var 2) (.const (.int ⟨32, true⟩ 1)) 8) (.ptr cb 8) :=
      index_const1 s0 cb _ 2 hv2 hmcb (by simp [List.length_append, encodeLE_length])
    exact EvE.load hidx (load_f64_splice m cb (encodeLE 8 c0) ctail c1 (by simp [hmcb]) hc1)
  -- the four differences and two products, then the final add of a negation
  have hsub1 : EvE Gen.prog s0 (.bin .sub (some ⟨64, false⟩)
      (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 0)) 8))
      (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8)))
      (.f64 (F64.subBits b0 a0)) :=
    EvE.bin lb0 la0 (evalBin_f64_sub b0 a0)
  have hsub2 : EvE Gen.prog s0 (.bin .sub (some ⟨64, false⟩)
      (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 1)) 8))
      (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8)))
      (.f64 (F64.subBits c1 a1)) :=
    EvE.bin lc1 la1 (evalBin_f64_sub c1 a1)
  have hsub3 : EvE Gen.prog s0 (.bin .sub (some ⟨64, false⟩)
      (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 1)) 8))
      (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8)))
      (.f64 (F64.subBits b1 a1)) :=
    EvE.bin lb1 la1 (evalBin_f64_sub b1 a1)
  have hsub4 : EvE Gen.prog s0 (.bin .sub (some ⟨64, false⟩)
      (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 0)) 8))
      (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8)))
      (.f64 (F64.subBits c0 a0)) :=
    EvE.bin lc0 la0 (evalBin_f64_sub c0 a0)
  have hmul1 : EvE Gen.prog s0 (.bin .mul (some ⟨64, false⟩)
      (.bin .sub (some ⟨64, false⟩)
        (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 0)) 8))
        (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8)))
      (.bin .sub (some ⟨64, false⟩)
        (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 1)) 8))
        (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8))))
      (.f64 (F64.mulBits (F64.subBits b0 a0) (F64.subBits c1 a1))) :=
    EvE.bin hsub1 hsub2 (evalBin_f64_mul _ _)
  have hmul2 : EvE Gen.prog s0 (.bin .mul (some ⟨64, false⟩)
      (.bin .sub (some ⟨64, false⟩)
        (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 1)) 8))
        (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8)))
      (.bin .sub (some ⟨64, false⟩)
        (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 0)) 8))
        (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8))))
      (.f64 (F64.mulBits (F64.subBits b1 a1) (F64.subBits c0 a0))) :=
    EvE.bin hsub3 hsub4 (evalBin_f64_mul _ _)
  have hneg : EvE Gen.prog s0 (.un .neg ⟨64, false⟩
      (.bin .mul (some ⟨64, false⟩)
        (.bin .sub (some ⟨64, false⟩)
          (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 1)) 8))
          (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8)))
        (.bin .sub (some ⟨64, false⟩)
          (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 0)) 8))
          (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8)))))
      (.f64 (F64.negBits (F64.mulBits (F64.subBits b1 a1) (F64.subBits c0 a0)))) :=
    EvE.un hmul2 (evalUn_f64_neg _)
  have hfinal : EvE Gen.prog s0 (.bin .add (some ⟨64, false⟩)
      (.bin .mul (some ⟨64, false⟩)
        (.bin .sub (some ⟨64, false⟩)
          (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 0)) 8))
          (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8)))
        (.bin .sub (some ⟨64, false⟩)
          (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 1)) 8))
          (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8))))
      (.un .neg ⟨64, false⟩
        (.bin .mul (some ⟨64, false⟩)
          (.bin .sub (some ⟨64, false⟩)
            (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 1)) 8))
            (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8)))
          (.bin .sub (some ⟨64, false⟩)
            (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 0)) 8))
            (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8))))))
      (.f64 (orient2dGen a0 a1 b0 b1 c0 c1)) :=
    EvE.bin hmul1 hneg (evalBin_f64_add _ _)
  have hbody : Gen.tobj_orient2d.body =
      .ret (some (.bin .add (some ⟨64, false⟩)
        (.bin .mul (some ⟨64, false⟩)
          (.bin .sub (some ⟨64, false⟩)
            (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 0)) 8))
            (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8)))
          (.bin .sub (some ⟨64, false⟩)
            (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 1)) 8))
            (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8))))
        (.un .neg ⟨64, false⟩
          (.bin .mul (some ⟨64, false⟩)
            (.bin .sub (some ⟨64, false⟩)
              (.load .f64 (.index (.var 1) (.const (.int ⟨32, true⟩ 1)) 8))
              (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 8)))
            (.bin .sub (some ⟨64, false⟩)
              (.load .f64 (.index (.var 2) (.const (.int ⟨32, true⟩ 0)) 8))
              (.load .f64 (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 8))))))) := rfl
  rw [hbody]
  exact ExS.ret hfinal

end Obj.C.Proofs

/-! ### The pure model of `orient2d` -/

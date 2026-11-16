/-
  Refinement proof for the translated `acmp` in `lib/tess/src/exact.c`.

  `acmp a b` compares two little-endian limb vectors. It returns -1 when the
  first limb-vector mismatch has `a < b`, 1 when it has `a > b`, and 0 when the
  vectors are equal. The n-length mismatch branch in C takes precedence. The
  theorem is over the translated MiniC `acmp`, about arbitrary memories
  containing two `zi` blocks and their limb arrays. Sign is never read.

  Memory blocks are not assumed to come from any allocator; the proof only
  uses the existence and contents of the blocks. No claim is made about the
  surrounding allocator or the `zi` orchestration in `zi_add`.
-/
import Obj.C.Hoare
import Obj.C.Splice
import Tess.C.LimbGen
import Tess.C.ZiMem

namespace Tess.C
open Obj.C

def i32c : IntTy := ⟨32, true⟩

/-- Load the v limb pointer of a `zi` value in memory. -/
theorem evVPointer (s : State) (v : Nat) (zb vblk : Nat) (n : Nat)
    (hm : s.mem zb = some (ziBlock vblk n 1)) (hb : vblk < 4294967296)
    (hl : s.locals v = some (.ptr zb 0)) :
    EvE LimbGen.prog s (.load .ptr (.field (.var v) 0)) (.ptr vblk 0) := by
  have hfield : EvE LimbGen.prog s (.field (.var v) 0) (.ptr zb 0) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  exact EvE.load hfield (load_ziBlock_v s.mem zb vblk n 1 hm hb)

/-- Load limb `j` (at index expression `i - 1` where `i = j + 1`) of a limb array. -/
theorem evLimbLoad (s : State) (v : Nat) (zb vblk : Nat)
    (limbs : List Nat) (j : Nat)
    (hm : s.mem zb = some (ziBlock vblk limbs.length 1)) (hb : vblk < 4294967296)
    (hl : s.locals v = some (.ptr zb 0))
    (hl2 : s.locals 2 = some (.int ⟨64, false⟩ (j + 1)))
    (hlm : s.mem vblk = some (limbBytes limbs)) (hj : j < limbs.length)
    (hlt : ∀ x ∈ limbs, x < 2 ^ 32) (hj64 : j < 18446744073709551616) :
    EvE LimbGen.prog s (.load (.int u32) (.index (.load .ptr (.field (.var v) 0))
        (.bin .sub (some ⟨64, false⟩) (.var 2)
          (.cast u64 (.const (.int i32c 1)))) 4))
      (.int u32 (limbs[j]'hj)) := by
  have hfield : EvE LimbGen.prog s (.field (.var v) 0) (.ptr zb 0) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var v) 0)) (.ptr vblk 0) :=
    EvE.load hfield (load_ziBlock_v s.mem zb vblk limbs.length 1 hm hb)
  have hsub : EvE LimbGen.prog s (.bin .sub (some ⟨64, false⟩) (.var 2)
        (.cast u64 (.const (.int i32c 1)))) (.int ⟨64, false⟩ j) := by
    have h2 : EvE LimbGen.prog s (.var 2) (.int ⟨64, false⟩ (j + 1)) := EvE.var hl2
    have hc : EvE LimbGen.prog s (.const (.int i32c 1)) (.int i32c 1) := EvE.const _
    have hcast : evalCast u64 (.int i32c 1) = .ok (.int ⟨64, false⟩ 1) := rfl
    have hsub' : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ (j + 1)) (.int ⟨64, false⟩ 1) = .ok (.int ⟨64, false⟩ j) := rfl
    exact EvE.bin h2 (EvE.cast hc hcast) hsub'
  have hidxlen : (limbBytes limbs).length = 4 * limbs.length := limbBytes_length limbs
  have hbounds : 0 + j * 4 ≤ (limbBytes limbs).length := by
    rw [hidxlen]
    omega
  have hidx : EvE LimbGen.prog s
      (.index (.load .ptr (.field (.var v) 0))
        (.bin .sub (some ⟨64, false⟩) (.var 2)
          (.cast u64 (.const (.int i32c 1)))) 4)
      (.ptr vblk (0 + j * 4)) := by
    apply EvE.index hloadPtr hsub
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, hlm]
    rw [if_pos hbounds]
  have hload : load s.mem (.int u32) (.ptr vblk (0 + j * 4)) = .ok (.int u32 (limbs[j]'hj)) := by
    have hl4 : 0 + j * 4 = 4 * j := Nat.zero_add _ |>.trans (Nat.mul_comm _ _)
    rw [hl4, load_limb s.mem vblk limbs j hlm hj]
    congr 1
    rw [Nat.mod_eq_of_lt (hlt _ (List.getElem_mem hj))]
  exact EvE.load hidx hload

/-- Unsigned 32-bit comparison evaluation on values coming from limb loads. -/
theorem evGtU32 (x y : Nat) :
    evalBin .gt (some ⟨32, false⟩) (.int ⟨32, false⟩ x) (.int ⟨32, false⟩ y) = .ok (boolVal (decide (x > y))) := rfl

theorem evNeU32 (x y : Nat) :
    evalBin .ne (some ⟨32, false⟩) (.int ⟨32, false⟩ x) (.int ⟨32, false⟩ y) = .ok (boolVal (decide (x ≠ y))) := rfl



/-- ACMP loop AST helpers: the literal expressions produced by the translator.
Kept as `@[reducible]` definitions so the proofs can rewrite to/from them. -/
@[reducible] def acmpIdx : Expr :=
  .index (.load .ptr (.field (.var 0) 0))
    (.bin .sub (some ⟨64, false⟩) (.var 2) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4

@[reducible] def acmpIdxB : Expr :=
  .index (.load .ptr (.field (.var 1) 0))
    (.bin .sub (some ⟨64, false⟩) (.var 2) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4

@[reducible] def acmpLoadA : Expr := .load (.int ⟨32, false⟩) acmpIdx
@[reducible] def acmpLoadB : Expr := .load (.int ⟨32, false⟩) acmpIdxB
@[reducible] def acmpNe : Expr := .bin .ne (some ⟨32, false⟩) acmpLoadA acmpLoadB
@[reducible] def acmpGt : Expr := .bin .gt (some ⟨32, false⟩) acmpLoadA acmpLoadB
@[reducible] def acmpRetCond : Expr :=
  .cond acmpGt (.const (.int ⟨32, true⟩ 1)) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))

@[reducible] def acmpNeU64 : Expr :=
  .bin .ne (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
    (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
@[reducible] def acmpGtU64 : Expr :=
  .bin .gt (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
    (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
@[reducible] def acmpRetCondU64 : Expr :=
  .cond acmpGtU64 (.const (.int ⟨32, true⟩ 1))
    (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))

theorem acmp_loop_ast : LimbGen.acmp_loop0 =
    .loop
      (.ite (.var 2)
        (.ite (acmpNe) (.ret (some acmpRetCond)) .skip)
        .brk)
      (.set 2 (.cast u64 (.bin .sub (some ⟨64, false⟩) (.cast u64 (.var 2))
        (.const (.int ⟨64, false⟩ 1))))) := rfl

/-- u64 subtraction for a counter that stays positive during the step. -/
theorem u64_sub_val (a b : Nat) (h : b ≤ a) (ha : a < 18446744073709551616) :
    evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ a) (.int ⟨64, false⟩ b) = .ok (.int ⟨64, false⟩ (a - b)) := by
  simp only [evalBin, isPtr, Bool.and_false, ite_false]
  show Res.ok (Val.int ⟨64, false⟩ (if b ≤ a then a - b else a + 18446744073709551616 - b)) =
    Res.ok (Val.int ⟨64, false⟩ (a - b))
  rw [if_pos h]

/-- The cast from uint64 to uint64 of an in-range value is itself. -/
theorem cast_u64_u64' (a : Nat) (h : a < 18446744073709551616) :
    evalCast u64 (.int ⟨64, false⟩ a) = .ok (.int ⟨64, false⟩ a) := by
  simp [evalCast, u64, IntTy.modulus, Nat.mod_eq_of_lt h]

/-- The remaining count of unchecked limbs (`i`) in `acmp_loop0` starts from
`n`. While `i > 0` it inspects limb `i - 1`: if the limbs differ it returns
early with the comparison sign; otherwise it decrements. -/
theorem evIdxSub (s : State) (i : Nat) (h2 : s.locals 2 = some (.int ⟨64, false⟩ i)) (hi : 1 ≤ i)
    (hbound : i < 18446744073709551616) :
    EvE LimbGen.prog s (.bin .sub (some ⟨64, false⟩) (.var 2)
      (.cast u64 (.const (.int i32c 1)))) (.int ⟨64, false⟩ (i - 1)) := by
  have h2' : EvE LimbGen.prog s (.var 2) (.int ⟨64, false⟩ i) := EvE.var h2
  have hc : EvE LimbGen.prog s (.const (.int i32c 1)) (.int i32c 1) := EvE.const _
  have hcast : evalCast u64 (.int i32c 1) = .ok (.int u64 1) := rfl
  exact EvE.bin h2' (EvE.cast hc hcast) (u64_sub_val i 1 (by omega) (by omega : i < 18446744073709551616))

/-- Zi blocks for `acmp`: struct block plus limb array, all block indices < 2^32. -/
def AcmpLoopInv (naz avblk nbz bvblk : Nat) (aLimbs bLimbs : List Nat)
    (n : Nat) (i : Nat) (s : State) : Prop :=
  i ≤ n ∧ i < 18446744073709551616 ∧
    s.locals 0 = some (.ptr naz 0) ∧ s.locals 1 = some (.ptr nbz 0) ∧
    s.locals 2 = some (.int ⟨64, false⟩ i) ∧
    (∀ x ∈ aLimbs, x < 2 ^ 32) ∧ (∀ x ∈ bLimbs, x < 2 ^ 32) ∧
    aLimbs.length = n ∧ bLimbs.length = n ∧
    s.mem naz = some (ziBlock avblk n 1) ∧ s.mem nbz = some (ziBlock bvblk n 1) ∧
    s.mem avblk = some (limbBytes aLimbs) ∧ s.mem bvblk = some (limbBytes bLimbs) ∧
    aLimbs.drop i = bLimbs.drop i ∧
    naz < 4294967296 ∧ nbz < 4294967296 ∧ avblk < 4294967296 ∧ bvblk < 4294967296

/-- The inner loop: either it exits normally with all limbs equal (locals 2 = 0),
or it returns early with the comparison sign of the first limb mismatch. -/
theorem acmp_loop_impl (naz avblk nbz bvblk : Nat)
    (aLimbs bLimbs : List Nat) (n : Nat)
    (hlen : aLimbs.length = n) (hlen2 : bLimbs.length = n) :
    ∀ (k : Nat) (s : State), k ≤ n →
    AcmpLoopInv naz avblk nbz bvblk aLimbs bLimbs n k s →
    (∃ sf, ExS LimbGen.prog s LimbGen.acmp_loop0 .normal sf ∧
        aLimbs = bLimbs ∧ sf.locals 2 = some (.int ⟨64, false⟩ 0) ∧ sf.mem = s.mem ∧
        sf.locals 0 = some (.ptr naz 0) ∧ sf.locals 1 = some (.ptr nbz 0)) ∨
    (∃ sf, ExS LimbGen.prog s LimbGen.acmp_loop0 (.ret (some (.int ⟨32, true⟩ 1))) sf ∧
        (∃ j, ∃ hj : j < n, aLimbs.drop (j + 1) = bLimbs.drop (j + 1) ∧
              aLimbs[j]'(by omega) > bLimbs[j]'(by omega))) ∨
    (∃ sf, ExS LimbGen.prog s LimbGen.acmp_loop0 (.ret (some (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))))) sf ∧
        (∃ j, ∃ hj : j < n, aLimbs.drop (j + 1) = bLimbs.drop (j + 1) ∧
              bLimbs[j]'(by omega) > aLimbs[j]'(by omega))) := by
  intro k
  induction k generalizing n with
  | zero =>
      intro s _ hinv
      obtain ⟨_, _, hloc0, hloc1, hloc2, _, _, _, _, _, _, _, _, hdrop, _, _, _, _⟩ := hinv
      refine Or.inl ⟨s, ?_, ?_, ?_, rfl, hloc0, hloc1⟩
      · exact ExS.loop_brk (ExS.ite (EvE.var hloc2) (by rfl) ExS.brk)
      · simpa using hdrop
      · exact hloc2
  | succ k ih =>
      intro s hkn hinv
      obtain ⟨hle, hlt64, hloc0, hloc1, hloc2, hlla, hllb, hna, hnb,
        hnaz, hnbz, havblk, hbvblk, hdrop, hnad, hnad2, hav, hbv⟩ := hinv
      have hjlt : k < n := by omega
      have hjlt' : k < aLimbs.length := by rw [hna]; exact hjlt
      have hjlt2 : k < bLimbs.length := by rw [hnb]; exact hjlt
      have hj64 : (k : Nat) < 18446744073709551616 := by omega
      have hloadA : EvE LimbGen.prog s acmpLoadA
          (.int ⟨32, false⟩ (aLimbs[k]'hjlt')) :=
        evLimbLoad s 0 naz avblk aLimbs k (by rw [hna]; exact hnaz) hav hloc0 hloc2 havblk hjlt' hlla hj64
      have hloadB : EvE LimbGen.prog s acmpLoadB
          (.int ⟨32, false⟩ (bLimbs[k]'hjlt2)) :=
        evLimbLoad s 1 nbz bvblk bLimbs k (by rw [hnb]; exact hnbz) hbv hloc1 hloc2 hbvblk hjlt2 hllb hj64
      have hne : EvE LimbGen.prog s acmpNe
          (boolVal (decide (aLimbs[k]'hjlt' ≠ bLimbs[k]'hjlt2))) :=
        EvE.bin hloadA hloadB (evNeU32 _ _)
      have hgt : EvE LimbGen.prog s acmpGt
          (boolVal (decide (aLimbs[k]'hjlt' > bLimbs[k]'hjlt2))) :=
        EvE.bin hloadA hloadB (evGtU32 _ _)
      by_cases hlimb : aLimbs[k]'hjlt' = bLimbs[k]'hjlt2
      · -- limbs equal: body no-ops, then step decrements i, then recurse
        have hlimb_dec : decide (aLimbs[k]'hjlt' ≠ bLimbs[k]'hjlt2) = false := by
          rw [decide_eq_false_iff_not]; simp [hlimb]
        have hout : EvE LimbGen.prog s (.var 2) (.int ⟨64, false⟩ (k + 1)) := EvE.var hloc2
        have htr : truthy (.int ⟨64, false⟩ (k + 1)) = .ok true := by
          simp [truthy]
        have hbody : ExS LimbGen.prog s (.ite (.var 2) (.ite acmpNe (.ret (some acmpRetCond)) .skip) .brk)
            .normal s :=
          ExS.ite hout htr (ExS.ite hne (by rw [hlimb_dec]; rfl) ExS.skip)
        have cast1 : EvE LimbGen.prog s (.cast ⟨64, false⟩ (.var 2)) (.int ⟨64, false⟩ (k + 1)) :=
          EvE.cast (EvE.var hloc2) (cast_u64_u64' (k + 1) (by omega))
        have subb : EvE LimbGen.prog s (.bin .sub (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 2)) (.const (.int ⟨64, false⟩ 1))) (.int ⟨64, false⟩ k) :=
          EvE.bin cast1 (EvE.const _) (by
            show evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ (k + 1)) (.int ⟨64, false⟩ 1) = .ok (.int ⟨64, false⟩ k)
            simp only [evalBin, isPtr, Bool.and_false, ite_false, Nat.mod_eq_of_lt (by omega : k + 1 < 18446744073709551616)]
            show Res.ok (Val.int ⟨64, false⟩ (if (1:Nat) ≤ k + 1 then k + 1 - 1 else k + 1 + 18446744073709551616 - 1)) = Res.ok (Val.int ⟨64, false⟩ k)
            rw [if_pos (by omega : (1:Nat) ≤ k + 1), Nat.add_sub_cancel])
        have hstep : ExS LimbGen.prog s (.set 2 (.cast ⟨64, false⟩ (.bin .sub (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 2)) (.const (.int ⟨64, false⟩ 1)))))
            .normal { s with locals := s.locals.upd 2 (.int ⟨64, false⟩ k) } :=
          ExS.set (EvE.cast subb (cast_u64_u64' k (by omega)))
        have hinv' : AcmpLoopInv naz avblk nbz bvblk aLimbs bLimbs n k
            { s with locals := s.locals.upd 2 (.int ⟨64, false⟩ k) } := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · omega
          · omega
          · simpa using hloc0
          · simpa using hloc1
          · simp [Locals.upd]
          · exact hlla
          · exact hllb
          · exact hna
          · exact hnb
          · exact hnaz
          · exact hnbz
          · exact havblk
          · exact hbvblk
          · rw [List.drop_eq_getElem_cons hjlt', List.drop_eq_getElem_cons hjlt2, hlimb, hdrop]
          · exact hnad
          · exact hnad2
          · exact ⟨hav, hbv⟩
        cases ih n hlen hnb { s with locals := s.locals.upd 2 (.int ⟨64, false⟩ k) }
            (by omega) hinv' with
        | inl nor =>
            obtain ⟨sf, hl, hall, hl2, hm, hl0, hl1⟩ := nor
            exact Or.inl ⟨sf, ExS.loop_next hbody (Or.inl rfl) hstep hl, hall, hl2, hm, hl0, hl1⟩
        | inr rest =>
            cases rest with
            | inl r1 =>
                obtain ⟨sf, hl, hj, hdrop', hgt⟩ := r1
                exact Or.inr (Or.inl ⟨sf, ExS.loop_next hbody (Or.inl rfl) hstep hl, hj, hdrop', hgt⟩)
            | inr r2 =>
                obtain ⟨sf, hl, hj, hdrop', hbl⟩ := r2
                exact Or.inr (Or.inr ⟨sf, ExS.loop_next hbody (Or.inl rfl) hstep hl, hj, hdrop', hbl⟩)
      · -- limbs differ: return early
        have hne_dec : decide (aLimbs[k]'hjlt' ≠ bLimbs[k]'hjlt2) = true := by
          rw [decide_eq_true_iff]; exact hlimb
        have hout : EvE LimbGen.prog s (.var 2) (.int ⟨64, false⟩ (k + 1)) := EvE.var hloc2
        have htr : truthy (.int ⟨64, false⟩ (k + 1)) = .ok true := by
          simp [truthy]
        by_cases hgtlimb : aLimbs[k]'hjlt' > bLimbs[k]'hjlt2
        · have hd : decide (aLimbs[k]'hjlt' > bLimbs[k]'hjlt2) = true := by
            rw [decide_eq_true_iff]; exact hgtlimb
          have htrt : truthy (boolVal (decide (aLimbs[k]'hjlt' > bLimbs[k]'hjlt2))) = .ok true := by
            rw [hd]; rfl
          have hret : EvE LimbGen.prog s acmpRetCond (.int ⟨32, true⟩ 1) :=
            EvE.cond hgt htrt (EvE.const _)
          have htn : truthy (boolVal (decide (aLimbs[k]'hjlt' ≠ bLimbs[k]'hjlt2))) = .ok true := by
            rw [hne_dec]; rfl
          refine Or.inr (Or.inl ⟨s, ?_, k, hjlt, hdrop, hgtlimb⟩)
          · exact ExS.loop_ret (ExS.ite hout htr
              (ExS.ite hne htn
                (ExS.ret hret)))
        · have hd : decide (aLimbs[k]'hjlt' > bLimbs[k]'hjlt2) = false := by
            rw [decide_eq_false_iff_not]; exact hgtlimb
          have htrt : truthy (boolVal (decide (aLimbs[k]'hjlt' > bLimbs[k]'hjlt2))) = .ok false := by
            rw [hd]; rfl
          have hbl : bLimbs[k]'hjlt2 > aLimbs[k]'hjlt' := by
            have hle' := Nat.le_of_not_gt hgtlimb
            omega
          have hret : EvE LimbGen.prog s acmpRetCond (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))) :=
            EvE.cond hgt htrt (EvE.un (EvE.const _) (by rfl))
          have htn : truthy (boolVal (decide (aLimbs[k]'hjlt' ≠ bLimbs[k]'hjlt2))) = .ok true := by
            rw [hne_dec]; rfl
          refine Or.inr (Or.inr ⟨s, ?_, k, hjlt, hdrop, hbl⟩)
          · exact ExS.loop_ret (ExS.ite hout htr
              (ExS.ite hne htn
                (ExS.ret hret)))


/-- `acmp` for the unequal-length branch. The whole function is short-circuited
inside the `.ite`; the loop body is unreachable. The returned value is `1` when
`a` has more limbs than `b`, else `-1`. -/
theorem acmp_exs_unequal (naz avblk nbz bvblk : Nat) (m : Mem)
    (aLimbs bLimbs : List Nat) (na nb : Nat)
    (hna : aLimbs.length = na) (hnb : bLimbs.length = nb)
    (hna64 : na < 18446744073709551616) (hnb64 : nb < 18446744073709551616)
    (hne : na ≠ nb)
    (hnaz : m naz = some (ziBlock avblk na 1)) (hnbz : m nbz = some (ziBlock bvblk nb 1))
    (s0 : State) (h0 : s0 = ⟨frameLocals LimbGen.acmp.params [.ptr naz 0, .ptr nbz 0], m, false⟩) :
    (na > nb → ∃ sf, ExS LimbGen.prog s0 LimbGen.acmp.body
        (.ret (some (.int ⟨32, true⟩ 1))) sf ∧
      sf.mem = m ∧ sf.locals 0 = some (.ptr naz 0) ∧ sf.locals 1 = some (.ptr nbz 0))
    ∧
    (na < nb → ∃ sf, ExS LimbGen.prog s0 LimbGen.acmp.body
        (.ret (some (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))))) sf ∧
      sf.mem = m ∧ sf.locals 0 = some (.ptr naz 0) ∧ sf.locals 1 = some (.ptr nbz 0)) := by
  have hmem : s0.mem = m := by rw [h0]
  have l0 : s0.locals 0 = some (.ptr naz 0) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.ptr nbz 0) := by rw [h0]; rfl
  have hnaz' : s0.mem naz = some (ziBlock avblk na 1) := by rw [hmem]; exact hnaz
  have hnbz' : s0.mem nbz = some (ziBlock bvblk nb 1) := by rw [hmem]; exact hnbz
  have hloadA : EvE LimbGen.prog s0 (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
      (.int ⟨64, false⟩ (na % 2 ^ 64)) := by
    have hfield : EvE LimbGen.prog s0 (.field (.var 0) 8) (.ptr naz 8) :=
      EvE.field (EvE.var l0) (by simp [ptrAddN, hnaz', ziBlock_length])
    exact EvE.load hfield (load_u64_at s0.mem naz (ziBlock avblk na 1) 8 na
      hnaz' (by simp [ziBlock_length]) (by simp [ziBlock, encodeLE_length]))
  have hloadB : EvE LimbGen.prog s0 (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
      (.int ⟨64, false⟩ (nb % 2 ^ 64)) := by
    have hfield : EvE LimbGen.prog s0 (.field (.var 1) 8) (.ptr nbz 8) :=
      EvE.field (EvE.var l1) (by simp [ptrAddN, hnbz', ziBlock_length])
    exact EvE.load hfield (load_u64_at s0.mem nbz (ziBlock bvblk nb 1) 8 nb
      hnbz' (by simp [ziBlock_length]) (by simp [ziBlock, encodeLE_length]))
  have hneV : EvE LimbGen.prog s0 acmpNeU64
      (boolVal (decide (na % 2 ^ 64 ≠ nb % 2 ^ 64))) := by
    show EvE LimbGen.prog _ (.bin .ne (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
        (.load (.int ⟨64, false⟩) (.field (.var 1) 8))) (boolVal (decide (na % 2 ^ 64 ≠ nb % 2 ^ 64)))
    exact EvE.bin hloadA hloadB (by rfl)
  have hneTrue : truthy (boolVal (decide (na % 2 ^ 64 ≠ nb % 2 ^ 64))) = .ok true := by
    have hd : decide (na % 2 ^ 64 ≠ nb % 2 ^ 64) = true := by
      rw [decide_eq_true_iff, Nat.mod_eq_of_lt hna64, Nat.mod_eq_of_lt hnb64]; exact hne
    rw [hd]; rfl
  have hgtv : EvE LimbGen.prog s0 acmpGtU64
      (boolVal (decide (na % 2 ^ 64 > nb % 2 ^ 64))) := by
    show EvE LimbGen.prog _ (.bin .gt (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
        (.load (.int ⟨64, false⟩) (.field (.var 1) 8))) (boolVal (decide (na % 2 ^ 64 > nb % 2 ^ 64)))
    exact EvE.bin hloadA hloadB (by rfl)
  constructor
  · intro hgtna
    have htrtu : truthy (boolVal (decide (na % 2 ^ 64 > nb % 2 ^ 64))) = .ok true := by
      have hd : decide (na % 2 ^ 64 > nb % 2 ^ 64) = true := by
        rw [decide_eq_true_iff, Nat.mod_eq_of_lt hna64, Nat.mod_eq_of_lt hnb64]; exact hgtna
      rw [hd]; rfl
    have hretCond : EvE LimbGen.prog s0 acmpRetCondU64 (.int ⟨32, true⟩ 1) :=
      EvE.cond hgtv htrtu (EvE.const _)
    have hif : ExS LimbGen.prog s0
        (.ite (.bin .ne (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
          (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
        (.ret (some (.cond (.bin .gt (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
            (.load (.int ⟨64, false⟩) (.field (.var 1) 8))) (.const (.int ⟨32, true⟩ 1))
          (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))))) .skip)
        (.ret (some (.int ⟨32, true⟩ 1))) s0 :=
      ExS.ite hneV hneTrue (ExS.ret hretCond)
    exact ⟨s0, ExS.seq_ret hif, hmem, l0, l1⟩
  · intro hlt
    have htrtf : truthy (boolVal (decide (na % 2 ^ 64 > nb % 2 ^ 64))) = .ok false := by
      have hd : decide (na % 2 ^ 64 > nb % 2 ^ 64) = false := by
        rw [decide_eq_false_iff_not, Nat.mod_eq_of_lt hna64, Nat.mod_eq_of_lt hnb64]; omega
      rw [hd]; rfl
    have hretCond : EvE LimbGen.prog s0 acmpRetCondU64 (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))) :=
      EvE.cond hgtv htrtf (EvE.un (EvE.const _) (by rfl))
    have hif : ExS LimbGen.prog s0
        (.ite (.bin .ne (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
          (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
        (.ret (some (.cond (.bin .gt (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
            (.load (.int ⟨64, false⟩) (.field (.var 1) 8))) (.const (.int ⟨32, true⟩ 1))
          (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))))) .skip)
        (.ret (some (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))))) s0 :=
      ExS.ite hneV hneTrue (ExS.ret hretCond)
    exact ⟨s0, ExS.seq_ret hif, hmem, l0, l1⟩


/-- Top-level `acmp` refinement for equal-length limb inputs. Zero when all
limbs are equal; `1` on the first mismatching limb with `a > b`; `-1` when
the first mismatch has `a < b`. -/
theorem acmp_exs (naz avblk nbz bvblk : Nat) (m : Mem)
    (aLimbs bLimbs : List Nat) (n : Nat)
    (hna : aLimbs.length = n) (hnb : bLimbs.length = n)
    (hna64 : n < 18446744073709551616)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (hnaz : m naz = some (ziBlock avblk n 1)) (hnbz : m nbz = some (ziBlock bvblk n 1))
    (havblk : m avblk = some (limbBytes aLimbs)) (hbvblk : m bvblk = some (limbBytes bLimbs))
    (hnad : naz < 4294967296) (hnad2 : nbz < 4294967296)
    (hav : avblk < 4294967296) (hbv : bvblk < 4294967296)
    (s0 : State) (h0 : s0 = ⟨frameLocals LimbGen.acmp.params [.ptr naz 0, .ptr nbz 0], m, false⟩) :
    (∃ sf, ExS LimbGen.prog s0 LimbGen.acmp.body (.ret (some (.int ⟨32, true⟩ 0))) sf ∧
        aLimbs = bLimbs ∧ sf.mem = m ∧ sf.locals 0 = some (.ptr naz 0) ∧
        sf.locals 1 = some (.ptr nbz 0))
    ∨ (∃ sf, ExS LimbGen.prog s0 LimbGen.acmp.body (.ret (some (.int ⟨32, true⟩ 1))) sf ∧
        (∃ j, ∃ hj : j < n, aLimbs.drop (j + 1) = bLimbs.drop (j + 1) ∧
              aLimbs[j]'(by omega) > bLimbs[j]'(by omega)))
    ∨ (∃ sf, ExS LimbGen.prog s0 LimbGen.acmp.body
          (.ret (some (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))))) sf ∧
        (∃ j, ∃ hj : j < n, aLimbs.drop (j + 1) = bLimbs.drop (j + 1) ∧
              bLimbs[j]'(by omega) > aLimbs[j]'(by omega))) := by
  have hmem : s0.mem = m := by rw [h0]
  have l0 : s0.locals 0 = some (.ptr naz 0) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.ptr nbz 0) := by rw [h0]; rfl
  have hnaz' : s0.mem naz = some (ziBlock avblk n 1) := by rw [hmem]; exact hnaz
  have hnbz' : s0.mem nbz = some (ziBlock bvblk n 1) := by rw [hmem]; exact hnbz
  have havblk' : s0.mem avblk = some (limbBytes aLimbs) := by rw [hmem]; exact havblk
  have hbvblk' : s0.mem bvblk = some (limbBytes bLimbs) := by rw [hmem]; exact hbvblk
  have hloadA : EvE LimbGen.prog s0 (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
      (.int ⟨64, false⟩ (n % 2 ^ 64)) := by
    have hfield : EvE LimbGen.prog s0 (.field (.var 0) 8) (.ptr naz 8) :=
      EvE.field (EvE.var l0) (by simp [ptrAddN, hnaz', ziBlock_length])
    exact EvE.load hfield (load_u64_at s0.mem naz (ziBlock avblk n 1) 8 n
      hnaz' (by simp [ziBlock_length]) (by simp [ziBlock, encodeLE_length]))
  have hloadB : EvE LimbGen.prog s0 (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
      (.int ⟨64, false⟩ (n % 2 ^ 64)) := by
    have hfield : EvE LimbGen.prog s0 (.field (.var 1) 8) (.ptr nbz 8) :=
      EvE.field (EvE.var l1) (by simp [ptrAddN, hnbz', ziBlock_length])
    exact EvE.load hfield (load_u64_at s0.mem nbz (ziBlock bvblk n 1) 8 n
      hnbz' (by simp [ziBlock_length]) (by simp [ziBlock, encodeLE_length]))
  have hneV : EvE LimbGen.prog s0 acmpNeU64 (boolVal (decide (n % 2 ^ 64 ≠ n % 2 ^ 64))) := by
    show EvE LimbGen.prog _ (.bin .ne (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
        (.load (.int ⟨64, false⟩) (.field (.var 1) 8))) (boolVal (decide (n % 2 ^ 64 ≠ n % 2 ^ 64)))
    have hb : evalBin .ne (some ⟨64, false⟩) (.int ⟨64, false⟩ (n % 2 ^ 64)) (.int ⟨64, false⟩ (n % 2 ^ 64)) = .ok (boolVal (decide (n % 2 ^ 64 ≠ n % 2 ^ 64))) := by
      simp [evalBin, isPtr, evalBinInt, binInt, intOf, u64, IntTy.modulus]
    exact EvE.bin hloadA hloadB hb
  have hdec : decide (n % 2 ^ 64 ≠ n % 2 ^ 64) = false := by simp
  have htrfalse : truthy (boolVal (decide (n % 2 ^ 64 ≠ n % 2 ^ 64))) = .ok false := by
    rw [hdec]; rfl
  have hit : ExS LimbGen.prog s0
      (.ite acmpNeU64 (.ret (some acmpRetCondU64)) .skip) .normal s0 :=
    ExS.ite hneV htrfalse ExS.skip
  have hset2 : ExS LimbGen.prog s0
      (.set 2 (.load (.int ⟨64, false⟩) (.field (.var 0) 8)))
      .normal { s0 with locals := s0.locals.upd 2 (.int ⟨64, false⟩ (n % 2 ^ 64)) } := by
    exact ExS.set hloadA
  have hinv' : AcmpLoopInv naz avblk nbz bvblk aLimbs bLimbs n n
      { s0 with locals := s0.locals.upd 2 (.int ⟨64, false⟩ (n % 2 ^ 64)) } := by
    have hmod : n % 2 ^ 64 = n := Nat.mod_eq_of_lt hna64
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · exact hna64
    · simpa using l0
    · simpa using l1
    · show s0.locals.upd 2 (.int ⟨64, false⟩ (n % 2 ^ 64)) 2 = some (.int ⟨64, false⟩ n)
      simp [Locals.upd, Nat.mod_eq_of_lt hna64]
    · exact hlla
    · exact hllb
    · exact hna
    · exact hnb
    · exact hnaz'
    · exact hnbz'
    · exact havblk'
    · exact hbvblk'
    · simp [List.drop_eq_nil_of_le (by omega : aLimbs.length ≤ n),
        List.drop_eq_nil_of_le (by omega : bLimbs.length ≤ n)]
    · exact hnad
    · exact hnad2
    · exact ⟨hav, hbv⟩
  let s2 : State := { s0 with locals := s0.locals.upd 2 (.int ⟨64, false⟩ (n % 2 ^ 64)) }
  have hinv'' : AcmpLoopInv naz avblk nbz bvblk aLimbs bLimbs n n s2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · simpa [s2] using l0
    · simpa [s2] using l1
    · show s2.locals 2 = some (.int ⟨64, false⟩ n)
      simp [s2, Locals.upd, Nat.mod_eq_of_lt hna64]
    · exact hlla
    · exact hllb
    · exact hna
    · exact hnb
    · exact hnaz'
    · exact hnbz'
    · exact havblk'
    · exact hbvblk'
    · simp [List.drop_eq_nil_of_le (by omega : aLimbs.length ≤ n),
        List.drop_eq_nil_of_le (by omega : bLimbs.length ≤ n)]
    · exact hnad
    · exact hnad2
    · exact ⟨hav, hbv⟩
  -- The outer body of `acmp` = `.seq (.ite ...) (.seq (.seq (.set 2 ...) acmp_loop0) (.ret (some (.const 0))))`
  cases acmp_loop_impl naz avblk nbz bvblk aLimbs bLimbs n hna hnb n s2 (n.le_refl) hinv'' with
  | inl nor =>
      obtain ⟨sf, hl, hall, hl2, hm, hl0, hl1⟩ := nor
      have hC : ExS LimbGen.prog s0
          (.seq (.set 2 (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) LimbGen.acmp_loop0)
          .normal sf :=
        ExS.seq hset2 hl
      have hB : ExS LimbGen.prog s0
          (.seq (.seq (.set 2 (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) LimbGen.acmp_loop0)
            (.ret (some (.const (.int ⟨32, true⟩ 0)))))
          (.ret (some (.int ⟨32, true⟩ 0))) sf :=
        ExS.seq hC (ExS.ret (EvE.const _))
      have hm' : sf.mem = m := by
        have hs : s2.mem = m := hmem
        rw [hs] at hm
        exact hm
      exact Or.inl ⟨sf, ExS.seq hit hB, hall, hm', hl0, hl1⟩
  | inr rest =>
      cases rest with
      | inl r1 =>
          obtain ⟨sf, hl, hj, hjdrop, hgt⟩ := r1
          have hCc : ExS LimbGen.prog s0
              (.seq (.set 2 (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) LimbGen.acmp_loop0)
              (.ret (some (.int ⟨32, true⟩ 1))) sf :=
            ExS.seq hset2 hl
          have hB : ExS LimbGen.prog s0
              (.seq (.seq (.set 2 (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) LimbGen.acmp_loop0)
                (.ret (some (.const (.int ⟨32, true⟩ 0)))))
              (.ret (some (.int ⟨32, true⟩ 1))) sf :=
            ExS.seq_ret hCc
          exact Or.inr (Or.inl ⟨sf, ExS.seq hit hB, hj, hjdrop, hgt⟩)
      | inr r2 =>
          obtain ⟨sf, hl, hj, hjdrop, hbl⟩ := r2
          have hCc : ExS LimbGen.prog s0
              (.seq (.set 2 (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) LimbGen.acmp_loop0)
              (.ret (some (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))))) sf :=
            ExS.seq hset2 hl
          have hB : ExS LimbGen.prog s0
              (.seq (.seq (.set 2 (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) LimbGen.acmp_loop0)
                (.ret (some (.const (.int ⟨32, true⟩ 0)))))
              (.ret (some (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))))) sf :=
            ExS.seq_ret hCc
          exact Or.inr (Or.inr ⟨sf, ExS.seq hit hB, hj, hjdrop, hbl⟩)

end Tess.C

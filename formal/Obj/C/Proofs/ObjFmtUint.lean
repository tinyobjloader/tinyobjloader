/-
  Refinement proof for the translated `tobj_fmt_uint` (tobj_write_core.inc), the
  allocation-free decimal formatter used by the `.obj` writer `tobj_write.c`.
  `fmt_uint_exs`: when the digits fit, the function returns the digit count and
  writes exactly the bytes `decBytes v` = the pure `Obj.decDigits v`;
  `fmt_uint_fail`: a too-small capacity returns 0 and leaves memory unchanged;
  `fmt_uint_scanInt` closes the loop with the loader: the written bytes scan
  back to the same number.
-/
import Obj.C.Proofs.ObjEmitFace
import Obj.Write
namespace Obj.C.Proofs
open Obj.C Obj

theorem decDigits_lt10 (t : Nat) (h : t < 10) : decDigits t = [48 + t] := by
  rw [decDigits]; simp [h]

theorem decDigits_ge10 (t : Nat) (h : 10 ≤ t) : decDigits t = decDigits (t / 10) ++ [48 + t % 10] := by
  rw [decDigits]; simp; omega

theorem decDigits_len_ge10 (t : Nat) (h : 10 ≤ t) :
    (decDigits t).length = (decDigits (t / 10)).length + 1 := by
  rw [decDigits_ge10 t h]; simp

theorem u64_ge_val (a n : Nat) :
    evalBin .ge (some ⟨64, false⟩) (.int u64 a) (.int u64 n) = .ok (boolVal (decide (a ≥ n))) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u64, IntTy.modulus, Res.bind]

theorem u64_div_val (a n : Nat) (hn : 0 < n) (ha : a < 18446744073709551616)
    (hn' : n < 18446744073709551616) :
    evalBin .div (some ⟨64, false⟩) (.int u64 a) (.int u64 n) = .ok (.int u64 (a / n)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u64, IntTy.modulus, Res.bind]
  omega


theorem u64_mod_val (a n : Nat) (hn : 0 < n) :
    evalBin .mod (some ⟨64, false⟩) (.int u64 a) (.int u64 n) = .ok (.int u64 (a % n)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u64, IntTy.modulus, Res.bind]
  omega

theorem cast_u64_u32_const10 : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 10) = .ok (.int u64 10) :=
  cast_u64_u32 10 (by omega)

def ft0Body : Stmt :=
  (.ite (.bin .ge (some ⟨64, false⟩) (.var 4) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10))))
    (.seq (.set 4 (.bin .div (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10)))))
      (.set 3 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
        (.const (.int ⟨64, false⟩ 1)))))) .brk)

theorem ft0_ast : Gen.tobj_fmt_uint_loop0 = .loop ft0Body .skip := rfl

/-- Digit-counting loop: `n + j = L` where `j + 1` is the digit count of `t`. -/
def Ft0Inv (L : Nat) (s0 : State) (j : Nat) (s : State) : Prop :=
  s.locals 0 = s0.locals 0 ∧ s.locals 1 = s0.locals 1 ∧ s.locals 2 = s0.locals 2 ∧
  (∃ n t : Nat, s.locals 3 = some (.int u64 n) ∧ s.locals 4 = some (.int u64 t) ∧
    t < 18446744073709551616 ∧ (decDigits t).length = j + 1 ∧ n + j = L) ∧
  s.mem = s0.mem ∧ s.ro = s0.ro

theorem decDigits_len_pos (t : Nat) : 1 ≤ (decDigits t).length := by
  by_cases h : t < 10
  · rw [decDigits_lt10 t h]; simp
  · rw [decDigits_len_ge10 t (by omega)]; omega

theorem decDigits_len_one (t : Nat) (h : (decDigits t).length = 1) : t < 10 := by
  by_cases h' : t < 10
  · exact h'
  · rw [decDigits_len_ge10 t (by omega)] at h
    have := decDigits_len_pos (t / 10)
    omega

theorem decDigits_len_ge2 (t : Nat) (h : 2 ≤ (decDigits t).length) : 10 ≤ t := by
  by_cases h' : t < 10
  · rw [decDigits_lt10 t h'] at h; simp at h
  · omega

theorem ft0_loop (L : Nat) (hL : L < 18446744073709551616) (s0 s1 : State)
    (hinv : Ft0Inv L s0 (L - 1) s1) :
    ∃ sf, ExS Gen.prog s1 (.loop ft0Body .skip) .normal sf ∧ Ft0Inv L s0 0 sf := by
  have hstep : ∀ j s, Ft0Inv L s0 (j + 1) s → ∃ s1 s2, ExS Gen.prog s ft0Body .normal s1 ∧
      ExS Gen.prog s1 .skip .normal s2 ∧ Ft0Inv L s0 j s2 := by
    intro j s ⟨h0, h1, h2, ⟨n, t, l3, l4, ht, hlen, hn⟩, hmem, hro⟩
    have h10 : 10 ≤ t := decDigits_len_ge2 t (by omega)
    have hv4 : EvE Gen.prog s (.var 4) (.int u64 t) := EvE.var l4
    have hc10 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10))) (.int u64 10) :=
      EvE.cast (EvE.const _) cast_u64_u32_const10
    have hge : EvE Gen.prog s (.bin .ge (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10)))) (boolVal (decide (t ≥ 10))) :=
      EvE.bin hv4 hc10 (u64_ge_val _ _)
    have hdiv : EvE Gen.prog s (.bin .div (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10)))) (.int u64 (t / 10)) :=
      EvE.bin hv4 hc10 (u64_div_val _ _ (by omega) ht (by omega))
    have hset4 := ExS.set (p := Gen.prog) (i := 4) hdiv
    let sa : State := { s with locals := s.locals.upd 4 (.int u64 (t / 10)) }
    have l3a : sa.locals 3 = some (.int u64 n) := by simpa [sa, Locals.upd] using l3
    have hv3 : EvE Gen.prog sa (.var 3) (.int u64 n) := EvE.var l3a
    have hn64 : n < 18446744073709551615 := by omega
    have hcn : EvE Gen.prog sa (.cast ⟨64, false⟩ (.var 3)) (.int u64 n) :=
      EvE.cast hv3 (cast_u64_u64 _ (by omega))
    have hadd : EvE Gen.prog sa (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
        (.const (.int ⟨64, false⟩ 1))) (.int u64 (n + 1)) :=
      EvE.bin hcn (EvE.const _) (u64_add_val _ _ (by omega))
    have hset3 := ExS.set (p := Gen.prog) (i := 3)
      (EvE.cast hadd (cast_u64_u64 _ (by omega)))
    let sb : State := { sa with locals := sa.locals.upd 3 (.int u64 (n + 1)) }
    have hbody : ExS Gen.prog s ft0Body .normal sb := by
      unfold ft0Body
      exact ExS.ite hge (bc := true) (by simp [truthy, boolVal, h10])
        (by simpa using ExS.seq hset4 hset3)
    refine ⟨sb, sb, hbody, ExS.skip, ?_⟩
    refine ⟨?_, ?_, ?_, ⟨n + 1, t / 10, ?_, ?_, by omega, ?_, by omega⟩, hmem, hro⟩
    · simpa [sb, sa, Locals.upd] using h0
    · simpa [sb, sa, Locals.upd] using h1
    · simpa [sb, sa, Locals.upd] using h2
    · simp [sb, sa, Locals.upd]
    · simp [sb, sa, Locals.upd]
    · have := decDigits_len_ge10 t h10; omega
  have hexit : ∀ s, Ft0Inv L s0 0 s → ∃ s1, ExS Gen.prog s ft0Body .brk s1 ∧ Ft0Inv L s0 0 s1 := by
    intro s hs
    obtain ⟨h0, h1, h2, ⟨n, t, l3, l4, ht, hlen, hn⟩, hmem, hro⟩ := hs
    have hlt : t < 10 := decDigits_len_one t (by omega)
    have hv4 : EvE Gen.prog s (.var 4) (.int u64 t) := EvE.var l4
    have hc10 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10))) (.int u64 10) :=
      EvE.cast (EvE.const _) cast_u64_u32_const10
    have hge : EvE Gen.prog s (.bin .ge (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10)))) (boolVal (decide (t ≥ 10))) :=
      EvE.bin hv4 hc10 (u64_ge_val _ _)
    refine ⟨s, ?_, ⟨h0, h1, h2, ⟨n, t, l3, l4, ht, hlen, hn⟩, hmem, hro⟩⟩
    unfold ft0Body
    apply ExS.ite hge (bc := false) (by simp [truthy, boolVal]; omega)
    simpa using (ExS.brk (p := Gen.prog) (s := s))
  obtain ⟨sf, hl, hq⟩ := ExS.loop_decreasing_post (p := Gen.prog)
    (P := Ft0Inv L s0) (Q := Ft0Inv L s0 0) (n := L - 1) (s := s1) hinv hstep
    (fun s hs => by obtain ⟨s', hb, hq⟩ := hexit s hs; exact ⟨s', hb, hq⟩)
  exact ⟨sf, hl, hq⟩


theorem u64_sub_val (a c : Nat) (h : c ≤ a) :
    evalBin .sub (some ⟨64, false⟩) (.int u64 a) (.int u64 c) = .ok (.int u64 (a - c)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u64, IntTy.modulus, Res.bind, h]

theorem digit_value_eval (t : Nat) :
    evalCast ⟨8, false⟩ (.int ⟨32, false⟩ (48 + t % 10)) = .ok (.int ⟨8, false⟩ (48 + t % 10)) := by
  simp [evalCast, IntTy.modulus]; omega

theorem add48_val (r : Nat) (hr : r < 10) :
    evalBin .add (some ⟨32, false⟩) (.int ⟨32, false⟩ 48) (.int u32 r) =
      .ok (.int ⟨32, false⟩ (48 + r)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.modulus, Res.bind]
  omega

theorem cast_u32_u64_small (r : Nat) (hr : r < 10) :
    evalCast ⟨32, false⟩ (.int u64 r) = .ok (.int u32 r) := by
  simp [evalCast, u64, u32, IntTy.modulus]; omega

theorem splice_single (P S Q : Block) (p x : UInt8) :
    splice ((P ++ [p]) ++ S ++ Q) P.length [x] = (P ++ [x]) ++ S ++ Q := by
  simp [splice, List.take_append]

def ft1Body : Stmt :=
  (.ite (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
    (.seq (.set 5 (.cast ⟨64, false⟩ (.bin .sub (some ⟨64, false⟩)
        (.cast ⟨64, false⟩ (.var 5)) (.const (.int ⟨64, false⟩ 1)))))
      (.seq (.store (.int ⟨8, false⟩) (.index (.var 0) (.var 5) 1)
          (.cast ⟨8, false⟩ (.bin .add (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 48))
            (.cast ⟨32, false⟩ (.bin .mod (some ⟨64, false⟩) (.var 4)
              (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10))))))))
        (.set 4 (.bin .div (some ⟨64, false⟩) (.var 4)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10))))))) .brk)

theorem ft1_ast : Gen.tobj_fmt_uint_loop1 = .loop ft1Body .skip := rfl


theorem fmt_digit_step (D : List Nat) (t i : Nat) (hi : 0 < i) (hle : i ≤ D.length)
    (hk : D.take i = decDigits t) :
    D[i - 1]? = some (48 + t % 10) ∧
      ((i = 1 ∧ t / 10 = 0) ∨ (2 ≤ i ∧ D.take (i - 1) = decDigits (t / 10))) := by
  have hlen : (D.take i).length = i := by simp; omega
  have hget : D[i - 1]? = (D.take i)[i - 1]? := by
    rw [List.getElem?_take_of_lt (by omega)]
  by_cases h10 : t < 10
  · rw [decDigits_lt10 t h10] at hk
    rw [hk] at hlen
    simp at hlen
    subst hlen
    refine ⟨?_, Or.inl ⟨rfl, by omega⟩⟩
    rw [hget, hk]; simp; omega
  · have hge : 10 ≤ t := by omega
    rw [decDigits_ge10 t hge] at hk
    have hl1 := decDigits_len_pos (t / 10)
    have hlen' : (decDigits (t / 10) ++ [48 + t % 10]).length = i := by rw [← hk]; exact hlen
    simp only [List.length_append, List.length_singleton] at hlen'
    refine ⟨?_, Or.inr ⟨by omega, ?_⟩⟩
    · rw [hget, hk]
      have : i - 1 = (decDigits (t / 10)).length := by omega
      rw [this]; simp
    · have : (D.take i).take (i - 1) = D.take (i - 1) := by
        rw [List.take_take]; congr 1; omega
      rw [← this, hk]
      have : i - 1 = (decDigits (t / 10)).length := by omega
      rw [this]; simp


/-- Bytes of the decimal rendering. -/
def decBytes (v : Nat) : Block := (decDigits v).map Nat.toUInt8

def Ft1Inv (m : Mem) (bb boff : Nat) (blk : Block) (D : List Nat) (i : Nat) (s : State) : Prop :=
  i ≤ D.length ∧ s.locals 0 = some (.ptr bb boff) ∧ s.locals 3 = some (.int u64 D.length) ∧
  (∃ t, s.locals 4 = some (.int u64 t) ∧ t < 18446744073709551616 ∧
    ((i = 0 ∧ t = 0) ∨ (0 < i ∧ D.take i = decDigits t))) ∧
  s.locals 5 = some (.int u64 i) ∧ s.ro = false ∧
  s.mem bb = some (blk.take (boff + i) ++ (D.drop i).map Nat.toUInt8 ++
    blk.drop (boff + D.length)) ∧ ∀ b, b ≠ bb → s.mem b = m b

theorem ft1_loop (m : Mem) (bb boff : Nat) (blk : Block) (D : List Nat)
    (hlen : boff + D.length ≤ blk.length)
    (hbig : D.length < 18446744073709551616) (s1 : State)
    (hinv : Ft1Inv m bb boff blk D D.length s1) :
    ∃ sf, ExS Gen.prog s1 (.loop ft1Body .skip) .normal sf ∧ Ft1Inv m bb boff blk D 0 sf := by
  have hstep : ∀ j s, Ft1Inv m bb boff blk D (j + 1) s → ∃ s1 s2,
      ExS Gen.prog s ft1Body .normal s1 ∧ ExS Gen.prog s1 .skip .normal s2 ∧
      Ft1Inv m bb boff blk D j s2 := by
    intro j s ⟨hj, l0, l3, ⟨t, l4, ht, hcase⟩, l5, hro, hmem, hrest⟩
    have hcase' : D.take (j + 1) = decDigits t := by
      rcases hcase with ⟨h, _⟩ | ⟨_, h⟩
      · omega
      · exact h
    obtain ⟨hDj, hnext⟩ := fmt_digit_step D t (j + 1) (by omega) hj hcase'
    have hv5 : EvE Gen.prog s (.var 5) (.int u64 (j + 1)) := EvE.var l5
    have hc0 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int u64 0) :=
      EvE.cast (EvE.const _) (cast_u64_u32 0 (by omega))
    have hgt : EvE Gen.prog s (.bin .gt (some ⟨64, false⟩) (.var 5)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) (boolVal (decide (j + 1 > 0))) :=
      EvE.bin hv5 hc0 (u64_gt_val _ _)
    have hci : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 5)) (.int u64 (j + 1)) :=
      EvE.cast hv5 (cast_u64_u64 _ (by omega))
    have hsub : EvE Gen.prog s (.bin .sub (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 5))
        (.const (.int ⟨64, false⟩ 1))) (.int u64 j) := by
      have := EvE.bin hci (EvE.const (.int ⟨64, false⟩ 1)) (u64_sub_val (j + 1) 1 (by omega))
      simpa using this
    have hset5 := ExS.set (p := Gen.prog) (i := 5)
      (EvE.cast hsub (cast_u64_u64 _ (by omega)))
    let sa : State := { s with locals := s.locals.upd 5 (.int u64 j) }
    have la0 : sa.locals 0 = some (.ptr bb boff) := by simpa [sa, Locals.upd] using l0
    have la4 : sa.locals 4 = some (.int u64 t) := by simpa [sa, Locals.upd] using l4
    have la5 : sa.locals 5 = some (.int u64 j) := by simp [sa, Locals.upd]
    have hv0 : EvE Gen.prog sa (.var 0) (.ptr bb boff) := EvE.var la0
    have hv5a : EvE Gen.prog sa (.var 5) (.int u64 j) := EvE.var la5
    have hv4 : EvE Gen.prog sa (.var 4) (.int u64 t) := EvE.var la4
    have hc10 : EvE Gen.prog sa (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10))) (.int u64 10) :=
      EvE.cast (EvE.const _) cast_u64_u32_const10
    have hmod : EvE Gen.prog sa (.bin .mod (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10)))) (.int u64 (t % 10)) :=
      EvE.bin hv4 hc10 (u64_mod_val _ _ (by omega))
    have hmod32 : EvE Gen.prog sa (.cast ⟨32, false⟩ (.bin .mod (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10))))) (.int u32 (t % 10)) :=
      EvE.cast hmod (cast_u32_u64_small _ (by omega))
    have hsum : EvE Gen.prog sa (.bin .add (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 48))
        (.cast ⟨32, false⟩ (.bin .mod (some ⟨64, false⟩) (.var 4)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10)))))) (.int ⟨32, false⟩ (48 + t % 10)) :=
      EvE.bin (EvE.const _) hmod32 (add48_val _ (by omega))
    have hval : EvE Gen.prog sa (.cast ⟨8, false⟩ (.bin .add (some ⟨32, false⟩)
        (.const (.int ⟨32, false⟩ 48)) (.cast ⟨32, false⟩ (.bin .mod (some ⟨64, false⟩) (.var 4)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10))))))) (.int ⟨8, false⟩ (48 + t % 10)) :=
      EvE.cast hsum (digit_value_eval t)
    have hmema : sa.mem bb = some (blk.take (boff + (j + 1)) ++ (D.drop (j + 1)).map Nat.toUInt8 ++
        blk.drop (boff + D.length)) := hmem
    have hbl : (blk.take (boff + (j + 1)) ++ (D.drop (j + 1)).map Nat.toUInt8 ++
        blk.drop (boff + D.length)).length = blk.length := by
      simp; omega
    have haddr : EvE Gen.prog sa (.index (.var 0) (.var 5) 1) (.ptr bb (boff + j)) := by
      apply EvE.index hv0 hv5a
      simp [u64, ptrAddN, hmema, hbl]
      omega
    have hst := store_int sa.mem bb (boff + j) _ hmema ⟨8, false⟩ (48 + t % 10)
      (by simp [IntTy.bytes, hbl]; omega)
    let M2 := sa.mem.upd bb (splice (blk.take (boff + (j + 1)) ++ (D.drop (j + 1)).map Nat.toUInt8 ++
        blk.drop (boff + D.length)) (boff + j) (encodeLE 1 (48 + t % 10)))
    let sb : State := { sa with mem := M2 }
    have hm2 : store sa.mem (.int ⟨8, false⟩) (.ptr bb (boff + j)) (.int ⟨8, false⟩ (48 + t % 10))
        = .ok M2 := by simpa [M2, IntTy.bytes] using hst
    have hstore : ExS Gen.prog sa (.store (.int ⟨8, false⟩) (.index (.var 0) (.var 5) 1)
        (.cast ⟨8, false⟩ (.bin .add (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 48))
          (.cast ⟨32, false⟩ (.bin .mod (some ⟨64, false⟩) (.var 4)
            (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10)))))))) .normal sb :=
      ExS.store haddr hval hro hm2
    have lb4 : sb.locals 4 = some (.int u64 t) := la4
    have hv4b : EvE Gen.prog sb (.var 4) (.int u64 t) := EvE.var lb4
    have hdiv : EvE Gen.prog sb (.bin .div (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 10)))) (.int u64 (t / 10)) :=
      EvE.bin hv4b (EvE.cast (EvE.const _) cast_u64_u32_const10)
        (u64_div_val _ _ (by omega) ht (by omega))
    have hset4 := ExS.set (p := Gen.prog) (i := 4) hdiv
    have hbody : ExS Gen.prog s ft1Body .normal
        { sb with locals := sb.locals.upd 4 (.int u64 (t / 10)) } := by
      unfold ft1Body
      exact ExS.ite hgt (bc := true) (by simp [truthy, boolVal])
        (by simpa using ExS.seq hset5 (ExS.seq hstore hset4))
    refine ⟨_, _, hbody, ExS.skip, ?_⟩
    have hjD : j < D.length := by omega
    have hDj' : D[j] = 48 + t % 10 := by
      have := hDj
      simp only [Nat.add_sub_cancel] at this
      rw [List.getElem?_eq_getElem hjD] at this
      simpa using this
    refine ⟨by omega, ?_, ?_, ⟨t / 10, ?_, by omega, ?_⟩, ?_, hro, ?_, ?_⟩
    · simpa [sb, sa, Locals.upd] using l0
    · simpa [sb, sa, Locals.upd] using l3
    · simp [sb, sa, Locals.upd]
    · rcases hnext with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by omega, h2⟩
      · right; exact ⟨by omega, by simpa using h2⟩
    · simp [sb, sa, Locals.upd]
    · show M2 bb = _
      simp only [M2, Mem.upd_same]
      have htk : blk.take (boff + (j + 1)) = blk.take (boff + j) ++ [blk[boff + j]'(by omega)] := by
        have e : boff + (j + 1) = (boff + j) + 1 := rfl
        rw [e, List.take_succ, List.getElem?_eq_getElem (by omega)]; rfl
      have hP : (blk.take (boff + j)).length = boff + j := by simp; omega
      have hdr : D.drop j = D[j] :: D.drop (j + 1) := List.drop_eq_getElem_cons hjD
      have := splice_single (blk.take (boff + j)) ((D.drop (j + 1)).map Nat.toUInt8)
        (blk.drop (boff + D.length)) (blk[boff + j]'(by omega)) (Nat.toUInt8 (48 + t % 10))
      rw [hP] at this
      have hx : encodeLE 1 (48 + t % 10) = [Nat.toUInt8 (48 + t % 10)] := by
        have : (48 + t % 10) % 256 = 48 + t % 10 := by omega
        simp [encodeLE, this]
      rw [htk, hx, this, hdr, hDj']
      simp
    · intro b hb
      show (sa.mem.upd bb _) b = _
      rw [Mem.upd_ne _ _ hb]
      exact hrest b hb
  have hexit : ∀ s, Ft1Inv m bb boff blk D 0 s →
      ∃ s1, ExS Gen.prog s ft1Body .brk s1 ∧ Ft1Inv m bb boff blk D 0 s1 := by
    intro s hs
    obtain ⟨hj, l0, l3, ⟨t, l4, ht, hc⟩, l5, hro, hmem, hrest⟩ := hs
    have hv5 : EvE Gen.prog s (.var 5) (.int u64 0) := EvE.var l5
    have hc0 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int u64 0) :=
      EvE.cast (EvE.const _) (cast_u64_u32 0 (by omega))
    have hgt : EvE Gen.prog s (.bin .gt (some ⟨64, false⟩) (.var 5)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) (boolVal (decide (0 > 0))) :=
      EvE.bin hv5 hc0 (u64_gt_val _ _)
    refine ⟨s, ?_, ⟨hj, l0, l3, ⟨t, l4, ht, hc⟩, l5, hro, hmem, hrest⟩⟩
    unfold ft1Body
    apply ExS.ite hgt (bc := false) (by simp [truthy, boolVal])
    simpa using (ExS.brk (p := Gen.prog) (s := s))
  obtain ⟨sf, hl, hq⟩ := ExS.loop_decreasing_post (p := Gen.prog)
    (P := Ft1Inv m bb boff blk D) (Q := Ft1Inv m bb boff blk D 0) (n := D.length) (s := s1)
    hinv hstep (fun s hs => by obtain ⟨s', hb, hq⟩ := hexit s hs; exact ⟨s', hb, hq⟩)
  exact ⟨sf, hl, hq⟩


/-- State after `n = 1; t = v` (shared by the success and failure theorems). -/
theorem fmt_uint_prefix (m : Mem) (bb boff cap v : Nat) :
    ∃ sa s0 : State, s0.mem = m ∧ s0.ro = false ∧ s0.locals 0 = some (.ptr bb boff) ∧
      s0.locals 1 = some (.int u64 cap) ∧ s0.locals 2 = some (.int u64 v) ∧
      s0.locals 3 = some (.int u64 1) ∧ s0.locals 4 = some (.int u64 v) ∧
      ExS Gen.prog ⟨frameLocals Gen.tobj_fmt_uint.params
        [.ptr bb boff, .int u64 cap, .int u64 v], m, false⟩
        (.set 3 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) .normal sa ∧
      ExS Gen.prog sa (.set 4 (.var 2)) .normal s0 := by
  let sz : State := ⟨frameLocals Gen.tobj_fmt_uint.params
        [.ptr bb boff, .int u64 cap, .int u64 v], m, false⟩
  have l0 : sz.locals 0 = some (.ptr bb boff) := by
    simp [sz, frameLocals, Gen.tobj_fmt_uint, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : sz.locals 1 = some (.int u64 cap) := by
    simp [sz, frameLocals, Gen.tobj_fmt_uint, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : sz.locals 2 = some (.int u64 v) := by
    simp [sz, frameLocals, Gen.tobj_fmt_uint, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have c1 : evalCast ⟨64, false⟩ (.int ⟨32, true⟩ 1) = .ok (.int u64 1) := by
    simp [evalCast, u64, IntTy.toInt, IntTy.wrap, IntTy.modulus]
  have h3 := ExS.set (p := Gen.prog) (s := sz) (i := 3) (EvE.cast (EvE.const _) c1)
  let sa : State := { sz with locals := sz.locals.upd 3 (.int u64 1) }
  have l2a : sa.locals 2 = some (.int u64 v) := by simpa [sa, Locals.upd] using l2
  have h4 := ExS.set (p := Gen.prog) (s := sa) (i := 4) (EvE.var l2a)
  let sb : State := { sa with locals := sa.locals.upd 4 (.int u64 v) }
  refine ⟨sa, sb, rfl, rfl, ?_, ?_, ?_, ?_, ?_, h3, h4⟩
  · simpa [sb, sa, Locals.upd] using l0
  · simpa [sb, sa, Locals.upd] using l1
  · simpa [sb, sa, Locals.upd] using l2
  · simp [sb, sa, Locals.upd]
  · simp [sb, sa, Locals.upd]


theorem fmt_uint_fail (m : Mem) (bb boff cap v : Nat) (hv : v < 18446744073709551616)
    (hcap : cap < (decDigits v).length) (hcap64 : cap < 18446744073709551616)
    (hbig : (decDigits v).length < 18446744073709551616) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tobj_fmt_uint.params
        [.ptr bb boff, .int u64 cap, .int u64 v], m, false⟩ Gen.tobj_fmt_uint.body
        (.ret (some (.int u64 0))) s' ∧ s'.mem = m := by
  obtain ⟨sa, s0, hm0, hro0, l0, l1, l2, l3, l4, h3, h4⟩ := fmt_uint_prefix m bb boff cap v
  have hLpos := decDigits_len_pos v
  have hinv0 : Ft0Inv (decDigits v).length s0 ((decDigits v).length - 1) s0 :=
    ⟨rfl, rfl, rfl, ⟨1, v, l3, l4, hv, by omega, by omega⟩, rfl, rfl⟩
  obtain ⟨sf, hl0, hq⟩ := ft0_loop _ hbig s0 s0 hinv0
  obtain ⟨h0', h1', h2', ⟨n, t, l3', l4', _, hlen, hn⟩, hmem, hro⟩ := hq
  have hnL : n = (decDigits v).length := by omega
  subst hnL
  have hv3 : EvE Gen.prog sf (.var 3) (.int u64 (decDigits v).length) := EvE.var l3'
  have hv1 : EvE Gen.prog sf (.var 1) (.int u64 cap) := EvE.var (by rw [h1']; exact l1)
  have hgt : EvE Gen.prog sf (.bin .gt (some ⟨64, false⟩) (.var 3) (.var 1))
      (boolVal (decide ((decDigits v).length > cap))) := EvE.bin hv3 hv1 (u64_gt_val _ _)
  have hz : evalCast ⟨64, false⟩ (.int ⟨32, true⟩ 0) = .ok (.int u64 0) := by
    simp [evalCast, u64, IntTy.toInt, IntTy.wrap, IntTy.modulus]
  have hret : EvE Gen.prog sf (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))) (.int u64 0) :=
    EvE.cast (EvE.const _) hz
  have hite : ExS Gen.prog sf (.ite (.bin .gt (some ⟨64, false⟩) (.var 3) (.var 1))
      (.ret (some (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))) .skip)
      (.ret (some (.int u64 0))) sf :=
    ExS.ite hgt (bc := true) (by simp [truthy, boolVal]; omega) (ExS.ret hret)
  refine ⟨sf, ?_, by rw [hmem, hm0]⟩
  have hbody : Gen.tobj_fmt_uint.body = .seq (.set 3 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1))))
      (.seq (.set 4 (.var 2)) (.seq (.loop ft0Body .skip) (.seq (.ite (.bin .gt (some ⟨64, false⟩)
        (.var 3) (.var 1)) (.ret (some (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))) .skip)
        (.seq (.set 5 (.var 3)) (.seq (.set 4 (.var 2)) (.seq (.loop ft1Body .skip)
          (.ret (some (.var 3))))))))) := rfl
  rw [hbody]
  exact ExS.seq h3 (ExS.seq h4 (ExS.seq hl0 (ExS.seq_ret hite)))


/-- **`tobj_fmt_uint` refines `Obj.decDigits`.**  When the digits fit in `cap`
    bytes and in the buffer, the translated function returns the digit count,
    writes exactly `decBytes v` at `boff`, and touches nothing else. -/
theorem fmt_uint_exs (m : Mem) (bb boff cap v : Nat) (blk : Block) (hbb : m bb = some blk)
    (hv : v < 18446744073709551616)
    (hlen : boff + (decDigits v).length ≤ blk.length) (hcap : (decDigits v).length ≤ cap)
    (hcap64 : cap < 18446744073709551616)
    (hbig : (decDigits v).length < 18446744073709551616) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tobj_fmt_uint.params
        [.ptr bb boff, .int u64 cap, .int u64 v], m, false⟩ Gen.tobj_fmt_uint.body
        (.ret (some (.int u64 (decDigits v).length))) s' ∧
      s'.mem bb = some (blk.take boff ++ decBytes v ++ blk.drop (boff + (decDigits v).length)) ∧
      ∀ b, b ≠ bb → s'.mem b = m b := by
  obtain ⟨sa, s0, hm0, hro0, l0, l1, l2, l3, l4, h3, h4⟩ := fmt_uint_prefix m bb boff cap v
  have hLpos := decDigits_len_pos v
  have hinv0 : Ft0Inv (decDigits v).length s0 ((decDigits v).length - 1) s0 :=
    ⟨rfl, rfl, rfl, ⟨1, v, l3, l4, hv, by omega, by omega⟩, rfl, rfl⟩
  obtain ⟨sf, hl0, hq⟩ := ft0_loop _ hbig s0 s0 hinv0
  obtain ⟨h0', h1', h2', ⟨n, t, l3', l4', _, hlen', hn⟩, hmem, hro⟩ := hq
  have hnL : n = (decDigits v).length := by omega
  subst hnL
  have hv3 : EvE Gen.prog sf (.var 3) (.int u64 (decDigits v).length) := EvE.var l3'
  have hv1 : EvE Gen.prog sf (.var 1) (.int u64 cap) := EvE.var (by rw [h1']; exact l1)
  have hgt : EvE Gen.prog sf (.bin .gt (some ⟨64, false⟩) (.var 3) (.var 1))
      (boolVal (decide ((decDigits v).length > cap))) := EvE.bin hv3 hv1 (u64_gt_val _ _)
  have hite : ExS Gen.prog sf (.ite (.bin .gt (some ⟨64, false⟩) (.var 3) (.var 1))
      (.ret (some (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))) .skip) .normal sf :=
    ExS.ite hgt (bc := false) (by simp [truthy, boolVal]; omega)
      (by simpa using (ExS.skip (p := Gen.prog) (s := sf)))
  have hset5 := ExS.set (p := Gen.prog) (s := sf) (i := 5) hv3
  let sc : State := { sf with locals := sf.locals.upd 5 (.int u64 (decDigits v).length) }
  have l2c : sc.locals 2 = some (.int u64 v) := by
    simpa [sc, Locals.upd] using (by rw [h2']; exact l2 : sf.locals 2 = some (.int u64 v))
  have hset4 := ExS.set (p := Gen.prog) (s := sc) (i := 4) (EvE.var l2c)
  let sd : State := { sc with locals := sc.locals.upd 4 (.int u64 v) }
  have hmemd : sd.mem = m := by simp [sd, sc, hmem, hm0]
  have hinv1 : Ft1Inv m bb boff blk (decDigits v) (decDigits v).length sd := by
    refine ⟨Nat.le_refl _, ?_, ?_, ⟨v, ?_, hv, Or.inr ⟨by omega, by simp⟩⟩, ?_, ?_, ?_, ?_⟩
    · simpa [sd, sc, Locals.upd] using (by rw [h0']; exact l0 : sf.locals 0 = some (.ptr bb boff))
    · simpa [sd, sc, Locals.upd] using l3'
    · simp [sd, sc, Locals.upd]
    · simp [sd, sc, Locals.upd]
    · simpa [sd, sc] using (by rw [hro]; exact hro0 : sf.ro = false)
    · rw [hmemd, hbb]
      simp
    · intro b _; rw [hmemd]
  obtain ⟨sg, hl1, hq1⟩ := ft1_loop m bb boff blk (decDigits v) hlen hbig sd hinv1
  obtain ⟨_, _, hl3g, _, _, _, hmemg, hrestg⟩ := hq1
  have hv3g : EvE Gen.prog sg (.var 3) (.int u64 (decDigits v).length) := EvE.var hl3g
  refine ⟨sg, ?_, ?_, hrestg⟩
  · have hbody : Gen.tobj_fmt_uint.body = .seq (.set 3 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1))))
        (.seq (.set 4 (.var 2)) (.seq (.loop ft0Body .skip) (.seq (.ite (.bin .gt (some ⟨64, false⟩)
          (.var 3) (.var 1)) (.ret (some (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))) .skip)
          (.seq (.set 5 (.var 3)) (.seq (.set 4 (.var 2)) (.seq (.loop ft1Body .skip)
            (.ret (some (.var 3))))))))) := rfl
    rw [hbody]
    exact ExS.seq h3 (ExS.seq h4 (ExS.seq hl0 (ExS.seq hite (ExS.seq hset5 (ExS.seq hset4
      (ExS.seq hl1 (ExS.ret hv3g)))))))
  · rw [hmemg]; simp [decBytes]


/-- The bytes written by `tobj_fmt_uint` read back, through the pure scanner
    model, as the formatted number (`Obj.scanInt_decDigits`). -/
theorem decBytes_toNat (v : Nat) : (decBytes v).map UInt8.toNat = decDigits v := by
  unfold decBytes
  rw [List.map_map]
  rw [List.map_congr_left (g := id) (fun d hd => by
    have := decDigits_all v d hd
    simp [Function.comp, Nat.toUInt8]
    omega)]
  exact List.map_id _

theorem fmt_uint_scanInt (v : Nat) (hv : v ≤ 2147483647) :
    scanInt ((decBytes v).map UInt8.toNat) 0 =
      (true, (v : Int), (decDigits v).length) := by
  rw [decBytes_toNat]
  have := scanInt_decDigits [] [] v hv trivial (by intro b hb; simp at hb)
  simpa using this

end Obj.C.Proofs

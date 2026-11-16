/-
  MiniC refinement of the translated `trim_len` (`lib/tess/src/exact.c`, used by `norm`): it returns the
  number of limbs left after dropping most-significant zero limbs, i.e. `(trimL limbs).length`
  from `Tess.C.ZiOrder`. Pure: no allocation. Arbitrary read-only/writable frame, memory containing the
  `zi` struct block and the limb array block.
-/
import Tess.C.ZiOrder
import Tess.C.Acmp

namespace Tess.C
open Obj.C

/-- Length after dropping trailing zero limbs, computed as the C loop does. -/
def tcount (l : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if ziAddTerm l k = 0 then tcount l k else k + 1

theorem ziAddTerm_append_left (l r : List Nat) (k : Nat) (h : k < l.length) :
    ziAddTerm (l ++ r) k = ziAddTerm l k := by
  unfold ziAddTerm
  rw [dif_pos (by simp; omega), dif_pos h, List.getElem_append_left]

theorem tcount_append (l : List Nat) (x : Nat) (k : Nat) (h : k ≤ l.length) :
    tcount (l ++ [x]) k = tcount l k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [tcount]
      rw [ziAddTerm_append_left l [x] k (by omega), ih (by omega)]

theorem trimL_snoc (l' : List Nat) (x : Nat) :
    (trimL (l' ++ [x])).length = if x = 0 then (trimL l').length else l'.length + 1 := by
  unfold trimL
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  by_cases hz : x = 0
  · subst hz
    simp [List.dropWhile_cons]
  · simp [List.dropWhile_cons, hz]

theorem trimL_length_tcount_aux (n : Nat) : ∀ l : List Nat, l.length = n →
    (trimL l).length = tcount l l.length := by
  induction n with
  | zero => intro l h; rw [List.length_eq_zero_iff.mp h]; rfl
  | succ n ih =>
      intro l h
      have hne : l ≠ [] := by intro e; simp [e] at h
      have hsplit : l = l.dropLast ++ [l.getLast hne] := (List.dropLast_concat_getLast hne).symm
      have hlen : l.dropLast.length = n := by rw [List.length_dropLast]; omega
      rw [hsplit, trimL_snoc, List.length_append, List.length_singleton]
      simp only [tcount]
      have hx : ziAddTerm (l.dropLast ++ [l.getLast hne]) l.dropLast.length = l.getLast hne := by
        unfold ziAddTerm
        rw [dif_pos (by simp)]
        simp
      rw [hx, tcount_append l.dropLast _ l.dropLast.length le_rfl, ← ih l.dropLast hlen]

theorem trimL_length_tcount (l : List Nat) : (trimL l).length = tcount l l.length :=
  trimL_length_tcount_aux l.length l rfl

/-- Load limb `j` where the loop counter is local 1 and holds `j + 1`. -/
theorem evLimbLoad1 {sg : Int} (s : State) (zb vblk : Nat)
    (limbs : List Nat) (j : Nat)
    (hm : s.mem zb = some (ziBlock vblk limbs.length sg)) (hb : vblk < 4294967296)
    (hl : s.locals 0 = some (.ptr zb 0))
    (hl1 : s.locals 1 = some (.int ⟨64, false⟩ (j + 1)))
    (hlm : s.mem vblk = some (limbBytes limbs)) (hj : j < limbs.length)
    (hlt : ∀ x ∈ limbs, x < 2 ^ 32) (hj64 : j < 18446744073709551616) :
    EvE LimbGen.prog s (.load (.int u32) (.index (.load .ptr (.field (.var 0) 0))
        (.bin .sub (some ⟨64, false⟩) (.var 1)
          (.cast u64 (.const (.int i32c 1)))) 4))
      (.int u32 (limbs[j]'hj)) := by
  have hfield : EvE LimbGen.prog s (.field (.var 0) 0) (.ptr zb 0) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var 0) 0)) (.ptr vblk 0) :=
    EvE.load hfield (load_ziBlock_v s.mem zb vblk limbs.length sg hm hb)
  have hsub : EvE LimbGen.prog s (.bin .sub (some ⟨64, false⟩) (.var 1)
        (.cast u64 (.const (.int i32c 1)))) (.int ⟨64, false⟩ j) := by
    have h2 : EvE LimbGen.prog s (.var 1) (.int ⟨64, false⟩ (j + 1)) := EvE.var hl1
    have hc : EvE LimbGen.prog s (.const (.int i32c 1)) (.int i32c 1) := EvE.const _
    have hcast : evalCast u64 (.int i32c 1) = .ok (.int ⟨64, false⟩ 1) := rfl
    have hsub' : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ (j + 1)) (.int ⟨64, false⟩ 1) = .ok (.int ⟨64, false⟩ j) := rfl
    exact EvE.bin h2 (EvE.cast hc hcast) hsub'
  have hidxlen : (limbBytes limbs).length = 4 * limbs.length := limbBytes_length limbs
  have hbounds : 0 + j * 4 ≤ (limbBytes limbs).length := by
    rw [hidxlen]
    omega
  have hidx : EvE LimbGen.prog s
      (.index (.load .ptr (.field (.var 0) 0))
        (.bin .sub (some ⟨64, false⟩) (.var 1)
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

theorem trim_loop (za vblk : Nat) (sg : Int) (l : List Nat)
    (hl : ∀ x ∈ l, x < 2 ^ 32) (hlen : l.length < 18446744073709551616) (hvb : vblk < 4294967296) :
    ∀ k, k ≤ l.length → ∀ s : State, s.locals 0 = some (.ptr za 0) →
      s.locals 1 = some (.int ⟨64, false⟩ k) →
      s.mem za = some (ziBlock vblk l.length sg) → s.mem vblk = some (limbBytes l) →
      ∃ sf, ExS LimbGen.prog s LimbGen.trim_len_loop0 .normal sf ∧
        sf.locals 1 = some (.int ⟨64, false⟩ (tcount l k)) := by
  intro k
  induction k with
  | zero =>
      intro hk s h0 h1 hza hv
      refine ⟨s, ?_, by simpa [tcount] using h1⟩
      unfold LimbGen.trim_len_loop0
      apply ExS.loop_brk
      have hv1 : EvE LimbGen.prog s (.var 1) (.int ⟨64, false⟩ 0) := EvE.var h1
      have hcond := EvE.land_false (b := (.un .lnot ⟨32, true⟩ (.load (.int ⟨32, false⟩)
        (.index (.load .ptr (.field (.var 0) 0)) (.bin .sub (some ⟨64, false⟩) (.var 1)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4)))) hv1 (by rfl)
      exact ExS.ite hcond (by rfl) ExS.brk
  | succ k ih =>
      intro hk s h0 h1 hza hv
      have hjlt : k < l.length := by omega
      have hxv := evLimbLoad1 (sg := sg) s za vblk l k hza hvb h0 h1 hv hjlt hl (by omega)
      have hv1 : EvE LimbGen.prog s (.var 1) (.int ⟨64, false⟩ (k + 1)) := EvE.var h1
      have hne1 : ((k + 1) != 0) = true := by simp
      have htr : truthy (.int ⟨64, false⟩ (k + 1)) = .ok true := by simp [truthy, hne1]
      have hnot : EvE LimbGen.prog s (.un .lnot ⟨32, true⟩ (.load (.int ⟨32, false⟩)
          (.index (.load .ptr (.field (.var 0) 0)) (.bin .sub (some ⟨64, false⟩) (.var 1)
            (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4)))
          (boolVal (!(l[k]'hjlt != 0))) :=
        EvE.un hxv (by simp [evalUn, truthy])
      have tb : ∀ b : Bool, truthy (boolVal b) = .ok b := by intro b; cases b <;> rfl
      have hcond := EvE.land_true (bb := !(l[k]'hjlt != 0)) hv1 htr hnot (tb _)
      by_cases hz : l[k]'hjlt = 0
      · -- zero limb: decrement and continue
        have hcond' : truthy (boolVal (!(l[k]'hjlt != 0))) = .ok true := by rw [tb]; simp [hz]
        have hbody : ExS LimbGen.prog s (.ite (.land (.var 1) (.un .lnot ⟨32, true⟩ (.load (.int ⟨32, false⟩)
            (.index (.load .ptr (.field (.var 0) 0)) (.bin .sub (some ⟨64, false⟩) (.var 1)
              (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4))))
            (.set 1 (.cast ⟨64, false⟩ (.bin .sub (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 1))
              (.const (.int ⟨64, false⟩ 1))))) .brk)
            .normal { s with locals := s.locals.upd 1 (.int ⟨64, false⟩ k) } := by
          have cast1 : EvE LimbGen.prog s (.cast ⟨64, false⟩ (.var 1)) (.int ⟨64, false⟩ (k + 1)) :=
            EvE.cast hv1 (cast_u64_u64' (k + 1) (by omega))
          have subb : EvE LimbGen.prog s (.bin .sub (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 1))
              (.const (.int ⟨64, false⟩ 1))) (.int ⟨64, false⟩ k) :=
            EvE.bin cast1 (EvE.const _) (by
              show evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ (k + 1)) (.int ⟨64, false⟩ 1) = .ok (.int ⟨64, false⟩ k)
              simp only [evalBin, isPtr, Bool.and_false, ite_false, Nat.mod_eq_of_lt (by omega : k + 1 < 18446744073709551616)]
              show Res.ok (Val.int ⟨64, false⟩ (if (1:Nat) ≤ k + 1 then k + 1 - 1 else k + 1 + 18446744073709551616 - 1)) = Res.ok (Val.int ⟨64, false⟩ k)
              rw [if_pos (by omega : (1:Nat) ≤ k + 1), Nat.add_sub_cancel])
          exact ExS.ite hcond hcond' (ExS.set (EvE.cast subb (cast_u64_u64' k (by omega))))
        obtain ⟨sf, hloop, hres⟩ := ih (by omega) { s with locals := s.locals.upd 1 (.int ⟨64, false⟩ k) }
          (by simpa using h0) (by simp [Locals.upd]) hza hv
        refine ⟨sf, ?_, ?_⟩
        · unfold LimbGen.trim_len_loop0 at hloop ⊢
          exact ExS.loop_next hbody (Or.inl rfl) ExS.skip hloop
        · simp only [tcount, hz, ziAddTerm, dif_pos hjlt, if_true] at hres ⊢
          exact hres
      · -- nonzero limb: leave the loop
        have hcond' : truthy (boolVal (!(l[k]'hjlt != 0))) = .ok false := by rw [tb]; simp [hz]
        refine ⟨s, ?_, ?_⟩
        · unfold LimbGen.trim_len_loop0
          exact ExS.loop_brk (ExS.ite hcond hcond' ExS.brk)
        · simp only [tcount, ziAddTerm, dif_pos hjlt, hz, if_false]
          exact h1

/-- The translated `trim_len` returns the length of the trimmed limb list. -/
theorem trim_len_refines (za vblk : Nat) (sg : Int) (l : List Nat)
    (hl : ∀ x ∈ l, x < 2 ^ 32) (hlen : l.length < 18446744073709551616) (hvb : vblk < 4294967296)
    (m : Mem) (ro : Bool) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.trim_len.params [.ptr za 0], m, ro⟩)
    (hza : m za = some (ziBlock vblk l.length sg)) (hv : m vblk = some (limbBytes l)) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.trim_len.body
      (.ret (some (.int ⟨64, false⟩ (trimL l).length))) sf := by
  have hmem : s0.mem = m := by rw [h0]
  have l0 : s0.locals 0 = some (.ptr za 0) := by rw [h0]; rfl
  have hza' : s0.mem za = some (ziBlock vblk l.length sg) := by rw [hmem]; exact hza
  have hfield : EvE LimbGen.prog s0 (.field (.var 0) 8) (.ptr za 8) :=
    EvE.field (EvE.var l0) (by simp [ptrAddN, hza', ziBlock_length])
  have hload : EvE LimbGen.prog s0 (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
      (.int ⟨64, false⟩ l.length) := by
    have := load_ziBlock_n s0.mem za vblk l.length sg hza'
    rw [Nat.mod_eq_of_lt (by simpa using hlen)] at this
    exact EvE.load hfield this
  have hset := ExS.set (i := 1) hload
  obtain ⟨sf, hloop, hres⟩ := trim_loop za vblk sg l hl hlen hvb l.length le_rfl
    { s0 with locals := s0.locals.upd 1 (.int ⟨64, false⟩ l.length) }
    (by simpa using l0) (by simp [Locals.upd]) (by simpa using hza') (by simpa [hmem] using hv)
  refine ⟨sf, ?_⟩
  unfold LimbGen.trim_len
  show ExS LimbGen.prog s0 (.seq _ (.seq LimbGen.trim_len_loop0 (.ret (some (.var 1))))) _ sf
  rw [← trimL_length_tcount] at hres
  exact ExS.seq hset (ExS.seq hloop (ExS.ret (EvE.var hres)))

end Tess.C

/-
  Limb-level model of the whole binary path of `zi_divrem` (`lib/tess/src/exact.c`), assembled from the
  models of the refined kernels `div_shift_in` (`siPrefix`), `div_cmp` (`dcFull`) and `div_sub_in`
  (`sbPrefix`): starting from a zero remainder and zero quotient limbs it processes the bits of `a`
  top-down and ends with limbs denoting `lv a / lv b` and `lv a % lv b` (`binLoop_correct`).
  The C control flow around the kernels (`tick`/status, allocation, `norm`) is not refined.
-/
import Tess.C.DivCmpC

namespace Tess.C

theorem or_pow_of_bit_zero (x t : Nat) (h : x / 2 ^ t % 2 = 0) : x ||| 2 ^ t = x + 2 ^ t := by
  have hmod : x % 2 ^ (t + 1) = x % 2 ^ t := by
    rw [Nat.mod_pow_succ, h]; simp
  have hm : x % 2 ^ t < 2 ^ t := Nat.mod_lt _ (by positivity)
  have hx : x = 2 ^ (t + 1) * (x / 2 ^ (t + 1)) + x % 2 ^ t := by
    rw [← hmod]; exact (Nat.div_add_mod x (2 ^ (t + 1))).symm
  generalize x / 2 ^ (t + 1) = H at hx
  generalize x % 2 ^ t = m at hx hm
  subst hx
  have hP : 2 ^ t + m < 2 ^ (t + 1) := by rw [pow_succ]; omega
  have hm' : m < 2 ^ (t + 1) := by rw [pow_succ]; omega
  have e : 2 ^ (t + 1) * H + m + 2 ^ t = 2 ^ (t + 1) * H + (2 ^ t + m) := by ring
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, e, Nat.testBit_two_pow_mul_add H hP j, Nat.testBit_two_pow_mul_add H hm' j,
    Nat.testBit_two_pow]
  by_cases hj : j < t + 1
  · simp only [hj, ite_true]
    rcases Nat.lt_or_ge j t with hjt | hjt
    · rw [Nat.testBit_two_pow_add_gt hjt]
      simp [show t ≠ j by omega]
    · have : j = t := by omega
      subst this
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]
      simp
  · simp [hj, show t ≠ j by omega]

/-- C bit read `(a->v[i/32] >> (i%32)) & 1`. -/
def bitOf (a : List Nat) (i : Nat) : Nat := (ziAddTerm a (i / 32) >>> (i % 32)) &&& 1

/-- C `q.v[i/32] |= 1u << (i%32)`. -/
def setBitL (q : List Nat) (i : Nat) : List Nat :=
  q.set (i / 32) (ziAddTerm q (i / 32) ||| 2 ^ (i % 32))

theorem bitOf_eq_digit (a : List Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (i : Nat) (hi : i / 32 < a.length) :
    bitOf a i = digit 2 (lv a) i := by
  rw [digit2_lv a ha i hi]
  unfold bitOf ziAddTerm
  rw [dif_pos hi, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem setBitL_value (q : List Nat) (hq : ∀ x ∈ q, x < 2 ^ 32) (i : Nat) (hi : i / 32 < q.length)
    (hz : lv q / 2 ^ i % 2 = 0) :
    lv (setBitL q i) = lv q + 2 ^ i ∧ (setBitL q i).length = q.length ∧
      (∀ x ∈ setBitL q i, x < 2 ^ 32) := by
  have hd := digit2_lv q hq i hi
  have hz' : q[i / 32]'hi / 2 ^ (i % 32) % 2 = 0 := by
    rw [← hd]; unfold digit; simpa using hz
  have hor := or_pow_of_bit_zero (q[i / 32]'hi) (i % 32) hz'
  have hzt : ziAddTerm q (i / 32) = q[i / 32]'hi := by unfold ziAddTerm; rw [dif_pos hi]
  have hxlt : q[i / 32]'hi < 2 ^ 32 := hq _ (List.getElem_mem hi)
  have hlt32 : 2 ^ (i % 32) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt _ (by norm_num))
  have hor_lt : q[i / 32]'hi ||| 2 ^ (i % 32) < 2 ^ 32 := Nat.or_lt_two_pow hxlt hlt32
  unfold setBitL
  rw [hzt]
  refine ⟨?_, by simp, ?_⟩
  · have h := lv_set q (i / 32) (q[i / 32]'hi ||| 2 ^ (i % 32)) hi
    rw [hor] at h
    simp only [List.getElem?_eq_getElem hi, Option.getD_some] at h
    rw [hor]
    have hi' : 32 * (i / 32) + i % 32 = i := by omega
    have : 2 ^ i = 2 ^ (i % 32) * 2 ^ (32 * (i / 32)) := by rw [← pow_add]; congr 1; omega
    rw [this]
    nlinarith [h]
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact hq x hx
    · exact hor_lt

/-- One iteration of the C bit loop at bit `i`: shift in the bit of `a`, compare, subtract and set the
quotient bit when the remainder reached the divisor. -/
def blStep (a b : List Nat) (st : List Nat × List Nat) (i : Nat) : List Nat × List Nat :=
  let r1 := siPrefix st.2 (bitOf a i) st.2.length
  if lv b ≤ lv r1 then (setBitL st.1 i, sbPrefix r1 b st.2.length) else (st.1, r1)

def blRun (a b : List Nat) : Nat → List Nat × List Nat
  | 0 => (List.replicate a.length 0, List.replicate (b.length + 1) 0)
  | j + 1 => blStep a b (blRun a b j) (32 * a.length - 1 - j)

theorem blRun_inv (a b : List Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32)
    (hpos : 0 < lv b) :
    ∀ j, j ≤ 32 * a.length →
      (blRun a b j).1.length = a.length ∧ (blRun a b j).2.length = b.length + 1 ∧
      (∀ x ∈ (blRun a b j).1, x < 2 ^ 32) ∧ (∀ x ∈ (blRun a b j).2, x < 2 ^ 32) ∧
      lv (blRun a b j).2 = (binRun (lv b) (lv a) (32 * a.length) j).2 ∧
      lv (blRun a b j).1 = (binRun (lv b) (lv a) (32 * a.length) j).1 * 2 ^ (32 * a.length - j) ∧
      lv (blRun a b j).2 < lv b := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨by simp [blRun], by simp [blRun], ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx; simp [blRun] at hx; omega
      · intro x hx; simp [blRun] at hx; omega
      · simp [blRun, binRun, lv_zeros]
      · simp [blRun, binRun, lv_zeros]
      · simp [blRun, lv_zeros, hpos]
  | succ j ih =>
      intro hj
      obtain ⟨hq1, hr1, hq2, hr2, hlr, hlq, hrb⟩ := ih (by omega)
      set L := 32 * a.length with hL
      set i := L - 1 - j with hi
      have hiL : i < L := by omega
      have hi32 : i / 32 < a.length := by omega
      set st := blRun a b j with hst
      have hdig : bitOf a i = digit 2 (lv a) i := bitOf_eq_digit a ha i hi32
      have hk : bitOf a i ≤ 1 := by
        rw [hdig]; unfold digit; have := Nat.mod_lt (lv a / 2 ^ i) (show 0 < 2 by norm_num); omega
      have hden := bitStepLimbs_denotes st.2 b (bitOf a i) (binRun (lv b) (lv a) L j).1 hr2 hb hr1 hk hrb
      have hpair : ((binRun (lv b) (lv a) L j).1, lv st.2) = binRun (lv b) (lv a) L j := by
        rw [hlr]
      rw [hpair] at hden
      have hbin : binRun (lv b) (lv a) L (j + 1) =
          binStep (lv b) (binRun (lv b) (lv a) L j) (bitOf a i) := by
        show binStep _ _ _ = _
        rw [hdig]
      have hsucc : blRun a b (j + 1) = blStep a b st i := rfl
      have hbsl : (blStep a b st i).2 = bitStepLimbs st.2 b (bitOf a i) := by
        unfold blStep bitStepLimbs; simp only []; split_ifs <;> rfl
      have hLj : L - j = i + 1 := by omega
      have hLj1 : L - (j + 1) = i := by omega
      have hshift := bit_shift_step st.2 b (bitOf a i) hr2 hb hr1 hk hrb
      generalize binRun (lv b) (lv a) L j = B at hden hlr hlq hbin
      obtain ⟨Qj, Rj⟩ := B
      simp only [] at hlr hlq hden
      rw [hLj] at hlq
      rw [hLj1, hbin, hsucc]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · by_cases hge : lv b ≤ lv (siPrefix st.2 (bitOf a i) st.2.length)
        · have hz : lv st.1 / 2 ^ i % 2 = 0 := by
            rw [hlq, show Qj * 2 ^ (i + 1) = (2 * Qj) * 2 ^ i by ring,
              Nat.mul_div_cancel _ (by positivity)]
            omega
          obtain ⟨-, sl, -⟩ := setBitL_value st.1 hq2 i (by omega) hz
          unfold blStep; simp only [hge, if_true]; rw [sl, hq1]
        · unfold blStep; simp only [hge, if_false]; exact hq1
      · rw [hbsl]; exact hden.2.1.trans hr1
      · by_cases hge : lv b ≤ lv (siPrefix st.2 (bitOf a i) st.2.length)
        · have hz : lv st.1 / 2 ^ i % 2 = 0 := by
            rw [hlq, show Qj * 2 ^ (i + 1) = (2 * Qj) * 2 ^ i by ring,
              Nat.mul_div_cancel _ (by positivity)]
            omega
          obtain ⟨-, -, sb⟩ := setBitL_value st.1 hq2 i (by omega) hz
          unfold blStep; simp only [hge, if_true]; exact sb
        · unfold blStep; simp only [hge, if_false]; exact hq2
      · rw [hbsl]; exact hden.2.2.1
      · rw [hbsl]; exact hden.1
      · by_cases hge : lv b ≤ lv (siPrefix st.2 (bitOf a i) st.2.length)
        · have hz : lv st.1 / 2 ^ i % 2 = 0 := by
            rw [hlq, show Qj * 2 ^ (i + 1) = (2 * Qj) * 2 ^ i by ring,
              Nat.mul_div_cancel _ (by positivity)]
            omega
          obtain ⟨sv, -, -⟩ := setBitL_value st.1 hq2 i (by omega) hz
          have hge' : lv b ≤ 2 * Rj + bitOf a i := by
            have := hshift.1; omega
          unfold blStep binStep
          simp only [hge, hge', if_true]
          rw [sv, hlq, pow_succ]; ring
        · have hge' : ¬ lv b ≤ 2 * Rj + bitOf a i := by
            have := hshift.1; omega
          unfold blStep binStep
          simp only [hge, hge', if_false]
          rw [hlq, pow_succ]; ring
      · rw [hbsl]; exact hden.2.2.2

theorem binLoop_correct (a b : List Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32)
    (hbne : b ≠ []) (hbn : Normalized b) :
    lv (blRun a b (32 * a.length)).1 = lv a / lv b ∧
      lv (blRun a b (32 * a.length)).2 = lv a % lv b := by
  have hpos : 0 < lv b := by
    have := lv_normalized_ge b hbne hbn
    have : 0 < 2 ^ (32 * (b.length - 1)) := pow_pos (by norm_num) _
    omega
  obtain ⟨-, -, -, -, h2, h1, -⟩ := blRun_inv a b ha hb hpos (32 * a.length) le_rfl
  obtain ⟨f1, f2⟩ := divrem_multi a b ha hbne hbn
  rw [Nat.sub_self, pow_zero, Nat.mul_one] at h1
  exact ⟨h1.trans f1, h2.trans f2⟩

end Tess.C

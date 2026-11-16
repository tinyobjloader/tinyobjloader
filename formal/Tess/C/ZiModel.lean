/-
  Pure functional models of `zi_add`, `zi_sub` and `zi_mul` from
  `lib/tess/src/exact.c`, assembled from the proved limb-loop models, and
  proofs that they denote signed integer addition/subtraction/multiplication.

  The models mirror the C control flow (zero early-outs, sign dispatch via the
  `acmp` order, `norm` trimming with zero-sign). Allocation, budget ticks and
  `move` are not modelled. These are statements about the models, whose
  loop bodies are tied to the C by the MiniC refinement proofs.
-/
import Tess.C.ZiOrder

namespace Tess.C

/-- A signed bignum as in `zi`: sign in {-1,0,1} and normalized limbs. -/
structure ZiM where
  sign : Int
  limbs : List Nat

def ZiM.val (z : ZiM) : Int := sval z.sign z.limbs

/-- `norm`: trim zero limbs and zero the sign if empty. -/
def zNorm (s : Int) (l : List Nat) : ZiM :=
  ⟨if trimL l = [] then 0 else s, trimL l⟩

theorem trimL_mem (l : List Nat) (x : Nat) (h : x ∈ trimL l) : x ∈ l := by
  unfold trimL at h
  rw [List.mem_reverse] at h
  have hs := List.takeWhile_append_dropWhile (p := (· == 0)) (l := l.reverse)
  have : x ∈ l.reverse := by rw [← hs]; exact List.mem_append_right _ h
  exact List.mem_reverse.mp this

theorem zNorm_val (s : Int) (l : List Nat) : (zNorm s l).val = sval s l := by
  unfold ZiM.val sval zNorm
  by_cases h : trimL l = []
  · have h0 : lv l = 0 := by rw [← lv_trimL, h]; rfl
    simp [h, h0]
  · simp only [if_neg h, lv_trimL]

theorem zNorm_normalized (s : Int) (l : List Nat) : Normalized (zNorm s l).limbs :=
  trimL_normalized l

/-- Well-formed inputs: normalized limbs under 2^32 and a sign in {-1,0,1}. -/
structure ZiM.WF (z : ZiM) : Prop where
  norm : Normalized z.limbs
  bound : ∀ x ∈ z.limbs, x < 2 ^ 32
  sign : z.sign = 0 ∨ z.sign = 1 ∨ z.sign = -1
  zero : z.sign = 0 → z.limbs = []

/-- Model of `zi_add`. -/
def ziAddM (a b : ZiM) : ZiM :=
  let n := max a.limbs.length b.limbs.length
  if a.sign = 0 then b
  else if b.sign = 0 then a
  else if a.sign = b.sign then
    zNorm a.sign (ziAddPrefix a.limbs b.limbs n ++ [ziAddCarryPrefix a.limbs b.limbs n])
  else if lv b.limbs ≤ lv a.limbs then zNorm a.sign (ziMixedPrefix a.limbs b.limbs n)
  else zNorm b.sign (ziMixedPrefix b.limbs a.limbs n)

def ziNegM (b : ZiM) : ZiM := ⟨-b.sign, b.limbs⟩

theorem ziNegM_wf (b : ZiM) (h : b.WF) : (ziNegM b).WF :=
  ⟨h.norm, h.bound, by rcases h.sign with h | h | h <;> simp [ziNegM, h], by
    intro h0; exact h.zero (by simpa [ziNegM] using h0)⟩

theorem ziAddPrefix_mem (a b : List Nat) (k : Nat) : ∀ x ∈ ziAddPrefix a b k, x < 2 ^ 32 := by
  induction k with
  | zero => simp [ziAddPrefix]
  | succ k ih =>
      intro x hx
      simp only [ziAddPrefix, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih x hx
      · exact Nat.mod_lt _ (by omega)

theorem zNorm_wf (s : Int) (l : List Nat) (hl : ∀ x ∈ l, x < 2 ^ 32)
    (hs : s = 1 ∨ s = -1) : (zNorm s l).WF := by
  refine ⟨zNorm_normalized s l, fun x hx => hl x (trimL_mem l x hx), ?_, ?_⟩
  · by_cases h : trimL l = [] <;> simp [zNorm, h]
    exact Or.inr hs
  · by_cases h : trimL l = []
    · simp [zNorm, h]
    · intro h0
      simp only [zNorm, if_neg h] at h0
      rcases hs with rfl | rfl <;> simp at h0

theorem ziAddM_val (a b : ZiM) (ha : a.WF) (hb : b.WF) :
    (ziAddM a b).val = a.val + b.val ∧ (ziAddM a b).WF := by
  have hn : a.limbs.length ≤ max a.limbs.length b.limbs.length := le_max_left _ _
  have hm : b.limbs.length ≤ max a.limbs.length b.limbs.length := le_max_right _ _
  have hnz : ∀ z : ZiM, z.WF → z.sign ≠ 0 → (z.sign = 1 ∨ z.sign = -1) := by
    intro z hz h; rcases hz.sign with h' | h' | h' <;> simp_all
  unfold ziAddM
  by_cases h1 : a.sign = 0
  · have : a.limbs = [] := ha.zero h1
    simp only [h1, if_true]
    refine ⟨?_, hb⟩
    simp [ZiM.val, sval, h1, lv]
  by_cases h2 : b.sign = 0
  · have : b.limbs = [] := hb.zero h2
    simp only [h1, h2, if_false, if_true]
    refine ⟨?_, ha⟩
    simp [ZiM.val, sval, h2, lv]
  simp only [h1, h2, if_false]
  have sa := hnz a ha h1
  have sb := hnz b hb h2
  set n := max a.limbs.length b.limbs.length
  by_cases h3 : a.sign = b.sign
  · simp only [h3, if_true]
    have hmem : ∀ x ∈ ziAddPrefix a.limbs b.limbs n ++ [ziAddCarryPrefix a.limbs b.limbs n],
        x < 2 ^ 32 := by
      intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ziAddPrefix_mem a.limbs b.limbs n x hx
      · have := ziAddCarryPrefix_bound a.limbs b.limbs ha.bound hb.bound n
        omega
    refine ⟨?_, zNorm_wf _ _ hmem (by rw [← h3]; exact sa)⟩
    rw [zNorm_val]
    unfold sval ZiM.val
    rw [← h3, ziAdd_value _ _ n hn hm]
    push_cast; simp only [sval]; ring
  · simp only [h3, if_false]
    have hopp : b.sign = -a.sign := by rcases sa with h | h <;> rcases sb with h' | h' <;> simp_all
    by_cases h4 : lv b.limbs ≤ lv a.limbs
    · simp only [h4, if_true]
      obtain ⟨-, hv⟩ := ziMixed_value a.limbs b.limbs ha.bound hb.bound n hn hm h4
      refine ⟨?_, zNorm_wf _ _ (ziMixedPrefix_mem _ _ ha.bound hb.bound n) sa⟩
      rw [zNorm_val]
      unfold sval ZiM.val
      rw [hopp]
      have : (lv (ziMixedPrefix a.limbs b.limbs n) : Int) = lv a.limbs - lv b.limbs := by omega
      rw [this]; simp only [sval]; ring
    · simp only [h4, if_false]
      have h5 : lv a.limbs ≤ lv b.limbs := by omega
      obtain ⟨-, hv⟩ := ziMixed_value b.limbs a.limbs hb.bound ha.bound n hm hn h5
      refine ⟨?_, zNorm_wf _ _ (ziMixedPrefix_mem _ _ hb.bound ha.bound n) sb⟩
      rw [zNorm_val]
      unfold sval ZiM.val
      have hopp' : a.sign = -b.sign := by rw [hopp]; ring
      rw [hopp']
      have : (lv (ziMixedPrefix b.limbs a.limbs n) : Int) = lv b.limbs - lv a.limbs := by omega
      rw [this]; simp only [sval]; ring

/-- Model of `zi_sub`. -/
def ziSubM (a b : ZiM) : ZiM := ziAddM a (ziNegM b)

theorem ziSubM_val (a b : ZiM) (ha : a.WF) (hb : b.WF) :
    (ziSubM a b).val = a.val - b.val ∧ (ziSubM a b).WF := by
  obtain ⟨h1, h2⟩ := ziAddM_val a (ziNegM b) ha (ziNegM_wf b hb)
  refine ⟨?_, h2⟩
  unfold ziSubM; rw [h1]
  simp [ZiM.val, sval, ziNegM]; ring

/-- Model of `zi_mul`. -/
def ziMulM (a b : ZiM) : ZiM :=
  if a.limbs = [] ∨ b.limbs = [] then ⟨0, []⟩
  else zNorm (a.sign * b.sign)
    (ziMulRows a.limbs b.limbs (List.replicate (a.limbs.length + b.limbs.length) 0) a.limbs.length)

theorem ziMulM_val (a b : ZiM) (ha : a.WF) (hb : b.WF) :
    (ziMulM a b).val = a.val * b.val ∧ (ziMulM a b).WF := by
  unfold ziMulM
  by_cases hz : a.limbs = [] ∨ b.limbs = []
  · rw [if_pos hz]
    refine ⟨?_, ⟨by intro h; simp at h, by simp, Or.inl rfl, fun _ => rfl⟩⟩
    rcases hz with h | h <;> simp [ZiM.val, sval, h, lv]
  · rw [if_neg hz]
    have hsa : a.sign = 1 ∨ a.sign = -1 := by
      rcases ha.sign with h | h | h
      · exact absurd (ha.zero h) (by tauto)
      · exact Or.inl h
      · exact Or.inr h
    have hsb : b.sign = 1 ∨ b.sign = -1 := by
      rcases hb.sign with h | h | h
      · exact absurd (hb.zero h) (by tauto)
      · exact Or.inl h
      · exact Or.inr h
    have hmem : ∀ x ∈ ziMulRows a.limbs b.limbs (List.replicate (a.limbs.length + b.limbs.length) 0)
        a.limbs.length, x < 2 ^ 32 :=
      ziMulRows_mem_bound _ _ _ ha.bound hb.bound (by intro x hx; simp at hx; omega) _
    refine ⟨?_, zNorm_wf _ _ hmem (by rcases hsa with h | h <;> rcases hsb with h' | h' <;> simp [h, h'])⟩
    rw [zNorm_val]
    unfold sval ZiM.val
    rw [ziMul_value _ _ ha.bound hb.bound _ le_rfl]
    push_cast; simp only [sval]; ring

end Tess.C

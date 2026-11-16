/-
  Functional model of the rational layer of `lib/tess/src/exact.c`
  (`reduce`, `qr_add`, `qr_sub`, `qr_mul`): reduction by the Euclidean loop
  yields the canonical lowest-terms representation (positive denominator,
  coprime), preserves the rational value, and the arithmetic wrappers denote
  rational `+`, `-`, `*`. The equal-denominator shortcut in `qr_add` is shown
  to yield the same canonical pair. Allocation, budget and `move` are not
  modelled; the integer operations underneath are the `ZiModel` models.
-/
import Tess.C.ZiModel
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.GCD

namespace Tess.C

/-- The `while (y.n) { (x,y) = (y, x mod y) }` loop of `reduce` on magnitudes. -/
def euclidLoop : Nat → Nat → Nat → Nat
  | 0, x, _ => x
  | fuel + 1, x, y => if y = 0 then x else euclidLoop fuel y (x % y)

theorem euclidLoop_eq (x y : Nat) : ∀ fuel, y < fuel → euclidLoop fuel x y = Nat.gcd x y := by
  intro fuel
  induction fuel generalizing x y with
  | zero => intro h; omega
  | succ f ih =>
      intro h
      unfold euclidLoop
      by_cases hy : y = 0
      · simp [hy]
      · rw [if_neg hy, ih y (x % y) (by have := Nat.mod_lt x (Nat.pos_of_ne_zero hy); omega),
          Nat.gcd_comm y (x % y), ← Nat.gcd_rec y x, Nat.gcd_comm]

/-- `reduce`: fix the denominator sign, send zero to `0/1`, divide by the gcd. -/
def reduceM (n d : Int) : Int × Int :=
  let n1 := if d < 0 then -n else n
  let d1 := if d < 0 then -d else d
  if n1 = 0 then (0, 1)
  else (n1 / (Int.gcd n1 d1 : Int), d1 / (Int.gcd n1 d1 : Int))

/-- Canonical form: positive denominator, coprime. -/
def Canon (p : Int × Int) : Prop := 0 < p.2 ∧ Nat.Coprime p.1.natAbs p.2.natAbs

theorem reduce_pos (n d : Int) (hn : n ≠ 0) (hd : 0 < d) :
    0 < d / (Int.gcd n d : Int) ∧
    Nat.Coprime (n / (Int.gcd n d : Int)).natAbs (d / (Int.gcd n d : Int)).natAbs ∧
    ((n / (Int.gcd n d : Int) : Int) : Rat) / ((d / (Int.gcd n d : Int) : Int) : Rat) =
      (n : Rat) / d := by
  have hg : 0 < Int.gcd n d := Int.gcd_pos_of_ne_zero_right n (by omega)
  have hgi : (0 : Int) < (Int.gcd n d : Int) := by exact_mod_cast hg
  obtain ⟨n', hn'⟩ := Int.gcd_dvd_left (a := n) (b := d)
  obtain ⟨d', hd'⟩ := Int.gcd_dvd_right (a := n) (b := d)
  set g : Int := (Int.gcd n d : Int)
  have e1 : n / g = n' := by rw [hn']; exact Int.mul_ediv_cancel_left _ hgi.ne'
  have e2 : d / g = d' := by rw [hd']; exact Int.mul_ediv_cancel_left _ hgi.ne'
  have hd'pos : 0 < d' := by
    by_contra h; have : d' ≤ 0 := by omega
    nlinarith
  refine ⟨by rw [e2]; exact hd'pos, ?_, ?_⟩
  · have := Int.gcd_div_gcd_div_gcd hg
    rw [e1, e2] at this
    rw [e1, e2]
    exact this
  · rw [e1, e2]
    have hgq : (g : Rat) ≠ 0 := by exact_mod_cast hgi.ne'
    have hd'q : (d' : Rat) ≠ 0 := by exact_mod_cast hd'pos.ne'
    rw [hn', hd']
    push_cast
    rw [mul_div_mul_left _ _ hgq]

theorem reduceM_spec (n d : Int) (hd : d ≠ 0) :
    Canon (reduceM n d) ∧ ((reduceM n d).1 : Rat) / (reduceM n d).2 = (n : Rat) / d := by
  unfold reduceM Canon
  have hdq : (d : Rat) ≠ 0 := by exact_mod_cast hd
  by_cases hneg : d < 0
  · simp only [hneg, ite_true]
    by_cases hn : -n = 0
    · have : n = 0 := by omega
      simp [hn, this]
    · simp only [hn, ite_false]
      obtain ⟨h1, h2, h3⟩ := reduce_pos (-n) (-d) hn (by omega)
      refine ⟨⟨h1, h2⟩, ?_⟩
      rw [h3]; push_cast
      rw [neg_div_neg_eq]
  · simp only [hneg, ite_false]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ite_false]
      obtain ⟨h1, h2, h3⟩ := reduce_pos n d hn (by omega)
      exact ⟨⟨h1, h2⟩, h3⟩

def qv (p : Int × Int) : Rat := (p.1 : Rat) / p.2

theorem canon_unique (p q : Int × Int) (hp : Canon p) (hq : Canon q) (h : qv p = qv q) :
    p = q := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  have := Rat.div_int_inj hp.1 hq.1 hp.2 hq.2 h
  exact Prod.ext this.1 this.2

/-- `qr_add`: equal canonical denominators take the shortcut, else cross-multiply. -/
def qrAddM (a b : Int × Int) : Int × Int :=
  if a.2 = b.2 then reduceM (a.1 + b.1) a.2
  else reduceM (a.1 * b.2 + b.1 * a.2) (a.2 * b.2)

def qrMulM (a b : Int × Int) : Int × Int := reduceM (a.1 * b.1) (a.2 * b.2)
def qrSubM (a b : Int × Int) : Int × Int := qrAddM a (-b.1, b.2)

theorem qrAddM_spec (a b : Int × Int) (ha : Canon a) (hb : Canon b) :
    Canon (qrAddM a b) ∧ qv (qrAddM a b) = qv a + qv b := by
  have ha2 : (a.2 : Rat) ≠ 0 := by exact_mod_cast ha.1.ne'
  have hb2 : (b.2 : Rat) ≠ 0 := by exact_mod_cast hb.1.ne'
  unfold qrAddM
  by_cases h : a.2 = b.2
  · simp only [h, ite_true]
    obtain ⟨c1, c2⟩ := reduceM_spec (a.1 + b.1) b.2 hb.1.ne'
    refine ⟨c1, ?_⟩
    unfold qv at *
    rw [c2, ← h]; push_cast
    rw [add_div]
  · simp only [h, ite_false]
    obtain ⟨c1, c2⟩ := reduceM_spec (a.1 * b.2 + b.1 * a.2) (a.2 * b.2)
      (Int.mul_ne_zero ha.1.ne' hb.1.ne')
    refine ⟨c1, ?_⟩
    unfold qv at *
    rw [c2]; push_cast
    rw [div_add_div _ _ ha2 hb2]
    ring

theorem qrMulM_spec (a b : Int × Int) (ha : Canon a) (hb : Canon b) :
    Canon (qrMulM a b) ∧ qv (qrMulM a b) = qv a * qv b := by
  have ha2 : (a.2 : Rat) ≠ 0 := by exact_mod_cast ha.1.ne'
  have hb2 : (b.2 : Rat) ≠ 0 := by exact_mod_cast hb.1.ne'
  obtain ⟨c1, c2⟩ := reduceM_spec (a.1 * b.1) (a.2 * b.2) (Int.mul_ne_zero ha.1.ne' hb.1.ne')
  refine ⟨c1, ?_⟩
  unfold qrMulM qv at *
  rw [c2]; push_cast
  rw [div_mul_div_comm]

theorem qrSubM_spec (a b : Int × Int) (ha : Canon a) (hb : Canon b) :
    Canon (qrSubM a b) ∧ qv (qrSubM a b) = qv a - qv b := by
  have hnb : Canon (-b.1, b.2) := by
    refine ⟨hb.1, ?_⟩
    simpa using hb.2
  obtain ⟨c1, c2⟩ := qrAddM_spec a (-b.1, b.2) ha hnb
  refine ⟨c1, ?_⟩
  unfold qrSubM; rw [c2]
  unfold qv; push_cast; ring

/-- The equal-denominator shortcut agrees with the general path (canonical form is unique). -/
theorem qrAdd_shortcut_agrees (a b : Int × Int) (ha : Canon a) (hb : Canon b) (h : a.2 = b.2) :
    reduceM (a.1 + b.1) a.2 = reduceM (a.1 * b.2 + b.1 * a.2) (a.2 * b.2) := by
  have hp : 0 < a.2 * b.2 := Int.mul_pos ha.1 hb.1
  have s1 := reduceM_spec (a.1 + b.1) a.2 ha.1.ne'
  have s2 := reduceM_spec (a.1 * b.2 + b.1 * a.2) (a.2 * b.2) hp.ne'
  apply canon_unique _ _ s1.1 s2.1
  unfold qv; rw [s1.2, s2.2]
  have ha2 : (a.2 : Rat) ≠ 0 := by exact_mod_cast ha.1.ne'
  rw [← h]; push_cast
  rw [div_eq_div_iff ha2 (mul_ne_zero ha2 ha2)]
  ring

end Tess.C

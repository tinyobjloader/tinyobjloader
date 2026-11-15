/-
  Proof rules for MiniC ("eventually" semantics).

  `EvE p s e v` : for all sufficiently large fuel, `e` evaluates to `v`.
  `ExS p s st r`: for all sufficiently large fuel, `st` terminates with `r`.

  Both rule out undefined behaviour and non-termination. The rules below
  are lemmas about the executable semantics; nothing here is an axiom.
-/
import Obj.C.Semantics

namespace Obj.C

def EvE (p : Prog) (s : State) (e : Expr) (v : Val) : Prop :=
  ∃ K, ∀ n, K ≤ n → evalExpr p n s e = .ok v

def EvArgs (p : Prog) (s : State) (es : List Expr) (vs : List Val) : Prop :=
  ∃ K, ∀ n, K ≤ n → evalArgs p n s es = .ok vs

def ExS (p : Prog) (s : State) (st : Stmt) (o : Outcome) (s' : State) : Prop :=
  ∃ K, ∀ n, K ≤ n → execStmt p n s st = .ok (o, s')

section
variable {p : Prog} {s : State}

/-- Lift a single-step fuel shift. -/
private theorem shift {α} {f : Nat → Res α} {r : Res α} {K : Nat}
    (h : ∀ n, K ≤ n → f (n + 1) = r) : ∀ n, K + 1 ≤ n → f n = r := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact h m (by omega)

theorem EvE.const (v : Val) : EvE p s (.const v) v :=
  ⟨1, shift (K := 0) fun _ _ => rfl⟩

theorem EvE.var {i : Nat} {v : Val} (h : s.locals i = some v) : EvE p s (.var i) v :=
  ⟨1, shift (K := 0) fun _ _ => by simp [evalExpr, h]⟩

theorem EvE.load {ty a pa v} (ha : EvE p s a pa) (hl : load s.mem ty pa = .ok v) :
    EvE p s (.load ty a) v := by
  obtain ⟨K, hK⟩ := ha
  exact ⟨K + 1, shift fun n hn => by simp only [evalExpr, hK n hn, Res.bind_eq, Res.bind_ok, hl]⟩

theorem EvE.index {base idx pb t i r} {elem : Nat} (hb : EvE p s base pb) (hi : EvE p s idx (.int t i))
    (hr : (if t.signed then ptrAdd s.mem pb (t.toInt i * (elem : Int)) else ptrAddN s.mem pb (i * elem))
      = .ok r) : EvE p s (.index base idx elem) r := by
  obtain ⟨K1, h1⟩ := hb
  obtain ⟨K2, h2⟩ := hi
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), h2 n (by omega), Res.bind_eq, Res.bind_ok, hr]⟩

theorem EvE.field {base pb r} {off : Nat} (hb : EvE p s base pb)
    (hr : ptrAddN s.mem pb off = .ok r) : EvE p s (.field base off) r := by
  obtain ⟨K1, h1⟩ := hb
  exact ⟨K1 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), Res.bind_eq, Res.bind_ok, hr]⟩

theorem EvE.bin {op t a b va vb v} (ha : EvE p s a va) (hb : EvE p s b vb)
    (hv : evalBin op t va vb = .ok v) : EvE p s (.bin op t a b) v := by
  obtain ⟨K1, h1⟩ := ha
  obtain ⟨K2, h2⟩ := hb
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), h2 n (by omega), Res.bind_eq, Res.bind_ok, hv]⟩

theorem EvE.un {op t a va v} (ha : EvE p s a va) (hv : evalUn op t va = .ok v) :
    EvE p s (.un op t a) v := by
  obtain ⟨K1, h1⟩ := ha
  exact ⟨K1 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), Res.bind_eq, Res.bind_ok, hv]⟩

theorem EvE.cast {t a va v} (ha : EvE p s a va) (hv : evalCast t va = .ok v) :
    EvE p s (.cast t a) v := by
  obtain ⟨K1, h1⟩ := ha
  exact ⟨K1 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), Res.bind_eq, Res.bind_ok, hv]⟩

theorem EvE.land_false {a b va} (ha : EvE p s a va) (hf : truthy va = .ok false) :
    EvE p s (.land a b) (boolVal false) := by
  obtain ⟨K1, h1⟩ := ha
  exact ⟨K1 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), Res.bind_eq, Res.bind_ok, hf]; rfl⟩

theorem EvE.land_true {a b va vb bb} (ha : EvE p s a va) (ht : truthy va = .ok true)
    (hb : EvE p s b vb) (hbb : truthy vb = .ok bb) : EvE p s (.land a b) (boolVal bb) := by
  obtain ⟨K1, h1⟩ := ha
  obtain ⟨K2, h2⟩ := hb
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), h2 n (by omega), Res.bind_eq, Res.bind_ok, ht, hbb,
      ite_true]; rfl⟩

theorem EvE.lor_true {a b va} (ha : EvE p s a va) (ht : truthy va = .ok true) :
    EvE p s (.lor a b) (boolVal true) := by
  obtain ⟨K1, h1⟩ := ha
  exact ⟨K1 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), Res.bind_eq, Res.bind_ok, ht, ite_true]; rfl⟩

theorem EvE.lor_false {a b va vb bb} (ha : EvE p s a va) (hf : truthy va = .ok false)
    (hb : EvE p s b vb) (hbb : truthy vb = .ok bb) : EvE p s (.lor a b) (boolVal bb) := by
  obtain ⟨K1, h1⟩ := ha
  obtain ⟨K2, h2⟩ := hb
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), h2 n (by omega), Res.bind_eq, Res.bind_ok, hf, hbb]
    rfl⟩

theorem EvE.cond {c a b vc bc v} (hc : EvE p s c vc) (hbc : truthy vc = .ok bc)
    (hv : EvE p s (if bc then a else b) v) : EvE p s (.cond c a b) v := by
  obtain ⟨K1, h1⟩ := hc
  obtain ⟨K2, h2⟩ := hv
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), Res.bind_eq, Res.bind_ok, hbc]
    cases bc <;> simpa using h2 n (by omega)⟩

theorem EvArgs.nil : EvArgs p s [] [] := ⟨1, shift (K := 0) fun _ _ => rfl⟩

theorem EvArgs.cons {e es v vs} (h : EvE p s e v) (hs : EvArgs p s es vs) :
    EvArgs p s (e :: es) (v :: vs) := by
  obtain ⟨K1, h1⟩ := h
  obtain ⟨K2, h2⟩ := hs
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [evalArgs, h1 n (by omega), h2 n (by omega), Res.bind_eq, Res.bind_ok]; rfl⟩

theorem EvE.call {f args vs fn v s'} (hargs : EvArgs p s args vs) (hf : p f = some fn)
    (hlen : fn.params.length = vs.length)
    (hbody : ExS p ⟨frameLocals fn.params vs, s.mem, true⟩ fn.body (.ret (some v)) s') :
    EvE p s (.call f args) v := by
  obtain ⟨K1, h1⟩ := hargs
  obtain ⟨K2, h2⟩ := hbody
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [evalExpr, h1 n (by omega), Res.bind_eq, Res.bind_ok, hf, hlen, ite_true]
    simp only [h2 n (by omega), Res.bind_ok]⟩

/-! ### Statements -/

theorem ExS.skip : ExS p s .skip .normal s := ⟨1, shift (K := 0) fun _ _ => rfl⟩

theorem ExS.set {i e v} (h : EvE p s e v) :
    ExS p s (.set i e) .normal { s with locals := s.locals.upd i v } := by
  obtain ⟨K1, h1⟩ := h
  exact ⟨K1 + 1, shift fun n hn => by simp only [execStmt, h1 n hn, Res.bind_eq, Res.bind_ok]; rfl⟩

theorem ExS.store {ty a e pa v m'} (ha : EvE p s a pa) (he : EvE p s e v) (hro : s.ro = false)
    (hm : store s.mem ty pa v = .ok m') :
    ExS p s (.store ty a e) .normal { s with mem := m' } := by
  obtain ⟨K1, h1⟩ := ha
  obtain ⟨K2, h2⟩ := he
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), h2 n (by omega), Res.bind_eq, Res.bind_ok, hro, hm,
      guard, Bool.not_false, ite_true]; rfl⟩

theorem ExS.seq {a b s1 r s2} (ha : ExS p s a .normal s1) (hb : ExS p s1 b r s2) :
    ExS p s (.seq a b) r s2 := by
  obtain ⟨K1, h1⟩ := ha
  obtain ⟨K2, h2⟩ := hb
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), h2 n (by omega), Res.bind_eq, Res.bind_ok]⟩

theorem ExS.seq_ret {a b s1 v} (ha : ExS p s a (.ret v) s1) : ExS p s (.seq a b) (.ret v) s1 := by
  obtain ⟨K1, h1⟩ := ha
  exact ⟨K1 + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), Res.bind_eq, Res.bind_ok]; rfl⟩

theorem ExS.seq_brk {a b s1} (ha : ExS p s a .brk s1) : ExS p s (.seq a b) .brk s1 := by
  obtain ⟨K1, h1⟩ := ha
  exact ⟨K1 + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), Res.bind_eq, Res.bind_ok]; rfl⟩

theorem ExS.ite {c a b vc bc r s'} (hc : EvE p s c vc) (hbc : truthy vc = .ok bc)
    (h : ExS p s (if bc then a else b) r s') : ExS p s (.ite c a b) r s' := by
  obtain ⟨K1, h1⟩ := hc
  obtain ⟨K2, h2⟩ := h
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), Res.bind_eq, Res.bind_ok, hbc]
    cases bc <;> simpa using h2 n (by omega)⟩

theorem ExS.brk : ExS p s .brk .brk s := ⟨1, shift (K := 0) fun _ _ => rfl⟩

theorem ExS.ret {e v} (h : EvE p s e v) : ExS p s (.ret (some e)) (.ret (some v)) s := by
  obtain ⟨K1, h1⟩ := h
  exact ⟨K1 + 1, shift fun n hn => by simp only [execStmt, h1 n hn, Res.bind_eq, Res.bind_ok]; rfl⟩

theorem ExS.ret_none : ExS p s (.ret none) (.ret none) s := ⟨1, shift (K := 0) fun _ _ => rfl⟩

/-- Loop iteration: body ends normally (or by `continue`), the step runs,
    and the loop continues from the resulting state. -/
theorem ExS.loop_next {body step s1 s2 r s3} {o : Outcome}
    (hb : ExS p s body o s1) (ho : o = .normal ∨ o = .cont)
    (hs : ExS p s1 step .normal s2) (hl : ExS p s2 (.loop body step) r s3) :
    ExS p s (.loop body step) r s3 := by
  obtain ⟨K1, h1⟩ := hb
  obtain ⟨K2, h2⟩ := hs
  obtain ⟨K3, h3⟩ := hl
  exact ⟨max K1 (max K2 K3) + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), Res.bind_eq, Res.bind_ok]
    rcases ho with rfl | rfl <;>
      simp only [h2 n (by omega), h3 n (by omega), Res.bind_ok]⟩

theorem ExS.loop_brk {body step s1} (hb : ExS p s body .brk s1) :
    ExS p s (.loop body step) .normal s1 := by
  obtain ⟨K1, h1⟩ := hb
  exact ⟨K1 + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), Res.bind_eq, Res.bind_ok]; rfl⟩

theorem ExS.loop_ret {body step s1 v} (hb : ExS p s body (.ret v) s1) :
    ExS p s (.loop body step) (.ret v) s1 := by
  obtain ⟨K1, h1⟩ := hb
  exact ⟨K1 + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), Res.bind_eq, Res.bind_ok]; rfl⟩

/-- A loop terminates when an invariant is paired with a decreasing natural
    variant: positive variants admit one normal body/step iteration lowering
    the variant, and variant zero exits through `break`. This rule packages a
    finite sequence of `loop_next` applications and the final `loop_brk`. -/
theorem ExS.loop_decreasing {body step : Stmt} {P : Nat → State → Prop}
    {n : Nat} {s : State}
    (hinv : P n s)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2,
      ExS p s body .normal s1 ∧ ExS p s1 step .normal s2 ∧ P k s2)
    (hexit : ∀ s, P 0 s → ∃ s1, ExS p s body .brk s1) :
    ∃ s', ExS p s (.loop body step) .normal s' := by
  induction n generalizing s with
  | zero =>
    obtain ⟨s1, hb⟩ := hexit s hinv
    exact ⟨s1, ExS.loop_brk hb⟩
  | succ n ih =>
    obtain ⟨s1, s2, hb, hs, hnext⟩ := hstep n s hinv
    obtain ⟨s3, hl⟩ := ih hnext
    exact ⟨s3, ExS.loop_next hb (Or.inl rfl) hs hl⟩

/-- The decreasing-loop rule with an exit postcondition. The state satisfying
    the postcondition is the state produced by the final break. -/
theorem ExS.loop_decreasing_post {body step : Stmt} {P : Nat → State → Prop}
    {Q : State → Prop} {n : Nat} {s : State}
    (hinv : P n s)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2,
      ExS p s body .normal s1 ∧ ExS p s1 step .normal s2 ∧ P k s2)
    (hexit : ∀ s, P 0 s → ∃ s1, ExS p s body .brk s1 ∧ Q s1) :
    ∃ s', ExS p s (.loop body step) .normal s' ∧ Q s' := by
  induction n generalizing s with
  | zero =>
    obtain ⟨s1, hb, hq⟩ := hexit s hinv
    exact ⟨s1, ExS.loop_brk hb, hq⟩
  | succ n ih =>
    obtain ⟨s1, s2, hb, hs, hnext⟩ := hstep n s hinv
    obtain ⟨s3, hl, hq⟩ := ih hnext
    exact ⟨s3, ExS.loop_next hb (Or.inl rfl) hs hl, hq⟩

theorem ExS.call {f args vs fn o s'} (hargs : EvArgs p s args vs) (hf : p f = some fn)
    (hlen : fn.params.length = vs.length)
    (hbody : ExS p ⟨frameLocals fn.params vs, s.mem, s.ro⟩ fn.body o s')
    (ho : o = .normal ∨ o = .ret none) :
    ExS p s (.call none f args) .normal { s with mem := s'.mem } := by
  obtain ⟨K1, h1⟩ := hargs
  obtain ⟨K2, h2⟩ := hbody
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), Res.bind_eq, Res.bind_ok, hf, hlen, ite_true]
    rcases ho with rfl | rfl <;> simp only [h2 n (by omega), Res.bind_ok] <;> rfl⟩

theorem ExS.call_dst {d f args vs fn v s'} (hargs : EvArgs p s args vs) (hf : p f = some fn)
    (hlen : fn.params.length = vs.length)
    (hbody : ExS p ⟨frameLocals fn.params vs, s.mem, s.ro⟩ fn.body (.ret (some v)) s') :
    ExS p s (.call (some d) f args) .normal { s with mem := s'.mem, locals := s.locals.upd d v } := by
  obtain ⟨K1, h1⟩ := hargs
  obtain ⟨K2, h2⟩ := hbody
  exact ⟨max K1 K2 + 1, shift fun n hn => by
    simp only [execStmt, h1 n (by omega), Res.bind_eq, Res.bind_ok, hf, hlen, ite_true,
      h2 n (by omega)]
    rfl⟩

theorem ExS.seq_ex {a b s1 r} {P : State → Prop} (ha : ExS p s a .normal s1)
    (hb : ∃ s2, ExS p s1 b r s2 ∧ P s2) : ∃ s2, ExS p s (.seq a b) r s2 ∧ P s2 := by
  obtain ⟨s2, h, hp⟩ := hb
  exact ⟨s2, ExS.seq ha h, hp⟩

/-- Whole-function call from the outside. -/
theorem callFunc_of_ExS {f fn args m v s'} (hf : p f = some fn)
    (hlen : fn.params.length = args.length)
    (h : ExS p ⟨frameLocals fn.params args, m, false⟩ fn.body (.ret v) s') :
    ∃ K, ∀ n, K ≤ n → callFunc p n f args m = .ok (v, s'.mem) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n hn => ?_⟩
  simp only [callFunc, hf, hlen, ite_true, hK n hn]

/-- Whole-function call for a body that falls through normally. -/
theorem callFunc_of_ExS_normal {f fn args m s'} (hf : p f = some fn)
    (hlen : fn.params.length = args.length)
    (h : ExS p ⟨frameLocals fn.params args, m, false⟩ fn.body .normal s') :
    ∃ K, ∀ n, K ≤ n → callFunc p n f args m = .ok (none, s'.mem) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n hn => ?_⟩
  simp only [callFunc, hf, hlen, ite_true, hK n hn]

end

end Obj.C

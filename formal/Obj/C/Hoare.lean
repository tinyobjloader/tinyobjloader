/-
  A total-correctness Hoare logic over MiniC, derived from `ExS`/`EvE`.

  `Triple p P st Q` : from every state satisfying `P`, `st` terminates
  without undefined behaviour in an outcome/state satisfying `Q`.

  Soundness is by construction: `Triple` is *defined* via the executable
  semantics, and every rule below is a lemma.
-/
import Obj.C.Logic

namespace Obj.C

def Triple (p : Prog) (P : State → Prop) (st : Stmt) (Q : Outcome → State → Prop) : Prop :=
  ∀ s, P s → ∃ o s', ExS p s st o s' ∧ Q o s'

namespace Triple
variable {p : Prog}

theorem conseq {P P' : State → Prop} {Q Q' : Outcome → State → Prop} {st}
    (h : Triple p P st Q) (hp : ∀ s, P' s → P s) (hq : ∀ o s, Q o s → Q' o s) :
    Triple p P' st Q' := by
  intro s hs
  obtain ⟨o, s', h1, h2⟩ := h s (hp s hs)
  exact ⟨o, s', h1, hq _ _ h2⟩

theorem skip {Q : Outcome → State → Prop} : Triple p (Q .normal) .skip Q :=
  fun s hs => ⟨_, _, ExS.skip, hs⟩

theorem set {P : State → Prop} {Q : Outcome → State → Prop} {i e}
    (h : ∀ s, P s → ∃ v, EvE p s e v ∧ Q .normal { s with locals := s.locals.upd i v }) :
    Triple p P (.set i e) Q := by
  intro s hs
  obtain ⟨v, hv, hq⟩ := h s hs
  exact ⟨_, _, ExS.set hv, hq⟩

theorem store {P : State → Prop} {Q : Outcome → State → Prop} {ty a e}
    (h : ∀ s, P s → ∃ pa v m', EvE p s a pa ∧ EvE p s e v ∧ s.ro = false ∧
      C.store s.mem ty pa v = .ok m' ∧ Q .normal { s with mem := m' }) :
    Triple p P (.store ty a e) Q := by
  intro s hs
  obtain ⟨pa, v, m', ha, he, hro, hm, hq⟩ := h s hs
  exact ⟨_, _, ExS.store ha he hro hm, hq⟩

/-- Sequencing: `R` is the intermediate assertion for normal completion of
    `a`; abrupt completion of `a` must already satisfy `Q`. -/
theorem seq {P R : State → Prop} {Q : Outcome → State → Prop} {a b}
    (ha : Triple p P a (fun o s => (o = .normal ∧ R s) ∨
      (o = .brk ∧ Q .brk s) ∨ (∃ v, o = .ret v ∧ Q (.ret v) s)))
    (hb : Triple p R b Q) : Triple p P (.seq a b) Q := by
  intro s hs
  obtain ⟨o, s1, h1, h2⟩ := ha s hs
  rcases h2 with ⟨rfl, hr⟩ | ⟨rfl, hq⟩ | ⟨v, rfl, hq⟩
  · obtain ⟨o2, s2, h3, h4⟩ := hb s1 hr
    exact ⟨o2, s2, ExS.seq h1 h3, h4⟩
  · exact ⟨_, _, ExS.seq_brk h1, hq⟩
  · exact ⟨_, _, ExS.seq_ret h1, hq⟩

theorem ite {P Pa Pb : State → Prop} {Q : Outcome → State → Prop} {c a b}
    (hc : ∀ s, P s → ∃ vc bc, EvE p s c vc ∧ truthy vc = .ok bc ∧
      (bc = true → Pa s) ∧ (bc = false → Pb s))
    (ha : Triple p Pa a Q) (hb : Triple p Pb b Q) : Triple p P (.ite c a b) Q := by
  intro s hs
  obtain ⟨vc, bc, hv, ht, hpa, hpb⟩ := hc s hs
  cases bc
  · obtain ⟨o, s', h1, h2⟩ := hb s (hpb rfl)
    exact ⟨o, s', ExS.ite hv ht (by simpa using h1), h2⟩
  · obtain ⟨o, s', h1, h2⟩ := ha s (hpa rfl)
    exact ⟨o, s', ExS.ite hv ht (by simpa using h1), h2⟩

theorem ret {P : State → Prop} {Q : Outcome → State → Prop} {e}
    (h : ∀ s, P s → ∃ v, EvE p s e v ∧ Q (.ret (some v)) s) :
    Triple p P (.ret (some e)) Q := by
  intro s hs
  obtain ⟨v, hv, hq⟩ := h s hs
  exact ⟨_, _, ExS.ret hv, hq⟩

theorem brk {Q : Outcome → State → Prop} : Triple p (Q .brk) .brk Q :=
  fun s hs => ⟨_, _, ExS.brk, hs⟩

/-- Loops: `Inv` is the invariant, `μ` a measure decreasing on every
    iteration that does not leave the loop. -/
theorem loop {Inv : State → Prop} {μ : State → Nat} {Q : Outcome → State → Prop} {body step}
    (hbody : ∀ k, Triple p (fun s => Inv s ∧ μ s = k) body (fun o s =>
      ((o = .normal ∨ o = .cont) ∧ Inv s ∧ μ s < k) ∨
      (o = .brk ∧ Q .normal s) ∨ (∃ v, o = .ret v ∧ Q (.ret v) s)))
    (hstep : ∀ s, Inv s → ExS p s step .normal s) :
    Triple p Inv (.loop body step) Q := by
  intro s hs
  generalize hk : μ s = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    obtain ⟨o, s1, h1, h2⟩ := hbody k s ⟨hs, hk⟩
    rcases h2 with ⟨ho, hinv, hlt⟩ | ⟨rfl, hq⟩ | ⟨v, rfl, hq⟩
    · obtain ⟨o', s', h3, h4⟩ := ih _ hlt s1 hinv rfl
      exact ⟨o', s', ExS.loop_next h1 ho (hstep s1 hinv) h3, h4⟩
    · exact ⟨_, _, ExS.loop_brk h1, hq⟩
    · exact ⟨_, _, ExS.loop_ret h1, hq⟩

/-- Statement-level call with result assignment, from a callee triple. -/
theorem call_dst {P : State → Prop} {Q : Outcome → State → Prop} {d f args fn}
    (hf : p f = some fn)
    (h : ∀ s, P s → ∃ vs v s', EvArgs p s args vs ∧ fn.params.length = vs.length ∧
      ExS p ⟨frameLocals fn.params vs, s.mem, s.ro⟩ fn.body (.ret (some v)) s' ∧
      Q .normal { s with mem := s'.mem, locals := s.locals.upd d v }) :
    Triple p P (.call (some d) f args) Q := by
  intro s hs
  obtain ⟨vs, v, s', ha, hl, hb, hq⟩ := h s hs
  obtain ⟨K1, h1⟩ := ha
  obtain ⟨K2, h2⟩ := hb
  refine ⟨_, _, ⟨max K1 K2 + 1, fun n hn => ?_⟩, hq⟩
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [execStmt, h1 n (by omega), Res.bind_eq, Res.bind_ok, hf, hl, ite_true,
    h2 n (by omega)]
  rfl

theorem call_none {P : State → Prop} {Q : Outcome → State → Prop} {f args fn}
    (hf : p f = some fn)
    (h : ∀ s, P s → ∃ vs o s', EvArgs p s args vs ∧ fn.params.length = vs.length ∧
      ExS p ⟨frameLocals fn.params vs, s.mem, s.ro⟩ fn.body o s' ∧
      (o = .normal ∨ o = .ret none) ∧ Q .normal { s with mem := s'.mem }) :
    Triple p P (.call none f args) Q := by
  intro s hs
  obtain ⟨vs, o, s', ha, hl, hb, ho, hq⟩ := h s hs
  exact ⟨_, _, ExS.call ha hf hl hb ho, hq⟩

end Triple

/-- `EvE` from a fuel-shifted evaluation equation (for `simp`-driven proofs). -/
theorem EvE.of_eq {p : Prog} {s : State} {e : Expr} {v : Val} (K : Nat)
    (h : ∀ n, evalExpr p (n + K) s e = .ok v) : EvE p s e v :=
  ⟨K, fun n hn => by obtain ⟨m, rfl⟩ : ∃ m, n = m + K := ⟨n - K, by omega⟩; exact h m⟩

theorem ExS.of_eq {p : Prog} {s : State} {st : Stmt} {o : Outcome} {s' : State} (K : Nat)
    (h : ∀ n, execStmt p (n + K) s st = .ok (o, s')) : ExS p s st o s' :=
  ⟨K, fun n hn => by obtain ⟨m, rfl⟩ : ∃ m, n = m + K := ⟨n - K, by omega⟩; exact h m⟩

theorem EvArgs.of_eq {p : Prog} {s : State} {es : List Expr} {vs : List Val} (K : Nat)
    (h : ∀ n, evalArgs p (n + K) s es = .ok vs) : EvArgs p s es vs :=
  ⟨K, fun n hn => by obtain ⟨m, rfl⟩ : ∃ m, n = m + K := ⟨n - K, by omega⟩; exact h m⟩

end Obj.C

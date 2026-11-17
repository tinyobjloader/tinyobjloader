import TobjSubd.Model

/-!
# Lexical lemmas for the canonical round trip

Splitting printed text back into lines and tokens, and parsing printed numbers.
-/
namespace TobjSubd

/-! ## Lines and tokens -/

theorem splitOn_append (sep : Char) (l r : S) (hl : ∀ c ∈ l, c ≠ sep) :
    splitOn sep (l ++ sep :: r) = l :: splitOn sep r := by
  induction l with
  | nil => simp [splitOn]
  | cons c l ih =>
    have hc : (c == sep) = false := by simpa using hl c (by simp)
    simp only [List.cons_append, splitOn, hc, Bool.false_eq_true, ite_false]
    rw [ih (fun x hx => hl x (by simp [hx]))]

theorem splitOn_noSep (sep : Char) (l : S) (hl : ∀ c ∈ l, c ≠ sep) : splitOn sep l = [l] := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : (c == sep) = false := by simpa using hl c (by simp)
    simp only [splitOn, hc, Bool.false_eq_true, ite_false]
    rw [ih (fun x hx => hl x (by simp [hx]))]

theorem splitOn_lines (sep : Char) (ls : List S) (h : ∀ l ∈ ls, ∀ c ∈ l, c ≠ sep) :
    splitOn sep (ls.flatMap (· ++ [sep])) = ls ++ [[]] := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append]
    rw [splitOn_append sep l _ (h l (by simp)), ih (fun x hx => h x (by simp [hx]))]

theorem splitBlank_append (l r : S) (hl : ∀ c ∈ l, isBlank c = false) :
    splitBlank (l ++ ' ' :: r) = l :: splitBlank r := by
  induction l with
  | nil => simp [splitBlank, isBlank]
  | cons c l ih =>
    simp only [List.cons_append, splitBlank, hl c (by simp), Bool.false_eq_true, ite_false]
    rw [ih (fun x hx => hl x (by simp [hx]))]

theorem splitBlank_noBlank (l : S) (hl : ∀ c ∈ l, isBlank c = false) : splitBlank l = [l] := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [splitBlank, hl c (by simp), Bool.false_eq_true, ite_false]
    rw [ih (fun x hx => hl x (by simp [hx]))]

/-- A token as printed: non-empty, and free of blanks and line-break characters. -/
def GoodTok (w : S) : Prop := w ≠ [] ∧ ∀ c ∈ w, isBlank c = false ∧ c ≠ '\n' ∧ c ≠ '\r'

theorem splitBlank_joinSp : ∀ (ts : List S), ts ≠ [] → (∀ w ∈ ts, GoodTok w) →
    splitBlank (joinSp ts) = ts
  | [], h, _ => absurd rfl h
  | [w], _, h => by
    simp only [joinSp]; exact splitBlank_noBlank w (fun c hc => ((h w (by simp)).2 c hc).1)
  | w :: v :: ws, _, h => by
    simp only [joinSp]
    rw [splitBlank_append w _ (fun c hc => ((h w (by simp)).2 c hc).1)]
    have := splitBlank_joinSp (v :: ws) (by simp) (fun x hx => h x (by simp_all))
    cases ws with
    | nil => simp only [joinSp] at this ⊢; rw [this]
    | cons u us => rw [this]

theorem lineTokens_joinSp (ts : List S) (hne : ts ≠ []) (h : ∀ w ∈ ts, GoodTok w) :
    lineTokens (joinSp ts) = ts := by
  unfold lineTokens
  rw [splitBlank_joinSp ts hne h, List.filter_eq_self]
  intro w hw
  have := (h w hw).1
  cases w with
  | nil => exact absurd rfl this
  | cons => rfl

theorem mem_joinSp {c : Char} : ∀ {ts : List S}, c ∈ joinSp ts → c = ' ' ∨ ∃ w ∈ ts, c ∈ w
  | [], h => by simp [joinSp] at h
  | [w], h => by simp only [joinSp] at h; exact Or.inr ⟨w, by simp, h⟩
  | w :: v :: ws, h => by
    simp only [joinSp, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inr ⟨w, by simp, h⟩
    · exact Or.inl h
    · rcases mem_joinSp (ts := v :: ws) (by simpa [joinSp] using h) with h | ⟨x, hx, hc⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hc⟩

theorem joinSp_noBreak (ts : List S) (h : ∀ w ∈ ts, GoodTok w) :
    ∀ c ∈ joinSp ts, c ≠ '\n' ∧ c ≠ '\r' := by
  intro c hc
  rcases mem_joinSp hc with rfl | ⟨w, hw, hcw⟩
  · decide
  · exact ⟨((h w hw).2 c hcw).2.1, ((h w hw).2 c hcw).2.2⟩

theorem dropCR_of_noCR (l : S) (h : ∀ c ∈ l, c ≠ '\r') : dropCR l = l := by
  unfold dropCR
  cases hl : l.getLast? with
  | none => simp
  | some c =>
    have := h c (List.mem_of_getLast? hl)
    simp [this]

/-! ## Numbers -/

theorem digitChar_val (k : Nat) (hk : k < 10) :
    (digitChar k).toNat - '0'.toNat = k ∧ isDigit (digitChar k) = true := by
  match k, hk with
  | 0, _ => decide | 1, _ => decide | 2, _ => decide | 3, _ => decide | 4, _ => decide
  | 5, _ => decide | 6, _ => decide | 7, _ => decide | 8, _ => decide | 9, _ => decide

theorem digitsVal_append (l : S) (d : Char) :
    digitsVal (l ++ [d]) = digitsVal l * 10 + (d.toNat - '0'.toNat) := by
  simp [digitsVal, List.foldl_append]

theorem nat_spec (n : Nat) :
    nat n ≠ [] ∧ (∀ c ∈ nat n, isDigit c = true) ∧ digitsVal (nat n) = n := by
    rw [nat]
    split
    · rename_i h
      have := digitChar_val n h
      refine ⟨by simp, by simpa using this.2, ?_⟩
      show digitsVal [digitChar n] = n
      simp only [digitsVal, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
      exact this.1
    · rename_i h
      have ⟨_, hd, hv⟩ := nat_spec (n / 10)
      have := digitChar_val (n % 10) (by omega)
      refine ⟨by simp, ?_, ?_⟩
      · intro c hc
        simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact hd c hc
        · exact this.2
      · rw [digitsVal_append, hv, this.1]; omega
termination_by n
decreasing_by omega

theorem isDigit_char {c : Char} (h : isDigit c = true) :
    isBlank c = false ∧ c ≠ '\n' ∧ c ≠ '\r' ∧ c ≠ '/' ∧ c ≠ '-' ∧ c ≠ '+' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hb : isBlank c
    · rfl
    · simp only [isBlank, Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with rfl | rfl <;> simp_all [isDigit]
  all_goals (rintro rfl; simp [isDigit] at h)

theorem nat_good (n : Nat) : GoodTok (nat n) := by
  have ⟨hne, hd, _⟩ := nat_spec n
  exact ⟨hne, fun c hc => let h := isDigit_char (hd c hc); ⟨h.1, h.2.1, h.2.2.1⟩⟩

theorem parseInt?_nat (n : Nat) : parseInt? (nat n) = some (n : Int) := by
  have ⟨hne, hd, hv⟩ := nat_spec n
  unfold parseInt?
  obtain ⟨c, r, hcr⟩ : ∃ c r, nat n = c :: r := by
    cases h : nat n with
    | nil => exact absurd h hne
    | cons c r => exact ⟨c, r, rfl⟩
  have hc := isDigit_char (hd c (by simp [hcr]))
  have hall : (c :: r).all isDigit = true := by
    rw [← hcr]; exact List.all_eq_true.mpr hd
  have hv' : digitsVal (c :: r) = n := hcr ▸ hv
  rw [hcr]
  split <;> simp_all [isDigit]
  all_goals (rename_i heq; obtain ⟨-, rfl⟩ := heq; simp_all)

theorem count?_nat (n : Nat) (h : n ≤ maxCount) : count? (nat n) = some n := by
  have ⟨hne, hd, hv⟩ := nat_spec n
  unfold count?
  have he : (nat n).isEmpty = false := by simpa [List.isEmpty_iff] using hne
  have ha : (nat n).all isDigit = true := List.all_eq_true.mpr hd
  simp [he, ha, hv, h]

theorem parseCounts?_hole (n : Nat) (h : n ≤ maxCount) :
    parseCounts? (nat n ++ "/0/0".toList) = some (n, 0, 0) := by
  unfold parseCounts?
  have hs : splitOn '/' (nat n ++ "/0/0".toList) = [nat n, ['0'], ['0']] := by
    show splitOn '/' (nat n ++ '/' :: "0/0".toList) = _
    rw [splitOn_append _ _ _ (fun c hc => (isDigit_char ((nat_spec n).2.1 c hc)).2.2.2.1)]
    rfl
  rw [hs]
  simp only [count?_nat n h]
  rfl

theorem nat_hole_good (n : Nat) : GoodTok (nat n ++ "/0/0".toList) := by
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · exact (nat_good n).2 c hc
  · have key : ∀ d ∈ "/0/0".toList, isBlank d = false ∧ d ≠ '\n' ∧ d ≠ '\r' := by decide
    exact key c hc

/-! ## Decimals -/

theorem isDecChar_good {c : Char} (h : isDecChar c = true) :
    isBlank c = false ∧ c ≠ '\n' ∧ c ≠ '\r' := by
  unfold isDecChar at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((h | rfl) | rfl) | rfl) | rfl) | rfl
  · have := isDigit_char h; exact ⟨this.1, this.2.1, this.2.2.1⟩
  all_goals decide

theorem decimal_good {v : S} (h : isDecimal v = true) : GoodTok v := by
  unfold isDecimal at h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true] at h
  obtain ⟨⟨hne, hall⟩, _⟩ := h
  exact ⟨by simpa [List.isEmpty_iff] using hne, fun c hc => isDecChar_good (hall c hc)⟩

theorem sharp_decimal {v : S} (h : isDecimal v = true) : isDecimal (sharp v) = true := by
  unfold sharp
  split
  · decide
  · exact h

theorem sharp_idem (v : S) : sharp (sharp v) = sharp v := by
  unfold sharp
  split
  · decide
  · rename_i h; simp [h]

end TobjSubd

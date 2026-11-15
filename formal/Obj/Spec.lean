/-
  Specification of OBJ vertex-index resolution (the semantics the C loader
  implements in `fix_index`; see the OBJ format: `f 1 2 3`, and relative
  indices `f -1 -2 -3` that count back from the most recently declared
  vertex).

  This file is pure Lean: it does not mention the C source or MiniC.
  `Obj/C/Proofs/FixIndexRefines.lean` proves that the translated
  `fix_index_f` function refines these definitions.
-/
namespace Obj

/-- Resolve an OBJ index `idx` against `n` previously declared elements.
    Positive `idx` is 1-based and converted to `idx - 1` without checking
    it against `n`, matching `fix_index` (the caller validates array access).
    Negative `idx` counts back from the end and is invalid before element
    zero; zero is invalid. Returns the stored 0-based index. -/
def resolveIndex (idx : Int) (n : Nat) : Option Int :=
  if 0 < idx then some (idx - 1)
  else if idx = 0 then none
  else if 0 ≤ (n : Int) + idx then some ((n : Int) + idx)
  else none

/-- The value stored by the loader: the resolved index, or `-1` when invalid. -/
def storedIndex (idx : Int) (n : Nat) : Int := (resolveIndex idx n).getD (-1)

/-- ASCII space predicate used by the C scanner (space and horizontal tab). -/
def scanSpace (b : Nat) : Bool := b == 32 || b == 9

/-- ASCII decimal digit predicate for scanner input bytes. -/
def scanDigit (b : Nat) : Bool := decide (48 ≤ b ∧ b ≤ 57)

/-- One saturating decimal accumulation step. -/
def scanIntStep (acc b : Nat) : Nat := min 2147483647 (acc * 10 + (b - 48))

/-- One iteration of the C scanner's `(v, sat)` update. Once saturation has
    occurred, later digits leave the capped value unchanged. -/
def scanCLoopStep (state : Nat × Bool) (b : Nat) : Nat × Bool :=
  if state.2 then (state.1, true)
  else
    let candidate := state.1 * 10 + (b - 48)
    if candidate > 2147483647 then (2147483647, true)
    else (candidate, false)

/-- The C loop's saturation flag implies its accumulator is already capped. -/
theorem scanCLoopStep_saturated (v b : Nat) (sat : Bool)
    (hinv : sat = true → v = 2147483647) :
    (scanCLoopStep (v, sat) b).2 = true →
      (scanCLoopStep (v, sat) b).1 = 2147483647 := by
  by_cases hs : sat = true
  · have hc : 2147483647 ≤ 2147483647 * 10 + (b - 48) := by omega
    simp [scanCLoopStep, hs, hinv hs]
  · have hsfalse : sat = false := Bool.eq_false_iff.mpr hs
    simp only [scanCLoopStep, hsfalse]
    by_cases hc : v * 10 + (b - 48) > 2147483647
    · simp [hc]
    · simp [hc]

/-- Under the saturation invariant, a C update has the same accumulator
    value as one pure saturating decimal step. -/
theorem scanCLoopStep_value (v b : Nat) (sat : Bool)
    (hinv : sat = true → v = 2147483647) :
    (scanCLoopStep (v, sat) b).1 = scanIntStep v b := by
  by_cases hs : sat = true
  · have hc : 2147483647 ≤ 2147483647 * 10 + (b - 48) := by omega
    simp [scanCLoopStep, hs, hinv hs, scanIntStep, Nat.min_eq_left hc]
  · have hsfalse : sat = false := Bool.eq_false_iff.mpr hs
    simp only [scanCLoopStep, hsfalse]
    let candidate := v * 10 + (b - 48)
    by_cases hgt : candidate > 2147483647
    · have hbound : 2147483647 ≤ v * 10 + (b - 48) := by
        dsimp [candidate] at hgt
        omega
      simp [candidate, hgt, scanIntStep, Nat.min_eq_left hbound]
    · simp [candidate, hgt, scanIntStep]
      omega

/-- Pure fold used to state the value accumulated over a digit prefix. -/
def scanIntFold (bytes : List Nat) (acc : Nat) : Nat :=
  (bytes.takeWhile scanDigit).foldl scanIntStep acc

/-- The pure saturating decimal fold never exceeds `INT_MAX` when started
    from an in-range accumulator. -/
theorem scanIntFold_le_cap (bytes : List Nat) (acc : Nat)
    (hacc : acc ≤ 2147483647) : scanIntFold bytes acc ≤ 2147483647 := by
  induction bytes generalizing acc with
  | nil => simpa [scanIntFold] using hacc
  | cons b bs ih =>
      unfold scanIntFold
      simp only [List.takeWhile_cons]
      split
      · rename_i hdigit
        simp only [List.foldl_cons]
        apply ih
        simp [scanIntStep]
        omega
      · exact hacc

/-- Fold C-style scanner updates over the maximal digit prefix. -/
def scanCLoopFold (bytes : List Nat) (state : Nat × Bool) : Nat × Bool :=
  (bytes.takeWhile scanDigit).foldl scanCLoopStep state

/-- After any scanned prefix, a true saturation flag still implies the
    accumulator is exactly capped. -/
theorem scanCLoopFold_saturated (bytes : List Nat) (v : Nat) (sat : Bool)
    (hinv : sat = true → v = 2147483647) :
    (scanCLoopFold bytes (v, sat)).2 = true →
      (scanCLoopFold bytes (v, sat)).1 = 2147483647 := by
  induction bytes generalizing v sat with
  | nil => simpa [scanCLoopFold] using hinv
  | cons b bs ih =>
    simp only [scanCLoopFold, List.takeWhile_cons]
    split
    · let state' := scanCLoopStep (v, sat) b
      have hstep := scanCLoopStep_saturated v b sat hinv
      have hinv' : state'.2 = true → state'.1 = 2147483647 := by
        simpa [state'] using hstep
      simpa [state', scanCLoopFold] using ih state'.1 state'.2 hinv'
    · simp_all [scanCLoopFold]

/-- The C-style `(v, sat)` fold computes the same capped magnitude as the
    pure decimal fold. -/
theorem scanCLoopFold_value (bytes : List Nat) (v : Nat) (sat : Bool)
    (hinv : sat = true → v = 2147483647) :
    (scanCLoopFold bytes (v, sat)).1 = scanIntFold bytes v := by
  induction bytes generalizing v sat with
  | nil => rfl
  | cons b bs ih =>
    by_cases hd : scanDigit b = true
    · let state' := scanCLoopStep (v, sat) b
      have hstep := scanCLoopStep_value v b sat hinv
      have hinv' : state'.2 = true → state'.1 = 2147483647 := by
        simpa [state'] using scanCLoopStep_saturated v b sat hinv
      have hval : state'.1 = scanIntStep v b := by
        simpa [state'] using hstep
      have ih' := ih state'.1 state'.2 hinv'
      rw [hval] at ih'
      have hstate : scanCLoopStep (v, sat) b =
          (scanIntStep v b, (scanCLoopStep (v, sat) b).2) := Prod.ext hstep rfl
      simp only [scanCLoopFold, scanIntFold, List.takeWhile_cons, hd, ite_true,
        List.foldl_cons]
      rw [hstate]
      exact ih'
    · simp [scanCLoopFold, scanIntFold, hd]

/-- Starting the C-style fold at zero keeps its accumulator within the cap. -/
theorem scanCLoopFold_zero_le_cap (bytes : List Nat) :
    (scanCLoopFold bytes (0, false)).1 ≤ 2147483647 := by
  rw [scanCLoopFold_value bytes 0 false (by simp)]
  exact scanIntFold_le_cap bytes 0 (by omega)

/-- Scan decimal digits, saturating the magnitude at `INT_MAX` exactly as
    `tobj_scan_int` does. The returned count is the number of consumed bytes. -/
def scanDigits : List Nat → Nat → Nat × Nat
  | [], acc => (0, acc)
  | b :: bs, acc =>
      if 48 ≤ b ∧ b ≤ 57 then
        let (n, v) := scanDigits bs (min 2147483647 (acc * 10 + (b - 48)))
        (n + 1, v)
      else (0, acc)

/-- One scanner-loop step on a digit consumes it and updates the
    saturating decimal accumulator. -/
theorem scanDigits_cons_digit (b : Nat) (bs : List Nat) (acc : Nat)
    (h : 48 ≤ b ∧ b ≤ 57) :
    scanDigits (b :: bs) acc =
      let (n, v) := scanDigits bs (min 2147483647 (acc * 10 + (b - 48)))
      (n + 1, v) := by
  simp [scanDigits, h]

/-- A non-digit is the loop exit condition and is not consumed. -/
theorem scanDigits_cons_nondigit (b : Nat) (bs : List Nat) (acc : Nat)
    (h : ¬ (48 ≤ b ∧ b ≤ 57)) : scanDigits (b :: bs) acc = (0, acc) := by
  simp [scanDigits, h]

@[simp] theorem scanDigits_empty (acc : Nat) : scanDigits [] acc = (0, acc) := rfl

/-- The scanner consumes no more bytes than the supplied suffix contains. -/
theorem scanDigits_count_le (bytes : List Nat) (acc : Nat) :
    (scanDigits bytes acc).1 ≤ bytes.length := by
  induction bytes generalizing acc with
  | nil => simp [scanDigits]
  | cons b bs ih =>
    simp only [scanDigits]
    split
    · rename_i hdigit
      simp only [List.length_cons]
      have h := ih (min 2147483647 (acc * 10 + (b - 48)))
      omega
    · simp [List.length_cons]

/-- The number of consumed bytes is exactly the maximal leading run of digits. -/
theorem scanDigits_count_exact (bytes : List Nat) (acc : Nat) :
    (scanDigits bytes acc).1 = (bytes.takeWhile scanDigit).length := by
  induction bytes generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [scanDigits, List.takeWhile_cons, scanDigit]
    split
    · simp_all
    · have hnot : ¬ (48 ≤ b ∧ b ≤ 57) := by omega
      simp [hnot]

/-- The resulting magnitude equals a saturating decimal fold over precisely
    the maximal leading digit prefix. -/
theorem scanDigits_value_exact (bytes : List Nat) (acc : Nat) :
    (scanDigits bytes acc).2 = scanIntFold bytes acc := by
  induction bytes generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [scanDigits, List.takeWhile_cons, scanDigit, scanIntFold]
    split
    · simp_all [scanIntFold, scanIntStep, List.foldl_cons]
    · have hnot : ¬ (48 ≤ b ∧ b ≤ 57) := by omega
      simp [hnot]

/-- Starting from `(0, false)`, the abstract C-style accumulation loop
    produces the same magnitude as the recursive digit scanner. -/
theorem scanCLoopFold_scanDigits (bytes : List Nat) :
    (scanCLoopFold bytes (0, false)).1 = (scanDigits bytes 0).2 := by
  rw [scanCLoopFold_value bytes 0 false (by simp)]
  exact (scanDigits_value_exact bytes 0).symm

/-- Every accumulator produced by the scanner is at most `INT_MAX`. -/
theorem scanDigits_value_le_max (bytes : List Nat) (acc : Nat)
    (hacc : acc ≤ 2147483647) :
    (scanDigits bytes acc).2 ≤ 2147483647 := by
  induction bytes generalizing acc with
  | nil => simpa [scanDigits] using hacc
  | cons b bs ih =>
    simp only [scanDigits]
    split
    · apply ih
      exact Nat.min_le_left _ _
    · exact hacc

/-- Apply the optional minus sign after scanning a saturated magnitude. -/
def scanIntSignedValue (negative : Bool) (digits : List Nat) : Int :=
  if negative then -((scanDigits digits 0).2 : Int) else (scanDigits digits 0).2

/-- The signed scanner result stays within `[-INT_MAX, INT_MAX]`; the C
    implementation saturates magnitude before applying the sign. -/
theorem scanIntSignedValue_range (negative : Bool) (digits : List Nat) :
    -2147483647 ≤ scanIntSignedValue negative digits ∧
      scanIntSignedValue negative digits ≤ 2147483647 := by
  have hm := scanDigits_value_le_max digits 0 (by omega)
  cases negative <;> simp [scanIntSignedValue] <;> omega

/-- Parse the digit suffix after leading whitespace and an optional sign have
    been handled. `failureCursor` preserves C's rule that a lone sign is not
    committed to the caller's cursor. -/
def scanIntDigits (digits : List Nat) (negative : Bool)
    (digitStart failureCursor : Nat) : Bool × Int × Nat :=
  match digits with
  | [] => (false, 0, failureCursor)
  | b :: _ =>
    if scanDigit b then
      let (count, _) := scanDigits digits 0
      (true, scanIntSignedValue negative digits, digitStart + count)
    else (false, 0, failureCursor)

@[simp] theorem scanIntDigits_empty (negative : Bool)
    (digitStart failureCursor : Nat) :
    scanIntDigits [] negative digitStart failureCursor = (false, 0, failureCursor) := rfl

/-- A non-digit at the first byte fails without committing a possible sign. -/
theorem scanIntDigits_nondigit (b : Nat) (bs : List Nat) (negative : Bool)
    (digitStart failureCursor : Nat) (h : scanDigit b = false) :
    scanIntDigits (b :: bs) negative digitStart failureCursor =
      (false, 0, failureCursor) := by
  simp [scanIntDigits, h]

/-- Any suffix-helper failure stores zero and preserves its pre-sign cursor. -/
theorem scanIntDigits_failure_contract (digits : List Nat) (negative : Bool)
    (digitStart failureCursor : Nat) {value : Int} {cursor : Nat}
    (h : scanIntDigits digits negative digitStart failureCursor =
      (false, value, cursor)) : value = 0 ∧ cursor = failureCursor := by
  cases digits with
  | nil =>
    simp [scanIntDigits] at h
    exact ⟨h.1.symm, h.2.symm⟩
  | cons b bs =>
    by_cases hd : scanDigit b
    · simp [scanIntDigits, hd] at h
    · simp [scanIntDigits, hd] at h
      exact ⟨h.1.symm, h.2.symm⟩

/-- Every successful parse of a digit suffix returns an in-range signed int. -/
theorem scanIntDigits_success_range (digits : List Nat) (negative : Bool)
    (digitStart failureCursor : Nat) {value : Int} {cursor : Nat}
    (h : scanIntDigits digits negative digitStart failureCursor =
      (true, value, cursor)) :
    -2147483647 ≤ value ∧ value ≤ 2147483647 := by
  cases digits with
  | nil => simp [scanIntDigits] at h
  | cons b bs =>
    simp only [scanIntDigits] at h
    split at h
    · simp only [Prod.mk.injEq] at h
      rcases h with ⟨_, hv, _⟩
      subst value
      exact scanIntSignedValue_range negative (b :: bs)
    · simp at h

/-- A successful suffix parse returns the signed saturating decimal fold. -/
theorem scanIntDigits_success_value (digits : List Nat) (negative : Bool)
    (digitStart failureCursor : Nat) {value : Int} {cursor : Nat}
    (h : scanIntDigits digits negative digitStart failureCursor =
      (true, value, cursor)) :
    value = (if negative then -(scanIntFold digits 0 : Int) else scanIntFold digits 0) := by
  cases digits with
  | nil => simp [scanIntDigits] at h
  | cons b bs =>
    simp only [scanIntDigits] at h
    split at h
    · simp only [Prod.mk.injEq] at h
      rcases h with ⟨_, hv, _⟩
      calc
        value = scanIntSignedValue negative (b :: bs) := hv.symm
        _ = (if negative then -(scanIntFold (b :: bs) 0 : Int)
             else scanIntFold (b :: bs) 0) := by
          cases negative <;> simp [scanIntSignedValue, scanDigits_value_exact]
    · simp at h

/-- On success, the digit-suffix helper advances past exactly the maximal
    leading run of digits. -/
theorem scanIntDigits_success_cursor (digits : List Nat) (negative : Bool)
    (digitStart failureCursor : Nat) {value : Int} {cursor : Nat}
    (h : scanIntDigits digits negative digitStart failureCursor =
      (true, value, cursor)) :
    cursor = digitStart + (digits.takeWhile scanDigit).length := by
  cases digits with
  | nil => simp [scanIntDigits] at h
  | cons b bs =>
    simp only [scanIntDigits] at h
    split at h
    · simp only [Prod.mk.injEq] at h
      rcases h with ⟨_, _, hc⟩
      subst cursor
      rw [scanDigits_count_exact]
    · simp at h

/-- Result of scanning from a byte offset: success, signed value, and cursor.
    On failure the cursor is after leading spaces/tabs, but a lone sign is not
    consumed. On success the cursor is after all decimal digits. -/
def scanInt (bytes : List Nat) (pos : Nat) : Bool × Int × Nat :=
  let rest := bytes.drop pos
  let spaces := rest.takeWhile scanSpace
  let afterSpace := rest.drop spaces.length
  let hasSign := afterSpace.head? == some 43 || afterSpace.head? == some 45
  let negative := afterSpace.head? == some 45
  let digits := if hasSign then afterSpace.drop 1 else afterSpace
  let digitStart := pos + spaces.length + (if hasSign then 1 else 0)
  scanIntDigits digits negative digitStart (pos + spaces.length)

/-- Whole-scanner success preserves the signed integer range established by
    the digit-suffix parser. -/
theorem scanInt_success_value_range (bytes : List Nat) (pos : Nat)
    {value : Int} {cursor : Nat}
    (h : scanInt bytes pos = (true, value, cursor)) :
    -2147483647 ≤ value ∧ value ≤ 2147483647 := by
  exact scanIntDigits_success_range _ _ _ _ h

/-- Whole-scanner success returns the signed saturating fold of its digit
    suffix. -/
theorem scanInt_success_value_fold (bytes : List Nat) (pos : Nat)
    {value : Int} {cursor : Nat}
    (h : scanInt bytes pos = (true, value, cursor)) :
    let rest := bytes.drop pos
    let spaces := rest.takeWhile scanSpace
    let afterSpace := rest.drop spaces.length
    let negative := afterSpace.head? == some 45
    let hasSign := afterSpace.head? == some 43 || afterSpace.head? == some 45
    let digits := if hasSign then afterSpace.drop 1 else afterSpace
    value = (if negative then -(scanIntFold digits 0 : Int) else scanIntFold digits 0) := by
  exact scanIntDigits_success_value _ _ _ _ h

/-- Whole-scanner success advances over leading whitespace, an optional sign,
    and exactly the maximal leading digit prefix. -/
theorem scanInt_success_cursor (bytes : List Nat) (pos : Nat)
    {value : Int} {cursor : Nat}
    (h : scanInt bytes pos = (true, value, cursor)) :
    let rest := bytes.drop pos
    let spaces := rest.takeWhile scanSpace
    let afterSpace := rest.drop spaces.length
    let hasSign := afterSpace.head? == some 43 || afterSpace.head? == some 45
    let digits := if hasSign then afterSpace.drop 1 else afterSpace
    cursor = pos + spaces.length + (if hasSign then 1 else 0) +
      (digits.takeWhile scanDigit).length := by
  exact scanIntDigits_success_cursor _ _ _ _ h

/-- A failed whole scan stores zero and advances only over leading spaces and
    tabs; a sign without digits is left unconsumed. -/
theorem scanInt_failure_contract (bytes : List Nat) (pos : Nat)
    {value : Int} {cursor : Nat}
    (h : scanInt bytes pos = (false, value, cursor)) :
    value = 0 ∧ cursor = pos + ((bytes.drop pos).takeWhile scanSpace).length := by
  exact scanIntDigits_failure_contract _ _ _ _ h

/-- The success/failure flag depends on the scanned suffix, not on the absolute
    cursor values supplied to the digit-suffix helper. -/
theorem scanIntDigits_flag_positions (digits : List Nat) (negative : Bool)
    (digitStart failureCursor digitStart' failureCursor' : Nat) :
    (scanIntDigits digits negative digitStart failureCursor).1 =
      (scanIntDigits digits negative digitStart' failureCursor').1 := by
  cases digits with
  | nil => rfl
  | cons b bs =>
    by_cases hd : scanDigit b = true
    · simp [scanIntDigits, hd]
    · simp [scanIntDigits, hd]

/-- Scanning a buffer at `pos` and scanning its suffix at zero have the same
    success/failure flag. -/
theorem scanInt_drop_flag (bytes : List Nat) (pos : Nat) :
    (scanInt bytes pos).1 = (scanInt (bytes.drop pos) 0).1 := by
  simp only [scanInt, List.drop_zero]
  exact scanIntDigits_flag_positions _ _ _ _ _ _

/-- An all-whitespace input fails with zero and advances through the complete
    whitespace prefix. -/
theorem scanInt_whitespace_failure (bytes : List Nat)
    (hspaces : bytes.takeWhile scanSpace = bytes) :
    scanInt bytes 0 = (false, 0, bytes.length) := by
  simp [scanInt, hspaces, scanIntDigits]

/-- The pure scanner rejects a non-sign, non-digit byte immediately after a
    maximal leading whitespace prefix. The remaining suffix is irrelevant
    because the first digit check fails without consuming the delimiter. -/
theorem scanInt_delimiter_failure (spaces : List Nat) (byte : Nat)
    (tail : List Nat)
    (hspaces : spaces.takeWhile scanSpace = spaces)
    (hnotSpace : scanSpace byte = false)
    (hnotSign : byte ≠ 43 ∧ byte ≠ 45)
    (hnondigit : scanDigit byte = false) :
    scanInt (spaces ++ byte :: tail) 0 = (false, 0, spaces.length) := by
  have htake : (spaces ++ byte :: tail).takeWhile scanSpace = spaces := by
    induction spaces with
    | nil => simp [hnotSpace]
    | cons head rest ih =>
      simp only [List.takeWhile_cons] at hspaces
      have hhead : scanSpace head = true := by
        by_cases hhead : scanSpace head = true
        · exact hhead
        · simp [hhead] at hspaces
      have hrest : rest.takeWhile scanSpace = rest := by
        simpa [hhead] using hspaces
      simp [List.takeWhile_cons, hhead, ih hrest]
  have hafter : (spaces ++ byte :: tail).drop spaces.length = byte :: tail := by
    simp
  have hhasSign : ((byte :: tail).head? == some 43 ||
      (byte :: tail).head? == some 45) = false := by
    simp [hnotSign.1, hnotSign.2]
  have hplus : (byte == 43) = false := by simp [hnotSign.1]
  have hminus : (byte == 45) = false := by simp [hnotSign.2]
  simp [scanInt, htake, hafter, hhasSign, hplus, hminus,
    scanIntDigits, hnondigit]

/-- Scan the next token after spaces and tabs. The cursor stops at the first
    delimiter after a nonempty maximal token; that delimiter is consumed by
    the next call's whitespace skip, as in `tobj_next_token`. -/
def nextTokenStart (bytes : List Nat) (pos : Nat) : Nat :=
  let rest := bytes.drop pos
  let spaces := rest.takeWhile scanSpace
  pos + spaces.length

/-- The maximal non-space suffix beginning at `nextTokenStart`. -/
def nextTokenBytes (bytes : List Nat) (pos : Nat) : List Nat :=
  let rest := bytes.drop pos
  let spaces := rest.takeWhile scanSpace
  (rest.drop spaces.length).takeWhile (fun b => !scanSpace b)

private theorem takeWhile_all_true {α : Type} (p : α → Bool) (xs : List α) :
    (xs.takeWhile p).all p = true := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.takeWhile_cons]
    split
    · simp_all
    · rfl

/-- If `takeWhile` stops before the suffix ends, its next byte fails the
    predicate. -/
private theorem takeWhile_boundary {α : Type} (p : α → Bool) (xs : List α)
    (h : (xs.takeWhile p).length < xs.length) :
    ∃ b, (xs.drop (xs.takeWhile p).length).head? = some b ∧ p b = false := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    by_cases hp : p a = true
    · simp only [List.takeWhile_cons, hp, ite_true, List.length_cons] at h ⊢
      have htail : (as.takeWhile p).length < as.length := by omega
      obtain ⟨b, hb, hpb⟩ := ih htail
      exact ⟨b, by simpa using hb, hpb⟩
    · have hpfalse : p a = false := Bool.eq_false_iff.mpr hp
      simp only [List.takeWhile_cons, hpfalse] at h ⊢
      exact ⟨a, by simp, hpfalse⟩

/-- Indexed form of the delimiter failure contract, for a raw buffer whose
    first nonspace byte is a non-sign nondigit. -/
theorem scanInt_delimiter_failure_at (bytes : List Nat) (byte : Nat)
    (hbyteAt : bytes[(bytes.takeWhile scanSpace).length]? = some byte)
    (hnotSign : byte ≠ 43 ∧ byte ≠ 45)
    (hnondigit : scanDigit byte = false) :
    scanInt bytes 0 = (false, 0, (bytes.takeWhile scanSpace).length) := by
  let spaces := bytes.takeWhile scanSpace
  have hbound : spaces.length < bytes.length := by
    have hidx := (List.getElem?_eq_some_iff.mp hbyteAt).choose
    omega
  obtain ⟨first, hfirst, hnotSpace⟩ := takeWhile_boundary scanSpace bytes hbound
  have hvalue : bytes[spaces.length] = byte := by
    have h := hbyteAt
    rw [List.getElem?_eq_some_iff] at h
    rcases h with ⟨_, hvalue⟩
    exact hvalue
  have hhead : (bytes.drop spaces.length).head? =
      some (bytes[spaces.length]) := by
    rw [List.drop_eq_getElem_cons hbound]
    rfl
  have hfirstEq : first = byte := by
    exact (Option.some.inj (hfirst.symm.trans hhead)).trans hvalue
  subst first
  have hdrop : bytes.drop spaces.length = byte :: bytes.drop (spaces.length + 1) := by
    rw [List.drop_eq_getElem_cons hbound]
    rw [hvalue]
  have hplus : (byte == 43) = false := by simp [hnotSign.1]
  have hminus : (byte == 45) = false := by simp [hnotSign.2]
  simp [scanInt, spaces, hdrop, hnotSpace, hplus, hminus,
    scanIntDigits, hnondigit]

theorem takeWhile_append_stops {α : Type} (p : α → Bool)
    (spaces suffix : List α)
    (hspaces : spaces.takeWhile p = spaces)
    (hstop : ∀ b, suffix.head? = some b → p b = false) :
    (spaces ++ suffix).takeWhile p = spaces := by
  induction spaces with
  | nil =>
    cases suffix with
    | nil => rfl
    | cons head tail => simp [List.takeWhile_cons, hstop head rfl]
  | cons head rest ih =>
    simp only [List.takeWhile_cons] at hspaces
    have hhead : p head = true := by
      by_cases hhead : p head = true
      · exact hhead
      · simp [hhead] at hspaces
    have hrest : rest.takeWhile p = rest := by
      simpa [hhead] using hspaces
    simp [List.takeWhile_cons, hhead, ih hrest]

/-- A lone optional sign is a failed scan, and the pure scanner leaves the
    caller cursor just after the whitespace prefix. -/
theorem scanInt_lone_sign_failure (spaces : List Nat) (sign : Nat)
    (hspaces : spaces.takeWhile scanSpace = spaces)
    (hsign : sign = 43 ∨ sign = 45) :
    scanInt (spaces ++ [sign]) 0 = (false, 0, spaces.length) := by
  have hsignNotSpace : scanSpace sign = false := by
    rcases hsign with hp | hm
    · simp [scanSpace, hp]
    · simp [scanSpace, hm]
  have htake : (spaces ++ [sign]).takeWhile scanSpace = spaces :=
    takeWhile_append_stops scanSpace spaces [sign] hspaces
      (by intro b hb; simp at hb; subst b; exact hsignNotSpace)
  have hafter : (spaces ++ [sign]).drop spaces.length = [sign] := by simp
  simp only [scanInt, List.drop_zero, htake, hafter]
  rcases hsign with hp | hm
  · simp [hp, scanIntDigits]
  · simp [hm, scanIntDigits]

/-- A sign followed by a nondigit fails without committing the consumed sign
    to the caller cursor. -/
theorem scanInt_sign_nondigit_failure (spaces : List Nat)
    (sign byte : Nat) (tail : List Nat)
    (hspaces : spaces.takeWhile scanSpace = spaces)
    (hsign : sign = 43 ∨ sign = 45)
    (hnondigit : scanDigit byte = false) :
    scanInt (spaces ++ sign :: byte :: tail) 0 =
      (false, 0, spaces.length) := by
  have hsignNotSpace : scanSpace sign = false := by
    rcases hsign with hp | hm
    · simp [scanSpace, hp]
    · simp [scanSpace, hm]
  have htake : (spaces ++ sign :: byte :: tail).takeWhile scanSpace = spaces :=
    takeWhile_append_stops scanSpace spaces (sign :: byte :: tail) hspaces
      (by intro b hb; simp at hb; subst b; exact hsignNotSpace)
  have hafter : (spaces ++ sign :: byte :: tail).drop spaces.length =
      sign :: byte :: tail := by simp
  simp only [scanInt, List.drop_zero, htake, hafter]
  rcases hsign with hp | hm
  · simp [hp, scanIntDigits, hnondigit]
  · simp [hm, scanIntDigits, hnondigit]


/-- Every byte in the token slice is non-whitespace. -/
theorem nextTokenBytes_no_space (bytes : List Nat) (pos : Nat) :
    (nextTokenBytes bytes pos).all (fun b => !scanSpace b) = true := by
  unfold nextTokenBytes
  exact takeWhile_all_true _ _

/-- A token that ends before the input suffix is followed by whitespace. -/
theorem nextTokenBytes_boundary (bytes : List Nat) (pos : Nat)
    (h : (nextTokenBytes bytes pos).length <
      ((bytes.drop pos).drop ((bytes.drop pos).takeWhile scanSpace).length).length) :
    ∃ b, (((bytes.drop pos).drop ((bytes.drop pos).takeWhile scanSpace).length).drop
      (nextTokenBytes bytes pos).length).head? = some b ∧ scanSpace b = true := by
  obtain ⟨b, hb, hnot⟩ := takeWhile_boundary (fun b => !scanSpace b)
    ((bytes.drop pos).drop ((bytes.drop pos).takeWhile scanSpace).length) (by simpa [nextTokenBytes] using h)
  refine ⟨b, ?_, ?_⟩
  · simpa [nextTokenBytes] using hb
  · cases hs : scanSpace b <;> simp_all

def nextToken (bytes : List Nat) (pos : Nat) : Option (Nat × Nat) × Nat :=
  let start := nextTokenStart bytes pos
  let token := nextTokenBytes bytes pos
  if token.isEmpty then (none, start)
  else (some (start, token.length), start + token.length)

/-- Successful token length is exactly the maximal token slice length. -/
theorem nextToken_success_length {bytes : List Nat} {pos start len : Nat}
    (h : (nextToken bytes pos).1 = some (start, len)) :
    len = (nextTokenBytes bytes pos).length := by
  simp only [nextToken] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm

/-- A successful token begins immediately after the leading space/tab prefix. -/
theorem nextToken_success_start {bytes : List Nat} {pos start len : Nat}
    (h : (nextToken bytes pos).1 = some (start, len)) :
    start = nextTokenStart bytes pos := by
  simp only [nextToken] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm

/-- A successful pure token scan always reports a nonempty token and places
    the cursor exactly at the end of that token. -/
theorem nextToken_success_contract {bytes : List Nat} {pos start len : Nat}
    (h : (nextToken bytes pos).1 = some (start, len)) :
    0 < len ∧ (nextToken bytes pos).2 = start + len := by
  dsimp [nextToken] at h ⊢
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    constructor
    · apply List.length_pos_iff.mpr
      intro hnil
      simp_all
    · simp_all

example : nextToken [32, 32, 97, 98, 32, 99] 0 = (some (2, 2), 4) := by decide
example : nextToken [32, 9, 32] 0 = (none, 3) := by decide
example : nextToken [120, 32, 97] 1 = (some (2, 1), 3) := by decide

example : scanInt [32, 45, 49, 50, 120] 0 = (true, -12, 4) := by decide
example : scanInt [32, 43, 120] 0 = (false, 0, 1) := by decide
example : scanInt [57, 57, 57, 57, 57, 57, 57, 57, 57, 57] 0 =
    (true, 2147483647, 10) := by decide

theorem resolveIndex_pos {idx : Int} {n : Nat} (h : 0 < idx) :
    resolveIndex idx n = some (idx - 1) := by
  simp [resolveIndex, h]

theorem resolveIndex_zero {n : Nat} : resolveIndex 0 n = none := by
  simp [resolveIndex]

theorem resolveIndex_neg_in {idx : Int} {n : Nat} (h : idx < 0) (hn : 0 ≤ (n : Int) + idx) :
    resolveIndex idx n = some ((n : Int) + idx) := by
  have h1 : ¬ 0 < idx := by omega
  have h2 : idx ≠ 0 := by omega
  simp [resolveIndex, h1, h2, hn]

theorem resolveIndex_neg_out {idx : Int} {n : Nat} (h : idx < 0) (hn : (n : Int) + idx < 0) :
    resolveIndex idx n = none := by
  have h1 : ¬ 0 < idx := by omega
  have h2 : idx ≠ 0 := by omega
  have h3 : ¬ 0 ≤ (n : Int) + idx := by omega
  simp [resolveIndex, h1, h2, h3]

/-- Every valid resolution lands inside the array (`0 ≤ result < n` for
    positive indices in range is the caller's responsibility; the spec only
    guarantees non-negativity of the resolved relative index). -/
theorem resolved_nonneg {idx : Int} {n : Nat} {r : Int} (h : resolveIndex idx n = some r) :
    0 ≤ r := by
  unfold resolveIndex at h
  split at h
  · simp at h; omega
  · split at h
    · simp at h
    · split at h
      · simp at h; omega
      · simp at h

end Obj

/-
  MiniC: a small, executable operational semantics for the C subset used by
  the tinygltf "verified core" functions.

  The C source is translated mechanically by `formal/tools/c2lean.py` from
  clang's fully type-annotated AST (`-ast-dump=json`), so every implicit
  conversion (integer promotion, usual arithmetic conversion, lvalue-to-
  rvalue) is explicit in the input to this semantics.

  Scope (anything else is rejected by the translator):
  * integer types of width 8/16/32/64, signed and unsigned; `double`
    (as IEEE bit patterns, comparisons only); pointers to objects;
    structs/arrays through computed byte offsets (from clang's record layout)
  * locals whose address is never taken (they live in a register file)
  * `if`, `while`, `for` (desugared), `break`, `continue`, `return`,
    calls to other translated functions
  * no `goto`, `switch`, varargs, function pointers, `malloc`, libc calls

  Undefined behaviour is explicit: every operation that is UB in ISO C11
  (signed overflow, division by zero, oversized shifts, out-of-bounds or
  out-of-object memory access, pointer arithmetic leaving an object, reading
  an uninitialised local) yields `Res.ub`.

  Memory: a heap of blocks, each a list of bytes. Loads/stores are
  little-endian (all targets tinygltf supports). Strict aliasing and
  alignment are not modelled: the verified functions only access objects
  through their declared types.
-/
namespace Obj.C

/-! ## Types and values -/

structure IntTy where
  width : Nat
  signed : Bool
  deriving DecidableEq, Repr

namespace IntTy
def i8 : IntTy := ⟨8, true⟩
def u8 : IntTy := ⟨8, false⟩
def i16 : IntTy := ⟨16, true⟩
def u16 : IntTy := ⟨16, false⟩
def i32 : IntTy := ⟨32, true⟩
def u32 : IntTy := ⟨32, false⟩
def i64 : IntTy := ⟨64, true⟩
def u64 : IntTy := ⟨64, false⟩

def modulus (t : IntTy) : Nat := 2 ^ t.width
def bytes (t : IntTy) : Nat := t.width / 8

/-- Mathematical value of a representation `n < 2^w`. -/
def toInt (t : IntTy) (n : Nat) : Int :=
  if t.signed ∧ n ≥ 2 ^ (t.width - 1) then (n : Int) - (t.modulus : Int) else n

def minVal (t : IntTy) : Int := if t.signed then -((2 : Int) ^ (t.width - 1)) else 0
def maxVal (t : IntTy) : Int :=
  if t.signed then (2 : Int) ^ (t.width - 1) - 1 else (t.modulus : Int) - 1

/-- Two's-complement wrap of an integer into the representation range. -/
def wrap (t : IntTy) (z : Int) : Nat := (z % (t.modulus : Int)).toNat

def inRange (t : IntTy) (z : Int) : Bool := decide (t.minVal ≤ z) && decide (z ≤ t.maxVal)
end IntTy

inductive Ty where
  | int (t : IntTy)
  | f64
  | ptr
  deriving DecidableEq, Repr

def Ty.size : Ty → Nat
  | .int t => t.bytes
  | .f64 => 8
  | .ptr => 8

inductive Val where
  /-- Integer of type `t`, representation `n < 2^t.width`. -/
  | int (t : IntTy) (n : Nat)
  /-- IEEE-754 binary64 bit pattern. -/
  | f64 (bits : Nat)
  /-- Pointer into block `b` at byte offset `o`. -/
  | ptr (b : Nat) (o : Nat)
  /-- The null pointer. -/
  | null
  deriving DecidableEq, Repr

/-! ## Results -/

inductive Res (α : Type) where
  | ok (a : α)
  /-- Undefined behaviour. -/
  | ub
  /-- Fuel exhausted (non-termination is excluded by exhibiting fuel). -/
  | timeout
  deriving Repr

namespace Res
def bind {α β} : Res α → (α → Res β) → Res β
  | .ok a, f => f a
  | .ub, _ => .ub
  | .timeout, _ => .timeout

instance : Monad Res where
  pure := .ok
  bind := bind

@[simp] theorem bind_ok {α β} (a : α) (f : α → Res β) : bind (.ok a) f = f a := rfl
@[simp] theorem bind_ub {α β} (f : α → Res β) : bind (.ub : Res α) f = .ub := rfl
@[simp] theorem bind_timeout {α β} (f : α → Res β) : bind (.timeout : Res α) f = .timeout := rfl
@[simp] theorem bind_eq {α β} (x : Res α) (f : α → Res β) : x >>= f = bind x f := rfl
@[simp] theorem pure_eq {α} (a : α) : (pure a : Res α) = .ok a := rfl
end Res

def guard (c : Bool) : Res Unit := if c then .ok () else .ub

/-! ## Memory -/

abbrev Block := List UInt8
abbrev Mem := Nat → Option Block

def Mem.upd (m : Mem) (b : Nat) (blk : Block) : Mem :=
  fun b' => if b' = b then some blk else m b'

def decodeLE : List UInt8 → Nat
  | [] => 0
  | x :: xs => x.toNat + 256 * decodeLE xs

def encodeLE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => (n % 256).toUInt8 :: encodeLE k (n / 256)

/-- Read `n` bytes at `[o, o+n)` of block `b`. -/
def readBytes (m : Mem) (b o n : Nat) : Res (List UInt8) :=
  match m b with
  | none => .ub
  | some blk => if o + n ≤ blk.length then .ok ((blk.drop o).take n) else .ub

def writeBytes (m : Mem) (b o : Nat) (bs : List UInt8) : Res Mem :=
  match m b with
  | none => .ub
  | some blk =>
    if o + bs.length ≤ blk.length then
      .ok (m.upd b (blk.take o ++ bs ++ blk.drop (o + bs.length)))
    else .ub

/-- Pointers stored in memory are represented by the pair (block, offset)
    packed into 8 bytes; `0` is the null pointer. This is a modelling
    convention: the verified core never round-trips pointers through integer
    representation, it only stores and reloads them. -/
def ptrPack (p : Val) : Nat :=
  match p with
  | .ptr b o => 1 + b * 4294967296 + o
  | _ => 0

def ptrUnpack (v : Nat) : Val :=
  if v = 0 then .null else .ptr ((v - 1) / 4294967296) ((v - 1) % 4294967296)

def load (m : Mem) (ty : Ty) (p : Val) : Res Val :=
  match p with
  | .ptr b o => do
    let bs ← readBytes m b o ty.size
    match ty with
    | .int t => pure (.int t (decodeLE bs))
    | .f64 => pure (.f64 (decodeLE bs))
    | .ptr => pure (ptrUnpack (decodeLE bs))
  | _ => .ub

def store (m : Mem) (ty : Ty) (p v : Val) : Res Mem :=
  match p, ty, v with
  | .ptr b o, .int t, .int t' n => if t = t' then writeBytes m b o (encodeLE t.bytes n) else .ub
  | .ptr b o, .f64, .f64 n => writeBytes m b o (encodeLE 8 n)
  | .ptr b o, .ptr, p => writeBytes m b o (encodeLE 8 (ptrPack p))
  | _, _, _ => .ub

/-! ## Syntax -/

inductive BinOp where
  | add | sub | mul | div | mod | shl | shr | band | bor | bxor
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr

inductive UnOp where
  | neg | bnot | lnot
  deriving DecidableEq, Repr

inductive Expr where
  | const (v : Val)
  /-- Read a local variable (register). -/
  | var (id : Nat)
  /-- Load an object of type `ty` from the address computed by `addr`. -/
  | load (ty : Ty) (addr : Expr)
  /-- `base + idx * elem` (pointer arithmetic / array subscript address). -/
  | index (base : Expr) (idx : Expr) (elem : Nat)
  /-- `&base->field`: byte offset of a member. -/
  | field (base : Expr) (off : Nat)
  /-- Arithmetic on operands of integer type `t` (or comparisons of `f64`
      when `t` is `none`); comparisons yield `int`. -/
  | bin (op : BinOp) (t : Option IntTy) (a b : Expr)
  | un (op : UnOp) (t : IntTy) (a : Expr)
  /-- Integer conversion to `t`. -/
  | cast (t : IntTy) (a : Expr)
  /-- `a && b`, `a || b` (short-circuit), `c ? a : b`. -/
  | land (a b : Expr)
  | lor (a b : Expr)
  | cond (c a b : Expr)
  | call (f : Nat) (args : List Expr)
  /-- C `memcmp(p, q, n)`: first differing byte pair, or 0. -/
  | memcmp (p q n : Expr)
  /-- C `strlen(p)`: number of bytes before the first NUL. -/
  | strlen (p : Expr)
  /-- Fused multiply-add `a * b + c`, rounded once.  This models the hardware
      instruction that `fma()` / `__builtin_fma()` compile to: x86-64
      `vfmadd132/213/231sd` (AVX/FMA3) and AArch64 `fmadd d0, d1, d2, d3`
      both implement IEEE-754 `fusedMultiplyAdd`, i.e. the exact product is
      added to `c` and the *single* result is rounded to nearest, ties to
      even.  Because both architectures agree on that definition, one
      semantics covers both. -/
  | fma (a b c : Expr)
  deriving Repr, Inhabited

inductive Stmt where
  | skip
  | set (id : Nat) (e : Expr)
  | store (ty : Ty) (addr : Expr) (e : Expr)
  | eval (e : Expr)
  /-- Statement-level call; may write memory; result optionally assigned. -/
  | call (dst : Option Nat) (f : Nat) (args : List Expr)
  | seq (a b : Stmt)
  | ite (c : Expr) (a b : Stmt)
  /-- `loop body`: runs `body` until `break`/`return`; `continue` re-enters.
      `while (c) s` is `loop (if c then s else break)`; `for` adds the step. -/
  | loop (body : Stmt) (step : Stmt)
  | brk
  | cont
  | ret (e : Option Expr)
  deriving Repr, Inhabited

structure Func where
  params : List Nat
  body : Stmt
  deriving Repr, Inhabited

abbrev Prog := Nat → Option Func

/-! ## Evaluation -/

abbrev Locals := Nat → Option Val

def Locals.upd (l : Locals) (i : Nat) (v : Val) : Locals :=
  fun j => if j = i then some v else l j

/-- Locals of a fresh call frame: parameters bound to the argument values. -/
def frameLocals (params : List Nat) (vs : List Val) : Locals := fun i =>
  match params.idxOf? i with
  | some k => vs[k]?
  | none => none

structure State where
  locals : Locals
  mem : Mem
  /-- Inside a call that appears in an expression: memory writes are UB
      (the translator only emits expression calls to read-only functions,
      and this makes the semantics enforce it). -/
  ro : Bool := false

inductive Outcome where
  | normal | brk | cont | ret (v : Option Val)
  deriving Repr

def truthy : Val → Res Bool
  | .int _ n => .ok (n != 0)
  | .ptr _ _ => .ok true
  | .null => .ok false
  | .f64 _ => .ub

def boolVal (b : Bool) : Val := .int IntTy.i32 (if b then 1 else 0)

/-- Operand of type `t`. Type mismatches (a translator bug) are UB. Every
    value produced by the semantics is normalized (`n < 2^width`): constants
    are normalized by the translator, loads decode `width/8` bytes, and every
    operation reduces modulo `2^width`. -/
def intOf (t : IntTy) : Val → Res Nat
  | .int t' n => if t = t' then .ok n else .ub
  | _ => .ub

/-- Arithmetic result: signed overflow is UB, unsigned wraps. -/
def arith (t : IntTy) (z : Int) : Res Val :=
  if t.signed then (if t.inRange z then .ok (.int t (t.wrap z)) else .ub)
  else .ok (.int t (t.wrap z))

/-- IEEE comparison key on bit patterns (see `Obj.F64.key`). -/
def f64Key (bits : Nat) : Int :=
  let m : Int := (bits % 2^63 : Nat)
  if bits / 2^63 % 2 = 1 then -m else m
def f64IsNaN (bits : Nat) : Bool := (bits / 2^52) % 2^11 = 2047 && bits % 2^52 != 0

/-! ### Exact IEEE-754 binary64 arithmetic

The verified core includes `double` arithmetic (`tobj_dabs`, `tobj_orient2d`,
the area/orientation tests of `tobj_tess_polygon_core`).  To model it without
depending on the opaque host float, every operation is defined on bit patterns
and goes through an *exact* rational value:

1. `F64.toRat` decodes a finite bit pattern to the exact `Rat` it denotes
   (subnormals included);
2. the exact result (a `Rat`) is rounded to nearest binary64, ties to even, by
   `F64.ofRat`.

`Rat` is unbounded-precision, so no intermediate value is lost: this is a
correctly-rounded model of each operation.  Only the four basic operations and
negation are provided (no `fma`, no `sqrt`), which is exactly what the C
translation uses.  NaN/±inf/±0 rules follow IEEE-754.

All of this is decidable and kernel-checkable; `Obj.Tests.ObjF64` pins the
common vectors (including `0.1 + 0.2`, subnormals, overflow and signed zero)
against CPython's results. -/
namespace F64

/-- `2^k` for a `Nat` exponent. -/
def p2 (k : Nat) : Nat := 2 ^ k

theorem p2_zero : p2 0 = 1 := by decide
theorem p2_pos (k : Nat) : 0 < p2 k := by unfold p2; exact Nat.two_pow_pos k

def signBit (b : Nat) : Bool := b / p2 63 % 2 = 1
def expField (b : Nat) : Nat := b / p2 52 % p2 11
def mantissa (b : Nat) : Nat := b % p2 52
def isNaN (b : Nat) : Bool := expField b = 2047 && mantissa b ≠ 0
def isInf (b : Nat) : Bool := expField b = 2047 && mantissa b = 0
def isZero (b : Nat) : Bool := expField b = 0 && mantissa b = 0

def infBits (neg : Bool) : Nat := (if neg then p2 63 else 0) + 2047 * p2 52
def qnanBits : Nat := 2047 * p2 52 + p2 51
def zeroBits (neg : Bool) : Nat := if neg then p2 63 else 0

/-- Exact value of a finite bit pattern as a rational. -/
def toRat (b : Nat) : Rat :=
  let s := signBit b
  let e := expField b
  let f := mantissa b
  let mag : Rat :=
    if e = 0 then
      Rat.divInt (f : Int) ((p2 1074 : Nat) : Int)
    else
      let num := p2 52 + f
      let k : Int := (e : Int) - 1075
      if 0 ≤ k then Rat.divInt ((num * p2 k.toNat : Nat) : Int) 1
      else Rat.divInt (num : Int) (((p2 (-k).toNat) : Nat) : Int)
  if s then -mag else mag

/-- `2^e ≤ p/q` for `p, q > 0`. -/
def leShift (p q : Nat) (e : Int) : Bool :=
  if 0 ≤ e then decide (q * p2 e.toNat ≤ p) else decide (q ≤ p * p2 (-e).toNat)

/-- Binary search for the largest `e ∈ [lo, hi]` with `2^e ≤ p/q`. -/
def search (p q : Nat) : Nat → Int → Int → Int
  | 0, lo, _ => lo
  | k + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if leShift p q mid then search p q k mid hi else search p q k lo mid

/-- `⌊log₂(p/q)⌋` for `p, q > 0` (`p ≤ 2^1075`, `q ≤ 2^1100`, which covers
    every finite double and every finite sum/product/quotient of two of them
    after scaling). -/
def floorLog2 (p q : Nat) : Int := search p q 12 (-1100) 1100

/-- Round `p/q` to the nearest integer, ties to even. -/
def roundRat (p q : Nat) : Nat :=
  let m0 := p / q
  let r := p % q
  let twoR := 2 * r
  if twoR < q then m0
  else if q < twoR then m0 + 1
  else if m0 % 2 = 0 then m0 else m0 + 1

/-- Encode `m · 2^E` (`m > 0`) as a binary64 bit pattern with sign `neg`,
    rounding the significand to 53 bits (ties to even), handling subnormals
    and overflow to infinity. -/
def encode (neg : Bool) (m : Nat) (E : Int) : Nat :=
  let sgn := if neg then p2 63 else 0
  let bl := Nat.log2 m + 1
  let topExp := E + (bl : Int) - 1
  if topExp ≥ -1022 then
    let ef := topExp + 1023
    if ef ≥ 2047 then infBits neg
    else
      let shift := 52 - (bl - 1)
      let sig := m * p2 shift
      sgn + ef.toNat * p2 52 + (sig - p2 52)
  else
    sgn + m

/-- Round an exact rational to the nearest binary64 bit pattern. -/
def ofRat (r : Rat) : Nat :=
  let n : Int := r.num
  let d : Nat := r.den
  let neg : Bool := n < 0
  let p : Nat := n.natAbs
  if p = 0 then zeroBits neg
  else
    let e := floorLog2 p d
    let E : Int := if e - 52 < -1074 then -1074 else e - 52
    let nd : Nat × Nat :=
      if 0 ≤ E then (p, d * p2 E.toNat) else (p * p2 (-E).toNat, d)
    let m := roundRat nd.1 nd.2
    if m = 0 then zeroBits neg else encode neg m E

/-- Bitwise sign flip (IEEE negation; maps a NaN pattern to a NaN pattern). -/
def negBits (b : Nat) : Nat := b ^^^ p2 63

def addBits (a b : Nat) : Nat :=
  if isNaN a || isNaN b then qnanBits
  else if isInf a && isInf b then
    (if signBit a = signBit b then a else qnanBits)
  else if isInf a then a
  else if isInf b then b
  else ofRat (toRat a + toRat b)

/-- Fused multiply-add: `a * b + c` with a single rounding.  The product is
    computed exactly in `Rat` (no intermediate rounding), added to `c`, and
    only the final sum is rounded to binary64 -- which is exactly IEEE-754
    `fusedMultiplyAdd` and therefore both x86-64 `vfmadd*sd` and AArch64
    `fmadd`. -/
def fmaBits (a b c : Nat) : Nat :=
  if isNaN a || isNaN b || isNaN c then qnanBits
  else if (isInf a && isZero b) || (isZero a && isInf b) then qnanBits
  else if isInf a || isInf b then
    -- infinite product, finite `c`: propagate the product's sign unless `c`
    -- is an infinity of the opposite sign
    let prodNeg := signBit a != signBit b
    if isInf c && signBit c != prodNeg then qnanBits else infBits prodNeg
  else if isInf c then c
  else ofRat (toRat a * toRat b + toRat c)

def subBits (a b : Nat) : Nat := addBits a (negBits b)

def mulBits (a b : Nat) : Nat :=
  if isNaN a || isNaN b then qnanBits
  else if isInf a || isInf b then
    (if isZero a || isZero b then qnanBits else infBits (signBit a != signBit b))
  else if isZero a || isZero b then zeroBits (signBit a != signBit b)
  else ofRat (toRat a * toRat b)

def divBits (a b : Nat) : Nat :=
  if isNaN a || isNaN b then qnanBits
  else if isInf a && isInf b then qnanBits
  else if isInf a then infBits (signBit a != signBit b)
  else if isInf b then zeroBits (signBit a != signBit b)
  else if isZero b then
    (if isZero a then qnanBits else infBits (signBit a != signBit b))
  else
    let q := ofRat (toRat a / toRat b)
    if q = zeroBits false || q = zeroBits true then zeroBits (signBit a != signBit b)
    else q

end F64

def binF64 (op : BinOp) (a b : Nat) : Res Val :=
  let nan := f64IsNaN a || f64IsNaN b
  let ka := f64Key a
  let kb := f64Key b
  match op with
  | .lt => .ok (boolVal (!nan && decide (ka < kb)))
  | .le => .ok (boolVal (!nan && decide (ka ≤ kb)))
  | .gt => .ok (boolVal (!nan && decide (ka > kb)))
  | .ge => .ok (boolVal (!nan && decide (ka ≥ kb)))
  | .eq => .ok (boolVal (!nan && decide (ka = kb)))
  | .ne => .ok (boolVal (nan || decide (ka ≠ kb)))
  | .add => .ok (.f64 (F64.addBits a b))
  | .sub => .ok (.f64 (F64.subBits a b))
  | .mul => .ok (.f64 (F64.mulBits a b))
  | .div => .ok (.f64 (F64.divBits a b))
  | _ => .ub

def binInt (op : BinOp) (t : IntTy) (va vb : Val) : Res Val :=
  match op with
  | .shl | .shr => do
    -- operands are promoted independently; the result has the left type
    let a ← intOf t va
    let (tb, b) ← match vb with
      | .int tb b => pure (tb, b)
      | _ => .ub
    let k := tb.toInt b
    guard (decide (0 ≤ k) && decide (k < t.width))
    let k := k.toNat
    if op = .shl then
      if t.signed then
        if t.toInt a < 0 then .ub else arith t (t.toInt a * 2 ^ k)
      else pure (.int t ((a * 2 ^ k) % t.modulus))
    else pure (.int t (if t.signed then t.wrap (t.toInt a / 2 ^ k) else a / 2 ^ k))
  | _ => do
    let a ← intOf t va
    let b ← intOf t vb
    if t.signed then
      let za := t.toInt a
      let zb := t.toInt b
      match op with
      | .add => arith t (za + zb)
      | .sub => arith t (za - zb)
      | .mul => arith t (za * zb)
      | .div => if zb = 0 then .ub else arith t (za.tdiv zb)
      | .mod => if zb = 0 then .ub else
          if t.inRange (za.tdiv zb) then pure (.int t (t.wrap (za.tmod zb))) else .ub
      | .band => pure (.int t (a &&& b))
      | .bor => pure (.int t (a ||| b))
      | .bxor => pure (.int t (a ^^^ b))
      | .lt => pure (boolVal (decide (za < zb)))
      | .le => pure (boolVal (decide (za ≤ zb)))
      | .gt => pure (boolVal (decide (za > zb)))
      | .ge => pure (boolVal (decide (za ≥ zb)))
      | .eq => pure (boolVal (decide (za = zb)))
      | .ne => pure (boolVal (decide (za ≠ zb)))
      | _ => .ub
    else
      -- unsigned arithmetic is arithmetic modulo 2^width, computed on `Nat`
      let M := t.modulus
      match op with
      | .add => pure (.int t ((a + b) % M))
      | .sub => pure (.int t (if b ≤ a then a - b else a + M - b))
      | .mul => pure (.int t ((a * b) % M))
      | .div => if b = 0 then .ub else pure (.int t (a / b))
      | .mod => if b = 0 then .ub else pure (.int t (a % b))
      | .band => pure (.int t (a &&& b))
      | .bor => pure (.int t (a ||| b))
      | .bxor => pure (.int t (a ^^^ b))
      | .lt => pure (boolVal (decide (a < b)))
      | .le => pure (boolVal (decide (a ≤ b)))
      | .gt => pure (boolVal (decide (a > b)))
      | .ge => pure (boolVal (decide (a ≥ b)))
      | .eq => pure (boolVal (decide (a = b)))
      | .ne => pure (boolVal (decide (a ≠ b)))
      | _ => .ub

/-- Pointer comparison: `==`/`!=` only (C relational comparison of unrelated
    pointers is unspecified). -/
def ptrEq (a b : Val) : Bool :=
  match a, b with
  | .null, .null => true
  | .ptr x y, .ptr u v => x = u ∧ y = v
  | _, _ => false

def isPtr (v : Val) : Bool :=
  match v with
  | .ptr _ _ => true
  | .null => true
  | _ => false

/-- Binary integer/float operations.  `t` is the (usual-arithmetic-converted)
    operand type; when both operands are `double` the operation is IEEE float
    arithmetic regardless of whether the translator recorded the type as
    `none` (pure float context) or `some ⟨64, false⟩` (the converted `double`
    type) -- C's `double` operators are the same either way. -/
def evalBinInt (op : BinOp) (t : Option IntTy) (va vb : Val) : Res Val :=
  match va, vb with
  | .f64 a, .f64 b => binF64 op a b
  | _, _ =>
    match t with
    | some t => binInt op t va vb
    | none => .ub

/-- Unary operators.  `.neg` on a `double` is IEEE negation (a sign-bit flip,
    so `-0.0` is preserved and NaN stays NaN); on integers it is the usual
    two's-complement negation with signed-overflow UB. -/
def evalUn (op : UnOp) (t : IntTy) (v : Val) : Res Val :=
  match op with
  | .lnot => do let b ← truthy v; pure (boolVal (!b))
  | .neg =>
    match v with
    | .f64 bits => .ok (.f64 (F64.negBits bits))
    | _ => do let a ← intOf t v; arith t (-(t.toInt a))
  | .bnot => do let a ← intOf t v; pure (.int t (t.modulus - 1 - a))

def evalCast (t : IntTy) : Val → Res Val
  | .int t' n =>
    if t'.signed then .ok (.int t (t.wrap (t'.toInt n)))
    else .ok (.int t (n % t.modulus))
  | _ => .ub

/-- Pointer arithmetic may produce any address in `[0, length]` of the
    object (one-past-the-end included); anything else is UB. -/
def ptrAdd (m : Mem) (p : Val) (delta : Int) : Res Val :=
  match p with
  | .ptr b o =>
    match m b with
    | none => .ub
    | some blk =>
      let o' := (o : Int) + delta
      if 0 ≤ o' ∧ o' ≤ blk.length then .ok (.ptr b o'.toNat) else .ub
  | _ => .ub

/-- Non-negative pointer offset (unsigned index, member offset). -/
def evalBin (op : BinOp) (t : Option IntTy) (va vb : Val) : Res Val :=
  if isPtr va && isPtr vb then
    match op with
    | .sub =>
      match va, vb, t with
      | .ptr b1 o1, .ptr b2 o2, some ty =>
        if b1 = b2 then arith ty ((o1 : Int) - (o2 : Int)) else .ub
      | _, _, _ => .ub
    | .eq => .ok (boolVal (ptrEq va vb))
    | .ne => .ok (boolVal (!ptrEq va vb))
    | .lt =>
      match va, vb with
      | .ptr b1 o1, .ptr b2 o2 =>
        if b1 == b2 then .ok (boolVal (o1 < o2)) else .ub
      | _, _ => .ub
    | .le =>
      match va, vb with
      | .ptr b1 o1, .ptr b2 o2 =>
        if b1 == b2 then .ok (boolVal (o1 <= o2)) else .ub
      | _, _ => .ub
    | .gt =>
      match va, vb with
      | .ptr b1 o1, .ptr b2 o2 =>
        if b1 == b2 then .ok (boolVal (o1 > o2)) else .ub
      | _, _ => .ub
    | .ge =>
      match va, vb with
      | .ptr b1 o1, .ptr b2 o2 =>
        if b1 == b2 then .ok (boolVal (o1 >= o2)) else .ub
      | _, _ => .ub
    | _ => .ub
  else evalBinInt op t va vb

def ptrAddN (m : Mem) (p : Val) (k : Nat) : Res Val :=
  match p with
  | .ptr b o =>
    match m b with
    | none => .ub
    | some blk => if o + k ≤ blk.length then .ok (.ptr b (o + k)) else .ub
  | _ => .ub

/-- `strlen`: offset of the first zero byte at or after `o`, if any. -/
def strlenFrom (blk : Block) (o : Nat) : Option Nat :=
  if h : o < blk.length then
    if blk[o] = 0 then some o else strlenFrom blk (o + 1)
  else none
termination_by blk.length - o
decreasing_by omega

/-- Number of leading bytes on which `a` and `b` (from offsets `oa`, `ob`)
    agree, capped at `n`. -/
def commonPrefix (a : Block) (oa : Nat) (b : Block) (ob : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    match a[oa]?, b[ob]? with
    | some x, some y => if x = y then 1 + commonPrefix a (oa + 1) b (ob + 1) n else 0
    | _, _ => 0

def memcmpAt (m : Mem) (pa pb : Val) (n : Nat) : Res Val :=
  match pa, pb with
  | .ptr ba oa, .ptr bb ob =>
    match m ba, m bb with
    | some a, some b =>
      if oa + n ≤ a.length ∧ ob + n ≤ b.length then
        let k := commonPrefix a oa b ob n
        if h : k < n then
          match a[oa + k]?, b[ob + k]? with
          | some x, some y => .ok (.int IntTy.i32 (IntTy.wrap IntTy.i32 ((x.toNat : Int) - (y.toNat : Int))))
          | _, _ => .ub
        else .ok (.int IntTy.i32 0)
      else .ub
    | _, _ => .ub
  | _, _ => .ub

def strlenAt (m : Mem) (p : Val) : Res Val :=
  match p with
  | .ptr b o =>
    match m b with
    | none => .ub
    | some blk =>
      match strlenFrom blk o with
      | some e => .ok (.int IntTy.u64 (e - o))
      | none => .ub
  | _ => .ub

mutual
def evalExpr (p : Prog) : Nat → State → Expr → Res Val
  | 0, _, _ => .timeout
  | fuel + 1, s, e =>
    match e with
    | .const v => .ok v
    | .var i => match s.locals i with
      | some v => .ok v
      | none => .ub
    | .load ty a => do
      let pa ← evalExpr p fuel s a
      load s.mem ty pa
    | .index base idx elem => do
      let pb ← evalExpr p fuel s base
      let vi ← evalExpr p fuel s idx
      match vi with
      | .int t n => if t.signed then ptrAdd s.mem pb (t.toInt n * elem) else ptrAddN s.mem pb (n * elem)
      | _ => .ub
    | .field base off => do
      let pb ← evalExpr p fuel s base
      ptrAddN s.mem pb off
    | .bin op t a b => do
      let va ← evalExpr p fuel s a
      let vb ← evalExpr p fuel s b
      evalBin op t va vb
    | .un op t a => do
      let va ← evalExpr p fuel s a
      evalUn op t va
    | .cast t a => do
      let va ← evalExpr p fuel s a
      evalCast t va
    | .land a b => do
      let va ← evalExpr p fuel s a
      let ba ← truthy va
      if ba then do
        let vb ← evalExpr p fuel s b
        let bb ← truthy vb
        pure (boolVal bb)
      else pure (boolVal false)
    | .lor a b => do
      let va ← evalExpr p fuel s a
      let ba ← truthy va
      if ba then pure (boolVal true)
      else do
        let vb ← evalExpr p fuel s b
        let bb ← truthy vb
        pure (boolVal bb)
    | .cond c a b => do
      let vc ← evalExpr p fuel s c
      let bc ← truthy vc
      if bc then evalExpr p fuel s a else evalExpr p fuel s b
    | .memcmp pa pb pn => do
      let va ← evalExpr p fuel s pa
      let vb ← evalExpr p fuel s pb
      let vn ← evalExpr p fuel s pn
      match vn with
      | .int t n => memcmpAt s.mem va vb n
      | _ => .ub
    | .strlen pa => do
      let va ← evalExpr p fuel s pa
      strlenAt s.mem va
    | .fma a b c => do
      let va ← evalExpr p fuel s a
      let vb ← evalExpr p fuel s b
      let vc ← evalExpr p fuel s c
      match va, vb, vc with
      | .f64 x, .f64 y, .f64 z => .ok (.f64 (F64.fmaBits x y z))
      | _, _, _ => .ub
    | .call f args => do
      let vs ← evalArgs p fuel s args
      match p f with
      | none => .ub
      | some fn =>
        if fn.params.length = vs.length then do
          let (o, _) ← execStmt p fuel ⟨frameLocals fn.params vs, s.mem, true⟩ fn.body
          match o with
          | .ret (some v) => .ok v
          | _ => .ub
        else .ub

def evalArgs (p : Prog) : Nat → State → List Expr → Res (List Val)
  | 0, _, _ => .timeout
  | _ + 1, _, [] => .ok []
  | fuel + 1, s, e :: es => do
    let v ← evalExpr p fuel s e
    let vs ← evalArgs p fuel s es
    pure (v :: vs)

def execStmt (p : Prog) : Nat → State → Stmt → Res (Outcome × State)
  | 0, _, _ => .timeout
  | fuel + 1, s, st =>
    match st with
    | .skip => .ok (.normal, s)
    | .set i e => do
      let v ← evalExpr p fuel s e
      pure (.normal, { s with locals := s.locals.upd i v })
    | .store ty a e => do
      let pa ← evalExpr p fuel s a
      let v ← evalExpr p fuel s e
      guard (!s.ro)
      let m ← store s.mem ty pa v
      pure (.normal, { s with mem := m })
    | .eval e => do
      let _ ← evalExpr p fuel s e
      pure (.normal, s)
    | .call dst f args => do
      let vs ← evalArgs p fuel s args
      match p f with
      | none => .ub
      | some fn =>
        if fn.params.length = vs.length then do
          let (o, s') ← execStmt p fuel ⟨frameLocals fn.params vs, s.mem, s.ro⟩ fn.body
          let s2 : State := { s with mem := s'.mem }
          match o, dst with
          | .ret (some v), some d => pure (.normal, { s2 with locals := s2.locals.upd d v })
          | .ret _, none => pure (.normal, s2)
          | .normal, none => pure (.normal, s2)
          | _, _ => .ub
        else .ub
    | .seq a b => do
      let (o, s1) ← execStmt p fuel s a
      match o with
      | .normal => execStmt p fuel s1 b
      | o => pure (o, s1)
    | .ite c a b => do
      let vc ← evalExpr p fuel s c
      let bc ← truthy vc
      if bc then execStmt p fuel s a else execStmt p fuel s b
    | .loop body step => do
      let (o, s1) ← execStmt p fuel s body
      match o with
      | .brk => pure (.normal, s1)
      | .ret v => pure (.ret v, s1)
      | .normal | .cont => do
        let (o2, s2) ← execStmt p fuel s1 step
        match o2 with
        | .normal => execStmt p fuel s2 (.loop body step)
        | _ => .ub  -- the step of a `for` is an expression statement
    | .brk => .ok (.brk, s)
    | .cont => .ok (.cont, s)
    | .ret none => .ok (.ret none, s)
    | .ret (some e) => do
      let v ← evalExpr p fuel s e
      pure (.ret (some v), s)
end

/-- Call function `f` with argument values `args` in memory `m`. -/
def callFunc (p : Prog) (fuel : Nat) (f : Nat) (args : List Val) (m : Mem) :
    Res (Option Val × Mem) :=
  match p f with
  | none => .ub
  | some fn =>
    if fn.params.length = args.length then
      match execStmt p fuel ⟨frameLocals fn.params args, m, false⟩ fn.body with
      | .ok (.ret v, s') => .ok (v, s'.mem)
      | .ok (.normal, s') => .ok (none, s'.mem)
      | .ok _ => .ub
      | .ub => .ub
      | .timeout => .timeout
    else .ub

end Obj.C

/-
  Kernel-checked regression tests for the specification. Every `example` is
  decided by the kernel (`decide`), so a wrong verdict fails `lake build`.
  Each case mirrors a C test in tests/tester_v3_c.c.
-/
import Obj.Validate
import Obj.Glb
import Obj.C.Gen
import Obj.C.Logic
import Obj.C.Lemmas
import Obj.C.Proofs.ObjIsDigit
import Obj.C.Proofs.ObjFixIndex
import Obj.Spec
import Obj.Real
import Obj.C.Proofs.ObjDabs

namespace Obj.Tests
open Validate

def minimal : Model := {}

example : WellFormedStrict minimal := by decide

/-- tester_v3_c: check_strictness_levels, alphaMode "FOO". -/
def badAlpha : Model := { materials := [{ alphaMode := str "FOO" }] }
example : WellFormedSafe badAlpha := by decide
example : ¬ WellFormedStrict badAlpha := by decide
example : validate {} badAlpha = .ok := by decide
example : validate { strictness := .strict } badAlpha = .invalidValue := by decide

/-- camera type "foo". -/
def badCamera : Model := { cameras := [{ type := str "foo" }] }
example : validate { strictness := .strict } badCamera = .invalidValue := by decide
example : Validate.cameraMask { type := str "foo" } = bit 0 := by decide

/-- primitive mode 99. -/
def badMode : Model := { meshes := [{ primitives := [{ mode := 99 }] }] }
example : validate {} badMode = .ok := by decide
example : validate { strictness := .strict } badMode = .invalidValue := by decide

/-- metallicFactor 2.0 is out of [0,1]; NaN fails every range check. -/
example : materialMask { pbr := { metallicFactor := F64.two } } = bit 2 := by decide
example : materialMask { alphaCutoff := F64.nan } = bit 1 := by decide
example : materialMask {} = 0 := by decide

/-- byteStride 5. -/
example : bufferViewMask { buffer := 0, byteLength := 8, byteStride := 5 } = bit 1 := by decide

/-- extensionsRequired must be a subset of extensionsUsed. -/
example : modelMask { extensionsRequired := [str "EXT_x"] } = bit 0 := by decide
example : modelMask { extensionsRequired := [str "EXT_x"], extensionsUsed := [str "EXT_x"] } = 0 := by
  decide

/-- check_oob_index_rejected: out-of-range bufferView is a memory-safety error
    in every strictness mode. -/
def oobIndex : Model :=
  { buffers := [{ byteLength := 4 }],
    bufferViews := [{ buffer := 0, byteLength := 4 }],
    accessors := [{ bufferView := 1000000, componentType := CT.ubyte, count := 1, type := AT.scalar }] }
example : validate {} oobIndex = .invalidIndex := by decide
example : validate { validateIndices := false } oobIndex = .ok := by decide

/-- check_accessor_range_rejected-style case: 2 VEC3 floats need 24 bytes. -/
def accRange (bvLen : UInt64) : Model :=
  { buffers := [{ byteLength := 64 }],
    bufferViews := [{ buffer := 0, byteLength := bvLen }],
    accessors := [{ bufferView := 0, componentType := CT.float, count := 2, type := AT.vec3 }] }
example : validate {} (accRange 24) = .ok := by decide
example : validate {} (accRange 23) = .invalidAccessor := by decide

/-- Material texture indices are validated (added with tg3_validate). -/
example : validate {} { materials := [{ normalTexture := { index := 7 } }] } = .invalidIndex := by
  decide

/-! GLB framing -/

deriving instance DecidableEq for Except

def u32le (v : Nat) : List UInt8 :=
  [(v % 256).toUInt8, (v / 2^8 % 256).toUInt8, (v / 2^16 % 256).toUInt8, (v / 2^24 % 256).toUInt8]

def glbV2 (jsonLen : Nat) (declared : Nat) : List UInt8 :=
  [0x67, 0x6C, 0x54, 0x46] ++ u32le 2 ++ u32le (20 + jsonLen) ++
  u32le declared ++ u32le Glb.chunkJSON ++ List.replicate jsonLen 0x20

example : Glb.parseFrame (glbV2 8 8) =
    .ok { jsonOff := 20, jsonLen := 8, hasJson := true } := by decide +kernel
example : Glb.parseFrame (glbV2 8 12) = .error .chunk := by decide +kernel
example : Glb.parseFrame [0x67, 0x6C, 0x54, 0x46, 3, 0, 0, 0, 0, 0, 0, 0] = .error .header := by
  decide
example : Glb.layout 5 0 false = some ({ jsonOff := 20, jsonLen := 8, hasJson := true }, 28) := by
  decide


namespace Obj.Tests.ObjMiniC
open Obj.C

def isOkInt {α} (r : Res (Option Val × α)) (n : Nat) : Bool :=
  match r with
  | .ok (some (.int _ k), _) => k == n
  | _ => false

def memSpace : Mem := fun b => if b = 0 then some [32] else none

example : isOkInt (callFunc Gen.prog 50 Gen.fid_tobj_is_space
    [.int IntTy.i8 32] memSpace) 1 = true := by decide +kernel

def memDigit : Mem := fun b => if b = 0 then some [50] else none

example : isOkInt (callFunc Gen.prog 50 Gen.fid_tobj_is_digit
    [.int IntTy.i8 50] memDigit) 1 = true := by decide +kernel

example : isOkInt (callFunc Gen.prog 50 Gen.fid_tobj_is_pow2
    [.int IntTy.u64 8] memSpace) 1 = true := by decide +kernel

example : isOkInt (callFunc Gen.prog 50 Gen.fid_tobj_is_pow2
    [.int IntTy.u64 6] memSpace) 0 = true := by decide +kernel

def memFixIndex : Mem := fun b => if b = 0 then some [0, 0, 0, 0] else none

example : isOkInt (callFunc Gen.prog 100 Gen.fid_fix_index_f
    [.int IntTy.i32 5, .int IntTy.u64 10, .ptr 0 0] memFixIndex) 1 = true := by decide +kernel

example : isOkInt (callFunc Gen.prog 100 Gen.fid_fix_index_f
    [.int IntTy.i32 0, .int IntTy.u64 10, .ptr 0 0] memFixIndex) 0 = true := by decide +kernel

def memEmitFaceCore : Mem := fun b =>
  if b = 0 then some [1,0,0,0,2,0,0,0,3,0,0,0,
                      4,0,0,0,5,0,0,0,6,0,0,0,
                      7,0,0,0,8,0,0,0,9,0,0,0]
  else if b = 1 then some [0,0,0,0,1,0,0,0,2,0,0,0]
  else if b = 2 then some (List.replicate 36 0)
  else if b = 3 then some [0,0,0,0,0,0,0,0]
  else none

example : isOkInt (callFunc Gen.prog 500 Gen.fid_emit_face_core_f
    [.ptr 0 0, .ptr 1 0, .int IntTy.u32 1, .ptr 2 0, .ptr 3 0, .int IntTy.u64 3] memEmitFaceCore) 1 = true := by decide +kernel

end Obj.Tests.ObjMiniC

namespace Obj.Tests.ObjMiniC22
open Obj.C

def isOkInt {α} (r : Res (Option Val × α)) (n : Nat) : Bool :=
  match r with
  | .ok (some (.int _ k), _) => k == n
  | _ => false

def memOutBuf : Mem := fun b => if b = 0 then some [0, 0, 0, 0, 0, 0, 0, 0] else none

-- tobj_size_mul(0, 7): no overflow, returns 1
example : isOkInt (callFunc Gen.prog 100 Gen.fid_tobj_size_mul
    [.int IntTy.u64 0, .int IntTy.u64 7, .ptr 0 0] memOutBuf) 1 = true := by decide +kernel

-- tobj_size_mul(2^32, 2^32): overflow, returns 0
example : isOkInt (callFunc Gen.prog 100 Gen.fid_tobj_size_mul
    [.int IntTy.u64 4294967296, .int IntTy.u64 4294967296, .ptr 0 0] memOutBuf) 0 = true := by decide +kernel

-- tobj_size_add(1, 2): returns 1
example : isOkInt (callFunc Gen.prog 100 Gen.fid_tobj_size_add
    [.int IntTy.u64 1, .int IntTy.u64 2, .ptr 0 0] memOutBuf) 1 = true := by decide +kernel

end Obj.Tests.ObjMiniC22

namespace Obj.Tests.ObjMiniC23
open Obj.C

def isOkInt {α} (r : Res (Option Val × α)) (n : Nat) : Bool :=
  match r with
  | .ok (some (.int _ k), _) => k == n
  | _ => false

-- Address-of-local blocks (MiniC models `&local` as block 1000 + local id):
-- 1006 = cursor `c` (16 bytes), 1007 = `vi`, 1010 = `ti`, 1012 = `ni`.
-- Block 0 holds the token, block 1 is the `tobj_index` output (12 bytes).
def memCorner (tok : List UInt8) : Mem := fun b =>
  if b = 0 then some tok else
  if b = 1 then some (List.replicate 12 0) else
  if b = 1006 then some (List.replicate 16 0) else
  if b = 1007 then some [0, 0, 0, 0] else
  if b = 1010 then some [0, 0, 0, 0] else
  if b = 1012 then some [0, 0, 0, 0] else none

-- "1/2/3": v=1, vt=2, vn=3 with 10 entries each -> parse succeeds (returns 1)
example : isOkInt (callFunc Gen.prog 100000 Gen.fid_parse_corner_n_f
    [.ptr 0 0, .int IntTy.u64 5, .int IntTy.u64 10, .int IntTy.u64 10, .int IntTy.u64 10, .ptr 1 0]
    (memCorner [49, 47, 50, 47, 51])) 1 = true := by decide +kernel

-- "0": a zero index is invalid, so parse reports failure (returns 0)
example : isOkInt (callFunc Gen.prog 100000 Gen.fid_parse_corner_n_f
    [.ptr 0 0, .int IntTy.u64 1, .int IntTy.u64 10, .int IntTy.u64 10, .int IntTy.u64 10, .ptr 1 0]
    (memCorner [48])) 0 = true := by decide +kernel

end Obj.Tests.ObjMiniC23

namespace Obj.Tests.ObjMiniC24
open Obj.C Obj

/-- Run `parse_corner_n_f` on a token; returns (return flag, 12-byte out block). -/
def runCorner (tok : List UInt8) (nv nvt nvn : Nat) : Option (Nat × Block) :=
  match callFunc Gen.prog 100000 Gen.fid_parse_corner_n_f
      [.ptr 0 0, .int IntTy.u64 tok.length, .int IntTy.u64 nv, .int IntTy.u64 nvt,
       .int IntTy.u64 nvn, .ptr 1 0] (ObjMiniC23.memCorner tok) with
  | .ok (v, m) =>
    match v, m 1 with
    | some (.int _ k), some b => some (k, b)
    | _, _ => none
  | _ => none

/-- Expected out block: `vertex_index` at 0, `normal_index` at 4, `texcoord_index` at 8. -/
def expBlock (v n t : Int) : Block :=
  encodeLE 4 (IntTy.wrap IntTy.i32 v) ++ encodeLE 4 (IntTy.wrap IntTy.i32 n) ++
    encodeLE 4 (IntTy.wrap IntTy.i32 t)

example : runCorner [49] 10 10 10 = some (1, expBlock (storedIndex 1 10) (-1) (-1)) := by
  decide +kernel
example : runCorner [49, 47, 50, 47, 51] 10 10 10 =
    some (1, expBlock (storedIndex 1 10) (storedIndex 3 10) (storedIndex 2 10)) := by
  decide +kernel
example : runCorner [49, 47, 50] 10 10 10 =
    some (1, expBlock (storedIndex 1 10) (-1) (storedIndex 2 10)) := by
  decide +kernel
example : runCorner [49, 47, 47, 51] 10 10 10 =
    some (1, expBlock (storedIndex 1 10) (storedIndex 3 10) (-1)) := by
  decide +kernel
example : runCorner [45, 49, 47, 45, 50, 47, 45, 51] 10 10 10 =
    some (1, expBlock (storedIndex (-1) 10) (storedIndex (-3) 10) (storedIndex (-2) 10)) := by
  decide +kernel
example : runCorner [48] 10 10 10 = some (0, expBlock (-1) (-1) (-1)) := by
  decide +kernel
example : runCorner [53] 3 3 3 = some (1, expBlock (storedIndex 5 3) (-1) (-1)) := by
  decide +kernel
example : runCorner [45, 53] 3 3 3 = some (0, expBlock (-1) (-1) (-1)) := by
  decide +kernel

end Obj.Tests.ObjMiniC24

namespace Obj.Tests.ObjMiniC25
open Obj.C Obj

/-- Run the translated integer scanner with its `pp` parameter in block 1000.
    Return flag, output bytes, and the final cursor offset. -/
def runScanInt (tok : List UInt8) (pos : Nat := 0) : Option (Nat × Block × Nat) :=
  let m : Mem := fun b =>
    if b = 0 then some tok else
    if b = 1 then some [0, 0, 0, 0] else
    if b = 1000 then some (encodeLE 8 (ptrPack (.ptr 0 pos))) else none
  match callFunc Gen.prog 100000 Gen.fid_tobj_scan_int
      [.ptr 1000 0, .ptr 0 tok.length, .ptr 1 0] m with
  | .ok (v, m') =>
    match v, m' 1, m' 1000 with
    | some (.int _ k), some out, some p =>
      match ptrUnpack (decodeLE p) with
      | .ptr 0 off => some (k, out, off)
      | _ => none
    | _, _, _ => none
  | _ => none

/-- Projection of the pure scanner model to the C return value and output
    representation. `none` means the output argument is left untouched. -/
def specScanInt (tok : List UInt8) (pos : Nat := 0) : Option (Nat × Block × Nat) :=
  let (ok, value, cursor) := scanInt (tok.map UInt8.toNat) pos
  if ok then some (1, encodeLE 4 (IntTy.wrap IntTy.i32 value), cursor)
  else some (0, [0, 0, 0, 0], cursor)

example : runScanInt [32, 45, 49, 50, 120] = specScanInt [32, 45, 49, 50, 120] := by
  decide +kernel
example : runScanInt [32, 43, 120] = specScanInt [32, 43, 120] := by decide +kernel
example : runScanInt [] = specScanInt [] := by decide +kernel
example : runScanInt [9, 9, 49, 120] = specScanInt [9, 9, 49, 120] := by
  decide +kernel
example : runScanInt [120] = specScanInt [120] := by decide +kernel
example : runScanInt [120, 32, 45, 52, 50, 33] 2 =
    specScanInt [120, 32, 45, 52, 50, 33] 2 := by decide +kernel
example : runScanInt [120, 9, 43, 120] 1 =
    specScanInt [120, 9, 43, 120] 1 := by decide +kernel
example : runScanInt [57, 57, 57, 57, 57, 57, 57, 57, 57, 57] =
    specScanInt [57, 57, 57, 57, 57, 57, 57, 57, 57, 57] := by decide +kernel
example : runScanInt [45, 57, 57, 57, 57, 57, 57, 57, 57, 57] =
    specScanInt [45, 57, 57, 57, 57, 57, 57, 57, 57, 57] := by decide +kernel
end Obj.Tests.ObjMiniC25

namespace Obj.Tests.ObjMiniC26
open Obj.C Obj

/-- Run translated `tobj_next_token`; successful output includes token start
    and length, while failure leaves the token output absent. -/
def runNextToken (bytes : List UInt8) (pos : Nat := 0) :
    Option ((Option (Nat × Nat)) × Nat) :=
  let cursor := encodeLE 8 (ptrPack (.ptr 0 pos)) ++ encodeLE 8 (ptrPack (.ptr 0 bytes.length))
  let m : Mem := fun b =>
    if b = 0 then some bytes else
    if b = 1000 then some cursor else
    if b = 1001 then some (List.replicate 8 0) else
    if b = 1002 then some (List.replicate 8 0) else none
  match callFunc Gen.prog 100000 Gen.fid_tobj_next_token
      [.ptr 1000 0, .ptr 1001 0, .ptr 1002 0] m with
  | .ok (v, m') =>
    match v, m' 1000, m' 1001, m' 1002 with
    | some (.int _ k), some c, some t, some l =>
      match ptrUnpack (decodeLE (c.take 8)) with
      | .ptr 0 next =>
        if k = 0 then some (none, next)
        else match ptrUnpack (decodeLE t) with
          | .ptr 0 start => some (some (start, decodeLE l), next)
          | _ => none
      | _ => none
    | _, _, _, _ => none
  | _ => none

def specNextToken (bytes : List UInt8) (pos : Nat := 0) :
    Option ((Option (Nat × Nat)) × Nat) :=
  some (nextToken (bytes.map UInt8.toNat) pos)

example : runNextToken [32, 32, 97, 98, 32, 99] =
    specNextToken [32, 32, 97, 98, 32, 99] := by decide +kernel
example : runNextToken [32, 9, 32] = specNextToken [32, 9, 32] := by decide +kernel
example : runNextToken [120, 32, 97] 1 = specNextToken [120, 32, 97] 1 := by decide +kernel
example : evalBin .sub (some IntTy.i64) (.ptr 7 5) (.ptr 7 2) =
    .ok (.int IntTy.i64 3) := by rfl
example : evalBin .sub (some IntTy.i64) (.ptr 7 5) (.ptr 8 2) = .ub := by rfl

end Obj.Tests.ObjMiniC26

namespace Obj.Tests.ObjMiniC27
open Obj.C
open Obj

/-- Concrete MiniC state for one digit iteration of `tobj_scan_int_loop0`:
    the input byte is `'7'`, `v` is 12, and saturation has not occurred. -/
def scanLoopState (byte : UInt8) (initial : Nat) (saturated : Bool) : State :=
  { locals := fun i =>
      if i = 1 then some (.ptr 20 1) else
      if i = 3 then some (.ptr 20 0) else
      if i = 5 then some (.int IntTy.i64 initial) else
      if i = 6 then some (.int IntTy.u8 (if saturated then 1 else 0)) else none,
    mem := fun b => if b = 20 then some [byte, 0] else none,
    ro := false }

/-- Scanner state over an arbitrary byte block and cursor.  This is the state
    shape needed to lift one-step proofs from a sample byte to a whole input. -/
def scanLoopStateAt (bytes : Block) (cursor endpoint initial : Nat)
    (saturated : Bool) : State :=
  { locals := fun i =>
      if i = 1 then some (.ptr 20 endpoint) else
      if i = 3 then some (.ptr 20 cursor) else
      if i = 5 then some (.int IntTy.i64 initial) else
      if i = 6 then some (.int IntTy.u8 (if saturated then 1 else 0)) else none,
    mem := fun b => if b = 20 then some bytes else none,
    ro := false }

/-- State shape for the generated leading-space loop. -/
def scanSkipSpaceStateAt (bytes : Block) (cursor endpoint : Nat)
    (frame : Mem := fun _ => none) : State :=
  { locals := (frameLocals [0, 1] [.ptr 20 0, .ptr 20 endpoint]).upd
      2 (.ptr 20 cursor),
    mem := fun b => if b = 20 then some bytes else frame b,
    ro := false }

def scanSkipSpaceGuard : Expr :=
  .land (.bin .lt (some IntTy.u64) (.var 2) (.var 1))
    (.cast IntTy.i32 (.call 6 [.load (.int IntTy.i8) (.var 2)]))

def scanSkipSpaceIterationBody : Stmt :=
  .ite scanSkipSpaceGuard
    (.set 2 (.index (.var 2) (.const (.int IntTy.i64 1)) 1)) .brk

def scanSkipSpaceLoop : Stmt := .loop scanSkipSpaceIterationBody .skip

theorem scanSkipSpace_ast_factor :
    Gen.tobj_skip_space_loop0 = scanSkipSpaceLoop := rfl

/-- At an in-bounds cursor, the generalized scanner state's byte load returns
    the byte stored at that offset. -/
theorem scanLoop_load_byte_at (bytes : Block) (cursor endpoint initial : Nat)
    (saturated : Bool) (byte : UInt8)
    (hcursor : cursor < bytes.length)
    (hbyte : bytes[cursor]? = some byte) :
    load (scanLoopStateAt bytes cursor endpoint initial saturated).mem
      (.int IntTy.i8) (.ptr 20 cursor) = .ok (.int IntTy.i8 byte.toNat) := by
  have hdrop : bytes.drop cursor = byte :: bytes.drop (cursor + 1) := by
    rw [List.drop_eq_getElem_cons hcursor]
    rw [List.getElem?_eq_some_iff] at hbyte
    rcases hbyte with ⟨hvalid, hvalue⟩
    rw [hvalue]
  have hroom : cursor + 1 ≤ bytes.length := by omega
  simp [scanLoopStateAt, load, readBytes, hdrop, hroom, decodeLE,
    Ty.size, IntTy.bytes, IntTy.i8]

/-- Load an in-bounds byte from any memory containing the scanner block. -/
theorem scanLoop_load_byte_from_mem (mem : Mem) (bytes : Block)
    (cursor : Nat) (byte : UInt8) (hmem : mem 20 = some bytes)
    (hcursor : cursor < bytes.length)
    (hbyte : bytes[cursor]? = some byte) :
    load mem (.int IntTy.i8) (.ptr 20 cursor) =
      .ok (.int IntTy.i8 byte.toNat) := by
  have hdrop : bytes.drop cursor = byte :: bytes.drop (cursor + 1) := by
    rw [List.drop_eq_getElem_cons hcursor]
    rw [List.getElem?_eq_some_iff] at hbyte
    rcases hbyte with ⟨hvalid, hvalue⟩
    rw [hvalue]
  have hroom : cursor + 1 ≤ bytes.length := by omega
  simp [load, readBytes, hmem, hdrop, hroom, decodeLE,
    Ty.size, IntTy.bytes, IntTy.i8]

/-- The leading-space loop's in-bounds load agrees with the same byte in its
    memory block. -/
theorem scanSkipSpace_load_byte_at (bytes : Block) (cursor endpoint : Nat)
    (byte : UInt8) (hcursor : cursor < bytes.length)
    (hbyte : bytes[cursor]? = some byte)
    (frame : Mem := fun _ => none) :
    load (scanSkipSpaceStateAt bytes cursor endpoint frame).mem
      (.int IntTy.i8) (.ptr 20 cursor) = .ok (.int IntTy.i8 byte.toNat) := by
  apply scanLoop_load_byte_from_mem _ bytes cursor byte ?_ hcursor hbyte
  simp [scanSkipSpaceStateAt]

/-- The translated whitespace predicate returns true for a space or tab byte
    loaded from any in-bounds scanner buffer. -/
theorem scanSkipSpace_call_true_at (bytes : Block) (cursor endpoint : Nat)
    (byte : UInt8) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hspace : byte.toNat = 9 ∨ byte.toNat = 32)
    (frame : Mem := fun _ => none) :
    EvE Gen.prog (scanSkipSpaceStateAt bytes cursor endpoint frame)
      (.cast IntTy.i32 (.call 6 [.load (.int IntTy.i8) (.var 2)]))
      (.int IntTy.i32 1) := by
  let s := scanSkipSpaceStateAt bytes cursor endpoint frame
  let loc := frameLocals [0] [.int IntTy.i8 byte.toNat]
  have hwrap : IntTy.wrap IntTy.i8 (byte.toNat : Int) = byte.toNat := by
    rcases hspace with htab | hspace
    · simp [IntTy.wrap, IntTy.modulus, IntTy.i8, htab]
    · simp [IntTy.wrap, IntTy.modulus, IntTy.i8, hspace]
  have hlocal : loc 0 = some (.int IntTy.i8
      (IntTy.wrap IntTy.i8 (byte.toNat : Int))) := by
    simp [loc, frameLocals, hwrap]
  have hSpace : ExS Gen.prog ⟨loc, s.mem, true⟩ Gen.tobj_is_space.body
      (.ret (some (.int IntTy.u8 1))) ⟨loc, s.mem, true⟩ := by
    rcases hspace with htab | hspace
    · have hlocal' := hlocal
      rw [hwrap] at hlocal'
      exact Obj.C.Proofs.tobj_is_space_tab loc s.mem (ro := true) (by
        simpa [htab] using hlocal')
    · have hlocal' := hlocal
      rw [hwrap] at hlocal'
      exact Obj.C.Proofs.tobj_is_space_space loc s.mem (ro := true) (by
        simpa [hspace] using hlocal')
  have hp : EvE Gen.prog s (.var 2) (.ptr 20 cursor) := by
    apply EvE.var
    simp [s, scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?_cons]
  have hload : EvE Gen.prog s (.load (.int IntTy.i8) (.var 2))
      (.int IntTy.i8 byte.toNat) := by
    apply EvE.load hp
    exact scanSkipSpace_load_byte_at bytes cursor endpoint byte hcursor hbyteAt frame
  have hargs : EvArgs Gen.prog s [.load (.int IntTy.i8) (.var 2)]
      [.int IntTy.i8 byte.toNat] := EvArgs.cons hload EvArgs.nil
  have hcall : EvE Gen.prog s (.call 6 [.load (.int IntTy.i8) (.var 2)])
      (.int IntTy.u8 1) := by
    simpa [loc] using (EvE.call hargs (by rfl) (by rfl) hSpace)
  have hcast : evalCast IntTy.i32 (.int IntTy.u8 1) =
      .ok (.int IntTy.i32 1) := by
    simp [evalCast, IntTy.u8, IntTy.i32, IntTy.modulus]
  exact EvE.cast hcall hcast

/-- The translated whitespace predicate returns false for every non-space
    byte, including bytes whose signed i8 promotion is negative. -/
theorem scanSkipSpace_call_false_at (bytes : Block) (cursor endpoint : Nat)
    (byte : UInt8) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hnotspace : scanSpace byte.toNat = false)
    (frame : Mem := fun _ => none) :
    EvE Gen.prog (scanSkipSpaceStateAt bytes cursor endpoint frame)
      (.cast IntTy.i32 (.call 6 [.load (.int IntTy.i8) (.var 2)]))
      (.int IntTy.i32 0) := by
  let s := scanSkipSpaceStateAt bytes cursor endpoint frame
  let c : Int := IntTy.toInt IntTy.i8 byte.toNat
  have hbyteRange : byte.toNat < 256 := by
    have h := UInt8.toNat_lt byte
    omega
  have hrange : IntTy.inRange IntTy.i8 c = true := by
    by_cases hhigh : 128 ≤ byte.toNat
    · simp [c, IntTy.toInt, IntTy.modulus, IntTy.inRange, IntTy.minVal,
        IntTy.maxVal, IntTy.i8, hhigh]
      omega
    · have hlow : byte.toNat < 128 := by omega
      simp [c, IntTy.toInt, IntTy.modulus, IntTy.inRange, IntTy.minVal,
        IntTy.maxVal, IntTy.i8, hlow, hhigh]
      omega
  have hwrap : IntTy.wrap IntTy.i8 c = byte.toNat := by
    by_cases hsmall : byte.toNat < 128
    · have hc : c = byte.toNat := by
        have hnohigh : ¬ 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hnohigh]
      rw [hc]
      simp only [IntTy.wrap, IntTy.modulus, IntTy.i8]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      simp
    · have hc : c = (byte.toNat : Int) - 256 := by
        have hhigh : 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hhigh]
      rw [hc]
      simp only [IntTy.wrap, IntTy.modulus, IntTy.i8]
      change (((byte.toNat : Int) - 256) % (256 : Int)).toNat = byte.toNat
      have hmod : ((byte.toNat : Int) - 256) % (256 : Int) = byte.toNat := by
        have hmod := Int.emod_add_emod (-256) (256 : Int) (byte.toNat : Int)
        have hz : (-256 : Int) % 256 = 0 := by decide
        have hlt : 0 ≤ (byte.toNat : Int) := by omega
        have hlt2 : (byte.toNat : Int) < 256 := by omega
        have hnat : (byte.toNat : Int) % 256 = byte.toNat :=
          Int.emod_eq_of_lt hlt hlt2
        rw [hz] at hmod
        have hleft : (0 + (byte.toNat : Int)) % 256 = byte.toNat := by
          simpa using hnat
        rw [hleft] at hmod
        simpa [Int.sub_eq_add_neg, Int.add_comm] using hmod.symm
      rw [hmod]
      simp
  have h32 : c ≠ 32 := by
    by_cases hsmall : byte.toNat < 128
    · have hc : c = byte.toNat := by
        have hnohigh : ¬ 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hnohigh]
      intro heq
      have hraw : byte.toNat = 32 := by omega
      simp [scanSpace, hraw] at hnotspace
    · have hhigh : 128 ≤ byte.toNat := by omega
      simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hhigh]
      omega
  have h9 : c ≠ 9 := by
    by_cases hsmall : byte.toNat < 128
    · have hc : c = byte.toNat := by
        have hnohigh : ¬ 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hnohigh]
      intro heq
      have hraw : byte.toNat = 9 := by omega
      simp [scanSpace, hraw] at hnotspace
    · have hhigh : 128 ≤ byte.toNat := by omega
      simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hhigh]
      omega
  let loc := frameLocals [0] [.int IntTy.i8 byte.toNat]
  have hlocal : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c)) := by
    simp [loc, frameLocals, hwrap]
  have hSpace : ExS Gen.prog ⟨loc, s.mem, true⟩ Gen.tobj_is_space.body
      (.ret (some (.int IntTy.u8 0))) ⟨loc, s.mem, true⟩ :=
    Obj.C.Proofs.tobj_is_space_other loc s.mem c (ro := true) hrange h32 h9 hlocal
  have hp : EvE Gen.prog s (.var 2) (.ptr 20 cursor) := by
    apply EvE.var
    simp [s, scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?_cons]
  have hload : EvE Gen.prog s (.load (.int IntTy.i8) (.var 2))
      (.int IntTy.i8 byte.toNat) := by
    apply EvE.load hp
    exact scanSkipSpace_load_byte_at bytes cursor endpoint byte hcursor hbyteAt frame
  have hargs : EvArgs Gen.prog s [.load (.int IntTy.i8) (.var 2)]
      [.int IntTy.i8 byte.toNat] := EvArgs.cons hload EvArgs.nil
  have hcall : EvE Gen.prog s (.call 6 [.load (.int IntTy.i8) (.var 2)])
      (.int IntTy.u8 0) := by
    simpa [loc] using (EvE.call hargs (by rfl) (by rfl) hSpace)
  have hcast : evalCast IntTy.i32 (.int IntTy.u8 0) =
      .ok (.int IntTy.i32 0) := by
    simp [evalCast, IntTy.u8, IntTy.i32, IntTy.modulus]
  exact EvE.cast hcall hcast

/-- A non-space byte before the endpoint makes the generated whitespace-loop
    guard false. -/
theorem scanSkipSpace_guard_false_at (bytes : Block) (cursor endpoint : Nat)
    (byte : UInt8) (hcursor : cursor < endpoint)
    (hbyteAt : bytes[cursor]? = some byte)
    (hnotspace : scanSpace byte.toNat = false)
    (frame : Mem := fun _ => none) :
    EvE Gen.prog (scanSkipSpaceStateAt bytes cursor endpoint frame)
      scanSkipSpaceGuard (boolVal false) := by
  let s := scanSkipSpaceStateAt bytes cursor endpoint frame
  have hp : EvE Gen.prog s (.var 2) (.ptr 20 cursor) := by
    apply EvE.var
    simp [s, scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?_cons]
  have he : EvE Gen.prog s (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [s, scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?_cons]
  have hptr : EvE Gen.prog s
      (.bin .lt (some IntTy.u64) (.var 2) (.var 1)) (boolVal true) := by
    apply EvE.bin hp he
    simp [evalBin, isPtr, boolVal]
    omega
  have ht : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hcall := scanSkipSpace_call_false_at bytes cursor endpoint byte
    ((List.getElem?_eq_some_iff.mp hbyteAt).choose) hbyteAt hnotspace frame
  have hf : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  exact EvE.land_true hptr ht hcall hf

/-- When an in-bounds byte is space or tab and the cursor is before the end,
    the generated leading-space loop guard succeeds. -/
theorem scanSkipSpace_guard_true_at (bytes : Block) (cursor endpoint : Nat)
    (byte : UInt8) (hcursor : cursor < endpoint)
    (hbyteAt : bytes[cursor]? = some byte)
    (hspace : byte.toNat = 9 ∨ byte.toNat = 32)
    (frame : Mem := fun _ => none) :
    EvE Gen.prog (scanSkipSpaceStateAt bytes cursor endpoint frame)
      scanSkipSpaceGuard (boolVal true) := by
  let s := scanSkipSpaceStateAt bytes cursor endpoint frame
  have hp : EvE Gen.prog s (.var 2) (.ptr 20 cursor) := by
    apply EvE.var
    simp [s, scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?_cons]
  have he : EvE Gen.prog s (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [s, scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?_cons]
  have hptr : EvE Gen.prog s
      (.bin .lt (some IntTy.u64) (.var 2) (.var 1)) (boolVal true) := by
    apply EvE.bin hp he
    simp [evalBin, isPtr, boolVal]
    omega
  have ht : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hcall := scanSkipSpace_call_true_at bytes cursor endpoint byte
    ((List.getElem?_eq_some_iff.mp hbyteAt).choose) hbyteAt hspace frame
  exact EvE.land_true hptr ht hcall (by simp [truthy, boolVal])

/-- One in-bounds increment of the leading-space loop's pointer local. -/
theorem scanSkipSpace_cursor_advance_exs (s : State) (cursor : Nat) (blk : Block)
    (hcursor : s.locals 2 = some (.ptr 20 cursor))
    (hmem : s.mem 20 = some blk) (hbound : cursor + 1 ≤ blk.length) :
    ExS Gen.prog s (.set 2 (.index (.var 2) (.const (.int IntTy.i64 1)) 1))
      .normal { s with locals := Locals.upd s.locals 2 (.ptr 20 (cursor + 1)) } := by
  have hp : EvE Gen.prog s (.var 2) (.ptr 20 cursor) := EvE.var hcursor
  have hi : EvE Gen.prog s (.const (.int IntTy.i64 1)) (.int IntTy.i64 1) := EvE.const _
  have hptr : ptrAdd s.mem (.ptr 20 cursor) (IntTy.i64.toInt 1) =
      .ok (.ptr 20 (cursor + 1)) := by
    simp [ptrAdd, hmem, IntTy.toInt, IntTy.i64]
    omega
  exact ExS.set (EvE.index hp hi hptr)

/-- One complete whitespace-loop iteration consumes one space or tab byte. -/
theorem scanSkipSpace_iteration_at (bytes : Block) (cursor endpoint : Nat)
    (byte : UInt8) (hcursor : cursor < endpoint)
    (hnext : cursor + 1 ≤ bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hspace : byte.toNat = 9 ∨ byte.toNat = 32)
    (frame : Mem := fun _ => none) :
    ExS Gen.prog (scanSkipSpaceStateAt bytes cursor endpoint frame)
      scanSkipSpaceIterationBody .normal
      { scanSkipSpaceStateAt bytes cursor endpoint frame with
        locals := Locals.upd (scanSkipSpaceStateAt bytes cursor endpoint frame).locals
          2 (.ptr 20 (cursor + 1)) } := by
  let s := scanSkipSpaceStateAt bytes cursor endpoint frame
  have hguard := scanSkipSpace_guard_true_at bytes cursor endpoint byte
    hcursor hbyteAt hspace frame
  have htrue : truthy (boolVal true) = .ok true := by rfl
  have hlocal : s.locals 2 = some (.ptr 20 cursor) := by
    simp [s, scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?_cons]
  have hmem : s.mem 20 = some bytes := by simp [s, scanSkipSpaceStateAt]
  have hinc := scanSkipSpace_cursor_advance_exs s cursor bytes hlocal hmem hnext
  exact ExS.ite hguard htrue hinc

/-- At a non-space byte before the endpoint, the whitespace loop breaks
    without changing its pointer. -/
theorem scanSkipSpace_break_at_nonspace (bytes : Block) (cursor endpoint : Nat)
    (byte : UInt8) (hcursor : cursor < endpoint)
    (hbyteAt : bytes[cursor]? = some byte)
    (hnotspace : scanSpace byte.toNat = false)
    (frame : Mem := fun _ => none) :
    ExS Gen.prog (scanSkipSpaceStateAt bytes cursor endpoint frame)
      scanSkipSpaceIterationBody .brk (scanSkipSpaceStateAt bytes cursor endpoint frame) := by
  let s := scanSkipSpaceStateAt bytes cursor endpoint frame
  have hguard := scanSkipSpace_guard_false_at bytes cursor endpoint byte
    hcursor hbyteAt hnotspace frame
  have hf : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  simpa [scanSkipSpaceIterationBody, s] using
    (ExS.ite hguard hf ExS.brk : ExS Gen.prog s
      (.ite scanSkipSpaceGuard
        (.set 2 (.index (.var 2) (.const (.int IntTy.i64 1)) 1)) .brk)
      .brk s)

/-- At the end pointer the whitespace loop also breaks. -/
theorem scanSkipSpace_break_at_endpoint (bytes : Block) (endpoint : Nat)
    (frame : Mem := fun _ => none) :
    ExS Gen.prog (scanSkipSpaceStateAt bytes endpoint endpoint frame)
      scanSkipSpaceIterationBody .brk (scanSkipSpaceStateAt bytes endpoint endpoint frame) := by
  let s := scanSkipSpaceStateAt bytes endpoint endpoint frame
  have hp : EvE Gen.prog s (.var 2) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [s, scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?_cons]
  have he : EvE Gen.prog s (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [s, scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?_cons]
  have hptr : EvE Gen.prog s
      (.bin .lt (some IntTy.u64) (.var 2) (.var 1)) (boolVal false) := by
    apply EvE.bin hp he
    simp [evalBin, isPtr, boolVal]
  have hf : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hguard : EvE Gen.prog s scanSkipSpaceGuard (boolVal false) :=
    EvE.land_false hptr hf
  simpa [scanSkipSpaceIterationBody, s] using
    (ExS.ite hguard hf ExS.brk : ExS Gen.prog s
      (.ite scanSkipSpaceGuard
        (.set 2 (.index (.var 2) (.const (.int IntTy.i64 1)) 1)) .brk)
      .brk s)

/-- The bytes before the stopping cursor are all spaces or tabs. -/
def scanSkipSpaceFrom (bytes : Block) (cursor count : Nat) : Prop :=
  ∀ offset, offset < count → ∃ byte, bytes[cursor + offset]? = some byte ∧
    scanSpace byte.toNat = true

/-- Every byte in the maximal whitespace prefix has the expected indexed
    witness. -/
theorem scanSkipSpace_takeWhile_bytes (bytes : Block) (cursor : Nat) :
    scanSkipSpaceFrom bytes cursor
      ((bytes.drop cursor).takeWhile (fun byte => scanSpace byte.toNat)).length := by
  let pred := fun byte : UInt8 => scanSpace byte.toNat
  have hprefix : ∀ (xs : List UInt8) offset,
      offset < (xs.takeWhile pred).length →
        ∃ byte, xs[offset]? = some byte ∧ pred byte = true := by
    intro xs
    induction xs with
    | nil => intro offset h; simp at h
    | cons head tail ih =>
      intro offset hoff
      rw [List.takeWhile_cons] at hoff
      by_cases hp : pred head = true
      · rw [if_pos hp, List.length_cons] at hoff
        cases offset with
        | zero => exact ⟨head, by simp, hp⟩
        | succ offset =>
          have htail : offset < (tail.takeWhile pred).length := by omega
          obtain ⟨byte, hbyte, hpred⟩ := ih offset htail
          exact ⟨byte, by simpa using hbyte, hpred⟩
      · rw [if_neg hp] at hoff
        simp at hoff
  intro offset hoff
  obtain ⟨byte, hbyte, hspace⟩ := hprefix (bytes.drop cursor) offset hoff
  refine ⟨byte, ?_, hspace⟩
  simpa only [List.getElem?_drop] using hbyte

/-- The byte following a finite `takeWhile` prefix fails its predicate. -/
theorem scanSkipSpace_takeWhile_boundary (xs : List UInt8)
    (hlen : (xs.takeWhile (fun byte => scanSpace byte.toNat)).length < xs.length) :
    ∃ byte, xs[(xs.takeWhile (fun byte => scanSpace byte.toNat)).length]? =
      some byte ∧ scanSpace byte.toNat = false := by
  let pred := fun byte : UInt8 => scanSpace byte.toNat
  have hboundary : ∀ (xs : List UInt8),
      (xs.takeWhile pred).length < xs.length →
        ∃ byte, xs[(xs.takeWhile pred).length]? = some byte ∧ pred byte = false := by
    intro xs
    induction xs with
    | nil => intro h; simp at h
    | cons head tail ih =>
      intro h
      rw [List.takeWhile_cons] at h
      by_cases hp : pred head = true
      · rw [if_pos hp, List.length_cons, List.length_cons] at h
        have htail : (tail.takeWhile pred).length < tail.length := by omega
        obtain ⟨byte, hbyte, hfalse⟩ := ih htail
        refine ⟨byte, ?_, hfalse⟩
        have hlen : ((head :: tail).takeWhile pred).length =
            (tail.takeWhile pred).length + 1 := by simp [List.takeWhile_cons, hp]
        rw [hlen, List.getElem?_cons_succ]
        exact hbyte
      · rw [if_neg hp] at h
        have hfalse : pred head = false := Bool.eq_false_iff.mpr hp
        refine ⟨head, ?_, hfalse⟩
        have hnil : (head :: tail).takeWhile pred = [] := by
          simp [List.takeWhile_cons, hp]
        simp [hnil]
  simpa [pred] using hboundary xs hlen

def scanSkipSpaceInvariant (bytes : Block) (endpoint stop k : Nat) (s : State)
    (frame : Mem := fun _ => none) : Prop :=
  ∃ cursor, cursor + k = stop ∧
    s = scanSkipSpaceStateAt bytes cursor endpoint frame ∧
      scanSkipSpaceFrom bytes cursor k

/-- A whitespace prefix with an endpoint or first non-space boundary gives a
    terminating generated leading-space loop at the boundary cursor. -/
theorem scanSkipSpace_terminates_prefix (bytes : Block) (endpoint start stop : Nat)
    (hstart : start ≤ stop) (hstop : stop ≤ endpoint)
    (hend : endpoint ≤ bytes.length)
    (hboundary : stop = endpoint ∨ (stop < endpoint ∧ ∃ byte,
      bytes[stop]? = some byte ∧ scanSpace byte.toNat = false))
    (hprefix : scanSkipSpaceFrom bytes start (stop - start))
    (frame : Mem := fun _ => none) :
    ∃ finalState, ExS Gen.prog (scanSkipSpaceStateAt bytes start endpoint frame)
      Gen.tobj_skip_space_loop0 .normal finalState ∧
      finalState = scanSkipSpaceStateAt bytes stop endpoint frame := by
  let P := fun k s => scanSkipSpaceInvariant bytes endpoint stop k s frame
  let Q := fun state => state = scanSkipSpaceStateAt bytes stop endpoint frame
  have hinv : P (stop - start) (scanSkipSpaceStateAt bytes start endpoint frame) := by
    refine ⟨start, ?_, rfl, hprefix⟩
    omega
  have hstep : ∀ k state, P (k + 1) state → ∃ s1 s2,
      ExS Gen.prog state scanSkipSpaceIterationBody .normal s1 ∧
      ExS Gen.prog s1 .skip .normal s2 ∧ P k s2 := by
    intro k state hs
    obtain ⟨cursor, hpos, rfl, hspaces⟩ := hs
    obtain ⟨byte, hbyteAt, hspace⟩ := hspaces 0 (by omega)
    have hbyteAt' : bytes[cursor]? = some byte := by simpa using hbyteAt
    have hcursor : cursor < endpoint := by omega
    have hnext : cursor + 1 ≤ bytes.length := by
      have hget := (List.getElem?_eq_some_iff.mp hbyteAt).choose
      omega
    have hspaceCases : byte.toNat = 9 ∨ byte.toNat = 32 := by
      simp [scanSpace] at hspace
      omega
    have hiter := scanSkipSpace_iteration_at bytes cursor endpoint byte
      hcursor hnext hbyteAt' hspaceCases frame
    let s2 := { scanSkipSpaceStateAt bytes cursor endpoint frame with
      locals := Locals.upd (scanSkipSpaceStateAt bytes cursor endpoint frame).locals
        2 (.ptr 20 (cursor + 1)) }
    have hstate2 : s2 = scanSkipSpaceStateAt bytes (cursor + 1) endpoint frame := by
      rw [State.mk.injEq]
      constructor
      · funext i
        by_cases hi1 : i = 1
        · subst i
          simp [s2, scanSkipSpaceStateAt, Locals.upd]
        · by_cases hi2 : i = 2
          · subst i
            simp [s2, scanSkipSpaceStateAt, Locals.upd]
          · simp [s2, scanSkipSpaceStateAt, Locals.upd, hi1, hi2]
      constructor
      · funext b
        by_cases hb : b = 20 <;> simp [s2, scanSkipSpaceStateAt, hb]
      · rfl
    have hspaces' : scanSkipSpaceFrom bytes (cursor + 1) k := by
      intro offset hoff
      obtain ⟨b, hbAt, hbspace⟩ := hspaces (offset + 1) (by omega)
      refine ⟨b, ?_, hbspace⟩
      have hidx : cursor + 1 + offset = cursor + (offset + 1) := by omega
      rw [hidx]
      exact hbAt
    refine ⟨s2, s2, ?_, ExS.skip, ?_⟩
    · simpa [scanSkipSpaceIterationBody, s2] using hiter
    · refine ⟨cursor + 1, ?_, hstate2, hspaces'⟩
      omega
  have hexit : ∀ state, P 0 state → ∃ s1,
      ExS Gen.prog state scanSkipSpaceIterationBody .brk s1 ∧ Q s1 := by
    intro state hs
    obtain ⟨cursor, hpos, rfl, _⟩ := hs
    have hcursorStop : cursor = stop := by omega
    subst cursor
    rcases hboundary with hboundary | ⟨hcursor, byte, hbyteAt, hnotspace⟩
    · subst endpoint
      refine ⟨scanSkipSpaceStateAt bytes stop stop frame,
        scanSkipSpace_break_at_endpoint bytes stop frame, rfl⟩
    · refine ⟨scanSkipSpaceStateAt bytes stop endpoint frame,
        scanSkipSpace_break_at_nonspace bytes stop endpoint byte hcursor hbyteAt
          hnotspace frame, rfl⟩
  obtain ⟨finalState, hloop, hpost⟩ :=
    ExS.loop_decreasing_post hinv hstep hexit
  exact ⟨finalState, by
    simpa [P, scanSkipSpace_ast_factor, scanSkipSpaceLoop,
      scanSkipSpaceIterationBody, scanSkipSpaceGuard] using hloop, hpost⟩

/-- Instantiate the whitespace-loop proof with the pure maximal
    `takeWhile scanSpace` prefix of an arbitrary byte buffer. -/
theorem scanSkipSpace_terminates_takeWhile (bytes : Block) (start : Nat)
    (hstart : start ≤ bytes.length) (frame : Mem := fun _ => none) :
    ∃ finalState, ExS Gen.prog (scanSkipSpaceStateAt bytes start bytes.length frame)
      Gen.tobj_skip_space_loop0 .normal finalState ∧
      finalState = scanSkipSpaceStateAt bytes
        (start + ((bytes.drop start).takeWhile
          (fun byte => scanSpace byte.toNat)).length) bytes.length frame := by
  let suffix := bytes.drop start
  let spacePrefix := suffix.takeWhile (fun byte => scanSpace byte.toNat)
  let stop := start + spacePrefix.length
  have hdropLen : suffix.length = bytes.length - start := by simp [suffix]
  have hprefixList : spacePrefix <+: suffix := List.takeWhile_prefix _
  have hprefixLen : spacePrefix.length ≤ suffix.length := hprefixList.length_le
  have hstop : stop ≤ bytes.length := by dsimp [stop]; omega
  have hstartStop : start ≤ stop := by dsimp [stop]; omega
  have hprefix : scanSkipSpaceFrom bytes start spacePrefix.length := by
    simpa [suffix, spacePrefix] using scanSkipSpace_takeWhile_bytes bytes start
  have hprefixCount : scanSkipSpaceFrom bytes start (stop - start) := by
    have hcount : stop - start = spacePrefix.length := by dsimp [stop]; omega
    rw [hcount]
    exact hprefix
  have hboundary : stop = bytes.length ∨ (stop < bytes.length ∧ ∃ byte,
      bytes[stop]? = some byte ∧ scanSpace byte.toNat = false) := by
    by_cases hfull : spacePrefix.length = suffix.length
    · left
      dsimp [stop]
      rw [hfull, hdropLen]
      omega
    · have hshort : spacePrefix.length < suffix.length := by omega
      obtain ⟨byte, hbyteAtSuffix, hnotspace⟩ :=
        scanSkipSpace_takeWhile_boundary suffix hshort
      have hbyteAt : bytes[stop]? = some byte := by
        dsimp [stop, suffix] at *
        simpa only [List.getElem?_drop] using hbyteAtSuffix
      right
      exact ⟨by dsimp [stop]; omega, byte, hbyteAt, hnotspace⟩
  obtain ⟨finalState, hloop, hpost⟩ :=
    scanSkipSpace_terminates_prefix bytes bytes.length start stop
      hstartStop hstop (by omega) hboundary hprefixCount frame
  refine ⟨finalState, hloop, ?_⟩
  simpa [stop, spacePrefix, suffix] using hpost

/-- The translated loop iteration accepts `'7'`, accumulates 127, preserves
    `sat = false`, and advances the cursor by one byte. -/
def scanLoopObserved (byte : UInt8) (initial : Nat) (saturated : Bool) :
    Option (Option Val × Option Val × Option Val) :=
  match execStmt Gen.prog 100 (scanLoopState byte initial saturated)
      Gen.tobj_scan_int_loop0 with
  | .ok (_, s) => some (s.locals 3, s.locals 5, s.locals 6)
  | _ => none

example : scanLoopObserved 55 12 false = some
    (some (.ptr 20 1), some (.int IntTy.i64 127), some (.int IntTy.u8 0)) := by
  decide +kernel

/-- For every ASCII decimal digit, the generated loop body agrees with one
    unsaturated decimal accumulation step and advances the pointer. -/
theorem scanLoop_digit_step (digit : Nat) (hdigit : digit < 10) :
    scanLoopObserved (48 + digit).toUInt8 12 false = some
      (some (.ptr 20 1), some (.int IntTy.i64 (120 + digit)),
        some (.int IntTy.u8 0)) := by
  have hcases : digit = 0 ∨ digit = 1 ∨ digit = 2 ∨ digit = 3 ∨
      digit = 4 ∨ digit = 5 ∨ digit = 6 ∨ digit = 7 ∨ digit = 8 ∨ digit = 9 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h <;> subst digit <;> decide +kernel

/-- At the saturation boundary, the translated loop agrees with the abstract
    capped step for every decimal digit, including both sides of the cutoff. -/
theorem scanLoop_digit_boundary (digit : Nat) (hdigit : digit < 10) :
    scanLoopObserved (48 + digit).toUInt8 214748364 false = some
      (some (.ptr 20 1),
        some (.int IntTy.i64 (Obj.scanCLoopStep (214748364, false) (48 + digit)).1),
        some (.int IntTy.u8
          (if (Obj.scanCLoopStep (214748364, false) (48 + digit)).2 then 1 else 0))) := by
  have hcases : digit = 0 ∨ digit = 1 ∨ digit = 2 ∨ digit = 3 ∨
      digit = 4 ∨ digit = 5 ∨ digit = 6 ∨ digit = 7 ∨ digit = 8 ∨ digit = 9 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h <;> subst digit <;> decide +kernel

/-- Every later digit preserves the capped value once the translated loop's
    saturation flag is true. -/
theorem scanLoop_digit_after_saturation (digit : Nat) (hdigit : digit < 10) :
    scanLoopObserved (48 + digit).toUInt8 2147483647 true = some
      (some (.ptr 20 1), some (.int IntTy.i64 2147483647), some (.int IntTy.u8 1)) := by
  have hcases : digit = 0 ∨ digit = 1 ∨ digit = 2 ∨ digit = 3 ∨
      digit = 4 ∨ digit = 5 ∨ digit = 6 ∨ digit = 7 ∨ digit = 8 ∨ digit = 9 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h <;> subst digit <;> decide +kernel

/-- The typed i64 multiply in the generated accumulator expression agrees
    with natural-number multiplication throughout the scanner's magnitude range. -/
theorem scanLoop_mul_ten_eval (initial : Nat) (hinitial : initial ≤ 2147483647) :
    evalBin .mul (some IntTy.i64) (.int IntTy.i64 initial) (.int IntTy.i64 10) =
      .ok (.int IntTy.i64 (initial * 10)) := by
  have hlo : 0 ≤ (initial : Int) * 10 := by omega
  have hhi : (initial : Int) * 10 < 9223372036854775808 := by omega
  have hno : ¬ 9223372036854775808 ≤ initial := by omega
  have hmod : ((initial : Int) * 10) % (18446744073709551616 : Int) =
      (initial : Int) * 10 := Int.emod_eq_of_lt hlo (by omega)
  have hnat : Int.toNat ((initial : Int) * 10) = initial * 10 := by
    have hcast : ((initial : Int) * 10).toNat = (initial : Int) * 10 :=
      Int.toNat_of_nonneg hlo
    omega
  have hrangeProp : -9223372036854775808 ≤ (initial : Int) * 10 ∧
      (initial : Int) * 10 ≤ 9223372036854775807 := by
    constructor <;> omega
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, arith, IntTy.inRange,
    IntTy.i64, IntTy.minVal, IntTy.maxVal, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, hmod, hnat, hrangeProp, hno]

/-- The typed i64 addition after multiplying and decoding an ASCII digit is
    also exact and remains inside the signed i64 range. -/
theorem scanLoop_add_digit_eval (initial digit : Nat)
    (hinitial : initial ≤ 2147483647) (hdigit : digit ≤ 9) :
    evalBin .add (some IntTy.i64) (.int IntTy.i64 (initial * 10))
      (.int IntTy.i64 digit) =
      .ok (.int IntTy.i64 (initial * 10 + digit)) := by
  have hz : (initial : Int) * 10 + digit ≥ 0 := by omega
  have hhi : (initial : Int) * 10 + digit < 9223372036854775808 := by omega
  have hnoMul : ¬ 9223372036854775808 ≤ initial * 10 := by omega
  have hnoDigit : ¬ 9223372036854775808 ≤ digit := by omega
  have hmod : ((initial : Int) * 10 + digit) % (18446744073709551616 : Int) =
      (initial : Int) * 10 + digit := Int.emod_eq_of_lt hz (by omega)
  have hnat : Int.toNat ((initial : Int) * 10 + digit) = initial * 10 + digit := by
    have hcast : ((initial : Int) * 10 + digit).toNat = (initial : Int) * 10 + digit :=
      Int.toNat_of_nonneg hz
    omega
  have hrangeProp : -9223372036854775808 ≤ (initial : Int) * 10 + digit ∧
      (initial : Int) * 10 + digit ≤ 9223372036854775807 := by
    constructor <;> omega
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, arith, IntTy.inRange,
    IntTy.i64, IntTy.minVal, IntTy.maxVal, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, hmod, hnat, hrangeProp, hnoMul, hnoDigit]

/-- Casting an ASCII decimal byte from signed i8 to i32 preserves its positive
    numeric value. -/
theorem scanLoop_ascii_i8_to_i32 (digit : Nat) (hdigit : digit < 10) :
    evalCast IntTy.i32 (.int IntTy.i8 (48 + digit)) =
      .ok (.int IntTy.i32 (48 + digit)) := by
  simp [evalCast, IntTy.i8, IntTy.i32, IntTy.wrap, IntTy.toInt, IntTy.modulus]
  omega

/-- The generated i32 subtraction of ASCII `'0'` yields the decimal value. -/
theorem scanLoop_sub_ascii_zero (digit : Nat) (hdigit : digit < 10) :
    evalBin .sub (some IntTy.i32) (.int IntTy.i32 (48 + digit))
      (.int IntTy.i32 48) = .ok (.int IntTy.i32 digit) := by
  have hnonneg : 0 ≤ (digit : Int) := by omega
  have hmod : (digit : Int) % (4294967296 : Int) = digit :=
    Int.emod_eq_of_lt hnonneg (by omega)
  have hnat : Int.toNat (digit : Int) = digit := by
    have hcast : ((digit : Int).toNat : Int) = digit := Int.toNat_of_nonneg hnonneg
    omega
  have hbyteSmall : ¬ 2147483648 ≤ 48 + digit := by omega
  have hrange : -2147483648 ≤ (digit : Int) ∧ (digit : Int) ≤ 2147483647 := by
    constructor <;> omega
  have hsub : (48 : Int) + digit - 48 = digit := by omega
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, arith, IntTy.inRange, IntTy.i32,
    IntTy.minVal, IntTy.maxVal, IntTy.toInt, IntTy.wrap, IntTy.modulus,
    hmod, hnat, hbyteSmall, hrange, hsub]

/-- The generated cast of the i32 digit difference back to i64 preserves the
    digit value. -/
theorem scanLoop_digit_i32_to_i64 (digit : Nat) (hdigit : digit < 10) :
    evalCast IntTy.i64 (.int IntTy.i32 digit) = .ok (.int IntTy.i64 digit) := by
  simp [evalCast, IntTy.i64, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus]
  omega

/-- The accumulator expression copied from the generated scanner AST. -/
def scanAccumulatorExpr : Expr :=
  .bin .add (some IntTy.i64)
    (.bin .mul (some IntTy.i64) (.var 5)
      (.cast IntTy.i64 (.const (.int IntTy.i32 10))))
    (.cast IntTy.i64
      (.bin .sub (some IntTy.i32)
        (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
        (.const (.int IntTy.i32 48))) )

/-- The saturation test and cap assignment inside the generated loop. -/
def scanLoopSaturationUpdate : Stmt :=
  .ite
    (.bin .gt (some IntTy.i64) (.var 5) (.const (.int IntTy.i64 2147483647)))
    (.seq
      (.set 5 (.const (.int IntTy.i64 2147483647)))
      (.set 6 (.cond (.const (.int IntTy.i32 1))
        (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))))
    .skip

/-- Once the candidate comparison is evaluated, the generated cap branch
    stores `INT_MAX` and sets the saturation byte exactly when it is true. -/
theorem scanLoop_saturation_update (s : State) (overflow : Bool)
    (hcond : EvE Gen.prog s
      (.bin .gt (some IntTy.i64) (.var 5) (.const (.int IntTy.i64 2147483647)))
      (boolVal overflow))
    (htruth : truthy (boolVal overflow) = .ok overflow) :
    ExS Gen.prog s scanLoopSaturationUpdate .normal
      (if overflow then
        { s with locals := Locals.upd (Locals.upd s.locals 5
          (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
      else s) := by
  have htrue : ExS Gen.prog s
      (.seq (.set 5 (.const (.int IntTy.i64 2147483647)))
        (.set 6 (.cond (.const (.int IntTy.i32 1))
          (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))) .normal
      { s with locals := Locals.upd (Locals.upd s.locals 5
        (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) } := by
    refine ExS.seq (ExS.set (EvE.const _)) ?_
    have hcond : EvE Gen.prog
        { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 2147483647) }
        (.cond (.const (.int IntTy.i32 1))
          (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
        (.int IntTy.u8 1) := by
      refine EvE.cond (EvE.const (.int IntTy.i32 1)) (by rfl) ?_
      exact EvE.const (.int IntTy.u8 1)
    exact ExS.set hcond
  have hfalse : ExS Gen.prog s .skip .normal s := ExS.skip
  by_cases hoverflow : overflow
  · simpa [scanLoopSaturationUpdate, hoverflow] using
      (ExS.ite hcond htruth (by simpa [hoverflow] using htrue))
  · simpa [scanLoopSaturationUpdate, hoverflow] using
      (ExS.ite hcond htruth (by simpa [hoverflow] using hfalse))

/-- The loop's pointer-index increment is defined for any in-bounds cursor and
    installs the next one-byte position in local 3. -/
theorem scanLoop_cursor_advance_exs (s : State) (cursor : Nat) (blk : Block)
    (hcursor : s.locals 3 = some (.ptr 20 cursor))
    (hmem : s.mem 20 = some blk)
    (hbound : cursor + 1 ≤ blk.length) :
    ExS Gen.prog s (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1))
      .normal { s with locals := Locals.upd s.locals 3 (.ptr 20 (cursor + 1)) } := by
  have hp : EvE Gen.prog s (.var 3) (.ptr 20 cursor) := EvE.var hcursor
  have hi : EvE Gen.prog s (.const (.int IntTy.i64 1)) (.int IntTy.i64 1) := EvE.const _
  have hptr : ptrAdd s.mem (.ptr 20 cursor) (IntTy.i64.toInt 1) =
      .ok (.ptr 20 (cursor + 1)) := by
    simp [ptrAdd, hmem, IntTy.toInt, IntTy.i64]
    omega
  have hindex : EvE Gen.prog s
      (.index (.var 3) (.const (.int IntTy.i64 1)) 1) (.ptr 20 (cursor + 1)) :=
    EvE.index hp hi hptr
  exact ExS.set hindex

/-- The generated signed i64 overflow comparison agrees with the scanner's
    natural-number comparison throughout the bounded candidate range. -/
theorem scanLoop_gt_i64_eval (candidate : Nat)
    (hcandidate : candidate ≤ 21474836479) :
    evalBin .gt (some IntTy.i64) (.int IntTy.i64 candidate)
      (.int IntTy.i64 2147483647) =
      .ok (boolVal (decide (candidate > 2147483647))) := by
  have hsmall : candidate < 9223372036854775808 := by omega
  have hcv : IntTy.toInt IntTy.i64 candidate = candidate := by
    simp [IntTy.toInt, IntTy.i64]
    omega
  have hmax : IntTy.toInt IntTy.i64 2147483647 = 2147483647 := by rfl
  unfold evalBin
  simp only [isPtr, Bool.false_and, evalBinInt]
  change binInt .gt IntTy.i64 (.int IntTy.i64 candidate)
    (.int IntTy.i64 2147483647) = _
  simp only [binInt, intOf, Res.bind_eq, Res.bind_ok, ite_true]
  rw [hcv, hmax]
  simp only [IntTy.i64, ite_true]
  have hrel : ((candidate : Int) > 2147483647) ↔ candidate > 2147483647 := by
    change (2147483647 : Int) < (candidate : Int) ↔ 2147483647 < candidate
    exact Int.ofNat_lt
  have hdec : decide ((candidate : Int) > 2147483647) = decide (candidate > 2147483647) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hrel
  change Res.ok (boolVal (decide ((candidate : Int) > 2147483647))) = _
  exact congrArg (fun b => Res.ok (boolVal b)) hdec

/-- The generated scanner loop with the accumulator expression factored out. -/
def scanLoopBodyFactored : Stmt :=
  .loop
    (.ite
      (.land
        (.bin .lt (some IntTy.u64) (.var 3) (.var 1))
        (.cast IntTy.i32 (.call 7 [(.load (.int IntTy.i8) (.var 3))])))
      (.seq
        (.ite (.un .lnot IntTy.i32 (.var 6))
          (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate)
          .skip)
        (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
      .brk)
    .skip

/-- Factoring the accumulator expression leaves the generated loop AST unchanged. -/
theorem scanLoop_ast_factor : Gen.tobj_scan_int_loop0 = scanLoopBodyFactored := rfl

/-- The generated loop's digit guard. -/
def scanLoopDigitGuard : Expr :=
  .land
    (.bin .lt (some IntTy.u64) (.var 3) (.var 1))
    (.cast IntTy.i32 (.call 7 [(.load (.int IntTy.i8) (.var 3))]))


/-- One loop-body iteration with the accumulator expression factored out. -/
def scanLoopIterationBody : Stmt :=
  .ite scanLoopDigitGuard
    (.seq
      (.ite (.un .lnot IntTy.i32 (.var 6))
        (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate)
        .skip)
      (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
    .brk


/-- The generated loop guard succeeds for any in-bounds ASCII digit byte. -/
theorem scanLoop_digit_guard (byte : UInt8) (initial : Nat) (saturated : Bool)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57) :
    EvE Gen.prog (scanLoopState byte initial saturated) scanLoopDigitGuard (boolVal true) := by
  let s := scanLoopState byte initial saturated
  let c : Int := byte.toNat
  have hmod : c % (256 : Int) = c := Int.emod_eq_of_lt (by omega) (by omega)
  have hnat : Int.toNat c = byte.toNat := by
    have hcast : (Int.toNat c : Int) = c := Int.toNat_of_nonneg (by omega)
    omega
  have hwrap : IntTy.wrap IntTy.i8 c = byte.toNat := by
    simp [IntTy.wrap, IntTy.modulus, IntTy.i8, hmod, hnat]
  have hrange : IntTy.inRange IntTy.i8 c = true := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8]
    omega
  have hlocal : frameLocals [0] [.int IntTy.i8 (byte.toNat)] 0 =
      some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c)) := by
    simp [frameLocals, hwrap]
  have hDigit : ExS Gen.prog
      ⟨frameLocals [0] [.int IntTy.i8 (byte.toNat)], s.mem, true⟩
      Gen.tobj_is_digit.body (.ret (some (.int IntTy.u8 1)))
      ⟨frameLocals [0] [.int IntTy.i8 (byte.toNat)], s.mem, true⟩ := by
    exact Obj.C.Proofs.tobj_is_digit_ge _ s.mem c (ro := true) hrange (by dsimp [c]; omega)
      (by dsimp [c]; omega) hlocal
  have hload : EvE Gen.prog s (.load (.int IntTy.i8) (.var 3))
      (.int IntTy.i8 (byte.toNat)) := by
    have hp : EvE Gen.prog s (.var 3) (.ptr 20 0) := by
      apply EvE.var
      simp [s, scanLoopState]
    apply EvE.load hp
    simp [s, scanLoopState, load, readBytes, decodeLE, Ty.size, IntTy.bytes, IntTy.i8]
  have hargs : EvArgs Gen.prog s [.load (.int IntTy.i8) (.var 3)]
      [.int IntTy.i8 (byte.toNat)] := EvArgs.cons hload EvArgs.nil
  have hcall : EvE Gen.prog s (.call 7 [.load (.int IntTy.i8) (.var 3)])
      (.int IntTy.u8 1) := by
    exact EvE.call hargs (by rfl) (by rfl) hDigit
  have hcallCast : evalCast IntTy.i32 (.int IntTy.u8 1) =
      .ok (.int IntTy.i32 1) := by
    simp [evalCast, IntTy.u8, IntTy.i32, IntTy.modulus]
  have hsecond : EvE Gen.prog s
      (.cast IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (.int IntTy.i32 1) := EvE.cast hcall hcallCast
  have hp : EvE Gen.prog s (.var 3) (.ptr 20 0) := by
    apply EvE.var
    simp [s, scanLoopState]
  have he : EvE Gen.prog s (.var 1) (.ptr 20 1) := by
    apply EvE.var
    simp [s, scanLoopState]
  have hptr : EvE Gen.prog s (.bin .lt (some IntTy.u64) (.var 3) (.var 1))
      (boolVal true) := by
    apply EvE.bin hp he
    simp [evalBin, isPtr, boolVal]
  have ht : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  exact EvE.land_true hptr ht hsecond (by simp [truthy])

/-- The generated guard succeeds at any cursor below the scanner endpoint when
    the corresponding input byte is an ASCII decimal digit. -/
theorem scanLoop_digit_guard_at (bytes : Block) (cursor endpoint initial : Nat)
    (saturated : Bool) (byte : UInt8)
    (hcursor : cursor < endpoint) (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57) :
    EvE Gen.prog (scanLoopStateAt bytes cursor endpoint initial saturated)
      scanLoopDigitGuard (boolVal true) := by
  let s := scanLoopStateAt bytes cursor endpoint initial saturated
  let c : Int := byte.toNat
  have hmod : c % (256 : Int) = c := Int.emod_eq_of_lt (by omega) (by omega)
  have hnat : Int.toNat c = byte.toNat := by
    have hcast : (Int.toNat c : Int) = c := Int.toNat_of_nonneg (by omega)
    omega
  have hwrap : IntTy.wrap IntTy.i8 c = byte.toNat := by
    simp [IntTy.wrap, IntTy.modulus, IntTy.i8, hmod, hnat]
  have hrange : IntTy.inRange IntTy.i8 c = true := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8]
    omega
  have hlocal : frameLocals [0] [.int IntTy.i8 (byte.toNat)] 0 =
      some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c)) := by
    simp [frameLocals, hwrap]
  have hDigit : ExS Gen.prog
      ⟨frameLocals [0] [.int IntTy.i8 (byte.toNat)], s.mem, true⟩
      Gen.tobj_is_digit.body (.ret (some (.int IntTy.u8 1)))
      ⟨frameLocals [0] [.int IntTy.i8 (byte.toNat)], s.mem, true⟩ := by
    exact Obj.C.Proofs.tobj_is_digit_ge _ s.mem c (ro := true) hrange (by
      dsimp [c]; omega) (by dsimp [c]; omega) hlocal
  have hp : EvE Gen.prog s (.var 3) (.ptr 20 cursor) := by
    apply EvE.var
    simp [s, scanLoopStateAt]
  have hload : EvE Gen.prog s (.load (.int IntTy.i8) (.var 3))
      (.int IntTy.i8 byte.toNat) := by
    apply EvE.load hp
    exact scanLoop_load_byte_at bytes cursor endpoint initial saturated byte
      ((List.getElem?_eq_some_iff.mp hbyteAt).choose) hbyteAt
  have hargs : EvArgs Gen.prog s [.load (.int IntTy.i8) (.var 3)]
      [.int IntTy.i8 (byte.toNat)] := EvArgs.cons hload EvArgs.nil
  have hcall : EvE Gen.prog s (.call 7 [.load (.int IntTy.i8) (.var 3)])
      (.int IntTy.u8 1) := by
    exact EvE.call hargs (by rfl) (by rfl) hDigit
  have hcallCast : evalCast IntTy.i32 (.int IntTy.u8 1) =
      .ok (.int IntTy.i32 1) := by
    simp [evalCast, IntTy.u8, IntTy.i32, IntTy.modulus]
  have hsecond : EvE Gen.prog s
      (.cast IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (.int IntTy.i32 1) := EvE.cast hcall hcallCast
  have he : EvE Gen.prog s (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [s, scanLoopStateAt]
  have hptr : EvE Gen.prog s (.bin .lt (some IntTy.u64) (.var 3) (.var 1))
      (boolVal true) := by
    apply EvE.bin hp he
    simp [evalBin, isPtr, boolVal]
    omega
  have ht : truthy (boolVal true) = .ok true := by
    simp [truthy, boolVal]
  exact EvE.land_true hptr ht hsecond (by simp [truthy])

/-- Digit-guard evaluation for a real scanner frame with arbitrary unrelated
    locals. The loop frame may retain the caller pointers and the sign local;
    only locals 1 and 3 and the input memory are needed by the guard. -/
theorem scanLoop_digit_guard_state_at (s : State) (bytes : Block)
    (cursor endpoint : Nat) (byte : UInt8)
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hendLocal : s.locals 1 = some (.ptr 20 endpoint))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < endpoint)
    (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57) :
    EvE Gen.prog s scanLoopDigitGuard (boolVal true) := by
  let c : Int := byte.toNat
  have hmod : c % (256 : Int) = c := Int.emod_eq_of_lt (by omega) (by omega)
  have hnat : Int.toNat c = byte.toNat := by
    have hcast : (Int.toNat c : Int) = c := Int.toNat_of_nonneg (by omega)
    omega
  have hwrap : IntTy.wrap IntTy.i8 c = byte.toNat := by
    simp [IntTy.wrap, IntTy.modulus, IntTy.i8, hmod, hnat]
  have hrange : IntTy.inRange IntTy.i8 c = true := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8]
    omega
  have hlocal : frameLocals [0] [.int IntTy.i8 byte.toNat] 0 =
      some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c)) := by
    simp [frameLocals, hwrap]
  have hDigit : ExS Gen.prog
      ⟨frameLocals [0] [.int IntTy.i8 byte.toNat], s.mem, true⟩
      Gen.tobj_is_digit.body (.ret (some (.int IntTy.u8 1)))
      ⟨frameLocals [0] [.int IntTy.i8 byte.toNat], s.mem, true⟩ := by
    exact Obj.C.Proofs.tobj_is_digit_ge _ s.mem c (ro := true) hrange
      (by dsimp [c]; omega) (by dsimp [c]; omega) hlocal
  have hload : EvE Gen.prog s (.load (.int IntTy.i8) (.var 3))
      (.int IntTy.i8 byte.toNat) := by
    apply EvE.load (EvE.var hcursorLocal)
    exact scanLoop_load_byte_from_mem s.mem bytes cursor byte hmem
      ((List.getElem?_eq_some_iff.mp hbyteAt).choose) hbyteAt
  have hargs : EvArgs Gen.prog s [.load (.int IntTy.i8) (.var 3)]
      [.int IntTy.i8 byte.toNat] := EvArgs.cons hload EvArgs.nil
  have hcall : EvE Gen.prog s (.call 7 [.load (.int IntTy.i8) (.var 3)])
      (.int IntTy.u8 1) := EvE.call hargs (by rfl) (by rfl) hDigit
  have hcallCast : evalCast IntTy.i32 (.int IntTy.u8 1) =
      .ok (.int IntTy.i32 1) := by
    simp [evalCast, IntTy.u8, IntTy.i32, IntTy.modulus]
  have hsecond : EvE Gen.prog s
      (.cast IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (.int IntTy.i32 1) := EvE.cast hcall hcallCast
  have hptr : EvE Gen.prog s
      (.bin .lt (some IntTy.u64) (.var 3) (.var 1)) (boolVal true) := by
    apply EvE.bin (EvE.var hcursorLocal) (EvE.var hendLocal)
    simp [evalBin, isPtr, boolVal]
    exact hcursor
  have htrue : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  exact EvE.land_true hptr htrue hsecond (by simp [truthy])

/-- The translated digit predicate returns false on any in-range non-digit
    byte loaded from an arbitrary scanner buffer. -/
theorem scanLoop_digit_call_false_at (s : State) (bytes : Block) (cursor : Nat)
    (byte : UInt8) (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat) :
    EvE Gen.prog s
      (.call 7 [.load (.int IntTy.i8) (.var 3)]) (.int IntTy.u8 0) ∧
    EvE Gen.prog s
      (.cast IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (.int IntTy.i32 0) := by
  let c : Int := IntTy.toInt IntTy.i8 byte.toNat
  have hbyteRange : byte.toNat < 256 := by
    have h := UInt8.toNat_lt byte
    omega
  have hrange : IntTy.inRange IntTy.i8 c = true := by
    by_cases hhigh : 128 ≤ byte.toNat
    · simp [c, IntTy.toInt, IntTy.modulus, IntTy.inRange, IntTy.minVal,
        IntTy.maxVal, IntTy.i8, hhigh]
      omega
    · have hlow : byte.toNat < 128 := by omega
      simp [c, IntTy.toInt, IntTy.modulus, IntTy.inRange, IntTy.minVal,
        IntTy.maxVal, IntTy.i8, hlow, hhigh]
      omega
  have hwrap : IntTy.wrap IntTy.i8 c = byte.toNat := by
    by_cases hsmall : byte.toNat < 128
    · have hc : c = byte.toNat := by
        have hnohigh : ¬ 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hnohigh]
      rw [hc]
      simp only [IntTy.wrap, IntTy.modulus, IntTy.i8]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      simp
    · have hc : c = (byte.toNat : Int) - 256 := by
        have hhigh : 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hhigh]
      rw [hc]
      simp only [IntTy.wrap, IntTy.modulus, IntTy.i8]
      change (((byte.toNat : Int) - 256) % (256 : Int)).toNat = byte.toNat
      have hmod : ((byte.toNat : Int) - 256) % (256 : Int) = byte.toNat := by
        have hmod := Int.emod_add_emod (-256) (256 : Int) (byte.toNat : Int)
        have hz : (-256 : Int) % 256 = 0 := by decide
        have hlt : 0 ≤ (byte.toNat : Int) := by omega
        have hlt2 : (byte.toNat : Int) < 256 := by omega
        have hnat : (byte.toNat : Int) % 256 = byte.toNat :=
          Int.emod_eq_of_lt hlt hlt2
        rw [hz] at hmod
        have hleft : (0 + (byte.toNat : Int)) % 256 = byte.toNat := by
          simpa using hnat
        rw [hleft] at hmod
        simpa [Int.sub_eq_add_neg, Int.add_comm] using hmod.symm
      rw [hmod]
      simp
  have hnondigitSigned : c < 48 ∨ 57 < c := by
    by_cases hsmall : byte.toNat < 128
    · have hc : c = byte.toNat := by
        have hnohigh : ¬ 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hnohigh]
      rw [hc]
      rcases hnondigit with hlo | hhi
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · left
      have hhigh : 128 ≤ byte.toNat := by omega
      simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hhigh]
      omega
  have hlocal : frameLocals [0] [.int IntTy.i8 byte.toNat] 0 =
      some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c)) := by
    simp [frameLocals, hwrap]
  let loc := frameLocals [0] [.int IntTy.i8 byte.toNat]
  have hloc : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c)) := by
    simpa [loc] using hlocal
  have hDigit : ExS Gen.prog
      ⟨loc, s.mem, true⟩
      Gen.tobj_is_digit.body (.ret (some (.int IntTy.u8 0)))
      ⟨loc, s.mem, true⟩ := by
    rcases hnondigitSigned with hlo | hhi
    · exact Obj.C.Proofs.tobj_is_digit_lo loc s.mem c (ro := true) hrange hlo hloc
    · exact Obj.C.Proofs.tobj_is_digit_hi loc s.mem c (ro := true) hrange hhi hloc
  have hp : EvE Gen.prog s (.var 3) (.ptr 20 cursor) := EvE.var hcursorLocal
  have hload : EvE Gen.prog s (.load (.int IntTy.i8) (.var 3))
      (.int IntTy.i8 byte.toNat) := by
    apply EvE.load hp
    exact scanLoop_load_byte_from_mem s.mem bytes cursor byte hmem hcursor hbyteAt
  have hargs : EvArgs Gen.prog s [.load (.int IntTy.i8) (.var 3)]
      [.int IntTy.i8 byte.toNat] := EvArgs.cons hload EvArgs.nil
  have hcall : EvE Gen.prog s (.call 7 [.load (.int IntTy.i8) (.var 3)])
      (.int IntTy.u8 0) := by
    simpa [loc] using (EvE.call hargs (by rfl) (by rfl) hDigit)
  have hcast : evalCast IntTy.i32 (.int IntTy.u8 0) =
      .ok (.int IntTy.i32 0) := by
    simp [evalCast, IntTy.u8, IntTy.i32, IntTy.modulus]
  exact ⟨hcall, EvE.cast hcall hcast⟩

/-- The translated digit predicate returns true on any in-range ASCII digit
    loaded from an arbitrary scanner buffer. -/
theorem scanLoop_digit_call_true_at (s : State) (bytes : Block) (cursor : Nat)
    (byte : UInt8) (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57) :
    EvE Gen.prog s
      (.call 7 [.load (.int IntTy.i8) (.var 3)]) (.int IntTy.u8 1) ∧
    EvE Gen.prog s
      (.cast IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (.int IntTy.i32 1) := by
  let c : Int := byte.toNat
  have hmod : c % (256 : Int) = c := Int.emod_eq_of_lt (by omega) (by omega)
  have hnat : Int.toNat c = byte.toNat := by
    have hcast : (Int.toNat c : Int) = c := Int.toNat_of_nonneg (by omega)
    omega
  have hwrap : IntTy.wrap IntTy.i8 c = byte.toNat := by
    simp [IntTy.wrap, IntTy.modulus, IntTy.i8, hmod, hnat]
  have hrange : IntTy.inRange IntTy.i8 c = true := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8]
    omega
  have hlocal : frameLocals [0] [.int IntTy.i8 byte.toNat] 0 =
      some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c)) := by
    simp [frameLocals, hwrap]
  let loc := frameLocals [0] [.int IntTy.i8 byte.toNat]
  have hloc : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c)) := by
    simpa [loc] using hlocal
  have hDigit : ExS Gen.prog ⟨loc, s.mem, true⟩
      Gen.tobj_is_digit.body (.ret (some (.int IntTy.u8 1)))
      ⟨loc, s.mem, true⟩ := by
    exact Obj.C.Proofs.tobj_is_digit_ge loc s.mem c (ro := true)
      hrange (by dsimp [c]; omega) (by dsimp [c]; omega) hloc
  have hp : EvE Gen.prog s (.var 3) (.ptr 20 cursor) :=
    EvE.var hcursorLocal
  have hload : EvE Gen.prog s (.load (.int IntTy.i8) (.var 3))
      (.int IntTy.i8 byte.toNat) := by
    apply EvE.load hp
    exact scanLoop_load_byte_from_mem s.mem bytes cursor byte hmem hcursor hbyteAt
  have hargs : EvArgs Gen.prog s [.load (.int IntTy.i8) (.var 3)]
      [.int IntTy.i8 byte.toNat] := EvArgs.cons hload EvArgs.nil
  have hcall : EvE Gen.prog s (.call 7 [.load (.int IntTy.i8) (.var 3)])
      (.int IntTy.u8 1) := by
    simpa [loc] using (EvE.call hargs (by rfl) (by rfl) hDigit)
  have hcast : evalCast IntTy.i32 (.int IntTy.u8 1) =
      .ok (.int IntTy.i32 1) := by
    simp [evalCast, IntTy.u8, IntTy.i32, IntTy.modulus]
  exact ⟨hcall, EvE.cast hcall hcast⟩

/-- At a non-digit byte before the endpoint the generated loop guard is
    false, so the generated body breaks without consuming that byte. -/
theorem scanLoop_guard_false_nondigit_at (bytes : Block)
    (cursor endpoint initial : Nat) (saturated : Bool) (byte : UInt8)
    (hcursor : cursor < endpoint) (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : cursor < bytes.length)
    (hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat) :
    EvE Gen.prog (scanLoopStateAt bytes cursor endpoint initial saturated)
      scanLoopDigitGuard (boolVal false) := by
  let s := scanLoopStateAt bytes cursor endpoint initial saturated
  have hp : EvE Gen.prog s (.var 3) (.ptr 20 cursor) := by
    apply EvE.var
    simp [s, scanLoopStateAt]
  have he : EvE Gen.prog s (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [s, scanLoopStateAt]
  have hptr : EvE Gen.prog s
      (.bin .lt (some IntTy.u64) (.var 3) (.var 1)) (boolVal true) := by
    apply EvE.bin hp he
    simp [evalBin, isPtr, boolVal]
    omega
  have ht : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hcall := scanLoop_digit_call_false_at s bytes cursor byte
    (by simp [s, scanLoopStateAt]) (by simp [s, scanLoopStateAt])
    hbyte hbyteAt hnondigit
  have hf : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  exact EvE.land_true hptr ht hcall.2 hf

/-- The loop guard exits at the scanner endpoint, producing the `break`
    outcome required by the zero case of `ExS.loop_decreasing`. -/
theorem scanLoop_break_at_endpoint (bytes : Block) (endpoint initial : Nat)
    (saturated : Bool) :
    ExS Gen.prog (scanLoopStateAt bytes endpoint endpoint initial saturated)
      scanLoopIterationBody .brk
      (scanLoopStateAt bytes endpoint endpoint initial saturated) := by
  let s := scanLoopStateAt bytes endpoint endpoint initial saturated
  have hp : EvE Gen.prog s (.var 3) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [s, scanLoopStateAt]
  have he : EvE Gen.prog s (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [s, scanLoopStateAt]
  have hptr : EvE Gen.prog s
      (.bin .lt (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin hp he
    simp [evalBin, isPtr, boolVal]
  have hf : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hguard : EvE Gen.prog s scanLoopDigitGuard (boolVal false) :=
    EvE.land_false hptr hf
  simpa [scanLoopIterationBody, s] using
    (ExS.ite hguard hf ExS.brk : ExS Gen.prog s
      (.ite scanLoopDigitGuard
        (.seq
          (.ite (.un .lnot IntTy.i32 (.var 6))
            (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
          (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
        .brk) .brk s)

theorem scanLoop_break_at_nondigit (bytes : Block) (cursor endpoint initial : Nat)
    (saturated : Bool) (byte : UInt8)
    (hcursor : cursor < endpoint) (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : cursor < bytes.length)
    (hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat) :
    ExS Gen.prog (scanLoopStateAt bytes cursor endpoint initial saturated)
      scanLoopIterationBody .brk
      (scanLoopStateAt bytes cursor endpoint initial saturated) := by
  let s := scanLoopStateAt bytes cursor endpoint initial saturated
  have hguard := scanLoop_guard_false_nondigit_at bytes cursor endpoint initial
    saturated byte hcursor hbyteAt hbyte hnondigit
  have hf : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  simpa [scanLoopIterationBody, s] using
    (ExS.ite hguard hf ExS.brk : ExS Gen.prog s
      (.ite scanLoopDigitGuard
        (.seq
          (.ite (.un .lnot IntTy.i32 (.var 6))
            (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
          (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
        .brk) .brk s)

/-- Endpoint exit from an arbitrary framed scanner state. -/
theorem scanLoop_break_at_endpoint_state (s : State) (endpoint : Nat)
    (hcursorLocal : s.locals 3 = some (.ptr 20 endpoint))
    (hendLocal : s.locals 1 = some (.ptr 20 endpoint)) :
    ExS Gen.prog s scanLoopIterationBody .brk s := by
  have hptr : EvE Gen.prog s
      (.bin .lt (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin (EvE.var hcursorLocal) (EvE.var hendLocal)
    simp [evalBin, isPtr, boolVal]
  have hfalse : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hguard : EvE Gen.prog s scanLoopDigitGuard (boolVal false) :=
    EvE.land_false hptr hfalse
  simpa [scanLoopIterationBody] using
    (ExS.ite hguard hfalse ExS.brk : ExS Gen.prog s
      (.ite scanLoopDigitGuard
        (.seq
          (.ite (.un .lnot IntTy.i32 (.var 6))
            (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
          (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
        .brk) .brk s)

/-- Nondigit exit from an arbitrary framed scanner state. -/
theorem scanLoop_break_at_nondigit_state (s : State) (bytes : Block)
    (cursor endpoint : Nat) (byte : UInt8)
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hendLocal : s.locals 1 = some (.ptr 20 endpoint))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < endpoint)
    (hbyteAt : bytes[cursor]? = some byte) (hbyte : cursor < bytes.length)
    (hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat) :
    ExS Gen.prog s scanLoopIterationBody .brk s := by
  have hp : EvE Gen.prog s (.var 3) (.ptr 20 cursor) := EvE.var hcursorLocal
  have he : EvE Gen.prog s (.var 1) (.ptr 20 endpoint) := EvE.var hendLocal
  have hptr : EvE Gen.prog s
      (.bin .lt (some IntTy.u64) (.var 3) (.var 1)) (boolVal true) := by
    apply EvE.bin hp he
    simp [evalBin, isPtr, boolVal]
    exact hcursor
  have htrue : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hcall := scanLoop_digit_call_false_at s bytes cursor byte
    hcursorLocal hmem hbyte hbyteAt hnondigit
  have hfalse : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hguard : EvE Gen.prog s scanLoopDigitGuard (boolVal false) :=
    EvE.land_true hptr htrue hcall.2 hfalse
  simpa [scanLoopIterationBody] using
    (ExS.ite hguard hfalse ExS.brk : ExS Gen.prog s
      (.ite scanLoopDigitGuard
        (.seq
          (.ite (.un .lnot IntTy.i32 (.var 6))
            (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
          (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
        .brk) .brk s)

/-- The remaining bytes up to the scanner's stopping cursor are all ASCII
    decimal digits. -/
def scanLoopDigitsFrom (bytes : Block) (cursor count : Nat) : Prop :=
  ∀ offset, offset < count → ∃ byte, bytes[cursor + offset]? = some byte ∧
    48 ≤ byte.toNat ∧ byte.toNat ≤ 57

/-- Every byte in a `takeWhile scanDigit` prefix has the expected indexed
    decimal-digit witness. -/
theorem scanLoop_takeWhile_digits (bytes : Block) (cursor : Nat) :
    scanLoopDigitsFrom bytes cursor
      ((bytes.drop cursor).takeWhile (fun byte => scanDigit byte.toNat)).length := by
  let pred := fun byte : UInt8 => scanDigit byte.toNat
  have hprefix : ∀ (xs : List UInt8) offset,
      offset < (xs.takeWhile pred).length →
        ∃ byte, xs[offset]? = some byte ∧
          48 ≤ byte.toNat ∧ byte.toNat ≤ 57 := by
    intro xs
    induction xs with
    | nil => intro offset hoff; simp at hoff
    | cons head tail ih =>
      intro offset hoff
      rw [List.takeWhile_cons] at hoff
      by_cases hp : pred head = true
      · rw [if_pos hp, List.length_cons] at hoff
        cases offset with
        | zero =>
          refine ⟨head, by simp, ?_⟩
          have hdec : decide (48 ≤ head.toNat ∧ head.toNat ≤ 57) = true := by
            simpa [pred, scanDigit] using hp
          exact of_decide_eq_true hdec
        | succ offset =>
          have hoff' : offset < (tail.takeWhile pred).length := by omega
          obtain ⟨byte, hbyte, hrange⟩ := ih offset hoff'
          exact ⟨byte, by simpa using hbyte, hrange⟩
      · rw [if_neg hp] at hoff
        simp at hoff
  intro offset hoff
  have hget := hprefix (bytes.drop cursor) offset hoff
  obtain ⟨byte, hbyte, hlo, hhi⟩ := hget
  refine ⟨byte, ?_, hlo, hhi⟩
  simpa only [List.getElem?_drop] using hbyte

/-- If `takeWhile` stops before the end, its next byte fails the predicate. -/
theorem scanLoop_takeWhile_boundary (xs : List UInt8)
    (hlen : (xs.takeWhile (fun byte => scanDigit byte.toNat)).length < xs.length) :
    ∃ byte, xs[(xs.takeWhile (fun byte => scanDigit byte.toNat)).length]? = some byte ∧
      scanDigit byte.toNat = false := by
  let pred := fun byte : UInt8 => scanDigit byte.toNat
  have hboundary : ∀ (xs : List UInt8),
      (xs.takeWhile pred).length < xs.length →
        ∃ byte, xs[(xs.takeWhile pred).length]? = some byte ∧ pred byte = false := by
    intro xs
    induction xs with
    | nil => intro h; simp at h
    | cons head tail ih =>
      intro h
      rw [List.takeWhile_cons] at h
      by_cases hp : pred head = true
      · rw [if_pos hp, List.length_cons, List.length_cons] at h
        have htail : (tail.takeWhile pred).length < tail.length := by omega
        obtain ⟨byte, hbyte, hfalse⟩ := ih htail
        refine ⟨byte, ?_, hfalse⟩
        have hlen : ((head :: tail).takeWhile pred).length =
            (tail.takeWhile pred).length + 1 := by
          simp [List.takeWhile_cons, hp]
        rw [hlen, List.getElem?_cons_succ]
        exact hbyte
      · rw [if_neg hp] at h
        have hfalse : pred head = false := Bool.eq_false_iff.mpr hp
        refine ⟨head, ?_, hfalse⟩
        have hnil : (head :: tail).takeWhile pred = [] := by
          simp [List.takeWhile_cons, hp]
        simp [hnil]
  simpa [pred] using hboundary xs hlen

/-- The maximal byte-level digit prefix has the same length as the pure
    recursive scanner's consumed-count result. -/
theorem scanLoop_takeWhile_count (bytes : Block) (cursor : Nat) :
    ((bytes.drop cursor).takeWhile (fun byte => scanDigit byte.toNat)).length =
      (scanDigits ((bytes.drop cursor).map UInt8.toNat) 0).1 := by
  rw [scanDigits_count_exact]
  rw [List.takeWhile_map]
  simp only [List.length_map]
  rfl

/-- The prefix through a present element splits as the shorter prefix followed
    by that element. -/
theorem scanLoop_take_succ_append {α : Type} (xs : List α) (n : Nat) (x : α)
    (h : xs[n]? = some x) : xs.take (n + 1) = xs.take n ++ [x] := by
  induction xs generalizing n with
  | nil => simp at h
  | cons head tail ih =>
    cases n with
    | zero =>
      have hx : head = x := by simpa using h
      subst x
      rfl
    | succ n =>
      have htail : tail[n]? = some x := by simpa using h
      change head :: tail.take (n + 1) = head :: (tail.take n ++ [x])
      rw [ih n htail]

/-- Scanner loop invariant parameterized by the remaining digit count and the
    C-style fold accumulated over the consumed prefix. -/
def scanLoopPrefixInvariant (bytes : Block) (endpoint stop origin initial : Nat)
    (initialSat : Bool) (k : Nat) (s : State) : Prop :=
  ∃ cursor value saturated,
    origin ≤ cursor ∧
    cursor + k = stop ∧
    value ≤ 2147483647 ∧
    (saturated = true → value = 2147483647) ∧
    s = scanLoopStateAt bytes cursor endpoint value saturated ∧
    scanLoopDigitsFrom bytes cursor k ∧
    (value, saturated) =
      (((bytes.drop origin).take (cursor - origin)).map UInt8.toNat).foldl
        scanCLoopStep (initial, initialSat)

/-- Rebuild the loop's mutable locals over a real scanner frame, preserving
    caller parameters and the optional sign across every digit iteration. -/
def scanLoopFrameAt (base : State) (cursor value : Nat) (saturated : Bool) : State :=
  { base with locals :=
      Locals.upd (Locals.upd (Locals.upd base.locals 3 (.ptr 20 cursor)) 5
        (.int IntTy.i64 value)) 6 (.int IntTy.u8 (if saturated then 1 else 0)) }

/-- Prefix invariant for a loop running inside a caller's scanner frame. -/
def scanLoopFramePrefixInvariant (base : State) (bytes : Block)
    (endpoint stop origin initial : Nat) (initialSat : Bool)
    (k : Nat) (s : State) : Prop :=
  ∃ cursor value saturated,
    origin ≤ cursor ∧ cursor + k = stop ∧
    value ≤ 2147483647 ∧ (saturated = true → value = 2147483647) ∧
    s = scanLoopFrameAt base cursor value saturated ∧
    scanLoopDigitsFrom bytes cursor k ∧
    (value, saturated) =
      (((bytes.drop origin).take (cursor - origin)).map UInt8.toNat).foldl
        scanCLoopStep (initial, initialSat)

/-- The generated accumulator expression evaluates correctly in a MiniC state
    for any ASCII digit byte and any in-range magnitude. -/
theorem scanAccumulatorExpr_eval (byte : UInt8) (initial : Nat)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    EvE Gen.prog (scanLoopState byte initial false) scanAccumulatorExpr
      (.int IntTy.i64 (initial * 10 + (byte.toNat - 48))) := by
  let delta := byte.toNat - 48
  have hchar : byte.toNat = 48 + delta := by dsimp [delta]; omega
  have hp : EvE Gen.prog (scanLoopState byte initial false) (.var 3) (.ptr 20 0) := by
    apply EvE.var
    simp [scanLoopState]
  have hload : EvE Gen.prog (scanLoopState byte initial false)
      (.load (.int IntTy.i8) (.var 3)) (.int IntTy.i8 (byte.toNat)) := by
    apply EvE.load hp
    simp [scanLoopState, load, readBytes, decodeLE, Ty.size, IntTy.bytes, IntTy.i8]
  have hcastByte : evalCast IntTy.i32 (.int IntTy.i8 (byte.toNat)) =
      .ok (.int IntTy.i32 (byte.toNat)) := by
    rw [hchar]
    exact scanLoop_ascii_i8_to_i32 delta (by omega)
  have hbyte32 : EvE Gen.prog (scanLoopState byte initial false)
      (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
      (.int IntTy.i32 (byte.toNat)) := EvE.cast hload hcastByte
  have hzero : EvE Gen.prog (scanLoopState byte initial false)
      (.const (.int IntTy.i32 48)) (.int IntTy.i32 48) := EvE.const _
  have hsub : evalBin .sub (some IntTy.i32) (.int IntTy.i32 (byte.toNat))
      (.int IntTy.i32 48) = .ok (.int IntTy.i32 delta) := by
    rw [hchar]
    exact scanLoop_sub_ascii_zero delta (by omega)
  have hdelta32 : EvE Gen.prog (scanLoopState byte initial false)
      (.bin .sub (some IntTy.i32)
        (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
        (.const (.int IntTy.i32 48))) (.int IntTy.i32 delta) :=
    EvE.bin hbyte32 hzero hsub
  have hdelta64 : evalCast IntTy.i64 (.int IntTy.i32 delta) =
      .ok (.int IntTy.i64 delta) := scanLoop_digit_i32_to_i64 delta (by omega)
  have hdelta : EvE Gen.prog (scanLoopState byte initial false)
      (.cast IntTy.i64
        (.bin .sub (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 48)))) (.int IntTy.i64 delta) :=
    EvE.cast hdelta32 hdelta64
  have hv : EvE Gen.prog (scanLoopState byte initial false) (.var 5)
      (.int IntTy.i64 initial) := by
    apply EvE.var
    simp [scanLoopState]
  have hten : EvE Gen.prog (scanLoopState byte initial false)
      (.const (.int IntTy.i32 10)) (.int IntTy.i32 10) := EvE.const _
  have htenCast : evalCast IntTy.i64 (.int IntTy.i32 10) =
      .ok (.int IntTy.i64 10) := by
    simp [evalCast, IntTy.i64, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus]
  have hten64 : EvE Gen.prog (scanLoopState byte initial false)
      (.cast IntTy.i64 (.const (.int IntTy.i32 10))) (.int IntTy.i64 10) :=
    EvE.cast hten htenCast
  have hmul : EvE Gen.prog (scanLoopState byte initial false)
      (.bin .mul (some IntTy.i64) (.var 5)
        (.cast IntTy.i64 (.const (.int IntTy.i32 10))))
      (.int IntTy.i64 (initial * 10)) :=
    EvE.bin hv hten64 (scanLoop_mul_ten_eval initial hinitial)
  have hadd := scanLoop_add_digit_eval initial delta hinitial (by omega)
  exact EvE.bin hmul hdelta hadd

/-- The accumulator expression also evaluates over an arbitrary scanner
    buffer and cursor, given the byte lookup and cursor bounds. -/
theorem scanAccumulatorExpr_eval_at (bytes : Block) (cursor endpoint initial : Nat)
    (byte : UInt8) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    EvE Gen.prog (scanLoopStateAt bytes cursor endpoint initial false)
      scanAccumulatorExpr (.int IntTy.i64 (initial * 10 + (byte.toNat - 48))) := by
  let s := scanLoopStateAt bytes cursor endpoint initial false
  let delta := byte.toNat - 48
  have hchar : byte.toNat = 48 + delta := by dsimp [delta]; omega
  have hp : EvE Gen.prog s (.var 3) (.ptr 20 cursor) := by
    apply EvE.var
    simp [s, scanLoopStateAt]
  have hload : EvE Gen.prog s (.load (.int IntTy.i8) (.var 3))
      (.int IntTy.i8 byte.toNat) := by
    apply EvE.load hp
    exact scanLoop_load_byte_at bytes cursor endpoint initial false byte hcursor hbyteAt
  have hcastByte : evalCast IntTy.i32 (.int IntTy.i8 byte.toNat) =
      .ok (.int IntTy.i32 byte.toNat) := by
    rw [hchar]
    exact scanLoop_ascii_i8_to_i32 delta (by omega)
  have hbyte32 : EvE Gen.prog s
      (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
      (.int IntTy.i32 byte.toNat) := EvE.cast hload hcastByte
  have hzero : EvE Gen.prog s (.const (.int IntTy.i32 48))
      (.int IntTy.i32 48) := EvE.const _
  have hsub : evalBin .sub (some IntTy.i32) (.int IntTy.i32 byte.toNat)
      (.int IntTy.i32 48) = .ok (.int IntTy.i32 delta) := by
    rw [hchar]
    exact scanLoop_sub_ascii_zero delta (by omega)
  have hdelta32 : EvE Gen.prog s
      (.bin .sub (some IntTy.i32)
        (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
        (.const (.int IntTy.i32 48))) (.int IntTy.i32 delta) :=
    EvE.bin hbyte32 hzero hsub
  have hdelta64 : evalCast IntTy.i64 (.int IntTy.i32 delta) =
      .ok (.int IntTy.i64 delta) := scanLoop_digit_i32_to_i64 delta (by omega)
  have hdelta : EvE Gen.prog s
      (.cast IntTy.i64
        (.bin .sub (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 48)))) (.int IntTy.i64 delta) :=
    EvE.cast hdelta32 hdelta64
  have hv : EvE Gen.prog s (.var 5) (.int IntTy.i64 initial) := by
    apply EvE.var
    simp [s, scanLoopStateAt]
  have hten : EvE Gen.prog s (.const (.int IntTy.i32 10))
      (.int IntTy.i32 10) := EvE.const _
  have htenCast : evalCast IntTy.i64 (.int IntTy.i32 10) =
      .ok (.int IntTy.i64 10) := by
    simp [evalCast, IntTy.i64, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus]
  have hten64 : EvE Gen.prog s
      (.cast IntTy.i64 (.const (.int IntTy.i32 10))) (.int IntTy.i64 10) :=
    EvE.cast hten htenCast
  have hmul : EvE Gen.prog s
      (.bin .mul (some IntTy.i64) (.var 5)
        (.cast IntTy.i64 (.const (.int IntTy.i32 10))))
      (.int IntTy.i64 (initial * 10)) :=
    EvE.bin hv hten64 (scanLoop_mul_ten_eval initial hinitial)
  have hadd := scanLoop_add_digit_eval initial delta hinitial (by omega)
  exact EvE.bin hmul hdelta hadd

/-- The accumulator expression also evaluates from any live scanner frame;
    extra locals such as caller pointers and the optional sign are preserved. -/
theorem scanAccumulatorExpr_eval_state_at (s : State) (bytes : Block)
    (cursor initial : Nat) (byte : UInt8)
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hvalueLocal : s.locals 5 = some (.int IntTy.i64 initial))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    EvE Gen.prog s scanAccumulatorExpr
      (.int IntTy.i64 (initial * 10 + (byte.toNat - 48))) := by
  let delta := byte.toNat - 48
  have hchar : byte.toNat = 48 + delta := by dsimp [delta]; omega
  have hload : EvE Gen.prog s (.load (.int IntTy.i8) (.var 3))
      (.int IntTy.i8 byte.toNat) := by
    apply EvE.load (EvE.var hcursorLocal)
    exact scanLoop_load_byte_from_mem s.mem bytes cursor byte hmem hcursor hbyteAt
  have hcastByte : evalCast IntTy.i32 (.int IntTy.i8 byte.toNat) =
      .ok (.int IntTy.i32 byte.toNat) := by
    rw [hchar]
    exact scanLoop_ascii_i8_to_i32 delta (by omega)
  have hbyte32 : EvE Gen.prog s
      (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
      (.int IntTy.i32 byte.toNat) := EvE.cast hload hcastByte
  have hzero : EvE Gen.prog s (.const (.int IntTy.i32 48))
      (.int IntTy.i32 48) := EvE.const _
  have hsub : evalBin .sub (some IntTy.i32) (.int IntTy.i32 byte.toNat)
      (.int IntTy.i32 48) = .ok (.int IntTy.i32 delta) := by
    rw [hchar]
    exact scanLoop_sub_ascii_zero delta (by omega)
  have hdelta32 : EvE Gen.prog s
      (.bin .sub (some IntTy.i32)
        (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
        (.const (.int IntTy.i32 48))) (.int IntTy.i32 delta) :=
    EvE.bin hbyte32 hzero hsub
  have hdelta64 : evalCast IntTy.i64 (.int IntTy.i32 delta) =
      .ok (.int IntTy.i64 delta) := scanLoop_digit_i32_to_i64 delta (by omega)
  have hdelta : EvE Gen.prog s
      (.cast IntTy.i64
        (.bin .sub (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 48)))) (.int IntTy.i64 delta) :=
    EvE.cast hdelta32 hdelta64
  have hv : EvE Gen.prog s (.var 5) (.int IntTy.i64 initial) := EvE.var hvalueLocal
  have hten : EvE Gen.prog s (.const (.int IntTy.i32 10))
      (.int IntTy.i32 10) := EvE.const _
  have htenCast : evalCast IntTy.i64 (.int IntTy.i32 10) =
      .ok (.int IntTy.i64 10) := by
    simp [evalCast, IntTy.i64, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus]
  have hten64 : EvE Gen.prog s
      (.cast IntTy.i64 (.const (.int IntTy.i32 10))) (.int IntTy.i64 10) :=
    EvE.cast hten htenCast
  have hmul : EvE Gen.prog s
      (.bin .mul (some IntTy.i64) (.var 5)
        (.cast IntTy.i64 (.const (.int IntTy.i32 10))))
      (.int IntTy.i64 (initial * 10)) :=
    EvE.bin hv hten64 (scanLoop_mul_ten_eval initial hinitial)
  have hadd := scanLoop_add_digit_eval initial delta hinitial (by omega)
  exact EvE.bin hmul hdelta hadd

/-- Executing the generated accumulator assignment installs the value proved
    by `scanAccumulatorExpr_eval` in local 5. -/
theorem scanAccumulatorAssign_exs (byte : UInt8) (initial : Nat)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    ExS Gen.prog (scanLoopState byte initial false)
      (.set 5 scanAccumulatorExpr) .normal
      { scanLoopState byte initial false with
        locals := (scanLoopState byte initial false).locals.upd 5
          (.int IntTy.i64 (initial * 10 + (byte.toNat - 48))) } := by
  exact ExS.set (scanAccumulatorExpr_eval byte initial hbyte hinitial)

theorem scanAccumulatorAssign_exs_at (bytes : Block) (cursor endpoint initial : Nat)
    (byte : UInt8) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    ExS Gen.prog (scanLoopStateAt bytes cursor endpoint initial false)
      (.set 5 scanAccumulatorExpr) .normal
      { scanLoopStateAt bytes cursor endpoint initial false with
        locals := (scanLoopStateAt bytes cursor endpoint initial false).locals.upd 5
          (.int IntTy.i64 (initial * 10 + (byte.toNat - 48))) } := by
  exact ExS.set (scanAccumulatorExpr_eval_at bytes cursor endpoint initial byte
    hcursor hbyteAt hbyte hinitial)

/-- The generated accumulator assignment followed by its overflow/cap update
    matches one unsaturated mathematical scanner step. -/
theorem scanLoop_accumulate_and_saturate_exs (byte : UInt8) (initial : Nat)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    ExS Gen.prog (scanLoopState byte initial false)
      (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .normal
      (if initial * 10 + (byte.toNat - 48) > 2147483647 then
        { scanLoopState byte initial false with
          locals := Locals.upd (Locals.upd (scanLoopState byte initial false).locals 5
            (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
      else
        { scanLoopState byte initial false with
          locals := Locals.upd (scanLoopState byte initial false).locals 5
            (.int IntTy.i64 (initial * 10 + (byte.toNat - 48))) }) := by
  let candidate := initial * 10 + (byte.toNat - 48)
  let s := scanLoopState byte initial false
  let s' := { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }
  have hassign := scanAccumulatorAssign_exs byte initial hbyte hinitial
  have hcand : candidate ≤ 21474836479 := by dsimp [candidate]; omega
  have hval : EvE Gen.prog s' (.var 5) (.int IntTy.i64 candidate) := by
    apply EvE.var
    simp [s', Locals.upd]
  have hcmp := scanLoop_gt_i64_eval candidate hcand
  have hcond : EvE Gen.prog s'
      (.bin .gt (some IntTy.i64) (.var 5) (.const (.int IntTy.i64 2147483647)))
      (boolVal (decide (candidate > 2147483647))) :=
    EvE.bin hval (EvE.const _) hcmp
  have htruth : truthy (boolVal (decide (candidate > 2147483647))) =
      .ok (decide (candidate > 2147483647)) := by
    cases h : decide (candidate > 2147483647) <;> simp [truthy, boolVal]
  have hsat := scanLoop_saturation_update s' (decide (candidate > 2147483647))
    hcond htruth
  have hseq := ExS.seq hassign hsat
  have hcap : Locals.upd (Locals.upd s.locals 5 (.int IntTy.i64 candidate)) 5
      (.int IntTy.i64 2147483647) = Locals.upd s.locals 5 (.int IntTy.i64 2147483647) := by
    funext i
    by_cases h : i = 5 <;> simp [Locals.upd, h]
  by_cases hoverflow : candidate > 2147483647
  · simpa [s', s, candidate, hoverflow, Locals.upd, hcap] using hseq
  · simpa [s', s, candidate, hoverflow, Locals.upd] using hseq

/-- One unsaturated accumulation and saturation update over an arbitrary
    scanner buffer/cursor. -/
theorem scanLoop_accumulate_and_saturate_at (bytes : Block)
    (cursor endpoint initial : Nat) (byte : UInt8)
    (hcursor : cursor < bytes.length) (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    let candidate := initial * 10 + (byte.toNat - 48)
    ExS Gen.prog (scanLoopStateAt bytes cursor endpoint initial false)
      (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .normal
      (if candidate > 2147483647 then
        { scanLoopStateAt bytes cursor endpoint initial false with
          locals := Locals.upd
            (Locals.upd (scanLoopStateAt bytes cursor endpoint initial false).locals 5
              (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
      else
        { scanLoopStateAt bytes cursor endpoint initial false with
          locals := Locals.upd (scanLoopStateAt bytes cursor endpoint initial false).locals 5
            (.int IntTy.i64 candidate) }) := by
  dsimp only
  let candidate := initial * 10 + (byte.toNat - 48)
  let s := scanLoopStateAt bytes cursor endpoint initial false
  let s' := { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }
  have hassign := scanAccumulatorAssign_exs_at bytes cursor endpoint initial byte
    hcursor hbyteAt hbyte hinitial
  have hcand : candidate ≤ 21474836479 := by dsimp [candidate]; omega
  have hval : EvE Gen.prog s' (.var 5) (.int IntTy.i64 candidate) := by
    apply EvE.var
    simp [s', Locals.upd]
  have hcmp := scanLoop_gt_i64_eval candidate hcand
  have hcond : EvE Gen.prog s'
      (.bin .gt (some IntTy.i64) (.var 5) (.const (.int IntTy.i64 2147483647)))
      (boolVal (decide (candidate > 2147483647))) :=
    EvE.bin hval (EvE.const _) hcmp
  have htruth : truthy (boolVal (decide (candidate > 2147483647))) =
      .ok (decide (candidate > 2147483647)) := by
    cases h : decide (candidate > 2147483647) <;> simp [truthy, boolVal]
  have hsat := scanLoop_saturation_update s' (decide (candidate > 2147483647))
    hcond htruth
  have hseq := ExS.seq hassign hsat
  have hcap : Locals.upd (Locals.upd s.locals 5 (.int IntTy.i64 candidate)) 5
      (.int IntTy.i64 2147483647) = Locals.upd s.locals 5
        (.int IntTy.i64 2147483647) := by
    funext i
    by_cases h : i = 5 <;> simp [Locals.upd, h]
  by_cases hoverflow : candidate > 2147483647
  · simpa [s', s, candidate, hoverflow, Locals.upd, hcap] using hseq
  · simpa [s', s, candidate, hoverflow, Locals.upd] using hseq

/-- Accumulation and saturation in a scanner frame with arbitrary preserved
    locals. -/
theorem scanLoop_accumulate_and_saturate_state_at (s : State) (bytes : Block)
    (cursor initial : Nat) (byte : UInt8)
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hvalueLocal : s.locals 5 = some (.int IntTy.i64 initial))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    let candidate := initial * 10 + (byte.toNat - 48)
    ExS Gen.prog s (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate)
      .normal (if candidate > 2147483647 then
        { s with locals := Locals.upd (Locals.upd s.locals 5
          (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
      else { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }) := by
  dsimp only
  let candidate := initial * 10 + (byte.toNat - 48)
  let s' := { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }
  have hassign : ExS Gen.prog s (.set 5 scanAccumulatorExpr) .normal s' := by
    exact ExS.set (scanAccumulatorExpr_eval_state_at s bytes cursor initial byte
      hcursorLocal hvalueLocal hmem hcursor hbyteAt hbyte hinitial)
  have hcand : candidate ≤ 21474836479 := by dsimp [candidate]; omega
  have hval : EvE Gen.prog s' (.var 5) (.int IntTy.i64 candidate) := by
    apply EvE.var
    simp [s', Locals.upd]
  have hcmp := scanLoop_gt_i64_eval candidate hcand
  have hcond : EvE Gen.prog s'
      (.bin .gt (some IntTy.i64) (.var 5) (.const (.int IntTy.i64 2147483647)))
      (boolVal (decide (candidate > 2147483647))) :=
    EvE.bin hval (EvE.const _) hcmp
  have htruth : truthy (boolVal (decide (candidate > 2147483647))) =
      .ok (decide (candidate > 2147483647)) := by
    cases h : decide (candidate > 2147483647) <;> simp [truthy, boolVal]
  have hsat := scanLoop_saturation_update s' (decide (candidate > 2147483647))
    hcond htruth
  have hseq := ExS.seq hassign hsat
  have hcap : Locals.upd (Locals.upd s.locals 5 (.int IntTy.i64 candidate)) 5
      (.int IntTy.i64 2147483647) = Locals.upd s.locals 5
        (.int IntTy.i64 2147483647) := by
    funext i
    by_cases hi : i = 5 <;> simp [Locals.upd, hi]
  by_cases hoverflow : candidate > 2147483647
  · simpa [s', candidate, hoverflow, Locals.upd, hcap] using hseq
  · simpa [s', candidate, hoverflow, Locals.upd] using hseq

/-- One digit iteration from a live scanner frame. This preserves unrelated
    frame locals (including caller pointers and the sign) while advancing the
    cursor and applying the same saturating accumulator step. -/
theorem scanLoop_digit_iteration_state_at (s : State) (bytes : Block)
    (cursor endpoint initial : Nat) (saturated : Bool) (byte : UInt8)
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hendLocal : s.locals 1 = some (.ptr 20 endpoint))
    (hvalueLocal : s.locals 5 = some (.int IntTy.i64 initial))
    (hsatLocal : s.locals 6 = some (.int IntTy.u8 (if saturated then 1 else 0)))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < endpoint)
    (hnext : cursor + 1 ≤ bytes.length) (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    let candidate := initial * 10 + (byte.toNat - 48)
    let accumulated := if saturated then s else
      if candidate > 2147483647 then
        { s with locals := Locals.upd (Locals.upd s.locals 5
          (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
      else { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }
    let finalState := { accumulated with locals := Locals.upd accumulated.locals 3 (.ptr 20 (cursor + 1)) }
    ExS Gen.prog s scanLoopIterationBody .normal finalState := by
  dsimp only
  let candidate := initial * 10 + (byte.toNat - 48)
  let accumulated := if saturated then s else
    if candidate > 2147483647 then
      { s with locals := Locals.upd (Locals.upd s.locals 5
        (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
    else { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }
  let finalState := { accumulated with locals := Locals.upd accumulated.locals 3 (.ptr 20 (cursor + 1)) }
  have hacc : ExS Gen.prog s
      (.ite (.un .lnot IntTy.i32 (.var 6))
        (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
      .normal accumulated := by
    have hflag : EvE Gen.prog s (.var 6)
        (.int IntTy.u8 (if saturated then 1 else 0)) := EvE.var hsatLocal
    have hnot : EvE Gen.prog s (.un .lnot IntTy.i32 (.var 6))
        (boolVal (!saturated)) := EvE.un hflag (by
          cases saturated <;> simp [evalUn, truthy, boolVal])
    have htruth : truthy (boolVal (!saturated)) = .ok (!saturated) := by
      cases saturated <;> rfl
    apply ExS.ite hnot htruth
    cases saturated with
    | true =>
        simp [accumulated]
        exact ExS.skip
    | false =>
        have hstep := scanLoop_accumulate_and_saturate_state_at s bytes cursor
          initial byte hcursorLocal hvalueLocal hmem (by omega) hbyteAt hbyte hinitial
        simpa [accumulated, candidate] using hstep
  have hcursorAcc : accumulated.locals 3 = some (.ptr 20 cursor) := by
    cases saturated with
    | true => exact hcursorLocal
    | false =>
        by_cases hoverflow : candidate > 2147483647
        · simp [accumulated, hoverflow, Locals.upd, hcursorLocal]
        · simp [accumulated, hoverflow, Locals.upd, hcursorLocal]
  have hmemAcc : accumulated.mem 20 = some bytes := by
    cases saturated with
    | true => exact hmem
    | false =>
        by_cases hoverflow : candidate > 2147483647 <;>
          simp [accumulated, hoverflow, hmem]
  have hcursorStep := scanLoop_cursor_advance_exs accumulated cursor bytes
    hcursorAcc hmemAcc hnext
  have hbody : ExS Gen.prog s
      (.seq
        (.ite (.un .lnot IntTy.i32 (.var 6))
          (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
        (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
      .normal finalState := by
    simpa [finalState] using ExS.seq hacc hcursorStep
  have htrue : truthy (boolVal true) = .ok true := by rfl
  simpa [scanLoopIterationBody] using
    (ExS.ite (scanLoop_digit_guard_state_at s bytes cursor endpoint byte
      hcursorLocal hendLocal hmem hcursor hbyteAt hbyte) htrue hbody)

/-- For an arbitrary in-range scanner cursor, one generated body iteration
    processes a digit, updates saturation/value as needed, and advances. -/
theorem scanLoop_digit_iteration_at (bytes : Block)
    (cursor endpoint initial : Nat) (saturated : Bool) (byte : UInt8)
    (hcursor : cursor < endpoint)
    (hnext : cursor + 1 ≤ bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    let candidate := initial * 10 + (byte.toNat - 48)
    let s := scanLoopStateAt bytes cursor endpoint initial saturated
    let accumulated := if saturated then s else
      if candidate > 2147483647 then
        { s with locals := Locals.upd (Locals.upd s.locals 5
          (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
      else { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }
    ExS Gen.prog s scanLoopIterationBody .normal
      { accumulated with locals := Locals.upd accumulated.locals 3 (.ptr 20 (cursor + 1)) } := by
  dsimp only
  let candidate := initial * 10 + (byte.toNat - 48)
  let s := scanLoopStateAt bytes cursor endpoint initial saturated
  let accumulated := if saturated then s else
    if candidate > 2147483647 then
      { s with locals := Locals.upd (Locals.upd s.locals 5
        (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
    else { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }
  let finalState := { accumulated with locals := Locals.upd accumulated.locals 3 (.ptr 20 (cursor + 1)) }
  have hacc : ExS Gen.prog s
      (.ite (.un .lnot IntTy.i32 (.var 6))
        (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
      .normal accumulated := by
    have hflag : EvE Gen.prog s (.var 6)
        (.int IntTy.u8 (if saturated then 1 else 0)) := by
      apply EvE.var
      simp [s, scanLoopStateAt]
    have hnot : EvE Gen.prog s (.un .lnot IntTy.i32 (.var 6))
        (boolVal (!saturated)) := EvE.un hflag (by
          cases saturated <;> simp [evalUn, truthy, boolVal])
    have htruth : truthy (boolVal (!saturated)) = .ok (!saturated) := by
      cases saturated <;> rfl
    apply ExS.ite hnot htruth
    by_cases hsaturated : saturated
    · simp [accumulated, s, hsaturated]
      exact ExS.skip
    · have hstep := scanLoop_accumulate_and_saturate_at bytes cursor endpoint
        initial byte (by omega) hbyteAt hbyte hinitial
      simpa [accumulated, s, hsaturated, candidate] using hstep
  have hcursorStep : ExS Gen.prog accumulated
      (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1))
      .normal finalState := by
    have hmem : accumulated.mem 20 = some bytes := by
      by_cases hsaturated : saturated
      · simp [accumulated, s, hsaturated, scanLoopStateAt]
      · by_cases hoverflow : candidate > 2147483647 <;>
          simp [accumulated, s, hsaturated, hoverflow, scanLoopStateAt]
    apply scanLoop_cursor_advance_exs accumulated cursor bytes
    · by_cases hsaturated : saturated
      · simp [accumulated, s, hsaturated, scanLoopStateAt]
      · by_cases hoverflow : candidate > 2147483647 <;>
          simp [accumulated, s, hsaturated, hoverflow, candidate, scanLoopStateAt,
            Locals.upd]
    · exact hmem
    · exact hnext
  have hbody : ExS Gen.prog s
      (.seq
        (.ite (.un .lnot IntTy.i32 (.var 6))
          (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
        (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
      .normal finalState := ExS.seq hacc hcursorStep
  have htrue : truthy (boolVal true) = .ok true := by rfl
  simpa [scanLoopIterationBody, s, finalState] using
    (ExS.ite (scanLoop_digit_guard_at bytes cursor endpoint initial saturated byte
      hcursor hbyteAt hbyte) htrue hbody)

/-- If a finite prefix consists of digits and its boundary is either the input
    endpoint or a non-digit, the translated loop terminates at that boundary. -/
theorem scanLoop_terminates_prefix (bytes : Block) (endpoint start stop initial : Nat)
    (saturated : Bool)
    (hstart : start ≤ stop) (hstop : stop ≤ endpoint)
    (hend : endpoint ≤ bytes.length)
    (hboundary : stop = endpoint ∨ (stop < endpoint ∧ ∃ byte,
      bytes[stop]? = some byte ∧ (byte.toNat < 48 ∨ 57 < byte.toNat)))
    (hprefix : scanLoopDigitsFrom bytes start (stop - start))
    (hinitial : initial ≤ 2147483647)
    (hsaturated : saturated = true → initial = 2147483647) :
    ∃ finalState, ExS Gen.prog (scanLoopStateAt bytes start endpoint initial saturated)
      Gen.tobj_scan_int_loop0 .normal finalState ∧
      ∃ value finalSat, finalState = scanLoopStateAt bytes stop endpoint value finalSat ∧
        (value, finalSat) =
          (((bytes.drop start).take (stop - start)).map UInt8.toNat).foldl
            scanCLoopStep (initial, saturated) := by
  let P := scanLoopPrefixInvariant bytes endpoint stop start initial saturated
  let Q := fun s => ∃ value finalSat,
    s = scanLoopStateAt bytes stop endpoint value finalSat ∧
    (value, finalSat) =
      (((bytes.drop start).take (stop - start)).map UInt8.toNat).foldl
        scanCLoopStep (initial, saturated)
  have hinv : P (stop - start)
      (scanLoopStateAt bytes start endpoint initial saturated) := by
    refine ⟨start, initial, saturated, Nat.le_refl start, ?_, hinitial, hsaturated,
      rfl, hprefix, ?_⟩
    · omega
    · simp [Nat.sub_self]
  have hstep : ∀ k s, P (k + 1) s → ∃ s1 s2,
      ExS Gen.prog s scanLoopIterationBody .normal s1 ∧
      ExS Gen.prog s1 .skip .normal s2 ∧ P k s2 := by
    intro k s hs
    obtain ⟨cursor, value, sat, horigin, hpos, hvalue, hsat, rfl,
      hdigits, hfold⟩ := hs
    obtain ⟨byte, hbyteAt, hbyteLo, hbyteHi⟩ := hdigits 0 (by omega)
    have hbyteAt' : bytes[cursor]? = some byte := by simpa using hbyteAt
    have hcursorEnd : cursor < endpoint := by omega
    have hcursorMem : cursor < bytes.length := by
      have hget := (List.getElem?_eq_some_iff.mp hbyteAt).choose
      exact hget
    have hnext : cursor + 1 ≤ bytes.length := by omega
    let candidate := value * 10 + (byte.toNat - 48)
    let nextValue := if sat then value else
      if candidate > 2147483647 then 2147483647 else candidate
    let nextSat := if sat then true else decide (candidate > 2147483647)
    let s1 := scanLoopStateAt bytes cursor endpoint value sat
    let accumulated := if sat then s1 else
      if candidate > 2147483647 then
        { s1 with locals := Locals.upd (Locals.upd s1.locals 5
          (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
      else { s1 with locals := Locals.upd s1.locals 5 (.int IntTy.i64 candidate) }
    let s2 := { accumulated with locals := Locals.upd accumulated.locals 3 (.ptr 20 (cursor + 1)) }
    have hiter := scanLoop_digit_iteration_at bytes cursor endpoint value sat byte
      hcursorEnd hnext hbyteAt' ⟨hbyteLo, hbyteHi⟩ hvalue
    have hiter' : ExS Gen.prog (scanLoopStateAt bytes cursor endpoint value sat)
        scanLoopIterationBody .normal s2 := by
      cases sat <;> by_cases hoverflow : candidate > 2147483647 <;>
        simpa [s2, accumulated, s1, candidate, scanLoopStateAt, Locals.upd,
          hoverflow] using hiter
    have hstate2 : s2 = scanLoopStateAt bytes (cursor + 1) endpoint nextValue nextSat := by
      cases sat <;> by_cases hoverflow : candidate > 2147483647
      all_goals
        dsimp [s2, scanLoopStateAt, accumulated, s1, hoverflow]
        rw [State.mk.injEq]
        constructor
        · funext i
          by_cases h1 : i = 1
          · subst i
            simp [nextValue, nextSat, candidate, Locals.upd, hoverflow]
          · by_cases h3 : i = 3
            · subst i
              simp [nextValue, nextSat, candidate, Locals.upd, hoverflow]
            · by_cases h5 : i = 5
              · subst i
                simp [nextValue, nextSat, candidate, Locals.upd, hoverflow]
              · by_cases h6 : i = 6
                · subst i
                  simp [nextValue, nextSat, candidate, Locals.upd, hoverflow]
                · simp [h1, h3, h5, h6, nextValue, nextSat, candidate,
                    Locals.upd, hoverflow]
        constructor
        · funext b
          by_cases hb : b = 20 <;>
            simp [hb, nextValue, nextSat, candidate, Locals.upd, hoverflow]
        · simp [nextValue, nextSat, candidate, Locals.upd, hoverflow]
    have hnextValue : nextValue ≤ 2147483647 := by
      by_cases hs : sat
      · simp [nextValue, hs, hvalue]
      · by_cases ho : candidate > 2147483647 <;> simp [nextValue, hs, ho] <;> omega
    have hnextSat : nextSat = true → nextValue = 2147483647 := by
      intro h
      by_cases hs : sat
      · simp [nextSat, nextValue, hs, hsat hs]
      · have hdec : decide (candidate > 2147483647) = true := by
          simpa [nextSat, hs] using h
        have hgt : candidate > 2147483647 := of_decide_eq_true hdec
        simp [nextSat, nextValue, hs, hgt]
    have hbyteAtSuffix : (bytes.drop start)[cursor - start]? = some byte := by
      rw [List.getElem?_drop]
      have hidx : start + (cursor - start) = cursor := by omega
      rw [hidx]
      exact hbyteAt'
    let processed := (bytes.drop start).take (cursor - start)
    have hprocessed :
        (bytes.drop start).take (cursor + 1 - start) = processed ++ [byte] := by
      have htake := scanLoop_take_succ_append (bytes.drop start) (cursor - start)
        byte hbyteAtSuffix
      have hidx : cursor + 1 - start = (cursor - start) + 1 := by omega
      simpa [processed, hidx]
        using htake
    have hstepFold : scanCLoopStep (value, sat) byte.toNat =
        (nextValue, nextSat) := by
      cases sat <;> by_cases hoverflow : candidate > 2147483647 <;>
        simp [scanCLoopStep, nextValue, nextSat, candidate, hoverflow]
    have hfoldNext : (nextValue, nextSat) =
        (((bytes.drop start).take (cursor + 1 - start)).map UInt8.toNat).foldl
          scanCLoopStep (initial, saturated) := by
      rw [hprocessed, List.map_append, List.foldl_append]
      change (nextValue, nextSat) = scanCLoopStep
        ((((bytes.drop start).take (cursor - start)).map UInt8.toNat).foldl
          scanCLoopStep (initial, saturated)) byte.toNat
      rw [← hfold]
      exact hstepFold.symm
    have hdigits' : scanLoopDigitsFrom bytes (cursor + 1) k := by
      intro offset hoff
      obtain ⟨b, hbAt, hbLo, hbHi⟩ := hdigits (offset + 1) (by omega)
      refine ⟨b, ?_, hbLo, hbHi⟩
      have hidx : cursor + 1 + offset = cursor + (offset + 1) := by omega
      rw [hidx]
      exact hbAt
    refine ⟨s2, s2, hiter', ExS.skip, ?_⟩
    exact ⟨cursor + 1, nextValue, nextSat, by omega, by omega, hnextValue,
      hnextSat, hstate2, hdigits', hfoldNext⟩
  have hexit : ∀ s, P 0 s → ∃ s1,
      ExS Gen.prog s scanLoopIterationBody .brk s1 ∧ Q s1 := by
    intro s hs
    obtain ⟨cursor, value, sat, horigin, hpos, hvalue, hsat, rfl, _, hfold⟩ := hs
    have hcursorStop : cursor = stop := by omega
    subst cursor
    rcases hboundary with hboundary | ⟨hcursorEnd, byte, hbyteAt, hnondigit⟩
    · have heq : endpoint = stop := hboundary.symm
      subst endpoint
      refine ⟨scanLoopStateAt bytes stop stop value sat,
        scanLoop_break_at_endpoint bytes stop value sat, ?_⟩
      refine ⟨value, sat, rfl, ?_⟩
      simpa using hfold
    ·
      have hcursorMem : stop < bytes.length := by omega
      refine ⟨scanLoopStateAt bytes stop endpoint value sat,
        scanLoop_break_at_nondigit bytes stop endpoint value sat byte
          hcursorEnd hbyteAt hcursorMem hnondigit, ?_⟩
      refine ⟨value, sat, rfl, ?_⟩
      simpa using hfold
  obtain ⟨finalState, hloop, hpost⟩ :=
    ExS.loop_decreasing_post hinv hstep hexit
  exact ⟨finalState, by
    simpa [P, scanLoop_ast_factor, scanLoopBodyFactored,
      scanLoopIterationBody, scanLoopDigitGuard] using hloop, hpost⟩

/-- The explicit-prefix termination proof, lifted to a scanner frame that
    retains unrelated locals and memory while the digit loop updates its own
    cursor, accumulator, and saturation locals. -/
theorem scanLoop_terminates_prefix_in_frame (base : State) (bytes : Block)
    (stop start initial : Nat) (saturated : Bool)
    (hendLocal : base.locals 1 = some (.ptr 20 (bytes.length)))
    (hmem : base.mem 20 = some bytes)
    (hstart : start ≤ stop) (hstop : stop ≤ bytes.length)
    (hboundary : stop = bytes.length ∨ (stop < bytes.length ∧ ∃ byte,
      bytes[stop]? = some byte ∧ (byte.toNat < 48 ∨ 57 < byte.toNat)))
    (hprefix : scanLoopDigitsFrom bytes start (stop - start))
    (hinitial : initial ≤ 2147483647)
    (hsaturated : saturated = true → initial = 2147483647) :
    ∃ finalState, ExS Gen.prog (scanLoopFrameAt base start initial saturated)
      Gen.tobj_scan_int_loop0 .normal finalState ∧
      ∃ value finalSat,
        finalState = scanLoopFrameAt base stop value finalSat ∧
        (value, finalSat) =
          (((bytes.drop start).take (stop - start)).map UInt8.toNat).foldl
            scanCLoopStep (initial, saturated) := by
  let P := scanLoopFramePrefixInvariant base bytes (bytes.length) stop start
    initial saturated
  let Q := fun s => ∃ value finalSat,
    s = scanLoopFrameAt base stop value finalSat ∧
    (value, finalSat) =
      (((bytes.drop start).take (stop - start)).map UInt8.toNat).foldl
        scanCLoopStep (initial, saturated)
  have hinv : P (stop - start)
      (scanLoopFrameAt base start initial saturated) := by
    refine ⟨start, initial, saturated, Nat.le_refl start, ?_, hinitial,
      hsaturated, rfl, hprefix, ?_⟩
    · omega
    · simp [Nat.sub_self]
  have hstep : ∀ k s, P (k + 1) s → ∃ s1 s2,
      ExS Gen.prog s scanLoopIterationBody .normal s1 ∧
      ExS Gen.prog s1 .skip .normal s2 ∧ P k s2 := by
    intro k s hs
    obtain ⟨cursor, value, sat, horigin, hpos, hvalue, hsat, hsframe,
      hdigits, hfold⟩ := hs
    subst s
    obtain ⟨byte, hbyteAt, hbyteLo, hbyteHi⟩ := hdigits 0 (by omega)
    have hbyteAt' : bytes[cursor]? = some byte := by simpa using hbyteAt
    have hcursorEnd : cursor < bytes.length := by omega
    have hnext : cursor + 1 ≤ bytes.length := by omega
    have hcursorLocal : (scanLoopFrameAt base cursor value sat).locals 3 =
        some (.ptr 20 cursor) := by simp [scanLoopFrameAt, Locals.upd]
    have hend : (scanLoopFrameAt base cursor value sat).locals 1 =
        some (.ptr 20 bytes.length) := by
      simp [scanLoopFrameAt, Locals.upd, hendLocal]
    have hvalueLocal : (scanLoopFrameAt base cursor value sat).locals 5 =
        some (.int IntTy.i64 value) := by simp [scanLoopFrameAt, Locals.upd]
    have hsatLocal : (scanLoopFrameAt base cursor value sat).locals 6 =
        some (.int IntTy.u8 (if sat then 1 else 0)) := by
      simp [scanLoopFrameAt, Locals.upd]
    let candidate := value * 10 + (byte.toNat - 48)
    let nextValue := if sat then value else
      if candidate > 2147483647 then 2147483647 else candidate
    let nextSat := if sat then true else decide (candidate > 2147483647)
    let accumulated := if sat then scanLoopFrameAt base cursor value sat else
      if candidate > 2147483647 then
        { scanLoopFrameAt base cursor value sat with
          locals := Locals.upd (Locals.upd
            (scanLoopFrameAt base cursor value sat).locals 5
            (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
      else { scanLoopFrameAt base cursor value sat with
        locals := Locals.upd (scanLoopFrameAt base cursor value sat).locals 5
          (.int IntTy.i64 candidate) }
    let s2 := { accumulated with locals := Locals.upd accumulated.locals 3 (.ptr 20 (cursor + 1)) }
    have hiter := scanLoop_digit_iteration_state_at
      (scanLoopFrameAt base cursor value sat) bytes cursor bytes.length value sat byte
      hcursorLocal hend hvalueLocal hsatLocal hmem hcursorEnd hnext hbyteAt'
      ⟨hbyteLo, hbyteHi⟩ hvalue
    have hiter' : ExS Gen.prog (scanLoopFrameAt base cursor value sat)
        scanLoopIterationBody .normal s2 := by
      cases sat <;> by_cases hoverflow : candidate > 2147483647 <;>
        simpa [s2, accumulated, candidate, scanLoopFrameAt, Locals.upd,
          hoverflow] using hiter
    have hstate2 : s2 = scanLoopFrameAt base (cursor + 1) nextValue nextSat := by
      cases sat <;> by_cases hoverflow : candidate > 2147483647 <;>
        all_goals
          rw [State.mk.injEq]
          constructor
          · funext i
            by_cases h3 : i = 3
            · subst i
              simp [s2, accumulated, nextValue, nextSat, candidate,
                scanLoopFrameAt, Locals.upd, hoverflow]
            · by_cases h5 : i = 5
              · subst i
                simp [s2, accumulated, nextValue, nextSat, candidate,
                  scanLoopFrameAt, Locals.upd, hoverflow]
              · by_cases h6 : i = 6
                · subst i
                  simp [s2, accumulated, nextValue, nextSat, candidate,
                    scanLoopFrameAt, Locals.upd, hoverflow]
                · simp [s2, accumulated, nextValue, nextSat, candidate,
                    scanLoopFrameAt, Locals.upd, hoverflow, h3, h5, h6]
          constructor
          · simp [s2, accumulated, scanLoopFrameAt, hoverflow]
          · simp [s2, accumulated, scanLoopFrameAt, hoverflow]
    have hnextValue : nextValue ≤ 2147483647 := by
      by_cases hs : sat
      · simp [nextValue, hs, hvalue]
      · by_cases ho : candidate > 2147483647 <;>
          simp [nextValue, hs, ho] <;> omega
    have hnextSat : nextSat = true → nextValue = 2147483647 := by
      intro h
      by_cases hs : sat
      · simp [nextSat, nextValue, hs, hsat hs]
      · have hdec : decide (candidate > 2147483647) = true := by
          simpa [nextSat, hs] using h
        have hgt : candidate > 2147483647 := of_decide_eq_true hdec
        simp [nextSat, nextValue, hs, hgt]
    have hbyteAtSuffix : (bytes.drop start)[cursor - start]? = some byte := by
      rw [List.getElem?_drop]
      have hidx : start + (cursor - start) = cursor := by omega
      rw [hidx]
      exact hbyteAt'
    let processed := (bytes.drop start).take (cursor - start)
    have hprocessed :
        (bytes.drop start).take (cursor + 1 - start) = processed ++ [byte] := by
      have htake := scanLoop_take_succ_append (bytes.drop start) (cursor - start)
        byte hbyteAtSuffix
      have hidx : cursor + 1 - start = (cursor - start) + 1 := by omega
      simpa [processed, hidx] using htake
    have hstepFold : scanCLoopStep (value, sat) byte.toNat =
        (nextValue, nextSat) := by
      cases sat <;> by_cases hoverflow : candidate > 2147483647 <;>
        simp [scanCLoopStep, nextValue, nextSat, candidate, hoverflow]
    have hfoldNext : (nextValue, nextSat) =
        (((bytes.drop start).take (cursor + 1 - start)).map UInt8.toNat).foldl
          scanCLoopStep (initial, saturated) := by
      rw [hprocessed, List.map_append, List.foldl_append]
      change (nextValue, nextSat) = scanCLoopStep
        ((((bytes.drop start).take (cursor - start)).map UInt8.toNat).foldl
          scanCLoopStep (initial, saturated)) byte.toNat
      rw [← hfold]
      exact hstepFold.symm
    have hdigits' : scanLoopDigitsFrom bytes (cursor + 1) k := by
      intro offset hoff
      obtain ⟨b, hbAt, hbLo, hbHi⟩ := hdigits (offset + 1) (by omega)
      refine ⟨b, ?_, hbLo, hbHi⟩
      have hidx : cursor + 1 + offset = cursor + (offset + 1) := by omega
      rw [hidx]
      exact hbAt
    refine ⟨s2, s2, hiter', ExS.skip, ?_⟩
    exact ⟨cursor + 1, nextValue, nextSat, by omega, by omega, hnextValue,
      hnextSat, hstate2, hdigits', hfoldNext⟩
  have hexit : ∀ s, P 0 s → ∃ s1,
      ExS Gen.prog s scanLoopIterationBody .brk s1 ∧ Q s1 := by
    intro s hs
    obtain ⟨cursor, value, sat, horigin, hpos, hvalue, hsat, hsframe,
      _hdigits, hfold⟩ := hs
    subst s
    have hcursorStop : cursor = stop := by omega
    subst cursor
    rcases hboundary with hboundary | ⟨hcursorEnd, byte, hbyteAt, hnondigit⟩
    · have heq : bytes.length = stop := hboundary.symm
      have hendBase : base.locals 1 = some (.ptr 20 stop) := by
        simpa [heq] using hendLocal
      have hcursorLocal : (scanLoopFrameAt base stop value sat).locals 3 =
          some (.ptr 20 stop) := by simp [scanLoopFrameAt, Locals.upd]
      have hend : (scanLoopFrameAt base stop value sat).locals 1 =
          some (.ptr 20 stop) := by simp [scanLoopFrameAt, Locals.upd, hendBase]
      refine ⟨scanLoopFrameAt base stop value sat,
        scanLoop_break_at_endpoint_state _ stop hcursorLocal hend, ?_⟩
      refine ⟨value, sat, rfl, ?_⟩
      simpa using hfold
    · have hbyteBound : stop < bytes.length := by omega
      have hcursorLocal : (scanLoopFrameAt base stop value sat).locals 3 =
          some (.ptr 20 stop) := by simp [scanLoopFrameAt, Locals.upd]
      have hend : (scanLoopFrameAt base stop value sat).locals 1 =
          some (.ptr 20 bytes.length) := by
        simp [scanLoopFrameAt, Locals.upd, hendLocal]
      refine ⟨scanLoopFrameAt base stop value sat,
        scanLoop_break_at_nondigit_state _ bytes stop bytes.length byte
          hcursorLocal hend hmem hcursorEnd hbyteAt hbyteBound hnondigit, ?_⟩
      refine ⟨value, sat, rfl, ?_⟩
      simpa using hfold
  obtain ⟨finalState, hloop, hpost⟩ := ExS.loop_decreasing_post hinv hstep hexit
  exact ⟨finalState, by
    simpa [P, scanLoop_ast_factor, scanLoopBodyFactored,
      scanLoopIterationBody, scanLoopDigitGuard] using hloop, hpost⟩

/-- Run the complete maximal digit loop inside a real scanner frame. This is
    the loop refinement used to connect scanner setup to post-loop stores. -/
theorem scanLoop_terminates_takeWhile_in_frame (base : State) (bytes : Block)
    (start initial : Nat) (saturated : Bool)
    (hendLocal : base.locals 1 = some (.ptr 20 bytes.length))
    (hmem : base.mem 20 = some bytes) (hstart : start ≤ bytes.length)
    (hinitial : initial ≤ 2147483647)
    (hsaturated : saturated = true → initial = 2147483647) :
    ∃ finalState value finalSat,
      ExS Gen.prog (scanLoopFrameAt base start initial saturated)
        Gen.tobj_scan_int_loop0 .normal finalState ∧
      finalState = scanLoopFrameAt base
        (start + (scanDigits ((bytes.drop start).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((bytes.drop start).map UInt8.toNat) (initial, saturated) := by
  let suffix := bytes.drop start
  let digitPrefix := suffix.takeWhile (fun byte => scanDigit byte.toNat)
  let stop := start + digitPrefix.length
  have hdropLen : suffix.length = bytes.length - start := by simp [suffix]
  have hprefixList : digitPrefix <+: suffix := List.takeWhile_prefix _
  have hprefixLen : digitPrefix.length ≤ suffix.length := hprefixList.length_le
  have hstop : stop ≤ bytes.length := by dsimp [stop]; omega
  have hstartStop : start ≤ stop := by dsimp [stop]; omega
  have hprefix : scanLoopDigitsFrom bytes start digitPrefix.length := by
    simpa [suffix, digitPrefix] using scanLoop_takeWhile_digits bytes start
  have hprefixCount : scanLoopDigitsFrom bytes start (stop - start) := by
    have hcount : stop - start = digitPrefix.length := by dsimp [stop]; omega
    rw [hcount]
    exact hprefix
  have hboundary : stop = bytes.length ∨ (stop < bytes.length ∧ ∃ byte,
      bytes[stop]? = some byte ∧ (byte.toNat < 48 ∨ 57 < byte.toNat)) := by
    by_cases hfull : digitPrefix.length = suffix.length
    · left
      dsimp [stop]
      rw [hfull, hdropLen]
      omega
    · have hshort : digitPrefix.length < suffix.length := by omega
      obtain ⟨byte, hbyteAtSuffix, hnotDigit⟩ :=
        scanLoop_takeWhile_boundary suffix hshort
      have hbyteAt : bytes[stop]? = some byte := by
        dsimp [stop, suffix] at *
        simpa only [List.getElem?_drop] using hbyteAtSuffix
      have hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat := by
        simp [scanDigit] at hnotDigit
        omega
      right
      exact ⟨by dsimp [stop]; omega, byte, hbyteAt, hnondigit⟩
  obtain ⟨finalState, hloop, hpost⟩ :=
    scanLoop_terminates_prefix_in_frame base bytes stop start initial saturated
      hendLocal hmem hstartStop hstop hboundary hprefixCount hinitial hsaturated
  have hcount := scanLoop_takeWhile_count bytes start
  rcases hpost with ⟨value, finalSat, hstate, hfold⟩
  refine ⟨finalState, value, finalSat, hloop, ?_, ?_⟩
  · rw [← hcount]
    simpa [stop] using hstate
  · have hstopCount : stop - start = digitPrefix.length := by
      dsimp [stop]
      omega
    have htakePrefix : suffix.take digitPrefix.length = digitPrefix := by
      obtain ⟨tail, hconcat⟩ := hprefixList
      rw [← hconcat, List.take_append_of_le_length (by simp)]
      simp
    rw [hstopCount, htakePrefix] at hfold
    have hprefixMap : digitPrefix.map UInt8.toNat =
        (suffix.map UInt8.toNat).takeWhile scanDigit := by
      dsimp [digitPrefix]
      rw [List.takeWhile_map]
      rfl
    simpa [scanCLoopFold, hprefixMap, suffix] using hfold

/-- Instantiate the explicit-prefix loop proof with the pure maximal digit
    prefix of the remaining input. The signed-i8 promotion maps high bytes to
    negative integers, which also fail the generated digit predicate. -/
theorem scanLoop_terminates_takeWhile (bytes : Block) (start initial : Nat)
    (saturated : Bool) (hstart : start ≤ bytes.length)
    (hinitial : initial ≤ 2147483647)
    (hsaturated : saturated = true → initial = 2147483647) :
    ∃ finalState value finalSat,
      ExS Gen.prog (scanLoopStateAt bytes start bytes.length initial saturated)
        Gen.tobj_scan_int_loop0 .normal finalState ∧
      finalState = scanLoopStateAt bytes
        (start + (scanDigits ((bytes.drop start).map UInt8.toNat) 0).1)
        bytes.length value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((bytes.drop start).map UInt8.toNat) (initial, saturated) := by
  let suffix := bytes.drop start
  let digitPrefix := suffix.takeWhile (fun byte => scanDigit byte.toNat)
  let stop := start + digitPrefix.length
  have hdropLen : suffix.length = bytes.length - start := by
    simp [suffix]
  have hprefixList : digitPrefix <+: suffix := List.takeWhile_prefix _
  have hprefixLen : digitPrefix.length ≤ suffix.length := hprefixList.length_le
  have hstop : stop ≤ bytes.length := by dsimp [stop]; omega
  have hstartStop : start ≤ stop := by dsimp [stop]; omega
  have hprefix : scanLoopDigitsFrom bytes start digitPrefix.length := by
    simpa [suffix, digitPrefix] using scanLoop_takeWhile_digits bytes start
  have hprefixCount : scanLoopDigitsFrom bytes start (stop - start) := by
    have hcount : stop - start = digitPrefix.length := by dsimp [stop]; omega
    rw [hcount]
    exact hprefix
  have hboundary : stop = bytes.length ∨ (stop < bytes.length ∧ ∃ byte,
      bytes[stop]? = some byte ∧ (byte.toNat < 48 ∨ 57 < byte.toNat)) := by
    by_cases hfull : digitPrefix.length = suffix.length
    · left
      dsimp [stop]
      rw [hfull, hdropLen]
      omega
    · have hshort : digitPrefix.length < suffix.length := by omega
      obtain ⟨byte, hbyteAtSuffix, hnotDigit⟩ :=
        scanLoop_takeWhile_boundary suffix hshort
      have hbyteAt : bytes[stop]? = some byte := by
        dsimp [stop, suffix] at *
        simpa only [List.getElem?_drop] using hbyteAtSuffix
      have hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat := by
        simp [scanDigit] at hnotDigit
        omega
      right
      exact ⟨by dsimp [stop]; omega, byte, hbyteAt, hnondigit⟩
  obtain ⟨finalState, hloop, hpost⟩ :=
    scanLoop_terminates_prefix bytes bytes.length start stop initial saturated
      hstartStop hstop (by omega) hboundary hprefixCount hinitial hsaturated
  have hcount := scanLoop_takeWhile_count bytes start
  rcases hpost with ⟨value, finalSat, hstate⟩
  refine ⟨finalState, value, finalSat, hloop, ?_, ?_⟩
  · rw [← hcount]
    simpa [stop] using hstate.1
  · have hstopCount : stop - start = digitPrefix.length := by
      dsimp [stop]
      omega
    have htakePrefix : suffix.take digitPrefix.length = digitPrefix := by
      obtain ⟨tail, hconcat⟩ := hprefixList
      rw [← hconcat, List.take_append_of_le_length (by simp)]
      simp
    have hfoldPrefix := hstate.2
    rw [hstopCount, htakePrefix] at hfoldPrefix
    have hprefixMap : digitPrefix.map UInt8.toNat =
        (suffix.map UInt8.toNat).takeWhile scanDigit := by
      dsimp [digitPrefix]
      rw [List.takeWhile_map]
      rfl
    simpa [scanCLoopFold, hprefixMap, suffix] using hfoldPrefix

/-- From the scanner's initial accumulator state, the translated digit loop
    finishes at the pure scanner's exact consumed cursor and folded value. -/
theorem scanLoop_terminates_takeWhile_zero (bytes : Block) (start : Nat)
    (hstart : start ≤ bytes.length) :
    ∃ finalState value finalSat,
      ExS Gen.prog (scanLoopStateAt bytes start bytes.length 0 false)
        Gen.tobj_scan_int_loop0 .normal finalState ∧
      finalState = scanLoopStateAt bytes
        (start + (scanDigits ((bytes.drop start).map UInt8.toNat) 0).1)
        bytes.length value finalSat ∧
      value = (scanDigits ((bytes.drop start).map UInt8.toNat) 0).2 := by
  obtain ⟨finalState, value, finalSat, hloop, hstate, hfold⟩ :=
    scanLoop_terminates_takeWhile bytes start 0 false hstart (by omega) (by simp)
  have hvalue : value =
      (scanDigits ((bytes.drop start).map UInt8.toNat) 0).2 := by
    simpa [scanCLoopFold_scanDigits] using congrArg Prod.fst hfold
  exact ⟨finalState, value, finalSat, hloop, hstate, hvalue⟩

/-- For an unsaturated scanner state and an ASCII digit, the generated loop
    body performs accumulation, saturation, and cursor advancement in one
    terminating MiniC iteration. -/
theorem scanLoop_digit_iteration_exs (byte : UInt8) (initial : Nat)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hinitial : initial ≤ 2147483647) :
    let candidate := initial * 10 + (byte.toNat - 48)
    let s := scanLoopState byte initial false
    let accumulated := if candidate > 2147483647 then
      { s with locals := Locals.upd (Locals.upd s.locals 5
        (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
    else { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }
    ExS Gen.prog s scanLoopIterationBody .normal
      { accumulated with locals := Locals.upd accumulated.locals 3 (.ptr 20 1) } := by
  dsimp only
  let candidate := initial * 10 + (byte.toNat - 48)
  let s := scanLoopState byte initial false
  let accumulated := if candidate > 2147483647 then
    { s with locals := Locals.upd (Locals.upd s.locals 5
      (.int IntTy.i64 2147483647)) 6 (.int IntTy.u8 1) }
  else { s with locals := Locals.upd s.locals 5 (.int IntTy.i64 candidate) }
  let finalState := { accumulated with locals := Locals.upd accumulated.locals 3 (.ptr 20 1) }
  have hacc := scanLoop_accumulate_and_saturate_exs byte initial hbyte hinitial
  have hcursor : ExS Gen.prog accumulated
      (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)) .normal finalState := by
    apply scanLoop_cursor_advance_exs accumulated 0 [byte, 0]
    · dsimp [accumulated, s, candidate]
      by_cases hoverflow : initial * 10 + (byte.toNat - 48) > 2147483647 <;>
        simp [hoverflow, Locals.upd, scanLoopState]
    · by_cases hoverflow : candidate > 2147483647
      · simp [accumulated, s, candidate, hoverflow, scanLoopState]
      · simp [accumulated, s, candidate, hoverflow, scanLoopState]
    · simp
  have hflag : EvE Gen.prog s (.var 6) (.int IntTy.u8 0) := by
    apply EvE.var
    dsimp [s, scanLoopState]
  have hnot : EvE Gen.prog s (.un .lnot IntTy.i32 (.var 6)) (boolVal true) :=
    EvE.un hflag (by rfl)
  have htruth : truthy (boolVal true) = .ok true := by rfl
  have hinner : ExS Gen.prog s
      (.ite (.un .lnot IntTy.i32 (.var 6))
        (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
      .normal accumulated := by
    apply ExS.ite hnot htruth
    exact hacc
  have hbody : ExS Gen.prog s
      (.seq
        (.ite (.un .lnot IntTy.i32 (.var 6))
          (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
        (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
      .normal finalState := ExS.seq hinner hcursor
  exact ExS.ite (scanLoop_digit_guard byte initial false hbyte)
    htruth hbody

/-- When the invariant says the scanner is already saturated, a digit still
    passes the guard and advances the cursor while preserving the capped value. -/
theorem scanLoop_digit_iteration_saturated_exs (byte : UInt8)
    (hbyte : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57) :
    ExS Gen.prog (scanLoopState byte 2147483647 true) scanLoopIterationBody .normal
      { scanLoopState byte 2147483647 true with
        locals := (scanLoopState byte 2147483647 true).locals.upd 3 (.ptr 20 1) } := by
  let s := scanLoopState byte 2147483647 true
  have hflag : EvE Gen.prog s (.var 6) (.int IntTy.u8 1) := by
    apply EvE.var
    dsimp [s, scanLoopState]
  have hnot : EvE Gen.prog s (.un .lnot IntTy.i32 (.var 6)) (boolVal false) :=
    EvE.un hflag (by rfl)
  have hfalse : truthy (boolVal false) = .ok false := by rfl
  have hinner : ExS Gen.prog s
      (.ite (.un .lnot IntTy.i32 (.var 6))
        (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
      .normal s := ExS.ite hnot hfalse ExS.skip
  have hcursor : ExS Gen.prog s
      (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)) .normal
      { s with locals := Locals.upd s.locals 3 (.ptr 20 1) } := by
    apply scanLoop_cursor_advance_exs s 0 [byte, 0]
    · dsimp [s, scanLoopState]
    · dsimp [s, scanLoopState]
    · simp
  have hbody : ExS Gen.prog s
      (.seq
        (.ite (.un .lnot IntTy.i32 (.var 6))
          (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
        (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
      .normal { s with locals := Locals.upd s.locals 3 (.ptr 20 1) } :=
    ExS.seq hinner hcursor
  have hbody' : ExS Gen.prog (scanLoopState byte 2147483647 true)
      (.seq
        (.ite (.un .lnot IntTy.i32 (.var 6))
          (.seq (.set 5 scanAccumulatorExpr) scanLoopSaturationUpdate) .skip)
        (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
      .normal { scanLoopState byte 2147483647 true with
        locals := (scanLoopState byte 2147483647 true).locals.upd 3 (.ptr 20 1) } := by
    simpa [s] using hbody
  have htrue : truthy (boolVal true) = .ok true := by rfl
  simpa [scanLoopIterationBody] using
    (ExS.ite (bc := true) (scanLoop_digit_guard byte 2147483647 true hbyte) htrue hbody')

/-- An overflowing digit takes the generated saturation branch: the value is
    capped at `INT_MAX`, the flag becomes true, and the cursor still advances. -/
def scanLoopOverflowObserved : Option (Option Val × Option Val × Option Val) :=
  scanLoopObserved 57 214748364 false

example : scanLoopOverflowObserved = some
    (some (.ptr 20 1), some (.int IntTy.i64 2147483647), some (.int IntTy.u8 1)) := by
  decide +kernel

/-- Once already saturated, a later digit leaves the capped accumulator and
    saturation flag unchanged while still advancing the cursor. -/
def scanLoopAlreadySaturatedObserved : Option (Option Val × Option Val × Option Val) :=
  scanLoopObserved 51 2147483647 true

example : scanLoopAlreadySaturatedObserved = some
    (some (.ptr 20 1), some (.int IntTy.i64 2147483647), some (.int IntTy.u8 1)) := by
  decide +kernel

end Obj.Tests.ObjMiniC27

namespace Obj.Tests.ObjMiniC28
open Obj.C Obj

/-- Run translated `tobj_skip_space` with the cursor cell in block 1000 and
    the input bytes in block 0. Report the stored cursor and unchanged input. -/
def runSkipSpace (bytes : List UInt8) (pos : Nat := 0) :
    Option (Nat × Block) :=
  let m : Mem := fun b =>
    if b = 0 then some bytes else
    if b = 1000 then some (encodeLE 8 (ptrPack (.ptr 0 pos))) else none
  match callFunc Gen.prog 100000 Gen.fid_tobj_skip_space
      [.ptr 1000 0, .ptr 0 bytes.length] m with
  | .ok (none, m') =>
    match m' 1000 with
    | some p =>
      match ptrUnpack (decodeLE p) with
      | .ptr 0 cursor => some (cursor, m' 0 |>.getD [])
      | _ => none
    | _ => none
  | _ => none

/-- Pure cursor contract of `tobj_skip_space`. -/
def specSkipSpace (bytes : List UInt8) (pos : Nat := 0) :
    Option (Nat × Block) :=
  some (pos + ((bytes.drop pos).takeWhile
    (fun b => scanSpace b.toNat)).length, bytes)

example : runSkipSpace [32, 9, 32, 97, 9] =
    specSkipSpace [32, 9, 32, 97, 9] := by decide +kernel
example : runSkipSpace [97, 32, 9, 98] 1 =
    specSkipSpace [97, 32, 9, 98] 1 := by decide +kernel
example : runSkipSpace [32, 9] = specSkipSpace [32, 9] := by decide +kernel
example : runSkipSpace [200, 32, 9] = specSkipSpace [200, 32, 9] := by decide +kernel

end Obj.Tests.ObjMiniC28

namespace Obj.Tests.ObjMiniC29
open Obj.C Obj Obj.Tests.ObjMiniC27

def skipSpacePackedBlock (bytes : Block) (pos : Nat) : Block :=
  encodeLE 8 (ptrPack (.ptr 20 (8 + pos))) ++ bytes

/-- Dropping through the packed pointer cell and `pos` input bytes exposes the
    corresponding raw input suffix. -/
theorem skipSpacePackedBlock_drop (bytes : Block) (pos : Nat) :
    (skipSpacePackedBlock bytes pos).drop (8 + pos) = bytes.drop pos := by
  simp [skipSpacePackedBlock, List.drop_append, encodeLE_length]

def skipSpacePackedMem (bytes : Block) (pos : Nat) : Mem :=
  fun b => if b = 20 then some (skipSpacePackedBlock bytes pos) else none

theorem ptr20_offset_pack_bound (pos : Nat) (hpos : 8 + pos < 4294967296) :
    ptrPack (.ptr 20 (8 + pos)) < 256 ^ 8 := by
  have hpow : 256 ^ 8 = 4294967296 * 4294967296 := by decide
  rw [hpow]
  simp only [ptrPack]
  omega

theorem skipSpacePacked_load (bytes : Block) (pos : Nat)
    (hpos : 8 + pos < 4294967296) :
    load (skipSpacePackedMem bytes pos) .ptr (.ptr 20 0) =
      .ok (.ptr 20 (8 + pos)) := by
  let packed := ptrPack (.ptr 20 (8 + pos))
  have hpack : packed < 256 ^ 8 := ptr20_offset_pack_bound pos hpos
  have hlen : (encodeLE 8 packed).length = 8 := encodeLE_length 8 packed
  have hread : readBytes (skipSpacePackedMem bytes pos) 20 0 8 =
      .ok (encodeLE 8 packed) := by
    simp [readBytes, skipSpacePackedMem, skipSpacePackedBlock, packed,
      hlen, List.take_append_of_le_length]
  have hdecode : decodeLE (encodeLE 8 packed) = packed := by
    rw [decodeLE_encodeLE]
    exact Nat.mod_eq_of_lt hpack
  simp [load, Ty.size, hread, Res.bind, hdecode]
  dsimp [packed]
  have hdiv : (20 * 4294967296 + (8 + pos)) / 4294967296 = 20 := by omega
  have hmod : (20 * 4294967296 + (8 + pos)) % 4294967296 = 8 + pos := by omega
  simp [ptrUnpack, ptrPack, Nat.add_sub_cancel_left, hdiv, hmod]

theorem skipSpacePacked_store (bytes : Block) (pos stop : Nat) :
    store (skipSpacePackedMem bytes pos) .ptr (.ptr 20 0) (.ptr 20 stop) =
      .ok (fun b => if b = 20 then
        some (encodeLE 8 (ptrPack (.ptr 20 stop)) ++ bytes) else none) := by
  apply congrArg Res.ok
  funext b
  by_cases hb : b = 20 <;>
    simp [store, writeBytes, skipSpacePackedMem, skipSpacePackedBlock,
      Mem.upd, List.take_append_of_le_length, List.drop_append_of_le_length,
      encodeLE_length, hb]

/-- Scanner memory with the caller's pointer cell and input in block 20, and
    the output integer in a separate writable block 21. -/
def scanIntSuccessPackedMem (bytes output : Block) (pos : Nat) : Mem :=
  fun b =>
    if b = 20 then some (skipSpacePackedBlock bytes pos)
    else if b = 21 then some output
    else none

/-- Scanner memory after the packed cursor cell and input buffer have already
    been laid out in block 20. Unlike `scanIntSuccessPackedMem`, the first
    argument here is the complete block read by the scanner loop. -/
def scanIntActualPackedMem (packed output : Block) : Mem :=
  fun b => if b = 20 then some packed else if b = 21 then some output else none

/-- Loading the packed input cursor works unchanged when the caller's output
    block is also present in memory. -/
theorem scanIntSuccessPacked_load (bytes output : Block) (pos : Nat)
    (hpos : 8 + pos < 4294967296) :
    load (scanIntSuccessPackedMem bytes output pos) .ptr (.ptr 20 0) =
      .ok (.ptr 20 (8 + pos)) := by
  let packed := ptrPack (.ptr 20 (8 + pos))
  have hpack : packed < 256 ^ 8 := ptr20_offset_pack_bound pos hpos
  have hlen : (encodeLE 8 packed).length = 8 := encodeLE_length 8 packed
  have hread : readBytes (scanIntSuccessPackedMem bytes output pos) 20 0 8 =
      .ok (encodeLE 8 packed) := by
    simp [readBytes, scanIntSuccessPackedMem, skipSpacePackedBlock, packed,
      hlen, List.take_append_of_le_length]
  have hdecode : decodeLE (encodeLE 8 packed) = packed := by
    rw [decodeLE_encodeLE]
    exact Nat.mod_eq_of_lt hpack
  simp [load, Ty.size, hread, Res.bind, hdecode]
  dsimp [packed]
  have hdiv : (20 * 4294967296 + (8 + pos)) / 4294967296 = 20 := by omega
  have hmod : (20 * 4294967296 + (8 + pos)) % 4294967296 = 8 + pos := by omega
  simp [ptrUnpack, ptrPack, Nat.add_sub_cancel_left, hdiv, hmod]

/-- The success value store updates the first four bytes of the output block
    while preserving the packed input and caller-pointer cell. -/
theorem scanInt_success_output_store (bytes output : Block) (pos value : Nat)
    (houtput : 4 ≤ output.length) :
    store (scanIntSuccessPackedMem bytes output pos) (.int IntTy.i32)
      (.ptr 21 0) (.int IntTy.i32 value) =
      .ok (fun b =>
        if b = 20 then some (skipSpacePackedBlock bytes pos)
        else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
        else none) := by
  change writeBytes (scanIntSuccessPackedMem bytes output pos) 21 0
      (encodeLE 4 value) = .ok _
  unfold writeBytes
  rw [show scanIntSuccessPackedMem bytes output pos 21 = some output by
    simp [scanIntSuccessPackedMem]]
  simp only [encodeLE_length]
  rw [if_pos (by omega)]
  apply congrArg Res.ok
  funext b
  by_cases h20 : b = 20
  · subst b
    simp [store, writeBytes, scanIntSuccessPackedMem, Mem.upd,
      encodeLE_length, houtput]
  · by_cases h21 : b = 21
    · subst b
      simp [store, writeBytes, scanIntSuccessPackedMem, Mem.upd,
        encodeLE_length, houtput, h20]
    · simp [store, writeBytes, scanIntSuccessPackedMem, Mem.upd, h20, h21]

/-- Committing the new input cursor updates only the packed caller-pointer
    cell after the output value has been stored. -/
theorem scanInt_success_cursor_store (bytes output : Block) (pos value cursor : Nat)
    (houtput : 4 ≤ output.length) :
    store
      (fun b =>
        if b = 20 then some (skipSpacePackedBlock bytes pos)
        else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
        else none)
      .ptr (.ptr 20 0) (.ptr 20 cursor) =
      .ok (fun b =>
        if b = 20 then some (encodeLE 8 (ptrPack (.ptr 20 cursor)) ++ bytes)
        else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
        else none) := by
  change writeBytes
      (fun b =>
        if b = 20 then some (skipSpacePackedBlock bytes pos)
        else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
        else none)
      20 0 (encodeLE 8 (ptrPack (.ptr 20 cursor))) = .ok _
  unfold writeBytes
  rw [show (fun b =>
      if b = 20 then some (skipSpacePackedBlock bytes pos)
      else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
      else none) 20 = some (skipSpacePackedBlock bytes pos) by simp]
  simp only [encodeLE_length]
  rw [if_pos (by simp [skipSpacePackedBlock, encodeLE_length])]
  apply congrArg Res.ok
  funext b
  by_cases h20 : b = 20
  · subst b
    simp [store, writeBytes, skipSpacePackedBlock, Mem.upd,
      List.take_append_of_le_length, List.drop_append_of_le_length,
      encodeLE_length]
  · by_cases h21 : b = 21
    · subst b
      simp [store, writeBytes, Mem.upd, encodeLE_length, houtput, h20]
    · simp [store, writeBytes, Mem.upd, h20, h21]

/-- Store the parsed value when the complete packed input block is already
    represented directly in block 20. -/
theorem scanInt_actual_output_store (packed output : Block) (value : Nat)
    (houtput : 4 ≤ output.length) :
    store (scanIntActualPackedMem packed output) (.int IntTy.i32)
      (.ptr 21 0) (.int IntTy.i32 value) =
      .ok (fun b => if b = 20 then some packed
        else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
        else none) := by
  change writeBytes (scanIntActualPackedMem packed output) 21 0
      (encodeLE 4 value) = .ok _
  unfold writeBytes
  rw [show scanIntActualPackedMem packed output 21 = some output by
    simp [scanIntActualPackedMem]]
  simp only [encodeLE_length]
  rw [if_pos (by omega)]
  apply congrArg Res.ok
  funext b
  by_cases h20 : b = 20
  · subst b
    simp [scanIntActualPackedMem, Mem.upd, encodeLE_length, houtput]
  · by_cases h21 : b = 21
    · subst b
      simp [scanIntActualPackedMem, Mem.upd, encodeLE_length, houtput, h20]
    · simp [scanIntActualPackedMem, Mem.upd, h20, h21]

/-- Commit the scanner cursor in the first eight bytes of the actual packed
    input block, retaining every byte after the pointer cell. -/
theorem scanInt_actual_cursor_store (packed output : Block)
    (value cursor : Nat) (hpacked : 8 ≤ packed.length)
    (houtput : 4 ≤ output.length) :
    store
      (fun b => if b = 20 then some packed
        else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
        else none)
      .ptr (.ptr 20 0) (.ptr 20 cursor) =
      .ok (fun b => if b = 20 then
        some (encodeLE 8 (ptrPack (.ptr 20 cursor)) ++ packed.drop 8)
        else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
        else none) := by
  change writeBytes
      (fun b => if b = 20 then some packed
        else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
        else none)
      20 0 (encodeLE 8 (ptrPack (.ptr 20 cursor))) = .ok _
  unfold writeBytes
  rw [show (fun b => if b = 20 then some packed
      else if b = 21 then some (encodeLE 4 value ++ output.drop 4)
      else none) 20 = some packed by simp]
  simp only [encodeLE_length]
  rw [if_pos (by omega)]
  apply congrArg Res.ok
  funext b
  by_cases h20 : b = 20
  · subst b
    simp [Mem.upd, List.take_append_of_le_length,
      List.drop_append_of_le_length, encodeLE_length, hpacked]
  · by_cases h21 : b = 21
    · subst b
      simp [Mem.upd, encodeLE_length, houtput, h20]
    · simp [Mem.upd, h20, h21]

theorem skipSpacePacked_refines (bytes : Block) (pos : Nat)
    (hpos : pos ≤ bytes.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K final,
      (∀ n, K ≤ n →
        callFunc Gen.prog n Gen.fid_tobj_skip_space
          [.ptr 20 0, .ptr 20 (8 + bytes.length)] (skipSpacePackedMem bytes pos) =
          .ok (none, final.mem)) ∧
      ExS Gen.prog
        ⟨frameLocals [0, 1] [.ptr 20 0, .ptr 20 (8 + bytes.length)],
          skipSpacePackedMem bytes pos, false⟩
        Gen.tobj_skip_space.body .normal final ∧
      final.mem = (fun b => if b = 20 then
        some (encodeLE 8 (ptrPack (.ptr 20
          (8 + pos + ((bytes.drop pos).takeWhile
            (fun byte => scanSpace byte.toNat)).length))) ++ bytes) else none) := by

  let packed := skipSpacePackedBlock bytes pos
  let cursor := 8 + pos
  let endpoint := packed.length
  let stop := cursor + ((packed.drop cursor).takeWhile
    (fun byte => scanSpace byte.toNat)).length
  let mem := skipSpacePackedMem bytes pos
  let resultMem : Mem := fun b => if b = 20 then
    some (encodeLE 8 (ptrPack (.ptr 20 stop)) ++ bytes) else none
  let initial : State :=
    ⟨frameLocals [0, 1] [.ptr 20 0, .ptr 20 endpoint], mem, false⟩
  have hpackedLen : packed.length = 8 + bytes.length := by
    simp [packed, skipSpacePackedBlock, encodeLE_length]
  have hcursorBound : cursor < 4294967296 := by dsimp [cursor]; omega
  have hloadPtr : load mem .ptr (.ptr 20 0) = .ok (.ptr 20 cursor) := by
    dsimp [cursor]
    exact skipSpacePacked_load bytes pos (by omega)
  have hvar0 : EvE Gen.prog initial (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?_cons,
      List.findIdx?_nil]
  have hload : EvE Gen.prog initial (.load .ptr (.var 0)) (.ptr 20 cursor) :=
    EvE.load hvar0 hloadPtr
  let afterSet : State :=
    { initial with locals := Locals.upd initial.locals 2 (.ptr 20 cursor) }
  have hset : ExS Gen.prog initial (.set 2 (.load .ptr (.var 0)))
      .normal afterSet := by
    simpa [afterSet] using ExS.set hload
  have hstate : afterSet = scanSkipSpaceStateAt packed cursor endpoint := by
    rw [State.mk.injEq]
    constructor
    · rfl
    constructor
    · funext b
      by_cases hb : b = 20
      · subst b
        simp [initial, mem, packed, skipSpacePackedMem, skipSpacePackedBlock,
          scanSkipSpaceStateAt]
      · simp [initial, mem, packed, skipSpacePackedMem, hb, scanSkipSpaceStateAt]
    · rfl
  have hrun := scanSkipSpace_terminates_takeWhile packed cursor (by
    dsimp [cursor]
    omega)
  obtain ⟨final, hloop, hfinal⟩ := hrun
  have hloop' : ExS Gen.prog afterSet Gen.tobj_skip_space_loop0 .normal final := by
    rw [hstate]
    exact hloop
  have hstop : final = scanSkipSpaceStateAt packed stop endpoint := by
    dsimp [stop, endpoint, cursor] at *
    have hfinal' := hfinal
    simpa [packed] using hfinal'
  have hfinal0 : final.locals 0 = some (.ptr 20 0) := by
    rw [hstop]
    simp [scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hfinal2 : final.locals 2 = some (.ptr 20 stop) := by
    rw [hstop]
    simp [scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hfinalMem : final.mem = mem := by
    rw [hstop]
    funext b
    by_cases hb : b = 20
    · subst b; simp [scanSkipSpaceStateAt, mem, packed, skipSpacePackedMem,
        skipSpacePackedBlock]
    · simp [scanSkipSpaceStateAt, mem, skipSpacePackedMem, hb]
  have hstore : store final.mem .ptr (.ptr 20 0) (.ptr 20 stop) =
      .ok (fun b => if b = 20 then
        some (encodeLE 8 (ptrPack (.ptr 20 stop)) ++ bytes) else none) := by
    rw [hfinalMem]
    exact skipSpacePacked_store bytes pos stop
  have haddr : EvE Gen.prog final (.var 0) (.ptr 20 0) := EvE.var hfinal0
  have hvalue : EvE Gen.prog final (.var 2) (.ptr 20 stop) := EvE.var hfinal2
  have hro : final.ro = false := by rw [hstop]; rfl
  have hstoreExS := ExS.store haddr hvalue hro hstore
  have hbody : ExS Gen.prog initial Gen.tobj_skip_space.body .normal
      { final with mem := resultMem } := by
    exact ExS.seq hset (ExS.seq hloop' hstoreExS)
  have hcall := callFunc_of_ExS_normal (p := Gen.prog)
    (f := Gen.fid_tobj_skip_space) (fn := Gen.tobj_skip_space)
    (args := [.ptr 20 0, .ptr 20 endpoint]) (m := mem)
    (s' := { final with mem := resultMem })
    (by rfl) (by simp [Gen.tobj_skip_space])
    (by simpa [initial, Gen.tobj_skip_space, frameLocals] using hbody)
  have hdrop : packed.drop cursor = bytes.drop pos := by
    dsimp [packed, cursor, skipSpacePackedBlock]
    rw [List.drop_append]
    have hlen : (encodeLE 8 (ptrPack (.ptr 20 (8 + pos)))).length = 8 :=
      encodeLE_length 8 _
    simp [hlen]
  have hcursorEq : stop = 8 + pos + ((bytes.drop pos).takeWhile
      (fun byte => scanSpace byte.toNat)).length := by
    dsimp [stop, cursor]
    rw [hdrop]
  let output : State := { final with mem := resultMem }
  refine ⟨hcall.choose, output, ?_, ?_, ?_⟩
  · intro n hn
    have hresult := hcall.choose_spec n hn
    simpa [output, mem, skipSpacePackedMem, endpoint, hpackedLen] using hresult
  · simpa [initial, Gen.tobj_skip_space, frameLocals, mem,
      skipSpacePackedMem, endpoint, hpackedLen] using hbody
  · funext b
    simp [output, resultMem, hcursorEq]

/-- The whitespace helper updates the packed caller pointer while preserving
    the scanner's separate output block. -/
theorem skipSpacePacked_store_with_output (bytes output : Block)
    (pos stop : Nat) :
    store (scanIntSuccessPackedMem bytes output pos) .ptr
      (.ptr 20 0) (.ptr 20 stop) =
      .ok (fun b => if b = 20 then
        some (encodeLE 8 (ptrPack (.ptr 20 stop)) ++ bytes)
        else if b = 21 then some output else none) := by
  change writeBytes (scanIntSuccessPackedMem bytes output pos) 20 0
    (encodeLE 8 (ptrPack (.ptr 20 stop))) = .ok _
  unfold writeBytes
  rw [show scanIntSuccessPackedMem bytes output pos 20 =
      some (skipSpacePackedBlock bytes pos) by
    simp [scanIntSuccessPackedMem, skipSpacePackedBlock]]
  simp only [encodeLE_length]
  rw [if_pos (by simp [skipSpacePackedBlock, encodeLE_length])]
  apply congrArg Res.ok
  funext b
  by_cases h20 : b = 20
  · subst b
    simp [scanIntSuccessPackedMem, skipSpacePackedBlock, Mem.upd,
      List.take_append_of_le_length, List.drop_append_of_le_length,
      encodeLE_length]
  · by_cases h21 : b = 21
    · subst b
      simp [scanIntSuccessPackedMem, Mem.upd, encodeLE_length, h20]
    · simp [scanIntSuccessPackedMem, Mem.upd, h20, h21]

/-- Body refinement for the whitespace helper in the scanner's two-block
    layout. Its loop carries the output block in the state memory frame. -/
theorem skipSpacePacked_body_with_output (bytes output : Block) (pos : Nat)
    (hpos : pos ≤ bytes.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ final,
      ExS Gen.prog
        ⟨frameLocals [0, 1]
          [.ptr 20 0, .ptr 20 (8 + bytes.length)],
          scanIntSuccessPackedMem bytes output pos, false⟩
        Gen.tobj_skip_space.body .normal final ∧
      final.locals 2 = some (.ptr 20
        (8 + pos + ((bytes.drop pos).takeWhile
          (fun byte => scanSpace byte.toNat)).length)) ∧
      final.mem = (fun b => if b = 20 then
        some (encodeLE 8 (ptrPack (.ptr 20
          (8 + pos + ((bytes.drop pos).takeWhile
            (fun byte => scanSpace byte.toNat)).length))) ++ bytes)
        else if b = 21 then some output else none) := by
  let packed := skipSpacePackedBlock bytes pos
  let cursor := 8 + pos
  let endpoint := packed.length
  let stop := cursor + ((packed.drop cursor).takeWhile
    (fun byte => scanSpace byte.toNat)).length
  let frame : Mem := fun b => if b = 21 then some output else none
  let mem := scanIntSuccessPackedMem bytes output pos
  let initial : State :=
    ⟨frameLocals [0, 1] [.ptr 20 0, .ptr 20 endpoint], mem, false⟩
  have hpackedLen : packed.length = 8 + bytes.length := by
    simp [packed, skipSpacePackedBlock, encodeLE_length]
  have hloadPtr : load mem .ptr (.ptr 20 0) = .ok (.ptr 20 cursor) := by
    dsimp [mem, cursor]
    exact scanIntSuccessPacked_load bytes output pos (by omega)
  have hvar0 : EvE Gen.prog initial (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?_cons,
      List.findIdx?_nil]
  have hload : EvE Gen.prog initial (.load .ptr (.var 0)) (.ptr 20 cursor) :=
    EvE.load hvar0 hloadPtr
  let afterSet : State :=
    { initial with locals := Locals.upd initial.locals 2 (.ptr 20 cursor) }
  have hset : ExS Gen.prog initial (.set 2 (.load .ptr (.var 0)))
      .normal afterSet := by
    simpa [afterSet] using ExS.set hload
  have hstate : afterSet = scanSkipSpaceStateAt packed cursor endpoint frame := by
    rw [State.mk.injEq]
    constructor
    · rfl
    constructor
    · funext b
      by_cases hb : b = 20
      · subst b
        simp [initial, mem, packed, scanIntSuccessPackedMem,
          skipSpacePackedBlock, scanSkipSpaceStateAt, frame]
      · by_cases hb21 : b = 21
        · subst b
          simp [initial, mem, scanIntSuccessPackedMem,
            scanSkipSpaceStateAt, frame]
        · simp [initial, mem, packed, scanIntSuccessPackedMem,
            skipSpacePackedBlock, scanSkipSpaceStateAt, frame, hb, hb21]
    · rfl
  obtain ⟨loopFinal, hloop, hfinal⟩ :=
    scanSkipSpace_terminates_takeWhile packed cursor (by
      dsimp [cursor]
      omega) frame
  have hloop' : ExS Gen.prog afterSet Gen.tobj_skip_space_loop0 .normal
      loopFinal := by
    rw [hstate]
    exact hloop
  have hstop : loopFinal = scanSkipSpaceStateAt packed stop endpoint frame := by
    dsimp [stop, endpoint, cursor] at *
    simpa [packed] using hfinal
  have hfinal0 : loopFinal.locals 0 = some (.ptr 20 0) := by
    rw [hstop]
    simp [scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?,
      List.findIdx?.go]
  have hfinal2 : loopFinal.locals 2 = some (.ptr 20 stop) := by
    rw [hstop]
    simp [scanSkipSpaceStateAt, frameLocals, List.idxOf?, List.findIdx?,
      List.findIdx?.go]
  have hfinalMem : loopFinal.mem = mem := by
    rw [hstop]
    funext b
    by_cases hb : b = 20
    · subst b
      simp [scanSkipSpaceStateAt, mem, packed, scanIntSuccessPackedMem,
        skipSpacePackedBlock]
    · by_cases hb21 : b = 21
      · subst b
        simp [scanSkipSpaceStateAt, mem, scanIntSuccessPackedMem, frame]
      · simp [scanSkipSpaceStateAt, mem, scanIntSuccessPackedMem, frame,
          hb, hb21]
  have hstore : store loopFinal.mem .ptr (.ptr 20 0) (.ptr 20 stop) =
      .ok (fun b => if b = 20 then
        some (encodeLE 8 (ptrPack (.ptr 20 stop)) ++ bytes)
        else if b = 21 then some output else none) := by
    rw [hfinalMem]
    exact skipSpacePacked_store_with_output bytes output pos stop
  have haddr : EvE Gen.prog loopFinal (.var 0) (.ptr 20 0) :=
    EvE.var hfinal0
  have hvalue : EvE Gen.prog loopFinal (.var 2) (.ptr 20 stop) :=
    EvE.var hfinal2
  have hro : loopFinal.ro = false := by rw [hstop]; rfl
  have hstoreExS := ExS.store haddr hvalue hro hstore
  let resultMem : Mem := fun b => if b = 20 then
    some (encodeLE 8 (ptrPack (.ptr 20 stop)) ++ bytes)
    else if b = 21 then some output else none
  have hbody : ExS Gen.prog initial Gen.tobj_skip_space.body .normal
      { loopFinal with mem := resultMem } := by
    exact ExS.seq hset (ExS.seq hloop' hstoreExS)
  have hdrop : packed.drop cursor = bytes.drop pos := by
    dsimp [packed, cursor, skipSpacePackedBlock]
    rw [List.drop_append]
    have hlen : (encodeLE 8 (ptrPack (.ptr 20 (8 + pos)))).length = 8 :=
      encodeLE_length 8 _
    simp [hlen]
  have hcursorEq : stop = 8 + pos + ((bytes.drop pos).takeWhile
      (fun byte => scanSpace byte.toNat)).length := by
    dsimp [stop, cursor]
    rw [hdrop]
  refine ⟨{ loopFinal with mem := resultMem }, ?_, ?_, ?_⟩
  · simpa [initial, Gen.tobj_skip_space, frameLocals, mem,
      scanIntSuccessPackedMem, endpoint, hpackedLen] using hbody
  · rw [hstop]
    simp [scanSkipSpaceStateAt, hcursorEq, frameLocals,
      List.idxOf?, List.findIdx?, List.findIdx?.go]
  · funext b
    simp [resultMem, hcursorEq]

/-- Scanner setup after the whitespace helper: the caller pointer is reloaded
    into local 3 at the first non-space byte, with the output block preserved. -/
theorem scanInt_setup_after_whitespace_exs (s : State) (bytes output : Block)
    (pos : Nat)
    (hpp : s.locals 0 = some (.ptr 20 0))
    (hend : s.locals 1 = some (.ptr 20 (8 + bytes.length)))
    (hout : s.locals 2 = some (.ptr 21 0))
    (hmem : s.mem = scanIntSuccessPackedMem bytes output pos)
    (hro : s.ro = false)
    (hpos : pos ≤ bytes.length)
    (hbound : 8 + bytes.length < 4294967296) :
    let spaces := ((bytes.drop pos).takeWhile
      (fun byte => scanSpace byte.toNat)).length
    ∃ afterCall,
      ExS Gen.prog s (.call none 23 [.var 0, .var 1]) .normal afterCall ∧
      afterCall = ⟨s.locals,
        scanIntSuccessPackedMem bytes output (pos + spaces), s.ro⟩ ∧
      ExS Gen.prog afterCall (.set 3 (.load .ptr (.var 0))) .normal
        ⟨Locals.upd s.locals 3 (.ptr 20 (8 + pos + spaces)),
          scanIntSuccessPackedMem bytes output (pos + spaces), s.ro⟩ := by
  dsimp
  let spaces := ((bytes.drop pos).takeWhile
    (fun byte => scanSpace byte.toNat)).length
  have hpos' : pos + spaces ≤ bytes.length := by
    have hprefix : (bytes.drop pos).takeWhile
        (fun byte => scanSpace byte.toNat) <+: bytes.drop pos :=
      List.takeWhile_prefix _
    have hlen := hprefix.length_le
    have hdrop : (bytes.drop pos).length = bytes.length - pos := by simp
    omega
  obtain ⟨skipFinal, hskipBody, hskipCursor, hskipMem⟩ :=
    skipSpacePacked_body_with_output bytes output pos hpos hbound
  have hskipMem' : skipFinal.mem =
      scanIntSuccessPackedMem bytes output (pos + spaces) := by
    have hcursor : 8 + pos + spaces = 8 + (pos + spaces) := by omega
    rw [hskipMem]
    funext b
    by_cases hb : b = 20
    · subst b
      simp [scanIntSuccessPackedMem, skipSpacePackedBlock, spaces, hcursor]
    · by_cases hb21 : b = 21
      · subst b
        simp [scanIntSuccessPackedMem]
      · simp [scanIntSuccessPackedMem, hb, hb21]
  have hvar0 : EvE Gen.prog s (.var 0) (.ptr 20 0) := EvE.var hpp
  have hvar1 : EvE Gen.prog s (.var 1)
      (.ptr 20 (8 + bytes.length)) := EvE.var hend
  have hargs : EvArgs Gen.prog s [.var 0, .var 1]
      [.ptr 20 0, .ptr 20 (8 + bytes.length)] := by
    exact EvArgs.cons hvar0 (EvArgs.cons hvar1 EvArgs.nil)
  have hskipCall : ExS Gen.prog s (.call none 23 [.var 0, .var 1])
      .normal { s with mem := skipFinal.mem } := by
    have hbody : ExS Gen.prog
        ⟨frameLocals [0, 1]
          [.ptr 20 0, .ptr 20 (8 + bytes.length)], s.mem, s.ro⟩
        Gen.tobj_skip_space.body .normal skipFinal := by
      have hbody' := hskipBody
      rw [← hmem] at hbody'
      simpa [hro] using hbody'
    have hparams : Gen.tobj_skip_space.params.length = 2 := by
      simp [Gen.tobj_skip_space]
    exact ExS.call hargs (by rfl) hparams hbody (Or.inl rfl)
  have hloadPtr : load (scanIntSuccessPackedMem bytes output (pos + spaces))
      .ptr (.ptr 20 0) = .ok (.ptr 20 (8 + pos + spaces)) := by
    have hcursor : 8 + (pos + spaces) = 8 + pos + spaces := by omega
    rw [← hcursor]
    exact scanIntSuccessPacked_load bytes output (pos + spaces) (by omega)
  let afterCall : State := { s with mem := skipFinal.mem }
  have hmemAfterCall : afterCall.mem =
      scanIntSuccessPackedMem bytes output (pos + spaces) := by
    simp [afterCall, hskipMem']
  have hvar0' : EvE Gen.prog afterCall (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simpa [afterCall] using hpp
  have hload : EvE Gen.prog afterCall (.load .ptr (.var 0))
      (.ptr 20 (8 + pos + spaces)) := by
    apply EvE.load hvar0'
    rw [hmemAfterCall]
    exact hloadPtr
  have hset : ExS Gen.prog afterCall (.set 3 (.load .ptr (.var 0)))
      .normal ⟨Locals.upd afterCall.locals 3 (.ptr 20 (8 + pos + spaces)),
        afterCall.mem, afterCall.ro⟩ := by
    exact ExS.set hload
  have hset' : ExS Gen.prog { s with mem := skipFinal.mem }
      (.set 3 (.load .ptr (.var 0))) .normal
      ⟨Locals.upd s.locals 3 (.ptr 20 (8 + pos + spaces)),
        skipFinal.mem, s.ro⟩ := by
    simpa [afterCall] using hset
  have hcallState : afterCall =
      ⟨s.locals, scanIntSuccessPackedMem bytes output (pos + spaces), s.ro⟩ := by
    simp [afterCall, hskipMem', spaces]
  refine ⟨afterCall, hskipCall, hcallState, ?_⟩
  rw [hcallState]
  simpa [spaces, hskipMem'] using hset'

private theorem scanSpace_takeWhile_map (bytes : Block) :
    (bytes.map UInt8.toNat).takeWhile scanSpace =
      (bytes.takeWhile (fun b => scanSpace b.toNat)).map UInt8.toNat := by
  induction bytes with
  | nil => rfl
  | cons head tail ih =>
    by_cases hspace : scanSpace head.toNat = true
    · simp [hspace, ih]
    · simp [hspace]

def scanIntFailureShape (bytes : Block) : Prop :=
  bytes.takeWhile (fun b => scanSpace b.toNat) = bytes ∨
  (∃ spaces sign, spaces.takeWhile (fun b => scanSpace b.toNat) = spaces ∧
    (sign.toNat = 43 ∨ sign.toNat = 45) ∧ bytes = spaces ++ [sign]) ∨
  (∃ spaces sign byte tail,
    spaces.takeWhile (fun b => scanSpace b.toNat) = spaces ∧
    (sign.toNat = 43 ∨ sign.toNat = 45) ∧
    (byte.toNat < 48 ∨ 57 < byte.toNat) ∧
    bytes = spaces ++ ([sign, byte] ++ tail)) ∨
  (∃ spaces byte tail,
    spaces.takeWhile (fun b => scanSpace b.toNat) = spaces ∧
    bytes = spaces ++ byte :: tail ∧
    scanSpace byte.toNat = false ∧
    byte.toNat ≠ 43 ∧ byte.toNat ≠ 45 ∧
    (byte.toNat < 48 ∨ 57 < byte.toNat))

private theorem takeWhile_append_drop_eq {α : Type} (p : α → Bool)
    (xs : List α) : xs.takeWhile p ++ xs.drop (xs.takeWhile p).length = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    by_cases hp : p head = true
    · simp [List.takeWhile_cons, hp, ih]
    · simp [List.takeWhile_cons, hp]

private theorem takeWhile_idempotent {α : Type} (p : α → Bool)
    (xs : List α) : (xs.takeWhile p).takeWhile p = xs.takeWhile p := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    by_cases hp : p head = true
    · simp [List.takeWhile_cons, hp, ih]
    · simp [List.takeWhile_cons, hp]

private theorem takeWhile_boundary_exists {α : Type} (p : α → Bool)
    (xs : List α) (h : (xs.takeWhile p).length < xs.length) :
    ∃ b, (xs.drop (xs.takeWhile p).length).head? = some b ∧ p b = false := by
  induction xs with
  | nil => simp at h
  | cons head tail ih =>
    by_cases hp : p head = true
    · simp only [List.takeWhile_cons, hp, ite_true, List.length_cons] at h ⊢
      have htail : (tail.takeWhile p).length < tail.length := by omega
      obtain ⟨b, hb, hpb⟩ := ih htail
      exact ⟨b, by simpa using hb, hpb⟩
    · have hpfalse : p head = false := Bool.eq_false_iff.mpr hp
      simp only [List.takeWhile_cons, hpfalse] at h ⊢
      exact ⟨head, by simp, hpfalse⟩


theorem scanInt_whitespaceOnly_fails (bytes output : Block) (pos : Nat)
    (hpos : pos ≤ bytes.length)
    (hspaces : ((bytes.drop pos).takeWhile
      (fun byte => scanSpace byte.toNat)) = bytes.drop pos)
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K, (∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output pos) =
      .ok (some (.int IntTy.u8 0),
        scanIntSuccessPackedMem bytes output bytes.length)) ∧
      scanInt (bytes.map UInt8.toNat) pos =
        (false, 0, (bytes.map UInt8.toNat).length) := by
  let endpoint := 8 + bytes.length
  let mem := scanIntSuccessPackedMem bytes output pos
  let initial : State :=
    ⟨frameLocals [0, 1, 2] [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0], mem, false⟩
  obtain ⟨skipFinal, hskipBody, _hskipCursor, hskipMem⟩ :=
    skipSpacePacked_body_with_output bytes output pos hpos hbound
  have hspaceLen : pos + ((bytes.drop pos).takeWhile
      (fun byte => scanSpace byte.toNat)).length = bytes.length := by
    rw [hspaces]
    simp
    omega
  have haddress : 8 + pos + ((bytes.drop pos).takeWhile
      (fun byte => scanSpace byte.toNat)).length = 8 + bytes.length := by
    omega
  have hskipMem' : skipFinal.mem =
      scanIntSuccessPackedMem bytes output bytes.length := by
    rw [hskipMem]
    funext b
    by_cases hb20 : b = 20
    · subst b
      rw [haddress]
      simp [scanIntSuccessPackedMem, skipSpacePackedBlock, hspaces,
        Nat.add_assoc]
    · by_cases hb21 : b = 21
      · subst b
        simp [scanIntSuccessPackedMem]
      · simp [scanIntSuccessPackedMem, hb20, hb21]
  have hvar0 : EvE Gen.prog initial (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hvar1 : EvE Gen.prog initial (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hargs : EvArgs Gen.prog initial [.var 0, .var 1]
      [.ptr 20 0, .ptr 20 endpoint] := EvArgs.cons hvar0 (EvArgs.cons hvar1 EvArgs.nil)
  have hskipCall : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal { initial with mem := skipFinal.mem } := by
    have hcall := ExS.call (p := Gen.prog) (s := initial)
      (f := Gen.fid_tobj_skip_space) (args := [.var 0, .var 1])
      (vs := [.ptr 20 0, .ptr 20 endpoint]) (fn := Gen.tobj_skip_space)
      (o := .normal) (s' := skipFinal) hargs (by rfl) (by rfl) hskipBody
      (Or.inl rfl)
    simpa [initial, hskipMem'] using hcall
  let afterSkip : State :=
    { initial with mem := scanIntSuccessPackedMem bytes output bytes.length }
  have hskipCall' : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal afterSkip := by
    simpa [afterSkip, hskipMem'] using hskipCall
  have hloadPtr : load afterSkip.mem .ptr (.ptr 20 0) = .ok (.ptr 20 endpoint) := by
    dsimp [afterSkip, endpoint]
    exact skipSpacePacked_load bytes bytes.length (by omega)
  have hvar0' : EvE Gen.prog afterSkip (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simpa [afterSkip, initial, frameLocals, List.idxOf?, List.findIdx?,
      List.findIdx?.go] using (show initial.locals 0 = some (.ptr 20 0) by
        simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go])
  have hload : EvE Gen.prog afterSkip (.load .ptr (.var 0)) (.ptr 20 endpoint) :=
    EvE.load hvar0' hloadPtr
  let afterSet : State :=
    { afterSkip with locals := Locals.upd afterSkip.locals 3 (.ptr 20 endpoint) }
  have hset : ExS Gen.prog afterSkip (.set 3 (.load .ptr (.var 0)))
      .normal afterSet := by
    simpa [afterSet] using ExS.set hload
  have hp : EvE Gen.prog afterSet (.var 3) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [afterSet, afterSkip, initial, frameLocals, Locals.upd,
      List.idxOf?, List.findIdx?, List.findIdx?.go]
  have he : EvE Gen.prog afterSet (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [afterSet, afterSkip, initial, frameLocals, Locals.upd,
      List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hcmp : EvE Gen.prog afterSet
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal true) := by
    apply EvE.bin hp he
    simp [evalBin, isPtr, boolVal]
  have htrue : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  let falseValue : Expr := .cond (.const (.int IntTy.i32 0))
    (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))
  have hfalseValue : EvE Gen.prog afterSet falseValue (.int IntTy.u8 0) := by
    unfold falseValue
    exact EvE.cond (bc := false) (EvE.const (.int IntTy.i32 0)) (by simp [truthy])
      (EvE.const (.int IntTy.u8 0))
  have hreturn : ExS Gen.prog afterSet
      (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.ret (some falseValue)) .skip)
      (.ret (some (.int IntTy.u8 0))) afterSet := by
    apply ExS.ite hcmp htrue
    exact ExS.ret hfalseValue
  have hbody : ExS Gen.prog initial Gen.tobj_scan_int.body
      (.ret (some (.int IntTy.u8 0))) afterSet := by
    apply ExS.seq hskipCall'
    apply ExS.seq hset
    exact ExS.seq_ret hreturn
  obtain ⟨K, hcall⟩ := callFunc_of_ExS (p := Gen.prog)
    (f := Gen.fid_tobj_scan_int) (fn := Gen.tobj_scan_int)
    (args := [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0]) (m := mem)
    (v := some (.int IntTy.u8 0)) (s' := afterSet)
    (hf := by rfl) (hlen := by rfl)
    (by simpa [initial, Gen.tobj_scan_int] using hbody)
  refine ⟨K, (fun n hn => ?_), ?_⟩
  have hresult := hcall n hn
  · simpa [mem, afterSet, afterSkip, initial, endpoint, hskipMem'] using hresult
  · have hspacesNat : ((bytes.map UInt8.toNat).drop pos).takeWhile scanSpace =
        (bytes.map UInt8.toNat).drop pos := by
      rw [← List.map_drop]
      rw [scanSpace_takeWhile_map]
      exact congrArg (List.map UInt8.toNat) hspaces
    have hdropLen : pos + (bytes.drop pos).length = bytes.length := by
      simp
      omega
    have hposLen : pos + (bytes.length - pos) = bytes.length := by omega
    have hmapLen : (bytes.map UInt8.toNat).length = bytes.length := by simp
    have hmapDrop : (bytes.map UInt8.toNat).drop bytes.length = [] := by
      rw [← hmapLen]
      exact List.drop_length
    have hmodel : scanInt (bytes.map UInt8.toNat) pos =
        (false, 0, (bytes.map UInt8.toNat).length) := by
      simp [scanInt, hspacesNat, hdropLen, hposLen, scanIntDigits,
        hmapDrop, List.drop_length]
    simpa using hmodel

/-- The generated optional-sign guard and its separate plus/minus comparisons
    classify a loaded ASCII byte from any in-bounds scanner state. -/
def scanIntPlusExpr : Expr :=
  .bin .eq (some IntTy.i32)
    (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
    (.const (.int IntTy.i32 43))

def scanIntMinusExpr : Expr :=
  .bin .eq (some IntTy.i32)
    (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
    (.const (.int IntTy.i32 45))

def scanIntSignGuard : Expr := .lor scanIntPlusExpr scanIntMinusExpr

theorem scanInt_signGuard_at (s : State) (bytes : Block) (cursor : Nat)
    (byte : UInt8) (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte) (hascii : byte.toNat < 128) :
    EvE Gen.prog s scanIntSignGuard
      (boolVal (decide (byte.toNat = 43) || decide (byte.toNat = 45))) ∧
    EvE Gen.prog s scanIntPlusExpr
      (.int IntTy.i32 (if byte.toNat = 43 then 1 else 0)) ∧
    EvE Gen.prog s scanIntMinusExpr
      (.int IntTy.i32 (if byte.toNat = 45 then 1 else 0)) := by
  have hload := scanLoop_load_byte_from_mem s.mem bytes cursor byte
    hmem hcursor hbyteAt
  have hcharLoad : EvE Gen.prog s (.load (.int IntTy.i8) (.var 3))
      (.int IntTy.i8 byte.toNat) := EvE.load (EvE.var hcursorLocal) hload
  have hmod : (byte.toNat : Int) % (4294967296 : Int) = byte.toNat :=
    Int.emod_eq_of_lt (by omega) (by omega)
  have hcast : evalCast IntTy.i32 (.int IntTy.i8 byte.toNat) =
      .ok (.int IntTy.i32 byte.toNat) := by
    simp [evalCast, IntTy.i8, IntTy.i32, IntTy.wrap, IntTy.toInt,
      IntTy.modulus, show ¬ 128 ≤ byte.toNat from by omega, hmod]
  have hchar : EvE Gen.prog s
      (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
      (.int IntTy.i32 byte.toNat) := EvE.cast hcharLoad hcast
  have hplus : EvE Gen.prog s
      (.bin .eq (some IntTy.i32)
        (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
        (.const (.int IntTy.i32 43)))
      (.int IntTy.i32 (if byte.toNat = 43 then 1 else 0)) := by
    apply EvE.bin hchar (EvE.const _)
    simp [evalBin, evalBinInt, binInt, intOf, isPtr, boolVal,
      IntTy.i32, IntTy.toInt,
      show ¬ 2147483648 ≤ byte.toNat from by omega]
    by_cases heq : byte.toNat = 43 <;> simp [heq] <;> omega
  have hminus : EvE Gen.prog s
      (.bin .eq (some IntTy.i32)
        (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
        (.const (.int IntTy.i32 45)))
      (.int IntTy.i32 (if byte.toNat = 45 then 1 else 0)) := by
    apply EvE.bin hchar (EvE.const _)
    simp [evalBin, evalBinInt, binInt, intOf, isPtr, boolVal,
      IntTy.i32, IntTy.toInt,
      show ¬ 2147483648 ≤ byte.toNat from by omega]
    by_cases heq : byte.toNat = 45 <;> simp [heq] <;> omega
  have hguard : EvE Gen.prog s scanIntSignGuard
      (boolVal (decide (byte.toNat = 43) || decide (byte.toNat = 45))) := by
    by_cases hplusTrue : decide (byte.toNat = 43) = true
    · have htruth : truthy (.int IntTy.i32
          (if byte.toNat = 43 then 1 else 0)) = .ok true := by
        have hplusEq : byte.toNat = 43 := of_decide_eq_true hplusTrue
        simp [truthy, hplusEq]
      have hguard : EvE Gen.prog s scanIntSignGuard (boolVal true) := by
        change EvE Gen.prog s (.lor _ _) (boolVal true)
        exact EvE.lor_true hplus htruth
      simpa [scanIntSignGuard, scanIntPlusExpr, scanIntMinusExpr, hplusTrue] using hguard
    · have htruthPlus : truthy (.int IntTy.i32
          (if byte.toNat = 43 then 1 else 0)) = .ok false := by
        have hplusNe : byte.toNat ≠ 43 := by simpa using hplusTrue
        simp [truthy, hplusNe]
      have htruthMinus : truthy (.int IntTy.i32
          (if byte.toNat = 45 then 1 else 0)) =
          .ok (decide (byte.toNat = 45)) := by
        by_cases hminusEq : byte.toNat = 45 <;> simp [truthy, hminusEq]
      have hguard := EvE.lor_false hplus htruthPlus hminus htruthMinus
      simpa [scanIntSignGuard, scanIntPlusExpr, scanIntMinusExpr, hplusTrue] using hguard
  refine ⟨hguard, ?_, ?_⟩
  · simpa [scanIntPlusExpr] using hplus
  · simpa [scanIntMinusExpr] using hminus

/-- The optional-sign guard also classifies bytes 128–255 correctly after
    signed `i8` promotion: those values become negative and match neither sign. -/
theorem scanInt_signGuard_high_at (s : State) (bytes : Block) (cursor : Nat)
    (byte : UInt8) (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte) (hhigh : 128 ≤ byte.toNat) :
    EvE Gen.prog s scanIntSignGuard (boolVal false) ∧
    EvE Gen.prog s scanIntPlusExpr (.int IntTy.i32 0) ∧
    EvE Gen.prog s scanIntMinusExpr (.int IntTy.i32 0) := by
  have hload := scanLoop_load_byte_from_mem s.mem bytes cursor byte
    hmem hcursor hbyteAt
  have hcharLoad : EvE Gen.prog s (.load (.int IntTy.i8) (.var 3))
      (.int IntTy.i8 byte.toNat) := EvE.load (EvE.var hcursorLocal) hload
  let c : Int := IntTy.toInt IntTy.i8 byte.toNat
  have hbyteBound : byte.toNat < 256 := by
    have h := UInt8.toNat_lt byte
    omega
  have hcRange : -128 ≤ c ∧ c ≤ 127 := by
    simp [c, IntTy.toInt, IntTy.i8, IntTy.modulus]
    omega
  have hcNeg : c < 0 := by
    simp [c, IntTy.toInt, IntTy.i8, IntTy.modulus]
    omega
  have hcast : evalCast IntTy.i32 (.int IntTy.i8 byte.toNat) =
      .ok (.int IntTy.i32 (IntTy.wrap IntTy.i32 c)) := by
    simp [evalCast, c, IntTy.i8, IntTy.i32]
  have hchar : EvE Gen.prog s
      (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 c)) := EvE.cast hcharLoad hcast
  have hconv : IntTy.toInt IntTy.i32 (IntTy.wrap IntTy.i32 c) = c :=
    Obj.C.Proofs.toInt_i32_wrap_i8 c hcRange
  have hcNe43 : c ≠ 43 := by omega
  have hcNe45 : c ≠ 45 := by omega
  have hnot43 : byte.toNat ≠ 43 := by omega
  have hnot45 : byte.toNat ≠ 45 := by omega
  have hplus : EvE Gen.prog s
      (.bin .eq (some IntTy.i32)
        (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
        (.const (.int IntTy.i32 43))) (.int IntTy.i32 0) := by
    apply EvE.bin hchar (EvE.const _)
    simp [evalBin, evalBinInt, binInt, intOf, isPtr, boolVal, IntTy.i32]
    change decide (IntTy.i32.toInt (IntTy.i32.wrap c) =
      IntTy.i32.toInt 43) = false
    rw [hconv]
    simp [IntTy.toInt, IntTy.i32, hcNe43]
  have hminus : EvE Gen.prog s
      (.bin .eq (some IntTy.i32)
        (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
        (.const (.int IntTy.i32 45))) (.int IntTy.i32 0) := by
    apply EvE.bin hchar (EvE.const _)
    simp [evalBin, evalBinInt, binInt, intOf, isPtr, boolVal, IntTy.i32]
    change decide (IntTy.i32.toInt (IntTy.i32.wrap c) =
      IntTy.i32.toInt 45) = false
    rw [hconv]
    simp [IntTy.toInt, IntTy.i32, hcNe45]
  have hfalse : truthy (.int IntTy.i32 0) = .ok false := by
    simp [truthy, boolVal, IntTy.i32]
  have hguard : EvE Gen.prog s scanIntSignGuard (boolVal false) := by
    change EvE Gen.prog s (.lor _ _) (boolVal false)
    exact EvE.lor_false hplus hfalse hminus hfalse
  refine ⟨hguard, ?_, ?_⟩
  · simpa [scanIntPlusExpr, hnot43] using hplus
  · simpa [scanIntMinusExpr, hnot45] using hminus

/-- Sign-guard evaluation for every `UInt8`, combining ordinary ASCII
    promotion with the negative signed-byte case. -/
theorem scanInt_signGuard_any_at (s : State) (bytes : Block) (cursor : Nat)
    (byte : UInt8) (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte) :
    EvE Gen.prog s scanIntSignGuard
      (boolVal (decide (byte.toNat = 43) || decide (byte.toNat = 45))) ∧
    EvE Gen.prog s scanIntPlusExpr
      (.int IntTy.i32 (if byte.toNat = 43 then 1 else 0)) ∧
    EvE Gen.prog s scanIntMinusExpr
      (.int IntTy.i32 (if byte.toNat = 45 then 1 else 0)) := by
  by_cases hascii : byte.toNat < 128
  · exact scanInt_signGuard_at s bytes cursor byte hcursorLocal hmem
      hcursor hbyteAt hascii
  · have hhigh : 128 ≤ byte.toNat := by omega
    obtain ⟨hguard, hplus, hminus⟩ :=
      scanInt_signGuard_high_at s bytes cursor byte hcursorLocal hmem
        hcursor hbyteAt hhigh
    have hnot43 : byte.toNat ≠ 43 := by omega
    have hnot45 : byte.toNat ≠ 45 := by omega
    simpa [hnot43, hnot45] using And.intro hguard (And.intro hplus hminus)

/-- The scanner's optional-sign branch records `-1` only for a minus sign,
    preserves the incoming `+1` sign otherwise, and advances one byte. -/
def scanIntSignBranch : Stmt :=
  .ite scanIntSignGuard
    (.seq
      (.ite scanIntMinusExpr
        (.set 4 (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))) .skip)
      (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
    .skip

/-- Select the optional-sign branch at its generated position in the scanner
    body, to check that `scanIntSignBranch` is the actual translated AST. -/
def scanIntSignBranchFromGen : Stmt :=
  match Gen.tobj_scan_int.body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq branch _)))) => branch
  | _ => .skip

theorem scanInt_signBranch_ast : scanIntSignBranchFromGen = scanIntSignBranch := by
  rfl

theorem scanInt_signBranch_at (s : State) (bytes : Block) (cursor : Nat)
    (byte : UInt8) (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hsignLocal : s.locals 4 = some (.int IntTy.i32 1))
    (hmem : s.mem 20 = some bytes) (hbound : cursor + 1 ≤ bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hsign : byte.toNat = 43 ∨ byte.toNat = 45) :
    ∃ finalState, ExS Gen.prog s scanIntSignBranch .normal finalState ∧
      finalState.locals 3 = some (.ptr 20 (cursor + 1)) ∧
      finalState.locals 4 = some (.int IntTy.i32
        (if byte.toNat = 45 then IntTy.wrap IntTy.i32 (-1) else 1)) ∧
      finalState.locals 0 = s.locals 0 ∧
      finalState.locals 2 = s.locals 2 ∧
      finalState.locals 1 = s.locals 1 ∧
      finalState.mem = s.mem ∧
      finalState.locals = Locals.upd
        (Locals.upd s.locals 4 (.int IntTy.i32
          (if byte.toNat = 45 then IntTy.wrap IntTy.i32 (-1) else 1)))
        3 (.ptr 20 (cursor + 1)) ∧
      finalState.ro = s.ro := by
  have hascii : byte.toNat < 128 := by rcases hsign with hp | hm <;> omega
  obtain ⟨_hguard, hplus, hminus⟩ := scanInt_signGuard_at s bytes cursor byte
    hcursorLocal hmem (by omega) hbyteAt hascii
  have hguardTrue : EvE Gen.prog s scanIntSignGuard (boolVal true) := by
    rcases hsign with hp | hm
    · have hplusTruth : truthy (.int IntTy.i32
          (if byte.toNat = 43 then 1 else 0)) = .ok true := by
        simp [truthy, hp]
      have hguard := EvE.lor_true (a := scanIntPlusExpr)
        (b := scanIntMinusExpr) hplus hplusTruth
      simpa [scanIntSignGuard, scanIntPlusExpr, scanIntMinusExpr] using hguard
    · have hplusNe : byte.toNat ≠ 43 := by omega
      have hplusTruth : truthy (.int IntTy.i32
          (if byte.toNat = 43 then 1 else 0)) = .ok false := by
        simp [truthy, hplusNe]
      have hminusTruth : truthy (.int IntTy.i32
          (if byte.toNat = 45 then 1 else 0)) = .ok true := by
        simp [truthy, hm]
      have hguard := EvE.lor_false (a := scanIntPlusExpr)
        (b := scanIntMinusExpr) hplus hplusTruth hminus hminusTruth
      simpa [scanIntSignGuard, scanIntPlusExpr, scanIntMinusExpr] using hguard
  have hminusTruth : truthy (.int IntTy.i32
      (if byte.toNat = 45 then 1 else 0)) =
      .ok (decide (byte.toNat = 45)) := by
    by_cases hm : byte.toNat = 45 <;> simp [truthy, hm]
  have hneg : EvE Gen.prog s
      (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 (-1))) := by
    exact EvE.un (EvE.const (.int IntTy.i32 1)) (by rfl)
  let afterMinus : State := if decide (byte.toNat = 45) then
      { s with locals := Locals.upd s.locals 4 (.int IntTy.i32 (IntTy.wrap IntTy.i32 (-1))) }
    else s
  have hminusChoice : ExS Gen.prog s
      (if decide (byte.toNat = 45) then
        (.set 4 (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))) else .skip)
      .normal afterMinus := by
    by_cases hm : byte.toNat = 45
    · have hset : ExS Gen.prog s
          (.set 4 (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))) .normal
          { s with locals := Locals.upd s.locals 4 (.int IntTy.i32 (IntTy.wrap IntTy.i32 (-1))) } :=
        ExS.set hneg
      have hmDec : decide (byte.toNat = 45) = true := by simp [hm]
      simpa [afterMinus, hmDec] using hset
    · have hmDec : decide (byte.toNat = 45) = false := by simp [hm]
      simpa [afterMinus, hmDec] using (ExS.skip : ExS Gen.prog s .skip .normal s)
  have hminusStep : ExS Gen.prog s
      (.ite scanIntMinusExpr
        (.set 4 (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))) .skip)
      .normal afterMinus := by
    apply ExS.ite hminus
    · exact hminusTruth
    · simpa [scanIntMinusExpr] using hminusChoice
  have hcursorAfterMinus : afterMinus.locals 3 = some (.ptr 20 cursor) := by
    by_cases hm : byte.toNat = 45 <;>
      simp [afterMinus, hm, Locals.upd, hcursorLocal]
  have hmemAfterMinus : afterMinus.mem 20 = some bytes := by
    by_cases hm : byte.toNat = 45 <;> simp [afterMinus, hm, hmem]
  have hadvance := scanLoop_cursor_advance_exs afterMinus cursor bytes
    hcursorAfterMinus hmemAfterMinus hbound
  let finalState := { afterMinus with
    locals := Locals.upd afterMinus.locals 3 (.ptr 20 (cursor + 1)) }
  have hbody : ExS Gen.prog s
      (.seq
        (.ite scanIntMinusExpr
          (.set 4 (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))) .skip)
        (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
      .normal finalState := by
    exact ExS.seq hminusStep (by simpa [finalState] using hadvance)
  have hbranch : ExS Gen.prog s scanIntSignBranch .normal finalState := by
    exact ExS.ite (bc := true) hguardTrue (by simp [truthy, boolVal])
      (by simpa [scanIntSignBranch] using hbody)
  have hplusId : Locals.upd s.locals 4 (.int IntTy.i32 1) = s.locals := by
    funext i
    by_cases hi : i = 4
    · subst i
      simp [Locals.upd, hsignLocal]
    · simp [Locals.upd, hi]
  refine ⟨finalState, hbranch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [finalState, Locals.upd]
  · by_cases hm : byte.toNat = 45 <;>
      simp [finalState, afterMinus, Locals.upd, hsignLocal, hplusId, hm]
  · by_cases hm : byte.toNat = 45 <;>
      simp [finalState, afterMinus, Locals.upd, hsignLocal, hplusId, hm]
  · by_cases hm : byte.toNat = 45 <;>
      simp [finalState, afterMinus, Locals.upd, hsignLocal, hm]
  · by_cases hm : byte.toNat = 45 <;>
      simp [finalState, afterMinus, Locals.upd, hm]
  · by_cases hm : byte.toNat = 45 <;> simp [finalState, afterMinus, hm]
  · by_cases hm : byte.toNat = 45
    · simp [finalState, afterMinus, Locals.upd, hm]
    · have hdec : decide (byte.toNat = 45) = false := by simp [hm]
      simp only [finalState, afterMinus, hdec, Bool.false_eq_true, if_false,
        if_neg hm]
      rw [hplusId]
  · by_cases hm : byte.toNat = 45 <;> simp [finalState, afterMinus, hm]

/-- A byte that is neither optional sign takes the generated sign branch's
    no-op arm, preserving the cursor, sign, caller parameters, and memory. -/
theorem scanInt_signBranch_no_sign_at (s : State) (bytes : Block)
    (cursor : Nat) (byte : UInt8)
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hsignLocal : s.locals 4 = some (.int IntTy.i32 1))
    (hmem : s.mem 20 = some bytes) (hcursor : cursor < bytes.length)
    (hbyteAt : bytes[cursor]? = some byte) (hascii : byte.toNat < 128)
    (hnotPlus : byte.toNat ≠ 43) (hnotMinus : byte.toNat ≠ 45) :
    ExS Gen.prog s scanIntSignBranch .normal s := by
  obtain ⟨hguard, _hplus, _hminus⟩ := scanInt_signGuard_at s bytes cursor byte
    hcursorLocal hmem hcursor hbyteAt hascii
  have hguardFalse : EvE Gen.prog s scanIntSignGuard (boolVal false) := by
    simpa [scanIntSignGuard, scanIntPlusExpr, scanIntMinusExpr,
      hnotPlus, hnotMinus] using hguard
  have hfalse : truthy (boolVal false) = .ok false := by
    simp [truthy, boolVal, IntTy.i32]
  have hbranch : ExS Gen.prog s scanIntSignBranch .normal s := by
    unfold scanIntSignBranch
    apply ExS.ite hguardFalse hfalse
    exact ExS.skip
  exact hbranch

def scanIntFalseValue : Expr :=
  .cond (.const (.int IntTy.i32 0))
    (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))

def scanIntFailGuard : Expr :=
  .lor
    (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
    (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))

def scanIntEndFailureCheck : Stmt :=
  .ite scanIntFailGuard (.ret (some scanIntFalseValue)) .skip

def scanIntStartFailureCheck : Stmt :=
  .ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
    (.ret (some scanIntFalseValue)) .skip

def scanIntSuccessValue : Expr :=
  .cond (.bin .lt (some IntTy.i32) (.var 4) (.const (.int IntTy.i32 0)))
    (.un .neg IntTy.i64 (.var 5)) (.var 5)

def scanIntSuccess : Expr :=
  .cond (.const (.int IntTy.i32 1))
    (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))

/-- Scanner suffix after the early failure check. Failure returns before this
    suffix, but keeping its exact generated shape lets prefix proofs compose
    directly into the translated function body. -/
def scanIntSuccessRest : Stmt :=
  .seq (.set 5 (.cast IntTy.i64 (.const (.int IntTy.i32 0))))
    (.seq (.set 6 (.cond (.const (.int IntTy.i32 0))
      (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))
      (.seq Gen.tobj_scan_int_loop0
        (.seq (.store (.int IntTy.i32) (.var 2)
          (.cast IntTy.i32 scanIntSuccessValue))
          (.seq (.store .ptr (.var 0) (.var 3))
            (.ret (some scanIntSuccess))))))

/-- The scanner's success-value expression stores the sign-applied magnitude
    as the corresponding wrapped i32 representation. -/
theorem scanInt_successValue_eval_state (s : State) (value : Nat)
    (negative : Bool)
    (hsignLocal : s.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)))
    (hvalueLocal : s.locals 5 = some (.int IntTy.i64 value))
    (hnegativeEval : EvE Gen.prog s
      (.bin .lt (some IntTy.i32) (.var 4) (.const (.int IntTy.i32 0)))
      (boolVal negative))
    (hvalue : value ≤ 2147483647) :
    EvE Gen.prog s (.cast IntTy.i32 scanIntSuccessValue)
      (.int IntTy.i32 (IntTy.wrap IntTy.i32
        (if negative then -(value : Int) else value))) := by
  let signed : Int := if negative then -(value : Int) else value
  have hvalueInt : IntTy.toInt IntTy.i64 value = value := by
    simp [IntTy.toInt, IntTy.i64, IntTy.modulus]
    omega
  have hwrapPos : IntTy.wrap IntTy.i64 (value : Int) = value := by
    simp only [IntTy.wrap, IntTy.modulus, IntTy.i64]
    have hmod : (value : Int) % 18446744073709551616 = value :=
      Int.emod_eq_of_lt (by omega) (by omega)
    change ((value : Int) % 18446744073709551616).toNat = value
    rw [hmod]
    simp
  have hnegRange : IntTy.inRange IntTy.i64 (-(value : Int)) = true := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i64,
      IntTy.modulus]
    omega
  have hnegEval : evalUn .neg IntTy.i64 (.int IntTy.i64 value) =
      .ok (.int IntTy.i64 (IntTy.wrap IntTy.i64 (-(value : Int)))) := by
    simp [evalUn, intOf, hvalueInt, arith, hnegRange]
  have hnegValue : EvE Gen.prog s (.un .neg IntTy.i64 (.var 5))
      (.int IntTy.i64 (IntTy.wrap IntTy.i64 (-(value : Int)))) :=
    EvE.un (EvE.var hvalueLocal) hnegEval
  have hpositiveValue : EvE Gen.prog s (.var 5) (.int IntTy.i64 value) :=
    EvE.var hvalueLocal
  have hselected : EvE Gen.prog s scanIntSuccessValue
      (.int IntTy.i64 (IntTy.wrap IntTy.i64 signed)) := by
    unfold scanIntSuccessValue
    apply EvE.cond (bc := negative) hnegativeEval
    · cases negative <;> simp [truthy, boolVal]
    · cases negative with
      | false => simpa [signed, hwrapPos] using hpositiveValue
      | true => simpa [signed] using hnegValue
  have hsignedRange : -2147483647 ≤ signed ∧ signed ≤ 2147483647 := by
    dsimp [signed]
    cases negative <;> simp <;> omega
  have htoInt : IntTy.toInt IntTy.i64 (IntTy.wrap IntTy.i64 signed) = signed :=
    Obj.C.Proofs.toInt_i64_wrap signed (by omega)
  have hcast : evalCast IntTy.i32 (.int IntTy.i64 (IntTy.wrap IntTy.i64 signed)) =
      .ok (.int IntTy.i32 (IntTy.wrap IntTy.i32 signed)) := by
    simp only [evalCast]
    rw [if_pos (by decide : IntTy.i64.signed = true)]
    change Res.ok (Val.int IntTy.i32
      (IntTy.i32.wrap (IntTy.toInt IntTy.i64 (IntTy.wrap IntTy.i64 signed)))) =
      Res.ok (Val.int IntTy.i32 (IntTy.i32.wrap signed))
    rw [htoInt]
  exact EvE.cast hselected hcast

/-- The scanner's sign local is negative exactly when its generated i32
    comparison against zero evaluates true. -/
theorem scanInt_sign_negative_eval_state (s : State) (negative : Bool)
    (hsignLocal : s.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1))) :
    EvE Gen.prog s
      (.bin .lt (some IntTy.i32) (.var 4) (.const (.int IntTy.i32 0)))
      (boolVal negative) := by
  apply EvE.bin (EvE.var hsignLocal) (EvE.const (.int IntTy.i32 0))
  cases negative <;>
    simp [evalBin, evalBinInt, binInt, intOf, boolVal,
      isPtr, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus]

/-- The generated success tail writes the parsed value, commits the scanner
    cursor through `pp`, and returns true, provided both pointer stores are
    defined. This isolates the remaining packed-memory obligations from the
    scanner-loop refinement. -/
theorem scanInt_successStores_exs (s : State) (outPtr ppPtr cursor : Val)
    (result : Val) (valueMem finalMem : Mem)
    (hout : EvE Gen.prog s (.var 2) outPtr)
    (hppLocal : s.locals 0 = some ppPtr)
    (hcursorLocal : s.locals 3 = some cursor)
    (hvalue : EvE Gen.prog s (.cast IntTy.i32 scanIntSuccessValue) result)
    (hro : s.ro = false)
    (hvalueStore : store s.mem (.int IntTy.i32) outPtr result = .ok valueMem)
    (hcursorStore : store valueMem .ptr ppPtr cursor = .ok finalMem) :
    ExS Gen.prog s
      (.seq (.store (.int IntTy.i32) (.var 2)
          (.cast IntTy.i32 scanIntSuccessValue))
        (.seq (.store .ptr (.var 0) (.var 3))
          (.ret (some scanIntSuccess))))
      (.ret (some (.int IntTy.u8 1))) { s with mem := finalMem } := by
  let afterValue : State := { s with mem := valueMem }
  let afterCursor : State := { s with mem := finalMem }
  have hroAfterValue : afterValue.ro = false := by simp [afterValue, hro]
  have hppAfterValue : EvE Gen.prog afterValue (.var 0) ppPtr := by
    apply EvE.var
    simpa [afterValue] using hppLocal
  have hcursorAfterValue : EvE Gen.prog afterValue (.var 3) cursor := by
    apply EvE.var
    simpa [afterValue] using hcursorLocal
  have hvalueStep := ExS.store hout hvalue hro hvalueStore
  have hcursorStep := ExS.store hppAfterValue hcursorAfterValue
    hroAfterValue hcursorStore
  have hsuccess : EvE Gen.prog afterCursor scanIntSuccess
      (.int IntTy.u8 1) := by
    unfold scanIntSuccess
    apply EvE.cond (bc := true) (EvE.const (.int IntTy.i32 1))
    · simp [truthy, boolVal]
    · exact EvE.const (.int IntTy.u8 1)
  have hreturn := ExS.ret hsuccess
  have htail := ExS.seq hcursorStep hreturn
  have hbody := ExS.seq hvalueStep htail
  simpa [afterValue, afterCursor] using hbody

/-- Compose the scanner's two success-path scratch-local initializations, its
    generated digit loop, and the output/cursor stores into the exact suffix of
    the translated scanner body. -/
theorem scanInt_successRest_exs (s loopFinal : State) (valueMem finalMem : Mem)
    (outPtr ppPtr cursor : Val) (result : Val)
    (hloop : ExS Gen.prog
      { s with locals := Locals.upd (Locals.upd s.locals 5
        (.int IntTy.i64 0)) 6 (.int IntTy.u8 0) }
      Gen.tobj_scan_int_loop0 .normal loopFinal)
    (hout : EvE Gen.prog loopFinal (.var 2) outPtr)
    (hppLocal : loopFinal.locals 0 = some ppPtr)
    (hcursorLocal : loopFinal.locals 3 = some cursor)
    (hvalue : EvE Gen.prog loopFinal (.cast IntTy.i32 scanIntSuccessValue) result)
    (hro : loopFinal.ro = false)
    (hvalueStore : store loopFinal.mem (.int IntTy.i32) outPtr result = .ok valueMem)
    (hcursorStore : store valueMem .ptr ppPtr cursor = .ok finalMem) :
    ExS Gen.prog s scanIntSuccessRest
      (.ret (some (.int IntTy.u8 1))) { loopFinal with mem := finalMem } := by
  let afterValueInit : State := { s with locals :=
    (Locals.upd s.locals 5 (.int IntTy.i64 0)) }
  have hsetValue : ExS Gen.prog s
      (.set 5 (.cast IntTy.i64 (.const (.int IntTy.i32 0))))
      .normal afterValueInit := by
    apply ExS.set
    apply EvE.cast (EvE.const (.int IntTy.i32 0))
    simp [evalCast, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus]
  let loopStart : State := { afterValueInit with locals :=
    (Locals.upd afterValueInit.locals 6 (.int IntTy.u8 0)) }
  have hsetSat : ExS Gen.prog afterValueInit
      (.set 6 (.cond (.const (.int IntTy.i32 0))
        (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))
      .normal loopStart := by
    apply ExS.set
    apply EvE.cond (bc := false) (EvE.const (.int IntTy.i32 0))
    · simp [truthy, boolVal]
    · exact EvE.const (.int IntTy.u8 0)
  have hloopStart : loopStart =
      ⟨Locals.upd (Locals.upd s.locals 5 (.int IntTy.i64 0))
        6 (.int IntTy.u8 0), s.mem, s.ro⟩ := by
    simp [loopStart, afterValueInit]
  have hloop' : ExS Gen.prog loopStart Gen.tobj_scan_int_loop0
      .normal loopFinal := by simpa [hloopStart] using hloop
  have hstores := scanInt_successStores_exs loopFinal outPtr ppPtr cursor
    result valueMem finalMem hout hppLocal hcursorLocal hvalue hro
    hvalueStore hcursorStore
  have htail := ExS.seq hloop' hstores
  have hinit := ExS.seq hsetValue (ExS.seq hsetSat htail)
  simpa [scanIntSuccessRest, afterValueInit, loopStart] using hinit

/-- Success suffix for an actual packed input block. The loop reads the full
    block 20, and committing the final cursor preserves bytes after the
    pointer cell. -/
theorem scanInt_successRest_actual_packed_exs (s loopFinal : State)
    (packed output : Block) (cursorOffset value : Nat) (negative : Bool)
    (hloop : ExS Gen.prog
      { s with locals := Locals.upd (Locals.upd s.locals 5
        (.int IntTy.i64 0)) 6 (.int IntTy.u8 0) }
      Gen.tobj_scan_int_loop0 .normal loopFinal)
    (hmem : loopFinal.mem = scanIntActualPackedMem packed output)
    (hpacked : 8 ≤ packed.length) (houtput : 4 ≤ output.length)
    (houtLocal : loopFinal.locals 2 = some (.ptr 21 0))
    (hppLocal : loopFinal.locals 0 = some (.ptr 20 0))
    (hcursorLocal : loopFinal.locals 3 = some (.ptr 20 cursorOffset))
    (hsignLocal : loopFinal.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)))
    (hvalueLocal : loopFinal.locals 5 = some (.int IntTy.i64 value))
    (hvalue : value ≤ 2147483647) (hro : loopFinal.ro = false) :
    ExS Gen.prog s scanIntSuccessRest
      (.ret (some (.int IntTy.u8 1)))
      ⟨loopFinal.locals,
        (fun b => if b = 20 then
          some (encodeLE 8 (ptrPack (.ptr 20 cursorOffset)) ++ packed.drop 8)
          else if b = 21 then some
            (encodeLE 4 (IntTy.wrap IntTy.i32
              (if negative then -(value : Int) else value)) ++ output.drop 4)
          else none), loopFinal.ro⟩ := by
  let signed : Int := if negative then -(value : Int) else value
  let result : Val := .int IntTy.i32 (IntTy.wrap IntTy.i32 signed)
  let valueMem : Mem := fun b => if b = 20 then some packed
    else if b = 21 then some (encodeLE 4 (IntTy.wrap IntTy.i32 signed) ++
      output.drop 4) else none
  let finalMem : Mem := fun b => if b = 20 then
    some (encodeLE 8 (ptrPack (.ptr 20 cursorOffset)) ++ packed.drop 8)
    else if b = 21 then some (encodeLE 4 (IntTy.wrap IntTy.i32 signed) ++
      output.drop 4) else none
  have hout : EvE Gen.prog loopFinal (.var 2) (.ptr 21 0) := EvE.var houtLocal
  have hnegativeEval := scanInt_sign_negative_eval_state loopFinal negative
    hsignLocal
  have hvalueEval := scanInt_successValue_eval_state loopFinal value negative
    hsignLocal hvalueLocal hnegativeEval hvalue
  have hvalueEval' : EvE Gen.prog loopFinal
      (.cast IntTy.i32 scanIntSuccessValue) result := by
    simpa [signed, result] using hvalueEval
  have hvalueStore : store loopFinal.mem (.int IntTy.i32) (.ptr 21 0) result =
      .ok valueMem := by
    rw [hmem]
    simpa [valueMem, signed, result, scanIntActualPackedMem] using
      scanInt_actual_output_store packed output
        (IntTy.wrap IntTy.i32 signed) houtput
  have hcursorStore : store valueMem .ptr (.ptr 20 0)
      (.ptr 20 cursorOffset) = .ok finalMem := by
    simpa [valueMem, finalMem, signed] using
      scanInt_actual_cursor_store packed output
        (IntTy.wrap IntTy.i32 signed) cursorOffset hpacked houtput
  exact scanInt_successRest_exs s loopFinal valueMem finalMem
    (.ptr 21 0) (.ptr 20 0) (.ptr 20 cursorOffset) result hloop hout
    hppLocal hcursorLocal hvalueEval' hro hvalueStore hcursorStore

/-- Discharge the success suffix's stores for the concrete packed scanner
    layout: block 20 contains `pp` and the input, and block 21 contains the
    writable i32 output slot. -/
theorem scanInt_successRest_packed_exs (s loopFinal : State)
    (bytes output : Block) (pos cursorOffset value : Nat) (negative : Bool)
    (hloop : ExS Gen.prog
      { s with locals := Locals.upd (Locals.upd s.locals 5
        (.int IntTy.i64 0)) 6 (.int IntTy.u8 0) }
      Gen.tobj_scan_int_loop0 .normal loopFinal)
    (hmem : loopFinal.mem = scanIntSuccessPackedMem bytes output pos)
    (houtput : 4 ≤ output.length)
    (houtLocal : loopFinal.locals 2 = some (.ptr 21 0))
    (hppLocal : loopFinal.locals 0 = some (.ptr 20 0))
    (hcursorLocal : loopFinal.locals 3 = some (.ptr 20 cursorOffset))
    (hsignLocal : loopFinal.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)))
    (hvalueLocal : loopFinal.locals 5 = some (.int IntTy.i64 value))
    (hvalue : value ≤ 2147483647)
    (hro : loopFinal.ro = false) :
    ExS Gen.prog s scanIntSuccessRest
      (.ret (some (.int IntTy.u8 1)))
      ⟨loopFinal.locals,
        (fun b =>
          if b = 20 then some
            (encodeLE 8 (ptrPack (.ptr 20 cursorOffset)) ++ bytes)
          else if b = 21 then some
            (encodeLE 4 (IntTy.wrap IntTy.i32
              (if negative then -(value : Int) else value)) ++ output.drop 4)
          else none),
        loopFinal.ro⟩ := by
  let signed : Int := if negative then -(value : Int) else value
  let result : Val := .int IntTy.i32 (IntTy.wrap IntTy.i32 signed)
  let valueMem : Mem := fun b =>
    if b = 20 then some (skipSpacePackedBlock bytes pos)
    else if b = 21 then some
      (encodeLE 4 (IntTy.wrap IntTy.i32 signed) ++ output.drop 4)
    else none
  let finalMem : Mem := fun b =>
    if b = 20 then some (encodeLE 8 (ptrPack (.ptr 20 cursorOffset)) ++ bytes)
    else if b = 21 then some
      (encodeLE 4 (IntTy.wrap IntTy.i32 signed) ++ output.drop 4)
    else none
  have hout : EvE Gen.prog loopFinal (.var 2) (.ptr 21 0) :=
    EvE.var houtLocal
  have hnegativeEval := scanInt_sign_negative_eval_state loopFinal negative
    hsignLocal
  have hvalueEval := scanInt_successValue_eval_state loopFinal value negative
    hsignLocal hvalueLocal hnegativeEval hvalue
  have hvalueEval' : EvE Gen.prog loopFinal
      (.cast IntTy.i32 scanIntSuccessValue) result := by
    simpa [signed, result] using hvalueEval
  have hvalueStore : store loopFinal.mem (.int IntTy.i32) (.ptr 21 0) result =
      .ok valueMem := by
    rw [hmem]
    simpa [valueMem, signed, result, scanIntSuccessPackedMem] using
      scanInt_success_output_store bytes output pos
        (IntTy.wrap IntTy.i32 signed) houtput
  have hcursorStore : store valueMem .ptr (.ptr 20 0)
      (.ptr 20 cursorOffset) = .ok finalMem := by
    simpa [valueMem, finalMem, signed] using
      scanInt_success_cursor_store bytes output pos
        (IntTy.wrap IntTy.i32 signed) cursorOffset houtput
  have hrest := scanInt_successRest_exs s loopFinal valueMem finalMem
    (.ptr 21 0) (.ptr 20 0) (.ptr 20 cursorOffset) result hloop hout
    hppLocal hcursorLocal hvalueEval' hro hvalueStore hcursorStore
  simpa [scanIntSuccessRest, finalMem] using hrest

/-- A framed digit loop started at zero supplies its own accumulator bound,
    final sign/value locals, and cursor for the packed success suffix. -/
theorem scanInt_success_after_framed_loop_packed_exs (base : State)
    (input output : Block) (pos start : Nat) (negative : Bool)
    (hendLocal : base.locals 1 = some (.ptr 20 input.length))
    (hmemInput : base.mem 20 = some input)
    (hpackedMem : base.mem = scanIntSuccessPackedMem input output pos)
    (hstart : start ≤ input.length) (houtput : 4 ≤ output.length)
    (houtLocal : base.locals 2 = some (.ptr 21 0))
    (hppLocal : base.locals 0 = some (.ptr 20 0))
    (hsignLocal : base.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)))
    (hro : base.ro = false) :
    ∃ loopFinal value finalSat,
    ExS Gen.prog
      ⟨Locals.upd base.locals 3 (.ptr 20 start), base.mem, base.ro⟩
      scanIntSuccessRest
      (.ret (some (.int IntTy.u8 1)))
      ⟨loopFinal.locals,
        (fun b =>
          if b = 20 then some
            (encodeLE 8 (ptrPack (.ptr 20
              (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1))) ++ input)
          else if b = 21 then some
            (encodeLE 4 (IntTy.wrap IntTy.i32
              (if negative then
                -((scanDigits ((input.drop start).map UInt8.toNat) 0).2 : Int)
               else (scanDigits ((input.drop start).map UInt8.toNat) 0).2)) ++ output.drop 4)
          else none),
        loopFinal.ro⟩ ∧
    loopFinal = scanLoopFrameAt base
      (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1)
      value finalSat ∧
    (value, finalSat) = scanCLoopFold
      ((input.drop start).map UInt8.toNat) (0, false) := by
  let successStart : State :=
    ⟨Locals.upd base.locals 3 (.ptr 20 start), base.mem, base.ro⟩
  obtain ⟨loopFinal, value, finalSat, hloop, hfinal, hfold⟩ :=
    scanLoop_terminates_takeWhile_in_frame base input start 0 false
      hendLocal hmemInput hstart (by omega) (by simp)
  have hloopStart : scanLoopFrameAt base start 0 false =
      ⟨Locals.upd (Locals.upd successStart.locals 5 (.int IntTy.i64 0))
        6 (.int IntTy.u8 0), successStart.mem, successStart.ro⟩ := by
    simp [successStart, scanLoopFrameAt, Locals.upd]
  have hloop' : ExS Gen.prog
      ⟨Locals.upd (Locals.upd successStart.locals 5 (.int IntTy.i64 0))
        6 (.int IntTy.u8 0), successStart.mem, successStart.ro⟩
      Gen.tobj_scan_int_loop0 .normal loopFinal := by
    rw [← hloopStart]
    exact hloop
  have hvalueBound : value ≤ 2147483647 := by
    have hbound := scanCLoopFold_zero_le_cap
      ((input.drop start).map UInt8.toNat)
    have hfst := congrArg Prod.fst hfold
    have hv : value =
        (scanCLoopFold ((input.drop start).map UInt8.toNat) (0, false)).1 := by
      simpa using hfst
    rw [hv]
    exact hbound
  have hvalueFold : value = scanIntFold
      ((input.drop start).map UInt8.toNat) 0 := by
    calc
      value = (scanCLoopFold ((input.drop start).map UInt8.toNat)
          (0, false)).1 := by
        simpa using congrArg Prod.fst hfold
      _ = scanIntFold ((input.drop start).map UInt8.toNat) 0 :=
        scanCLoopFold_value ((input.drop start).map UInt8.toNat) 0 false (by simp)
  have hvalueSpec : value =
      (scanDigits ((input.drop start).map UInt8.toNat) 0).2 := by
    rw [scanDigits_value_exact]
    exact hvalueFold
  have hfinalShape := hfinal
  have hmemFinal : loopFinal.mem = scanIntSuccessPackedMem input output pos := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, scanIntSuccessPackedMem, hpackedMem]
  have houtFinal : loopFinal.locals 2 = some (.ptr 21 0) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd, houtLocal]
  have hppFinal : loopFinal.locals 0 = some (.ptr 20 0) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd, hppLocal]
  have hsignFinal : loopFinal.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd, hsignLocal]
  have hcursorFinal : loopFinal.locals 3 = some (.ptr 20
      (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1)) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd]
  have hvalueFinal : loopFinal.locals 5 = some (.int IntTy.i64 value) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd]
  have hroFinal : loopFinal.ro = false := by
    rw [hfinalShape]
    exact hro
  have hpackedRest := scanInt_successRest_packed_exs successStart loopFinal
    input output pos (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1)
    value negative hloop' hmemFinal houtput houtFinal hppFinal hcursorFinal
    hsignFinal hvalueFinal hvalueBound hroFinal
  refine ⟨loopFinal, value, finalSat, ?_, hfinal, hfold⟩
  simpa [successStart, hvalueSpec] using hpackedRest

/-- Correctly framed success refinement for a complete block 20. This version
    keeps the packed input block distinct from its raw payload and applies the
    success stores to the actual two-block memory layout. -/
theorem scanInt_success_after_framed_loop_actual_packed_exs (base : State)
    (packed output : Block) (start : Nat) (negative : Bool)
    (hendLocal : base.locals 1 = some (.ptr 20 packed.length))
    (hmemPacked : base.mem = scanIntActualPackedMem packed output)
    (hstart : start ≤ packed.length) (hpacked : 8 ≤ packed.length)
    (houtput : 4 ≤ output.length)
    (houtLocal : base.locals 2 = some (.ptr 21 0))
    (hppLocal : base.locals 0 = some (.ptr 20 0))
    (hsignLocal : base.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)))
    (hro : base.ro = false) :
    ∃ loopFinal value finalSat,
      ExS Gen.prog
        ⟨Locals.upd base.locals 3 (.ptr 20 start), base.mem, base.ro⟩
        scanIntSuccessRest
        (.ret (some (.int IntTy.u8 1)))
        ⟨loopFinal.locals,
          (fun b => if b = 20 then some
            (encodeLE 8 (ptrPack (.ptr 20
              (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1))) ++
              packed.drop 8)
          else if b = 21 then some
            (encodeLE 4 (IntTy.wrap IntTy.i32
              (if negative then
                -((scanDigits ((packed.drop start).map UInt8.toNat) 0).2 : Int)
               else (scanDigits ((packed.drop start).map UInt8.toNat) 0).2)) ++
              output.drop 4)
          else none), loopFinal.ro⟩ ∧
      loopFinal = scanLoopFrameAt base
        (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((packed.drop start).map UInt8.toNat) (0, false) := by
  let successStart : State :=
    ⟨Locals.upd base.locals 3 (.ptr 20 start), base.mem, base.ro⟩
  have hmemInput : base.mem 20 = some packed := by
    simpa [scanIntActualPackedMem] using congrArg (fun mem => mem 20) hmemPacked
  obtain ⟨loopFinal, value, finalSat, hloop, hfinal, hfold⟩ :=
    scanLoop_terminates_takeWhile_in_frame base packed start 0 false
      hendLocal hmemInput hstart (by omega) (by simp)
  have hloopStart : scanLoopFrameAt base start 0 false =
      ⟨Locals.upd (Locals.upd successStart.locals 5 (.int IntTy.i64 0))
        6 (.int IntTy.u8 0), successStart.mem, successStart.ro⟩ := by
    simp [successStart, scanLoopFrameAt, Locals.upd]
  have hloop' : ExS Gen.prog
      ⟨Locals.upd (Locals.upd successStart.locals 5 (.int IntTy.i64 0))
        6 (.int IntTy.u8 0), successStart.mem, successStart.ro⟩
      Gen.tobj_scan_int_loop0 .normal loopFinal := by
    rw [← hloopStart]
    exact hloop
  have hvalueBound : value ≤ 2147483647 := by
    have hbound := scanCLoopFold_zero_le_cap
      ((packed.drop start).map UInt8.toNat)
    have hv := congrArg Prod.fst hfold
    have heq : value =
        (scanCLoopFold ((packed.drop start).map UInt8.toNat)
          (0, false)).1 := by simpa using hv
    rw [heq]
    exact hbound
  have hvalueFold : value = scanIntFold
      ((packed.drop start).map UInt8.toNat) 0 := by
    calc
      value = (scanCLoopFold ((packed.drop start).map UInt8.toNat)
          (0, false)).1 := by simpa using congrArg Prod.fst hfold
      _ = scanIntFold ((packed.drop start).map UInt8.toNat) 0 :=
        scanCLoopFold_value ((packed.drop start).map UInt8.toNat) 0 false
          (by simp)
  have hvalueSpec : value =
      (scanDigits ((packed.drop start).map UInt8.toNat) 0).2 := by
    rw [scanDigits_value_exact]
    exact hvalueFold
  have hfinalShape := hfinal
  have hmemFinal : loopFinal.mem = scanIntActualPackedMem packed output := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, hmemPacked]
  have houtFinal : loopFinal.locals 2 = some (.ptr 21 0) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd, houtLocal]
  have hppFinal : loopFinal.locals 0 = some (.ptr 20 0) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd, hppLocal]
  have hsignFinal : loopFinal.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd, hsignLocal]
  have hcursorFinal : loopFinal.locals 3 = some (.ptr 20
      (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1)) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd]
  have hvalueFinal : loopFinal.locals 5 = some (.int IntTy.i64 value) := by
    rw [hfinalShape]
    simp [scanLoopFrameAt, Locals.upd]
  have hroFinal : loopFinal.ro = false := by
    rw [hfinalShape]
    exact hro
  have hrest := scanInt_successRest_actual_packed_exs successStart loopFinal
    packed output (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1)
    value negative hloop' hmemFinal hpacked houtput houtFinal hppFinal
    hcursorFinal hsignFinal hvalueFinal hvalueBound hroFinal
  refine ⟨loopFinal, value, finalSat, ?_, hfinal, hfold⟩
  simpa [successStart, hvalueSpec] using hrest

/-- Once sign handling has left the cursor on an ASCII digit, the scanner's
    short-circuit failure check falls through and the framed loop proves the
    rest of the packed success path. -/
theorem scanInt_success_after_digit_check_actual_packed_exs (base : State)
    (packed output : Block) (start : Nat) (byte : UInt8) (negative : Bool)
    (hendLocal : base.locals 1 = some (.ptr 20 packed.length))
    (hpackedMem : base.mem = scanIntActualPackedMem packed output)
    (hstart : start < packed.length) (hbyteAt : packed[start]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hpacked : 8 ≤ packed.length) (houtput : 4 ≤ output.length)
    (houtLocal : base.locals 2 = some (.ptr 21 0))
    (hppLocal : base.locals 0 = some (.ptr 20 0))
    (hcursorLocal : base.locals 3 = some (.ptr 20 start))
    (hsignLocal : base.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)))
    (hro : base.ro = false) :
    ∃ loopFinal value finalSat,
      ExS Gen.prog base (.seq scanIntEndFailureCheck scanIntSuccessRest)
        (.ret (some (.int IntTy.u8 1)))
        ⟨loopFinal.locals,
          (fun b => if b = 20 then some
            (encodeLE 8 (ptrPack (.ptr 20
              (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1))) ++
              packed.drop 8)
          else if b = 21 then some
            (encodeLE 4 (IntTy.wrap IntTy.i32
              (if negative then
                -((scanDigits ((packed.drop start).map UInt8.toNat) 0).2 : Int)
               else (scanDigits ((packed.drop start).map UInt8.toNat) 0).2)) ++
              output.drop 4)
          else none), loopFinal.ro⟩ ∧
      loopFinal = scanLoopFrameAt base
        (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((packed.drop start).map UInt8.toNat) (0, false) := by
  have hmemInput : base.mem 20 = some packed := by
    simpa [scanIntActualPackedMem] using congrArg (fun mem => mem 20) hpackedMem
  have hge : EvE Gen.prog base
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin (EvE.var hcursorLocal) (EvE.var hendLocal)
    simp [evalBin, isPtr, boolVal]
    exact hstart
  obtain ⟨hdigitCall, _hdigitCast⟩ := scanLoop_digit_call_true_at
    base packed start byte hcursorLocal hmemInput hstart hbyteAt hdigit
  have hnotDigit : EvE Gen.prog base
      (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (boolVal false) := by
    apply EvE.un hdigitCall
    simp [evalUn, truthy, boolVal]
  have hfalse : truthy (boolVal false) = .ok false := by
    simp [truthy, boolVal, IntTy.i32]
  have hfailGuard : EvE Gen.prog base scanIntFailGuard (boolVal false) := by
    unfold scanIntFailGuard
    exact EvE.lor_false hge hfalse hnotDigit hfalse
  have hfailureCheck : ExS Gen.prog base scanIntEndFailureCheck .normal base := by
    apply ExS.ite hfailGuard hfalse
    exact ExS.skip
  obtain ⟨loopFinal, value, finalSat, hsuccess, hfinal, hfold⟩ :=
    scanInt_success_after_framed_loop_actual_packed_exs base packed output start
      negative hendLocal hpackedMem (by omega) hpacked houtput houtLocal
      hppLocal hsignLocal hro
  have hsuccess' : ExS Gen.prog base scanIntSuccessRest
      (.ret (some (.int IntTy.u8 1)))
      ⟨loopFinal.locals,
        (fun b => if b = 20 then some
          (encodeLE 8 (ptrPack (.ptr 20
            (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1))) ++
            packed.drop 8)
        else if b = 21 then some
          (encodeLE 4 (IntTy.wrap IntTy.i32
            (if negative then
              -((scanDigits ((packed.drop start).map UInt8.toNat) 0).2 : Int)
             else (scanDigits ((packed.drop start).map UInt8.toNat) 0).2)) ++
            output.drop 4)
        else none), loopFinal.ro⟩ := by
    have hlocals : Locals.upd base.locals 3 (.ptr 20 start) = base.locals := by
      funext i
      by_cases hi : i = 3
      · subst i
        simp [Locals.upd, hcursorLocal]
      · simp [Locals.upd, hi]
    have hstate :
        (⟨Locals.upd base.locals 3 (.ptr 20 start), base.mem, base.ro⟩ : State) = base := by
      cases base
      simp [hlocals]
    rw [hstate] at hsuccess
    exact hsuccess
  refine ⟨loopFinal, value, finalSat, ?_, hfinal, hfold⟩
  exact ExS.seq hfailureCheck hsuccess'

/-- No optional sign precedes the first digit. The generated sign branch is a
    no-op, then the actual packed-block digit check and success stores run. -/
theorem scanInt_success_no_sign_actual_packed_exs (base : State)
    (packed output : Block) (start : Nat) (byte : UInt8)
    (hendLocal : base.locals 1 = some (.ptr 20 packed.length))
    (hpackedMem : base.mem = scanIntActualPackedMem packed output)
    (hstart : start < packed.length) (hbyteAt : packed[start]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hnotPlus : byte.toNat ≠ 43) (hnotMinus : byte.toNat ≠ 45)
    (hpacked : 8 ≤ packed.length) (houtput : 4 ≤ output.length)
    (houtLocal : base.locals 2 = some (.ptr 21 0))
    (hppLocal : base.locals 0 = some (.ptr 20 0))
    (hcursorLocal : base.locals 3 = some (.ptr 20 start))
    (hsignLocal : base.locals 4 = some (.int IntTy.i32 1))
    (hro : base.ro = false) :
    ∃ loopFinal value finalSat,
      ExS Gen.prog base
        (.seq scanIntSignBranch
          (.seq scanIntEndFailureCheck scanIntSuccessRest))
        (.ret (some (.int IntTy.u8 1)))
        ⟨loopFinal.locals,
          (fun b => if b = 20 then some
            (encodeLE 8 (ptrPack (.ptr 20
              (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1))) ++
              packed.drop 8)
          else if b = 21 then some
            (encodeLE 4 (IntTy.wrap IntTy.i32
              (scanDigits ((packed.drop start).map UInt8.toNat) 0).2) ++
              output.drop 4)
          else none), loopFinal.ro⟩ ∧
      loopFinal = scanLoopFrameAt base
        (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((packed.drop start).map UInt8.toNat) (0, false) := by
  have hmemInput : base.mem 20 = some packed := by
    simpa [scanIntActualPackedMem] using congrArg (fun mem => mem 20) hpackedMem
  have hnoSign := scanInt_signBranch_no_sign_at base packed start byte
    hcursorLocal hsignLocal hmemInput hstart hbyteAt (by omega)
    hnotPlus hnotMinus
  obtain ⟨loopFinal, value, finalSat, hsuccess, hfinal, hfold⟩ :=
    scanInt_success_after_digit_check_actual_packed_exs base packed output
      start byte false hendLocal hpackedMem hstart hbyteAt hdigit hpacked
      houtput houtLocal hppLocal hcursorLocal hsignLocal hro
  refine ⟨loopFinal, value, finalSat, ?_, hfinal, hfold⟩
  exact ExS.seq hnoSign hsuccess

theorem scanInt_success_after_digit_check_packed_exs (base : State)
    (input output : Block) (pos start : Nat) (byte : UInt8) (negative : Bool)
    (hendLocal : base.locals 1 = some (.ptr 20 input.length))
    (hmemInput : base.mem 20 = some input)
    (hpackedMem : base.mem = scanIntSuccessPackedMem input output pos)
    (hstart : start < input.length) (hbyteAt : input[start]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (houtput : 4 ≤ output.length)
    (houtLocal : base.locals 2 = some (.ptr 21 0))
    (hppLocal : base.locals 0 = some (.ptr 20 0))
    (hcursorLocal : base.locals 3 = some (.ptr 20 start))
    (hsignLocal : base.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)))
    (hro : base.ro = false) :
    ∃ loopFinal value finalSat,
      ExS Gen.prog base (.seq scanIntEndFailureCheck scanIntSuccessRest)
        (.ret (some (.int IntTy.u8 1)))
        ⟨loopFinal.locals,
          (fun b =>
            if b = 20 then some
              (encodeLE 8 (ptrPack (.ptr 20
                (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1))) ++ input)
            else if b = 21 then some
              (encodeLE 4 (IntTy.wrap IntTy.i32
                (if negative then
                  -((scanDigits ((input.drop start).map UInt8.toNat) 0).2 : Int)
                 else (scanDigits ((input.drop start).map UInt8.toNat) 0).2)) ++ output.drop 4)
            else none),
          loopFinal.ro⟩ ∧
      loopFinal = scanLoopFrameAt base
        (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((input.drop start).map UInt8.toNat) (0, false) := by
  have hge : EvE Gen.prog base
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin (EvE.var hcursorLocal) (EvE.var hendLocal)
    simp [evalBin, isPtr, boolVal]
    exact hstart
  obtain ⟨hdigitCall, _hdigitCast⟩ := scanLoop_digit_call_true_at
    base input start byte hcursorLocal hmemInput hstart hbyteAt hdigit
  have hnotDigit : EvE Gen.prog base
      (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (boolVal false) := by
    apply EvE.un hdigitCall
    simp [evalUn, truthy, boolVal]
  have hfalse : truthy (boolVal false) = .ok false := by
    simp [truthy, boolVal, IntTy.i32]
  have hfailGuard : EvE Gen.prog base scanIntFailGuard (boolVal false) := by
    unfold scanIntFailGuard
    exact EvE.lor_false hge hfalse hnotDigit hfalse
  have hfailureCheck : ExS Gen.prog base scanIntEndFailureCheck
      .normal base := by
    apply ExS.ite hfailGuard hfalse
    exact ExS.skip
  obtain ⟨loopFinal, value, finalSat, hsuccess, hfinal, hfold⟩ :=
    scanInt_success_after_framed_loop_packed_exs base input output pos start
      negative hendLocal hmemInput hpackedMem (by omega) houtput houtLocal
      hppLocal hsignLocal hro
  have hsuccess' : ExS Gen.prog base scanIntSuccessRest
      (.ret (some (.int IntTy.u8 1)))
      ⟨loopFinal.locals,
        (fun b =>
          if b = 20 then some
            (encodeLE 8 (ptrPack (.ptr 20
              (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1))) ++ input)
          else if b = 21 then some
            (encodeLE 4 (IntTy.wrap IntTy.i32
              (if negative then
                -((scanDigits ((input.drop start).map UInt8.toNat) 0).2 : Int)
               else (scanDigits ((input.drop start).map UInt8.toNat) 0).2)) ++ output.drop 4)
          else none), loopFinal.ro⟩ := by
    have hlocals : Locals.upd base.locals 3 (.ptr 20 start) = base.locals := by
      funext i
      by_cases hi : i = 3
      · subst i
        simp [Locals.upd, hcursorLocal]
      · simp [Locals.upd, hi]
    have hstate :
        (⟨Locals.upd base.locals 3 (.ptr 20 start), base.mem, base.ro⟩ : State) = base := by
      cases base
      simp [hlocals]
    rw [hstate] at hsuccess
    exact hsuccess
  refine ⟨loopFinal, value, finalSat, ?_, hfinal, hfold⟩
  exact ExS.seq hfailureCheck hsuccess'

/-- A first digit without an optional sign composes the generated no-op sign
    branch, the successful digit check, the framed loop, and both packed
    stores. -/
theorem scanInt_success_no_sign_packed_exs (base : State)
    (input output : Block) (pos start : Nat) (byte : UInt8)
    (hendLocal : base.locals 1 = some (.ptr 20 input.length))
    (hmemInput : base.mem 20 = some input)
    (hpackedMem : base.mem = scanIntSuccessPackedMem input output pos)
    (hstart : start < input.length) (hbyteAt : input[start]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hnotPlus : byte.toNat ≠ 43) (hnotMinus : byte.toNat ≠ 45)
    (houtput : 4 ≤ output.length)
    (houtLocal : base.locals 2 = some (.ptr 21 0))
    (hppLocal : base.locals 0 = some (.ptr 20 0))
    (hcursorLocal : base.locals 3 = some (.ptr 20 start))
    (hsignLocal : base.locals 4 = some (.int IntTy.i32 1))
    (hro : base.ro = false) :
    ∃ loopFinal value finalSat,
      ExS Gen.prog base
        (.seq scanIntSignBranch
          (.seq scanIntEndFailureCheck scanIntSuccessRest))
        (.ret (some (.int IntTy.u8 1)))
        ⟨loopFinal.locals,
          (fun b =>
            if b = 20 then some
              (encodeLE 8 (ptrPack (.ptr 20
                (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1))) ++ input)
            else if b = 21 then some
              (encodeLE 4 (IntTy.wrap IntTy.i32
                (scanDigits ((input.drop start).map UInt8.toNat) 0).2) ++ output.drop 4)
            else none),
          loopFinal.ro⟩ ∧
      loopFinal = scanLoopFrameAt base
        (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((input.drop start).map UInt8.toNat) (0, false) := by
  have hnoSign := scanInt_signBranch_no_sign_at base input start byte
    hcursorLocal hsignLocal hmemInput hstart hbyteAt
    (by omega) hnotPlus hnotMinus
  obtain ⟨loopFinal, value, finalSat, hsuccess, hfinal, hfold⟩ :=
    scanInt_success_after_digit_check_packed_exs base input output pos start
      byte false hendLocal hmemInput hpackedMem hstart hbyteAt hdigit
      houtput houtLocal hppLocal hcursorLocal hsignLocal hro
  refine ⟨loopFinal, value, finalSat, ?_, hfinal, hfold⟩
  simpa using ExS.seq hnoSign hsuccess

/-- Compose the initial endpoint check and sign initialization with the
    no-sign success path, starting immediately after the caller cursor has
    been loaded into local 3. -/
theorem scanInt_success_no_sign_from_cursor_packed_exs (s : State)
    (input output : Block) (pos start : Nat) (byte : UInt8)
    (hendLocal : s.locals 1 = some (.ptr 20 input.length))
    (hmemInput : s.mem 20 = some input)
    (hpackedMem : s.mem = scanIntSuccessPackedMem input output pos)
    (hstart : start < input.length) (hbyteAt : input[start]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (houtput : 4 ≤ output.length)
    (houtLocal : s.locals 2 = some (.ptr 21 0))
    (hppLocal : s.locals 0 = some (.ptr 20 0))
    (hcursorLocal : s.locals 3 = some (.ptr 20 start))
    (hro : s.ro = false) :
    ∃ loopFinal value finalSat,
      ExS Gen.prog s
        (.seq scanIntStartFailureCheck
          (.seq (.set 4 (.const (.int IntTy.i32 1)))
            (.seq scanIntSignBranch
              (.seq scanIntEndFailureCheck scanIntSuccessRest))))
        (.ret (some (.int IntTy.u8 1)))
        ⟨loopFinal.locals,
          (fun b =>
            if b = 20 then some
              (encodeLE 8 (ptrPack (.ptr 20
                (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1))) ++ input)
            else if b = 21 then some
              (encodeLE 4 (IntTy.wrap IntTy.i32
                (scanDigits ((input.drop start).map UInt8.toNat) 0).2) ++ output.drop 4)
            else none),
          loopFinal.ro⟩ ∧
      loopFinal = scanLoopFrameAt
        ⟨Locals.upd s.locals 4 (.int IntTy.i32 1), s.mem, s.ro⟩
        (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((input.drop start).map UInt8.toNat) (0, false) := by
  have hge : EvE Gen.prog s
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin (EvE.var hcursorLocal) (EvE.var hendLocal)
    simp [evalBin, isPtr, boolVal]
    exact hstart
  have hfalse : truthy (boolVal false) = .ok false := by
    simp [truthy, boolVal, IntTy.i32]
  have hstartCheck : ExS Gen.prog s scanIntStartFailureCheck .normal s := by
    apply ExS.ite hge hfalse
    exact ExS.skip
  let initialized : State :=
    ⟨Locals.upd s.locals 4 (.int IntTy.i32 1), s.mem, s.ro⟩
  have hsetSign : ExS Gen.prog s (.set 4 (.const (.int IntTy.i32 1)))
      .normal initialized := by
    exact ExS.set (EvE.const _)
  have hendInit : initialized.locals 1 = some (.ptr 20 input.length) := by
    simpa [initialized] using hendLocal
  have hmemInit : initialized.mem 20 = some input := by
    simpa [initialized] using hmemInput
  have hpackedInit : initialized.mem = scanIntSuccessPackedMem input output pos := by
    simpa [initialized] using hpackedMem
  have houtInit : initialized.locals 2 = some (.ptr 21 0) := by
    simpa [initialized] using houtLocal
  have hppInit : initialized.locals 0 = some (.ptr 20 0) := by
    simpa [initialized] using hppLocal
  have hcursorInit : initialized.locals 3 = some (.ptr 20 start) := by
    simpa [initialized] using hcursorLocal
  have hsignInit : initialized.locals 4 = some (.int IntTy.i32 1) := by
    simp [initialized, Locals.upd]
  have hnoSign : byte.toNat ≠ 43 ∧ byte.toNat ≠ 45 := by omega
  obtain ⟨loopFinal, value, finalSat, hsuccess, hfinal, hfold⟩ :=
    scanInt_success_no_sign_packed_exs initialized input output pos start byte
      hendInit hmemInit hpackedInit hstart hbyteAt hdigit hnoSign.1 hnoSign.2
      houtput houtInit hppInit hcursorInit hsignInit (by simpa [initialized] using hro)
  have hsuccess' : ExS Gen.prog initialized
      (.seq scanIntSignBranch
        (.seq scanIntEndFailureCheck scanIntSuccessRest))
      (.ret (some (.int IntTy.u8 1)))
      ⟨loopFinal.locals,
        (fun b =>
          if b = 20 then some
            (encodeLE 8 (ptrPack (.ptr 20
              (start + (scanDigits ((input.drop start).map UInt8.toNat) 0).1))) ++ input)
          else if b = 21 then some
            (encodeLE 4 (IntTy.wrap IntTy.i32
              (scanDigits ((input.drop start).map UInt8.toNat) 0).2) ++ output.drop 4)
          else none), loopFinal.ro⟩ := hsuccess
  refine ⟨loopFinal, value, finalSat, ?_, hfinal, hfold⟩
  exact ExS.seq hstartCheck (ExS.seq hsetSign hsuccess')

/-- No-sign success from a scanner frame whose block 20 is the complete packed
    input buffer, with the start check and sign initialization included. -/
theorem scanInt_success_no_sign_from_cursor_actual_packed_exs (s : State)
    (packed output : Block) (start : Nat) (byte : UInt8)
    (hendLocal : s.locals 1 = some (.ptr 20 packed.length))
    (hpackedMem : s.mem = scanIntActualPackedMem packed output)
    (hstart : start < packed.length) (hbyteAt : packed[start]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hnotPlus : byte.toNat ≠ 43) (hnotMinus : byte.toNat ≠ 45)
    (hpacked : 8 ≤ packed.length) (houtput : 4 ≤ output.length)
    (houtLocal : s.locals 2 = some (.ptr 21 0))
    (hppLocal : s.locals 0 = some (.ptr 20 0))
    (hcursorLocal : s.locals 3 = some (.ptr 20 start))
    (hro : s.ro = false) :
    ∃ loopFinal value finalSat,
      ExS Gen.prog s
        (.seq scanIntStartFailureCheck
          (.seq (.set 4 (.const (.int IntTy.i32 1)))
            (.seq scanIntSignBranch
              (.seq scanIntEndFailureCheck scanIntSuccessRest))))
        (.ret (some (.int IntTy.u8 1)))
        ⟨loopFinal.locals,
          (fun b => if b = 20 then some
            (encodeLE 8 (ptrPack (.ptr 20
              (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1))) ++
              packed.drop 8)
          else if b = 21 then some
            (encodeLE 4 (IntTy.wrap IntTy.i32
              (scanDigits ((packed.drop start).map UInt8.toNat) 0).2) ++
              output.drop 4)
          else none), loopFinal.ro⟩ ∧
      loopFinal = scanLoopFrameAt
        ⟨Locals.upd s.locals 4 (.int IntTy.i32 1), s.mem, s.ro⟩
        (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((packed.drop start).map UInt8.toNat) (0, false) := by
  have hge : EvE Gen.prog s
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin (EvE.var hcursorLocal) (EvE.var hendLocal)
    simp [evalBin, isPtr, boolVal]
    exact hstart
  have hfalse : truthy (boolVal false) = .ok false := by
    simp [truthy, boolVal, IntTy.i32]
  have hstartCheck : ExS Gen.prog s scanIntStartFailureCheck .normal s := by
    apply ExS.ite hge hfalse
    exact ExS.skip
  let initialized : State :=
    ⟨Locals.upd s.locals 4 (.int IntTy.i32 1), s.mem, s.ro⟩
  have hsetSign : ExS Gen.prog s (.set 4 (.const (.int IntTy.i32 1)))
      .normal initialized := ExS.set (EvE.const _)
  have hendInit : initialized.locals 1 = some (.ptr 20 packed.length) := by
    simpa [initialized] using hendLocal
  have hpackedInit : initialized.mem = scanIntActualPackedMem packed output := by
    simpa [initialized] using hpackedMem
  have houtInit : initialized.locals 2 = some (.ptr 21 0) := by
    simpa [initialized] using houtLocal
  have hppInit : initialized.locals 0 = some (.ptr 20 0) := by
    simpa [initialized] using hppLocal
  have hcursorInit : initialized.locals 3 = some (.ptr 20 start) := by
    simpa [initialized] using hcursorLocal
  have hsignInit : initialized.locals 4 = some (.int IntTy.i32 1) := by
    simp [initialized, Locals.upd]
  obtain ⟨loopFinal, value, finalSat, hsuccess, hfinal, hfold⟩ :=
    scanInt_success_no_sign_actual_packed_exs initialized packed output start
      byte hendInit hpackedInit hstart hbyteAt hdigit hnotPlus hnotMinus
      hpacked houtput houtInit hppInit hcursorInit hsignInit
      (by simpa [initialized] using hro)
  have hsuccess' : ExS Gen.prog initialized
      (.seq scanIntSignBranch
        (.seq scanIntEndFailureCheck scanIntSuccessRest))
      (.ret (some (.int IntTy.u8 1)))
      ⟨loopFinal.locals,
        (fun b => if b = 20 then some
          (encodeLE 8 (ptrPack (.ptr 20
            (start + (scanDigits ((packed.drop start).map UInt8.toNat) 0).1))) ++
            packed.drop 8)
        else if b = 21 then some
          (encodeLE 4 (IntTy.wrap IntTy.i32
            (scanDigits ((packed.drop start).map UInt8.toNat) 0).2) ++
            output.drop 4)
        else none), loopFinal.ro⟩ := hsuccess
  refine ⟨loopFinal, value, finalSat, ?_, hfinal, hfold⟩
  exact ExS.seq hstartCheck (ExS.seq hsetSign hsuccess')

/-- Signed success from a scanner frame over the complete packed input block.
    The sign branch advances local 3, after which the framed loop and stores
    refine the remaining digit suffix. -/
theorem scanInt_success_sign_from_cursor_actual_packed_exs (s : State)
    (packed output : Block) (cursor : Nat) (sign digit : UInt8)
    (hendLocal : s.locals 1 = some (.ptr 20 packed.length))
    (hpackedMem : s.mem = scanIntActualPackedMem packed output)
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hsignAt : packed[cursor]? = some sign)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (hcursorBound : cursor + 1 ≤ packed.length)
    (hdigitAt : packed[cursor + 1]? = some digit)
    (hdigit : 48 ≤ digit.toNat ∧ digit.toNat ≤ 57)
    (hpacked : 8 ≤ packed.length) (houtput : 4 ≤ output.length)
    (houtLocal : s.locals 2 = some (.ptr 21 0))
    (hppLocal : s.locals 0 = some (.ptr 20 0))
    (hro : s.ro = false) :
    ∃ final, ExS Gen.prog s
      (.seq scanIntStartFailureCheck
        (.seq (.set 4 (.const (.int IntTy.i32 1)))
          (.seq scanIntSignBranch
            (.seq scanIntEndFailureCheck scanIntSuccessRest))))
      (.ret (some (.int IntTy.u8 1))) final ∧
      final.mem 20 = some
        (encodeLE 8 (ptrPack (.ptr 20
          (cursor + 1 +
            (scanDigits ((packed.drop (cursor + 1)).map UInt8.toNat) 0).1))) ++
          packed.drop 8) ∧
      final.mem 21 = some
        (encodeLE 4 (IntTy.wrap IntTy.i32
          (if sign.toNat = 45 then
            -((scanDigits ((packed.drop (cursor + 1)).map UInt8.toNat) 0).2 : Int)
           else (scanDigits ((packed.drop (cursor + 1)).map UInt8.toNat) 0).2)) ++
          output.drop 4) := by
  have hcursor : cursor < packed.length :=
    (List.getElem?_eq_some_iff.mp hsignAt).choose
  have hge : EvE Gen.prog s
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin (EvE.var hcursorLocal) (EvE.var hendLocal)
    simp [evalBin, isPtr, boolVal]
    exact hcursor
  have hfalse : truthy (boolVal false) = .ok false := by
    simp [truthy, boolVal, IntTy.i32]
  have hstartCheck : ExS Gen.prog s scanIntStartFailureCheck .normal s := by
    apply ExS.ite hge hfalse
    exact ExS.skip
  let initialized : State :=
    ⟨Locals.upd s.locals 4 (.int IntTy.i32 1), s.mem, s.ro⟩
  have hsetSign : ExS Gen.prog s (.set 4 (.const (.int IntTy.i32 1)))
      .normal initialized := ExS.set (EvE.const _)
  have hendInit : initialized.locals 1 = some (.ptr 20 packed.length) := by
    simpa [initialized] using hendLocal
  have hmemInit : initialized.mem 20 = some packed := by
    simpa [initialized, scanIntActualPackedMem] using
      congrArg (fun mem => mem 20) hpackedMem
  have hcursorInit : initialized.locals 3 = some (.ptr 20 cursor) := by
    simpa [initialized] using hcursorLocal
  have hsignInit : initialized.locals 4 = some (.int IntTy.i32 1) := by
    simp [initialized, Locals.upd]
  have houtInit : initialized.locals 2 = some (.ptr 21 0) := by
    simpa [initialized] using houtLocal
  have hppInit : initialized.locals 0 = some (.ptr 20 0) := by
    simpa [initialized] using hppLocal
  obtain ⟨afterSign, hsignBranch, hcursorAfter, hsignAfter,
      hlocal0After, hlocal2After, hendAfter, hmemAfter,
      _hlocalsAfter, hroAfter⟩ :=
    scanInt_signBranch_at initialized packed cursor sign hcursorInit hsignInit
      hmemInit hcursorBound hsignAt hsign
  let negative : Bool := decide (sign.toNat = 45)
  have hsignAfter' : afterSign.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)) := by
    simpa [negative] using hsignAfter
  have hmemAfter' : afterSign.mem = scanIntActualPackedMem packed output := by
    calc
      afterSign.mem = initialized.mem := hmemAfter
      _ = s.mem := rfl
      _ = scanIntActualPackedMem packed output := hpackedMem
  have hendAfter' : afterSign.locals 1 = some (.ptr 20 packed.length) := by
    simpa [hendAfter] using hendInit
  have houtAfter : afterSign.locals 2 = some (.ptr 21 0) := by
    simpa [hlocal2After] using houtInit
  have hppAfter : afterSign.locals 0 = some (.ptr 20 0) := by
    simpa [hlocal0After] using hppInit
  have hcursorAfterBound : cursor + 1 < packed.length :=
    (List.getElem?_eq_some_iff.mp hdigitAt).choose
  have hsuccess := scanInt_success_after_digit_check_actual_packed_exs
    afterSign packed output (cursor + 1) digit negative hendAfter' hmemAfter'
    hcursorAfterBound hdigitAt hdigit hpacked houtput houtAfter hppAfter
    hcursorAfter hsignAfter' (by simpa [hroAfter, initialized, hro])
  obtain ⟨loopFinal, _value, _finalSat, hrest, _hfinal, _hfold⟩ := hsuccess
  have hnegativeValue (digits : List Nat) :
      (if negative then -((scanDigits digits 0).2 : Int)
        else (scanDigits digits 0).2) =
      (if sign.toNat = 45 then -((scanDigits digits 0).2 : Int)
        else (scanDigits digits 0).2) := by
    rcases hsign with hplus | hminus
    · have hnot : sign.toNat ≠ 45 := by omega
      simp [negative, hplus, hnot]
    · simp [negative, hminus]
  have hrest' := hrest
  rw [hnegativeValue ((packed.drop (cursor + 1)).map UInt8.toNat)] at hrest'
  let final : State := ⟨loopFinal.locals,
    (fun b => if b = 20 then some
      (encodeLE 8 (ptrPack (.ptr 20
        (cursor + 1 +
          (scanDigits ((packed.drop (cursor + 1)).map UInt8.toNat) 0).1))) ++
        packed.drop 8)
      else if b = 21 then some
        (encodeLE 4 (IntTy.wrap IntTy.i32
          (if sign.toNat = 45 then
            -((scanDigits ((packed.drop (cursor + 1)).map UInt8.toNat) 0).2 : Int)
           else (scanDigits ((packed.drop (cursor + 1)).map UInt8.toNat) 0).2)) ++
          output.drop 4)
      else none), loopFinal.ro⟩
  have hbody : ExS Gen.prog s
      (.seq scanIntStartFailureCheck
        (.seq (.set 4 (.const (.int IntTy.i32 1)))
          (.seq scanIntSignBranch
            (.seq scanIntEndFailureCheck scanIntSuccessRest))))
      (.ret (some (.int IntTy.u8 1))) final := by
    exact ExS.seq hstartCheck (ExS.seq hsetSign (ExS.seq hsignBranch hrest'))
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa [final, negative] using hbody
  · simp [final]
  · simp [final]

/-- Full no-sign success composition from a raw byte slice: the whitespace
    helper advances the packed pointer cell, the scanner reloads it, and the
    actual packed-buffer loop consumes the same suffix as the pure spec. -/
theorem scanInt_success_body_ast :
    Gen.tobj_scan_int.body =
      (.seq (.call none 23 [.var 0, .var 1])
        (.seq (.set 3 (.load .ptr (.var 0)))
          (.seq scanIntStartFailureCheck
            (.seq (.set 4 (.const (.int IntTy.i32 1)))
              (.seq scanIntSignBranch
                (.seq scanIntEndFailureCheck scanIntSuccessRest)))))) := by
  rfl

/-- The pure specification agrees with the positive digit fold when the
    first non-space byte is a decimal digit rather than a sign. -/
theorem scanInt_no_sign_success_spec_from_bytes (bytes : Block) (pos : Nat)
    (byte : UInt8)
    (hbyteAt : (bytes.drop pos)[((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hnotPlus : byte.toNat ≠ 43) (hnotMinus : byte.toNat ≠ 45) :
    let rest := bytes.drop pos
    let spaces := (rest.takeWhile (fun b => scanSpace b.toNat)).length
    let digits := (bytes.drop (pos + spaces)).map UInt8.toNat
    scanInt (bytes.map UInt8.toNat) pos =
      (true, ((scanDigits digits 0).2 : Int),
        pos + spaces + (scanDigits digits 0).1) := by
  dsimp
  let raw := (bytes.drop pos).map UInt8.toNat
  let spaces := ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length
  let digits := (bytes.drop (pos + spaces)).map UInt8.toNat
  have hspaces : (raw.takeWhile scanSpace).length = spaces := by
    simp only [raw, spaces, List.takeWhile_map, List.length_map]
    rfl
  have hrawSource : (bytes.map UInt8.toNat).drop pos = raw := by
    simp [raw]
  have hbyteRaw : raw[spaces]? = some byte.toNat := by
    simpa [raw, spaces, List.getElem?_map, List.takeWhile_map] using
      congrArg (Option.map UInt8.toNat) hbyteAt
  have hbyte0 : (raw.drop spaces)[0]? = some byte.toNat := by
    simpa only [List.getElem?_drop, Nat.add_zero] using hbyteRaw
  have hrawDigits : raw.drop spaces = digits := by
    simp [digits, raw]
  cases hafter : raw.drop spaces with
  | nil => simp [hafter] at hbyte0
  | cons first suffix =>
    rw [hafter] at hbyte0
    simp at hbyte0
    have hfirst : first = byte.toNat := hbyte0
    subst first
    have hdigitsCons : digits = byte.toNat :: suffix := by
      rw [← hrawDigits, hafter]
    have hdigitOk : scanDigit byte.toNat = true := by
      simp [scanDigit, hdigit]
    have hscan : scanInt (bytes.map UInt8.toNat) pos =
        (true, ((scanDigits digits 0).2 : Int),
          pos + spaces + (scanDigits digits 0).1) := by
      unfold scanInt
      simp only [List.drop_zero, hrawSource, hspaces]
      simp [hafter, hbyteRaw, hdigitsCons, hnotPlus, hnotMinus, hdigitOk, scanIntDigits,
        scanDigit, hdigit, scanIntSignedValue, Nat.add_assoc]
    simpa [raw, digits, Nat.add_assoc] using hscan

theorem scanInt_success_no_sign_after_whitespace_exs (s : State)
    (bytes output : Block) (pos : Nat) (byte : UInt8)
    (hpp : s.locals 0 = some (.ptr 20 0))
    (hend : s.locals 1 = some (.ptr 20 (8 + bytes.length)))
    (hout : s.locals 2 = some (.ptr 21 0))
    (hmem : s.mem = scanIntSuccessPackedMem bytes output pos)
    (hro : s.ro = false) (hbound : 8 + bytes.length < 4294967296)
    (hpos : pos ≤ bytes.length)
    (houtput : 4 ≤ output.length)
    (hbyteAt : (bytes.drop pos)[((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hnotPlus : byte.toNat ≠ 43) (hnotMinus : byte.toNat ≠ 45) :
    let rest := bytes.drop pos
    let spaces := (rest.takeWhile (fun b => scanSpace b.toNat)).length
    let digits := (bytes.drop (pos + spaces)).map UInt8.toNat
    ∃ final, ExS Gen.prog s
      (.seq (.call none 23 [.var 0, .var 1])
        (.seq (.set 3 (.load .ptr (.var 0)))
          (.seq scanIntStartFailureCheck
            (.seq (.set 4 (.const (.int IntTy.i32 1)))
              (.seq scanIntSignBranch
                (.seq scanIntEndFailureCheck scanIntSuccessRest))))))
      (.ret (some (.int IntTy.u8 1))) final ∧
      final.mem 20 = some
        (encodeLE 8 (ptrPack (.ptr 20 (8 + pos + spaces + (scanDigits digits 0).1))) ++
          bytes) ∧
      final.mem 21 = some
        (encodeLE 4 (IntTy.wrap IntTy.i32 (scanDigits digits 0).2) ++
          output.drop 4) ∧
      scanInt (bytes.map UInt8.toNat) pos =
        (true, ((scanDigits digits 0).2 : Int),
          pos + spaces + (scanDigits digits 0).1) := by
  dsimp
  let spaces := ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length
  let start := 8 + pos + spaces
  let packed := skipSpacePackedBlock bytes (pos + spaces)
  let digits := (bytes.drop (pos + spaces)).map UInt8.toNat
  let afterSetup : State :=
    ⟨Locals.upd s.locals 3 (.ptr 20 start),
      scanIntSuccessPackedMem bytes output (pos + spaces), false⟩
  have hlenDrop : (bytes.drop pos).length = bytes.length - pos := by simp
  have hspacesBound : spaces ≤ bytes.length := by
    have hprefix : (bytes.drop pos).takeWhile (fun b => scanSpace b.toNat) <+:
        bytes.drop pos :=
      List.takeWhile_prefix _
    have hle : spaces ≤ (bytes.drop pos).length := by
      dsimp [spaces]
      exact hprefix.length_le
    omega
  have hbyteStart : pos + spaces < bytes.length := by
    have hget := (List.getElem?_eq_some_iff.mp hbyteAt).choose
    omega
  have hdrop : packed.drop start = bytes.drop (pos + spaces) := by
    have hstart : start = 8 + (pos + spaces) := by dsimp [start]; omega
    rw [hstart]
    dsimp [packed, start]
    exact skipSpacePackedBlock_drop bytes (pos + spaces)
  have hpackedTail : packed.drop 8 = bytes := by
    dsimp [packed, skipSpacePackedBlock]
    simp [encodeLE_length]
  have hbyte0 : (bytes.drop (pos + spaces))[0]? = some byte := by
    simpa only [List.getElem?_drop, Nat.add_zero] using hbyteAt
  have hpackedByte0 : (packed.drop start)[0]? = some byte := by
    rw [hdrop]
    exact hbyte0
  have hpackedByte : packed[start]? = some byte := by
    simpa only [List.getElem?_drop, Nat.add_zero] using hpackedByte0
  obtain ⟨afterCall, hcall, hcallState, hset⟩ :=
    scanInt_setup_after_whitespace_exs s bytes output pos
      hpp hend hout hmem hro hpos hbound
  have hsetSetup : ExS Gen.prog afterCall (.set 3 (.load .ptr (.var 0)))
      .normal afterSetup := by
    simpa [afterSetup, start, spaces, hro] using hset
  have hpackedMem : afterSetup.mem = scanIntActualPackedMem packed output := by
    funext b
    by_cases hb20 : b = 20
    · subst b
      simp [afterSetup, scanIntActualPackedMem, scanIntSuccessPackedMem,
        packed, skipSpacePackedBlock]
    · by_cases hb21 : b = 21
      · subst b
        simp [afterSetup, scanIntActualPackedMem, scanIntSuccessPackedMem]
      · simp [afterSetup, scanIntActualPackedMem, scanIntSuccessPackedMem,
          hb20, hb21]
  have hendSetup : afterSetup.locals 1 = some (.ptr 20 packed.length) := by
    have hlen : packed.length = 8 + bytes.length := by
      simp [packed, skipSpacePackedBlock, encodeLE_length]
    simp [afterSetup, start, hlen, hend]
  have hstartSetup : start < packed.length := by
    have hlen : packed.length = 8 + bytes.length := by
      simp [packed, skipSpacePackedBlock, encodeLE_length]
    dsimp [start]
    omega
  have hcursorSetup : afterSetup.locals 3 = some (.ptr 20 start) := by
    simp [afterSetup]
  have hppSetup : afterSetup.locals 0 = some (.ptr 20 0) := by
    simp [afterSetup, hpp]
  have houtSetup : afterSetup.locals 2 = some (.ptr 21 0) := by
    simp [afterSetup, hout]
  have hsuccess := scanInt_success_no_sign_from_cursor_actual_packed_exs
    afterSetup packed output start byte hendSetup hpackedMem hstartSetup
    hpackedByte hdigit (by omega) (by omega) (by omega) houtput
    houtSetup hppSetup hcursorSetup rfl
  obtain ⟨loopFinal, value, finalSat, hrest, hfinal, hfold⟩ := hsuccess
  have hdigits :
      (scanDigits ((packed.drop start).map UInt8.toNat) 0) = scanDigits digits 0 := by
    simp [hdrop, digits]
  have hbody := ExS.seq hcall (ExS.seq hsetSetup hrest)
  let final : State := ⟨loopFinal.locals,
    (fun b => if b = 20 then some
      (encodeLE 8 (ptrPack (.ptr 20
        (8 + pos + spaces + (scanDigits digits 0).1))) ++ bytes)
      else if b = 21 then some
        (encodeLE 4 (IntTy.wrap IntTy.i32 (scanDigits digits 0).2) ++ output.drop 4)
      else none), loopFinal.ro⟩
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · simpa [final, afterSetup, start, spaces, digits, packed, hdigits, hdrop,
      hpackedTail, scanIntSuccessPackedMem, IntTy.wrap, IntTy.i32] using hbody
  · simp [final, start, spaces, digits]
  · simp [final, start, spaces, digits]
  · exact scanInt_no_sign_success_spec_from_bytes bytes pos byte hbyteAt hdigit
      hnotPlus hnotMinus

/-- The pure specification returns the same suffix fold and cursor for raw
    bytes whose first non-space byte is an optional sign followed by a digit. -/
theorem scanInt_signed_success_spec_from_bytes (bytes : Block) (pos : Nat)
    (sign digit : UInt8)
    (hsignAt : (bytes.drop pos)[((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length]? = some sign)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (hdigitAt : (bytes.drop pos)[((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length + 1]? = some digit)
    (hdigit : 48 ≤ digit.toNat ∧ digit.toNat ≤ 57) :
    let rest := bytes.drop pos
    let spaces := (rest.takeWhile (fun b => scanSpace b.toNat)).length
    let digits := (bytes.drop (pos + spaces + 1)).map UInt8.toNat
    scanInt (bytes.map UInt8.toNat) pos =
      (true,
        if sign.toNat = 45 then -((scanDigits digits 0).2 : Int)
        else (scanDigits digits 0).2,
        pos + spaces + 1 + (scanDigits digits 0).1) := by
  dsimp
  let raw := (bytes.drop pos).map UInt8.toNat
  let spaces := ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length
  let digits := (bytes.drop (pos + spaces + 1)).map UInt8.toNat
  have hspaces : (raw.takeWhile scanSpace).length = spaces := by
    simp only [raw, spaces, List.takeWhile_map, List.length_map]
    rfl
  have hrawSource : (bytes.map UInt8.toNat).drop pos = raw := by
    simp [raw]
  have hsignRaw : raw[spaces]? = some sign.toNat := by
    simpa [raw, spaces, List.getElem?_map, List.takeWhile_map] using
      congrArg (Option.map UInt8.toNat) hsignAt
  have hdigitRaw : raw[spaces + 1]? = some digit.toNat := by
    simpa [raw, spaces, List.getElem?_map, List.takeWhile_map] using
      congrArg (Option.map UInt8.toNat) hdigitAt
  have hsign0 : (raw.drop spaces)[0]? = some sign.toNat := by
    simpa only [List.getElem?_drop, Nat.add_zero] using hsignRaw
  have hafterDigit : (raw.drop spaces)[1]? = some digit.toNat := by
    simpa only [List.getElem?_drop] using hdigitRaw
  cases hafter : raw.drop spaces with
  | nil => simp [hafter] at hsign0
  | cons first suffix =>
    rw [hafter] at hsign0 hafterDigit
    simp at hsign0
    have hfirst : first = sign.toNat := hsign0
    subst first
    have hsignList : raw.drop spaces = sign.toNat :: suffix := hafter
    have hdigitSuffix : suffix[0]? = some digit.toNat := by
      simpa using hafterDigit
    cases hsuffix : suffix with
    | nil => simp [hsuffix] at hdigitSuffix
    | cons firstDigit rest =>
      have hfirstDigit : firstDigit = digit.toNat := by
        simpa [hsuffix] using hdigitSuffix
      subst firstDigit
      have hdropDigits : raw.drop (spaces + 1) = suffix := by
        calc
          raw.drop (spaces + 1) = (raw.drop spaces).drop 1 := by
            rw [List.drop_drop]
          _ = suffix := by rw [hsignList]; rfl
      have hdigitOk : scanDigit digit.toNat = true := by
        simp [scanDigit, hdigit]
      have hdigitsMap : suffix = digits := by
        rw [← hdropDigits]
        simp [digits, raw, Nat.add_assoc]
      have hrawDigits : raw.drop (spaces + 1) = digits := by
        rw [hdropDigits, hdigitsMap]
      have hrawAfter : raw.drop spaces = sign.toNat :: digits := by
        rw [hsignList, hdigitsMap]
      have hdigitsCons : digits = digit.toNat :: rest := by
        calc
          digits = suffix := hdigitsMap.symm
          _ = digit.toNat :: rest := hsuffix
      have hscan : scanInt (bytes.map UInt8.toNat) pos =
          (true,
            if sign.toNat = 45 then -((scanDigits digits 0).2 : Int)
            else (scanDigits digits 0).2,
            pos + spaces + 1 + (scanDigits digits 0).1) := by
        unfold scanInt
        simp only [hrawSource]
        rw [hspaces]
        simp [hrawAfter, hrawDigits, hdigitsCons, hsign, scanIntDigits,
          hdigitOk, scanIntSignedValue, Nat.add_assoc]
      simpa [raw, digits, Nat.add_assoc] using hscan

/-- Full signed success composition from raw bytes: whitespace skipping stores
    the packed cursor, the generated sign branch consumes one sign byte, and
    the digit loop and success stores refine the remaining raw suffix. -/
theorem scanInt_success_sign_after_whitespace_exs (s : State)
    (bytes output : Block) (pos : Nat) (sign digit : UInt8)
    (hpp : s.locals 0 = some (.ptr 20 0))
    (hend : s.locals 1 = some (.ptr 20 (8 + bytes.length)))
    (hout : s.locals 2 = some (.ptr 21 0))
    (hmem : s.mem = scanIntSuccessPackedMem bytes output pos)
    (hro : s.ro = false) (hbound : 8 + bytes.length < 4294967296)
    (hpos : pos ≤ bytes.length)
    (houtput : 4 ≤ output.length)
    (hsignAt : (bytes.drop pos)[((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length]? = some sign)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (hdigitAt : (bytes.drop pos)[((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length + 1]? = some digit)
    (hdigit : 48 ≤ digit.toNat ∧ digit.toNat ≤ 57) :
    let rest := bytes.drop pos
    let spaces := (rest.takeWhile (fun b => scanSpace b.toNat)).length
    let digits := (bytes.drop (pos + spaces + 1)).map UInt8.toNat
    ∃ final, ExS Gen.prog s
      (.seq (.call none 23 [.var 0, .var 1])
        (.seq (.set 3 (.load .ptr (.var 0)))
          (.seq scanIntStartFailureCheck
            (.seq (.set 4 (.const (.int IntTy.i32 1)))
              (.seq scanIntSignBranch
                (.seq scanIntEndFailureCheck scanIntSuccessRest))))))
      (.ret (some (.int IntTy.u8 1))) final ∧
      final.mem 20 = some
        (encodeLE 8 (ptrPack (.ptr 20
          (8 + pos + spaces + 1 + (scanDigits digits 0).1))) ++ bytes) ∧
      final.mem 21 = some
        (encodeLE 4 (IntTy.wrap IntTy.i32
          (if sign.toNat = 45 then -((scanDigits digits 0).2 : Int)
           else (scanDigits digits 0).2)) ++ output.drop 4) ∧
      scanInt (bytes.map UInt8.toNat) pos =
        (true,
          if sign.toNat = 45 then -((scanDigits digits 0).2 : Int)
          else (scanDigits digits 0).2,
          pos + spaces + 1 + (scanDigits digits 0).1) := by
  dsimp
  let spaces := ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length
  let start := 8 + pos + spaces
  let packed := skipSpacePackedBlock bytes (pos + spaces)
  let digits := (bytes.drop (pos + spaces + 1)).map UInt8.toNat
  let afterSetup : State :=
    ⟨Locals.upd s.locals 3 (.ptr 20 start),
      scanIntSuccessPackedMem bytes output (pos + spaces), false⟩
  have hspacesBound : spaces ≤ bytes.length := by
    have hprefix : (bytes.drop pos).takeWhile (fun b => scanSpace b.toNat) <+:
        bytes.drop pos :=
      List.takeWhile_prefix _
    have hle : spaces ≤ (bytes.drop pos).length := by
      dsimp [spaces]
      exact hprefix.length_le
    have hlen : (bytes.drop pos).length = bytes.length - pos := by simp
    omega
  have hlenDrop : (bytes.drop pos).length = bytes.length - pos := by simp
  have hsignRaw0 : (bytes.drop (pos + spaces))[0]? = some sign := by
    simpa only [List.getElem?_drop, Nat.add_zero] using hsignAt
  have hstartEq : start = 8 + (pos + spaces) := by
    dsimp [start]
    omega
  have hdropStart : packed.drop start = bytes.drop (pos + spaces) := by
    rw [hstartEq]
    exact skipSpacePackedBlock_drop bytes (pos + spaces)
  have hsignPacked0 : (packed.drop start)[0]? = some sign := by
    rw [hdropStart]
    exact hsignRaw0
  have hsignPacked : packed[start]? = some sign := by
    simpa only [List.getElem?_drop, Nat.add_zero] using hsignPacked0
  have hdigitRaw1 : (bytes.drop (pos + spaces))[1]? = some digit := by
    simpa only [List.getElem?_drop, Nat.add_assoc] using hdigitAt
  have hdigitPacked1 : (packed.drop start)[1]? = some digit := by
    rw [hdropStart]
    exact hdigitRaw1
  have hdigitPacked : packed[start + 1]? = some digit := by
    simpa only [List.getElem?_drop] using hdigitPacked1
  have hpackedTail : packed.drop 8 = bytes := by
    dsimp [packed, skipSpacePackedBlock]
    simp [encodeLE_length]
  have hdropDigit : packed.drop (start + 1) = bytes.drop (pos + spaces + 1) := by
    calc
      packed.drop (start + 1) = (packed.drop start).drop 1 := by
        rw [List.drop_drop]
      _ = (bytes.drop (pos + spaces)).drop 1 := by
        rw [hdropStart]
      _ = bytes.drop (pos + spaces + 1) := by
        rw [List.drop_drop]
  obtain ⟨afterCall, hcall, hcallState, hset⟩ :=
    scanInt_setup_after_whitespace_exs s bytes output pos
      hpp hend hout hmem hro hpos hbound
  have hsetSetup : ExS Gen.prog afterCall (.set 3 (.load .ptr (.var 0)))
      .normal afterSetup := by
    simpa [afterSetup, start, spaces, hro] using hset
  have hpackedMem : afterSetup.mem = scanIntActualPackedMem packed output := by
    funext b
    by_cases hb20 : b = 20
    · subst b
      simp [afterSetup, scanIntActualPackedMem, scanIntSuccessPackedMem,
        packed, skipSpacePackedBlock]
    · by_cases hb21 : b = 21
      · subst b
        simp [afterSetup, scanIntActualPackedMem, scanIntSuccessPackedMem]
      · simp [afterSetup, scanIntActualPackedMem, scanIntSuccessPackedMem,
          hb20, hb21]
  have hendSetup : afterSetup.locals 1 = some (.ptr 20 packed.length) := by
    have hlen : packed.length = 8 + bytes.length := by
      simp [packed, skipSpacePackedBlock, encodeLE_length]
    simp [afterSetup, start, hlen, hend]
  have hstartSetup : start < packed.length := by
    have hget := (List.getElem?_eq_some_iff.mp hsignAt).choose
    have hlen : packed.length = 8 + bytes.length := by
      simp [packed, skipSpacePackedBlock, encodeLE_length]
    dsimp [start]
    omega
  have hcursorBound : start + 1 ≤ packed.length := by
    have hget := (List.getElem?_eq_some_iff.mp hdigitAt).choose
    have hlen : packed.length = 8 + bytes.length := by
      simp [packed, skipSpacePackedBlock, encodeLE_length]
    dsimp [start]
    omega
  have hcursorSetup : afterSetup.locals 3 = some (.ptr 20 start) := by
    simp [afterSetup]
  have hppSetup : afterSetup.locals 0 = some (.ptr 20 0) := by
    simp [afterSetup, hpp]
  have houtSetup : afterSetup.locals 2 = some (.ptr 21 0) := by
    simp [afterSetup, hout]
  obtain ⟨final, hsuccess, hmem20, hmem21⟩ :=
    scanInt_success_sign_from_cursor_actual_packed_exs afterSetup packed output
      start sign digit hendSetup hpackedMem hcursorSetup hsignPacked hsign
      hcursorBound hdigitPacked hdigit (by omega) houtput houtSetup hppSetup rfl
  have hbody := ExS.seq hcall (ExS.seq hsetSetup hsuccess)
  let final' : State := final
  have hfinal20 : final'.mem 20 = some
      (encodeLE 8 (ptrPack (.ptr 20
        (8 + pos + spaces + 1 + (scanDigits digits 0).1))) ++ bytes) := by
    simpa [final', start, digits, hdropDigit, hpackedTail] using hmem20
  have hfinal21 : final'.mem 21 = some
      (encodeLE 4 (IntTy.wrap IntTy.i32
        (if sign.toNat = 45 then -((scanDigits digits 0).2 : Int)
         else (scanDigits digits 0).2)) ++ output.drop 4) := by
    simpa [final', digits, hdropDigit] using hmem21
  refine ⟨final', hbody, hfinal20, hfinal21, ?_⟩
  exact scanInt_signed_success_spec_from_bytes bytes pos sign digit
      hsignAt hsign hdigitAt hdigit

/-- Lift the no-sign success execution to an outside `callFunc` result from
    the scanner's parameter frame, retaining the pure result and both writes. -/
theorem scanInt_success_no_sign_after_whitespace_callFunc
    (bytes output : Block) (pos : Nat) (byte : UInt8)
    (hbound : 8 + bytes.length < 4294967296)
    (hpos : pos ≤ bytes.length) (houtput : 4 ≤ output.length)
    (hbyteAt : (bytes.drop pos)[((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length]? = some byte)
    (hdigit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
    (hnotPlus : byte.toNat ≠ 43) (hnotMinus : byte.toNat ≠ 45) :
    let spaces := ((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length
    let digits := (bytes.drop (pos + spaces)).map UInt8.toNat
    ∃ (K : Nat) (final : State),
      (∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output pos) =
          .ok (some (.int IntTy.u8 1), final.mem)) ∧
      final.mem 20 = some
        (encodeLE 8 (ptrPack (.ptr 20
          (8 + pos + spaces + (scanDigits digits 0).1))) ++ bytes) ∧
      final.mem 21 = some
        (encodeLE 4 (IntTy.wrap IntTy.i32 (scanDigits digits 0).2) ++
          output.drop 4) ∧
      scanInt (bytes.map UInt8.toNat) pos =
        (true, ((scanDigits digits 0).2 : Int),
          pos + spaces + (scanDigits digits 0).1) := by
  dsimp
  let initial : State :=
    ⟨frameLocals [0, 1, 2]
      [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0],
      scanIntSuccessPackedMem bytes output pos, false⟩
  have hpp : initial.locals 0 = some (.ptr 20 0) := by
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hend : initial.locals 1 = some (.ptr 20 (8 + bytes.length)) := by
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hout : initial.locals 2 = some (.ptr 21 0) := by
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  obtain ⟨final, hbody, hmem20, hmem21, hspec⟩ :=
    scanInt_success_no_sign_after_whitespace_exs initial bytes output pos byte
      hpp hend hout rfl rfl hbound hpos houtput hbyteAt hdigit
      hnotPlus hnotMinus
  have hgen : ExS Gen.prog
      ⟨frameLocals Gen.tobj_scan_int.params
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0],
        scanIntSuccessPackedMem bytes output pos, false⟩
      Gen.tobj_scan_int.body (.ret (some (.int IntTy.u8 1))) final := by
    rw [scanInt_success_body_ast]
    exact hbody
  obtain ⟨K, hcall⟩ := callFunc_of_ExS (p := Gen.prog)
    (f := Gen.fid_tobj_scan_int) (fn := Gen.tobj_scan_int)
    (args := [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0])
    (m := scanIntSuccessPackedMem bytes output pos)
    (v := some (.int IntTy.u8 1)) (s' := final)
    (hf := by rfl) (hlen := by rfl) hgen
  exact ⟨K, final, fun n hn => hcall n hn, hmem20, hmem21, hspec⟩

/-- Outside `callFunc` result for signed successful input at an arbitrary
    starting offset, including its memory writes and pure scanner tuple. -/
theorem scanInt_success_sign_after_whitespace_callFunc
    (bytes output : Block) (pos : Nat) (sign digit : UInt8)
    (hbound : 8 + bytes.length < 4294967296)
    (hpos : pos ≤ bytes.length) (houtput : 4 ≤ output.length)
    (hsignAt : (bytes.drop pos)[((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length]? = some sign)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (hdigitAt : (bytes.drop pos)[((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length + 1]? = some digit)
    (hdigit : 48 ≤ digit.toNat ∧ digit.toNat ≤ 57) :
    let spaces := ((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length
    let digits := (bytes.drop (pos + spaces + 1)).map UInt8.toNat
    ∃ (K : Nat) (final : State),
      (∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output pos) =
          .ok (some (.int IntTy.u8 1), final.mem)) ∧
      final.mem 20 = some
        (encodeLE 8 (ptrPack (.ptr 20
          (8 + pos + spaces + 1 + (scanDigits digits 0).1))) ++ bytes) ∧
      final.mem 21 = some
        (encodeLE 4 (IntTy.wrap IntTy.i32
          (if sign.toNat = 45 then -((scanDigits digits 0).2 : Int)
           else (scanDigits digits 0).2)) ++ output.drop 4) ∧
      scanInt (bytes.map UInt8.toNat) pos =
        (true,
          if sign.toNat = 45 then -((scanDigits digits 0).2 : Int)
          else (scanDigits digits 0).2,
          pos + spaces + 1 + (scanDigits digits 0).1) := by
  dsimp
  let initial : State :=
    ⟨frameLocals [0, 1, 2]
      [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0],
      scanIntSuccessPackedMem bytes output pos, false⟩
  have hpp : initial.locals 0 = some (.ptr 20 0) := by
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hend : initial.locals 1 = some (.ptr 20 (8 + bytes.length)) := by
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hout : initial.locals 2 = some (.ptr 21 0) := by
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  obtain ⟨final, hbody, hmem20, hmem21, hspec⟩ :=
    scanInt_success_sign_after_whitespace_exs initial bytes output pos sign digit
      hpp hend hout rfl rfl hbound hpos houtput hsignAt hsign hdigitAt hdigit
  have hgen : ExS Gen.prog
      ⟨frameLocals Gen.tobj_scan_int.params
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0],
        scanIntSuccessPackedMem bytes output pos, false⟩
      Gen.tobj_scan_int.body (.ret (some (.int IntTy.u8 1))) final := by
    rw [scanInt_success_body_ast]
    exact hbody
  obtain ⟨K, hcall⟩ := callFunc_of_ExS (p := Gen.prog)
    (f := Gen.fid_tobj_scan_int) (fn := Gen.tobj_scan_int)
    (args := [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0])
    (m := scanIntSuccessPackedMem bytes output pos)
    (v := some (.int IntTy.u8 1)) (s' := final)
    (hf := by rfl) (hlen := by rfl) hgen
  exact ⟨K, final, fun n hn => hcall n hn, hmem20, hmem21, hspec⟩

/-- A consumed optional sign followed by a digit composes the generated sign
    branch with the successful digit check and framed-loop suffix. -/
theorem scanInt_success_after_sign_packed_exs (s : State)
    (input output : Block) (pos cursor : Nat) (sign digit : UInt8)
    (hmemInput : s.mem 20 = some input)
    (hpackedMem : s.mem = scanIntSuccessPackedMem input output pos)
    (hendLocal : s.locals 1 = some (.ptr 20 input.length))
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hsignLocal : s.locals 4 = some (.int IntTy.i32 1))
    (houtLocal : s.locals 2 = some (.ptr 21 0))
    (hppLocal : s.locals 0 = some (.ptr 20 0))
    (houtput : 4 ≤ output.length)
    (hcursorBound : cursor + 1 ≤ input.length)
    (hsignAt : input[cursor]? = some sign)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (hdigitAt : input[cursor + 1]? = some digit)
    (hdigit : 48 ≤ digit.toNat ∧ digit.toNat ≤ 57)
    (hro : s.ro = false) :
    ∃ loopFinal value finalSat,
      ExS Gen.prog s
        (.seq scanIntSignBranch
          (.seq scanIntEndFailureCheck scanIntSuccessRest))
        (.ret (some (.int IntTy.u8 1)))
        ⟨loopFinal.locals,
          (fun b =>
            if b = 20 then some
              (encodeLE 8 (ptrPack (.ptr 20
                (cursor + 1 + (scanDigits ((input.drop (cursor + 1)).map UInt8.toNat) 0).1))) ++ input)
            else if b = 21 then some
              (encodeLE 4 (IntTy.wrap IntTy.i32
                (if sign.toNat = 45 then
                  -((scanDigits ((input.drop (cursor + 1)).map UInt8.toNat) 0).2 : Int)
                 else (scanDigits ((input.drop (cursor + 1)).map UInt8.toNat) 0).2)) ++ output.drop 4)
            else none),
          loopFinal.ro⟩ ∧
      loopFinal = scanLoopFrameAt
        ⟨Locals.upd
          (Locals.upd s.locals 4 (.int IntTy.i32
            (if sign.toNat = 45 then IntTy.wrap IntTy.i32 (-1) else 1)))
          3 (.ptr 20 (cursor + 1)), s.mem, s.ro⟩
        (cursor + 1 + (scanDigits ((input.drop (cursor + 1)).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((input.drop (cursor + 1)).map UInt8.toNat) (0, false) := by
  obtain ⟨afterSign, hsignBranch, hcursorAfter, hsignAfter,
      hlocal0After, hlocal2After, hendAfter, hmemAfter,
      hlocalsAfter, hroAfter⟩ :=
    scanInt_signBranch_at s input cursor sign hcursorLocal hsignLocal
      hmemInput hcursorBound hsignAt hsign
  have hcursorAfterDigit : afterSign.locals 3 = some (.ptr 20 (cursor + 1)) :=
    hcursorAfter
  have hsignAfterDigit : afterSign.locals 4 = some (.int IntTy.i32
      (if sign.toNat = 45 then IntTy.wrap IntTy.i32 (-1) else 1)) := by
    simpa using hsignAfter
  have houtAfter : afterSign.locals 2 = some (.ptr 21 0) := by
    rw [hlocal2After, houtLocal]
  have hppAfter : afterSign.locals 0 = some (.ptr 20 0) := by
    rw [hlocal0After, hppLocal]
  have hendAfter' : afterSign.locals 1 = some (.ptr 20 input.length) := by
    rw [hendAfter, hendLocal]
  have hmemInputAfter : afterSign.mem 20 = some input := by
    rw [hmemAfter]
    exact hmemInput
  have hpackedMemAfter : afterSign.mem = scanIntSuccessPackedMem input output pos := by
    rw [hmemAfter]
    exact hpackedMem
  have hroFinalAfter : afterSign.ro = false := by
    rw [hroAfter]
    exact hro
  let branchFrame : State :=
    ⟨Locals.upd
      (Locals.upd s.locals 4 (.int IntTy.i32
        (if sign.toNat = 45 then IntTy.wrap IntTy.i32 (-1) else 1)))
      3 (.ptr 20 (cursor + 1)), s.mem, s.ro⟩
  have hbranchState : afterSign = branchFrame := by
    cases afterSign with
    | mk locals mem ro =>
      dsimp at hlocalsAfter hmemAfter hroAfter
      subst locals
      subst mem
      subst ro
      rfl
  have hdigitBound : cursor + 1 < input.length :=
    (List.getElem?_eq_some_iff.mp hdigitAt).choose
  let negative : Bool := decide (sign.toNat = 45)
  have hsignAfterDigit' : afterSign.locals 4 = some (.int IntTy.i32
      (if negative then IntTy.wrap IntTy.i32 (-1) else 1)) := by
    simpa [negative] using hsignAfterDigit
  have hsuccess := scanInt_success_after_digit_check_packed_exs afterSign
    input output pos (cursor + 1) digit negative
    hendAfter' hmemInputAfter hpackedMemAfter hdigitBound hdigitAt hdigit
    houtput houtAfter hppAfter hcursorAfterDigit hsignAfterDigit' hroFinalAfter
  obtain ⟨loopFinal, value, finalSat, hsuccess', hfinal, hfold⟩ := hsuccess
  rw [hbranchState] at hfinal
  refine ⟨loopFinal, value, finalSat, ?_, hfinal, hfold⟩
  · simpa [negative] using ExS.seq hsignBranch hsuccess'

/-- Compose the initial endpoint check and sign initialization with the
    consumed-sign success path, starting immediately after `p = *pp`. -/
theorem scanInt_success_sign_from_cursor_packed_exs (s : State)
    (input output : Block) (pos cursor : Nat) (sign digit : UInt8)
    (hendLocal : s.locals 1 = some (.ptr 20 input.length))
    (hmemInput : s.mem 20 = some input)
    (hpackedMem : s.mem = scanIntSuccessPackedMem input output pos)
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hsignAt : input[cursor]? = some sign)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (hcursorBound : cursor + 1 ≤ input.length)
    (hdigitAt : input[cursor + 1]? = some digit)
    (hdigit : 48 ≤ digit.toNat ∧ digit.toNat ≤ 57)
    (houtput : 4 ≤ output.length)
    (houtLocal : s.locals 2 = some (.ptr 21 0))
    (hppLocal : s.locals 0 = some (.ptr 20 0))
    (hro : s.ro = false) :
    ∃ loopFinal value finalSat,
      ExS Gen.prog s
        (.seq scanIntStartFailureCheck
          (.seq (.set 4 (.const (.int IntTy.i32 1)))
            (.seq scanIntSignBranch
              (.seq scanIntEndFailureCheck scanIntSuccessRest))))
        (.ret (some (.int IntTy.u8 1)))
        ⟨loopFinal.locals,
          (fun b =>
            if b = 20 then some
              (encodeLE 8 (ptrPack (.ptr 20
                (cursor + 1 + (scanDigits ((input.drop (cursor + 1)).map UInt8.toNat) 0).1))) ++ input)
            else if b = 21 then some
              (encodeLE 4 (IntTy.wrap IntTy.i32
                (if sign.toNat = 45 then
                  -((scanDigits ((input.drop (cursor + 1)).map UInt8.toNat) 0).2 : Int)
                 else (scanDigits ((input.drop (cursor + 1)).map UInt8.toNat) 0).2)) ++ output.drop 4)
            else none),
          loopFinal.ro⟩ ∧
      loopFinal = scanLoopFrameAt
        ⟨Locals.upd
          (Locals.upd s.locals 4 (.int IntTy.i32
            (if sign.toNat = 45 then IntTy.wrap IntTy.i32 (-1) else 1)))
          3 (.ptr 20 (cursor + 1)), s.mem, s.ro⟩
        (cursor + 1 + (scanDigits ((input.drop (cursor + 1)).map UInt8.toNat) 0).1)
        value finalSat ∧
      (value, finalSat) = scanCLoopFold
        ((input.drop (cursor + 1)).map UInt8.toNat) (0, false) := by
  have hcursor : cursor < input.length :=
    (List.getElem?_eq_some_iff.mp hsignAt).choose
  have hge : EvE Gen.prog s
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin (EvE.var hcursorLocal) (EvE.var hendLocal)
    simp [evalBin, isPtr, boolVal]
    exact hcursor
  have hfalse : truthy (boolVal false) = .ok false := by
    simp [truthy, boolVal, IntTy.i32]
  have hstartCheck : ExS Gen.prog s scanIntStartFailureCheck .normal s := by
    apply ExS.ite hge hfalse
    exact ExS.skip
  let initialized : State :=
    ⟨Locals.upd s.locals 4 (.int IntTy.i32 1), s.mem, s.ro⟩
  have hsetSign : ExS Gen.prog s (.set 4 (.const (.int IntTy.i32 1)))
      .normal initialized := ExS.set (EvE.const _)
  have hendInit : initialized.locals 1 = some (.ptr 20 input.length) := by
    simpa [initialized] using hendLocal
  have hmemInit : initialized.mem 20 = some input := by
    simpa [initialized] using hmemInput
  have hpackedInit : initialized.mem = scanIntSuccessPackedMem input output pos := by
    simpa [initialized] using hpackedMem
  have hcursorInit : initialized.locals 3 = some (.ptr 20 cursor) := by
    simpa [initialized] using hcursorLocal
  have houtInit : initialized.locals 2 = some (.ptr 21 0) := by
    simpa [initialized] using houtLocal
  have hppInit : initialized.locals 0 = some (.ptr 20 0) := by
    simpa [initialized] using hppLocal
  have hsignInit : initialized.locals 4 = some (.int IntTy.i32 1) := by
    simp [initialized, Locals.upd]
  have hsuccess := scanInt_success_after_sign_packed_exs initialized
    input output pos cursor sign digit hmemInit hpackedInit hendInit
    hcursorInit hsignInit houtInit hppInit houtput hcursorBound hsignAt hsign
    hdigitAt hdigit (by simpa [initialized] using hro)
  obtain ⟨loopFinal, value, finalSat, hsuccess', hfinal, hfold⟩ := hsuccess
  have hfinal' : loopFinal = scanLoopFrameAt
      ⟨Locals.upd
        (Locals.upd s.locals 4 (.int IntTy.i32
          (if sign.toNat = 45 then IntTy.wrap IntTy.i32 (-1) else 1)))
        3 (.ptr 20 (cursor + 1)), s.mem, s.ro⟩
      (cursor + 1 + (scanDigits ((input.drop (cursor + 1)).map UInt8.toNat) 0).1)
      value finalSat := by
    simpa [initialized, Locals.upd_upd] using hfinal
  refine ⟨loopFinal, value, finalSat, ?_, hfinal', hfold⟩
  exact ExS.seq hstartCheck (ExS.seq hsetSign hsuccess')

/-- After a lone sign reaches the input endpoint, the scanner's short-circuit
    failure check returns false without writing the output and keeps the
    advanced cursor. -/
theorem scanInt_signOnly_end_failure_at (s : State) (bytes : Block)
    (cursor : Nat) (byte : UInt8)
    (hcursorLocal : s.locals 3 = some (.ptr 20 cursor))
    (hsignLocal : s.locals 4 = some (.int IntTy.i32 1))
    (hendLocal : s.locals 1 = some (.ptr 20 (cursor + 1)))
    (hmem : s.mem 20 = some bytes) (hbound : cursor + 1 ≤ bytes.length)
    (hbyteAt : bytes[cursor]? = some byte)
    (hsign : byte.toNat = 43 ∨ byte.toNat = 45) :
    ∃ finalState,
      ExS Gen.prog s scanIntSignBranch .normal finalState ∧
      ExS Gen.prog finalState scanIntEndFailureCheck
        (.ret (some (.int IntTy.u8 0))) finalState ∧
      ExS Gen.prog s (.seq scanIntSignBranch scanIntEndFailureCheck)
        (.ret (some (.int IntTy.u8 0))) finalState ∧
      finalState.locals 3 = some (.ptr 20 (cursor + 1)) ∧
      finalState.locals 1 = s.locals 1 ∧ finalState.mem = s.mem := by
  obtain ⟨afterSign, hsignBranch, hcursorAfter, _hsignAfter,
      _hlocal0After, _hlocal2After, hendAfter, hmemAfter,
      _hlocalsAfter, _hroAfter⟩ :=
    scanInt_signBranch_at s bytes cursor byte
    hcursorLocal hsignLocal hmem hbound hbyteAt hsign
  have hcursorEval : EvE Gen.prog afterSign (.var 3)
      (.ptr 20 (cursor + 1)) := EvE.var hcursorAfter
  have hendLocalAfter : afterSign.locals 1 = some (.ptr 20 (cursor + 1)) := by
    simpa [hendAfter] using hendLocal
  have hendEval : EvE Gen.prog afterSign (.var 1) (.ptr 20 (cursor + 1)) :=
    EvE.var hendLocalAfter
  have hge : EvE Gen.prog afterSign
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal true) := by
    apply EvE.bin hcursorEval hendEval
    simp [evalBin, isPtr, boolVal]
  have htrue : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hfailGuard : EvE Gen.prog afterSign scanIntFailGuard (boolVal true) := by
    change EvE Gen.prog afterSign (.lor _ _) (boolVal true)
    exact EvE.lor_true (b := .un .lnot IntTy.i32
      (.call 7 [.load (.int IntTy.i8) (.var 3)])) hge htrue
  have hfalseValue : EvE Gen.prog afterSign scanIntFalseValue
      (.int IntTy.u8 0) := by
    unfold scanIntFalseValue
    exact EvE.cond (bc := false) (EvE.const (.int IntTy.i32 0))
      (by simp [truthy]) (EvE.const (.int IntTy.u8 0))
  have hcheck : ExS Gen.prog afterSign scanIntEndFailureCheck
      (.ret (some (.int IntTy.u8 0))) afterSign := by
    apply ExS.ite (bc := true) hfailGuard htrue
    simpa [scanIntEndFailureCheck] using ExS.ret hfalseValue
  have hbody := ExS.seq hsignBranch hcheck
  exact ⟨afterSign, hsignBranch, hcheck,
    by simpa [scanIntEndFailureCheck] using hbody,
    hcursorAfter, hendAfter, hmemAfter⟩


/-- End-to-end scanner failure for a lone sign after any leading space/tab
    prefix. The helper commits the caller's pointer past whitespace; the sign
    branch advances only its local cursor, then the endpoint check fails. -/
theorem scanInt_loneSign_fails (spaces output : Block) (sign : UInt8)
    (hspaces : spaces.takeWhile (fun byte => scanSpace byte.toNat) = spaces)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (houtput : 4 ≤ output.length)
    (hbound : 8 + (spaces.length + 1) < 4294967296) :
    ∃ K, (∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + (spaces.length + 1)), .ptr 21 0]
        (scanIntSuccessPackedMem (spaces ++ [sign]) output 0) =
      .ok (some (.int IntTy.u8 0),
        scanIntSuccessPackedMem (spaces ++ [sign]) output spaces.length)) ∧
      scanInt ((spaces ++ [sign]).map UInt8.toNat) 0 =
        (false, 0, spaces.length) := by
  let input := spaces ++ [sign]
  let spaceCount := spaces.length
  let cursor := 8 + spaceCount
  let endpoint := 8 + input.length
  let packed := skipSpacePackedBlock input spaceCount
  let initialMem := scanIntSuccessPackedMem input output 0
  let initial : State :=
    ⟨frameLocals [0, 1, 2]
      [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0], initialMem, false⟩
  have hsignNotSpace : scanSpace sign.toNat = false := by
    rcases hsign with hp | hm
    · simp [scanSpace, hp]
    · simp [scanSpace, hm]
  have htakePrefix : input.takeWhile (fun byte => scanSpace byte.toNat) = spaces := by
    have hall : ∀ xs : Block,
        xs.takeWhile (fun byte => scanSpace byte.toNat) = xs →
        (xs ++ [sign]).takeWhile (fun byte => scanSpace byte.toNat) = xs := by
      intro xs
      induction xs with
      | nil => intro _; simp [hsignNotSpace]
      | cons head tail ih =>
        intro hxs
        simp only [List.takeWhile_cons] at hxs
        by_cases hhead : scanSpace head.toNat
        · have htail : tail.takeWhile (fun byte => scanSpace byte.toNat) = tail := by
            simpa [hhead] using hxs
          simp [List.takeWhile_cons, hhead, ih htail]
        · simp [List.takeWhile_cons, hhead] at hxs
    exact hall spaces hspaces
  have hinputLen : input.length = spaces.length + 1 := by simp [input]
  have hendpoint : endpoint = cursor + 1 := by
    dsimp [endpoint, cursor, spaceCount]
    rw [hinputLen]
    omega
  have hbyteAt : input[spaceCount]? = some sign := by
    dsimp [input, spaceCount]
    rw [List.getElem?_append_right
      (l₁ := spaces) (l₂ := [sign]) (i := spaces.length) (by simp)]
    simp
  have hpackedLen : packed.length = 8 + input.length := by
    simp [packed, skipSpacePackedBlock, encodeLE_length]
  have hpackedByte : packed[cursor]? = some sign := by
    have hlen : (encodeLE 8 (ptrPack (.ptr 20 cursor))).length = 8 :=
      encodeLE_length 8 _
    change (skipSpacePackedBlock input spaceCount)[cursor]? = some sign
    unfold skipSpacePackedBlock
    rw [List.getElem?_append_right
      (l₁ := encodeLE 8 (ptrPack (.ptr 20 cursor))) (l₂ := input)
      (i := cursor) (by rw [hlen]; dsimp [cursor, spaceCount]; omega)]
    rw [hlen]
    have hindex : cursor - 8 = spaceCount := by dsimp [cursor, spaceCount]; omega
    rw [hindex]
    exact hbyteAt
  obtain ⟨skipFinal, hskipBody, _hskipCursor, hskipMem⟩ :=
    skipSpacePacked_body_with_output input output 0 (by simp [input])
      (by simpa [input, hinputLen] using hbound)
  have hskipMem' : skipFinal.mem =
      scanIntSuccessPackedMem input output spaceCount := by
    rw [hskipMem]
    funext b
    by_cases hb20 : b = 20
    · subst b
      simp [scanIntSuccessPackedMem, skipSpacePackedBlock, input, spaceCount,
        htakePrefix]
    · by_cases hb21 : b = 21
      · subst b
        simp [scanIntSuccessPackedMem]
      · simp [scanIntSuccessPackedMem, hb20, hb21]
  have hvar0 : EvE Gen.prog initial (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hvar1 : EvE Gen.prog initial (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hargs : EvArgs Gen.prog initial [.var 0, .var 1]
      [.ptr 20 0, .ptr 20 endpoint] := EvArgs.cons hvar0 (EvArgs.cons hvar1 EvArgs.nil)
  have hskipCall : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal { initial with mem := skipFinal.mem } := by
    have hcall := ExS.call (p := Gen.prog) (s := initial)
      (f := Gen.fid_tobj_skip_space) (args := [.var 0, .var 1])
      (vs := [.ptr 20 0, .ptr 20 endpoint]) (fn := Gen.tobj_skip_space)
      (o := .normal) (s' := skipFinal) hargs (by rfl) (by rfl) hskipBody
      (Or.inl rfl)
    simpa [initial, hskipMem'] using hcall
  let afterSkip : State :=
    { initial with mem := scanIntSuccessPackedMem input output spaceCount }
  have hskipCall' : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal afterSkip := by simpa [afterSkip, hskipMem'] using hskipCall
  have hloadPtr : load afterSkip.mem .ptr (.ptr 20 0) = .ok (.ptr 20 cursor) := by
    dsimp [afterSkip, cursor, spaceCount]
    exact skipSpacePacked_load input spaces.length (by omega)
  have hvar0' : EvE Gen.prog afterSkip (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [afterSkip, initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hloadPtrLocal : EvE Gen.prog afterSkip (.load .ptr (.var 0)) (.ptr 20 cursor) :=
    EvE.load hvar0' hloadPtr
  let afterCursor : State :=
    { afterSkip with locals := Locals.upd afterSkip.locals 3 (.ptr 20 cursor) }
  have hsetCursor : ExS Gen.prog afterSkip (.set 3 (.load .ptr (.var 0)))
      .normal afterCursor := by simpa [afterCursor] using ExS.set hloadPtrLocal
  have hcursorLocal : afterCursor.locals 3 = some (.ptr 20 cursor) := by
    simp [afterCursor, Locals.upd]
  have hmemCursor : afterCursor.mem 20 = some packed := by
    simp [afterCursor, afterSkip, packed, scanIntSuccessPackedMem,
      skipSpacePackedBlock]
  have hcursorBound : cursor + 1 ≤ packed.length := by
    rw [hpackedLen]
    dsimp [cursor, spaceCount]
    rw [hinputLen]
    omega
  have hsetSignInit : ExS Gen.prog afterCursor
      (.set 4 (.const (.int IntTy.i32 1))) .normal
      { afterCursor with locals := Locals.upd afterCursor.locals 4 (.int IntTy.i32 1) } :=
    ExS.set (EvE.const (.int IntTy.i32 1))
  let afterSignInit : State :=
    { afterCursor with locals := Locals.upd afterCursor.locals 4 (.int IntTy.i32 1) }
  have hsetSignInit' : ExS Gen.prog afterCursor
      (.set 4 (.const (.int IntTy.i32 1))) .normal afterSignInit := by
    simpa [afterSignInit] using hsetSignInit
  have hbranchLocal3 : afterSignInit.locals 3 = some (.ptr 20 cursor) := by
    simp [afterSignInit, Locals.upd, hcursorLocal]
  have hbranchLocal4 : afterSignInit.locals 4 = some (.int IntTy.i32 1) := by
    simp [afterSignInit, Locals.upd]
  have hbranchEnd : afterSignInit.locals 1 = some (.ptr 20 (cursor + 1)) := by
    have hlocal : afterCursor.locals 1 = some (.ptr 20 endpoint) := by
      simp [afterCursor, afterSkip, initial, frameLocals,
        List.idxOf?, List.findIdx?, List.findIdx?.go]
    simpa [afterSignInit, afterCursor, hendpoint] using hlocal
  obtain ⟨afterFailure, hsignBranch, hfailureCheck, _hsignFailure,
      _hcursorFailure, _hendFailure, hmemFailure⟩ := scanInt_signOnly_end_failure_at
    afterSignInit packed cursor sign hbranchLocal3 hbranchLocal4 hbranchEnd
    hmemCursor hcursorBound hpackedByte hsign
  have hfirstGuard : EvE Gen.prog afterCursor
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    have hend : EvE Gen.prog afterCursor (.var 1) (.ptr 20 endpoint) := by
      apply EvE.var
      simp [afterCursor, afterSkip, initial, frameLocals, Locals.upd,
        List.idxOf?, List.findIdx?, List.findIdx?.go]
    apply EvE.bin (EvE.var hcursorLocal) hend
    simp [evalBin, isPtr, boolVal]
    dsimp [cursor, endpoint]
    omega
  have hfalse : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hfirstCheck : ExS Gen.prog afterCursor
      (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.ret (some scanIntFalseValue)) .skip) .normal afterCursor := by
    apply ExS.ite hfirstGuard hfalse
    exact ExS.skip
  have htail : ExS Gen.prog afterSignInit
      (.seq scanIntSignBranch (.seq scanIntEndFailureCheck scanIntSuccessRest))
      (.ret (some (.int IntTy.u8 0))) afterFailure := by
    exact ExS.seq hsignBranch (ExS.seq_ret hfailureCheck)
  have hbody : ExS Gen.prog initial Gen.tobj_scan_int.body
      (.ret (some (.int IntTy.u8 0))) afterFailure := by
    apply ExS.seq hskipCall'
    apply ExS.seq hsetCursor
    apply ExS.seq hfirstCheck
    exact ExS.seq hsetSignInit' htail
  obtain ⟨K, hcall⟩ := callFunc_of_ExS (p := Gen.prog)
    (f := Gen.fid_tobj_scan_int) (fn := Gen.tobj_scan_int)
    (args := [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0]) (m := initialMem)
    (v := some (.int IntTy.u8 0)) (s' := afterFailure)
    (hf := by rfl) (hlen := by simp [Gen.tobj_scan_int])
    (by simpa [initial, Gen.tobj_scan_int] using hbody)
  refine ⟨K, (fun n hn => ?_), ?_⟩
  have hresult := hcall n hn
  have hfinalMem : afterFailure.mem =
      scanIntSuccessPackedMem input output spaceCount := by
    rw [hmemFailure]
  rw [hfinalMem] at hresult
  · simpa [initialMem, input, endpoint, scanIntSuccessPackedMem,
      skipSpacePackedBlock, spaceCount, htakePrefix] using hresult
  · have hspacesNat : (spaces.map UInt8.toNat).takeWhile scanSpace =
        spaces.map UInt8.toNat := by
      rw [scanSpace_takeWhile_map]
      exact congrArg (List.map UInt8.toNat) hspaces
    rcases hsign with hplus | hminus
    · have hmodel := scanInt_lone_sign_failure
        (spaces.map UInt8.toNat) 43 hspacesNat (Or.inl rfl)
      simpa [input, hplus] using hmodel
    · have hmodel := scanInt_lone_sign_failure
        (spaces.map UInt8.toNat) 45 hspacesNat (Or.inr rfl)
      simpa [input, hminus] using hmodel

/-- End-to-end failure for an optional `+` or `-` followed by a non-digit,
    with any trailing suffix. The local cursor consumes the sign, but a failed
    scan commits only the whitespace prefix and preserves the output block. -/
theorem scanInt_signDelimiter_fails (spaces output tail : Block)
    (sign byte : UInt8)
    (hspaces : spaces.takeWhile (fun c => scanSpace c.toNat) = spaces)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat)
    (houtput : 4 ≤ output.length)
    (hbound : 8 + (spaces.length + 2 + tail.length) < 4294967296) :
    ∃ K, (∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + (spaces.length + 2 + tail.length)), .ptr 21 0]
        (scanIntSuccessPackedMem (spaces ++ ([sign, byte] ++ tail)) output 0) =
      .ok (some (.int IntTy.u8 0),
        scanIntSuccessPackedMem (spaces ++ ([sign, byte] ++ tail)) output spaces.length)) ∧
      scanInt ((spaces ++ ([sign, byte] ++ tail)).map UInt8.toNat) 0 =
        (false, 0, spaces.length) := by
  let input := spaces ++ ([sign, byte] ++ tail)
  let spaceCount := spaces.length
  let cursor := 8 + spaceCount
  let endpoint := 8 + input.length
  let packed := skipSpacePackedBlock input spaceCount
  let initialMem := scanIntSuccessPackedMem input output 0
  let initial : State :=
    ⟨frameLocals [0, 1, 2]
      [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0], initialMem, false⟩
  have hsignNotSpace : scanSpace sign.toNat = false := by
    rcases hsign with hp | hm
    · simp [scanSpace, hp]
    · simp [scanSpace, hm]
  have htakePrefix : input.takeWhile (fun c => scanSpace c.toNat) = spaces := by
    apply takeWhile_append_stops (fun c : UInt8 => scanSpace c.toNat)
      spaces ([sign, byte] ++ tail) hspaces
    intro b hb
    simp at hb
    subst b
    exact hsignNotSpace
  have hinputLen : input.length = spaces.length + 2 + tail.length := by
    simp [input, Nat.add_assoc]
    omega
  have hendpoint : endpoint = cursor + 2 + tail.length := by
    dsimp [endpoint, cursor, spaceCount]
    rw [hinputLen]
    omega
  have hbyteAtSign : input[spaceCount]? = some sign := by
    dsimp [input, spaceCount]
    rw [List.getElem?_append_right
      (l₁ := spaces) (l₂ := sign :: byte :: tail)
      (i := spaces.length) (by simp)]
    simp
  have hbyteAtDelimiter : input[spaceCount + 1]? = some byte := by
    dsimp [input, spaceCount]
    rw [List.getElem?_append_right
      (l₁ := spaces) (l₂ := sign :: byte :: tail)
      (i := spaces.length + 1) (by simp)]
    simp
  have hspaceLen : (input.takeWhile (fun c => scanSpace c.toNat)).length =
      spaceCount := by
    rw [htakePrefix]
  have hendpointLen : endpoint = 8 + (spaces.length + 2 + tail.length) := by
    dsimp [endpoint]
    rw [hinputLen]
  have hpackedLen : packed.length = 8 + input.length := by
    simp [packed, skipSpacePackedBlock, encodeLE_length]
  have hpackedData (i : Nat) : packed[cursor + i]? = input[spaceCount + i]? := by
    have hlen : (encodeLE 8 (ptrPack (.ptr 20 cursor))).length = 8 :=
      encodeLE_length 8 _
    change (encodeLE 8 (ptrPack (.ptr 20 cursor)) ++ input)[cursor + i]? =
      input[spaceCount + i]?
    rw [List.getElem?_append_right
      (l₁ := encodeLE 8 (ptrPack (.ptr 20 cursor))) (l₂ := input)
      (i := cursor + i) (by rw [hlen]; dsimp [cursor, spaceCount]; omega)]
    rw [hlen]
    have hindex : cursor + i - 8 = spaceCount + i := by
      dsimp [cursor, spaceCount]
      omega
    rw [hindex]
  have hpackedSign : packed[cursor]? = some sign := by
    simpa [hbyteAtSign] using hpackedData 0
  have hpackedDelimiter : packed[cursor + 1]? = some byte := by
    simpa [hbyteAtDelimiter] using hpackedData 1
  have hinputBound : 8 + input.length < 4294967296 := by
    rw [hinputLen]
    exact hbound
  obtain ⟨skipFinal, hskipBody, _hskipCursor, hskipMem⟩ :=
    skipSpacePacked_body_with_output input output 0 (by simp [input])
      hinputBound
  have hskipMem' : skipFinal.mem =
      scanIntSuccessPackedMem input output spaceCount := by
    rw [hskipMem]
    funext b
    by_cases hb20 : b = 20
    · subst b
      simp [scanIntSuccessPackedMem, skipSpacePackedBlock, hspaceLen,
        spaceCount]
    · by_cases hb21 : b = 21
      · subst b
        simp [scanIntSuccessPackedMem]
      · simp [scanIntSuccessPackedMem, hb20, hb21]
  have hvar0 : EvE Gen.prog initial (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hvar1 : EvE Gen.prog initial (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hargs : EvArgs Gen.prog initial [.var 0, .var 1]
      [.ptr 20 0, .ptr 20 endpoint] := EvArgs.cons hvar0 (EvArgs.cons hvar1 EvArgs.nil)
  have hskipCall : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal { initial with mem := skipFinal.mem } := by
    have hcall := ExS.call (p := Gen.prog) (s := initial)
      (f := Gen.fid_tobj_skip_space) (args := [.var 0, .var 1])
      (vs := [.ptr 20 0, .ptr 20 endpoint]) (fn := Gen.tobj_skip_space)
      (o := .normal) (s' := skipFinal) hargs (by rfl) (by rfl) hskipBody
      (Or.inl rfl)
    simpa [initial, hskipMem'] using hcall
  let afterSkip : State :=
    { initial with mem := scanIntSuccessPackedMem input output spaceCount }
  have hskipCall' : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal afterSkip := by simpa [afterSkip, hskipMem'] using hskipCall
  have hloadPtr : load afterSkip.mem .ptr (.ptr 20 0) = .ok (.ptr 20 cursor) := by
    dsimp [afterSkip, cursor, spaceCount]
    exact skipSpacePacked_load input spaces.length (by omega)
  have hvar0' : EvE Gen.prog afterSkip (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [afterSkip, initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hloadPtrLocal : EvE Gen.prog afterSkip (.load .ptr (.var 0)) (.ptr 20 cursor) :=
    EvE.load hvar0' hloadPtr
  let afterCursor : State :=
    { afterSkip with locals := Locals.upd afterSkip.locals 3 (.ptr 20 cursor) }
  have hsetCursor : ExS Gen.prog afterSkip (.set 3 (.load .ptr (.var 0)))
      .normal afterCursor := by simpa [afterCursor] using ExS.set hloadPtrLocal
  have hcursorLocal : afterCursor.locals 3 = some (.ptr 20 cursor) := by
    simp [afterCursor, Locals.upd]
  have hmemCursor : afterCursor.mem 20 = some packed := by
    simp [afterCursor, afterSkip, packed, scanIntSuccessPackedMem,
      skipSpacePackedBlock]
  have hfirstGuard : EvE Gen.prog afterCursor
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    have hend : EvE Gen.prog afterCursor (.var 1) (.ptr 20 endpoint) := by
      apply EvE.var
      simp [afterCursor, afterSkip, initial, frameLocals, Locals.upd,
        List.idxOf?, List.findIdx?, List.findIdx?.go]
    apply EvE.bin (EvE.var hcursorLocal) hend
    simp [evalBin, isPtr, boolVal]
    rw [hendpoint]
    omega
  have hfalse : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hfirstCheck : ExS Gen.prog afterCursor
      (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.ret (some scanIntFalseValue)) .skip) .normal afterCursor := by
    apply ExS.ite hfirstGuard hfalse
    exact ExS.skip
  let afterSignInit : State :=
    { afterCursor with locals := Locals.upd afterCursor.locals 4 (.int IntTy.i32 1) }
  have hsetSign : ExS Gen.prog afterCursor
      (.set 4 (.const (.int IntTy.i32 1))) .normal afterSignInit :=
    ExS.set (EvE.const _)
  have hbranchLocal3 : afterSignInit.locals 3 = some (.ptr 20 cursor) := by
    simp [afterSignInit, Locals.upd, hcursorLocal]
  have hbranchLocal4 : afterSignInit.locals 4 = some (.int IntTy.i32 1) := by
    simp [afterSignInit, Locals.upd]
  have hbranchEnd : afterSignInit.locals 1 = some (.ptr 20 endpoint) := by
    simp [afterSignInit, afterCursor, afterSkip, initial, frameLocals,
      Locals.upd, List.idxOf?, List.findIdx?, List.findIdx?.go]
  obtain ⟨afterSign, hsignBranch, hcursorAfter, _hsignAfter,
      _hlocal0After, _hlocal2After, _hendAfter, hmemAfter,
      _hlocalsAfter, _hroAfter⟩ :=
    scanInt_signBranch_at afterSignInit packed cursor sign
    hbranchLocal3 hbranchLocal4 hmemCursor
    (by rw [hpackedLen]; dsimp [cursor, spaceCount]; rw [hinputLen]; omega)
    hpackedSign hsign
  have hdigitCursor : afterSign.locals 3 = some (.ptr 20 (cursor + 1)) := hcursorAfter
  have hmemSign : afterSign.mem 20 = some packed := by
    rw [hmemAfter]
    change afterSignInit.mem 20 = some packed
    change afterCursor.mem 20 = some packed
    exact hmemCursor
  have hdigitCall := scanLoop_digit_call_false_at afterSign packed (cursor + 1) byte
      hdigitCursor hmemSign
      (by rw [hpackedLen, hinputLen]; dsimp [cursor, spaceCount]; omega)
      hpackedDelimiter hnondigit
  have hnotDigit : EvE Gen.prog afterSign
      (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (boolVal true) := by
    apply EvE.un hdigitCall.1
    simp [evalUn, truthy, boolVal]
  have hcursorEval : EvE Gen.prog afterSign (.var 3) (.ptr 20 (cursor + 1)) :=
    EvE.var hdigitCursor
  have hendEval : EvE Gen.prog afterSign (.var 1) (.ptr 20 endpoint) := by
    have hendSignLocal : afterSign.locals 1 = some (.ptr 20 endpoint) := by
      rw [_hendAfter]
      exact hbranchEnd
    apply EvE.var
    exact hendSignLocal
  have hge : EvE Gen.prog afterSign
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin hcursorEval hendEval
    simp [evalBin, isPtr, boolVal]
    rw [hendpoint]
    omega
  have hfailGuard : EvE Gen.prog afterSign scanIntFailGuard (boolVal true) := by
    change EvE Gen.prog afterSign (.lor _ _) (boolVal true)
    exact EvE.lor_false hge hfalse hnotDigit (by simp [truthy, boolVal])
  have hfalseValue : EvE Gen.prog afterSign scanIntFalseValue
      (.int IntTy.u8 0) := by
    unfold scanIntFalseValue
    exact EvE.cond (bc := false) (EvE.const (.int IntTy.i32 0))
      (by simp [truthy]) (EvE.const (.int IntTy.u8 0))
  have hfailureCheck : ExS Gen.prog afterSign scanIntEndFailureCheck
      (.ret (some (.int IntTy.u8 0))) afterSign := by
    apply ExS.ite (bc := true) hfailGuard (by simp [truthy, boolVal])
    simpa [scanIntEndFailureCheck] using ExS.ret hfalseValue
  have hbody : ExS Gen.prog initial Gen.tobj_scan_int.body
      (.ret (some (.int IntTy.u8 0))) afterSign := by
    apply ExS.seq hskipCall'
    apply ExS.seq hsetCursor
    apply ExS.seq hfirstCheck
    apply ExS.seq hsetSign
    exact ExS.seq hsignBranch (ExS.seq_ret hfailureCheck)
  obtain ⟨K, hcall⟩ := callFunc_of_ExS (p := Gen.prog)
    (f := Gen.fid_tobj_scan_int) (fn := Gen.tobj_scan_int)
    (args := [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0]) (m := initialMem)
    (v := some (.int IntTy.u8 0)) (s' := afterSign)
    (hf := by rfl) (hlen := by simp [Gen.tobj_scan_int])
    (by simpa [initial, Gen.tobj_scan_int] using hbody)
  refine ⟨K, (fun n hn => ?_), ?_⟩
  have hresult := hcall n hn
  have hfinalMem : afterSign.mem =
      scanIntSuccessPackedMem input output spaceCount := by
    rw [hmemAfter]
  rw [hfinalMem] at hresult
  · simpa [initialMem, input, endpoint, hinputLen,
      scanIntSuccessPackedMem, skipSpacePackedBlock, spaceCount,
      htakePrefix] using (by rw [hendpointLen] at hresult; exact hresult)
  · have hnondigitModel : scanDigit byte.toNat = false := by
      simp [scanDigit]
      omega
    have hspacesNat : (spaces.map UInt8.toNat).takeWhile scanSpace =
        spaces.map UInt8.toNat := by
      rw [scanSpace_takeWhile_map]
      exact congrArg (List.map UInt8.toNat) hspaces
    have hmodel := scanInt_sign_nondigit_failure
      (spaces.map UInt8.toNat) sign.toNat byte.toNat (tail.map UInt8.toNat)
      hspacesNat hsign
      hnondigitModel
    simpa [input, List.map_append, List.append_assoc] using hmodel

/-- A first nonspace non-sign nondigit returns false, commits only the
    whitespace cursor, and preserves a valid separate output block. -/
theorem scanInt_delimiter_fails (bytes output : Block) (byte : UInt8)
    (hbyteAt : bytes[(bytes.takeWhile (fun b => scanSpace b.toNat)).length]? = some byte)
    (hnotSign : byte.toNat ≠ 43 ∧ byte.toNat ≠ 45)
    (hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat)
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K, ∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output 0) =
      .ok (some (.int IntTy.u8 0),
        scanIntSuccessPackedMem bytes output ((bytes.takeWhile
          (fun byte => scanSpace byte.toNat)).length)) := by
  let spaceCount := (bytes.takeWhile (fun byte => scanSpace byte.toNat)).length
  let cursor := 8 + spaceCount
  let endpoint := 8 + bytes.length
  let packed := skipSpacePackedBlock bytes spaceCount
  let initialMem := scanIntSuccessPackedMem bytes output 0
  let initial : State :=
    ⟨frameLocals [0, 1, 2] [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0], initialMem, false⟩
  have hspaceBound : spaceCount ≤ bytes.length := by
    dsimp [spaceCount]
    exact (List.takeWhile_prefix _).length_le
  have hcursor : cursor < endpoint := by
    dsimp [cursor, endpoint]
    have hbyteIdx := (List.getElem?_eq_some_iff.mp hbyteAt).choose
    omega
  have hpackedLen : packed.length = 8 + bytes.length := by
    simp [packed, skipSpacePackedBlock, spaceCount, encodeLE_length]
  have hboundCursor : cursor < 4294967296 := by dsimp [cursor]; omega
  have hpackedByte : packed[cursor]? = some byte := by
    have hlen : (encodeLE 8 (ptrPack (.ptr 20 cursor))).length = 8 :=
      encodeLE_length 8 _
    have hget := List.getElem?_append_right
      (l₁ := encodeLE 8 (ptrPack (.ptr 20 cursor))) (l₂ := bytes)
      (i := cursor) (by dsimp [cursor]; rw [hlen]; omega)
    have hindex : cursor - (encodeLE 8 (ptrPack (.ptr 20 cursor))).length =
        spaceCount := by
      rw [hlen]
      dsimp [cursor, spaceCount]
      omega
    change (skipSpacePackedBlock bytes spaceCount)[cursor]? = some byte
    unfold skipSpacePackedBlock
    rw [List.getElem?_append_right
      (l₁ := encodeLE 8 (ptrPack (.ptr 20 cursor))) (l₂ := bytes)
      (i := cursor) (by rw [hlen]; dsimp [cursor]; omega)]
    rw [hlen]
    have hindex' : cursor - 8 = spaceCount := by
      dsimp [cursor]
      omega
    rw [hindex']
    exact hbyteAt
  obtain ⟨skipFinal, hskipBody, _hskipCursor, hskipMem⟩ :=
    skipSpacePacked_body_with_output bytes output 0 (by omega) hbound
  have hskipMem' : skipFinal.mem =
      scanIntSuccessPackedMem bytes output spaceCount := by
    rw [hskipMem]
    funext b
    by_cases hb20 : b = 20
    · subst b
      simp [scanIntSuccessPackedMem, skipSpacePackedBlock, cursor, spaceCount]
    · by_cases hb21 : b = 21
      · subst b
        simp [scanIntSuccessPackedMem]
      · simp [scanIntSuccessPackedMem, hb20, hb21]
  have hvar0 : EvE Gen.prog initial (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hvar1 : EvE Gen.prog initial (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hargs : EvArgs Gen.prog initial [.var 0, .var 1]
      [.ptr 20 0, .ptr 20 endpoint] := EvArgs.cons hvar0 (EvArgs.cons hvar1 EvArgs.nil)
  have hskipCall : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal { initial with mem := skipFinal.mem } := by
    have hcall := ExS.call (p := Gen.prog) (s := initial)
      (f := Gen.fid_tobj_skip_space) (args := [.var 0, .var 1])
      (vs := [.ptr 20 0, .ptr 20 endpoint]) (fn := Gen.tobj_skip_space)
      (o := .normal) (s' := skipFinal) hargs (by rfl) (by rfl) hskipBody
      (Or.inl rfl)
    simpa [initial, hskipMem'] using hcall
  let afterSkip : State :=
    { initial with mem := scanIntSuccessPackedMem bytes output spaceCount }
  have hskipCall' : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1]) .normal afterSkip := by
    simpa [afterSkip, hskipMem'] using hskipCall
  have hloadPtr : load afterSkip.mem .ptr (.ptr 20 0) = .ok (.ptr 20 cursor) := by
    dsimp [afterSkip, cursor, spaceCount]
    exact skipSpacePacked_load bytes _ (by omega)
  have hvar0' : EvE Gen.prog afterSkip (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [afterSkip, initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hloadPtrLocal : EvE Gen.prog afterSkip (.load .ptr (.var 0)) (.ptr 20 cursor) :=
    EvE.load hvar0' hloadPtr
  let afterCursor : State :=
    { afterSkip with locals := Locals.upd afterSkip.locals 3 (.ptr 20 cursor) }
  have hsetCursor : ExS Gen.prog afterSkip (.set 3 (.load .ptr (.var 0)))
      .normal afterCursor := by
    simpa [afterCursor] using ExS.set hloadPtrLocal
  have hcursorLocal : afterCursor.locals 3 = some (.ptr 20 cursor) := by
    simp [afterCursor, Locals.upd]
  have hmemCursor : afterCursor.mem 20 = some packed := by
    simp [afterCursor, afterSkip, packed, scanIntSuccessPackedMem,
      skipSpacePackedBlock]
  have hfalse : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hsignGuardEval := scanInt_signGuard_any_at afterCursor packed cursor byte
    hcursorLocal hmemCursor (by rw [hpackedLen]; exact hcursor) hpackedByte
  have hsignGuard : EvE Gen.prog afterCursor
      (.lor
        (.bin .eq (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 43)))
        (.bin .eq (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 45)))) (boolVal false) :=
    by simpa [scanIntSignGuard, scanIntPlusExpr, scanIntMinusExpr,
      hnotSign.1, hnotSign.2, boolVal] using hsignGuardEval.1
  have hgeFalse : EvE Gen.prog afterCursor
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    have hend : EvE Gen.prog afterCursor (.var 1) (.ptr 20 endpoint) := by
      apply EvE.var
      simp [afterCursor, afterSkip, initial, frameLocals, Locals.upd,
        List.idxOf?, List.findIdx?, List.findIdx?.go]
    apply EvE.bin (EvE.var hcursorLocal) hend
    simp [evalBin, isPtr, boolVal]
    exact hcursor
  let falseValue : Expr := .cond (.const (.int IntTy.i32 0))
    (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))
  have hfalseValue : EvE Gen.prog afterCursor falseValue (.int IntTy.u8 0) := by
    unfold falseValue
    exact EvE.cond (bc := false) (EvE.const (.int IntTy.i32 0))
      (by simp [truthy]) (EvE.const (.int IntTy.u8 0))
  have hfirstCheck : ExS Gen.prog afterCursor
      (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.ret (some falseValue)) .skip) .normal afterCursor :=
    ExS.ite hgeFalse hfalse ExS.skip
  let afterSignInit : State :=
    { afterCursor with locals := Locals.upd afterCursor.locals 4 (.int IntTy.i32 1) }
  have hsetSign : ExS Gen.prog afterCursor
      (.set 4 (.const (.int IntTy.i32 1))) .normal afterSignInit := by
    exact ExS.set (EvE.const _)
  have hcursorSign : afterSignInit.locals 3 = some (.ptr 20 cursor) := by
    simp [afterSignInit, Locals.upd, hcursorLocal]
  have hsignGuardEvalSign := scanInt_signGuard_any_at afterSignInit packed cursor byte
    hcursorSign (by simpa [afterSignInit, afterCursor] using hmemCursor)
    (by rw [hpackedLen]; exact hcursor) hpackedByte
  have hsignGuardSign : EvE Gen.prog afterSignInit
      (.lor
        (.bin .eq (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 43)))
        (.bin .eq (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 45)))) (boolVal false) :=
    by simpa [scanIntSignGuard, scanIntPlusExpr, scanIntMinusExpr,
      hnotSign.1, hnotSign.2, boolVal] using hsignGuardEvalSign.1
  have hsignCheck : ExS Gen.prog afterSignInit
      (.ite
        (.lor
          (.bin .eq (some IntTy.i32)
            (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
            (.const (.int IntTy.i32 43)))
          (.bin .eq (some IntTy.i32)
            (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
            (.const (.int IntTy.i32 45))))
        (.seq
          (.ite (.bin .eq (some IntTy.i32)
            (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
            (.const (.int IntTy.i32 45)))
            (.set 4 (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))) .skip)
          (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
        .skip) .normal afterSignInit :=
    ExS.ite hsignGuardSign hfalse ExS.skip
  let afterSign : State := afterSignInit
  have hdigitCall := scanLoop_digit_call_false_at afterSign packed cursor
      byte (by simp [afterSign, afterSignInit, Locals.upd, hcursorLocal])
      (by simpa [afterSign, afterSignInit, hmemCursor] using hmemCursor)
      (by rw [hpackedLen]; exact hcursor) hpackedByte hnondigit
  have hnotDigit : EvE Gen.prog afterSign
      (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (boolVal true) := by
    apply EvE.un hdigitCall.1
    simp [evalUn, truthy, boolVal]
  have hcursorAfterSign : EvE Gen.prog afterSign (.var 3) (.ptr 20 cursor) := by
    apply EvE.var
    simp [afterSign, afterSignInit, afterCursor, Locals.upd, hcursorLocal]
  have hendAfterSign : EvE Gen.prog afterSign (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [afterSign, afterSignInit, afterCursor, afterSkip, initial,
      frameLocals, Locals.upd, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hgeAfterSign : EvE Gen.prog afterSign
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin hcursorAfterSign hendAfterSign
    simp [evalBin, isPtr, boolVal]
    exact hcursor
  have hfailGuard : EvE Gen.prog afterSign
      (.lor (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)])))
      (boolVal true) :=
    EvE.lor_false hgeAfterSign hfalse hnotDigit (by simp [truthy, boolVal])
  have hfalseValueSign : EvE Gen.prog afterSign falseValue (.int IntTy.u8 0) := by
    unfold falseValue
    exact EvE.cond (bc := false) (EvE.const (.int IntTy.i32 0))
      (by simp [truthy]) (EvE.const (.int IntTy.u8 0))
  have hfailCheck : ExS Gen.prog afterSign
      (.ite
        (.lor (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
          (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)])))
        (.ret (some falseValue)) .skip)
      (.ret (some (.int IntTy.u8 0))) afterSign := by
    exact ExS.ite (bc := true) hfailGuard (by simp [truthy, boolVal])
      (ExS.ret hfalseValueSign)
  have hbody : ExS Gen.prog initial Gen.tobj_scan_int.body
      (.ret (some (.int IntTy.u8 0))) afterSign := by
    apply ExS.seq hskipCall'
    apply ExS.seq hsetCursor
    apply ExS.seq hfirstCheck
    apply ExS.seq hsetSign
    apply ExS.seq hsignCheck
    exact ExS.seq_ret hfailCheck
  obtain ⟨K, hcall⟩ := callFunc_of_ExS (p := Gen.prog)
    (f := Gen.fid_tobj_scan_int) (fn := Gen.tobj_scan_int)
    (args := [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0]) (m := initialMem)
    (v := some (.int IntTy.u8 0)) (s' := afterSign)
    (hf := by rfl) (hlen := by rfl)
    (by simpa [initial, Gen.tobj_scan_int] using hbody)
  refine ⟨K, fun n hn => ?_⟩
  have hresult := hcall n hn
  simpa [initialMem, scanIntSuccessPackedMem, skipSpacePackedBlock,
    spaceCount, afterSign, afterSignInit, afterCursor, afterSkip, initial,
    endpoint] using hresult

/-- The generated-C and pure-model results agree for a first nonspace
    non-sign nondigit, including arbitrary bytes after the delimiter. -/
theorem scanInt_delimiter_refines_model (bytes output : Block) (byte : UInt8)
    (hbyteAt : bytes[(bytes.takeWhile (fun b => scanSpace b.toNat)).length]? = some byte)
    (hnotSign : byte.toNat ≠ 43 ∧ byte.toNat ≠ 45)
    (hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat)
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K, (∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output 0) =
      .ok (some (.int IntTy.u8 0),
        scanIntSuccessPackedMem bytes output ((bytes.takeWhile
          (fun b => scanSpace b.toNat)).length))) ∧
      scanInt (bytes.map UInt8.toNat) 0 =
        (false, 0, ((bytes.map UInt8.toNat).takeWhile scanSpace).length) := by
  obtain ⟨K, hcall⟩ := scanInt_delimiter_fails bytes output byte hbyteAt
    hnotSign hnondigit houtput hbound
  have hprefixMap := scanSpace_takeWhile_map bytes
  have hbyteAtModel :
      (bytes.map UInt8.toNat)[((bytes.map UInt8.toNat).takeWhile scanSpace).length]? =
        some byte.toNat := by
    have hmapped := congrArg (Option.map UInt8.toNat) hbyteAt
    rw [hprefixMap]
    simpa [List.getElem?_map, Option.map_some] using hmapped
  have hnondigitModel : scanDigit byte.toNat = false := by
    simp [scanDigit]
    omega
  have hmodel := scanInt_delimiter_failure_at (bytes.map UInt8.toNat)
    byte.toNat hbyteAtModel hnotSign hnondigitModel
  refine ⟨K, hcall, ?_⟩
  simpa using hmodel

/-- Any pure scanner failure has one of the four concrete byte shapes used by
    the translated failure proofs. -/
theorem scanInt_pure_failure_has_shape (bytes : Block)
    {value : Int} {cursor : Nat}
    (h : scanInt (bytes.map UInt8.toNat) 0 =
      (false, value, cursor)) :
    scanIntFailureShape bytes := by
  have hcontract := scanInt_failure_contract (bytes.map UInt8.toNat) 0 h
  have hvalue : value = 0 := hcontract.1
  have hcursor : cursor = ((bytes.map UInt8.toNat).takeWhile scanSpace).length := by
    simpa using hcontract.2
  subst value
  subst cursor
  have hNormalized : scanInt (bytes.map UInt8.toNat) 0 =
      (false, 0, ((bytes.map UInt8.toNat).takeWhile scanSpace).length) := by
    simpa using h
  let spaces := bytes.takeWhile (fun b => scanSpace b.toNat)
  let suffix := bytes.drop spaces.length
  have hspaces : spaces.takeWhile (fun b => scanSpace b.toNat) = spaces := by
    exact takeWhile_idempotent _ bytes
  have hbytes : bytes = spaces ++ suffix := by
    dsimp [spaces, suffix]
    exact (takeWhile_append_drop_eq _ bytes).symm
  have htakeMap : ((bytes.map UInt8.toNat).takeWhile scanSpace) =
      spaces.map UInt8.toNat := by
    rw [scanSpace_takeWhile_map]
  have hmodelCursor : ((bytes.map UInt8.toNat).takeWhile scanSpace).length =
      spaces.length := by
    rw [htakeMap]
    simp
  cases hsuffix : suffix with
  | nil =>
    rw [hsuffix] at hbytes
    left
    rw [hbytes]
    simpa using hspaces
  | cons head tail =>
    rw [hsuffix] at hbytes
    have hbound : spaces.length < bytes.length := by
      rw [hbytes]
      simp
    obtain ⟨first, hfirst, hnotSpace⟩ :=
      takeWhile_boundary_exists (fun b : UInt8 => scanSpace b.toNat)
        bytes (by simpa [spaces] using hbound)
    have hfirst' : (bytes.drop spaces.length).head? = some first := by
      simpa [spaces] using hfirst
    have hfirstEq : first = head := by
      have hdrop : bytes.drop spaces.length = head :: tail := by
        rw [hbytes]
        simp
      rw [hdrop] at hfirst'
      simpa using hfirst'.symm
    subst first
    have hheadNotSpace : scanSpace head.toNat = false := hnotSpace
    have hstop : ∀ b, (head :: tail).head? = some b →
        scanSpace b.toNat = false := by
      intro b hb
      simp at hb
      subst b
      exact hheadNotSpace
    have htakeRaw : (spaces ++ head :: tail).takeWhile
        (fun b => scanSpace b.toNat) = spaces :=
      takeWhile_append_stops (fun b : UInt8 => scanSpace b.toNat)
        spaces (head :: tail) hspaces hstop
    have htakeMapRaw : ((spaces ++ head :: tail).map UInt8.toNat).takeWhile
        scanSpace = spaces.map UInt8.toNat := by
      rw [scanSpace_takeWhile_map]
      exact congrArg (List.map UInt8.toNat) htakeRaw
    have hresult : scanInt ((spaces ++ head :: tail).map UInt8.toNat) 0 =
        (false, 0, spaces.length) := by
      have h' := hNormalized
      rw [hmodelCursor] at h'
      rw [hbytes] at h'
      exact h'
    by_cases hplus : head.toNat = 43
    · cases tail with
      | nil =>
        right
        left
        exact ⟨spaces, head, hspaces, Or.inl hplus, by simpa [hsuffix] using hbytes⟩
      | cons next rest =>
        by_cases hdigit : scanDigit next.toNat = true
        · have hscanTrue : (scanInt ((spaces ++ head :: next :: rest).map
              UInt8.toNat) 0).1 = true := by
            have htakeMapRaw' := htakeMapRaw
            simp only [List.map_append] at htakeMapRaw'
            simp only [List.map_cons, hplus] at htakeMapRaw'
            simp [scanInt, htakeMapRaw', hplus, hdigit, scanIntDigits,
              List.map_append]
          have hbad := congrArg Prod.fst hresult
          rw [hscanTrue] at hbad
          cases hbad
        · right
          right
          left
          refine ⟨spaces, head, next, rest, hspaces, Or.inl hplus, ?_, ?_⟩
          · simp [scanDigit] at hdigit ⊢
            omega

          · simpa [hsuffix] using hbytes
    · by_cases hminus : head.toNat = 45
      · cases tail with
        | nil =>
          right
          left
          exact ⟨spaces, head, hspaces, Or.inr hminus, by simpa [hsuffix] using hbytes⟩
        | cons next rest =>
          by_cases hdigit : scanDigit next.toNat = true
          · have hscanTrue : (scanInt ((spaces ++ head :: next :: rest).map
                UInt8.toNat) 0).1 = true := by
              have htakeMapRaw' := htakeMapRaw
              simp only [List.map_append] at htakeMapRaw'
              simp only [List.map_cons, hminus] at htakeMapRaw'
              simp [scanInt, htakeMapRaw', hminus, hdigit, scanIntDigits,
                List.map_append]
            have hbad := congrArg Prod.fst hresult
            rw [hscanTrue] at hbad
            cases hbad
          · right
            right
            left
            refine ⟨spaces, head, next, rest, hspaces, Or.inr hminus, ?_, ?_⟩
            · simp [scanDigit] at hdigit ⊢
              omega
            · simpa [hsuffix] using hbytes
      · by_cases hdigit : scanDigit head.toNat = true
        · have hscanTrue : (scanInt ((spaces ++ head :: tail).map
              UInt8.toNat) 0).1 = true := by
            have htakeMapRaw' := htakeMapRaw
            simp only [List.map_append] at htakeMapRaw'
            simp only [List.map_cons] at htakeMapRaw'
            simp [scanInt, htakeMapRaw', hplus, hminus, hdigit,
              scanIntDigits, List.map_append]
          have hbad := congrArg Prod.fst hresult
          rw [hscanTrue] at hbad
          cases hbad
        · right
          right
          right
          refine ⟨spaces, head, tail, hspaces, ?_, hheadNotSpace, ?_, ?_, ?_⟩
          · simpa [hsuffix] using hbytes
          · exact hplus
          · exact hminus
          · simp [scanDigit] at hdigit ⊢
            omega

/-- Failure-shape classification also holds when scanning begins at a
    nonzero pure-model offset; classify the remaining input slice. -/
theorem scanInt_pure_failure_has_shape_at (bytes : Block) (pos : Nat)
    {value : Int} {cursor : Nat}
    (hpure : scanInt (bytes.map UInt8.toNat) pos = (false, value, cursor)) :
    scanIntFailureShape (bytes.drop pos) := by
  have hflag := congrArg Prod.fst hpure
  rw [scanInt_drop_flag] at hflag
  have htailFlag : (scanInt ((bytes.drop pos).map UInt8.toNat) 0).1 = false := by
    simpa [List.map_drop] using hflag
  cases hresult : scanInt ((bytes.drop pos).map UInt8.toNat) 0 with
  | mk flag rest =>
    cases rest with
    | mk tailValue tailCursor =>
      have hflag' : flag = false := by
        rw [hresult] at htailFlag
        exact htailFlag
      subst flag
      have htail : scanInt ((bytes.drop pos).map UInt8.toNat) 0 =
          (false, tailValue, tailCursor) := by
        simpa using hresult
      exact scanInt_pure_failure_has_shape (bytes.drop pos) htail

/-- Compose the four scanner failure branches into one result theorem for an
    input whose failure shape has been classified. The theorem returns both
    the translated `callFunc` result and the pure scanner tuple. -/
theorem scanInt_failure_shapes_refine (bytes output : Block)
    (hshape : scanIntFailureShape bytes)
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K, (∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output 0) =
      .ok (some (.int IntTy.u8 0), scanIntSuccessPackedMem bytes output
        ((bytes.takeWhile (fun b => scanSpace b.toNat)).length))) ∧
      scanInt (bytes.map UInt8.toNat) 0 =
        (false, 0, ((bytes.map UInt8.toNat).takeWhile scanSpace).length) := by
  rcases hshape with hwhite | ⟨spaces, sign, hspaces, hsign, hbytes⟩ |
      ⟨spaces, sign, byte, tail, hspaces, hsign, hnondigit, hbytes⟩ |
      ⟨spaces, byte, tail, hspaces, hbytes, hnotSpace,
        hnotPlus, hnotMinus, hnondigit⟩
  · obtain ⟨K, hcall, hmodel⟩ :=
      scanInt_whitespaceOnly_fails bytes output 0 (by omega) hwhite houtput hbound
    refine ⟨K, ?_, ?_⟩
    · intro n hn
      have hresult := hcall n hn
      simpa [hwhite] using hresult
    · have hmodelTake : (bytes.map UInt8.toNat).takeWhile scanSpace =
          bytes.map UInt8.toNat := by
        rw [scanSpace_takeWhile_map]
        exact congrArg (List.map UInt8.toNat) hwhite
      have hmodelLen := congrArg List.length hmodelTake
      simpa [hmodelLen] using hmodel
  · subst bytes
    have hbound' : 8 + (spaces.length + 1) < 4294967296 := by
      simpa using hbound
    obtain ⟨K, hcall, hmodel⟩ := scanInt_loneSign_fails
      spaces output sign hspaces hsign houtput hbound'
    have hsignNotSpace : scanSpace sign.toNat = false := by
      rcases hsign with hp | hm
      · simp [scanSpace, hp]
      · simp [scanSpace, hm]
    have htake : (spaces ++ [sign]).takeWhile
        (fun b => scanSpace b.toNat) = spaces :=
      takeWhile_append_stops (fun b : UInt8 => scanSpace b.toNat)
        spaces [sign] hspaces (by intro b hb; simp at hb; subst b; exact hsignNotSpace)
    have hmodelTake : ((spaces ++ [sign]).map UInt8.toNat).takeWhile scanSpace =
        spaces.map UInt8.toNat := by
      rw [scanSpace_takeWhile_map]
      simp [htake]
    have hmodelLen :
        (((spaces ++ [sign]).map UInt8.toNat).takeWhile scanSpace).length =
          spaces.length := by
      rw [hmodelTake]
      simp
    refine ⟨K, ?_, ?_⟩
    · intro n hn
      have hresult := hcall n hn
      simpa [List.length_append, htake] using hresult
    · rw [hmodelLen]
      exact hmodel
  · subst bytes
    have hinputLen : (spaces ++ ([sign, byte] ++ tail)).length =
        spaces.length + 2 + tail.length := by
      simp [List.length_append, Nat.add_assoc]
      omega
    have hbound' : 8 + (spaces.length + 2 + tail.length) < 4294967296 := by
      rw [← hinputLen]
      exact hbound
    obtain ⟨K, hcall, hmodel⟩ := scanInt_signDelimiter_fails
      spaces output tail sign byte hspaces hsign hnondigit houtput hbound'
    have hsignNotSpace : scanSpace sign.toNat = false := by
      rcases hsign with hp | hm
      · simp [scanSpace, hp]
      · simp [scanSpace, hm]
    have htake : (spaces ++ sign :: byte :: tail).takeWhile
        (fun b => scanSpace b.toNat) = spaces :=
      takeWhile_append_stops (fun b : UInt8 => scanSpace b.toNat)
        spaces (sign :: byte :: tail) hspaces
        (by intro b hb; simp at hb; subst b; exact hsignNotSpace)
    have hmodelTake :
        ((spaces ++ ([sign, byte] ++ tail)).map UInt8.toNat).takeWhile scanSpace =
          spaces.map UInt8.toNat := by
      rw [scanSpace_takeWhile_map]
      exact congrArg (List.map UInt8.toNat) htake
    have hmodelLen :
        (((spaces ++ ([sign, byte] ++ tail)).map UInt8.toNat).takeWhile
          scanSpace).length = spaces.length := by
      rw [hmodelTake]
      simp
    have htakeInput : (spaces ++ ([sign, byte] ++ tail)).takeWhile
        (fun b => scanSpace b.toNat) = spaces := by
      simpa [List.append_assoc] using htake
    refine ⟨K, ?_, ?_⟩
    · intro n hn
      have hresult := hcall n hn
      rw [hinputLen, htakeInput]
      exact hresult
    · rw [hmodelLen]
      exact hmodel
  · subst bytes
    have htake : (spaces ++ byte :: tail).takeWhile
        (fun b => scanSpace b.toNat) = spaces := by
      apply takeWhile_append_stops (fun b : UInt8 => scanSpace b.toNat)
        spaces (byte :: tail) hspaces
      intro head hhead
      simp at hhead
      subst head
      exact hnotSpace
    have hbyteAt : (spaces ++ byte :: tail)[((spaces ++ byte :: tail).takeWhile
        (fun b => scanSpace b.toNat)).length]? = some byte := by
      rw [htake]
      simp
    exact scanInt_delimiter_refines_model (spaces ++ byte :: tail) output byte
      hbyteAt ⟨hnotPlus, hnotMinus⟩ hnondigit houtput (by simpa using hbound)

/-- Full failure refinement for every input whose pure scan fails: the pure
    failure result supplies its own exhaustive failure-shape classification. -/
theorem scanInt_failure_refines_model (bytes output : Block)
    (hpure : scanInt (bytes.map UInt8.toNat) 0 =
      (false, 0, ((bytes.map UInt8.toNat).takeWhile scanSpace).length))
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K, (∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output 0) =
      .ok (some (.int IntTy.u8 0), scanIntSuccessPackedMem bytes output
        ((bytes.takeWhile (fun b => scanSpace b.toNat)).length))) ∧
      scanInt (bytes.map UInt8.toNat) 0 =
        (false, 0, ((bytes.map UInt8.toNat).takeWhile scanSpace).length) := by
  have hshape := scanInt_pure_failure_has_shape bytes hpure
  exact scanInt_failure_shapes_refine bytes output hshape houtput hbound

/-- Failure refinement stated for any pure result with a false flag; the
    scanner failure contract supplies its zero value and whitespace cursor. -/
theorem scanInt_failure_refines_model_of_failure (bytes output : Block)
    {value : Int} {cursor : Nat}
    (hpure : scanInt (bytes.map UInt8.toNat) 0 = (false, value, cursor))
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K, (∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output 0) =
      .ok (some (.int IntTy.u8 0), scanIntSuccessPackedMem bytes output
        ((bytes.takeWhile (fun b => scanSpace b.toNat)).length))) ∧
      scanInt (bytes.map UInt8.toNat) 0 =
        (false, 0, ((bytes.map UInt8.toNat).takeWhile scanSpace).length) := by
  have hcontract := scanInt_failure_contract (bytes.map UInt8.toNat) 0 hpure
  have hvalue : value = 0 := hcontract.1
  have hcursor : cursor = ((bytes.map UInt8.toNat).takeWhile scanSpace).length := by
    simpa using hcontract.2
  subst value
  subst cursor
  have hpure' : scanInt (bytes.map UInt8.toNat) 0 =
      (false, 0, ((bytes.map UInt8.toNat).takeWhile scanSpace).length) := by
    simpa using hpure
  exact scanInt_failure_refines_model bytes output hpure' houtput hbound

theorem scanSpace_takeWhile_map' (bytes : Block) :
    (bytes.map UInt8.toNat).takeWhile scanSpace =
      (bytes.takeWhile (fun b => scanSpace b.toNat)).map UInt8.toNat := by
  induction bytes with
  | nil => rfl
  | cons head tail ih =>
    by_cases hspace : scanSpace head.toNat = true
    · simp [hspace, ih]
    · simp [hspace]

theorem scanInt_success_shape (bytes : Block) {value : Int} {cursor : Nat}
    (hpure : scanInt (bytes.map UInt8.toNat) 0 = (true, value, cursor)) :
    let sp := (bytes.takeWhile (fun b => scanSpace b.toNat)).length
    (∃ byte, bytes[sp]? = some byte ∧ (48 ≤ byte.toNat ∧ byte.toNat ≤ 57) ∧
        byte.toNat ≠ 43 ∧ byte.toNat ≠ 45) ∨
    (∃ sign digit, bytes[sp]? = some sign ∧ (sign.toNat = 43 ∨ sign.toNat = 45) ∧
        bytes[sp + 1]? = some digit ∧ (48 ≤ digit.toNat ∧ digit.toNat ≤ 57)) := by
  intro sp
  have hmap := scanSpace_takeWhile_map' bytes
  have hlen : ((bytes.map UInt8.toNat).takeWhile scanSpace).length = sp := by
    rw [hmap]; simp [sp]
  unfold scanInt at hpure
  simp only [List.drop_zero, hlen, ← List.map_drop] at hpure
  generalize hrest : bytes.drop sp = rest at hpure
  have hget : ∀ i, bytes[sp + i]? = rest[i]? := by
    intro i
    rw [← hrest]; simp [List.getElem?_drop]
  cases rest with
  | nil => simp [scanIntDigits] at hpure
  | cons b tl =>
    by_cases hs : b.toNat = 43 ∨ b.toNat = 45
    · cases tl with
      | nil => rcases hs with h | h <;> simp [scanIntDigits, h] at hpure
      | cons d tl' =>
        right
        refine ⟨b, d, ?_, hs, ?_, ?_⟩
        · simpa using hget 0
        · simpa using hget 1
        · refine Classical.byContradiction fun hc => ?_
          rcases hs with h | h <;> simp [scanIntDigits, h, scanDigit, hc] at hpure
    · left
      refine ⟨b, by simpa using hget 0, ?_, by omega, by omega⟩
      simp only [not_or] at hs
      have h43 : (b.toNat == 43) = false := by simp [hs.1]
      have h45 : (b.toNat == 45) = false := by simp [hs.2]
      refine Classical.byContradiction fun hc => ?_
      simp [scanIntDigits, h43, h45, scanDigit, hc] at hpure

/-- Unified `tobj_scan_int` refinement at offset zero: whatever the pure
    scanner returns, the translated function agrees on flag, cursor, value
    and memory.  Split on the pure flag. -/
theorem scanInt_refines_model (bytes output : Block)
    {flag : Bool} {value : Int} {cursor : Nat}
    (hpure : scanInt (bytes.map UInt8.toNat) 0 = (flag, value, cursor))
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    (flag = false → value = 0 ∧ cursor = (bytes.takeWhile
        (fun b => scanSpace b.toNat)).length ∧
      ∃ K, ∀ n, K ≤ n →
        callFunc Gen.prog n Gen.fid_tobj_scan_int
          [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
          (scanIntSuccessPackedMem bytes output 0) =
        .ok (some (.int IntTy.u8 0),
          scanIntSuccessPackedMem bytes output cursor)) ∧
    (flag = true → ∃ (K : Nat) (final : State),
      (∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output 0) =
          .ok (some (.int IntTy.u8 1), final.mem)) ∧
      final.mem 20 = some
        (encodeLE 8 (ptrPack (.ptr 20 (8 + cursor))) ++ bytes) ∧
      final.mem 21 = some
        (encodeLE 4 (IntTy.wrap IntTy.i32 value) ++ output.drop 4)) := by
  refine ⟨?_, ?_⟩
  · intro hflag
    subst flag
    have hcontract := scanInt_failure_contract (bytes.map UInt8.toNat) 0 hpure
    have hlen : ((bytes.map UInt8.toNat).takeWhile scanSpace).length =
        (bytes.takeWhile (fun b => scanSpace b.toNat)).length := by
      rw [scanSpace_takeWhile_map']; simp
    have hc : cursor = (bytes.takeWhile (fun b => scanSpace b.toNat)).length := by
      have := hcontract.2
      simp at this
      omega
    refine ⟨hcontract.1, hc, ?_⟩
    obtain ⟨K, hK, _⟩ := scanInt_failure_refines_model_of_failure bytes output
      hpure houtput hbound
    exact ⟨K, fun n hn => by rw [hc]; exact hK n hn⟩
  · intro hflag
    subst flag
    rcases scanInt_success_shape bytes hpure with
      ⟨byte, hat, hdig, hn43, hn45⟩ | ⟨sign, digit, hat, hsign, hat1, hdig⟩
    · obtain ⟨K, final, hcall, h20, h21, hspec⟩ :=
        scanInt_success_no_sign_after_whitespace_callFunc bytes output 0 byte
          hbound (Nat.zero_le _) houtput (by simpa using hat) hdig hn43 hn45
      simp only [Nat.zero_add, List.drop_zero] at hspec h20 h21
      rw [hpure] at hspec
      simp only [Prod.mk.injEq, true_and] at hspec
      obtain ⟨hv, hc⟩ := hspec
      subst hv hc
      exact ⟨K, final, hcall, by simpa [Nat.add_assoc] using h20, h21⟩
    · obtain ⟨K, final, hcall, h20, h21, hspec⟩ :=
        scanInt_success_sign_after_whitespace_callFunc bytes output 0 sign digit
          hbound (Nat.zero_le _) houtput (by simpa using hat) hsign
          (by simpa using hat1) hdig
      simp only [Nat.zero_add, List.drop_zero] at hspec h20 h21
      rw [hpure] at hspec
      simp only [Prod.mk.injEq, true_and] at hspec
      obtain ⟨hv, hc⟩ := hspec
      subst hv hc
      exact ⟨K, final, hcall, by simpa [Nat.add_assoc] using h20, h21⟩

/-! ### Scanner failure contracts from an arbitrary start offset -/

theorem scanInt_delimiter_fails_at (bytes output : Block) (pos : Nat) (byte : UInt8)
    (hpos : pos ≤ bytes.length)
    (hbyteAt : bytes[pos + ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length]? = some byte)
    (hnotSign : byte.toNat ≠ 43 ∧ byte.toNat ≠ 45)
    (hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat)
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K, ∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output pos) =
      .ok (some (.int IntTy.u8 0),
        scanIntSuccessPackedMem bytes output (pos + ((bytes.drop pos).takeWhile
          (fun byte => scanSpace byte.toNat)).length)) := by
  let spaceCount := pos + ((bytes.drop pos).takeWhile (fun byte => scanSpace byte.toNat)).length
  let cursor := 8 + spaceCount
  let endpoint := 8 + bytes.length
  let packed := skipSpacePackedBlock bytes spaceCount
  let initialMem := scanIntSuccessPackedMem bytes output pos
  let initial : State :=
    ⟨frameLocals [0, 1, 2] [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0], initialMem, false⟩
  have hspaceBound : spaceCount ≤ bytes.length := by
    dsimp [spaceCount]
    have := (List.takeWhile_prefix (fun b : UInt8 => scanSpace b.toNat) (l := bytes.drop pos)).length_le
    simp only [List.length_drop] at this
    omega
  have hcursor : cursor < endpoint := by
    dsimp [cursor, endpoint]
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hbyteAt
    omega
  have hpackedLen : packed.length = 8 + bytes.length := by
    simp [packed, skipSpacePackedBlock, spaceCount, encodeLE_length]
  have hboundCursor : cursor < 4294967296 := by dsimp [cursor]; omega
  have hpackedByte : packed[cursor]? = some byte := by
    have hlen : (encodeLE 8 (ptrPack (.ptr 20 cursor))).length = 8 :=
      encodeLE_length 8 _
    have hget := List.getElem?_append_right
      (l₁ := encodeLE 8 (ptrPack (.ptr 20 cursor))) (l₂ := bytes)
      (i := cursor) (by dsimp [cursor]; rw [hlen]; omega)
    have hindex : cursor - (encodeLE 8 (ptrPack (.ptr 20 cursor))).length =
        spaceCount := by
      rw [hlen]
      dsimp [cursor, spaceCount]
      omega
    change (skipSpacePackedBlock bytes spaceCount)[cursor]? = some byte
    unfold skipSpacePackedBlock
    rw [List.getElem?_append_right
      (l₁ := encodeLE 8 (ptrPack (.ptr 20 cursor))) (l₂ := bytes)
      (i := cursor) (by rw [hlen]; dsimp [cursor]; omega)]
    rw [hlen]
    have hindex' : cursor - 8 = spaceCount := by
      dsimp [cursor]
      omega
    rw [hindex']
    exact hbyteAt
  obtain ⟨skipFinal, hskipBody, _hskipCursor, hskipMem⟩ :=
    skipSpacePacked_body_with_output bytes output pos hpos hbound
  have hskipMem' : skipFinal.mem =
      scanIntSuccessPackedMem bytes output spaceCount := by
    rw [hskipMem]
    funext b
    by_cases hb20 : b = 20
    · subst b
      simp [scanIntSuccessPackedMem, skipSpacePackedBlock, cursor, spaceCount, Nat.add_assoc]
    · by_cases hb21 : b = 21
      · subst b
        simp [scanIntSuccessPackedMem]
      · simp [scanIntSuccessPackedMem, hb20, hb21]
  have hvar0 : EvE Gen.prog initial (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hvar1 : EvE Gen.prog initial (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hargs : EvArgs Gen.prog initial [.var 0, .var 1]
      [.ptr 20 0, .ptr 20 endpoint] := EvArgs.cons hvar0 (EvArgs.cons hvar1 EvArgs.nil)
  have hskipCall : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal { initial with mem := skipFinal.mem } := by
    have hcall := ExS.call (p := Gen.prog) (s := initial)
      (f := Gen.fid_tobj_skip_space) (args := [.var 0, .var 1])
      (vs := [.ptr 20 0, .ptr 20 endpoint]) (fn := Gen.tobj_skip_space)
      (o := .normal) (s' := skipFinal) hargs (by rfl) (by rfl) hskipBody
      (Or.inl rfl)
    simpa [initial, hskipMem'] using hcall
  let afterSkip : State :=
    { initial with mem := scanIntSuccessPackedMem bytes output spaceCount }
  have hskipCall' : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1]) .normal afterSkip := by
    simpa [afterSkip, hskipMem'] using hskipCall
  have hloadPtr : load afterSkip.mem .ptr (.ptr 20 0) = .ok (.ptr 20 cursor) := by
    dsimp [afterSkip, cursor, spaceCount]
    exact skipSpacePacked_load bytes _ (by omega)
  have hvar0' : EvE Gen.prog afterSkip (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [afterSkip, initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hloadPtrLocal : EvE Gen.prog afterSkip (.load .ptr (.var 0)) (.ptr 20 cursor) :=
    EvE.load hvar0' hloadPtr
  let afterCursor : State :=
    { afterSkip with locals := Locals.upd afterSkip.locals 3 (.ptr 20 cursor) }
  have hsetCursor : ExS Gen.prog afterSkip (.set 3 (.load .ptr (.var 0)))
      .normal afterCursor := by
    simpa [afterCursor] using ExS.set hloadPtrLocal
  have hcursorLocal : afterCursor.locals 3 = some (.ptr 20 cursor) := by
    simp [afterCursor, Locals.upd]
  have hmemCursor : afterCursor.mem 20 = some packed := by
    simp [afterCursor, afterSkip, packed, scanIntSuccessPackedMem,
      skipSpacePackedBlock]
  have hfalse : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hsignGuardEval := scanInt_signGuard_any_at afterCursor packed cursor byte
    hcursorLocal hmemCursor (by rw [hpackedLen]; exact hcursor) hpackedByte
  have hsignGuard : EvE Gen.prog afterCursor
      (.lor
        (.bin .eq (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 43)))
        (.bin .eq (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 45)))) (boolVal false) :=
    by simpa [scanIntSignGuard, scanIntPlusExpr, scanIntMinusExpr,
      hnotSign.1, hnotSign.2, boolVal] using hsignGuardEval.1
  have hgeFalse : EvE Gen.prog afterCursor
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    have hend : EvE Gen.prog afterCursor (.var 1) (.ptr 20 endpoint) := by
      apply EvE.var
      simp [afterCursor, afterSkip, initial, frameLocals, Locals.upd,
        List.idxOf?, List.findIdx?, List.findIdx?.go]
    apply EvE.bin (EvE.var hcursorLocal) hend
    simp [evalBin, isPtr, boolVal]
    exact hcursor
  let falseValue : Expr := .cond (.const (.int IntTy.i32 0))
    (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))
  have hfalseValue : EvE Gen.prog afterCursor falseValue (.int IntTy.u8 0) := by
    unfold falseValue
    exact EvE.cond (bc := false) (EvE.const (.int IntTy.i32 0))
      (by simp [truthy]) (EvE.const (.int IntTy.u8 0))
  have hfirstCheck : ExS Gen.prog afterCursor
      (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.ret (some falseValue)) .skip) .normal afterCursor :=
    ExS.ite hgeFalse hfalse ExS.skip
  let afterSignInit : State :=
    { afterCursor with locals := Locals.upd afterCursor.locals 4 (.int IntTy.i32 1) }
  have hsetSign : ExS Gen.prog afterCursor
      (.set 4 (.const (.int IntTy.i32 1))) .normal afterSignInit := by
    exact ExS.set (EvE.const _)
  have hcursorSign : afterSignInit.locals 3 = some (.ptr 20 cursor) := by
    simp [afterSignInit, Locals.upd, hcursorLocal]
  have hsignGuardEvalSign := scanInt_signGuard_any_at afterSignInit packed cursor byte
    hcursorSign (by simpa [afterSignInit, afterCursor] using hmemCursor)
    (by rw [hpackedLen]; exact hcursor) hpackedByte
  have hsignGuardSign : EvE Gen.prog afterSignInit
      (.lor
        (.bin .eq (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 43)))
        (.bin .eq (some IntTy.i32)
          (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
          (.const (.int IntTy.i32 45)))) (boolVal false) :=
    by simpa [scanIntSignGuard, scanIntPlusExpr, scanIntMinusExpr,
      hnotSign.1, hnotSign.2, boolVal] using hsignGuardEvalSign.1
  have hsignCheck : ExS Gen.prog afterSignInit
      (.ite
        (.lor
          (.bin .eq (some IntTy.i32)
            (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
            (.const (.int IntTy.i32 43)))
          (.bin .eq (some IntTy.i32)
            (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
            (.const (.int IntTy.i32 45))))
        (.seq
          (.ite (.bin .eq (some IntTy.i32)
            (.cast IntTy.i32 (.load (.int IntTy.i8) (.var 3)))
            (.const (.int IntTy.i32 45)))
            (.set 4 (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))) .skip)
          (.set 3 (.index (.var 3) (.const (.int IntTy.i64 1)) 1)))
        .skip) .normal afterSignInit :=
    ExS.ite hsignGuardSign hfalse ExS.skip
  let afterSign : State := afterSignInit
  have hdigitCall := scanLoop_digit_call_false_at afterSign packed cursor
      byte (by simp [afterSign, afterSignInit, Locals.upd, hcursorLocal])
      (by simpa [afterSign, afterSignInit, hmemCursor] using hmemCursor)
      (by rw [hpackedLen]; exact hcursor) hpackedByte hnondigit
  have hnotDigit : EvE Gen.prog afterSign
      (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (boolVal true) := by
    apply EvE.un hdigitCall.1
    simp [evalUn, truthy, boolVal]
  have hcursorAfterSign : EvE Gen.prog afterSign (.var 3) (.ptr 20 cursor) := by
    apply EvE.var
    simp [afterSign, afterSignInit, afterCursor, Locals.upd, hcursorLocal]
  have hendAfterSign : EvE Gen.prog afterSign (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [afterSign, afterSignInit, afterCursor, afterSkip, initial,
      frameLocals, Locals.upd, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hgeAfterSign : EvE Gen.prog afterSign
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin hcursorAfterSign hendAfterSign
    simp [evalBin, isPtr, boolVal]
    exact hcursor
  have hfailGuard : EvE Gen.prog afterSign
      (.lor (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)])))
      (boolVal true) :=
    EvE.lor_false hgeAfterSign hfalse hnotDigit (by simp [truthy, boolVal])
  have hfalseValueSign : EvE Gen.prog afterSign falseValue (.int IntTy.u8 0) := by
    unfold falseValue
    exact EvE.cond (bc := false) (EvE.const (.int IntTy.i32 0))
      (by simp [truthy]) (EvE.const (.int IntTy.u8 0))
  have hfailCheck : ExS Gen.prog afterSign
      (.ite
        (.lor (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
          (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)])))
        (.ret (some falseValue)) .skip)
      (.ret (some (.int IntTy.u8 0))) afterSign := by
    exact ExS.ite (bc := true) hfailGuard (by simp [truthy, boolVal])
      (ExS.ret hfalseValueSign)
  have hbody : ExS Gen.prog initial Gen.tobj_scan_int.body
      (.ret (some (.int IntTy.u8 0))) afterSign := by
    apply ExS.seq hskipCall'
    apply ExS.seq hsetCursor
    apply ExS.seq hfirstCheck
    apply ExS.seq hsetSign
    apply ExS.seq hsignCheck
    exact ExS.seq_ret hfailCheck
  obtain ⟨K, hcall⟩ := callFunc_of_ExS (p := Gen.prog)
    (f := Gen.fid_tobj_scan_int) (fn := Gen.tobj_scan_int)
    (args := [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0]) (m := initialMem)
    (v := some (.int IntTy.u8 0)) (s' := afterSign)
    (hf := by rfl) (hlen := by rfl)
    (by simpa [initial, Gen.tobj_scan_int] using hbody)
  refine ⟨K, fun n hn => ?_⟩
  have hresult := hcall n hn
  simpa [initialMem, scanIntSuccessPackedMem, skipSpacePackedBlock,
    spaceCount, afterSign, afterSignInit, afterCursor, afterSkip, initial,
    endpoint] using hresult

theorem scanInt_signDelimiter_fails_at (bytes output : Block) (pos : Nat) (sign byte : UInt8)
    (hpos : pos ≤ bytes.length)
    (hsignAt : bytes[pos + ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length]? = some sign)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (hbyteAt : bytes[pos + ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length + 1]? = some byte)
    (hnondigit : byte.toNat < 48 ∨ 57 < byte.toNat)
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K, ∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output pos) =
      .ok (some (.int IntTy.u8 0),
        scanIntSuccessPackedMem bytes output (pos + ((bytes.drop pos).takeWhile
          (fun byte => scanSpace byte.toNat)).length)) := by
  let spaceCount := pos + ((bytes.drop pos).takeWhile (fun byte => scanSpace byte.toNat)).length
  let cursor := 8 + spaceCount
  let endpoint := 8 + bytes.length
  let packed := skipSpacePackedBlock bytes spaceCount
  let initialMem := scanIntSuccessPackedMem bytes output pos
  let initial : State :=
    ⟨frameLocals [0, 1, 2] [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0], initialMem, false⟩
  have hlt2 : spaceCount + 1 < bytes.length := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hbyteAt
    omega
  have hpackedLen : packed.length = 8 + bytes.length := by
    simp [packed, skipSpacePackedBlock, encodeLE_length]
  have hpackedData (i : Nat) : packed[cursor + i]? = bytes[spaceCount + i]? := by
    have hlen : (encodeLE 8 (ptrPack (.ptr 20 cursor))).length = 8 :=
      encodeLE_length 8 _
    change (encodeLE 8 (ptrPack (.ptr 20 cursor)) ++ bytes)[cursor + i]? =
      bytes[spaceCount + i]?
    rw [List.getElem?_append_right
      (l₁ := encodeLE 8 (ptrPack (.ptr 20 cursor))) (l₂ := bytes)
      (i := cursor + i) (by rw [hlen]; dsimp [cursor, spaceCount]; omega)]
    rw [hlen]
    have hindex : cursor + i - 8 = spaceCount + i := by
      dsimp [cursor, spaceCount]
      omega
    rw [hindex]
  have hpackedSign : packed[cursor]? = some sign := by
    simpa using (hpackedData 0).trans hsignAt
  have hpackedDelimiter : packed[cursor + 1]? = some byte := by
    exact (hpackedData 1).trans (by simpa [spaceCount, Nat.add_assoc] using hbyteAt)
  obtain ⟨skipFinal, hskipBody, _hskipCursor, hskipMem⟩ :=
    skipSpacePacked_body_with_output bytes output pos hpos hbound
  have hskipMem' : skipFinal.mem =
      scanIntSuccessPackedMem bytes output spaceCount := by
    rw [hskipMem]
    funext b
    by_cases hb20 : b = 20
    · subst b
      simp [scanIntSuccessPackedMem, skipSpacePackedBlock, spaceCount, Nat.add_assoc]
    · by_cases hb21 : b = 21
      · subst b
        simp [scanIntSuccessPackedMem]
      · simp [scanIntSuccessPackedMem, hb20, hb21]
  have hvar0 : EvE Gen.prog initial (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hvar1 : EvE Gen.prog initial (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hargs : EvArgs Gen.prog initial [.var 0, .var 1]
      [.ptr 20 0, .ptr 20 endpoint] := EvArgs.cons hvar0 (EvArgs.cons hvar1 EvArgs.nil)
  have hskipCall : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal { initial with mem := skipFinal.mem } := by
    have hcall := ExS.call (p := Gen.prog) (s := initial)
      (f := Gen.fid_tobj_skip_space) (args := [.var 0, .var 1])
      (vs := [.ptr 20 0, .ptr 20 endpoint]) (fn := Gen.tobj_skip_space)
      (o := .normal) (s' := skipFinal) hargs (by rfl) (by rfl) hskipBody
      (Or.inl rfl)
    simpa [initial, hskipMem'] using hcall
  let afterSkip : State :=
    { initial with mem := scanIntSuccessPackedMem bytes output spaceCount }
  have hskipCall' : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal afterSkip := by simpa [afterSkip, hskipMem'] using hskipCall
  have hloadPtr : load afterSkip.mem .ptr (.ptr 20 0) = .ok (.ptr 20 cursor) := by
    dsimp [afterSkip, cursor, spaceCount]
    exact skipSpacePacked_load bytes spaceCount (by omega)
  have hvar0' : EvE Gen.prog afterSkip (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [afterSkip, initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hloadPtrLocal : EvE Gen.prog afterSkip (.load .ptr (.var 0)) (.ptr 20 cursor) :=
    EvE.load hvar0' hloadPtr
  let afterCursor : State :=
    { afterSkip with locals := Locals.upd afterSkip.locals 3 (.ptr 20 cursor) }
  have hsetCursor : ExS Gen.prog afterSkip (.set 3 (.load .ptr (.var 0)))
      .normal afterCursor := by simpa [afterCursor] using ExS.set hloadPtrLocal
  have hcursorLocal : afterCursor.locals 3 = some (.ptr 20 cursor) := by
    simp [afterCursor, Locals.upd]
  have hmemCursor : afterCursor.mem 20 = some packed := by
    simp [afterCursor, afterSkip, packed, scanIntSuccessPackedMem,
      skipSpacePackedBlock]
  have hfirstGuard : EvE Gen.prog afterCursor
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    have hend : EvE Gen.prog afterCursor (.var 1) (.ptr 20 endpoint) := by
      apply EvE.var
      simp [afterCursor, afterSkip, initial, frameLocals, Locals.upd,
        List.idxOf?, List.findIdx?, List.findIdx?.go]
    apply EvE.bin (EvE.var hcursorLocal) hend
    simp [evalBin, isPtr, boolVal]
    dsimp [cursor, endpoint] at *
    omega
  have hfalse : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hfirstCheck : ExS Gen.prog afterCursor
      (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.ret (some scanIntFalseValue)) .skip) .normal afterCursor := by
    apply ExS.ite hfirstGuard hfalse
    exact ExS.skip
  let afterSignInit : State :=
    { afterCursor with locals := Locals.upd afterCursor.locals 4 (.int IntTy.i32 1) }
  have hsetSign : ExS Gen.prog afterCursor
      (.set 4 (.const (.int IntTy.i32 1))) .normal afterSignInit :=
    ExS.set (EvE.const _)
  have hbranchLocal3 : afterSignInit.locals 3 = some (.ptr 20 cursor) := by
    simp [afterSignInit, Locals.upd, hcursorLocal]
  have hbranchLocal4 : afterSignInit.locals 4 = some (.int IntTy.i32 1) := by
    simp [afterSignInit, Locals.upd]
  have hbranchEnd : afterSignInit.locals 1 = some (.ptr 20 endpoint) := by
    simp [afterSignInit, afterCursor, afterSkip, initial, frameLocals,
      Locals.upd, List.idxOf?, List.findIdx?, List.findIdx?.go]
  obtain ⟨afterSign, hsignBranch, hcursorAfter, _hsignAfter,
      _hlocal0After, _hlocal2After, _hendAfter, hmemAfter,
      _hlocalsAfter, _hroAfter⟩ :=
    scanInt_signBranch_at afterSignInit packed cursor sign
    hbranchLocal3 hbranchLocal4 hmemCursor
    (by rw [hpackedLen]; dsimp [cursor, spaceCount] at *; omega)
    hpackedSign hsign
  have hdigitCursor : afterSign.locals 3 = some (.ptr 20 (cursor + 1)) := hcursorAfter
  have hmemSign : afterSign.mem 20 = some packed := by
    rw [hmemAfter]
    change afterSignInit.mem 20 = some packed
    change afterCursor.mem 20 = some packed
    exact hmemCursor
  have hdigitCall := scanLoop_digit_call_false_at afterSign packed (cursor + 1) byte
      hdigitCursor hmemSign
      (by rw [hpackedLen]; dsimp [cursor, spaceCount] at *; omega)
      hpackedDelimiter hnondigit
  have hnotDigit : EvE Gen.prog afterSign
      (.un .lnot IntTy.i32 (.call 7 [.load (.int IntTy.i8) (.var 3)]))
      (boolVal true) := by
    apply EvE.un hdigitCall.1
    simp [evalUn, truthy, boolVal]
  have hcursorEval : EvE Gen.prog afterSign (.var 3) (.ptr 20 (cursor + 1)) :=
    EvE.var hdigitCursor
  have hendEval : EvE Gen.prog afterSign (.var 1) (.ptr 20 endpoint) := by
    have hendSignLocal : afterSign.locals 1 = some (.ptr 20 endpoint) := by
      rw [_hendAfter]
      exact hbranchEnd
    apply EvE.var
    exact hendSignLocal
  have hge : EvE Gen.prog afterSign
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin hcursorEval hendEval
    simp [evalBin, isPtr, boolVal]
    dsimp [cursor, endpoint] at *
    omega
  have hfailGuard : EvE Gen.prog afterSign scanIntFailGuard (boolVal true) := by
    change EvE Gen.prog afterSign (.lor _ _) (boolVal true)
    exact EvE.lor_false hge hfalse hnotDigit (by simp [truthy, boolVal])
  have hfalseValue : EvE Gen.prog afterSign scanIntFalseValue
      (.int IntTy.u8 0) := by
    unfold scanIntFalseValue
    exact EvE.cond (bc := false) (EvE.const (.int IntTy.i32 0))
      (by simp [truthy]) (EvE.const (.int IntTy.u8 0))
  have hfailureCheck : ExS Gen.prog afterSign scanIntEndFailureCheck
      (.ret (some (.int IntTy.u8 0))) afterSign := by
    apply ExS.ite (bc := true) hfailGuard (by simp [truthy, boolVal])
    simpa [scanIntEndFailureCheck] using ExS.ret hfalseValue
  have hbody : ExS Gen.prog initial Gen.tobj_scan_int.body
      (.ret (some (.int IntTy.u8 0))) afterSign := by
    apply ExS.seq hskipCall'
    apply ExS.seq hsetCursor
    apply ExS.seq hfirstCheck
    apply ExS.seq hsetSign
    exact ExS.seq hsignBranch (ExS.seq_ret hfailureCheck)
  obtain ⟨K, hcall⟩ := callFunc_of_ExS (p := Gen.prog)
    (f := Gen.fid_tobj_scan_int) (fn := Gen.tobj_scan_int)
    (args := [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0]) (m := initialMem)
    (v := some (.int IntTy.u8 0)) (s' := afterSign)
    (hf := by rfl) (hlen := by simp [Gen.tobj_scan_int])
    (by simpa [initial, Gen.tobj_scan_int] using hbody)
  refine ⟨K, fun n hn => ?_⟩
  have hresult := hcall n hn
  have hfinalMem : afterSign.mem =
      scanIntSuccessPackedMem bytes output spaceCount := by
    rw [hmemAfter]
  rw [hfinalMem] at hresult
  simpa [initialMem, endpoint, scanIntSuccessPackedMem, skipSpacePackedBlock,
    spaceCount] using hresult


theorem scanInt_loneSign_fails_at (bytes output : Block) (pos : Nat) (sign : UInt8)
    (hpos : pos ≤ bytes.length)
    (hsignAt : bytes[pos + ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length]? = some sign)
    (hsign : sign.toNat = 43 ∨ sign.toNat = 45)
    (hlast : pos + ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length + 1 = bytes.length)
    (houtput : 4 ≤ output.length)
    (hbound : 8 + bytes.length < 4294967296) :
    ∃ K, ∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output pos) =
      .ok (some (.int IntTy.u8 0),
        scanIntSuccessPackedMem bytes output (pos + ((bytes.drop pos).takeWhile
          (fun byte => scanSpace byte.toNat)).length)) := by
  let input := bytes
  let spaceCount := pos + ((bytes.drop pos).takeWhile (fun byte => scanSpace byte.toNat)).length
  let cursor := 8 + spaceCount
  let endpoint := 8 + input.length
  let packed := skipSpacePackedBlock input spaceCount
  let initialMem := scanIntSuccessPackedMem input output pos
  let initial : State :=
    ⟨frameLocals [0, 1, 2]
      [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0], initialMem, false⟩
  have hendpoint : endpoint = cursor + 1 := by
    dsimp [endpoint, cursor, spaceCount, input] at *
    omega
  have hbyteAt : input[spaceCount]? = some sign := hsignAt
  have hpackedLen : packed.length = 8 + input.length := by
    simp [packed, skipSpacePackedBlock, encodeLE_length]
  have hpackedByte : packed[cursor]? = some sign := by
    have hlen : (encodeLE 8 (ptrPack (.ptr 20 cursor))).length = 8 :=
      encodeLE_length 8 _
    change (skipSpacePackedBlock input spaceCount)[cursor]? = some sign
    unfold skipSpacePackedBlock
    rw [List.getElem?_append_right
      (l₁ := encodeLE 8 (ptrPack (.ptr 20 cursor))) (l₂ := input)
      (i := cursor) (by rw [hlen]; dsimp [cursor, spaceCount]; omega)]
    rw [hlen]
    have hindex : cursor - 8 = spaceCount := by dsimp [cursor, spaceCount]; omega
    rw [hindex]
    exact hbyteAt
  obtain ⟨skipFinal, hskipBody, _hskipCursor, hskipMem⟩ :=
    skipSpacePacked_body_with_output input output pos hpos hbound
  have hskipMem' : skipFinal.mem =
      scanIntSuccessPackedMem input output spaceCount := by
    rw [hskipMem]
    funext b
    by_cases hb20 : b = 20
    · subst b
      simp [scanIntSuccessPackedMem, skipSpacePackedBlock, input, spaceCount,
        Nat.add_assoc]
    · by_cases hb21 : b = 21
      · subst b
        simp [scanIntSuccessPackedMem]
      · simp [scanIntSuccessPackedMem, hb20, hb21]
  have hvar0 : EvE Gen.prog initial (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hvar1 : EvE Gen.prog initial (.var 1) (.ptr 20 endpoint) := by
    apply EvE.var
    simp [initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hargs : EvArgs Gen.prog initial [.var 0, .var 1]
      [.ptr 20 0, .ptr 20 endpoint] := EvArgs.cons hvar0 (EvArgs.cons hvar1 EvArgs.nil)
  have hskipCall : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal { initial with mem := skipFinal.mem } := by
    have hcall := ExS.call (p := Gen.prog) (s := initial)
      (f := Gen.fid_tobj_skip_space) (args := [.var 0, .var 1])
      (vs := [.ptr 20 0, .ptr 20 endpoint]) (fn := Gen.tobj_skip_space)
      (o := .normal) (s' := skipFinal) hargs (by rfl) (by rfl) hskipBody
      (Or.inl rfl)
    simpa [initial, hskipMem'] using hcall
  let afterSkip : State :=
    { initial with mem := scanIntSuccessPackedMem input output spaceCount }
  have hskipCall' : ExS Gen.prog initial
      (.call none Gen.fid_tobj_skip_space [.var 0, .var 1])
      .normal afterSkip := by simpa [afterSkip, hskipMem'] using hskipCall
  have hloadPtr : load afterSkip.mem .ptr (.ptr 20 0) = .ok (.ptr 20 cursor) := by
    dsimp [afterSkip, cursor, spaceCount]
    exact skipSpacePacked_load input spaceCount (by omega)
  have hvar0' : EvE Gen.prog afterSkip (.var 0) (.ptr 20 0) := by
    apply EvE.var
    simp [afterSkip, initial, frameLocals, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hloadPtrLocal : EvE Gen.prog afterSkip (.load .ptr (.var 0)) (.ptr 20 cursor) :=
    EvE.load hvar0' hloadPtr
  let afterCursor : State :=
    { afterSkip with locals := Locals.upd afterSkip.locals 3 (.ptr 20 cursor) }
  have hsetCursor : ExS Gen.prog afterSkip (.set 3 (.load .ptr (.var 0)))
      .normal afterCursor := by simpa [afterCursor] using ExS.set hloadPtrLocal
  have hcursorLocal : afterCursor.locals 3 = some (.ptr 20 cursor) := by
    simp [afterCursor, Locals.upd]
  have hmemCursor : afterCursor.mem 20 = some packed := by
    simp [afterCursor, afterSkip, packed, scanIntSuccessPackedMem,
      skipSpacePackedBlock]
  have hcursorBound : cursor + 1 ≤ packed.length := by
    rw [hpackedLen]
    dsimp [cursor, spaceCount, input] at *
    omega
  have hsetSignInit : ExS Gen.prog afterCursor
      (.set 4 (.const (.int IntTy.i32 1))) .normal
      { afterCursor with locals := Locals.upd afterCursor.locals 4 (.int IntTy.i32 1) } :=
    ExS.set (EvE.const (.int IntTy.i32 1))
  let afterSignInit : State :=
    { afterCursor with locals := Locals.upd afterCursor.locals 4 (.int IntTy.i32 1) }
  have hsetSignInit' : ExS Gen.prog afterCursor
      (.set 4 (.const (.int IntTy.i32 1))) .normal afterSignInit := by
    simpa [afterSignInit] using hsetSignInit
  have hbranchLocal3 : afterSignInit.locals 3 = some (.ptr 20 cursor) := by
    simp [afterSignInit, Locals.upd, hcursorLocal]
  have hbranchLocal4 : afterSignInit.locals 4 = some (.int IntTy.i32 1) := by
    simp [afterSignInit, Locals.upd]
  have hbranchEnd : afterSignInit.locals 1 = some (.ptr 20 (cursor + 1)) := by
    have hlocal : afterCursor.locals 1 = some (.ptr 20 endpoint) := by
      simp [afterCursor, afterSkip, initial, frameLocals,
        List.idxOf?, List.findIdx?, List.findIdx?.go]
    simpa [afterSignInit, afterCursor, hendpoint] using hlocal
  obtain ⟨afterFailure, hsignBranch, hfailureCheck, _hsignFailure,
      _hcursorFailure, _hendFailure, hmemFailure⟩ := scanInt_signOnly_end_failure_at
    afterSignInit packed cursor sign hbranchLocal3 hbranchLocal4 hbranchEnd
    hmemCursor hcursorBound hpackedByte hsign
  have hfirstGuard : EvE Gen.prog afterCursor
      (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    have hend : EvE Gen.prog afterCursor (.var 1) (.ptr 20 endpoint) := by
      apply EvE.var
      simp [afterCursor, afterSkip, initial, frameLocals, Locals.upd,
        List.idxOf?, List.findIdx?, List.findIdx?.go]
    apply EvE.bin (EvE.var hcursorLocal) hend
    simp [evalBin, isPtr, boolVal]
    dsimp [cursor, endpoint]
    omega
  have hfalse : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hfirstCheck : ExS Gen.prog afterCursor
      (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.ret (some scanIntFalseValue)) .skip) .normal afterCursor := by
    apply ExS.ite hfirstGuard hfalse
    exact ExS.skip
  have htail : ExS Gen.prog afterSignInit
      (.seq scanIntSignBranch (.seq scanIntEndFailureCheck scanIntSuccessRest))
      (.ret (some (.int IntTy.u8 0))) afterFailure := by
    exact ExS.seq hsignBranch (ExS.seq_ret hfailureCheck)
  have hbody : ExS Gen.prog initial Gen.tobj_scan_int.body
      (.ret (some (.int IntTy.u8 0))) afterFailure := by
    apply ExS.seq hskipCall'
    apply ExS.seq hsetCursor
    apply ExS.seq hfirstCheck
    exact ExS.seq hsetSignInit' htail
  obtain ⟨K, hcall⟩ := callFunc_of_ExS (p := Gen.prog)
    (f := Gen.fid_tobj_scan_int) (fn := Gen.tobj_scan_int)
    (args := [.ptr 20 0, .ptr 20 endpoint, .ptr 21 0]) (m := initialMem)
    (v := some (.int IntTy.u8 0)) (s' := afterFailure)
    (hf := by rfl) (hlen := by simp [Gen.tobj_scan_int])
    (by simpa [initial, Gen.tobj_scan_int] using hbody)
  refine ⟨K, fun n hn => ?_⟩
  have hresult := hcall n hn
  have hfinalMem : afterFailure.mem =
      scanIntSuccessPackedMem input output spaceCount := by
    rw [hmemFailure]
  rw [hfinalMem] at hresult
  simpa [initialMem, input, endpoint, scanIntSuccessPackedMem,
    skipSpacePackedBlock, spaceCount] using hresult


theorem scanInt_failure_refines_model_at (bytes output : Block) (pos : Nat)
    {value : Int} {cursor : Nat} (hpos : pos ≤ bytes.length)
    (hpure : scanInt (bytes.map UInt8.toNat) pos = (false, value, cursor))
    (houtput : 4 ≤ output.length) (hbound : 8 + bytes.length < 4294967296) :
    value = 0 ∧ cursor = pos + ((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length ∧
    ∃ K, ∀ n, K ≤ n →
      callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output pos) =
      .ok (some (.int IntTy.u8 0), scanIntSuccessPackedMem bytes output cursor) := by
  have hc := scanInt_failure_contract (bytes.map UInt8.toNat) pos hpure
  have hmap : ((bytes.map UInt8.toNat).drop pos).takeWhile scanSpace =
      ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).map UInt8.toNat := by
    rw [← List.map_drop]; exact scanSpace_takeWhile_map' _
  have hcur : cursor = pos + ((bytes.drop pos).takeWhile
      (fun b => scanSpace b.toNat)).length := by
    have := hc.2
    rw [hmap] at this
    simpa using this
  refine ⟨hc.1, hcur, ?_⟩
  subst hcur
  have hshape := scanInt_pure_failure_has_shape_at bytes pos hpure
  have hdl : (bytes.drop pos).length = bytes.length - pos := List.length_drop ..
  have hget : ∀ i, (bytes.drop pos)[i]? = bytes[pos + i]? := by
    intro i; rw [List.getElem?_drop]
  rcases hshape with hwhite | ⟨spaces, sign, hspaces, hsign, hbytes⟩ |
      ⟨spaces, sign, byte, tail, hspaces, hsign, hnondigit, hbytes⟩ |
      ⟨spaces, byte, tail, hspaces, hbytes, hnotSpace, hnotPlus, hnotMinus, hnondigit⟩
  · obtain ⟨K, hK, _⟩ := scanInt_whitespaceOnly_fails bytes output pos hpos hwhite houtput hbound
    refine ⟨K, fun n hn => ?_⟩
    have := hK n hn
    have hl : pos + ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length =
        bytes.length := by rw [hwhite]; simp; omega
    rw [hl]; exact this
  · have hsp : ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length =
        spaces.length := by
      rw [hbytes]
      have hnot : ∀ b, [sign].head? = some b → scanSpace b.toNat = false := by
        intro b hb; simp at hb; subst hb
        rcases hsign with h | h <;> simp [scanSpace, h]
      rw [takeWhile_append_stops _ spaces [sign] hspaces hnot]
    have hlen : bytes.length - pos = spaces.length + 1 := by rw [← hdl, hbytes]; simp
    have hat : bytes[pos + spaces.length]? = some sign := by
      rw [← hget, hbytes]; simp
    exact scanInt_loneSign_fails_at bytes output pos sign hpos (by rw [hsp]; exact hat) hsign
      (by rw [hsp]; omega) houtput hbound
  · have hsp : ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length =
        spaces.length := by
      rw [hbytes]
      have hnot : ∀ b, ([sign, byte] ++ tail).head? = some b → scanSpace b.toNat = false := by
        intro b hb; simp at hb; subst hb
        rcases hsign with h | h <;> simp [scanSpace, h]
      have := takeWhile_append_stops (fun b : UInt8 => scanSpace b.toNat) spaces
        ([sign, byte] ++ tail) hspaces hnot
      rw [this]
    have hat1 : bytes[pos + spaces.length]? = some sign := by
      rw [← hget, hbytes]; simp
    have hat2 : bytes[pos + spaces.length + 1]? = some byte := by
      have := hget (spaces.length + 1)
      rw [hbytes] at this
      rw [Nat.add_assoc, ← this]; simp
    exact scanInt_signDelimiter_fails_at bytes output pos sign byte hpos (by rw [hsp]; exact hat1)
      hsign (by rw [hsp]; exact hat2) hnondigit houtput hbound
  · have hsp : ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length =
        spaces.length := by
      rw [hbytes]
      have hnot : ∀ b, (byte :: tail).head? = some b → scanSpace b.toNat = false := by
        intro b hb; simp at hb; subst hb; exact hnotSpace
      rw [takeWhile_append_stops _ spaces (byte :: tail) hspaces hnot]
    have hat : bytes[pos + spaces.length]? = some byte := by
      rw [← hget, hbytes]; simp
    exact scanInt_delimiter_fails_at bytes output pos byte hpos (by rw [hsp]; exact hat)
      ⟨hnotPlus, hnotMinus⟩ hnondigit houtput hbound


theorem scanInt_success_shape_at (bytes : Block) (pos : Nat) {value : Int} {cursor : Nat}
    (hpure : scanInt (bytes.map UInt8.toNat) pos = (true, value, cursor)) :
    let sp := pos + ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length
    (∃ byte, bytes[sp]? = some byte ∧ (48 ≤ byte.toNat ∧ byte.toNat ≤ 57) ∧
        byte.toNat ≠ 43 ∧ byte.toNat ≠ 45) ∨
    (∃ sign digit, bytes[sp]? = some sign ∧ (sign.toNat = 43 ∨ sign.toNat = 45) ∧
        bytes[sp + 1]? = some digit ∧ (48 ≤ digit.toNat ∧ digit.toNat ≤ 57)) := by
  intro sp
  have hmap : ((bytes.map UInt8.toNat).drop pos).takeWhile scanSpace =
      ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).map UInt8.toNat := by
    rw [← List.map_drop]; exact scanSpace_takeWhile_map' _
  have hlen : (((bytes.map UInt8.toNat).drop pos).takeWhile scanSpace).length =
      ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length := by
    rw [hmap]; simp
  unfold scanInt at hpure
  simp only [hlen] at hpure
  have hdd : ((bytes.map UInt8.toNat).drop pos).drop
      ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length =
      (bytes.drop sp).map UInt8.toNat := by
    rw [← List.map_drop, ← List.map_drop, List.drop_drop]
  rw [hdd] at hpure
  generalize hrest : bytes.drop sp = rest at hpure
  have hget : ∀ i, bytes[sp + i]? = rest[i]? := by
    intro i
    rw [← hrest]; simp [List.getElem?_drop]
  cases rest with
  | nil => simp [scanIntDigits] at hpure
  | cons b tl =>
    by_cases hs : b.toNat = 43 ∨ b.toNat = 45
    · cases tl with
      | nil => rcases hs with h | h <;> simp [scanIntDigits, h] at hpure
      | cons d tl' =>
        right
        refine ⟨b, d, ?_, hs, ?_, ?_⟩
        · simpa using hget 0
        · simpa using hget 1
        · refine Classical.byContradiction fun hc => ?_
          rcases hs with h | h <;> simp [scanIntDigits, h, scanDigit, hc] at hpure
    · left
      refine ⟨b, by simpa using hget 0, ?_, by omega, by omega⟩
      simp only [not_or] at hs
      have h43 : (b.toNat == 43) = false := by simp [hs.1]
      have h45 : (b.toNat == 45) = false := by simp [hs.2]
      refine Classical.byContradiction fun hc => ?_
      simp [scanIntDigits, h43, h45, scanDigit, hc] at hpure

/-- **Unified `tobj_scan_int` refinement from any start offset.** -/
theorem scanInt_refines_model_at (bytes output : Block) (pos : Nat)
    {flag : Bool} {value : Int} {cursor : Nat} (hpos : pos ≤ bytes.length)
    (hpure : scanInt (bytes.map UInt8.toNat) pos = (flag, value, cursor))
    (houtput : 4 ≤ output.length) (hbound : 8 + bytes.length < 4294967296) :
    (flag = false → value = 0 ∧ ∃ K, ∀ n, K ≤ n →
        callFunc Gen.prog n Gen.fid_tobj_scan_int
          [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
          (scanIntSuccessPackedMem bytes output pos) =
        .ok (some (.int IntTy.u8 0), scanIntSuccessPackedMem bytes output cursor)) ∧
    (flag = true → ∃ (K : Nat) (final : State),
      (∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tobj_scan_int
        [.ptr 20 0, .ptr 20 (8 + bytes.length), .ptr 21 0]
        (scanIntSuccessPackedMem bytes output pos) =
          .ok (some (.int IntTy.u8 1), final.mem)) ∧
      final.mem 20 = some
        (encodeLE 8 (ptrPack (.ptr 20 (8 + cursor))) ++ bytes) ∧
      final.mem 21 = some
        (encodeLE 4 (IntTy.wrap IntTy.i32 value) ++ output.drop 4)) := by
  refine ⟨?_, ?_⟩
  · intro hflag
    subst hflag
    obtain ⟨h1, _, h3⟩ := scanInt_failure_refines_model_at bytes output pos hpos hpure
      houtput hbound
    exact ⟨h1, h3⟩
  · intro hflag
    subst hflag
    rcases scanInt_success_shape_at bytes pos hpure with
      ⟨byte, hat, hdig, hn43, hn45⟩ | ⟨sign, digit, hat, hsign, hat1, hdig⟩
    · obtain ⟨K, final, hcall, h20, h21, hspec⟩ :=
        scanInt_success_no_sign_after_whitespace_callFunc bytes output pos byte
          hbound hpos houtput (by simpa [Nat.add_assoc] using hat) hdig hn43 hn45
      rw [hpure] at hspec
      simp only [Prod.mk.injEq, true_and] at hspec
      obtain ⟨hv, hc⟩ := hspec
      subst hv hc
      exact ⟨K, final, hcall, by simpa [Nat.add_assoc] using h20, h21⟩
    · obtain ⟨K, final, hcall, h20, h21, hspec⟩ :=
        scanInt_success_sign_after_whitespace_callFunc bytes output pos sign digit
          hbound hpos houtput (by simpa [Nat.add_assoc] using hat) hsign
          (by simpa [Nat.add_assoc] using hat1) hdig
      rw [hpure] at hspec
      simp only [Prod.mk.injEq, true_and] at hspec
      obtain ⟨hv, hc⟩ := hspec
      subst hv hc
      exact ⟨K, final, hcall, by simpa [Nat.add_assoc] using h20, h21⟩

namespace Obj.Tests.ObjTessEmitK

open Obj.C Obj

/-- Output array in block 0 (16 zeroed u32 slots); the counter cell in block 1
    initially holding `k`, matching `tobj_tess_emit(out, &k, a, b, c)`. -/
def memEmit (k : Nat) : Mem := fun b =>
  if b = 0 then some (List.replicate 64 0)
  else if b = 1 then some (encodeLE 4 k)
  else none

/-- Run the translated `tobj_tess_emit` once; returns `(k', out block)`. -/
def runEmit (k a b c : Nat) : Option (Nat × Block) :=
  match callFunc Gen.prog 1000 Gen.fid_tobj_tess_emit
      [.ptr 0 0, .ptr 1 0, .int IntTy.u32 a, .int IntTy.u32 b,
       .int IntTy.u32 c] (memEmit k) with
  | .ok (_, m) => match m 0, m 1 with
    | some blk, some kb =>
      match decodeLE kb, blk with
      | k', blk => some (k', blk)
    | _, _ => none
  | _ => none

/-- The triangle branch of the polygon core (`n = 3`) emits the single triple
    `(0, 1, 2)` at slot 0 and advances the counter to 1 -- the pure spec
    `Obj.polyTri` written out byte for byte. -/
example : runEmit 0 0 1 2 =
    some (1, encodeLE 4 0 ++ encodeLE 4 1 ++ encodeLE 4 2 ++
      List.replicate 52 0) := by
  decide +kernel

/-- Second triple of the 0-2 quad split lands at slot 1: `(0, 2, 3)`, matching
    `Obj.quadTris true`'s second triangle. -/
example : runEmit 1 0 2 3 =
    some (2, List.replicate 12 0 ++ encodeLE 4 0 ++ encodeLE 4 2 ++
      encodeLE 4 3 ++ List.replicate 40 0) := by
  decide +kernel

end Obj.Tests.ObjTessEmitK

namespace Obj.Tests.ObjF64

open Obj.C Obj

/-- `Res` carries a `Mem` (a function), so equality is not decidable; classify
    the call result into a small tag instead. -/
def resClass {α} : Res (Option Val × α) → Nat
  | .ok _ => 0
  | .ub => 1
  | .timeout => 2

/-- The `f64` bit pattern a successful call returns, if any. -/
def f64Res {α} : Res (Option Val × α) → Option Nat
  | .ok (some (.f64 b), _) => some b
  | _ => none

/-- Run one translated binary f64 helper.  `tobj_orient2d` is the natural
    `double`-arithmetic kernel (`(b0-a0)*(c1-a1) - (b1-a1)*(c0-a0)`); it
    exercises `sub`, `mul` and `sub`.  Points are `double[2]` blocks. -/
def orient (ax ay bxx byy cxx cyy : Nat) : Option Nat :=
  let mem : Mem := fun b =>
    if b = 0 then some (encodeLE 8 ax ++ encodeLE 8 ay)
    else if b = 1 then some (encodeLE 8 bxx ++ encodeLE 8 byy)
    else if b = 2 then some (encodeLE 8 cxx ++ encodeLE 8 cyy)
    else none
  f64Res (callFunc Gen.prog 500 Gen.fid_tobj_orient2d [.ptr 0 0, .ptr 1 0, .ptr 2 0] mem)

/-- `tobj_dabs` on a positive double returns it unchanged. -/
example : f64Res (callFunc Gen.prog 100 Gen.fid_tobj_dabs
    [.f64 0x3FF0000000000000] (fun _ => none)) = some 0x3FF0000000000000 := by
  decide +kernel

/-- `tobj_dabs(-1.0)` is `1.0`: IEEE negation of the negative branch. -/
example : f64Res (callFunc Gen.prog 100 Gen.fid_tobj_dabs
    [.f64 0xBFF0000000000000] (fun _ => none)) = some 0x3FF0000000000000 := by
  decide +kernel

/-- `tobj_dabs(-0.0)` is `+0.0` (bit patterns differ, values agree). -/
example : f64Res (callFunc Gen.prog 100 Gen.fid_tobj_dabs
    [.f64 0x8000000000000000] (fun _ => none)) = some 0x8000000000000000 := by
  decide +kernel

/-- `orient2d((0,0),(1,0),(0,1)) = 1.0`: the unit right triangle. -/
example : orient 0 0 0x3FF0000000000000 0 0 0x3FF0000000000000
    = some 0x3FF0000000000000 := by
  decide +kernel

/-- Collinear points give exactly `0.0`. -/
example : orient 0 0 0x3FF0000000000000 0 0x4000000000000000 0 = some 0 := by
  decide +kernel

/-- `orient2d((0,0),(1,0),(0,-1)) = -1.0`: reversed winding. -/
example : orient 0 0 0x3FF0000000000000 0 0 0xBFF0000000000000
    = some 0xBFF0000000000000 := by
  decide +kernel

/-- `0.1 + 0.2 = 0.30000000000000004`: the classic correctly-rounded result. -/
example : F64.addBits 0x3FB999999999999A 0x3FC999999999999A = 0x3FD3333333333334 := by
  decide +kernel

/-- `1/3` rounds to the nearest double. -/
example : F64.divBits 0x3FF0000000000000 0x4008000000000000 = 0x3FD5555555555555 := by
  decide +kernel

/-- Overflow to `+inf`. -/
example : F64.mulBits 0x7FE1CCF385EBC8A0 0x4024000000000000 = 0x7FF0000000000000 := by
  decide +kernel

/-- Subnormal arithmetic: `5e-324 + 5e-324 = 1e-323`. -/
example : F64.addBits 0x0000000000000001 0x0000000000000001 = 0x0000000000000002 := by
  decide +kernel

/-- `2^53 + 1` rounds to `2^53` (ties to even). -/
example : F64.addBits 0x4340000000000000 0x3FF0000000000000 = 0x4340000000000000 := by
  decide +kernel

/-- `1.0 * -0.0 = -0.0` (signed zero preserved through multiply). -/
example : F64.mulBits 0x3FF0000000000000 0x8000000000000000 = 0x8000000000000000 := by
  decide +kernel

/-- `0/0` is NaN. -/
example : F64.divBits 0 0 = 0x7FF8000000000000 := by
  decide +kernel

/-- `inf - inf` is NaN. -/
example : F64.subBits 0x7FF0000000000000 0x7FF0000000000000 = 0x7FF8000000000000 := by
  decide +kernel

/-- `inf * 0` is NaN. -/
example : F64.mulBits 0x7FF0000000000000 0 = 0x7FF8000000000000 := by
  decide +kernel

/-- `3.0 - 3.0 = +0.0` rather than a signed zero from cancellation. -/
example : F64.subBits 0x4008000000000000 0x4008000000000000 = 0 := by
  decide +kernel


example : orient 0x0 0x0 0x3ff0000000000000 0x0 0x0 0x3ff0000000000000 = some 0x3ff0000000000000 := by decide +kernel
example : orient 0x0 0x0 0x3ff0000000000000 0x0 0x0 0xbff0000000000000 = some 0xbff0000000000000 := by decide +kernel
example : orient 0x0 0x0 0x4008000000000000 0x3ff0000000000000 0x3ff0000000000000 0x4008000000000000 = some 0x4020000000000000 := by decide +kernel
example : orient 0x3ff0000000000000 0x4000000000000000 0x4010000000000000 0x4018000000000000 0x4022000000000000 0x3ff0000000000000 = some 0xc041800000000000 := by decide +kernel
example : orient 0xc004000000000000 0x3fe0000000000000 0x400a000000000000 0xbffc000000000000 0x401c000000000000 0x4012000000000000 = some 0x4046300000000000 := by decide +kernel
example : orient 0x0 0x0 0x3ff0000000000000 0x3ff0000000000000 0x4000000000000000 0x4000000000000000 = some 0x0 := by decide +kernel

/-- `tobj_dabs(-3.75) = 3.75`, through the translated body. -/
example : f64Res (callFunc Gen.prog 100 Gen.fid_tobj_dabs
    [.f64 0xC00E000000000000] (fun _ => none)) = some 0x400E000000000000 := by
  decide +kernel

/-- `tobj_dabs(5.5) = 5.5`. -/
example : f64Res (callFunc Gen.prog 100 Gen.fid_tobj_dabs
    [.f64 0x4016000000000000] (fun _ => none)) = some 0x4016000000000000 := by
  decide +kernel

/-! ### Fused multiply-add

`F64.fmaBits` is IEEE-754 `fusedMultiplyAdd`: the exact product `a*b` is added
to `c` and the sum is rounded **once**.  x86-64 `vfmadd132/213/231sd` (FMA3)
and AArch64 `fmadd` both implement exactly this, so the same model covers both
architectures.  Expected values below are `math.fma` from CPython 3.14. -/

/-- `fma(1,2,3) = 5`. -/
example : F64.fmaBits 0x3FF0000000000000 0x4000000000000000 0x4008000000000000
    = 0x4014000000000000 := by decide +kernel

/-- `fma(2,3,-1) = 5`. -/
example : F64.fmaBits 0x4000000000000000 0x4008000000000000 0xBFF0000000000000
    = 0x4014000000000000 := by decide +kernel

/-- **Single rounding matters:** `fma(1+2^-52, 1+2^-52, -(1+2^-51))` is
    `2^-104`: the exact product is `1 + 2^-51 + 2^-104`, so adding
    `-(1+2^-51)` leaves the low term.  Rounding the product first would give
    `1 + 2^-51` and then `0.0`.  This is precisely the case where the fused
    form buys accuracy. -/
example : F64.fmaBits 0x3FF0000000000001 0x3FF0000000000001 0xBFF0000000000002
    = 0x3970000000000000 := by decide +kernel

/-- Unfused path for the same inputs: `a*b` rounds, then `+ c` cancels to zero. -/
example : F64.addBits (F64.mulBits 0x3FF0000000000001 0x3FF0000000000001)
    0xBFF0000000000002 = 0x0 := by decide +kernel

/-- `fma(0.1, 0.2, 0)` keeps the exact product before rounding. -/
example : F64.fmaBits 0x3FB999999999999A 0x3FC999999999999A 0x0
    = 0x3F947AE147AE147C := by decide +kernel

/-- `fma(3, 1/3, -1) = -2^-54`, not `0`: again the fused product survives. -/
example : F64.fmaBits 0x4008000000000000 0x3FD5555555555555 0xBFF0000000000000
    = 0xBC90000000000000 := by decide +kernel

/-- `fma(-1, 0, 0) = +0` (`-0 * 0 = -0`, and `-0 + +0 = +0`).  The `+0`
    convention is the one IEEE-754 specifies for `fusedMultiplyAdd`. -/
example : F64.fmaBits 0xBFF0000000000000 0x0 0x0 = 0x0 := by decide +kernel

/-- `fma(2, 0.5, 1) = 2`. -/
example : F64.fmaBits 0x4000000000000000 0x3FE0000000000000 0x3FF0000000000000
    = 0x4000000000000000 := by decide +kernel

/-- A tiny product of two tiny values is absorbed by `1.0`, exactly as
    `fma` specifies (no intermediate underflow to zero). -/
example : F64.fmaBits 0x16687E92154EF7AC 0x16687E92154EF7AC 0x3FF0000000000000
    = 0x3FF0000000000000 := by decide +kernel

/-- `fma(7.5, -2.25, 0.125) = -16.75`. -/
example : F64.fmaBits 0x401E000000000000 0xC002000000000000 0x3FC0000000000000
    = 0xC030C00000000000 := by decide +kernel

/-- `fma(1e16, 1, -1e16) = 0` for the fused form; the unfused form agrees
    here because 1e16 is exactly representable, so this pins the cancellation
    path rather than the precision win. -/
example : F64.fmaBits 0x4341C37937E08000 0x3FF0000000000000 0xC341C37937E08000
    = 0x0 := by decide +kernel

/-- Large-integer product: still correctly rounded in one step. -/
example : F64.fmaBits 0x419D6F3454000000 0x41CD6F3458800000 0xBFF0000000000000
    = 0x437B13114FBFF538 := by decide +kernel

/-- Subnormal product survives: `2^-1022 * 2 = 2^-1021`. -/
example : F64.fmaBits 0x0010000000000000 0x4000000000000000 0x0
    = 0x0020000000000000 := by decide +kernel

/-- NaN in any operand propagates. -/
example : F64.fmaBits 0x7FF8000000000000 0x3FF0000000000000 0x0
    = 0x7FF8000000000000 := by decide +kernel

/-- `inf * 0 + c` is NaN. -/
example : F64.fmaBits 0x7FF0000000000000 0x0 0x3FF0000000000000
    = 0x7FF8000000000000 := by decide +kernel

/-- `inf + (-inf)` in the fused form is NaN. -/
example : F64.fmaBits 0x3FF0000000000000 0x7FF0000000000000 0xFFF0000000000000
    = 0x7FF8000000000000 := by decide +kernel

/-! ### The translated `tobj_orient2d` is the unfused form

`c2lean.py` passes `-ffp-contract=off`, so `a*b + c` in the C source stays two
roundings in the model, matching a default (no `-mfma`) x86-64 build and the
`TOBJ_TESS_USE_FMA`-off C path.  If the translator ever contracted to FMA the
generated tree would contain `(.fma ...)` and these values would change. -/

/-- A near-degenerate orientation whose value depends on the rounding of the
    second product: `(1,0)` and `(1+2^-52, 2^-104)` against the origin give
    exactly `2^-104` with the unfused form. -/
example : orient 0 0 0x3FF0000000000000 0 0x3FF0000000000001 0x3970000000000000
    = some 0x3970000000000000 := by
  decide +kernel

/-- Plain collinear-almost point: `orient2d((0,0),(1+2^-52,1+2^-52),(1,2^-104))`
    equals `1 + 2^-51` rounded, i.e. `0x3ff0000000000002`. -/
example : orient 0 0 0x3FF0000000000001 0x3FF0000000000001 0 0x3FF0000000000001
    = some 0x3FF0000000000002 := by
  decide +kernel

end Obj.Tests.ObjF64

namespace Obj.Tests.FmtReal

open Obj

/-- `f64Parts` mirrors `tobj_dparts_of`: 1.0 is `2^52 * 2^-52`. -/
example : f64Parts 0x3FF0000000000000 = (2 ^ 52, -52) := by decide +kernel

/-- 0.5 = 2^52 * 2^-53. -/
example : f64Parts 0x3FE0000000000000 = (2 ^ 52, -53) := by decide +kernel

/-- 2.0 = 2^52 * 2^-51. -/
example : f64Parts 0x4000000000000000 = (2 ^ 52, -51) := by decide +kernel

/-- 3.0 = 3 * 2^51 * 2^-51: the significand is 1.5 in units of 2^-51. -/
example : f64Parts 0x4008000000000000 = (3 * 2 ^ 51, -51) := by decide +kernel

/-- The smallest subnormal is `1 * 2^-1074`. -/
example : f64Parts 1 = (1, -1074) := by decide +kernel

/-- Zero decodes to a zero significand. -/
example : (f64Parts 0).1 = 0 := by decide +kernel

/-- The decoded rational of 1.0 is 1. -/
example : f64Rat 0x3FF0000000000000 = 1 := by
  unfold f64Rat f64Parts; decide +kernel

/-- The significand bound holds on a sample of patterns. -/
example : (f64Parts 0x7FEFFFFFFFFFFFFF).1 < 2 ^ 53 := f64Parts_fst_lt _
example : (f64Parts 1).1 < 2 ^ 53 := f64Parts_fst_lt _

/-- A decimal literal evaluates exactly: `123 * 10^-2 = 123/100`. -/
example : (DecLit.mk false 123 (-2)).value = (123 : Rat) / 100 := by
  unfold DecLit.value
  decide +kernel

/-- Negative literals carry their sign. -/
example : (DecLit.mk true 5 0).value = -5 := by
  unfold DecLit.value
  decide +kernel

end Obj.Tests.FmtReal

namespace Obj.Tests.Dabs

open Obj.C Obj Obj.C.Proofs

/-- `dabs(-1.0) = 1.0`. -/
example : dabsBits 0xBFF0000000000000 = 0x3FF0000000000000 := by decide +kernel

/-- `dabs(+1.0) = 1.0` (identity branch). -/
example : dabsBits 0x3FF0000000000000 = 0x3FF0000000000000 := by decide +kernel

/-- `dabs(-0.0) = -0.0`: IEEE comparison treats `-0.0` as *not* less than
    `0.0`, so the identity branch runs and the sign bit survives.  This is the
    bit-exact behaviour of the C code. -/
example : dabsBits 0x8000000000000000 = 0x8000000000000000 := by decide +kernel

/-- `dabs(0.0) = 0.0`. -/
example : dabsBits 0 = 0 := by decide +kernel

/-- `dabs` of a finite value is never NaN (it only flips a bit). -/
example : f64IsNaN (dabsBits 0xBFF0000000000000) = false := by decide +kernel

end Obj.Tests.Dabs

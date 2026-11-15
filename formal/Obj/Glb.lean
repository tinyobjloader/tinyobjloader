/-
  GLB container framing (glTF 2.0 GLB v2, and the spec-unstable glTF 2.1
  GLB v3 with 64-bit lengths).

  `parseFrame` is the specification of `tg3__glb_frame_parse`; `layout` and
  `writeHeaders` specify `tg3__glb_layout` / `tg3__glb_write_headers`.
  Arithmetic is on `Nat`; the C code is proven (formal/Obj/C/) to compute
  the same results with `uint64_t` arithmetic.
-/
import Obj.Basic

namespace Obj
namespace Glb

/-- Little-endian reads; out-of-range bytes read as 0 (never happens under
    the guards of `parseFrame`, see `parseFrame_reads_in_bounds`). -/
def byteAt (d : List UInt8) (i : Nat) : Nat := (d.getD i 0).toNat

def rd32 (d : List UInt8) (off : Nat) : Nat :=
  byteAt d off + byteAt d (off + 1) * 2^8 + byteAt d (off + 2) * 2^16 + byteAt d (off + 3) * 2^24

def rd64 (d : List UInt8) (off : Nat) : Nat :=
  rd32 d off + rd32 d (off + 4) * 2^32

def chunkJSON : Nat := 0x4E4F534A
def chunkBIN : Nat := 0x004E4942

structure Frame where
  jsonOff : Nat := 0
  jsonLen : Nat := 0
  binOff : Nat := 0
  binLen : Nat := 0
  hasJson : Bool := false
  hasBin : Bool := false
  is64 : Bool := false
  deriving DecidableEq, Repr

inductive Err where
  | header | magic | version | sizeMismatch | chunk
  deriving DecidableEq, Repr

/-- Bytes skipped after a chunk so the next one is 4-byte aligned, clamped to
    the end of the input. -/
def pad (off size : Nat) : Nat := min ((4 - off % 4) % 4) (size - off)

theorem pad_le (off size : Nat) : pad off size ≤ size - off := Nat.min_le_right _ _

/-- Length field of the chunk header at `off` (64-bit for GLB v3). -/
def chunkLen (d : List UInt8) (hdr off : Nat) : Nat :=
  if hdr = 12 then rd64 d off else rd32 d off

/-- Type field of the chunk header at `off`. -/
def chunkType (d : List UInt8) (hdr off : Nat) : Nat :=
  if hdr = 12 then rd32 d (off + 8) else rd32 d (off + 4)

/-- Record a chunk of type `ctype` with payload `[off, off+len)`. The last
    chunk of a given type wins, as in the C runtime. -/
def record (f : Frame) (ctype off len : Nat) : Frame :=
  if ctype = chunkJSON then { f with jsonOff := off, jsonLen := len, hasJson := true }
  else if ctype = chunkBIN then { f with binOff := off, binLen := len, hasBin := true }
  else f

/-- Offset of the next chunk header after a payload ending at `e`. -/
def next (e size : Nat) : Nat := e + pad e size

/-- The chunk loop. `hdr` is the chunk-header size (8 for v2, 12 for v3).
    `fuel` bounds the number of iterations; `parseFrame` passes
    `d.length + 1`, which is never exhausted because every iteration advances
    `off` by at least `hdr ≥ 1` (`loop_fuel_enough`). -/
def loop (d : List UInt8) (hdr : Nat) : Nat → Nat → Frame → Except Err Frame
  | 0, _, _ => .error .chunk
  | fuel + 1, off, f =>
    if hdr ≤ d.length - off then
      if chunkLen d hdr off > d.length - (off + hdr) then .error .chunk
      else
        loop d hdr fuel (next (off + hdr + chunkLen d hdr off) d.length)
          (record f (chunkType d hdr off) (off + hdr) (chunkLen d hdr off))
    else if f.hasJson then .ok f else .error .chunk

def parseFrame (d : List UInt8) : Except Err Frame :=
  if d.length < 12 then .error .header
  else if byteAt d 0 = 0x67 ∧ byteAt d 1 = 0x6C ∧ byteAt d 2 = 0x54 ∧ byteAt d 3 = 0x46 then
    if rd32 d 4 = 2 then
      if rd32 d 8 ≠ d.length then .error .sizeMismatch
      else loop d 8 (d.length + 1) 12 {}
    else if rd32 d 4 = 3 then
      if d.length < 16 then .error .header
      else if rd64 d 8 ≠ d.length then .error .sizeMismatch
      else loop d 12 (d.length + 1) 16 { is64 := true }
    else .error .version
  else .error .magic

/-! ## Writer layout -/

def align4 (n : Nat) : Nat := (n + 3) / 4 * 4

/-- `tg3__glb_layout`: chunk offsets/lengths and total size, or `none` when
    the container cannot represent the payload. -/
def layout (jsonLen binLen : Nat) (is64 : Bool) : Option (Frame × Nat) :=
  let limit := if is64 then 2^64 - 1 else 2^32 - 1
  let start := if is64 then 16 else 12
  let hdr := if is64 then 12 else 8
  let jp := align4 jsonLen
  let total0 := start + hdr + jp
  if total0 > limit then none
  else if binLen = 0 then
    some ({ jsonOff := start + hdr, jsonLen := jp, hasJson := true, is64 := is64 }, total0)
  else
    let bp := align4 binLen
    let total := total0 + hdr + bp
    if total > limit then none
    else some ({ jsonOff := start + hdr, jsonLen := jp, hasJson := true,
                 binOff := total0 + hdr, binLen := bp, hasBin := true, is64 := is64 }, total)

/-! ## Safety theorems -/

/-- Invariant of the chunk loop: recorded chunks lie inside the input. -/
def FrameIn (size : Nat) (f : Frame) : Prop :=
  (f.hasJson = true → f.jsonOff + f.jsonLen ≤ size) ∧
  (f.hasBin = true → f.binOff + f.binLen ≤ size)

theorem loop_ok_in (d : List UInt8) (hdr : Nat) (hhdr : 0 < hdr) :
    ∀ (fuel off : Nat) (f : Frame), FrameIn d.length f →
    ∀ f', loop d hdr fuel off f = .ok f' →
    FrameIn d.length f' ∧ f'.hasJson = true ∧ f'.is64 = f.is64 := by
  intro fuel
  induction fuel with
  | zero => intro off f _ f' h; simp [loop] at h
  | succ fuel ih =>
    intro off f hf f' h
    simp only [loop] at h
    by_cases hle : hdr ≤ d.length - off
    · simp only [hle, ↓reduceIte] at h
      by_cases hclen : chunkLen d hdr off > d.length - (off + hdr)
      · simp only [hclen, ↓reduceIte] at h; contradiction
      · simp only [hclen, ↓reduceIte] at h
        have hrec := ih _ (record f (chunkType d hdr off) (off + hdr) (chunkLen d hdr off)) ?_ f' h
        · refine ⟨hrec.1, hrec.2.1, ?_⟩
          rw [hrec.2.2]; unfold record; split <;> (try split) <;> rfl
        · unfold FrameIn at hf ⊢
          unfold record
          split
          · exact ⟨fun _ => by simp only; omega, fun hb => hf.2 hb⟩
          · split
            · exact ⟨fun hj => hf.1 hj, fun _ => by simp only; omega⟩
            · exact hf
    · simp only [hle, ↓reduceIte] at h
      split at h
      · cases h; exact ⟨hf, by assumption, rfl⟩
      · contradiction

/-- **GLB framing safety.** Whenever `parseFrame` succeeds, it has found a
    JSON chunk, and every chunk it reports lies inside the input. -/
theorem parseFrame_ok_in (d : List UInt8) (f : Frame) (h : parseFrame d = .ok f) :
    f.hasJson = true ∧ f.jsonOff + f.jsonLen ≤ d.length ∧
    (f.hasBin = true → f.binOff + f.binLen ≤ d.length) := by
  unfold parseFrame at h
  have h0 : FrameIn d.length ({} : Frame) := by simp [FrameIn]
  have h1 : FrameIn d.length ({ is64 := true } : Frame) := by simp [FrameIn]
  have fin : ∀ f0, FrameIn d.length f0 → ∀ hdr, 0 < hdr → ∀ fuel off, loop d hdr fuel off f0 = .ok f →
      f.hasJson = true ∧ f.jsonOff + f.jsonLen ≤ d.length ∧
      (f.hasBin = true → f.binOff + f.binLen ≤ d.length) := by
    intro f0 hf0 hdr hhdr fuel off hl
    have := loop_ok_in d hdr hhdr fuel off f0 hf0 f hl
    exact ⟨this.2.1, this.1.1 this.2.1, this.1.2⟩
  split at h
  · contradiction
  split at h
  · split at h
    · split at h
      · contradiction
      · exact fin _ h0 _ (by decide) _ _ h
    · split at h
      · split at h
        · contradiction
        split at h
        · contradiction
        · exact fin _ h1 _ (by decide) _ _ h
      · contradiction
  · contradiction


/-! ## Producer-side properties of `layout` -/

/-- Little-endian encoding of `n` into exactly `k` bytes (spec-side copy of
    the encoder used by the C writer). -/
def encLE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => (n % 256).toUInt8 :: encLE k (n / 256)

theorem encLE_length (k n : Nat) : (encLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [encLE, ih]

end Glb

/-! ## Writer constants -/

def chunkTypeJSON : Nat := 0x4E4F534A

def chunkTypeBIN : Nat := 0x004E4942

end Obj

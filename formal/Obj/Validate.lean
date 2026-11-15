/-
  Normative validation rules for tinygltf v3.

  Three rule classes, mirroring `tiny_gltf_v3.c`:

  * `indicesOk`  — `tg3__validate_indices`  (memory safety, always an error)
  * `rangesOk`   — `tg3__validate_resources` (memory safety, always an error)
  * `*Mask`      — `tg3__spec_*_mask`        (spec conformance; warning under
                    `TG3_PERMISSIVE`, error under `TG3_STRICT`)

  Bit assignments of the masks are identical to the `TG3__R_*` macros.
-/
import Obj.Model

namespace Obj
namespace Validate

/-! ## Spec-conformance masks (`tg3__spec_*_mask`) -/

def bit (n : Nat) : UInt32 := (1 : UInt32) <<< n.toUInt32

def flag (c : Bool) (n : Nat) : UInt32 := if c then bit n else 0

def bufferMask (b : Buffer) : UInt32 :=
  flag (b.byteLength < 1) 0

def bufferViewMask (bv : BufferView) : UInt32 :=
  flag (bv.byteLength < 1) 0 |||
  flag (bv.byteStride != 0 &&
        (bv.byteStride < 4 || bv.byteStride > 252 || (bv.byteStride &&& 3) != 0)) 1 |||
  flag (bv.target != 0 && bv.target != 34962 && bv.target != 34963) 2

def minMaxBad (cnt : Nat) (nc : Int32) : Bool :=
  cnt != 0 && (decide (nc < 0) || cnt.toUInt32 != nc.toUInt32)

def accessorMask (a : Accessor) : UInt32 :=
  let nc := numComponents a.type
  let cs := componentSize a.componentType
  flag (a.count < 1) 0 |||
  flag (minMaxBad a.minValues.length nc || minMaxBad a.maxValues.length nc) 1 |||
  flag (decide (0 < cs) && a.byteOffset.toNat % cs.toInt.toNat != 0) 2 |||
  flag (a.normalized != 0 && (a.componentType == CT.float || a.componentType == CT.uint)) 3 |||
  flag (a.sparse.isSparse != 0 && decide (a.sparse.count < 1)) 4

def badMode (m : Int32) : Bool := m != -1 && (decide (m < 0) || decide (m > 6))

def meshMask (me : Mesh) : UInt32 :=
  flag me.primitives.isEmpty 0 |||
  flag (me.primitives.any (fun p => badMode p.mode)) 1

def alphaModeBad (s : Bytes) : Bool :=
  !s.isEmpty && s != str "OPAQUE" && s != str "MASK" && s != str "BLEND"

def materialMask (m : Material) : UInt32 :=
  let pbr := m.pbr
  flag (alphaModeBad m.alphaMode) 0 |||
  flag (!(F64.le F64.zero m.alphaCutoff)) 1 |||
  flag (!(pbr.baseColorFactor.all F64.unitInterval) ||
        !(m.emissiveFactor.all F64.unitInterval) ||
        !(F64.unitInterval pbr.metallicFactor) ||
        !(F64.unitInterval pbr.roughnessFactor) ||
        !(F64.unitInterval m.occlusionTexture.strength)) 2 |||
  flag (decide (pbr.baseColorTexture.texCoord < 0) ||
        decide (pbr.metallicRoughnessTexture.texCoord < 0) ||
        decide (m.normalTexture.texCoord < 0) ||
        decide (m.occlusionTexture.texCoord < 0) ||
        decide (m.emissiveTexture.texCoord < 0)) 3

def cameraMask (c : Camera) : UInt32 :=
  if c.type = str "perspective" then
    let p := c.perspective
    flag (!(F64.lt F64.zero p.yfov) || !(F64.lt F64.zero p.znear) ||
          !(F64.eq p.zfar F64.zero || F64.lt p.znear p.zfar) ||
          !(F64.le F64.zero p.aspectRatio)) 1
  else if c.type = str "orthographic" then
    let o := c.orthographic
    flag (!(F64.ne o.xmag F64.zero) || !(F64.ne o.ymag F64.zero) ||
          !(F64.le F64.zero o.znear) || !(F64.lt o.znear o.zfar)) 1
  else bit 0

def wrapBad (w : Int32) : Bool := w != 10497 && w != 33071 && w != 33648

def samplerMask (s : Sampler) : UInt32 :=
  flag (s.magFilter != -1 && s.magFilter != 9728 && s.magFilter != 9729) 0 |||
  flag (s.minFilter != -1 &&
        (decide (s.minFilter < 9728) ||
         (decide (s.minFilter > 9729) && decide (s.minFilter < 9984)) ||
         decide (s.minFilter > 9987))) 1 |||
  flag (wrapBad s.wrapS || wrapBad s.wrapT) 2

def skinMask (s : Skin) : UInt32 := flag s.joints.isEmpty 0

def lightMask (l : Light) : UInt32 :=
  flag (l.type != str "directional" && l.type != str "point" && l.type != str "spot") 0 |||
  flag (!(F64.le F64.zero l.range)) 1

def pathBad (p : Bytes) : Bool :=
  p != str "translation" && p != str "rotation" && p != str "scale" &&
  p != str "weights" && p != str "pointer"

def interpBad (p : Bytes) : Bool :=
  !p.isEmpty && p != str "LINEAR" && p != str "STEP" && p != str "CUBICSPLINE"

def animationMask (a : Animation) : UInt32 :=
  flag a.channels.isEmpty 0 |||
  flag a.samplers.isEmpty 1 |||
  flag (a.channels.any (fun c => pathBad c.path)) 2 |||
  flag (a.samplers.any (fun s => interpBad s.interpolation)) 3

def modelMask (m : Model) : UInt32 :=
  flag (m.extensionsRequired.any (fun e => !(m.extensionsUsed.contains e))) 0

/-- No spec-conformance rule is violated anywhere in the model. -/
def specOk (m : Model) : Bool :=
  modelMask m == 0 &&
  m.buffers.all (fun x => bufferMask x == 0) &&
  m.bufferViews.all (fun x => bufferViewMask x == 0) &&
  m.accessors.all (fun x => accessorMask x == 0) &&
  m.meshes.all (fun x => meshMask x == 0) &&
  m.materials.all (fun x => materialMask x == 0) &&
  m.cameras.all (fun x => cameraMask x == 0) &&
  m.samplers.all (fun x => samplerMask x == 0) &&
  m.skins.all (fun x => skinMask x == 0) &&
  m.lights.all (fun x => lightMask x == 0) &&
  m.animations.all (fun x => animationMask x == 0)

/-- `tg3_component_size` as returned by the C runtime (`-1` as `u32`). -/
def componentSizeU (ct : Int32) : Nat :=
  if ct = CT.byte ∨ ct = CT.ubyte then 1
  else if ct = CT.short ∨ ct = CT.ushort then 2
  else if ct = CT.int ∨ ct = CT.uint ∨ ct = CT.float then 4
  else if ct = CT.double then 8
  else 4294967295

/-- `tg3_num_components` as returned by the C runtime (`-1` as `u32`). -/
def numComponentsU (t : Int32) : Nat :=
  if t = AT.scalar then 1
  else if t = AT.vec2 then 2
  else if t = AT.vec3 then 3
  else if t = AT.vec4 then 4
  else if t = AT.mat2 then 4
  else if t = AT.mat3 then 9
  else if t = AT.mat4 then 16
  else 4294967295

/-! ## Memory safety: indices (`tg3__validate_indices`) -/

def indicesOk (m : Model) : Bool :=
  let nAcc := m.accessors.length
  let nBV := m.bufferViews.length
  let nNodes := m.nodes.length
  validOptIdx m.defaultScene m.scenes.length &&
  m.bufferViews.all (fun bv => validIdx bv.buffer m.buffers.length) &&
  m.accessors.all (fun a =>
    validOptIdx a.bufferView nBV &&
    (a.sparse.isSparse == 0 ||
      (validIdx a.sparse.indices.bufferView nBV && validIdx a.sparse.values.bufferView nBV))) &&
  m.meshes.all (fun me => me.primitives.all (fun p =>
    validOptIdx p.indices nAcc &&
    validOptIdx p.material m.materials.length &&
    p.attributes.all (fun kv => validIdx kv.2 nAcc) &&
    p.targets.all (fun t => t.all (fun kv => validIdx kv.2 nAcc)))) &&
  m.nodes.all (fun n =>
    validOptIdx n.mesh m.meshes.length &&
    validOptIdx n.skin m.skins.length &&
    validOptIdx n.camera m.cameras.length &&
    validOptIdx n.light m.lights.length &&
    n.children.all (fun c => validIdx c nNodes) &&
    validOptIdx n.emitter m.audioEmitters.length &&
    n.lods.all (fun c => validIdx c nNodes)) &&
  m.textures.all (fun t =>
    validOptIdx t.source m.images.length && validOptIdx t.sampler m.samplers.length) &&
  m.images.all (fun im => validOptIdx im.bufferView nBV) &&
  m.skins.all (fun s =>
    validOptIdx s.inverseBindMatrices nAcc &&
    validOptIdx s.skeleton nNodes &&
    s.joints.all (fun j => validIdx j nNodes)) &&
  m.animations.all (fun an =>
    an.channels.all (fun ch =>
      validIdx ch.sampler an.samplers.length && validOptIdx ch.targetNode nNodes) &&
    an.samplers.all (fun s => validIdx s.input nAcc && validIdx s.output nAcc)) &&
  m.scenes.all (fun sc =>
    sc.nodes.all (fun n => validIdx n nNodes) &&
    sc.audioEmitters.all (fun e => validIdx e m.audioEmitters.length)) &&
  m.materials.all (fun mat =>
    let nT := m.textures.length
    validOptIdx mat.pbr.baseColorTexture.index nT &&
    validOptIdx mat.pbr.metallicRoughnessTexture.index nT &&
    validOptIdx mat.normalTexture.index nT &&
    validOptIdx mat.occlusionTexture.index nT &&
    validOptIdx mat.emissiveTexture.index nT &&
    mat.lods.all (fun l => validIdx l m.materials.length)) &&
  m.audioSources.all (fun s => validOptIdx s.bufferView nBV) &&
  m.audioEmitters.all (fun e => validOptIdx e.source m.audioSources.length) &&
  m.thumbnails.all (fun t => validIdx t m.images.length)

/-! ## Memory safety: byte ranges (`tg3__validate_resources`) -/

/-- Accessor component types allowed by the glTF 2.0 schema. -/
def validAccessorCT (ct : Int32) : Bool :=
  ct == CT.byte || ct == CT.ubyte || ct == CT.short || ct == CT.ushort ||
  ct == CT.uint || ct == CT.float

def validSparseIndexCT (ct : Int32) : Bool :=
  ct == CT.ubyte || ct == CT.ushort || ct == CT.uint

/-- Effective size of a buffer (`byte_length ? byte_length : data.count`). -/
def bufSize (b : Buffer) : Nat :=
  if b.byteLength != 0 then b.byteLength.toNat else b.dataCount.toNat

/-- `[off, off+len)` lies inside a region of `cap` bytes. In C this is
    `!overflow(off+len) && off+len <= cap`; since `cap < 2^64` the overflow
    case is subsumed by the `Nat` comparison. -/
def fits (off len cap : Nat) : Bool := decide (off + len ≤ cap)

/-- Size of one accessor element (`component size * component count`). -/
def elemSize (a : Accessor) : Nat :=
  (componentSize a.componentType).toInt.toNat * (numComponents a.type).toInt.toNat

/-- Effective stride inside a buffer view. -/
def stride (a : Accessor) (bv : BufferView) : Nat :=
  if bv.byteStride != 0 then bv.byteStride.toNat else elemSize a

/-- Bytes spanned by `count` elements: `(count-1)*stride + elemSize`. -/
def span (a : Accessor) (bv : BufferView) : Nat :=
  if a.count.toNat = 0 then 0 else (a.count.toNat - 1) * stride a bv + elemSize a

def bufferOk (b : Buffer) : Bool :=
  b.dataCount == 0 || decide (b.byteLength ≤ b.dataCount)

def bufferViewOk (m : Model) (bv : BufferView) : Bool :=
  match getIdx? m.buffers bv.buffer with
  | none => true
  | some b => fits bv.byteOffset.toNat bv.byteLength.toNat (bufSize b)

def accessorBVOk (m : Model) (a : Accessor) : Bool :=
  match getIdx? m.bufferViews a.bufferView with
  | none => true
  | some bv =>
    decide (elemSize a ≤ stride a bv) &&
    decide (span a bv < u64Bound) &&
    fits a.byteOffset.toNat (span a bv) bv.byteLength.toNat

def sparseOk (m : Model) (a : Accessor) : Bool :=
  if a.sparse.isSparse == 0 then true else
  let sc := a.sparse.count
  if decide (sc < 0) || decide (sc.toInt > a.count.toNat) then false else
  let n := sc.toInt.toNat
  validSparseIndexCT a.sparse.indices.componentType &&
  (match getIdx? m.bufferViews a.sparse.indices.bufferView with
   | none => true
   | some bv =>
     let isz := componentSize a.sparse.indices.componentType
     decide (0 < isz) && decide (n * isz.toInt.toNat < u64Bound) &&
     fits a.sparse.indices.byteOffset.toNat (n * isz.toInt.toNat) bv.byteLength.toNat) &&
  (match getIdx? m.bufferViews a.sparse.values.bufferView with
   | none => true
   | some bv =>
     decide (n * elemSize a < u64Bound) &&
     fits a.sparse.values.byteOffset.toNat (n * elemSize a) bv.byteLength.toNat)

def accessorOk (m : Model) (a : Accessor) : Bool :=
  validAccessorCT a.componentType &&
  decide (0 < numComponents a.type) &&
  accessorBVOk m a && sparseOk m a

def rangesOk (m : Model) : Bool :=
  m.buffers.all bufferOk &&
  m.bufferViews.all (bufferViewOk m) &&
  m.accessors.all (accessorOk m)

/-! ## Verdict (`tg3__validate_model`) -/

inductive Strictness where
  | permissive | strict
  deriving DecidableEq, Repr

structure Options where
  validateIndices : Bool := true
  validateRanges : Bool := true
  strictness : Strictness := .permissive
  deriving Repr

inductive Code where
  | ok | invalidIndex | invalidAccessor | invalidValue
  deriving DecidableEq, Repr

/-- The result code `tg3__validate_model` returns. -/
def validate (o : Options) (m : Model) : Code :=
  if o.validateIndices && !indicesOk m then .invalidIndex
  else if o.validateRanges && !rangesOk m then .invalidAccessor
  else if o.strictness = .strict && !specOk m then .invalidValue
  else .ok

/-- Models every naive consumer can index without going out of bounds. -/
def WellFormedSafe (m : Model) : Prop := indicesOk m = true ∧ rangesOk m = true

/-- Models that additionally satisfy every spec-conformance rule. -/
def WellFormedStrict (m : Model) : Prop := WellFormedSafe m ∧ specOk m = true

instance (m : Model) : Decidable (WellFormedSafe m) := by
  unfold WellFormedSafe; infer_instance

instance (m : Model) : Decidable (WellFormedStrict m) := by
  unfold WellFormedStrict; infer_instance

end Validate
end Obj

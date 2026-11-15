/-
  The glTF object model as seen by the tinygltf v3 C runtime.

  Each structure mirrors the corresponding `tg3_*` struct in `tiny_gltf_v3.h`
  field-for-field, restricted to the fields that any validation rule reads.
  C `(pointer, count)` pairs become `List`s; the C invariant that `count`
  equals the number of readable elements is the assumption that links a C
  heap to this model. Fixed-size C arrays (`base_color_factor[4]`, ...) are
  lists of the corresponding length.
-/
import Obj.Basic

namespace Obj

/-! ## Constants (`TG3_*` macros) -/

namespace CT
def byte : Int32 := 5120
def ubyte : Int32 := 5121
def short : Int32 := 5122
def ushort : Int32 := 5123
def int : Int32 := 5124
def uint : Int32 := 5125
def float : Int32 := 5126
def double : Int32 := 5130
end CT

namespace AT
def vec2 : Int32 := 2
def vec3 : Int32 := 3
def vec4 : Int32 := 4
def mat2 : Int32 := 34
def mat3 : Int32 := 35
def mat4 : Int32 := 36
def scalar : Int32 := 65
end AT

/-- `tg3_component_size`. -/
def componentSize (ct : Int32) : Int32 :=
  if ct = CT.byte ∨ ct = CT.ubyte then 1
  else if ct = CT.short ∨ ct = CT.ushort then 2
  else if ct = CT.int ∨ ct = CT.uint ∨ ct = CT.float then 4
  else if ct = CT.double then 8
  else -1

/-- `tg3_num_components`. -/
def numComponents (t : Int32) : Int32 :=
  if t = AT.scalar then 1
  else if t = AT.vec2 then 2
  else if t = AT.vec3 then 3
  else if t = AT.vec4 then 4
  else if t = AT.mat2 then 4
  else if t = AT.mat3 then 9
  else if t = AT.mat4 then 16
  else -1

/-! ## Objects -/

structure Buffer where
  byteLength : UInt64 := 0
  /-- `data.count`: number of bytes actually loaded (0 = not loaded). -/
  dataCount : UInt64 := 0
  deriving Repr, Inhabited

structure BufferView where
  buffer : Int32
  byteOffset : UInt64 := 0
  byteLength : UInt64
  byteStride : UInt32 := 0
  target : Int32 := 0
  deriving Repr, Inhabited

structure SparseIndices where
  byteOffset : UInt64 := 0
  bufferView : Int32 := -1
  componentType : Int32 := 0
  deriving Repr, Inhabited

structure SparseValues where
  bufferView : Int32 := -1
  byteOffset : UInt64 := 0
  deriving Repr, Inhabited

structure Sparse where
  count : Int32 := 0
  isSparse : Int32 := 0
  indices : SparseIndices := {}
  values : SparseValues := {}
  deriving Repr, Inhabited

structure Accessor where
  bufferView : Int32 := -1
  byteOffset : UInt64 := 0
  normalized : Int32 := 0
  componentType : Int32
  count : UInt64
  type : Int32
  minValues : List F64 := []
  maxValues : List F64 := []
  sparse : Sparse := {}
  deriving Repr, Inhabited

structure TextureInfo where
  index : Int32 := -1
  texCoord : Int32 := 0
  deriving Repr, Inhabited

structure NormalTextureInfo where
  index : Int32 := -1
  texCoord : Int32 := 0
  scale : F64 := F64.one
  deriving Repr, Inhabited

structure OcclusionTextureInfo where
  index : Int32 := -1
  texCoord : Int32 := 0
  strength : F64 := F64.one
  deriving Repr, Inhabited

structure PbrMetallicRoughness where
  baseColorFactor : List F64 := [F64.one, F64.one, F64.one, F64.one]
  baseColorTexture : TextureInfo := {}
  metallicFactor : F64 := F64.one
  roughnessFactor : F64 := F64.one
  metallicRoughnessTexture : TextureInfo := {}
  deriving Repr, Inhabited

structure Material where
  emissiveFactor : List F64 := [F64.zero, F64.zero, F64.zero]
  alphaMode : Bytes := str "OPAQUE"
  alphaCutoff : F64 := F64.half
  lods : List Int32 := []
  pbr : PbrMetallicRoughness := {}
  normalTexture : NormalTextureInfo := {}
  occlusionTexture : OcclusionTextureInfo := {}
  emissiveTexture : TextureInfo := {}
  deriving Repr, Inhabited

structure Primitive where
  attributes : List (Bytes × Int32) := []
  material : Int32 := -1
  indices : Int32 := -1
  mode : Int32 := 4
  targets : List (List (Bytes × Int32)) := []
  deriving Repr, Inhabited

structure Mesh where
  primitives : List Primitive := []
  deriving Repr, Inhabited

structure Node where
  camera : Int32 := -1
  skin : Int32 := -1
  mesh : Int32 := -1
  light : Int32 := -1
  emitter : Int32 := -1
  lods : List Int32 := []
  children : List Int32 := []
  deriving Repr, Inhabited

structure Skin where
  inverseBindMatrices : Int32 := -1
  skeleton : Int32 := -1
  joints : List Int32 := []
  deriving Repr, Inhabited

structure AnimationChannel where
  sampler : Int32
  targetNode : Int32 := -1
  path : Bytes
  deriving Repr, Inhabited

structure AnimationSampler where
  input : Int32
  output : Int32
  interpolation : Bytes := str "LINEAR"
  deriving Repr, Inhabited

structure Animation where
  channels : List AnimationChannel := []
  samplers : List AnimationSampler := []
  deriving Repr, Inhabited

structure PerspectiveCamera where
  aspectRatio : F64 := F64.zero
  yfov : F64 := F64.zero
  zfar : F64 := F64.zero
  znear : F64 := F64.zero
  deriving Repr, Inhabited

structure OrthographicCamera where
  xmag : F64 := F64.zero
  ymag : F64 := F64.zero
  zfar : F64 := F64.zero
  znear : F64 := F64.zero
  deriving Repr, Inhabited

structure Camera where
  type : Bytes := []
  perspective : PerspectiveCamera := {}
  orthographic : OrthographicCamera := {}
  deriving Repr, Inhabited

structure Scene where
  nodes : List Int32 := []
  audioEmitters : List Int32 := []
  deriving Repr, Inhabited

structure Light where
  type : Bytes := []
  range : F64 := F64.zero
  deriving Repr, Inhabited

structure Texture where
  sampler : Int32 := -1
  source : Int32 := -1
  deriving Repr, Inhabited

structure Image where
  bufferView : Int32 := -1
  deriving Repr, Inhabited

structure Sampler where
  minFilter : Int32 := -1
  magFilter : Int32 := -1
  wrapS : Int32 := 10497
  wrapT : Int32 := 10497
  deriving Repr, Inhabited

structure AudioSource where
  bufferView : Int32 := -1
  deriving Repr, Inhabited

structure AudioEmitter where
  source : Int32 := -1
  deriving Repr, Inhabited

structure Model where
  version : Bytes := str "2.0"
  accessors : List Accessor := []
  animations : List Animation := []
  buffers : List Buffer := []
  bufferViews : List BufferView := []
  materials : List Material := []
  meshes : List Mesh := []
  nodes : List Node := []
  textures : List Texture := []
  images : List Image := []
  skins : List Skin := []
  samplers : List Sampler := []
  cameras : List Camera := []
  scenes : List Scene := []
  lights : List Light := []
  audioEmitters : List AudioEmitter := []
  audioSources : List AudioSource := []
  /-- glTF 2.1 (spec-unstable): image indices. -/
  thumbnails : List Int32 := []
  defaultScene : Int32 := -1
  extensionsUsed : List Bytes := []
  extensionsRequired : List Bytes := []
  deriving Repr, Inhabited

end Obj

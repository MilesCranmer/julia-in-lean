import JuliaLean.base.reinterpretarray
import JuliaLean.Registry.Types

/-!
# Properties of `base/reinterpretarray.jl`

Each open specification refers to the typed, source-mirrored methods in
`JuliaLean.base.reinterpretarray`. No proofs are supplied in this model pass.
-/

namespace JuliaLean.Proofs.base.reinterpretarray

open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.Registry

/-!
## Nothing to promise

throwbits@14: Internal constructor error helper; public validation is specified on the constructors.
throwsize0@18: Internal constructor error helper; public validation is specified on the constructors.
throwsingleton@23: Internal constructor error helper; public validation is specified on the constructors.
throwbitpadding@27: Internal constructor error helper; public validation is specified on the constructors.
thrownonint@74: Internal constructor error helper; public validation is specified on the constructor.
throwaxes1@80: Internal constructor error helper; public validation is specified on the constructor.
throwintmult@108: Internal constructor error helper; reshape validation is specified on the constructor.
throwsize1@113: Internal constructor error helper; reshape validation is specified on the constructor.
throwfromsingleton@119: Internal constructor error helper; reshape validation is specified on the constructor.
reinterpret@188: The Julia file declares the overload without a method body.
reinterpret@190: This overload delegates reinterpretation to its parent view without a further transformation.
_checkcontiguous@232: This method only forwards the contiguity query to its parent.
similar@234: This method only forwards similar-array allocation to its parent.
similar@235: This method only forwards type-based similar-array allocation to the parent type.
to_index@279: This conversion preserves the existing static Cartesian index value.
SimdLoop.simd_outer_range@327: This method supplies compiler-facing SIMD outer-range metadata.
SimdLoop.simd_inner_length@328: This method supplies compiler-facing SIMD inner-length metadata.
SimdLoop.simd_index@329: This method supplies compiler-facing SIMD index metadata.
_maybe_reshape@333: This private dispatch helper selects the ordinary Cartesian fallback for static indices.
_maybe_reshape@334: This private dispatch helper preserves an already reshaped array.
_getindex@337: This fallback delegates indexing to the ordinary Cartesian array path.
_setindex!@341: This fallback delegates assignment to the ordinary Cartesian array path.
_getindex@347: This private fallback adapts a static Cartesian index to ordinary parent indices.
_setindex!@352: This private fallback adapts static Cartesian assignment to ordinary parent indices.
eachindex@365: This method forwards eachindex to the underlying parent.
getindex@413: This zero-dimensional getter delegates to the shared checked getter except for scalar reinterpretation.
getindex@430: This zero-dimensional reshaped getter delegates to the first-index getter.
isassigned@433: This Cartesian isassigned overload forwards the query to the parent.
_isassigned_ra@434: This internal fallback deliberately assumes assigned storage; exact parent access is delegated to the getter.
getindex@442: This linear-index helper dispatches to the pointer or parent-element getter.
getindex@454: This Cartesian getter is an internal adapter from parent values to a static index.
setindex!@572: The non-scalar zero-dimensional setter delegates to the shared linear setter.
setindex!@580: This zero-dimensional reshaped setter delegates to the shared linear setter.
setindex!@588: This linear setter helper dispatches to the pointer or parent-element setter.
mapreduce_impl@984: This default reduction helper supplies the pairwise block size to the reduction worker.
_totuple@990: This specialization is an optimization path; tuple conversion semantics belong to the public constructor.
-/

/-- The first target-sized byte window of an array's parent storage. -/
def byteWindow (bytes : Bytes) (offset size : Nat) : Bytes := (bytes.drop offset).take size

/-- A successful write changes one byte window and preserves its prefix and suffix. -/
def writesOnlyWindow (before after expected : Bytes) (offset : Nat) : Prop :=
  after = overwriteBytes before offset expected ∧
  after.take offset = before.take offset ∧
  after.drop (offset + expected.length) = before.drop (offset + expected.length)

/-- Non-reshape construction preserves rank; reshape construction adjusts it by the element-size ratio. -/
def ReinterpretRankShape : Prop :=
  (∀ {T S A : Type} (target source : TypeLayout) (a : ArrayInput A)
      (r : ReinterpretArray T S (ArrayInput A)),
    m73_reinterpret.{0,0,0,0,0} target source a = .ok r → r.rank = a.rank ∧ r.reshaped = false) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (a : ArrayInput A)
      (r : ReinterpretArray T S (ArrayInput A)),
    m107_reinterpretReshape.{0,0,0,0,0} target source a = .ok r →
      (target.alignedSize = source.alignedSize → r.rank = a.rank) ∧
      (target.alignedSize < source.alignedSize → r.rank = a.rank + 1) ∧
      (source.alignedSize < target.alignedSize → r.rank + 1 = a.rank) ∧ r.reshaped = true)

/-- Constructors reject non-bits layouts in target-before-source order. -/
def ReinterpretConstructorValidation : Prop :=
  (∀ {T S A : Type} (target source : TypeLayout) (a : ArrayInput A),
    target.isBits = false → m73_reinterpret.{0,0,0,0,0} (T := T) (S := S) target source a = .error .argument) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (a : ArrayInput A),
    source.isBits = false → target.isBits = true →
      m73_reinterpret.{0,0,0,0,0} (T := T) (S := S) target source a = .error .argument) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (a : ArrayInput A),
    target.isBits = false → m107_reinterpretReshape.{0,0,0,0,0} (T := T) (S := S) target source a = .error .argument) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (a : ArrayInput A),
    source.isBits = false → target.isBits = true →
      m107_reinterpretReshape.{0,0,0,0,0} (T := T) (S := S) target source a = .error .argument)

/-- A successful non-reshape size computation preserves the source-to-target byte count. -/
def ReinterpretSizeOverflow : Prop :=
  ∀ {T S A : Type} (target source : TypeLayout) (input : ArrayInput A)
    (view : ReinterpretArray T S (ArrayInput A)) (dims : List I64),
    m73_reinterpret.{0,0,0,0,0} (T := T) (S := S) target source input = .ok view →
    m374_sizeNonReshaped.{0,0,0,0,0} (fun x y => (JInt.div x y).mapError (fun _ => .divide)) view = .ok dims →
    (dims.headD (JInt.lit .i64 0)).val * target.alignedSize.val =
      (input.size.headD (JInt.lit .i64 0)).val * source.alignedSize.val

/-- A checked non-reshape read returns exactly the target-sized bytes at its parent offset. -/
def RaGetCorrect : Prop :=
  ∀ {T S A : Type} (a : ReinterpretArray T S A) (i : I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (fieldtype : TypeLayout → Nat → TypeLayout)
    (getParent : A → I64 → List I64 → RResult Bytes),
    a.reshaped = false → a.target.singleton = false → a.readable = true →
    1 ≤ i.val → i.val * a.target.alignedSize.val.toNat ≤ a.bytes.length →
    (∀ k : Nat, getParent a.parent (JInt.lit .i64 (k + 1)) [] =
      .ok (byteWindow a.bytes (k * a.source.alignedSize.val.toNat) a.source.alignedSize.val.toNat)) →
    checkbounds a i [] = .ok () →
    (∀ b, m882_reinterpret.{0,0,0,0,0} (fun t => t.fields.length)
        (fun t j => (t.fields.getD j ⟨0, 0, true, [], false⟩).offset)
        fieldtype a.target a.source b = .ok b) →
    m473_getindexNonReshaped.{0,0,0,0,0} checkbounds fieldtype getParent a i [] =
      .ok (byteWindow a.bytes ((i.val - 1).toNat * a.target.alignedSize.val.toNat)
        a.target.alignedSize.val.toNat)

/-- A checked non-reshape write changes only the target-sized byte window. -/
def RaSetCorrect : Prop :=
  ∀ {T S A V : Type} (a : ReinterpretArray T S A) (value : V) (i : I64)
    (encoded : Bytes) (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (setParent : A → Bytes → RResult A),
    a.reshaped = false → a.target.singleton = false → 1 ≤ i.val →
    encoded.length = a.target.alignedSize.val.toNat →
    convertValue a.target value = .ok encoded → checkbounds a i [] = .ok () →
    (∀ b, m882_reinterpret.{0,0,0,0,0} fieldcount fieldoffset fieldtype a.source a.target b = .ok b) →
    (∀ bytes, setParent a.parent bytes = .ok a.parent) →
    ∀ updated, m619_setindexNonReshaped.{0,0,0,0,0} fieldcount fieldoffset fieldtype checkbounds
      convertValue setParent a value i [] = .ok updated →
      writesOnlyWindow a.bytes updated.bytes encoded ((i.val - 1).toNat * encoded.length)

/-- Successful checked reads and writes stay inside the parent byte image. -/
def ReinterpretGetMemorySafe : Prop :=
  ∀ {T S A : Type} (a : ReinterpretArray T S A) (i : I64) (tail : List I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit),
    checkbounds a i tail = .ok () → 1 ≤ i.val →
    (i.val - 1).toNat * a.target.alignedSize.val.toNat + a.target.alignedSize.val.toNat ≤ a.bytes.length

def ReinterpretSetMemorySafe : Prop := ReinterpretGetMemorySafe

/-- Constructor flags match the source and target padding relation. -/
def ReinterpretPaddingFlags : Prop :=
  ∀ {T S A : Type} (target source : TypeLayout) (parent : A) (bytes : Bytes)
    (rank : Nat) (axis : Axis) (size : List I64) (r : ReinterpretArray T S (ArrayInput A)),
    m73_reinterpret.{0,0,0,0,0} (T := T) (S := S) target source ⟨parent, bytes, rank, axis, size⟩ = .ok r →
    (r.readable = true ↔ m772_arraySubpadding.{0,0,0,0,0} target source = .ok true) ∧
    (r.writable = true ↔ m772_arraySubpadding.{0,0,0,0,0} source target = .ok true)

/-- Stride lookup returns the indexed stride when the dimension is in range and length otherwise. -/
def ReinterpretStrideBehavior : Prop :=
  ∀ {A K : Type} (ndims : A → I64) (strides : A → List I64) (length : A → I64)
    (lessEq : K → I64 → Bool) (get : List I64 → K → I64) (a : A) (k : K),
    lessEq k (ndims a) = false → m208_stride.{0,0,0,0,0} ndims strides length lessEq get a k = length a

/-- Index-style selection preserves linear indexing unless reshaping expands the channel dimension. -/
def ReinterpretIndexStyle : Prop :=
  (∀ {A : Type} (parentStyle : A → IndexStyleModel) (parent : A),
    m263_indexStyle.{0,0,0,0,0} parentStyle parent =
      if parentStyle parent == .linear then .linear else .cartesian) ∧
  (∀ {A : Type} (parentStyle : A → IndexStyleModel) (parent : A) (targetSize sourceSize : Nat),
    m266_indexStyleReshaped.{0,0,0,0,0} parentStyle parent targetSize sourceSize =
      if targetSize < sourceSize then
        if parentStyle parent == .linear then .staticCartesian (sourceSize / targetSize) else .cartesian
      else if parentStyle parent == .linear then .linear else .cartesian)

/-- The static Cartesian iterator exposes its dimensions and starts at the first parent index. -/
def ReinterpretCartesianIteration : Prop :=
  (∀ {K : Nat} (iter : SCartesianIndices2 K), m298_indicesSize.{0,0,0,0,0} iter = (K, iter.indices2.length)) ∧
  (∀ {K : Nat} (iter : SCartesianIndices2 K),
    m299_indicesAxes.{0,0,0,0,0} iter = [⟨JInt.lit .i64 1, JInt.lit .i64 K⟩,
      ⟨JInt.lit .i64 1, JInt.lit .i64 iter.indices2.length⟩]) ∧
  (∀ {K : Nat} (iter : SCartesianIndices2 K) {σ : Type} (item : I64) (state : σ)
      (iterate : List I64 → Option (I64 × σ)),
    iterate iter.indices2 = some (item, state) →
      m309_indicesIterate.{0,0,0,0,0} iterate iter = some (⟨JInt.lit .i64 1, item⟩,
        (JInt.lit .i64 1, item, state)))

/-- Equal-size nested reinterpretation unwraps the existing parent view. -/
def ReinterpretNestedDispatch : Prop :=
  ∀ {T S P A : Type} (target : TypeLayout) (a : ReinterpretArray S P (ArrayInput A)),
    target.id = a.source.id →
    m191_reinterpretReshapedParent.{0,0,0,0,0} (T := T) target a = .ok (.parent a.parent)

/-- Identity specializations return the same input array. -/
def ReinterpretIdentity : Prop :=
  (∀ {A : Type} (a : A), m104_reinterpretIdentity.{0,0,0,0,0} a = a) ∧
  (∀ {A : Type} (a : A), m145_reinterpretReshapeIdentity.{0,0,0,0,0} a = a)

/-- Parent, alias and pointer metadata operations delegate to the underlying parent. -/
def ReinterpretParentMetadata : Prop :=
  (∀ {T S A : Type} (a : ReinterpretArray T S A), m369_parent.{0,0,0,0,0} a = a.parent) ∧
  (∀ {T S A R : Type} (ids : A → R) (a : ReinterpretArray T S A),
    m370_dataids.{0,0,0,0,0} ids a = ids a.parent) ∧
  (∀ {T S A R : Type} (hasOffset : A → R) (a : ReinterpretArray T S A),
    m401_hasOffset.{0,0,0,0,0} hasOffset a = hasOffset a.parent)

/-- Pointer conversion preserves the parent conversion and casts its resulting pointer type. -/
def ReinterpretPointerMetadata : Prop :=
  ∀ {T S A R : Type} (convert : TypeLayout → A → R)
    (cast : TypeLayout → R → R) (a : ReinterpretArray T S A),
    m410_cconvert.{0,0,0,0,0} convert a = convert a.source a.parent ∧
    m411_unsafeConvert.{0,0,0,0,0} convert cast a.target a = cast a.target (convert a.source a.parent)

/-- Equal packed layouts reinterpret to the same byte sequence. -/
def ReinterpretScalarRoundtrip : Prop :=
  ∀ (fieldcount : TypeLayout → Nat) (fieldoffset : TypeLayout → Nat → Nat)
    (fieldtype : TypeLayout → Nat → TypeLayout) (output input : TypeLayout) (bytes : Bytes),
    output.isBits = true → input.isBits = true → output.bitPadding = false → input.bitPadding = false →
    output.datatypePadding = false → input.datatypePadding = false →
    output.alignedSize = input.alignedSize → bytes.length = output.alignedSize.val.toNat →
    m882_reinterpret.{0,0,0,0,0} fieldcount fieldoffset fieldtype output input bytes = .ok bytes

/-- Packed-copy operations preserve initialized bytes and zero-fill the destination padding. -/
def ReinterpretPackedCopies : Prop :=
  (∀ (fieldcount : TypeLayout → Nat) (fieldoffset : TypeLayout → Nat → Nat)
    (fieldtype : TypeLayout → Nat → TypeLayout) (sizeof : TypeLayout → Nat)
    (layout : TypeLayout) (input packed : Bytes),
    layout.primitive = true →
    m842_copytopacked.{0,0,0,0,0} fieldcount fieldoffset fieldtype sizeof layout input = .ok packed →
    packed.length = (m816_packedsize.{0,0,0,0,0} layout).toOption.getD 0) ∧
  (∀ (fieldcount : TypeLayout → Nat) (fieldoffset : TypeLayout → Nat → Nat)
    (fieldtype : TypeLayout → Nat → TypeLayout) (sizeof : TypeLayout → Nat)
    (layout : TypeLayout) (packed output : Bytes),
    m862_copyfrompacked.{0,0,0,0,0} fieldcount fieldoffset fieldtype sizeof layout packed = .ok output →
    output.length = layout.alignedSize.val.toNat)

/-- Padding errors display the incompatible source and target layouts. -/
def ReinterpretPaddingErrorDisplay : Prop :=
  ∀ (source target : String),
    m741_showerror.{0,0,0,0,0} ⟨source, target⟩ =
      "Padding of type " ++ source ++ " is not compatible with type " ++ target ++ "."

/-- Stringifying an empty byte reinterpretation returns the empty string without a read check. -/
def ReinterpretStringEmpty : Prop :=
  ∀ {T S A R : Type} (empty : R) (callString : Nat → RResult R) (a : ReinterpretArray T S A),
    a.bytes = [] → m937_string.{0,0,0,0,0} empty callString a = .ok empty

/-- A successful reduction over the static channel iterator has ordered column endpoints. -/
def ReinterpretMapreduceInBounds : Prop :=
  ∀ {A F OP X V : Type} {K : Nat}
    (get : A → SCartesianIndex2 → RResult X) (map : F → X → RResult V)
    (combine : OP → V → V → RResult V) (a : A) (f : F) (op : OP)
    (first last : SCartesianIndex2) (blocksize : Nat) (result : V),
    2 ≤ K → 1 ≤ first.i.val → first.i.val ≤ K → first.j.val ≤ last.j.val → 0 < blocksize →
    m956_mapreduceImpl (K := K) get map combine a f op first last blocksize = .ok result →
    1 ≤ first.j.val ∧ first.j.val ≤ last.j.val

/-- Reshaped size and axes add or consume only the first dimension according to element sizes. -/
def ReinterpretShapeDimensions : Prop :=
  (∀ {T S A : Type} (a : ReinterpretArray T S A) (dims : List I64),
    m379_sizeReshaped.{0,0,0,0,0} (fun x y => (JInt.div x y).mapError (fun _ => .divide)) a = .ok dims →
    (a.source.alignedSize > a.target.alignedSize →
      dims = (JInt.lit .i64 (a.source.alignedSize.val / a.target.alignedSize.val)) :: a.size) ∧
    (a.source.alignedSize < a.target.alignedSize → dims = a.size.drop 1) ∧
    (a.source.alignedSize = a.target.alignedSize → dims = a.size)) ∧
  (∀ {T S A : Type} (a : ReinterpretArray T S A), m385_sizeZero.{0,0,0,0,0} a = []) ∧
  (∀ {T S A : Type} (a : ReinterpretArray T S A), m399_axesZero.{0,0,0,0,0} a = [])

/-- Pointer-enabled reads take the pointer route after the readability check. -/
def ReinterpretReadRouting : Prop :=
  ∀ {T S A : Type} (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (ops : PointerReadOps A) (parentIndexStyle : A → IndexStyleModel)
    (fieldtype : TypeLayout → Nat → TypeLayout) (getParent : A → I64 → List I64 → RResult Bytes)
    (a : ReinterpretArray T S A) (i : I64) (tail : List I64),
    a.readable = true → m421_checkPtrIndexable.{0,0,0,0,0} a = true →
    m436_getindex.{0,0,0,0,0} checkbounds ops parentIndexStyle fieldtype getParent i tail a =
      m461_getindexPtr.{0,0,0,0,0} ops a (i :: tail)

/-- Pointer-enabled writes take the pointer route after the writability check. -/
def ReinterpretWriteRouting : Prop :=
  ∀ {T S A V : Type} (checkWritable : ReinterpretArray T S A → RResult Unit)
    (ops : PointerWriteOps A) (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (convertValue : TypeLayout → V → RResult Bytes) (setParent : A → Bytes → RResult A)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (a : ReinterpretArray T S A) (value : V) (i : I64) (tail : List I64),
    m421_checkPtrIndexable.{0,0,0,0,0} a = true →
    m582_setindex.{0,0,0,0,0} checkWritable ops fieldcount fieldoffset fieldtype convertValue setParent
      checkbounds a value i tail = do
      checkWritable a
      m610_setindexPtr.{0,0,0,0,0} ops a (← convertValue a.target value) (i :: tail)

/-- Static Cartesian routing translates the channel coordinate through the parent axes. -/
def ReinterpretCartesianRouting : Prop :=
  ∀ {A : Type} (eachOuter : IndexStyleModel → A → List I64) (axes : A → List Axis)
    (first : List I64 → I64) (cartesianIndices : List Axis → I64 → List I64)
    (style : IndexStyleModel) (a : A) (index : SCartesianIndex2),
    let k := index.j - first (eachOuter style a)
    let tailAxes := (axes a).drop 1
    m359_scartesian2Trailing.{0,0,0,0,0} eachOuter axes first cartesianIndices style a index =
      match tailAxes with
      | [axis] => [axis.first + k]
      | _ => cartesianIndices tailAxes (k + JInt.lit .i64 1)

/-- Parent indexability dispatch follows each specialized parent method. -/
def ReinterpretPointerEligibility : Prop :=
  (∀ {T S A : Type} (a : ReinterpretArray T S A),
    m421_checkPtrIndexable.{0,0,0,0,0} a =
      if a.target.alignedSize = a.source.alignedSize then false else a.pointerParent) ∧
  (∀ {A : Type} (checkParent : A → Bool) (a : A), m425_checkPtrReshaped.{0,0,0,0,0} checkParent a = checkParent a) ∧
  (∀ {A : Type} (checkParent : A → Bool) (a : A), m426_checkPtrSubarray.{0,0,0,0,0} checkParent a = checkParent a) ∧
  (∀ {A : Type} (a : A), m427_checkPtrDense.{0,0,0,1,0} a = true) ∧
  (∀ {A : Type} (a : A), m428_checkPtrAbstract.{0,0,0,0,1} a = false)

/-- Ordinary `isassigned` rejects out-of-bounds indices before checking storage. -/
def ReinterpretIsAssignedBounds : Prop :=
  ∀ {T S A : Type} (checkbounds : ReinterpretArray T S A → List I64 → Bool)
    (a : ReinterpretArray T S A) (indices : List I64),
    checkbounds a indices = false → m432_isassigned.{0,0,0,0,0} checkbounds a indices = false

/-- Every non-padding byte map has one entry per aligned storage byte. -/
def ReinterpretPaddingLayout : Prop :=
  ∀ (layout : TypeLayout) (used : List Bool),
    m750_nonPaddingBytes.{0,0,0,0,0} layout = .ok used → used.length = layout.alignedSize.val.toNat



/-- Stride methods preserve the parent's stride calculation and reject non-integral byte divisions. -/
def ReinterpretStrideComponents : Prop :=
  (∀ {A : Type} (size : A → List I64) (sizeToStrides : I64 → List I64 → List I64) (a : A),
    m207_strides.{0,0,0,0,0} size sizeToStrides a = sizeToStrides (JInt.lit .i64 1) (size a)) ∧
  (∀ {T S A : Type} (contiguous : A → Bool) (sizeToStrides : I64 → List I64 → List I64)
    (parentStrides : A → List I64) (parentElsize : A → I64)
    (divrem : I64 → I64 → RResult (I64 × I64)) (iszero : I64 → Bool)
    (a : ReinterpretArray T S A),
    contiguous a.parent = true →
    m211_strides.{0,0,0,0,0} contiguous sizeToStrides parentStrides parentElsize divrem iszero a =
      .ok (sizeToStrides (JInt.lit .i64 1) a.size)) ∧
  (∀ (divrem : Nat → Nat → RResult (Nat × Nat)) (iszero : Nat → Bool)
    (stride elementSize quotient remainder : Nat),
    divrem stride elementSize = .ok (quotient, remainder) → iszero remainder = false →
    m225_checkedStrides.{0,0,0,0,0} divrem iszero [stride] elementSize = .error .nonIntegralStride)

/-- Readability and writability checks reject an incompatible padding relation. -/
def ReinterpretPaddingChecks : Prop :=
  (∀ {T S A : Type} (a : ReinterpretArray T S A),
    a.readable = true → m237_checkReadable.{0,0,0,0,0} a = .ok ()) ∧
  (∀ {T S A : Type} (a : ReinterpretArray T S A),
    a.readable = false → m772_arraySubpadding.{0,0,0,0,0} a.target a.source = .ok false →
      m237_checkReadable.{0,0,0,0,0} a = .error .padding) ∧
  (∀ {T S A : Type} (a : ReinterpretArray T S A),
    a.writable = true → m244_checkWritable.{0,0,0,0,0} a = .ok ()) ∧
  (∀ {T S A : Type} (a : ReinterpretArray T S A),
    a.writable = false → m772_arraySubpadding.{0,0,0,0,0} a.source a.target = .ok false →
      m244_checkWritable.{0,0,0,0,0} a = .error .padding)

/-- Matching static Cartesian styles retain the same channel width. -/
def ReinterpretIndexCombination : Prop :=
  ∀ {K : Nat} (left right : IndexStyleModel),
    m273_combineStyle.{0,0,0,0,0} (K := K) left right = .staticCartesian K

/-- The iterator constructor, boundary indices, bounds checks and state step follow its axes. -/
def ReinterpretCartesianOperations : Prop :=
  (∀ (K : I64) (index : SCartesianIndex2),
    m280_nextIndex.{0,0,0,0,0} K index =
      if index.i < K then ⟨index.i + JInt.lit .i64 1, index.j⟩
      else ⟨JInt.lit .i64 1, index.j + JInt.lit .i64 1⟩) ∧
  (∀ (K : I64) (index : SCartesianIndex2),
    m282_prevIndex.{0,0,0,0,0} K index =
      if JInt.lit .i64 1 < index.i then ⟨index.i - JInt.lit .i64 1, index.j⟩
      else ⟨K, index.j - JInt.lit .i64 1⟩) ∧
  (∀ (K : Nat) (indices : List I64),
    m288_indicesConstructor.{0,0,0,0,0} K indices =
      if 1 < K then .ok ⟨indices⟩ else .error .assertion) ∧
  (∀ {T S A : Type} {K : Nat} (each : IndexStyleModel → A → List I64)
    (construct : List I64 → RResult (SCartesianIndices2 K)) (a : ReinterpretArray T S A),
    m290_eachindexReshaped.{0,0,0,0,0} each construct a = construct (each .linear a.parent)) ∧
  (∀ {A : Type} {K : Nat} (each : IndexStyleModel → A → List I64)
    (mismatch : List Axis → List (List Axis) → RResult (SCartesianIndices2 K))
    (style : IndexStyleModel) (a : A) (axes : A → List Axis),
    m291_eachindex.{0,0,0,0,0} each mismatch style a [] axes = .ok ⟨each style a⟩) ∧
  (∀ {K : Nat} (first : List I64 → RResult I64) (iter : SCartesianIndices2 K) (item : I64),
    first iter.indices2 = .ok item →
    m301_indicesFirst.{0,0,0,0,0} first iter = .ok ⟨JInt.lit .i64 1, item⟩) ∧
  (∀ {K : Nat} (last : List I64 → RResult I64) (iter : SCartesianIndices2 K) (item : I64),
    last iter.indices2 = .ok item →
    m302_indicesLast.{0,0,0,0,0} last iter = .ok ⟨JInt.lit .i64 K, item⟩) ∧
  (∀ {K : Nat} (checkbounds : SCartesianIndices2 K → I64 → I64 → Bool)
    (get : List I64 → I64 → RResult I64) (iter : SCartesianIndices2 K) (i j : I64),
    checkbounds iter i j = false → m304_indicesGet.{0,0,0,0,0} checkbounds get iter i j = .error .bounds) ∧
  (∀ {K : Nat} {σ : Type} (iterate : List I64 → σ → Option (I64 × σ))
    (iter : SCartesianIndices2 K) (state1 item2 : I64) (state2 : σ),
    state1 < JInt.lit .i64 K →
    m316_indicesIterateState.{0,0,0,0,0} iterate iter state1 item2 state2 =
      some (⟨state1 + JInt.lit .i64 1, item2⟩,
        (state1 + JInt.lit .i64 1, item2, state2)))

/-- Unaliasing copies the parent and preserves the view unless the element types coincide. -/
def ReinterpretUnaliasCopy : Prop :=
  (∀ {T S A : Type} (copy : ArrayInput A → RResult (ArrayInput A))
    (a : ReinterpretArray T S (ArrayInput A)) (p : ArrayInput A),
    a.target.id = a.source.id → copy a.parent = .ok p →
      m371_unaliascopy.{0,0,0,0,0} copy a = .ok (.parent p)) ∧
  (∀ {T S A : Type} (copy : ArrayInput A → RResult (ArrayInput A))
    (a : ReinterpretArray T S (ArrayInput A)) (p : ArrayInput A),
    a.target.id = a.source.id → copy a.parent = .ok p →
      m372_unaliascopyReshaped.{0,0,0,0,0} copy a = .ok (.parent p))

/-- Non-reshape size and axes retain the parent's trailing dimensions; reshape axes follow the channel ratio. -/
def ReinterpretParentDimensions : Prop :=
  (∀ {T S A : Type} (divide : I64 → I64 → RResult I64) (a : ReinterpretArray T S A)
    (dims : List I64),
    m374_sizeNonReshaped.{0,0,0,0,0} divide a = .ok dims → dims.drop 1 = a.size.drop 1) ∧
  (∀ {T S A : Type} (divide : I64 → I64 → RResult I64) (oftype : Axis → I64 → Axis)
    (a : ReinterpretArray T S A) (axes : List Axis),
    m387_axesNonReshaped.{0,0,0,0,0} divide oftype a = .ok axes → axes.drop 1 = a.axes.drop 1) ∧
  (∀ {T S A : Type} (divide : I64 → I64 → RResult I64) (a : ReinterpretArray T S A)
    (axes : List Axis),
    m393_axesReshaped.{0,0,0,0,0} divide a = .ok axes →
      (a.source.alignedSize < a.target.alignedSize → axes = a.axes.drop 1) ∧
      (a.source.alignedSize = a.target.alignedSize → axes = a.axes))

/-- Element-size metadata uses the parent size only when the target and source sizes agree. -/
def ReinterpretElementSize : Prop :=
  ∀ (parentElsize targetSize sourceSize : Nat),
    m403_elsize.{0,0,0,0,0} parentElsize targetSize sourceSize =
      if targetSize == sourceSize then parentElsize else targetSize

/-- Successful reshaped getters return one target-sized element. -/
def ReinterpretReshapedGetWindow : Prop :=
  ∀ {T S A : Type} (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (fieldtype : TypeLayout → Nat → TypeLayout) (getParent : A → I64 → List I64 → RResult Bytes)
    (parentIndexStyle : A → IndexStyleModel) (a : ReinterpretArray T S A) (i : I64)
    (tail : List I64) (result : Bytes),
    a.reshaped = true → a.target.singleton = false →
    m527_getindexReshaped.{0,0,0,0,0} checkbounds fieldtype getParent parentIndexStyle a i tail = .ok result →
    result.length = a.target.alignedSize.val.toNat

/-- Cartesian assignment updates only the selected target window in its parent element. -/
def ReinterpretCartesianSet : Prop :=
  ∀ {T S A V : Type} (checkWritable : ReinterpretArray T S A → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (parentGet : A → I64 → RResult Bytes)
    (parentSet : A → I64 → Bytes → RResult A) (a : ReinterpretArray T S A)
    (value : V) (encoded old : Bytes) (index : SCartesianIndex2)
    (parent : A) (updated : ReinterpretArray T S A),
    checkWritable a = .ok () → convertValue a.target value = .ok encoded →
    parentGet a.parent index.j = .ok old →
    parentSet a.parent index.j (overwriteBytes old (index.i.val - 1).toNat encoded) = .ok parent →
    m598_setindexCartesian.{0,0,0,0,0} checkWritable convertValue parentGet parentSet a value index = .ok updated →
    updated.parent = parent

/-- Successful reshaped assignments preserve the parent byte-image size. -/
def ReinterpretReshapedSetWindow : Prop :=
  ∀ {T S A V : Type} (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (setParent : A → Bytes → RResult A)
    (a : ReinterpretArray T S A) (value : V) (i : I64) (tail : List I64)
    (updated : ReinterpretArray T S A),
    a.reshaped = true →
    m688_setindexReshaped.{0,0,0,0,0} fieldcount fieldoffset fieldtype checkbounds convertValue
      setParent a value i tail = .ok updated → updated.bytes.length = a.bytes.length

/-- Padding helpers preserve layout width and reject non-integral stride-independent layouts. -/
def ReinterpretPaddingHelpers : Prop :=
  (∀ (layout : TypeLayout), m824_ispacked.{0,0,0,0,0} layout = !layout.datatypePadding) ∧
  (∀ (layout : TypeLayout),
    m828_hasBitPadding.{0,0,0,0,0} layout =
      if layout.primitive then layout.bits % 8 != 0
      else if layout.union then layout.unionBitPadding.any id else layout.fields.any FieldLayout.bitPadding) ∧
  (∀ (output input : TypeLayout),
    m812_structSubpadding.{0,0,0,0,0} output input = do
      let outputUsed ← m750_nonPaddingBytes.{0,0,0,0,0} output
      let inputUsed ← m750_nonPaddingBytes.{0,0,0,0,0} input
      pure (outputUsed == inputUsed)) ∧
  (∀ (layout : TypeLayout), layout.datatypePadding = false →
    m816_packedsize.{0,0,0,0,0} layout = .ok layout.alignedSize.val.toNat) ∧
  (∀ (source target : TypeLayout), m824_ispacked.{0,0,0,0,0} target = true →
    m772_arraySubpadding.{0,0,0,0,0} source target = .ok true) ∧
  (∀ (layout : TypeLayout) (offset : Nat) (used result : List Bool),
    m756_fillNonpadding.{0,0,0,0,0} layout offset used = result →
    result =
      if layout.primitive then
        setTrueOffsets used ((List.range ((layout.bits + 7) / 8)).map (· + offset))
      else
        layout.fields.foldl (fun bytes field =>
          setTrueOffsets bytes (field.usedOffsets.map (fun i => i + offset + field.offset))) used)

/-- Padding conversion returns an output with the target's aligned storage width. -/
def ReinterpretPaddingPacked : Prop :=
  ∀ (fieldcount : TypeLayout → Nat) (fieldoffset : TypeLayout → Nat → Nat)
    (fieldtype : TypeLayout → Nat → TypeLayout) (output input : TypeLayout)
    (bytes result : Bytes),
    m913_reinterpretPadding.{0,0,0,0,0} fieldcount fieldoffset fieldtype output input bytes = .ok result →
    result.length = output.alignedSize.val.toNat

/-- The non-byte-aligned scalar predicate is true exactly for equal-size primitive layouts. -/
def ReinterpretScalarApplicability : Prop :=
  ∀ (target source : TypeLayout),
    m469_scalarApplicable.{0,0,0,0,0} target source =
      (target.primitive && source.primitive && target.bits == source.bits)

/-- The custom reduction uses the empty reduction for no columns and the pairwise worker otherwise. -/
def ReinterpretMapreduceRoutes : Prop :=
  ∀ {A F OP X V E : Type} {K : Nat}
    (eachindex : IndexStyleModel → A → List (SCartesianIndices2 K))
    (columnCount : List (SCartesianIndices2 K) → Nat) (iteratorEltype : A → E)
    (empty : F → OP → A → E → RResult V)
    (first last : List (SCartesianIndices2 K) → SCartesianIndex2)
    (blocksize : F → OP → Nat) (get : A → SCartesianIndex2 → RResult X)
    (map : F → X → RResult V) (combine : OP → V → V → RResult V)
    (f : F) (op : OP) (style : IndexStyleModel) (a : A),
    m946_mapreduce eachindex columnCount iteratorEltype empty first last blocksize get map combine f op style a =
      if columnCount (eachindex style a) == 0 then empty f op a (iteratorEltype a)
      else m984_mapreduceDefault (K := K) blocksize get map combine a f op
        (first (eachindex style a)) (last (eachindex style a))

/-- Zero-dimensional scalar assignment reinterprets the value into the parent element. -/
def ReinterpretZeroSet : Prop :=
  ∀ {T S A V : Type} (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (isScalar : TypeLayout → TypeLayout → Bool) (convertValue : TypeLayout → V → RResult Bytes)
    (setParent : A → Bytes → RResult A) (checkWritable : ReinterpretArray T S A → RResult Unit)
    (ops : PointerWriteOps A) (parentIndexStyle : A → IndexStyleModel)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (a : ReinterpretArray T S A) (value : V) (encoded sourceBytes : Bytes) (parent : A),
    isScalar a.target a.source = true → convertValue a.target value = .ok encoded →
    m882_reinterpret.{0,0,0,0,0} fieldcount fieldoffset fieldtype a.source a.target encoded = .ok sourceBytes →
    setParent a.parent (overwriteBytes a.bytes 0 sourceBytes) = .ok parent →
    m572_setindexZero.{0,0,0,0,0} fieldcount fieldoffset fieldtype isScalar convertValue setParent
      checkWritable ops parentIndexStyle toSubscripts firstindex checkbounds a value =
      .ok { a with parent := parent, bytes := overwriteBytes a.bytes 0 sourceBytes }

def entries : List JuliaLean.Registry.Entry := [
  { id := "reinterpretarrays-ra-getindex-bytes", juliaFile := "base/reinterpretarray.jl", juliaFns := ["getindex(::ReinterpretArray, i1, tailinds...)", "_getindex_ra(::NonReshapedReinterpretArray)"],
    statement := "reinterpret(T, A)[i1, J...] returns exactly the sizeof(T) parent bytes starting at byte (i1-1)*sizeof(T) of column J (all three _getindex_ra branches), and throws BoundsError outside 1:size(R, 1).", source := "base/reinterpretarray.jl:35-39 (reinterpret docstring: a view with the same binary data)", status := .todo,
    prop := ``RaGetCorrect },
  { id := "reinterpretarrays-ra-setindex-bytes", juliaFile := "base/reinterpretarray.jl", juliaFns := ["setindex!(::ReinterpretArray, v, i1, tailinds...)", "_setindex_ra!(::NonReshapedReinterpretArray)"],
    statement := "reinterpret(T, A)[i1, J...] = v changes exactly the sizeof(T) parent bytes starting at byte (i1-1)*sizeof(T) of column J to the bytes of v and leaves every other byte, including the neighbouring bytes of partially overwritten parent elements, unchanged; out of bounds it throws BoundsError.", source := "base/reinterpretarray.jl:35-39 (reinterpret docstring), base/reshapedarray.jl:70-73 (shared data: setting elements of one alters the other)", status := .todo,
    prop := ``RaSetCorrect },
  { id := "reinterpretarrays-size-overflow", juliaFile := "base/reinterpretarray.jl", juliaFns := ["reinterpret(T, ::AbstractArray)", "size(::NonReshapedReinterpretArray)", "axes(::NonReshapedReinterpretArray)"],
    statement := "reinterpret(T, A) either throws or has size(R, 1) * sizeof(T) == size(A, 1) * sizeof(eltype(A)).", source := "base/reinterpretarray.jl:3-7 (ReinterpretArray docstring: the array is compressed/expanded in the first dimension), 76-78 (non-integral first dimension error)", status := .todo,
    prop := ``ReinterpretSizeOverflow },
  { id := "memsafety-reinterpretarray-getindex", juliaFile := "base/reinterpretarray.jl", juliaFns := ["getindex(::ReinterpretArray)", "_getindex_ptr", "_getindex_ra"],
    statement := "Every pointer and parent-element read used to assemble a checked ReinterpretArray element stays in its parent byte image.", source := "reinterpret docstring at base/reinterpretarray.jl:35-39; checks and branches at lines 433-567", status := .todo,
    prop := ``ReinterpretGetMemorySafe },
  { id := "memsafety-reinterpretarray-setindex", juliaFile := "base/reinterpretarray.jl", juliaFns := ["setindex!(::ReinterpretArray)", "_setindex_ptr!", "_setindex_ra!"],
    statement := "Every pointer and parent-element write used for a checked ReinterpretArray element stays in its parent byte image.", source := "reinterpret and shared-data docstrings; base/reinterpretarray.jl:579-730", status := .todo,
    prop := ``ReinterpretSetMemorySafe },
  { id := "memsafety-reinterpretarray-mapreduce", juliaFile := "base/reinterpretarray.jl", juliaFns := ["_mapreduce", "mapreduce_impl(::SCartesianIndex2)"],
    statement := "The sequential and pairwise branches visit only the K by n indices returned by eachindex.", source := "base/reinterpretarray.jl:943-978", status := .todo,
    prop := ``ReinterpretMapreduceInBounds },
  { id := "multidimcov-reinterpretarray-packed-copy", juliaFile := "base/reinterpretarray.jl", juliaFns := ["_copytopacked!, _copyfrompacked!"],
    statement := "Packed copying traverses fields in order, copies packed fields directly, recurses for padded fields, and advances exact byte offsets.", source := "base/reinterpretarray.jl:839-877", status := .todo,
    prop := ``ReinterpretPackedCopies },
  { id := "reinterpretarray-rank-shape", juliaFile := "base/reinterpretarray.jl", juliaFns := ["reinterpret(::Type,::AbstractArray)", "reinterpret(reshape,::Type,::AbstractArray)"],
    statement := "Successful constructors keep the non-reshape rank and adjust reshape rank only by the element-size ratio.", source := "base/reinterpretarray.jl:73-144; constructor invariant", status := .todo, prop := ``ReinterpretRankShape },
  { id := "reinterpretarray-constructor-validation", juliaFile := "base/reinterpretarray.jl", juliaFns := ["reinterpret(::Type,::AbstractArray)", "reinterpret(reshape,::Type,::AbstractArray)"],
    statement := "Both constructors reject non-bits source or target layouts in source order.", source := "base/reinterpretarray.jl:73-103, 107-144", status := .todo, prop := ``ReinterpretConstructorValidation },
  { id := "reinterpretarray-padding-flags", juliaFile := "base/reinterpretarray.jl", juliaFns := ["array_subpadding", "check_readable", "check_writable"],
    statement := "The constructor readability and writability flags agree with the source and target padding relation.", source := "base/reinterpretarray.jl:775-813, 234-251", status := .todo, prop := ``ReinterpretPaddingFlags },
  { id := "reinterpretarray-stride-behavior", juliaFile := "base/reinterpretarray.jl", juliaFns := ["stride", "_checked_strides"],
    statement := "Stride lookup returns the selected dimension stride or array length, and checked division rejects remainders.", source := "base/reinterpretarray.jl:208-209, 225-230", status := .todo, prop := ``ReinterpretStrideBehavior },
  { id := "reinterpretarray-index-style", juliaFile := "base/reinterpretarray.jl", juliaFns := ["IndexStyle(::Type{ReinterpretArray})"],
    statement := "Linear indexing is retained except when reshape expands the first dimension, where static Cartesian indexing is used for a linear parent.", source := "base/reinterpretarray.jl:263-270", status := .todo, prop := ``ReinterpretIndexStyle },
  { id := "reinterpretarray-cartesian-iteration", juliaFile := "base/reinterpretarray.jl", juliaFns := ["SCartesianIndices2", "iterate(::SCartesianIndices2)", "size(::SCartesianIndices2)", "axes(::SCartesianIndices2)"],
    statement := "The static Cartesian iterator exposes its channel and parent dimensions and begins at the first parent index.", source := "base/reinterpretarray.jl:288-326; iterator invariant", status := .todo, prop := ``ReinterpretCartesianIteration },
  { id := "reinterpretarray-nested-dispatch", juliaFile := "base/reinterpretarray.jl", juliaFns := ["reinterpret(::Type,::NonReshapedReinterpretArray)", "reinterpret(reshape,::Type,::ReshapedReinterpretArray)"],
    statement := "Nested reinterpretation unwraps the existing view when element sizes match and otherwise retains the nested view.", source := "base/reinterpretarray.jl:190-194", status := .todo, prop := ``ReinterpretNestedDispatch },
  { id := "reinterpretarray-identity-specializations", juliaFile := "base/reinterpretarray.jl", juliaFns := ["reinterpret(::Type,::AbstractArray{T})", "reinterpret(reshape,::Type,::AbstractArray{T})"],
    statement := "Reinterpreting an array with its existing element type returns the same array.", source := "base/reinterpretarray.jl:104, 145", status := .todo, prop := ``ReinterpretIdentity },
  { id := "reinterpretarray-shape-dimensions", juliaFile := "base/reinterpretarray.jl", juliaFns := ["size", "axes"],
    statement := "Reshaped reinterpretation adds or consumes the first dimension while preserving the remaining parent dimensions.", source := "base/reinterpretarray.jl:374-399; reinterpret(reshape) docstring", status := .todo, prop := ``ReinterpretShapeDimensions },
  { id := "reinterpretarray-parent-metadata", juliaFile := "base/reinterpretarray.jl", juliaFns := ["parent", "dataids", "has_offset_axes", "elsize"],
    statement := "Parent identity and alias metadata come from the underlying array.", source := "base/reinterpretarray.jl:369-370, 401, 403", status := .todo, prop := ``ReinterpretParentMetadata },
  { id := "reinterpretarray-pointer-metadata", juliaFile := "base/reinterpretarray.jl", juliaFns := ["cconvert", "unsafe_convert", "check_ptr_indexable"],
    statement := "Pointer conversion follows the parent conversion and specialized parent-indexability rules.", source := "base/reinterpretarray.jl:410-428", status := .todo, prop := ``ReinterpretPointerMetadata },
  { id := "reinterpretarray-pointer-eligibility", juliaFile := "base/reinterpretarray.jl", juliaFns := ["check_ptr_indexable"],
    statement := "Pointer access requires differing element sizes and follows the parent type dispatch.", source := "base/reinterpretarray.jl:421-428", status := .todo, prop := ``ReinterpretPointerEligibility },
  { id := "reinterpretarray-read-routing", juliaFile := "base/reinterpretarray.jl", juliaFns := ["getindex", "_getindex_ptr"],
    statement := "Readable pointer-indexable views use the pointer getter after the readability check.", source := "base/reinterpretarray.jl:436-467", status := .todo, prop := ``ReinterpretReadRouting },
  { id := "reinterpretarray-write-routing", juliaFile := "base/reinterpretarray.jl", juliaFns := ["setindex!", "_setindex_ptr!"],
    statement := "Writable pointer-indexable views use the pointer setter after the writability check.", source := "base/reinterpretarray.jl:582-617", status := .todo, prop := ``ReinterpretWriteRouting },
  { id := "reinterpretarray-cartesian-routing", juliaFile := "base/reinterpretarray.jl", juliaFns := ["_getindex", "_setindex!", "_scartesian2_trailing"],
    statement := "Static Cartesian indices map the channel coordinate and parent trailing axes to the underlying array indices.", source := "base/reinterpretarray.jl:333-362", status := .todo, prop := ``ReinterpretCartesianRouting },
  { id := "reinterpretarray-isassigned-bounds", juliaFile := "base/reinterpretarray.jl", juliaFns := ["isassigned"],
    statement := "Out-of-bounds ordinary isassigned queries return false before storage checks.", source := "base/reinterpretarray.jl:432", status := .todo, prop := ``ReinterpretIsAssignedBounds },
  { id := "reinterpretarray-padding-layout", juliaFile := "base/reinterpretarray.jl", juliaFns := ["non_padding_bytes", "fill_nonpadding_bytes!", "packedsize", "ispacked", "has_bit_padding"],
    statement := "Padding maps contain one flag for every aligned storage byte.", source := "base/reinterpretarray.jl:750-831", status := .todo, prop := ``ReinterpretPaddingLayout },
  { id := "reinterpretarray-scalar-roundtrip", juliaFile := "base/reinterpretarray.jl", juliaFns := ["_reinterpret"],
    statement := "Equal-size packed bit layouts reinterpret to the same byte sequence.", source := "base/reinterpretarray.jl:882-909", status := .todo, prop := ``ReinterpretScalarRoundtrip },
  { id := "reinterpretarray-padding-error-display", juliaFile := "base/reinterpretarray.jl", juliaFns := ["showerror(::PaddingError)"],
    statement := "Padding errors name the source and target layouts in the displayed message.", source := "base/reinterpretarray.jl:741-743", status := .todo, prop := ``ReinterpretPaddingErrorDisplay },
  { id := "reinterpretarray-empty-string", juliaFile := "base/reinterpretarray.jl", juliaFns := ["String(::ReinterpretArray{UInt8})"],
    statement := "String conversion of an empty byte reinterpretation returns the empty string without checking readability.", source := "base/reinterpretarray.jl:937-942", status := .todo, prop := ``ReinterpretStringEmpty },
  { id := "reinterpretarray-stride-components", juliaFile := "base/reinterpretarray.jl", juliaFns := ["strides", "_checked_strides"],
    statement := "Stride construction follows parent size-to-strides, retains contiguous parent strides, and rejects remainders in byte-to-element stride conversion.", source := "base/reinterpretarray.jl:207-230", status := .todo, prop := ``ReinterpretStrideComponents },
  { id := "reinterpretarray-padding-checks", juliaFile := "base/reinterpretarray.jl", juliaFns := ["check_readable", "check_writable"],
    statement := "Read and write access reject incompatible source and target padding layouts.", source := "base/reinterpretarray.jl:234-251", status := .todo, prop := ``ReinterpretPaddingChecks },
  { id := "reinterpretarray-index-combination", juliaFile := "base/reinterpretarray.jl", juliaFns := ["IndexStyle(::IndexSCartesian2,::IndexSCartesian2)"],
    statement := "Matching static Cartesian index styles retain their channel width.", source := "base/reinterpretarray.jl:273", status := .todo, prop := ``ReinterpretIndexCombination },
  { id := "reinterpretarray-cartesian-operations", juliaFile := "base/reinterpretarray.jl", juliaFns := ["nextind", "prevind", "SCartesianIndices2", "eachindex", "first", "last", "getindex", "iterate"],
    statement := "Static Cartesian iteration validates its channel count, reports parent endpoints, checks bounds, and advances the channel state.", source := "base/reinterpretarray.jl:280-326", status := .todo, prop := ``ReinterpretCartesianOperations },
  { id := "reinterpretarray-unalias-copy", juliaFile := "base/reinterpretarray.jl", juliaFns := ["unaliascopy(::NonReshapedReinterpretArray)", "unaliascopy(::ReshapedReinterpretArray)"],
    statement := "Unaliasing copies the parent and returns the parent view when element types match.", source := "base/reinterpretarray.jl:371-372", status := .todo, prop := ``ReinterpretUnaliasCopy },
  { id := "reinterpretarray-parent-dimensions", juliaFile := "base/reinterpretarray.jl", juliaFns := ["size", "axes"],
    statement := "Non-reshape size and axes keep parent trailing dimensions, while reshape axes consume or add the channel dimension.", source := "base/reinterpretarray.jl:374-399", status := .todo, prop := ``ReinterpretParentDimensions },
  { id := "reinterpretarray-elsize", juliaFile := "base/reinterpretarray.jl", juliaFns := ["elsize"],
    statement := "Element-size metadata uses parent elsize for equal-sized types and target size otherwise.", source := "base/reinterpretarray.jl:403", status := .todo, prop := ``ReinterpretElementSize },
  { id := "reinterpretarray-reshaped-get", juliaFile := "base/reinterpretarray.jl", juliaFns := ["_getindex_ra(::ReshapedReinterpretArray)"],
    statement := "Successful reshaped element reads return one target-sized value.", source := "base/reinterpretarray.jl:527-570", status := .todo, prop := ``ReinterpretReshapedGetWindow },
  { id := "reinterpretarray-cartesian-set", juliaFile := "base/reinterpretarray.jl", juliaFns := ["setindex!(::ReshapedReinterpretArray,::SCartesianIndex2)"],
    statement := "Cartesian assignment stores the converted target element into the selected parent element.", source := "base/reinterpretarray.jl:598-608", status := .todo, prop := ``ReinterpretCartesianSet },
  { id := "reinterpretarray-reshaped-set", juliaFile := "base/reinterpretarray.jl", juliaFns := ["_setindex_ra!(::ReshapedReinterpretArray)"],
    statement := "Successful reshaped assignment preserves the parent storage image size.", source := "base/reinterpretarray.jl:688-734", status := .todo, prop := ``ReinterpretReshapedSetWindow },
  { id := "reinterpretarray-padding-helpers", juliaFile := "base/reinterpretarray.jl", juliaFns := ["fill_nonpadding_bytes!", "array_subpadding", "struct_subpadding", "packedsize", "ispacked", "has_bit_padding"],
    statement := "Padding helpers preserve byte-layout width, packed-size semantics, and subpadding compatibility.", source := "base/reinterpretarray.jl:759-831", status := .todo, prop := ``ReinterpretPaddingHelpers },
  { id := "reinterpretarray-padding-conversion", juliaFile := "base/reinterpretarray.jl", juliaFns := ["_reinterpret_padding"],
    statement := "Padding-aware reinterpretation returns target storage of its aligned width.", source := "base/reinterpretarray.jl:913-935", status := .todo, prop := ``ReinterpretPaddingPacked },
  { id := "reinterpretarray-scalar-applicability", juliaFile := "base/reinterpretarray.jl", juliaFns := ["_is_scalar_reinterpret_applicable"],
    statement := "Scalar reinterpretation applies exactly to primitive layouts with equal bit sizes.", source := "base/reinterpretarray.jl:469-471", status := .todo, prop := ``ReinterpretScalarApplicability },
  { id := "reinterpretarray-mapreduce-routing", juliaFile := "base/reinterpretarray.jl", juliaFns := ["_mapreduce"],
    statement := "The custom reduction delegates empty iterators to the empty reduction and nonempty iterators to the pairwise worker.", source := "base/reinterpretarray.jl:946-954", status := .todo, prop := ``ReinterpretMapreduceRoutes },
  { id := "reinterpretarray-zero-set", juliaFile := "base/reinterpretarray.jl", juliaFns := ["setindex!(::NonReshapedReinterpretArray{T,0})"],
    statement := "Scalar zero-dimensional assignment converts the target value to the parent element representation.", source := "base/reinterpretarray.jl:572-578", status := .todo, prop := ``ReinterpretZeroSet },
]

/-!
## Method → property

  14 throwbits -> Nothing to promise
  18 throwsize0 -> Nothing to promise
  23 throwsingleton -> Nothing to promise
  27 throwbitpadding -> Nothing to promise
  73 reinterpret -> ReinterpretConstructorValidation
  74 thrownonint -> Nothing to promise
  80 throwaxes1 -> Nothing to promise
  104 reinterpret -> ReinterpretIdentity
  107 ReinterpretArray{T} -> ReinterpretConstructorValidation
  108 throwintmult -> Nothing to promise
  113 throwsize1 -> Nothing to promise
  119 throwfromsingleton -> Nothing to promise
  145 reinterpret -> ReinterpretIdentity
  188 reinterpret -> Nothing to promise
  190 reinterpret -> Nothing to promise
  191 reinterpret -> ReinterpretNestedDispatch
  207 strides -> ReinterpretStrideComponents
  208 stride -> ReinterpretStrideBehavior
  211 strides -> ReinterpretStrideComponents
  225 _checked_strides -> ReinterpretStrideComponents
  232 _checkcontiguous -> Nothing to promise
  234 similar -> Nothing to promise
  235 similar -> Nothing to promise
  237 check_readable -> ReinterpretPaddingChecks
  244 check_writable -> ReinterpretPaddingChecks
  263 IndexStyle -> ReinterpretIndexStyle
  266 IndexStyle -> ReinterpretIndexStyle
  273 IndexStyle -> ReinterpretIndexCombination
  279 to_index -> Nothing to promise
  280 nextind -> ReinterpretCartesianOperations
  282 prevind -> ReinterpretCartesianOperations
  288 SCartesianIndices2{K} -> ReinterpretCartesianOperations
  290 eachindex -> ReinterpretCartesianOperations
  291 eachindex -> ReinterpretCartesianOperations
  298 size -> ReinterpretCartesianIteration
  299 axes -> ReinterpretCartesianIteration
  301 first -> ReinterpretCartesianOperations
  302 last -> ReinterpretCartesianOperations
  304 getindex -> ReinterpretCartesianOperations
  309 iterate -> ReinterpretCartesianIteration
  316 iterate -> ReinterpretCartesianOperations
  327 SimdLoop.simd_outer_range -> Nothing to promise
  328 SimdLoop.simd_inner_length -> Nothing to promise
  329 SimdLoop.simd_index -> Nothing to promise
  333 _maybe_reshape -> Nothing to promise
  334 _maybe_reshape -> Nothing to promise
  337 _getindex -> Nothing to promise
  341 _setindex! -> Nothing to promise
  347 _getindex -> Nothing to promise
  352 _setindex! -> Nothing to promise
  359 _scartesian2_trailing -> ReinterpretCartesianRouting
  365 eachindex -> Nothing to promise
  369 parent -> ReinterpretParentMetadata
  370 dataids -> ReinterpretParentMetadata
  371 unaliascopy -> ReinterpretUnaliasCopy
  372 unaliascopy -> ReinterpretUnaliasCopy
  374 size -> ReinterpretParentDimensions
  379 size -> ReinterpretShapeDimensions
  385 size -> ReinterpretShapeDimensions
  387 axes -> ReinterpretParentDimensions
  393 axes -> ReinterpretParentDimensions
  399 axes -> ReinterpretShapeDimensions
  401 has_offset_axes -> ReinterpretParentMetadata
  403 elsize -> ReinterpretElementSize
  410 cconvert -> ReinterpretPointerMetadata
  411 unsafe_convert -> ReinterpretPointerMetadata
  413 getindex -> Nothing to promise
  421 check_ptr_indexable -> ReinterpretPointerEligibility
  425 check_ptr_indexable -> ReinterpretPointerEligibility
  426 check_ptr_indexable -> ReinterpretPointerEligibility
  427 check_ptr_indexable -> ReinterpretPointerEligibility
  428 check_ptr_indexable -> ReinterpretPointerEligibility
  430 getindex -> Nothing to promise
  432 isassigned -> ReinterpretIsAssignedBounds
  433 isassigned -> Nothing to promise
  434 _isassigned_ra -> Nothing to promise
  436 getindex -> ReinterpretReadRouting
  442 getindex -> Nothing to promise
  454 getindex -> Nothing to promise
  461 _getindex_ptr -> ReinterpretReadRouting
  469 _is_scalar_reinterpret_applicable -> ReinterpretScalarApplicability
  473 _getindex_ra -> RaGetCorrect
  527 _getindex_ra -> ReinterpretReshapedGetWindow
  572 setindex! -> Nothing to promise
  580 setindex! -> Nothing to promise
  582 setindex! -> ReinterpretWriteRouting
  588 setindex! -> Nothing to promise
  598 setindex! -> ReinterpretCartesianSet
  610 _setindex_ptr! -> ReinterpretWriteRouting
  619 _setindex_ra! -> RaSetCorrect
  688 _setindex_ra! -> ReinterpretReshapedSetWindow
  741 showerror -> ReinterpretPaddingErrorDisplay
  750 non_padding_bytes -> ReinterpretPaddingLayout
  759 fill_nonpadding_bytes! -> ReinterpretPaddingHelpers
  775 array_subpadding -> ReinterpretPaddingHelpers
  815 struct_subpadding -> ReinterpretPaddingHelpers
  819 packedsize -> ReinterpretPaddingHelpers
  827 ispacked -> ReinterpretPaddingHelpers
  831 has_bit_padding -> ReinterpretPaddingHelpers
  842 _copytopacked! -> ReinterpretPackedCopies
  862 _copyfrompacked! -> ReinterpretPackedCopies
  882 _reinterpret -> ReinterpretScalarRoundtrip
  913 _reinterpret_padding -> ReinterpretPaddingPacked
  937 String -> ReinterpretStringEmpty
  946 _mapreduce -> ReinterpretMapreduceRoutes
  956 mapreduce_impl -> ReinterpretMapreduceInBounds
  984 mapreduce_impl -> Nothing to promise
  990 _totuple -> Nothing to promise
-/

end JuliaLean.Proofs.base.reinterpretarray

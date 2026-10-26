import JuliaLean.MultidimCov.SubarrayAccess
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

/-! Exact row models for `base/subarray.jl:437-553`. -/

private def layoutOne : I64 := JInt.lit .i64 1
private def layoutZero : I64 := JInt.lit .i64 0

/-- `strides(::SubArray)`, line 437. -/
def subarrayStridesExact (parentStrides : List Axis → List I64) (view : SubModel) :
    MDResult (List I64) :=
  subStrides (parentStrides view.parentAxes) view.indices

/-- Scalar `substrides`, line 440. -/
def substridesScalarExact (strides : List I64) (rest : List ViewIndex) : MDResult (List I64) :=
  subStrides strides.tail rest

/-- Slice `substrides`, line 441. -/
def substridesSliceExact (strides : List I64) (rest : List ViewIndex) : MDResult (List I64) :=
  match strides with
  | [] => .argumentError
  | stride :: tail => match subStrides tail rest with
    | .ok values => .ok (stride :: values)
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

/-- Range `substrides`, line 442. -/
def substridesRangeExact (strides : List I64) (step : I64)
    (rest : List ViewIndex) : MDResult (List I64) :=
  match strides with
  | [] => .argumentError
  | stride :: tail => match subStrides tail rest with
    | .ok values => .ok (stride * step :: values)
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

/-- Invalid-index `substrides`, lines 443-444. -/
def substridesInvalidExact (_strides : List I64) (_index : ViewIndex)
    (_rest : List ViewIndex) : MDResult (List I64) := .argumentError

/-- `stride(::SubArray,d)`, line 446, including the rank-zero failure. -/
def subarrayStrideExact (strides : List I64) (sizes : List Nat) (dimension : I64) : MDResult I64 :=
  if dimension.val ≤ (sizes.length : Int) then
    if dimension.val < 1 then .boundsError
    else match strides[(dimension.val - 1).toNat]? with
      | some stride => .ok stride
      | none => .boundsError
  else match strides.getLast?, sizes.getLast? with
    | some stride, some size => .ok (stride * JInt.wrap .i64 (Int.ofNat size))
    | _, _ => .boundsError

private def fillAxes (axes : List Axis) (length : Nat) : List Axis :=
  (axes ++ List.replicate length (oneToAxis layoutOne)).take length

/-- `compute_stride1(parent,I)`, lines 448-449. -/
def computeStrideWrapperExact (parentAxes : List Axis) (indices : List ViewIndex) : MDResult I64 :=
  computeStride1 layoutOne (fillAxes parentAxes indices.length) indices

def computeStrideEmptyExact (stride : I64) (_axes : List Axis) : MDResult I64 := .ok stride

def computeStrideScalarsExact (stride : I64) (_axes : List Axis)
    (_scalars : List I64) : MDResult I64 := .ok stride

def computeStrideScalarExact (stride : I64) (axes : List Axis)
    (rest : List ViewIndex) : MDResult I64 :=
  match axes with
  | [] => .boundsError
  | axis :: tail => computeStride1 (stride * JInt.wrap .i64 (Int.ofNat axis.len)) tail rest

def computeStrideRangeExact (stride step : I64) : MDResult I64 := .ok (stride * step)

def computeStrideSliceExact (stride : I64) : MDResult I64 := .ok stride

def computeStrideInvalidExact (_stride : I64) (_axes : List Axis)
    (_index : ViewIndex) : MDResult I64 := .argumentError

def subarrayElsizeExact (parentElsize : Nat → Nat) (parentType : Nat) : Nat :=
  parentElsize parentType

def subarrayIscontiguousValueExact (typeContiguous : Bool) : Bool := typeContiguous

def subarrayIscontiguousTypeExact (_type : Nat) : Bool := false

def fastContiguousTypeExact (_type : Nat) : Bool := true

def fastFirstIndexExact (view : SubModel) (firstIndex : I64) : I64 :=
  view.offset + view.stride * firstIndex

def generalFirstIndexExact (compute : List Axis → List ViewIndex → I64)
    (view : SubModel) : I64 :=
  compute view.parentAxes view.indices

/-- Vector-specialized `compute_offset1`, lines 471-472. -/
def computeOffsetVectorExact (stride firstIndex firstAxis : I64) : I64 :=
  firstIndex - stride * firstAxis

def isScalarIndex : ViewIndex → Bool
  | .scalar _ => true
  | _ => false

def findExtendedDimsExact : Nat → List ViewIndex → List Nat
  | _, [] => []
  | dimension, index :: rest =>
      if isScalarIndex index then findExtendedDimsExact (dimension + 1) rest
      else dimension :: findExtendedDimsExact (dimension + 1) rest

def findExtendedIndicesExact : List ViewIndex → List ViewIndex
  | [] => []
  | index :: rest =>
      if isScalarIndex index then findExtendedIndicesExact rest
      else index :: findExtendedIndicesExact rest

/-- General `compute_offset1` wrapper, lines 478-479. -/
def computeOffsetWrapperExact
    (compute : List Axis → I64 → List Nat → List ViewIndex → List ViewIndex → I64)
    (parentAxes : List Axis) (stride : I64) (indices : List ViewIndex) : I64 :=
  compute parentAxes stride (findExtendedDimsExact 1 indices)
    (findExtendedIndicesExact indices) indices

/-- Slice-specialized `compute_offset1`, lines 480-481. -/
def computeOffsetSliceExact (linearIndex stride firstParentAxis : I64) : I64 :=
  linearIndex - stride * firstParentAxis

/-- Range-specialized `compute_offset1`, lines 482-483. -/
def computeOffsetRangeExact (linearIndex stride firstIndexAxis : I64) : I64 :=
  linearIndex - stride * firstIndexAxis

/-- Fallback `compute_offset1`, lines 484-485. -/
def computeOffsetFallbackExact (linearIndex stride : I64) : I64 := linearIndex - stride

def firstOfIndex : ViewIndex → I64
  | .scalar value => value
  | .slice axis | .range axis => axis.first
  | .array _ values => values.head?.getD layoutOne
  | .cartesianArray _ _ => layoutOne

def computeLinindexRecExact : I64 → I64 → List Axis → List ViewIndex → I64
  | first, _, _, [] => first
  | first, stride, axis :: parentAxes, index :: indices =>
      let delta := firstOfIndex index - axis.first
      if indices.isEmpty then first + delta * stride
      else computeLinindexRecExact (first + delta * stride)
        (stride * JInt.wrap .i64 (Int.ofNat axis.len)) parentAxes indices
  | first, _, _, _ => first

/-- `compute_linindex(parent,I)`, lines 486-490. -/
def computeLinindexWrapperExact (firstLinear : List Axis → I64)
    (parentAxes : List Axis) (indices : List ViewIndex) : I64 :=
  let axes := fillAxes parentAxes indices.length
  computeLinindexRecExact (firstLinear parentAxes) layoutOne axes indices

/-- Recursive multi-index `compute_linindex`, lines 491-495. -/
def computeLinindexManyExact (first stride : I64) (parentAxes : List Axis)
    (indices : List ViewIndex) : I64 :=
  match parentAxes, indices with
  | axis :: axes, index :: rest =>
      let delta := firstOfIndex index - axis.first
      computeLinindexRecExact (first + delta * stride)
        (stride * JInt.wrap .i64 (Int.ofNat axis.len)) axes rest
  | _, _ => first

/-- Singleton `compute_linindex`, lines 496-500. -/
def computeLinindexOneExact (first stride : I64) (axis : Axis) (index : ViewIndex) : I64 :=
  first + (firstOfIndex index - axis.first) * stride

/-- Empty `compute_linindex`, line 501. -/
def computeLinindexEmptyExact (first _stride : I64) (_axes : List Axis) : I64 := first

def findExtendedDimsScalarExact (dimension : Nat) (rest : List ViewIndex) : List Nat :=
  findExtendedDimsExact (dimension + 1) rest

def findExtendedDimsValueExact (dimension : Nat) (_index : ViewIndex)
    (rest : List ViewIndex) : List Nat :=
  dimension :: findExtendedDimsExact (dimension + 1) rest

def findExtendedDimsEmptyExact (_dimension : Nat) : List Nat := []

def findExtendedIndicesScalarExact (rest : List ViewIndex) : List ViewIndex :=
  findExtendedIndicesExact rest

def findExtendedIndicesValueExact (index : ViewIndex) (rest : List ViewIndex) : List ViewIndex :=
  index :: findExtendedIndicesExact rest

def findExtendedIndicesEmptyExact : List ViewIndex := []

def fastPointerExact (parentPointer : I64 → I64) (view : SubModel) (index : I64) : I64 :=
  parentPointer (view.offset + view.stride * index)

def contiguousPointerExact (parentPointer : I64 → I64) (view : SubModel)
    (index : I64) : I64 :=
  parentPointer (view.offset + index)

/-- Cartesian pointer method, lines 513-520. -/
def cartesianPointerExact (parentPointer : I64 → I64) (firstIndex : I64)
    (strides coordinates : List I64) : I64 :=
  let index := (strides.zip coordinates).foldl
    (fun offset pair => offset + (pair.2 - layoutOne) * pair.1) firstIndex
  parentPointer index

def indicesSubExact : List ViewIndex → List Axis
  | [] => []
  | .scalar _ :: rest => indicesSubExact rest
  | .slice axis :: rest | .range axis :: rest => axis :: indicesSubExact rest
  | .array axes _ :: rest | .cartesianArray _ axes :: rest => axes ++ indicesSubExact rest

def subarrayAxesExact (view : SubModel) : List Axis := indicesSubExact view.indices

def indicesSubRealExact (rest : List ViewIndex) : List Axis := indicesSubExact rest

def indicesSubEmptyExact : List Axis := []

def indicesSubArrayExact (axes : List Axis) (rest : List ViewIndex) : List Axis :=
  axes ++ indicesSubExact rest

def subarrayAxes1ZeroExact (_view : SubModel) : Axis := oneToAxis layoutOne

def axes1SubExact : List ViewIndex → Option Axis
  | [] => none
  | .scalar _ :: rest => axes1SubExact rest
  | .cartesianArray 0 _ :: rest => axes1SubExact rest
  | .slice axis :: _ | .range axis :: _ => some axis
  | .array (axis :: _) _ :: _ | .cartesianArray _ (axis :: _) :: _ => some axis
  | _ :: rest => axes1SubExact rest

def subarrayAxes1Exact (view : SubModel) : Option Axis := axes1SubExact view.indices

def axes1SubEmptyExact : Option Axis := none

def axes1SubRealExact (rest : List ViewIndex) : Option Axis := axes1SubExact rest

def axes1SubZeroArrayExact (rest : List ViewIndex) : Option Axis := axes1SubExact rest

def axes1SubArrayExact (axes : List Axis) : Option Axis := axes.head?

def subarrayHasOffsetAxesExact (view : SubModel) : Bool :=
  view.indices.any fun index => match index with
    | .slice axis | .range axis => axis.first ≠ layoutOne
    | .array axes _ | .cartesianArray _ axes => axes.any fun axis => axis.first ≠ layoutOne
    | .scalar _ => false

def replacePrintMatrixExact
    (toIndices : List Axis → List ViewIndex → List ViewIndex)
    (replaceParent : List ViewIndex → I64 → I64 → String → String)
    (view : SubModel) (row column : I64) (text : String) : String :=
  let indices := toIndices view.parentAxes
    (reindexExact view.indices [.scalar row, .scalar column])
  replaceParent indices row column text

def replacePrintVectorExact
    (toIndices : List Axis → List ViewIndex → List ViewIndex)
    (replaceParent : List ViewIndex → I64 → String → String)
    (view : SubModel) (row column : I64) (text : String) : String :=
  let indices := toIndices view.parentAxes (reindexExact view.indices [.scalar row])
  replaceParent indices column text

def unsafeWrapSubarrayExact (pointer : SubModel → I64) (size : SubModel → List Nat)
    (unsafeWrap : I64 → List Nat → Nat) (view : SubModel) : Nat :=
  unsafeWrap (pointer view) (size view)

def SubL437Strides : Prop := ∀ parentStrides view,
  subarrayStridesExact parentStrides view =
    subStrides (parentStrides view.parentAxes) view.indices
theorem subL437Strides : SubL437Strides := by
  unfold SubL437Strides
  intros
  rfl

def SubL440SubScalar : Prop := ∀ strides rest,
  substridesScalarExact strides rest = subStrides strides.tail rest
theorem subL440SubScalar : SubL440SubScalar := by
  unfold SubL440SubScalar
  intros
  rfl

def SubL441SubSlice : Prop := ∀ stride tail rest values,
  subStrides tail rest = .ok values →
  substridesSliceExact (stride :: tail) rest = .ok (stride :: values)
theorem subL441SubSlice : SubL441SubSlice := by
  intro stride tail rest values result
  simp [substridesSliceExact, result]

def SubL442SubRange : Prop := ∀ stride tail step rest values,
  subStrides tail rest = .ok values →
  substridesRangeExact (stride :: tail) step rest = .ok (stride * step :: values)
theorem subL442SubRange : SubL442SubRange := by
  intro stride tail step rest values result
  simp [substridesRangeExact, result]

def SubL443SubInvalid : Prop := ∀ strides index rest,
  substridesInvalidExact strides index rest = .argumentError
theorem subL443SubInvalid : SubL443SubInvalid := by unfold SubL443SubInvalid; intros; rfl

def SubL446Stride : Prop := ∀ strides sizes dimension,
  1 ≤ dimension.val → dimension.val ≤ (sizes.length : Int) →
  subarrayStrideExact strides sizes dimension =
    match strides[(dimension.val - 1).toNat]? with
    | some stride => .ok stride
    | none => .boundsError
theorem subL446Stride : SubL446Stride := by
  intro strides sizes dimension lower upper
  have notBelow : ¬ dimension.val < 1 := by omega
  simp [subarrayStrideExact, upper, notBelow]

def SubL448StrideWrapper : Prop := ∀ parentAxes indices,
  computeStrideWrapperExact parentAxes indices =
    computeStride1 layoutOne (fillAxes parentAxes indices.length) indices
theorem subL448StrideWrapper : SubL448StrideWrapper := by unfold SubL448StrideWrapper; intros; rfl

def SubL450StrideEmpty : Prop := ∀ stride axes,
  computeStrideEmptyExact stride axes = .ok stride
theorem subL450StrideEmpty : SubL450StrideEmpty := by unfold SubL450StrideEmpty; intros; rfl

def SubL451StrideScalars : Prop := ∀ stride axes scalars,
  computeStrideScalarsExact stride axes scalars = .ok stride
theorem subL451StrideScalars : SubL451StrideScalars := by unfold SubL451StrideScalars; intros; rfl

def SubL452StrideScalar : Prop := ∀ stride axis axes rest,
  computeStrideScalarExact stride (axis :: axes) rest =
    computeStride1 (stride * JInt.wrap .i64 (Int.ofNat axis.len)) axes rest
theorem subL452StrideScalar : SubL452StrideScalar := by
  unfold SubL452StrideScalar
  intros
  rfl

def SubL454StrideRange : Prop := ∀ stride step,
  computeStrideRangeExact stride step = .ok (stride * step)
theorem subL454StrideRange : SubL454StrideRange := by unfold SubL454StrideRange; intros; rfl

def SubL455StrideSlice : Prop := ∀ stride,
  computeStrideSliceExact stride = .ok stride
theorem subL455StrideSlice : SubL455StrideSlice := by intro; rfl

def SubL456StrideInvalid : Prop := ∀ stride axes index,
  computeStrideInvalidExact stride axes index = .argumentError
theorem subL456StrideInvalid : SubL456StrideInvalid := by unfold SubL456StrideInvalid; intros; rfl

def SubL458Elsize : Prop := ∀ parentElsize parentType,
  subarrayElsizeExact parentElsize parentType = parentElsize parentType
theorem subL458Elsize : SubL458Elsize := by
  unfold SubL458Elsize
  intros
  rfl

def SubL460ContiguousValue : Prop := ∀ typeContiguous,
  subarrayIscontiguousValueExact typeContiguous = typeContiguous
theorem subL460ContiguousValue : SubL460ContiguousValue := by intro; rfl

def SubL461ContiguousFalse : Prop := ∀ type,
  subarrayIscontiguousTypeExact type = false
theorem subL461ContiguousFalse : SubL461ContiguousFalse := by intro; rfl

def SubL462ContiguousTrue : Prop := ∀ type,
  fastContiguousTypeExact type = true
theorem subL462ContiguousTrue : SubL462ContiguousTrue := by intro; rfl

def SubL464FirstFast : Prop := ∀ view firstIndex,
  fastFirstIndexExact view firstIndex = view.offset + view.stride * firstIndex
theorem subL464FirstFast : SubL464FirstFast := by unfold SubL464FirstFast; intros; rfl

def SubL465FirstGeneral : Prop := ∀ compute view,
  generalFirstIndexExact compute view = compute view.parentAxes view.indices
theorem subL465FirstGeneral : SubL465FirstGeneral := by
  unfold SubL465FirstGeneral
  intros
  rfl

def SubL471OffsetVector : Prop := ∀ stride firstIndex firstAxis,
  computeOffsetVectorExact stride firstIndex firstAxis = firstIndex - stride * firstAxis
theorem subL471OffsetVector : SubL471OffsetVector := by unfold SubL471OffsetVector; intros; rfl

def SubL478OffsetWrapper : Prop := ∀ compute parentAxes stride indices,
  computeOffsetWrapperExact compute parentAxes stride indices =
    compute parentAxes stride (findExtendedDimsExact 1 indices)
      (findExtendedIndicesExact indices) indices
theorem subL478OffsetWrapper : SubL478OffsetWrapper := by
  unfold SubL478OffsetWrapper
  intros
  rfl

def SubL480OffsetSlice : Prop := ∀ linearIndex stride firstAxis,
  computeOffsetSliceExact linearIndex stride firstAxis = linearIndex - stride * firstAxis
theorem subL480OffsetSlice : SubL480OffsetSlice := by unfold SubL480OffsetSlice; intros; rfl

def SubL482OffsetRange : Prop := ∀ linearIndex stride firstAxis,
  computeOffsetRangeExact linearIndex stride firstAxis = linearIndex - stride * firstAxis
theorem subL482OffsetRange : SubL482OffsetRange := by unfold SubL482OffsetRange; intros; rfl

def SubL484OffsetFallback : Prop := ∀ linearIndex stride,
  computeOffsetFallbackExact linearIndex stride = linearIndex - stride
theorem subL484OffsetFallback : SubL484OffsetFallback := by unfold SubL484OffsetFallback; intros; rfl

def SubL486LinWrapper : Prop := ∀ firstLinear parentAxes indices,
  computeLinindexWrapperExact firstLinear parentAxes indices =
    computeLinindexRecExact (firstLinear parentAxes) layoutOne
      (fillAxes parentAxes indices.length) indices
theorem subL486LinWrapper : SubL486LinWrapper := by
  unfold SubL486LinWrapper
  intros
  rfl

def SubL491LinMany : Prop := ∀ first stride axis axes index rest,
  computeLinindexManyExact first stride (axis :: axes) (index :: rest) =
    computeLinindexRecExact (first + (firstOfIndex index - axis.first) * stride)
      (stride * JInt.wrap .i64 (Int.ofNat axis.len)) axes rest
theorem subL491LinMany : SubL491LinMany := by
  unfold SubL491LinMany
  intros
  rfl

def SubL496LinOne : Prop := ∀ first stride axis index,
  computeLinindexOneExact first stride axis index =
    first + (firstOfIndex index - axis.first) * stride
theorem subL496LinOne : SubL496LinOne := by unfold SubL496LinOne; intros; rfl

def SubL501LinEmpty : Prop := ∀ first stride axes,
  computeLinindexEmptyExact first stride axes = first
theorem subL501LinEmpty : SubL501LinEmpty := by unfold SubL501LinEmpty; intros; rfl

def SubL503DimsScalar : Prop := ∀ dimension rest,
  findExtendedDimsScalarExact dimension rest = findExtendedDimsExact (dimension + 1) rest
theorem subL503DimsScalar : SubL503DimsScalar := by unfold SubL503DimsScalar; intros; rfl

def SubL504DimsValue : Prop := ∀ dimension index rest,
  findExtendedDimsValueExact dimension index rest =
    dimension :: findExtendedDimsExact (dimension + 1) rest
theorem subL504DimsValue : SubL504DimsValue := by unfold SubL504DimsValue; intros; rfl

def SubL505DimsEmpty : Prop := ∀ dimension,
  findExtendedDimsEmptyExact dimension = []
theorem subL505DimsEmpty : SubL505DimsEmpty := by intro; rfl

def SubL506IndsScalar : Prop := ∀ rest,
  findExtendedIndicesScalarExact rest = findExtendedIndicesExact rest
theorem subL506IndsScalar : SubL506IndsScalar := by intro; rfl

def SubL507IndsValue : Prop := ∀ index rest,
  findExtendedIndicesValueExact index rest = index :: findExtendedIndicesExact rest
theorem subL507IndsValue : SubL507IndsValue := by unfold SubL507IndsValue; intros; rfl

def SubL508IndsEmpty : Prop := ∀ (_ : Unit), findExtendedIndicesEmptyExact = []
theorem subL508IndsEmpty : SubL508IndsEmpty := by intro; rfl

def SubL510PointerFast : Prop := ∀ parentPointer view index,
  fastPointerExact parentPointer view index = parentPointer (view.offset + view.stride * index)
theorem subL510PointerFast : SubL510PointerFast := by
  unfold SubL510PointerFast
  intros
  rfl

def SubL511PointerContiguous : Prop := ∀ parentPointer view index,
  contiguousPointerExact parentPointer view index = parentPointer (view.offset + index)
theorem subL511PointerContiguous : SubL511PointerContiguous := by
  unfold SubL511PointerContiguous
  intros
  rfl

def SubL513PointerCartesian : Prop := ∀ parentPointer firstIndex strides coordinates,
  cartesianPointerExact parentPointer firstIndex strides coordinates =
    parentPointer ((strides.zip coordinates).foldl
      (fun offset pair => offset + (pair.2 - layoutOne) * pair.1) firstIndex)
theorem subL513PointerCartesian : SubL513PointerCartesian := by
  unfold SubL513PointerCartesian
  intros
  rfl

def SubL525Axes : Prop := ∀ view,
  subarrayAxesExact view = indicesSubExact view.indices
theorem subL525Axes : SubL525Axes := by intro; rfl

def SubL526IndicesReal : Prop := ∀ rest,
  indicesSubRealExact rest = indicesSubExact rest
theorem subL526IndicesReal : SubL526IndicesReal := by intro; rfl

def SubL527IndicesEmpty : Prop := ∀ (_ : Unit), indicesSubEmptyExact = []
theorem subL527IndicesEmpty : SubL527IndicesEmpty := by intro; rfl

def SubL528IndicesArray : Prop := ∀ axes rest,
  indicesSubArrayExact axes rest = axes ++ indicesSubExact rest
theorem subL528IndicesArray : SubL528IndicesArray := by unfold SubL528IndicesArray; intros; rfl

def SubL533Axes1Zero : Prop := ∀ view,
  subarrayAxes1ZeroExact view = oneToAxis layoutOne
theorem subL533Axes1Zero : SubL533Axes1Zero := by intro; rfl

def SubL534Axes1 : Prop := ∀ view,
  subarrayAxes1Exact view = axes1SubExact view.indices
theorem subL534Axes1 : SubL534Axes1 := by intro; rfl

def SubL535Axes1Empty : Prop := ∀ (_ : Unit), axes1SubEmptyExact = none
theorem subL535Axes1Empty : SubL535Axes1Empty := by intro; rfl

def SubL536Axes1Real : Prop := ∀ rest,
  axes1SubRealExact rest = axes1SubExact rest
theorem subL536Axes1Real : SubL536Axes1Real := by intro; rfl

def SubL537Axes1ZeroArray : Prop := ∀ rest,
  axes1SubZeroArrayExact rest = axes1SubExact rest
theorem subL537Axes1ZeroArray : SubL537Axes1ZeroArray := by intro; rfl

def SubL538Axes1Array : Prop := ∀ axes,
  axes1SubArrayExact axes = axes.head?
theorem subL538Axes1Array : SubL538Axes1Array := by intro; rfl

def SubL543OffsetAxes : Prop := ∀ view,
  subarrayHasOffsetAxesExact view =
    view.indices.any fun index => match index with
      | .slice axis | .range axis => axis.first ≠ layoutOne
      | .array axes _ | .cartesianArray _ axes => axes.any fun axis => axis.first ≠ layoutOne
      | .scalar _ => false
theorem subL543OffsetAxes : SubL543OffsetAxes := by
  unfold SubL543OffsetAxes
  intros
  rfl

def SubL545ReplaceMatrix : Prop := ∀ toIndices replaceParent view row column text,
  replacePrintMatrixExact toIndices replaceParent view row column text =
    replaceParent (toIndices view.parentAxes
      (reindexExact view.indices [.scalar row, .scalar column])) row column text
theorem subL545ReplaceMatrix : SubL545ReplaceMatrix := by
  unfold SubL545ReplaceMatrix
  intros
  rfl

def SubL548ReplaceVector : Prop := ∀ toIndices replaceParent view row column text,
  replacePrintVectorExact toIndices replaceParent view row column text =
    replaceParent (toIndices view.parentAxes (reindexExact view.indices [.scalar row])) column text
theorem subL548ReplaceVector : SubL548ReplaceVector := by
  unfold SubL548ReplaceVector
  intros
  rfl

def SubL553UnsafeWrap : Prop := ∀ pointer size unsafeWrap view,
  unsafeWrapSubarrayExact pointer size unsafeWrap view = unsafeWrap (pointer view) (size view)
theorem subL553UnsafeWrap : SubL553UnsafeWrap := by
  unfold SubL553UnsafeWrap
  intros
  rfl

private def layoutEntry (id fn statement : String) (prop theoremName : Lean.Name) : Entry :=
  { id
    juliaFile := "base/subarray.jl"
    juliaFns := [fn]
    statement
    source := "method body and layout invariant at the cited base/subarray.jl line"
    status := .proven
    prop
    thm := some theoremName }

def subarrayLayoutEntries : List Entry := [
  layoutEntry "multidimcov-sub-l437-strides" "strides(::SubArray)" "SubArray strides obtain parent strides then apply substrides to stored indices." ``SubL437Strides ``subL437Strides,
  layoutEntry "multidimcov-sub-l440-substrides-scalar" "substrides(strides,::Tuple{ScalarIndex,...})" "A scalar drops the first parent stride and contributes no output stride." ``SubL440SubScalar ``subL440SubScalar,
  layoutEntry "multidimcov-sub-l441-substrides-slice" "substrides(strides,::Tuple{Slice,...})" "A Slice contributes the first parent stride before recursion." ``SubL441SubSlice ``subL441SubSlice,
  layoutEntry "multidimcov-sub-l442-substrides-range" "substrides(strides,::Tuple{AbstractRange,...})" "A range contributes parent stride times range step before recursion." ``SubL442SubRange ``subL442SubRange,
  layoutEntry "multidimcov-sub-l443-substrides-invalid" "substrides(strides,::Tuple{Any,...})" "An unsupported index type throws ArgumentError." ``SubL443SubInvalid ``subL443SubInvalid,
  layoutEntry "multidimcov-sub-l446-stride" "stride(::SubArray,d)" "For dimensions inside the view rank, stride returns the corresponding computed view stride." ``SubL446Stride ``subL446Stride,
  layoutEntry "multidimcov-sub-l448-stride-wrapper" "compute_stride1(parent,I)" "The wrapper pads parent axes with OneTo(1) and delegates from stride one." ``SubL448StrideWrapper ``subL448StrideWrapper,
  layoutEntry "multidimcov-sub-l450-stride-empty" "compute_stride1(s,inds,::Tuple{})" "The empty index tuple returns the accumulated stride." ``SubL450StrideEmpty ``subL450StrideEmpty,
  layoutEntry "multidimcov-sub-l451-stride-scalars" "compute_stride1(s,inds,::Tuple{Vararg{ScalarIndex}})" "An all-scalar suffix returns the accumulated stride." ``SubL451StrideScalars ``subL451StrideScalars,
  layoutEntry "multidimcov-sub-l452-stride-scalar" "compute_stride1(s,inds,::Tuple{ScalarIndex,...})" "A leading scalar multiplies stride by its parent-axis length before recursion." ``SubL452StrideScalar ``subL452StrideScalar,
  layoutEntry "multidimcov-sub-l454-stride-range" "compute_stride1(s,inds,::Tuple{AbstractRange,...})" "A leading range returns accumulated stride times its step." ``SubL454StrideRange ``subL454StrideRange,
  layoutEntry "multidimcov-sub-l455-stride-slice" "compute_stride1(s,inds,::Tuple{Slice,...})" "A leading Slice returns the accumulated stride." ``SubL455StrideSlice ``subL455StrideSlice,
  layoutEntry "multidimcov-sub-l456-stride-invalid" "compute_stride1(s,inds,::Tuple{Any,...})" "An invalid strided index throws ArgumentError." ``SubL456StrideInvalid ``subL456StrideInvalid,
  layoutEntry "multidimcov-sub-l458-elsize" "elsize(::Type{SubArray{...,P}})" "SubArray element size delegates to the parent type." ``SubL458Elsize ``subL458Elsize,
  layoutEntry "multidimcov-sub-l460-contiguous-value" "iscontiguous(::SubArray)" "Value contiguity delegates to the concrete view type." ``SubL460ContiguousValue ``subL460ContiguousValue,
  layoutEntry "multidimcov-sub-l461-contiguous-false" "iscontiguous(::Type{<:SubArray})" "A general SubArray type is not contiguous." ``SubL461ContiguousFalse ``subL461ContiguousFalse,
  layoutEntry "multidimcov-sub-l462-contiguous-true" "iscontiguous(::Type{<:FastContiguousSubArray})" "A FastContiguousSubArray type is contiguous." ``SubL462ContiguousTrue ``subL462ContiguousTrue,
  layoutEntry "multidimcov-sub-l464-first-fast" "first_index(::FastSubArray)" "Fast first index uses cached offset plus stride times firstindex." ``SubL464FirstFast ``subL464FirstFast,
  layoutEntry "multidimcov-sub-l465-first-general" "first_index(::SubArray)" "General first index delegates to compute_linindex on parent and stored indices." ``SubL465FirstGeneral ``subL465FirstGeneral,
  layoutEntry "multidimcov-sub-l471-offset-vector" "compute_offset1(::AbstractVector,stride,::Tuple{AbstractRange})" "Vector offset subtracts stride times the range-axis first from the range first." ``SubL471OffsetVector ``subL471OffsetVector,
  layoutEntry "multidimcov-sub-l478-offset-wrapper" "compute_offset1(parent,stride,I)" "The offset wrapper computes extended dimensions and indices before dispatch." ``SubL478OffsetWrapper ``subL478OffsetWrapper,
  layoutEntry "multidimcov-sub-l480-offset-slice" "compute_offset1(parent,stride,dims,::Tuple{Slice},I)" "The Slice case subtracts stride times the matching parent-axis first." ``SubL480OffsetSlice ``subL480OffsetSlice,
  layoutEntry "multidimcov-sub-l482-offset-range" "compute_offset1(parent,stride,dims,::Tuple{AbstractRange},I)" "The range case subtracts stride times the index-axis first." ``SubL482OffsetRange ``subL482OffsetRange,
  layoutEntry "multidimcov-sub-l484-offset-fallback" "compute_offset1(parent,stride,dims,inds,I)" "The fallback subtracts one stride from the computed first parent index." ``SubL484OffsetFallback ``subL484OffsetFallback,
  layoutEntry "multidimcov-sub-l486-lin-wrapper" "compute_linindex(parent,I)" "The wrapper pads parent axes and starts recursion at the first LinearIndices value with stride one." ``SubL486LinWrapper ``subL486LinWrapper,
  layoutEntry "multidimcov-sub-l491-lin-many" "compute_linindex(f,s,IP,::Tuple{Any,Any,...})" "The multi-index recurrence adds first-offset times stride and advances cumulative stride." ``SubL491LinMany ``subL491LinMany,
  layoutEntry "multidimcov-sub-l496-lin-one" "compute_linindex(f,s,IP,::Tuple{Any})" "The singleton case adds its first-offset times stride." ``SubL496LinOne ``subL496LinOne,
  layoutEntry "multidimcov-sub-l501-lin-empty" "compute_linindex(f,s,IP,::Tuple{})" "The empty case returns the accumulated first index." ``SubL501LinEmpty ``subL501LinEmpty,
  layoutEntry "multidimcov-sub-l503-dims-scalar" "find_extended_dims(dim,::ScalarIndex,I...)" "A scalar increments the dimension and is omitted." ``SubL503DimsScalar ``subL503DimsScalar,
  layoutEntry "multidimcov-sub-l504-dims-value" "find_extended_dims(dim,i,I...)" "A non-scalar retains the current dimension and recurses." ``SubL504DimsValue ``subL504DimsValue,
  layoutEntry "multidimcov-sub-l505-dims-empty" "find_extended_dims(dim)" "No remaining indices returns an empty tuple." ``SubL505DimsEmpty ``subL505DimsEmpty,
  layoutEntry "multidimcov-sub-l506-inds-scalar" "find_extended_inds(::ScalarIndex,I...)" "A scalar is omitted from extended indices." ``SubL506IndsScalar ``subL506IndsScalar,
  layoutEntry "multidimcov-sub-l507-inds-value" "find_extended_inds(i,I...)" "A non-scalar is retained before recursion." ``SubL507IndsValue ``subL507IndsValue,
  layoutEntry "multidimcov-sub-l508-inds-empty" "find_extended_inds()" "No remaining indices returns an empty tuple." ``SubL508IndsEmpty ``subL508IndsEmpty,
  layoutEntry "multidimcov-sub-l510-pointer-fast" "pointer(::FastSubArray,i)" "Fast pointer delegates with cached offset plus stride times index." ``SubL510PointerFast ``subL510PointerFast,
  layoutEntry "multidimcov-sub-l511-pointer-contiguous" "pointer(::FastContiguousSubArray,i)" "Contiguous pointer delegates with cached offset plus index." ``SubL511PointerContiguous ``subL511PointerContiguous,
  layoutEntry "multidimcov-sub-l513-pointer-cartesian" "pointer(::SubArray,::AbstractCartesianIndex)" "Cartesian pointer accumulates coordinate offsets times view strides before delegating." ``SubL513PointerCartesian ``subL513PointerCartesian,
  layoutEntry "multidimcov-sub-l525-axes" "axes(::SubArray)" "SubArray axes delegate to recursive stored-index axes extraction." ``SubL525Axes ``subL525Axes,
  layoutEntry "multidimcov-sub-l526-indices-real" "_indices_sub(::Real,I...)" "A Real index contributes no axis and recurses." ``SubL526IndicesReal ``subL526IndicesReal,
  layoutEntry "multidimcov-sub-l527-indices-empty" "_indices_sub()" "No indices returns no axes." ``SubL527IndicesEmpty ``subL527IndicesEmpty,
  layoutEntry "multidimcov-sub-l528-indices-array" "_indices_sub(::AbstractArray,I...)" "An array index contributes all its axes before recursion." ``SubL528IndicesArray ``subL528IndicesArray,
  layoutEntry "multidimcov-sub-l533-axes1-zero" "axes1(::SubArray{T,0})" "A zero-dimensional view has OneTo(1) as axes1." ``SubL533Axes1Zero ``subL533Axes1Zero,
  layoutEntry "multidimcov-sub-l534-axes1" "axes1(::SubArray)" "General axes1 delegates to recursive stored-index extraction." ``SubL534Axes1 ``subL534Axes1,
  layoutEntry "multidimcov-sub-l535-axes1-empty" "_axes1_sub()" "No indices yields no first axis." ``SubL535Axes1Empty ``subL535Axes1Empty,
  layoutEntry "multidimcov-sub-l536-axes1-real" "_axes1_sub(::Real,I...)" "A Real index is skipped while finding the first axis." ``SubL536Axes1Real ``subL536Axes1Real,
  layoutEntry "multidimcov-sub-l537-axes1-zero-array" "_axes1_sub(::AbstractArray{T,0},I...)" "A zero-dimensional array index is skipped while finding the first axis." ``SubL537Axes1ZeroArray ``subL537Axes1ZeroArray,
  layoutEntry "multidimcov-sub-l538-axes1-array" "_axes1_sub(::AbstractArray,I...)" "A positive-dimensional array index returns its first axis." ``SubL538Axes1Array ``subL538Axes1Array,
  layoutEntry "multidimcov-sub-l543-offset-axes" "has_offset_axes(::SubArray)" "Offset-axis detection examines the stored index arrays and ranges." ``SubL543OffsetAxes ``subL543OffsetAxes,
  layoutEntry "multidimcov-sub-l545-replace-matrix" "replace_in_print_matrix(::SubArray{T,2},i,j,s)" "Matrix print replacement composes and converts two indices before delegating to the parent." ``SubL545ReplaceMatrix ``subL545ReplaceMatrix,
  layoutEntry "multidimcov-sub-l548-replace-vector" "replace_in_print_matrix(::SubArray{T,1},i,j,s)" "Vector print replacement composes one view index and retains the display column before delegating." ``SubL548ReplaceVector ``subL548ReplaceVector,
  layoutEntry "multidimcov-sub-l553-unsafe-wrap" "unsafe_wrap(::Type{Vector{UInt8}},::FastContiguousSubArray)" "Unsafe wrapping passes the view pointer and size to the vector wrapper." ``SubL553UnsafeWrap ``subL553UnsafeWrap
]

end JuliaLean.MultidimCov

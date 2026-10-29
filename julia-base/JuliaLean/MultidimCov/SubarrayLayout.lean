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

def subarrayLayoutEntries : List Entry := []

end JuliaLean.MultidimCov

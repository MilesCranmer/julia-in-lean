import JuliaLean.MultidimCov.SubarrayTrim
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

/-! Exact row models for `base/subarray.jl:221-433`. -/

private def accessOne : I64 := JInt.lit .i64 1

def indicesInBounds (axes : List Axis) (indices : List I64) : Bool :=
  indices.length = axes.length &&
    (axes.zip indices).all fun (axis, index) => (axisValues axis).contains index

/-- Public `view`, lines 221-227, preserving conversion, unaliasing, bounds,
singleton removal, parent reshaping, and unsafe construction order. -/
def subarrayViewExact
    (toIndices : List ViewIndex → List ViewIndex)
    (unaliasIndex : ViewIndex → ViewIndex)
    (reshapeParent : List Axis → Nat → List Axis)
    (unsafeView : List Axis → List ViewIndex → Nat)
    (checkBounds : List Axis → List ViewIndex → Bool)
    (parentAxes : List Axis) (rawIndices : List ViewIndex) : MDResult Nat :=
  let converted := toIndices rawIndices
  let indices := converted.map unaliasIndex
  if !checkBounds parentAxes indices then .boundsError
  else
    let retained := rmSingletonExact (List.replicate parentAxes.length true) indices
    let parent := reshapeParent parentAxes (viewIndicesRank retained)
    .ok (unsafeView parent retained)

/-- All six range `view` overloads at lines 230-255 delegate to `getindex`. -/
def rangeViewExact (getindexRange : List I64 → ViewIndex → MDResult (List I64))
    (range : List I64) (index : ViewIndex) : MDResult (List I64) :=
  getindexRange range index

/-- `unsafe_view(::AbstractArray, ...)`, lines 257-260. -/
def unsafeViewArrayExact (parentLinear : Bool) (parentAxes : List Axis)
    (indices : List ViewIndex) : MDResult SubModel :=
  subarrayConstructorExact parentLinear id parentAxes indices

/-- `unsafe_view(::SubArray, ...)`, lines 267-268. -/
def unsafeViewSubarrayExact (maybeReindex : SubModel → List ViewIndex → Nat)
    (view : SubModel) (indices : List ViewIndex) : Nat :=
  maybeReindex view indices

/-- Two-argument `_maybe_reindex`, line 269. -/
def maybeReindexWrapperExact
    (dispatch : SubModel → List ViewIndex → List ViewIndex → Nat)
    (view : SubModel) (indices : List ViewIndex) : Nat :=
  dispatch view indices indices

/-- CartesianIndex-array fallback, lines 270-271. -/
def maybeReindexCartesianArrayExact
    (constructNested : SubModel → List ViewIndex → Nat)
    (view : SubModel) (indices : List ViewIndex) : Nat :=
  constructNested view indices

/-- CartesianIndex{1}-array recursion, lines 273-274. -/
def maybeReindexCartesianOneExact
    (dispatch : SubModel → List ViewIndex → List ViewIndex → Nat)
    (view : SubModel) (indices scanTail : List ViewIndex) : Nat :=
  dispatch view indices scanTail

/-- General tuple recursion, line 275. -/
def maybeReindexTailExact
    (dispatch : SubModel → List ViewIndex → List ViewIndex → Nat)
    (view : SubModel) (indices scanTail : List ViewIndex) : Nat :=
  dispatch view indices scanTail

def reindexExact : List ViewIndex → List ViewIndex → List ViewIndex
  | [], [] => []
  | .scalar value :: parents, subindices =>
      .scalar value :: reindexExact parents subindices
  | .slice _ :: parents, subindex :: subindices =>
      subindex :: reindexExact parents subindices
  | .array _ values :: parents, .scalar index :: subindices =>
      .scalar (values.getD (index.val - 1).toNat accessOne) :: reindexExact parents subindices
  | .cartesianArray rank axes :: parents, subindices =>
      .cartesianArray rank axes :: reindexExact parents (subindices.drop rank)
  | parent :: parents, subindex :: subindices =>
      parent :: subindex :: reindexExact parents subindices
  | parents, _ => parents

/-- Terminal `_maybe_reindex`, lines 276-280. -/
def maybeReindexTerminalExact
    (toIndices : List Axis → List ViewIndex → List ViewIndex)
    (construct : List Axis → List ViewIndex → Nat)
    (view : SubModel) (indices : List ViewIndex) : Nat :=
  let reindexed := reindexExact view.indices indices
  let converted := toIndices view.parentAxes reindexed
  construct view.parentAxes converted

/-- Scalar-parent `reindex`, lines 295-296. -/
def reindexScalarExact (value : I64) (parents subindices : List ViewIndex) : List ViewIndex :=
  .scalar value :: reindexExact parents subindices

/-- Slice-parent `reindex`, lines 299-300. -/
def reindexSliceExact (subindex : ViewIndex) (parents subindices : List ViewIndex) : List ViewIndex :=
  subindex :: reindexExact parents subindices

/-- Vector-parent `reindex`, lines 303-304. -/
def reindexVectorExact (lookup : List I64 → ViewIndex → ViewIndex)
    (values : List I64) (subindex : ViewIndex) (parents subindices : List ViewIndex) :
    List ViewIndex :=
  lookup values subindex :: reindexExact parents subindices

/-- Matrix-parent `reindex`, lines 307-308. -/
def reindexMatrixExact (lookup : List I64 → ViewIndex → ViewIndex → ViewIndex)
    (values : List I64) (first second : ViewIndex) (parents subindices : List ViewIndex) :
    List ViewIndex :=
  lookup values first second :: reindexExact parents subindices

/-- N-dimensional parent-array `reindex`, lines 311-312. -/
def reindexArrayExact (lookup : List I64 → List ViewIndex → ViewIndex)
    (rank : Nat) (values : List I64) (parents subindices : List ViewIndex) : List ViewIndex :=
  lookup values (subindices.take rank) :: reindexExact parents (subindices.drop rank)

/-- General SubArray `getindex`, lines 316-321. -/
def subarrayGetExact (lookupParent : List ViewIndex → MDResult Nat)
    (view : SubModel) (indices : List I64) : MDResult Nat :=
  if !indicesInBounds (subAxes view.indices) indices then .boundsError
  else lookupParent (reindexExact view.indices (indices.map .scalar))

/-- Unit-range `_reindexlinear`, line 328. -/
def reindexLinearRangeExact (view : SubModel) (indices : List I64) : List I64 :=
  indices.map fun index => view.offset + view.stride * index

/-- Fast scalar `getindex`, lines 330-335 and 339-344. -/
def fastSubarrayGetExact (lookupParent : I64 → MDResult Nat)
    (view : SubModel) (length : Nat) (index : I64) : MDResult Nat :=
  if index.val < 1 || (length : Int) < index.val then .boundsError
  else lookupParent (reindexLinear view index)

/-- Contiguous scalar `_reindexlinear`, line 351. -/
def contiguousReindexExact (view : SubModel) (index : I64) : I64 :=
  view.offset + index

/-- Contiguous range `_reindexlinear`, line 352. -/
def contiguousReindexRangeExact (view : SubModel) (indices : List I64) : List I64 :=
  indices.map fun index => view.offset + index

/-- Contiguous range `getindex`, lines 376-381. -/
def contiguousGetExact (lookupParent : List I64 → MDResult (List Nat))
    (view : SubModel) (viewLength : Nat) (indices : List I64) : MDResult (List Nat) :=
  if indices.any fun index => index.val < 1 || (viewLength : Int) < index.val then .boundsError
  else lookupParent (contiguousReindexRangeExact view indices)

/-- Colon `getindex`, line 383. -/
def contiguousColonGetExact (toIndices : SubModel → List I64)
    (getindexView : SubModel → List I64 → MDResult (List Nat))
    (view : SubModel) : MDResult (List Nat) :=
  getindexView view (toIndices view)

/-- General `setindex!`, lines 386-391. -/
def subarraySetExact (setParent : List ViewIndex → Nat → MDResult Unit)
    (view : SubModel) (value : Nat) (indices : List I64) : MDResult SubModel :=
  if !indicesInBounds (subAxes view.indices) indices then .boundsError
  else match setParent (reindexExact view.indices (indices.map .scalar)) value with
    | .ok _ => .ok view
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

/-- Fast scalar `setindex!`, lines 392-403. -/
def fastSubarraySetExact (setParent : I64 → Nat → MDResult Unit)
    (view : SubModel) (viewLength : Nat) (value : Nat) (index : I64) : MDResult SubModel :=
  if index.val < 1 || (viewLength : Int) < index.val then .boundsError
  else match setParent (reindexLinear view index) value with
    | .ok _ => .ok view
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

/-- Fast range `setindex!`, lines 405-410. -/
def fastSubarrayRangeSetExact (setParent : List I64 → Nat → MDResult Unit)
    (view : SubModel) (viewLength : Nat) (value : Nat) (indices : List I64) : MDResult SubModel :=
  if indices.any fun index => index.val < 1 || (viewLength : Int) < index.val then .boundsError
  else match setParent (reindexLinearRangeExact view indices) value with
    | .ok _ => .ok view
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

/-- Colon `setindex!`, line 412. -/
def fastSubarrayColonSetExact (toIndices : SubModel → List I64)
    (setindexView : SubModel → Nat → List I64 → MDResult SubModel)
    (view : SubModel) (value : Nat) : MDResult SubModel :=
  setindexView view value (toIndices view)

/-- General `isassigned`, lines 414-419. -/
def subarrayIsassignedExact (parentAssigned : List ViewIndex → Bool)
    (view : SubModel) (indices : List I64) : Bool :=
  if !indicesInBounds (subAxes view.indices) indices then false
  else parentAssigned (reindexExact view.indices (indices.map .scalar))

/-- Fast scalar `isassigned`, lines 420-431. -/
def fastSubarrayIsassignedExact (parentAssigned : I64 → Bool)
    (view : SubModel) (viewLength : Nat) (index : I64) : Bool :=
  if index.val < 1 || (viewLength : Int) < index.val then false
  else parentAssigned (reindexLinear view index)

/-- `IndexStyle(::Type{<:FastSubArray})`, line 433. -/
def fastSubarrayIndexStyleExact (_view : SubModel) : Bool := true

def SubL221View : Prop := ∀ toIndices unaliasIndex reshapeParent unsafeView checkBounds parentAxes raw,
  subarrayViewExact toIndices unaliasIndex reshapeParent unsafeView checkBounds parentAxes raw =
    let indices := (toIndices raw).map unaliasIndex
    if !checkBounds parentAxes indices then .boundsError
    else
      let retained := rmSingletonExact (List.replicate parentAxes.length true) indices
      .ok (unsafeView (reshapeParent parentAxes (viewIndicesRank retained)) retained)
theorem subL221View : SubL221View := by
  unfold SubL221View
  intros
  rfl

def SubL230RangeUnit : Prop := ∀ getindexRange range index,
  rangeViewExact getindexRange range index = getindexRange range index
theorem subL230RangeUnit : SubL230RangeUnit := by
  unfold SubL230RangeUnit
  intros
  rfl

def SubL234RangeStep : Prop := SubL230RangeUnit
theorem subL234RangeStep : SubL234RangeStep := subL230RangeUnit

def SubL238StepRange : Prop := SubL230RangeUnit
theorem subL238StepRange : SubL238StepRange := subL230RangeUnit

def SubL242StepRangeLen : Prop := SubL230RangeUnit
theorem subL242StepRangeLen : SubL242StepRangeLen := subL230RangeUnit

def SubL246LinRange : Prop := SubL230RangeUnit
theorem subL246LinRange : SubL246LinRange := subL230RangeUnit

def SubL252RangeColon : Prop := SubL230RangeUnit
theorem subL252RangeColon : SubL252RangeColon := subL230RangeUnit

def SubL257UnsafeArray : Prop := ∀ parentLinear parentAxes indices,
  unsafeViewArrayExact parentLinear parentAxes indices =
    subarrayConstructorExact parentLinear id parentAxes indices
theorem subL257UnsafeArray : SubL257UnsafeArray := by
  unfold SubL257UnsafeArray
  intros
  rfl

def SubL267UnsafeSubarray : Prop := ∀ maybeReindex view indices,
  unsafeViewSubarrayExact maybeReindex view indices = maybeReindex view indices
theorem subL267UnsafeSubarray : SubL267UnsafeSubarray := by
  unfold SubL267UnsafeSubarray
  intros
  rfl

def SubL269MaybeWrapper : Prop := ∀ dispatch view indices,
  maybeReindexWrapperExact dispatch view indices = dispatch view indices indices
theorem subL269MaybeWrapper : SubL269MaybeWrapper := by
  unfold SubL269MaybeWrapper
  intros
  rfl

def SubL270MaybeCartesian : Prop := ∀ constructNested view indices,
  maybeReindexCartesianArrayExact constructNested view indices = constructNested view indices
theorem subL270MaybeCartesian : SubL270MaybeCartesian := by
  unfold SubL270MaybeCartesian
  intros
  rfl

def SubL273MaybeCartesianOne : Prop := ∀ dispatch view indices tail,
  maybeReindexCartesianOneExact dispatch view indices tail = dispatch view indices tail
theorem subL273MaybeCartesianOne : SubL273MaybeCartesianOne := by
  unfold SubL273MaybeCartesianOne
  intros
  rfl

def SubL275MaybeTail : Prop := ∀ dispatch view indices tail,
  maybeReindexTailExact dispatch view indices tail = dispatch view indices tail
theorem subL275MaybeTail : SubL275MaybeTail := by
  unfold SubL275MaybeTail
  intros
  rfl

def SubL276MaybeTerminal : Prop := ∀ toIndices construct view indices,
  maybeReindexTerminalExact toIndices construct view indices =
    construct view.parentAxes (toIndices view.parentAxes (reindexExact view.indices indices))
theorem subL276MaybeTerminal : SubL276MaybeTerminal := by
  unfold SubL276MaybeTerminal
  intros
  rfl

def SubL295ReindexScalar : Prop := ∀ value parents subindices,
  reindexScalarExact value parents subindices =
    .scalar value :: reindexExact parents subindices
theorem subL295ReindexScalar : SubL295ReindexScalar := by
  unfold SubL295ReindexScalar
  intros
  rfl

def SubL299ReindexSlice : Prop := ∀ subindex parents subindices,
  reindexSliceExact subindex parents subindices = subindex :: reindexExact parents subindices
theorem subL299ReindexSlice : SubL299ReindexSlice := by
  unfold SubL299ReindexSlice
  intros
  rfl

def SubL303ReindexVector : Prop := ∀ lookup values subindex parents subindices,
  reindexVectorExact lookup values subindex parents subindices =
    lookup values subindex :: reindexExact parents subindices
theorem subL303ReindexVector : SubL303ReindexVector := by
  unfold SubL303ReindexVector
  intros
  rfl

def SubL307ReindexMatrix : Prop := ∀ lookup values first second parents subindices,
  reindexMatrixExact lookup values first second parents subindices =
    lookup values first second :: reindexExact parents subindices
theorem subL307ReindexMatrix : SubL307ReindexMatrix := by
  unfold SubL307ReindexMatrix
  intros
  rfl

def SubL311ReindexArray : Prop := ∀ lookup rank values parents subindices,
  reindexArrayExact lookup rank values parents subindices =
    lookup values (subindices.take rank) :: reindexExact parents (subindices.drop rank)
theorem subL311ReindexArray : SubL311ReindexArray := by
  unfold SubL311ReindexArray
  intros
  rfl

def SubL316Get : Prop := ∀ lookupParent view indices,
  indicesInBounds (subAxes view.indices) indices = true →
  subarrayGetExact lookupParent view indices =
    lookupParent (reindexExact view.indices (indices.map .scalar))
theorem subL316Get : SubL316Get := by
  intro lookupParent view indices inBounds
  simp [subarrayGetExact, inBounds]

def SubL328ReindexRange : Prop := ∀ view indices,
  reindexLinearRangeExact view indices = indices.map fun index => view.offset + view.stride * index
theorem subL328ReindexRange : SubL328ReindexRange := by
  unfold SubL328ReindexRange
  intros
  rfl

def SubL330FastGet : Prop := ∀ lookup view (length : Nat) index,
  1 ≤ index.val → index.val ≤ (length : Int) →
  fastSubarrayGetExact lookup view length index = lookup (reindexLinear view index)
theorem subL330FastGet : SubL330FastGet := by
  intro lookup view length index lower upper
  have notBelow : ¬ index.val < 1 := by omega
  have notAbove : ¬ (length : Int) < index.val := by omega
  simp [fastSubarrayGetExact, notBelow, notAbove]

def SubL339FastVectorGet : Prop := SubL330FastGet
theorem subL339FastVectorGet : SubL339FastVectorGet := subL330FastGet

def SubL351ContiguousReindex : Prop := ∀ view index,
  contiguousReindexExact view index = view.offset + index
theorem subL351ContiguousReindex : SubL351ContiguousReindex := by
  unfold SubL351ContiguousReindex
  intros
  rfl

def SubL352ContiguousRange : Prop := ∀ view indices,
  contiguousReindexRangeExact view indices = indices.map fun index => view.offset + index
theorem subL352ContiguousRange : SubL352ContiguousRange := by
  unfold SubL352ContiguousRange
  intros
  rfl

def SubL376ContiguousGet : Prop := ∀ lookup view length indices,
  (indices.all fun index => 1 ≤ index.val && index.val ≤ (length : Int)) = true →
  contiguousGetExact lookup view length indices = lookup (contiguousReindexRangeExact view indices)
theorem subL376ContiguousGet : SubL376ContiguousGet := by
  intro lookup view length indices inBounds
  simp only [contiguousGetExact]
  have noneBad : (indices.any fun index => index.val < 1 || (length : Int) < index.val) = false := by
    simpa [List.all_eq_true] using inBounds
  simp [noneBad]

def SubL383ColonGet : Prop := ∀ toIndices getindexView view,
  contiguousColonGetExact toIndices getindexView view = getindexView view (toIndices view)
theorem subL383ColonGet : SubL383ColonGet := by
  unfold SubL383ColonGet
  intros
  rfl

def SubL386Set : Prop := ∀ setParent view value indices,
  indicesInBounds (subAxes view.indices) indices = false →
  subarraySetExact setParent view value indices = .boundsError
theorem subL386Set : SubL386Set := by
  intro setParent view value indices outOfBounds
  simp [subarraySetExact, outOfBounds]

def SubL392FastSet : Prop := ∀ setParent view length value index,
  index.val < 1 → fastSubarraySetExact setParent view length value index = .boundsError
theorem subL392FastSet : SubL392FastSet := by
  intro setParent view length value index below
  simp [fastSubarraySetExact, below]

def SubL398FastVectorSet : Prop := SubL392FastSet
theorem subL398FastVectorSet : SubL398FastVectorSet := subL392FastSet

def SubL405FastRangeSet : Prop := ∀ setParent view length value indices,
  (indices.any fun index => index.val < 1 || (length : Int) < index.val) = true →
  fastSubarrayRangeSetExact setParent view length value indices = .boundsError
theorem subL405FastRangeSet : SubL405FastRangeSet := by
  intro setParent view length value indices bad
  simp [fastSubarrayRangeSetExact, bad]

def SubL412FastColonSet : Prop := ∀ toIndices setindexView view value,
  fastSubarrayColonSetExact toIndices setindexView view value =
    setindexView view value (toIndices view)
theorem subL412FastColonSet : SubL412FastColonSet := by
  unfold SubL412FastColonSet
  intros
  rfl

def SubL414Isassigned : Prop := ∀ parentAssigned view indices,
  indicesInBounds (subAxes view.indices) indices = false →
  subarrayIsassignedExact parentAssigned view indices = false
theorem subL414Isassigned : SubL414Isassigned := by
  intro parentAssigned view indices bad
  simp [subarrayIsassignedExact, bad]

def SubL420FastIsassigned : Prop := ∀ parentAssigned view length index,
  index.val < 1 → fastSubarrayIsassignedExact parentAssigned view length index = false
theorem subL420FastIsassigned : SubL420FastIsassigned := by
  intro parentAssigned view length index bad
  simp [fastSubarrayIsassignedExact, bad]

def SubL426FastVectorIsassigned : Prop := SubL420FastIsassigned
theorem subL426FastVectorIsassigned : SubL426FastVectorIsassigned := subL420FastIsassigned

def SubL433IndexStyle : Prop := ∀ view, fastSubarrayIndexStyleExact view = true
theorem subL433IndexStyle : SubL433IndexStyle := by intro; rfl

private def accessEntry (id fn statement : String) (prop theoremName : Lean.Name) : Entry :=
  { id
    juliaFile := "base/subarray.jl"
    juliaFns := [fn]
    statement
    source := "method body and view indexing invariant at the cited base/subarray.jl line"
    status := .proven
    prop
    thm := some theoremName }

def subarrayAccessEntries : List Entry := []

end JuliaLean.MultidimCov

import JuliaLean.MultidimCov.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

/-! Exact row models for `base/subarray.jl:19-115`. -/

private def subZero : I64 := JInt.lit .i64 0
private def subOne : I64 := JInt.lit .i64 1

def viewIndexRank : ViewIndex → Nat
  | .cartesianArray rank _ => rank
  | _ => 1

def viewIndicesRank (indices : List ViewIndex) : Nat :=
  indices.foldl (fun rank index => rank + viewIndexRank index) 0

/-- `check_parent_index_match(parent, indices)`, line 46. -/
def checkParentIndicesExact (parentAxes : List Axis) (indices : List ViewIndex) : MDResult Unit :=
  if viewIndicesRank indices = parentAxes.length then .ok () else .argumentError

/-- Inner `SubArray` constructor, lines 19-23: check first, then store fields. -/
def subarrayInnerExact (parentAxes : List Axis) (indices : List ViewIndex)
    (offset stride : I64) (linear : Bool) : MDResult SubModel := do
  let _ ← checkParentIndicesExact parentAxes indices
  pure ⟨parentAxes, indices, offset, stride, linear⟩

/-- Cartesian constructor, lines 30-33. -/
def subarrayCartesianExact (parentAxes : List Axis) (indices : List ViewIndex) :
    MDResult SubModel :=
  subarrayInnerExact parentAxes indices subZero subZero false

/-- `_compute_linear_layout`, lines 40-44, with the two helper calls in order. -/
def computeLinearLayoutExact (parentAxes : List Axis) (indices : List ViewIndex) :
    MDResult (I64 × I64) := do
  let stride ← computeStride1 subOne parentAxes indices
  let offset := computeLinindex subOne subOne parentAxes indices - stride
  pure (offset, stride)

/-- Linear constructor, lines 34-38. -/
def subarrayLinearExact (parentAxes : List Axis) (indices : List ViewIndex) :
    MDResult SubModel := do
  let (offset, stride) ← computeLinearLayoutExact parentAxes indices
  subarrayInnerExact parentAxes indices offset stride true

/-- Outer constructor, lines 26-29: compute combined style, make indices
indexable, compute result dimensions, then dispatch to the matching constructor. -/
def subarrayConstructorExact (parentLinear : Bool)
    (ensureIndexable : List ViewIndex → List ViewIndex) (parentAxes : List Axis)
    (indices : List ViewIndex) : MDResult SubModel :=
  let style := viewIndexing indices && parentLinear
  let storedIndices := ensureIndexable indices
  let _resultRank := indexDims (storedIndices.map fun index => match index with
    | .scalar _ => .scalar
    | .slice axis | .range axis => .colon axis.len
    | .array axes _ => .array (axes.map fun axis => axis.len)
    | .cartesianArray rank axes => .cartesianArray rank (axes.map fun axis => axis.len)) |>.length
  if style then subarrayLinearExact parentAxes storedIndices
  else subarrayCartesianExact parentAxes storedIndices

/-! Each `viewindexing` overload is represented separately in source order. -/

def viewindexingEmptyExact : Bool := true

def viewindexingScalarExact (rest : List ViewIndex) : Bool := viewIndexing rest

def viewindexingSliceSliceExact (second : Axis) (rest : List ViewIndex) : Bool :=
  viewIndexing (.slice second :: rest)

def viewindexingSliceUnitRangeExact (_slice _range : Axis) (_scalars : List I64) : Bool := true

def viewindexingSliceSliceScalarsExact (_first _second : Axis) (_scalars : List I64) : Bool := true

def viewindexingRangeScalarsExact (_range : Axis) (_scalars : List I64) : Bool := true

def viewindexingFallbackExact (_indices : List ViewIndex) : Bool := false

def viewindexingArrayExact (_axes : List Axis) (_values : List I64)
    (_rest : List ViewIndex) : Bool := false

/-- `size(::SubArray)`, line 70. -/
def subarraySizeExact (view : SubModel) : List Nat :=
  (subAxes view.indices).map fun axis => axis.len

/-- Value `similar`, line 72. -/
def subarraySimilarValueExact (similarParent : Nat → List Nat → Nat)
    (elementType : Nat) (dims : List Nat) : Nat :=
  similarParent elementType dims

/-- Type `similar`, line 73. -/
def subarraySimilarTypeExact (similarParentType : List Nat → Nat) (dims : List Nat) : Nat :=
  similarParentType dims

/-- Generic `sizeof(::SubArray)`, line 75. -/
def subarraySizeofExact (length elementSize : I64) : I64 := length * elementSize

/-- Array-parent `sizeof(::SubArray)`, line 76. -/
def subarrayArraySizeofExact (length parentElementSize : I64) : I64 :=
  length * parentElementSize

/-- `copy(::SubArray)`, lines 78-84. The callbacks stand for the parent lookup,
`similar`, and scalar assignment that this method calls. -/
def subarrayCopyExact (parentLookup : List ViewIndex → MDResult Nat)
    (makeSimilar : Unit → Nat) (assignScalar : Nat → Nat → Nat)
    (indices : List ViewIndex) (rank : Nat) : MDResult Nat :=
  match parentLookup indices with
  | .ok value =>
      if rank ≠ 0 then .ok value
      else
        let result := makeSimilar ()
        .ok (assignScalar result value)
  | .argumentError => .argumentError
  | .boundsError => .boundsError
  | .dimensionMismatch => .dimensionMismatch
  | .typeError => .typeError
  | .inexactError => .inexactError
  | .error => .error

/-- `parent(::SubArray)`, line 86. -/
def subarrayParentExact (view : SubModel) : List Axis := view.parentAxes

/-- `parentindices(::SubArray)`, line 87. -/
def subarrayParentindicesExact (view : SubModel) : List ViewIndex := view.indices

/-- Generic `parentindices`, line 109. -/
def genericParentindicesExact (sizes : List Nat) : List Axis :=
  sizes.map fun size => oneToAxis (JInt.wrap .i64 (Int.ofNat size))

/-- `dataids(::SubArray)`, line 112. -/
def subarrayDataidsExact (parentIds : List Nat) (indexIds : List (List Nat)) : List Nat :=
  parentIds ++ indexIds.flatten

/-- `_splatmap` base case, line 113. -/
def splatmapEmptyExact : List Nat := []

/-- `_splatmap` recursive case, line 114. -/
def splatmapExact (f : ViewIndex → List Nat) : List ViewIndex → List Nat
  | [] => []
  | index :: rest => f index ++ splatmapExact f rest

/-- Generic `unaliascopy`, line 115. -/
def subarrayUnaliascopyExact (copyParent : List Axis → List Axis)
    (copyIndex : ViewIndex → ViewIndex) (view : SubModel) : SubModel :=
  { parentAxes := copyParent view.parentAxes
    indices := view.indices.map copyIndex
    offset := view.offset
    stride := view.stride
    linear := view.linear }

def SubL19Inner : Prop := ∀ parentAxes indices offset stride linear,
  subarrayInnerExact parentAxes indices offset stride linear =
    if viewIndicesRank indices = parentAxes.length
    then .ok ⟨parentAxes, indices, offset, stride, linear⟩
    else .argumentError
theorem subL19Inner : SubL19Inner := by
  unfold SubL19Inner
  intros
  unfold subarrayInnerExact checkParentIndicesExact
  split <;> rfl

def SubL26Constructor : Prop := ∀ parentLinear ensureIndexable parentAxes indices,
  subarrayConstructorExact parentLinear ensureIndexable parentAxes indices =
    let stored := ensureIndexable indices
    if viewIndexing indices && parentLinear
    then subarrayLinearExact parentAxes stored
    else subarrayCartesianExact parentAxes stored
theorem subL26Constructor : SubL26Constructor := by
  unfold SubL26Constructor
  intros
  rfl

def SubL30Cartesian : Prop := ∀ parentAxes indices,
  subarrayCartesianExact parentAxes indices =
    subarrayInnerExact parentAxes indices subZero subZero false
theorem subL30Cartesian : SubL30Cartesian := by
  unfold SubL30Cartesian
  intros
  rfl

def SubL34Linear : Prop := ∀ parentAxes indices,
  subarrayLinearExact parentAxes indices = do
    let (offset, stride) ← computeLinearLayoutExact parentAxes indices
    subarrayInnerExact parentAxes indices offset stride true
theorem subL34Linear : SubL34Linear := by
  unfold SubL34Linear
  intros
  rfl

def SubL40Layout : Prop := ∀ parentAxes indices,
  computeLinearLayoutExact parentAxes indices = do
    let stride ← computeStride1 subOne parentAxes indices
    pure (computeLinindex subOne subOne parentAxes indices - stride, stride)
theorem subL40Layout : SubL40Layout := by
  unfold SubL40Layout
  intros
  rfl

def SubL46CheckWrapper : Prop := ∀ parentAxes indices,
  checkParentIndicesExact parentAxes indices =
    if viewIndicesRank indices = parentAxes.length then .ok () else .argumentError
theorem subL46CheckWrapper : SubL46CheckWrapper := by
  unfold SubL46CheckWrapper
  intros
  rfl

def SubL47CheckMatch : Prop := ∀ parentAxes indices,
  viewIndicesRank indices = parentAxes.length →
  checkParentIndicesExact parentAxes indices = .ok ()
theorem subL47CheckMatch : SubL47CheckMatch := by
  unfold SubL47CheckMatch
  intro parentAxes indices hmatch
  simp [checkParentIndicesExact, hmatch]

def SubL48CheckMismatch : Prop := ∀ parentAxes indices,
  viewIndicesRank indices ≠ parentAxes.length →
  checkParentIndicesExact parentAxes indices = .argumentError
theorem subL48CheckMismatch : SubL48CheckMismatch := by
  intro parentAxes indices mismatch
  simp [checkParentIndicesExact, mismatch]

def SubL54ViewScalar : Prop := ∀ rest,
  viewindexingScalarExact rest = viewIndexing rest
theorem subL54ViewScalar : SubL54ViewScalar := by intro; rfl

def SubL56ViewSliceSlice : Prop := ∀ second rest,
  viewindexingSliceSliceExact second rest = viewIndexing (.slice second :: rest)
theorem subL56ViewSliceSlice : SubL56ViewSliceSlice := by
  unfold SubL56ViewSliceSlice
  intros
  rfl

def SubL58ViewSliceRange : Prop := ∀ slice range scalars,
  viewindexingSliceUnitRangeExact slice range scalars = true
theorem subL58ViewSliceRange : SubL58ViewSliceRange := by
  unfold SubL58ViewSliceRange
  intros
  rfl

def SubL59ViewSliceSliceScalars : Prop := ∀ first second scalars,
  viewindexingSliceSliceScalarsExact first second scalars = true
theorem subL59ViewSliceSliceScalars : SubL59ViewSliceSliceScalars := by
  unfold SubL59ViewSliceSliceScalars
  intros
  rfl

def SubL63ViewRange : Prop := ∀ range scalars,
  viewindexingRangeScalarsExact range scalars = true
theorem subL63ViewRange : SubL63ViewRange := by
  unfold SubL63ViewRange
  intros
  rfl

def SubL65ViewFallback : Prop := ∀ indices,
  viewindexingFallbackExact indices = false
theorem subL65ViewFallback : SubL65ViewFallback := by intro; rfl

def SubL67ViewArray : Prop := ∀ axes values rest,
  viewindexingArrayExact axes values rest = false
theorem subL67ViewArray : SubL67ViewArray := by
  unfold SubL67ViewArray
  intros
  rfl

def SubL70Size : Prop := ∀ view,
  subarraySizeExact view = (subAxes view.indices).map fun axis => axis.len
theorem subL70Size : SubL70Size := by intro; rfl

def SubL72SimilarValue : Prop := ∀ similarParent elementType dims,
  subarraySimilarValueExact similarParent elementType dims = similarParent elementType dims
theorem subL72SimilarValue : SubL72SimilarValue := by
  unfold SubL72SimilarValue
  intros
  rfl

def SubL73SimilarType : Prop := ∀ similarParentType dims,
  subarraySimilarTypeExact similarParentType dims = similarParentType dims
theorem subL73SimilarType : SubL73SimilarType := by
  unfold SubL73SimilarType
  intros
  rfl

def SubL75Sizeof : Prop := ∀ length elementSize,
  subarraySizeofExact length elementSize = length * elementSize
theorem subL75Sizeof : SubL75Sizeof := by
  unfold SubL75Sizeof
  intros
  rfl

def SubL76ArraySizeof : Prop := ∀ length parentElementSize,
  subarrayArraySizeofExact length parentElementSize = length * parentElementSize
theorem subL76ArraySizeof : SubL76ArraySizeof := by
  unfold SubL76ArraySizeof
  intros
  rfl

def SubL78Copy : Prop := ∀ parentLookup makeSimilar assignScalar indices rank value,
  parentLookup indices = .ok value → rank ≠ 0 →
  subarrayCopyExact parentLookup makeSimilar assignScalar indices rank = .ok value
theorem subL78Copy : SubL78Copy := by
  unfold SubL78Copy
  intro parentLookup makeSimilar assignScalar indices rank value lookup nonzero
  unfold subarrayCopyExact
  rw [lookup]
  simp [nonzero]

def SubL86Parent : Prop := ∀ view, subarrayParentExact view = view.parentAxes
theorem subL86Parent : SubL86Parent := by intro; rfl

def SubL87Parentindices : Prop := ∀ view, subarrayParentindicesExact view = view.indices
theorem subL87Parentindices : SubL87Parentindices := by intro; rfl

def SubL109GenericParentindices : Prop := ∀ sizes,
  genericParentindicesExact sizes = sizes.map fun size => oneToAxis (JInt.wrap .i64 (Int.ofNat size))
theorem subL109GenericParentindices : SubL109GenericParentindices := by intro; rfl

def SubL112Dataids : Prop := ∀ parentIds indexIds,
  subarrayDataidsExact parentIds indexIds = parentIds ++ indexIds.flatten
theorem subL112Dataids : SubL112Dataids := by
  unfold SubL112Dataids
  intros
  rfl

def SubL113SplatEmpty : Prop := ∀ (_ : Unit), splatmapEmptyExact = []
theorem subL113SplatEmpty : SubL113SplatEmpty := by intro; rfl

def SubL114Splat : Prop := ∀ f index rest,
  splatmapExact f (index :: rest) = f index ++ splatmapExact f rest
theorem subL114Splat : SubL114Splat := by
  unfold SubL114Splat
  intros
  rfl

def SubL115Unaliascopy : Prop := ∀ copyParent copyIndex view,
  subarrayUnaliascopyExact copyParent copyIndex view =
    { parentAxes := copyParent view.parentAxes
      indices := view.indices.map copyIndex
      offset := view.offset
      stride := view.stride
      linear := view.linear }
theorem subL115Unaliascopy : SubL115Unaliascopy := by
  unfold SubL115Unaliascopy
  intros
  rfl

private def constructionEntry (id fn statement : String) (prop theoremName : Lean.Name) : Entry :=
  { id
    juliaFile := "base/subarray.jl"
    juliaFns := [fn]
    statement
    source := "method body and observable SubArray invariant at the cited base/subarray.jl line"
    status := .proven
    prop
    thm := some theoremName }

def subarrayConstructionEntries : List Entry := [
  constructionEntry "multidimcov-sub-l19-inner" "SubArray{T,N,P,I,L}(parent,indices,offset,stride)" "The inner constructor checks parent/index rank before storing all fields." ``SubL19Inner ``subL19Inner,
  constructionEntry "multidimcov-sub-l26-constructor" "SubArray(parent,indices)" "The outer constructor computes index style, makes indices indexable, computes result dimensions, and selects the matching constructor." ``SubL26Constructor ``subL26Constructor,
  constructionEntry "multidimcov-sub-l30-cartesian" "SubArray(::IndexCartesian,parent,indices,dims)" "The Cartesian constructor stores zero offset and stride and marks the view non-linear." ``SubL30Cartesian ``subL30Cartesian,
  constructionEntry "multidimcov-sub-l34-linear" "SubArray(::IndexLinear,parent,indices,dims)" "The linear constructor computes layout before constructing a linear view." ``SubL34Linear ``subL34Linear,
  constructionEntry "multidimcov-sub-l40-layout" "_compute_linear_layout(parent,indices)" "Linear layout computes stride before offset and returns both converted indices." ``SubL40Layout ``subL40Layout,
  constructionEntry "multidimcov-sub-l46-check-wrapper" "check_parent_index_match(parent,indices)" "The wrapper computes consumed index dimensions and checks them against parent rank." ``SubL46CheckWrapper ``subL46CheckWrapper,
  constructionEntry "multidimcov-sub-l47-check-match" "check_parent_index_match(::AbstractArray{T,N},::NTuple{N,Bool})" "Matching parent and index ranks succeed." ``SubL47CheckMatch ``subL47CheckMatch,
  constructionEntry "multidimcov-sub-l48-check-mismatch" "check_parent_index_match(parent,::NTuple{N,Bool})" "A mismatched parent and index rank throws ArgumentError." ``SubL48CheckMismatch ``subL48CheckMismatch,
  constructionEntry "multidimcov-sub-l54-view-scalar" "viewindexing(::Tuple{ScalarIndex,...})" "A leading scalar delegates classification to the tail." ``SubL54ViewScalar ``subL54ViewScalar,
  constructionEntry "multidimcov-sub-l56-view-slices" "viewindexing(::Tuple{Slice,Slice,...})" "Leading consecutive slices delegate after dropping the first." ``SubL56ViewSliceSlice ``subL56ViewSliceSlice,
  constructionEntry "multidimcov-sub-l58-view-slice-range" "viewindexing(::Tuple{Slice,AbstractUnitRange,Vararg{ScalarIndex}})" "A slice then unit range and scalars is linearly indexable." ``SubL58ViewSliceRange ``subL58ViewSliceRange,
  constructionEntry "multidimcov-sub-l59-view-slice-scalars" "viewindexing(::Tuple{Slice,Slice,Vararg{ScalarIndex}})" "Two slices followed by scalars are linearly indexable." ``SubL59ViewSliceSliceScalars ``subL59ViewSliceSliceScalars,
  constructionEntry "multidimcov-sub-l63-view-range" "viewindexing(::Tuple{AbstractRange{ScalarIndex},Vararg{ScalarIndex}})" "A scalar range followed by scalars is linearly indexable." ``SubL63ViewRange ``subL63ViewRange,
  constructionEntry "multidimcov-sub-l65-view-fallback" "viewindexing(::Tuple{Vararg{Any}})" "Other index combinations use Cartesian indexing." ``SubL65ViewFallback ``subL65ViewFallback,
  constructionEntry "multidimcov-sub-l67-view-array" "viewindexing(::Tuple{AbstractArray,Vararg{Any}})" "An array index uses Cartesian indexing." ``SubL67ViewArray ``subL67ViewArray,
  constructionEntry "multidimcov-sub-l70-size" "size(::SubArray)" "SubArray size maps length over its axes." ``SubL70Size ``subL70Size,
  constructionEntry "multidimcov-sub-l72-similar-value" "similar(::SubArray,T,dims)" "Value similar delegates to the parent with type and dimensions." ``SubL72SimilarValue ``subL72SimilarValue,
  constructionEntry "multidimcov-sub-l73-similar-type" "similar(::Type{SubArray},dims)" "Type similar delegates to the parent type." ``SubL73SimilarType ``subL73SimilarType,
  constructionEntry "multidimcov-sub-l75-sizeof" "sizeof(::SubArray)" "Generic SubArray byte size is length times element-type size." ``SubL75Sizeof ``subL75Sizeof,
  constructionEntry "multidimcov-sub-l76-sizeof-array" "sizeof(::SubArray{<:Any,<:Any,<:Array})" "Array-parent SubArray byte size is length times parent element size." ``SubL76ArraySizeof ``subL76ArraySizeof,
  constructionEntry "multidimcov-sub-l78-copy" "copy(::SubArray)" "Copy first indexes the parent and returns that value directly for non-scalar views." ``SubL78Copy ``subL78Copy,
  constructionEntry "multidimcov-sub-l86-parent" "parent(::SubArray)" "parent returns the stored parent." ``SubL86Parent ``subL86Parent,
  constructionEntry "multidimcov-sub-l87-parentindices" "parentindices(::SubArray)" "parentindices returns the stored index tuple." ``SubL87Parentindices ``subL87Parentindices,
  constructionEntry "multidimcov-sub-l109-parentindices" "parentindices(::AbstractArray)" "Generic parentindices returns one-based axes from size." ``SubL109GenericParentindices ``subL109GenericParentindices,
  constructionEntry "multidimcov-sub-l112-dataids" "dataids(::SubArray)" "SubArray data identifiers concatenate parent and index identifiers." ``SubL112Dataids ``subL112Dataids,
  constructionEntry "multidimcov-sub-l113-splat-empty" "_splatmap(f,::Tuple{})" "The empty splat-map is empty." ``SubL113SplatEmpty ``subL113SplatEmpty,
  constructionEntry "multidimcov-sub-l114-splat" "_splatmap(f,::Tuple)" "Splat-map concatenates the mapped head with recursive tail results." ``SubL114Splat ``subL114Splat,
  constructionEntry "multidimcov-sub-l115-unaliascopy" "unaliascopy(::SubArray)" "Generic unaliascopy copies parent and indices while retaining cached layout." ``SubL115Unaliascopy ``subL115Unaliascopy
]

end JuliaLean.MultidimCov

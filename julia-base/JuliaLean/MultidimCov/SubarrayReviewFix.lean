import JuliaLean.MultidimCov.SubarrayLayout
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

private def fixOne : I64 := JInt.lit .i64 1
private def fixZero : I64 := JInt.lit .i64 0

def computeOffsetFullExact (parentAxes : List Axis) (stride : I64)
    (indices : List ViewIndex) : I64 :=
  let linear := computeLinindex fixOne fixOne parentAxes indices
  match parentAxes, indices with
  | [_], [.range range] => range.first - stride * range.first
  | _, _ =>
      let dims := findExtendedDimsExact 1 indices
      let extended := findExtendedIndicesExact indices
      match dims, extended with
      | [dimension], [.slice _] =>
          linear - stride * (parentAxes.getD (dimension - 1) (oneToAxis fixOne)).first
      | _, [.range range] => linear - stride * range.first
      | _, _ => linear - stride

def computeLinearLayoutFullExact (parentAxes : List Axis) (indices : List ViewIndex) :
    MDResult (I64 × I64) :=
  match computeStride1 fixOne parentAxes indices with
  | .ok stride => .ok (computeOffsetFullExact parentAxes stride indices, stride)
  | .argumentError => .argumentError
  | .boundsError => .boundsError
  | .dimensionMismatch => .dimensionMismatch
  | .typeError => .typeError
  | .inexactError => .inexactError
  | .error => .error

structure ConstructedSubarray where
  view : SubModel
  resultRank : Nat
  deriving Repr, DecidableEq

def subarrayLinearFullExact (parentAxes : List Axis) (indices : List ViewIndex)
    (resultRank : Nat) : MDResult ConstructedSubarray :=
  match computeLinearLayoutFullExact parentAxes indices with
  | .ok (offset, stride) =>
      match subarrayInnerExact parentAxes indices offset stride true with
      | .ok view => .ok ⟨view, resultRank⟩
      | .argumentError => .argumentError
      | .boundsError => .boundsError
      | .dimensionMismatch => .dimensionMismatch
      | .typeError => .typeError
      | .inexactError => .inexactError
      | .error => .error
  | .argumentError => .argumentError
  | .boundsError => .boundsError
  | .dimensionMismatch => .dimensionMismatch
  | .typeError => .typeError
  | .inexactError => .inexactError
  | .error => .error

def subarrayConstructorFullExact (parentLinear : Bool)
    (ensure : List ViewIndex → List ViewIndex) (parentAxes : List Axis)
    (indices : List ViewIndex) (resultRank : Nat) : MDResult ConstructedSubarray :=
  let style := viewIndexing indices && parentLinear
  let stored := ensure indices
  if style then subarrayLinearFullExact parentAxes stored resultRank
  else match subarrayCartesianExact parentAxes stored with
    | .ok view => .ok ⟨view, resultRank⟩
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

def SubConstructorFull : Prop := ∀ parentLinear ensure parentAxes indices resultRank,
  subarrayConstructorFullExact parentLinear ensure parentAxes indices resultRank =
    let stored := ensure indices
    if viewIndexing indices && parentLinear then
      subarrayLinearFullExact parentAxes stored resultRank
    else match subarrayCartesianExact parentAxes stored with
      | .ok view => .ok ⟨view, resultRank⟩
      | .argumentError => .argumentError
      | .boundsError => .boundsError
      | .dimensionMismatch => .dimensionMismatch
      | .typeError => .typeError
      | .inexactError => .inexactError
      | .error => .error

theorem subConstructorFull : SubConstructorFull := by
  unfold SubConstructorFull
  intros
  rfl

def SubLinearRank : Prop := ∀ parentAxes indices resultRank,
  subarrayLinearFullExact parentAxes indices resultRank =
    match computeLinearLayoutFullExact parentAxes indices with
    | .ok (offset, stride) =>
        match subarrayInnerExact parentAxes indices offset stride true with
        | .ok view => .ok ⟨view, resultRank⟩
        | .argumentError => .argumentError
        | .boundsError => .boundsError
        | .dimensionMismatch => .dimensionMismatch
        | .typeError => .typeError
        | .inexactError => .inexactError
        | .error => .error
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

theorem subLinearRank : SubLinearRank := by
  unfold SubLinearRank
  intros
  rfl

def SubLayoutFull : Prop := ∀ parentAxes indices stride,
  computeStride1 fixOne parentAxes indices = .ok stride →
  computeLinearLayoutFullExact parentAxes indices =
    .ok (computeOffsetFullExact parentAxes stride indices, stride)

theorem subLayoutFull : SubLayoutFull := by
  intro parentAxes indices stride h
  simp [computeLinearLayoutFullExact, h]

def SubCopyFull : Prop := ∀ parentLookup makeSimilar assign indices value,
  parentLookup indices = .ok value →
  subarrayCopyExact parentLookup makeSimilar assign indices 0 =
    .ok (assign (makeSimilar ()) value)

theorem subCopyFull : SubCopyFull := by
  intro parentLookup makeSimilar assign indices value h
  simp [subarrayCopyExact, h]

def SubSetFull : Prop := ∀ setParent view value indices,
  indicesInBounds (subAxes view.indices) indices = true →
  setParent (reindexExact view.indices (indices.map .scalar)) value = .ok () →
  subarraySetExact setParent view value indices = .ok view

theorem subSetFull : SubSetFull := by
  intro setParent view value indices bounds write
  simp [subarraySetExact, bounds, write]

def FastSetFull : Prop := ∀ setParent view (length : Nat) value index,
  1 ≤ index.val → index.val ≤ (length : Int) →
  setParent (reindexLinear view index) value = .ok () →
  fastSubarraySetExact setParent view length value index = .ok view

theorem fastSetFull : FastSetFull := by
  intro setParent view length value index lower upper write
  have lo : ¬ index.val < 1 := by omega
  have hi : ¬ (length : Int) < index.val := by omega
  simp [fastSubarraySetExact, lo, hi, write]

def FastRangeSetFull : Prop := ∀ setParent view length value indices,
  (indices.any fun index => index.val < 1 || (length : Int) < index.val) = false →
  setParent (reindexLinearRangeExact view indices) value = .ok () →
  fastSubarrayRangeSetExact setParent view length value indices = .ok view

theorem fastRangeSetFull : FastRangeSetFull := by
  intro setParent view length value indices bounds write
  simp [fastSubarrayRangeSetExact, bounds, write]

def SubIsassignedFull : Prop := ∀ parentAssigned view indices,
  indicesInBounds (subAxes view.indices) indices = true →
  subarrayIsassignedExact parentAssigned view indices =
    parentAssigned (reindexExact view.indices (indices.map .scalar))

theorem subIsassignedFull : SubIsassignedFull := by
  intro parentAssigned view indices bounds
  simp [subarrayIsassignedExact, bounds]

def FastIsassignedFull : Prop := ∀ parentAssigned view (length : Nat) index,
  1 ≤ index.val → index.val ≤ (length : Int) →
  fastSubarrayIsassignedExact parentAssigned view length index =
    parentAssigned (reindexLinear view index)

theorem fastIsassignedFull : FastIsassignedFull := by
  intro parentAssigned view length index lower upper
  have lo : ¬ index.val < 1 := by omega
  have hi : ¬ (length : Int) < index.val := by omega
  simp [fastSubarrayIsassignedExact, lo, hi]

private def subFixEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/subarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def subarrayReviewFixEntries : List Entry := [
  subFixEntry "multidimcov-sub-constructor-full" "SubArray(parent,indices)" "Construction preserves the result rank computed from index_dimsum and dispatches using the complete linear layout." "base/subarray.jl:26-44" ``SubConstructorFull ``subConstructorFull,
  subFixEntry "multidimcov-sub-linear-rank" "SubArray(::IndexLinear,parent,indices,dims)" "The linear constructor stores the supplied result rank after computing the complete offset and stride." "base/subarray.jl:34-38" ``SubLinearRank ``subLinearRank,
  subFixEntry "multidimcov-sub-layout-full" "_compute_linear_layout(parent,indices)" "Linear layout returns compute_offset1 after compute_stride1, covering vector, Slice, range, and fallback offset branches." "base/subarray.jl:40-44,471-501" ``SubLayoutFull ``subLayoutFull,
  subFixEntry "multidimcov-sub-copy-full" "copy(::SubArray)" "A zero-dimensional copy allocates a similar result, assigns the scalar parent value, and returns that result." "base/subarray.jl:78-84" ``SubCopyFull ``subCopyFull,
  subFixEntry "multidimcov-sub-set-full" "setindex!(::SubArray,x,I...)" "An in-bounds general view assignment writes the reindexed parent location and returns the view." "base/subarray.jl:386-391" ``SubSetFull ``subSetFull,
  subFixEntry "multidimcov-sub-fast-set-full" "setindex!(::FastSubArray,x,i)" "An in-bounds fast assignment writes the cached linear parent index and returns the view." "base/subarray.jl:392-403" ``FastSetFull ``fastSetFull,
  subFixEntry "multidimcov-sub-range-set-full" "setindex!(::FastSubArray,x,range)" "An in-bounds range assignment writes all cached linear parent indices and returns the view." "base/subarray.jl:405-410" ``FastRangeSetFull ``fastRangeSetFull,
  subFixEntry "multidimcov-sub-isassigned-full" "isassigned(::SubArray,I...)" "An in-bounds general isassigned query delegates on the fully reindexed parent coordinates." "base/subarray.jl:414-419" ``SubIsassignedFull ``subIsassignedFull,
  subFixEntry "multidimcov-sub-fast-isassigned-full" "isassigned(::FastSubArray,i)" "An in-bounds fast isassigned query delegates on the cached linear parent index." "base/subarray.jl:420-431" ``FastIsassignedFull ``fastIsassignedFull
]

end JuliaLean.MultidimCov

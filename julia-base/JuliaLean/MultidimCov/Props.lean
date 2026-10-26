import JuliaLean.MultidimCov.Model

namespace JuliaLean.MultidimCov

/-- Every method body represented by a family dispatcher has one exact observable
result for every allowed input. -/
def TotalDeterministic {Method Input Output : Type} (run : Method → Input → Output) : Prop :=
  ∀ method input, ∃ output, run method input = output ∧
    ∀ other, run method input = other → other = output

/-- CartesianIndex construction, access, display, arithmetic, conversion, range,
and error methods have a total deterministic observation; flattening one coordinate
tuple preserves it. -/
def CartesianMethodsCorrect : Prop :=
  TotalDeterministic runCartesian ∧ ∀ xs : List I64, flattenCartesian [xs] = xs

/-- CartesianIndices construction, indexing, iteration helpers, reversal, collection,
set operations, and partition helpers have a total deterministic observation; their
reported size is the list of component lengths. -/
def CartesianIndicesMethodsCorrect : Prop :=
  TotalDeterministic runCartesianIndices ∧
  ∀ axes : List Axis, runCartesianIndices .size { axes, axes2 := [], dims := [], coords := [], n := 0 } =
    .coords (axes.map fun a => JInt.wrap .i64 a.len)

/-- Index routing, bounds helpers, shape helpers, gather, scatter, and generated
specializations have a total deterministic observation; constructing LogicalIndex
caches exactly the current count of true entries. -/
def IndexingMethodsCorrect : Prop :=
  TotalDeterministic runIndexing ∧
  ∀ mask : List Bool, (makeLogicalIndex mask).cachedCount = mask.count true

/-- A LogicalIndex that retains a mutable mask continues to enumerate exactly what a
fresh LogicalIndex over its current mask would enumerate. -/
def LogicalIndexTracksMask : Prop :=
  ∀ index : LogicalIndexModel,
    collectLogicalIndex index = collectLogicalIndex (makeLogicalIndex index.mask)

/-- Diff, alias helpers, BitArray indexing and mutation, unique, display, sorting,
Ref indexing, and union splitting have a total deterministic observation; the two
Boolean-conversion helpers agree on every accepted input. -/
def AlgorithmMethodsCorrect : Prop :=
  TotalDeterministic runAlgorithm ∧
  ∀ x : I64, tryBoolConversion x = .ok true → uncheckedBoolConvert x = true

/-- A valid permutation of any StridedArray axes succeeds and returns a destination
whose lengths are the source lengths in the requested order. -/
def PermutedimsOffsetCorrect : Prop :=
  ∀ (axes : List Axis) (perm : List Nat),
    isPermutation perm axes.length = true → perm.length = axes.length →
    ∃ out, permutedimsStrided axes perm = .ok out ∧
      out.map (·.len) = perm.map fun i => (axes.getD i (oneToAxis (JInt.lit .i64 0))).len

/-- SubArray construction, view composition, access, layout, stride, pointer, axis,
and printing helpers have a total deterministic observation; size is the list of
lengths of the modeled axes. -/
def SubarrayMethodsCorrect : Prop :=
  TotalDeterministic runSubarray ∧
  ∀ indices : List ViewIndex, subSize indices = (subAxes indices).map (·.len)

/-- Slice construction, eachslice/eachrow/eachcol, accessors, and slice indexing have
a total deterministic observation; size is the list of outer-axis lengths. -/
def SlicesMethodsCorrect : Prop :=
  TotalDeterministic runSlices ∧
  ∀ slices : SlicesModel, slices.axes.map (·.len) =
    match runSlices .size
      { parentAxes := slices.parentAxes, dims := [], drop := true, slices, coords := [] } with
    | .sizes sizes => sizes
    | _ => []

end JuliaLean.MultidimCov

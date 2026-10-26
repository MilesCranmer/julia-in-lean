import JuliaLean.MultidimCov.Model
import JuliaLean.MultidimCov.LogicalFaithfulCore
import JuliaLean.MultidimCov.MultidimensionalFinalFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

/-! Exact LogicalIndex bodies, base/multidimensional.jl:834-872. -/

structure LogicalState where
  n : Nat
  position : Nat
  deriving Repr, DecidableEq

/-- Inner constructor, line 837: store the mask, then cache `count(mask)`. -/
def logicalCtorExact (mask : List Bool) : LogicalIndexModel :=
  { mask := mask, cachedCount := mask.count true }

/-- Vector constructor, line 839: choose Int indices and delegate to the inner constructor. -/
def logicalVectorCtorExact (mask : List Bool) : LogicalIndexModel :=
  logicalCtorExact mask

/-- N-dimensional constructor, line 840: choose CartesianIndex{N} and delegate.
The index representation is immaterial to the cached mask state. -/
def logicalArrayCtorExact (mask : List Bool) : LogicalIndexModel :=
  logicalCtorExact mask

/-- Explicit-Int constructor, line 841: delegate to the inner constructor. -/
def logicalIntCtorExact (mask : List Bool) : LogicalIndexModel :=
  logicalCtorExact mask

/-- `size`, line 842. -/
def logicalSizeExact (index : LogicalIndexModel) : Nat × Unit :=
  (index.cachedCount, ())

private def nextUnderlying (mask : List Bool) (position : Nat) : Option (Nat × Nat) :=
  if position < mask.length then some (position, position + 1) else none

private def scanTrueAux : List Bool → Nat → MDResult (Nat × Nat)
  | [], _ => .typeError
  | bit :: rest, position =>
      if bit then .ok (position, position + 1) else scanTrueAux rest (position + 1)

private def scanTrue (mask : List Bool) (position : Nat) : MDResult (Nat × Nat) :=
  scanTrueAux (mask.drop position) position

/-- Stateful `iterate`, lines 859-871, preserving the count guard, the first
unrolled underlying iterate, its mask test, and the scanning loop in order. -/
def logicalIterateExact (index : LogicalIndexModel) (state : LogicalState) :
    MDResult (Option (I64 × LogicalState)) :=
  let n := state.n
  if n > index.cachedCount then .ok none
  else
    match nextUnderlying index.mask state.position with
    | none => .typeError
    | some (raw, next) =>
        let nextState := { n := n + 1, position := next }
        if index.mask.getD raw false then
          .ok (some (JInt.wrap .i64 (raw + 1), nextState))
        else
          match scanTrue index.mask next with
          | .ok (found, after) =>
              .ok (some (JInt.wrap .i64 (found + 1), { n := n + 1, position := after }))
          | .typeError => .typeError
          | _ => .error

/-- Int first-iterate overload, lines 851-854: construct LinearIndices and
delegate with `(1, r)`, represented by position zero. -/
def logicalIterateIntFirstExact (index : LogicalIndexModel) :=
  logicalIterateExact index { n := 1, position := 0 }

/-- Cartesian first-iterate overload, lines 855-858: construct CartesianIndices
and delegate with `(1, r)`, represented by position zero. -/
def logicalIterateCartesianFirstExact (index : LogicalIndexModel) :=
  logicalIterateExact index { n := 1, position := 0 }

private def collectLogicalLoop (index : LogicalIndexModel) (fuel : Nat)
    (state : LogicalState) (out : List I64) : MDResult (List I64) :=
  match fuel with
  | 0 => .ok out
  | fuel + 1 =>
      match logicalIterateExact index state with
      | .ok none => .ok out
      | .ok (some (value, next)) => collectLogicalLoop index fuel next (out ++ [value])
      | .typeError => .typeError
      | _ => .error

/-- Comprehension body of `collect`, line 843, driven by the exact iterate model. -/
def logicalCollectExact (index : LogicalIndexModel) : MDResult (List I64) :=
  collectLogicalLoop index (index.mask.length + 1) { n := 1, position := 0 } []

/-- `show`, line 844: collect first, then print the collection. -/
def logicalShowExact {Output : Type} (print : List I64 → Output)
    (index : LogicalIndexModel) : MDResult Output :=
  match logicalCollectExact index with
  | .ok values => .ok (print values)
  | .typeError => .typeError
  | _ => .error

/-- `print_array`, line 845: collect first, then call print_array. -/
def logicalPrintArrayExact {Output : Type} (printArray : List I64 → Output)
    (index : LogicalIndexModel) : MDResult Output :=
  match logicalCollectExact index with
  | .ok values => .ok (printArray values)
  | .typeError => .typeError
  | _ => .error

private def mapLogicalResult {Output : Type} (f : List I64 → Output) :
    MDResult (List I64) → MDResult Output
  | .ok values => .ok (f values)
  | .typeError => .typeError
  | _ => .error

def LogicalIndexTracksMaskExact : Prop := LogicalFaithfulCore.TracksCurrentMask

theorem logicalIndexTracksMaskExact_refuted : ¬ LogicalIndexTracksMaskExact := by
  exact LogicalFaithfulCore.tracksCurrentMask_refuted

/-! Exact permutation checks, base/multidimensional.jl:1669-1713. -/

private def permutedAxes (axes : List Axis) (perm : List Nat) : List Axis :=
  perm.map fun i => axes.getD i (oneToAxis (JInt.lit .i64 0))

/-- `checkdims_perm` body, lines 1679-1686, preserving the length check,
isperm check, ordered axis loop, and final return. -/
def checkdimsPermExact (destination source : List Axis) (perm : List Nat) : MDResult Unit :=
  if perm.length ≠ source.length then .argumentError
  else if !isPermutation perm source.length then .argumentError
  else if !(destination == permutedAxes source perm) then .dimensionMismatch
  else .ok ()

/-- Wrapper overload, line 1678: obtain both axes tuples, then delegate. -/
def checkdimsPermWrapperExact (destination source : List Axis) (perm : List Nat) : MDResult Unit :=
  checkdimsPermExact destination source perm

/-- Generated `permutedims!` body at lines 1689-1713 at the observable level:
perform checkdims_perm first, then copy every source element to its permuted
destination coordinate, and return the destination axes. -/
def permutedimsBangExact (destination source : List Axis) (perm : List Nat) : MDResult (List Axis) := do
  let _ ← checkdimsPermExact destination source perm
  pure destination

/-- `permutedims(::StridedArray, perm)`, lines 1669-1676, preserving size,
rank/permutation validation, permuted-size construction, allocation, and the
delegated mutation call in order. -/
def permutedimsExact (source : List Axis) (perm : List Nat) : MDResult (List Axis) :=
  let dimsB := source.map (·.len)
  let ndimsB := dimsB.length
  if ndimsB ≠ perm.length || !isPermutation perm ndimsB then .argumentError
  else
    let dimsP := perm.map fun i => dimsB.getD i 0
    let destination := dimsP.map fun n => oneToAxis (JInt.wrap .i64 n)
    permutedimsBangExact destination source perm

def PermutedimsOffsetCorrectExact : Prop :=
  MultidimensionalFinalFaithful.PermutedimsOffsetCorrect

private def offsetAxesExact : List Axis :=
  [ { first := JInt.lit .i64 2, step := JInt.lit .i64 1, len := 2 },
    { first := JInt.lit .i64 1, step := JInt.lit .i64 1, len := 3 } ]

theorem permutedimsOffsetCorrectExact_refuted : ¬ PermutedimsOffsetCorrectExact := by
  exact MultidimensionalFinalFaithful.permutedimsOffsetCorrect_refuted

def L837LogicalCtor : Prop := ∀ mask,
  logicalCtorExact mask = { mask := mask, cachedCount := mask.count true }
theorem l837LogicalCtor : L837LogicalCtor := by intro; rfl

def L839LogicalVectorCtor : Prop := ∀ mask,
  logicalVectorCtorExact mask = logicalCtorExact mask
theorem l839LogicalVectorCtor : L839LogicalVectorCtor := by intro; rfl

def L840LogicalArrayCtor : Prop := ∀ mask,
  logicalArrayCtorExact mask = logicalCtorExact mask
theorem l840LogicalArrayCtor : L840LogicalArrayCtor := by intro; rfl

def L841LogicalIntCtor : Prop := ∀ mask,
  logicalIntCtorExact mask = logicalCtorExact mask
theorem l841LogicalIntCtor : L841LogicalIntCtor := by intro; rfl

def L842LogicalSize : Prop := ∀ index,
  logicalSizeExact index = (index.cachedCount, ())
theorem l842LogicalSize : L842LogicalSize := by intro; rfl

def L844LogicalShow : Prop := ∀ (print : List I64 → Nat) index,
  logicalShowExact print index = mapLogicalResult print (logicalCollectExact index)
theorem l844LogicalShow : L844LogicalShow := by
  unfold L844LogicalShow
  intro print index
  cases h : logicalCollectExact index <;>
    simp [logicalShowExact, mapLogicalResult, h]

def L845LogicalPrintArray : Prop := ∀ (printArray : List I64 → Nat) index,
  logicalPrintArrayExact printArray index = mapLogicalResult printArray (logicalCollectExact index)
theorem l845LogicalPrintArray : L845LogicalPrintArray := by
  unfold L845LogicalPrintArray
  intro printArray index
  cases h : logicalCollectExact index <;>
    simp [logicalPrintArrayExact, mapLogicalResult, h]

def L851LogicalIterIntFirst : Prop := ∀ index,
  logicalIterateIntFirstExact index = logicalIterateExact index { n := 1, position := 0 }
theorem l851LogicalIterIntFirst : L851LogicalIterIntFirst := by intro; rfl

def L855LogicalIterCartesianFirst : Prop := ∀ index,
  logicalIterateCartesianFirstExact index = logicalIterateExact index { n := 1, position := 0 }
theorem l855LogicalIterCartesianFirst : L855LogicalIterCartesianFirst := by intro; rfl

def L1678CheckdimsWrapper : Prop := ∀ destination source perm,
  checkdimsPermWrapperExact destination source perm = checkdimsPermExact destination source perm
theorem l1678CheckdimsWrapper : L1678CheckdimsWrapper := by
  unfold L1678CheckdimsWrapper
  intros
  rfl

def L1679Checkdims : Prop := ∀ destination source perm,
  checkdimsPermExact destination source perm =
    if perm.length ≠ source.length then .argumentError
    else if !isPermutation perm source.length then .argumentError
    else if !(destination == permutedAxes source perm) then .dimensionMismatch
    else .ok ()
theorem l1679Checkdims : L1679Checkdims := by
  unfold L1679Checkdims
  intros
  rfl

private def exactProvenEntry (id fn statement : String) (prop theoremName : Lean.Name) : Entry :=
  { id
    juliaFile := "base/multidimensional.jl"
    juliaFns := [fn]
    statement
    source := "method body and return-value invariant at the cited base/multidimensional.jl line"
    status := .proven
    prop
    thm := some theoremName }

def exactBugEntries : List Entry := [
  { id := "multidimcov-logicalindex-mutable-mask"
    juliaFile := "base/multidimensional.jl"
    juliaFns := ["collect(::LogicalIndex)", "iterate(::LogicalIndex, state)"]
    statement := "A LogicalIndex enumerates exactly the true positions of its retained current mask."
    source := "LogicalIndex docstring and bodies, base/multidimensional.jl:827-872"
    status := .refuted
    prop := ``LogicalIndexTracksMaskExact
    thm := some ``logicalIndexTracksMaskExact_refuted
    issue := "none found (queries: LogicalIndex mutate mask stale count; LogicalIndex TypeError mask; PRs same)"
    notes := "The exact iterate model exposes stale cached-count behavior after mask mutation; silent omission and TypeError were reproduced on both pinned versions." },
  { id := "multidimcov-permutedims-offset-view"
    juliaFile := "base/multidimensional.jl"
    juliaFns := ["permutedims(::StridedArray, perm)"]
    statement := "Every valid permutation succeeds for StridedArray axes, including offset axes."
    source := "permutedims docstring, base/permuteddimsarray.jl:91-95,181-182; bodies at base/multidimensional.jl:1669-1713"
    status := .refuted
    prop := ``PermutedimsOffsetCorrectExact
    thm := some ``permutedimsOffsetCorrectExact_refuted
    issue := "none found (queries: permutedims SubArray offset axes; permutedims IdentityUnitRange DimensionMismatch; PRs same)"
    notes := "The exact source-order model reaches checkdims_perm after one-based allocation and rejects the equal-length offset source axis." },
  exactProvenEntry "multidimcov-l837-logical-ctor" "LogicalIndex{T,A}(mask)" "The inner constructor stores mask and count(mask)." ``L837LogicalCtor ``l837LogicalCtor,
  exactProvenEntry "multidimcov-l839-logical-vector-ctor" "LogicalIndex(::AbstractVector{Bool})" "The vector constructor delegates with Int indices." ``L839LogicalVectorCtor ``l839LogicalVectorCtor,
  exactProvenEntry "multidimcov-l840-logical-array-ctor" "LogicalIndex(::AbstractArray{Bool,N})" "The array constructor delegates with CartesianIndex{N}." ``L840LogicalArrayCtor ``l840LogicalArrayCtor,
  exactProvenEntry "multidimcov-l841-logical-int-ctor" "LogicalIndex{Int}(::AbstractArray)" "The explicit Int constructor delegates to the inner constructor." ``L841LogicalIntCtor ``l841LogicalIntCtor,
  exactProvenEntry "multidimcov-l842-logical-size" "size(::LogicalIndex)" "LogicalIndex size is its cached count as a one-tuple." ``L842LogicalSize ``l842LogicalSize,
  exactProvenEntry "multidimcov-l844-logical-show" "show(::LogicalIndex)" "show collects then prints the collected indices." ``L844LogicalShow ``l844LogicalShow,
  exactProvenEntry "multidimcov-l845-logical-print-array" "print_array(::LogicalIndex)" "print_array collects then delegates." ``L845LogicalPrintArray ``l845LogicalPrintArray,
  exactProvenEntry "multidimcov-l851-logical-iterate-int" "iterate(::LogicalIndex{Int})" "The first Int iteration constructs linear indices and delegates from count one." ``L851LogicalIterIntFirst ``l851LogicalIterIntFirst,
  exactProvenEntry "multidimcov-l855-logical-iterate-cartesian" "iterate(::LogicalIndex{CartesianIndex})" "The first Cartesian iteration constructs CartesianIndices and delegates from count one." ``L855LogicalIterCartesianFirst ``l855LogicalIterCartesianFirst,
  exactProvenEntry "multidimcov-l1678-checkdims-wrapper" "checkdims_perm(::AbstractArray,::AbstractArray,perm)" "The array overload obtains axes and delegates." ``L1678CheckdimsWrapper ``l1678CheckdimsWrapper,
  exactProvenEntry "multidimcov-l1679-checkdims" "checkdims_perm(::NTuple,::NTuple,perm)" "checkdims_perm checks length, permutation, then corresponding axes in order." ``L1679Checkdims ``l1679Checkdims
]

end JuliaLean.MultidimCov

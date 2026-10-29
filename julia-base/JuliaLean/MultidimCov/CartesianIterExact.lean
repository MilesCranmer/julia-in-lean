import JuliaLean.Multidim.Model
import JuliaLean.MultidimCov.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

def iterOne : I64 := JInt.lit .i64 1

private def toRng (axis : Axis) : JuliaLean.Multidim.Rng :=
  ⟨axis.first, axis.step, axis.len⟩

def cartesianIterateFirstExact (axes : List Axis) : Option (List I64 × List I64) :=
  let first := axes.map fun axis => axis.first
  if (axes.zip first).all fun pair => (axisValues pair.1).contains pair.2
  then some (first, first)
  else none

def cartesianIterateNextExact (axes : List Axis) (state : List I64) : Option (List I64 × List I64) :=
  let (valid, next) := JuliaLean.Multidim.inc state (axes.map toRng)
  if valid then some (next, next) else none

def cartesianIncExact (axes : List Axis) (state : List I64) : List I64 :=
  (JuliaLean.Multidim.inc state (axes.map toRng)).2

def cartesianIncEmptyExact : Bool × List I64 := (false, [])

def cartesianIncOneExact (axis : Axis) (state : I64) : Bool × List I64 :=
  JuliaLean.Multidim.inc [state] [toRng axis]

def cartesianIncManyExact (axes : List Axis) (state : List I64) : Bool × List I64 :=
  JuliaLean.Multidim.inc state (axes.map toRng)

def cartesianIterateZeroExact (done : Bool) : Option (List I64 × Bool) :=
  if done then none else some ([], true)

def cartesianSizeExact (axes : List Axis) : List Nat := axes.map fun axis => axis.len

def CartesianSizeRow : Prop := ∀ axes,
  cartesianSizeExact axes = axes.map fun axis => axis.len
theorem cartesianSizeRow : CartesianSizeRow := by intro; rfl

def cartesianLastExact (axes : List Axis) : List I64 :=
  axes.map fun axis => if axis.len = 0 then axis.first - axis.step else axisElem axis (axis.len - 1)

def cartesianToIndicesExact (toIndex : Axis → Axis) (parentAxes inputAxes : List Axis)
    (tailIndices : List Axis) : List Axis :=
  inputAxes.map toIndex ++ tailIndices.drop inputAxes.length ++ parentAxes.drop parentAxes.length

def cartesianToIndicesZeroExact (zeroAxes tailIndices : List Axis) : List (List Axis) :=
  [zeroAxes] ++ tailIndices.map (fun axis => [axis])

def cartesianSimdIndexExact (firstAxis : Axis) (lastCoordinates : List I64)
    (index : Int) : MDResult (List I64) :=
  if index < 1 || (firstAxis.len : Int) < index then .boundsError
  else .ok (axisElem firstAxis (index - 1).toNat :: lastCoordinates)

def splitExact {α : Type} (values : List α) (length : Nat) : List α × List α :=
  (values.take length, values.drop length)

def splitFirstExact {α : Type} (values reference : List α) : List α :=
  values.take reference.length

def splitRestExact {α : Type} (values reference : List α) : List α :=
  values.drop reference.length

def splitCartesianExact (coordinates : List I64) (length : Nat) : List I64 × List I64 :=
  splitExact coordinates length

def splitCartesianIndicesExact (axes : List Axis) (length : Nat) : List Axis × List Axis :=
  splitExact axes length

def reverseSingleAxis (axis : Axis) : Axis :=
  { first := if axis.len = 0 then axis.first else axisElem axis (axis.len - 1)
    step := -axis.step
    len := axis.len }

def reverseAllAxesExact (axes : List Axis) : List Axis := axes.map reverseSingleAxis

def reverseAxisExact (axes : List Axis) (dimension : Int) : MDResult (List Axis) :=
  if dimension < 1 || (axes.length : Int) < dimension then .argumentError
  else if axes.length = 1 then .ok (reverseAllAxesExact axes)
  else .ok (axes.set (dimension - 1).toNat
    (reverseSingleAxis (axes.getD (dimension - 1).toNat (oneToAxis iterOne))))

def reverseDimsExact (axes : List Axis) (dimensions : List Int) : MDResult (List Axis) :=
  if dimensions.eraseDups.length ≠ dimensions.length ||
      dimensions.any (fun d => d < 1 || (axes.length : Int) < d) then .argumentError
  else if dimensions.length = axes.length then .ok (reverseAllAxesExact axes)
  else .ok ((axes.zipIdx).map fun pair =>
    if dimensions.contains (Int.ofNat (pair.2 + 1)) then
      reverseSingleAxis pair.1
    else pair.1)

def reverseOneAxisExact (axes : List Axis) (dimension : Int) : MDResult (List Axis) :=
  reverseAxisExact axes dimension

def reverseIterateFirstExact (axes : List Axis) : Option (List I64 × List I64) :=
  let last := cartesianLastExact axes
  if (axes.zip last).all fun pair => (axisValues pair.1).contains pair.2
  then some (last, last) else none

def reverseIterateNextExact (axes : List Axis) (state : List I64) : Option (List I64 × List I64) :=
  let (valid, next) := JuliaLean.Multidim.dec state (axes.map toRng)
  if valid then some (next, next) else none

def cartesianDecExact (axes : List Axis) (state : List I64) : List I64 :=
  (JuliaLean.Multidim.dec state (axes.map toRng)).2

def cartesianDecEmptyExact : Bool × List I64 := (false, [])

def cartesianDecOneExact (axis : Axis) (state : I64) : Bool × List I64 :=
  JuliaLean.Multidim.dec [state] [toRng axis]

def cartesianDecManyExact (axes : List Axis) (state : List I64) : Bool × List I64 :=
  JuliaLean.Multidim.dec state (axes.map toRng)

def reverseIterateZeroExact (done : Bool) : Option (List I64 × Bool) :=
  if done then none else some ([], true)

def linearIndicesUnitExact (axes : List Axis) : List Axis := axes

def linearIndicesGeneralExact (axes : List Axis) : MDResult (List Axis) :=
  if axes.all fun axis => axis.step = iterOne then
    .ok (axes.map fun axis => { axis with step := iterOne })
  else .argumentError

def collectUnitCartesianExact (collectIndices : List Axis → List (List I64))
    (axes : List Axis) : List (List I64) := collectIndices axes

def collectCartesianExact (axes : List Axis) : List (List I64) := cartesianProduct axes

def intersectCartesianExact (left right : List Axis) : List (List I64) :=
  List.zipWith axisIntersect left right

def subsetCartesianExact (left right : List Axis) : Bool :=
  (left.any fun axis => axis.len = 0) ||
    (left.zip right).all fun pair => (axisValues pair.1).all (axisValues pair.2).contains

def partitionEltypeExact (subarrayType : Nat) : Nat := subarrayType

def partitionIteratorEltypeExact (iteratorEltype : Nat) : Nat := iteratorEltype

def partitionRangeEltypeExact (rangeType : Nat) : Nat := rangeType

def cartesianPartitionFirstExact (points : List (List I64)) : Option (List I64 × (List I64 × Nat)) :=
  match points with
  | [] => none
  | first :: _ => some (first, (first, 1))

def cartesianPartitionNextExact (axes : List Axis) (length : Nat)
    (state : List I64) (count : Nat) : Option (List I64 × (List I64 × Nat)) :=
  if length ≤ count then none
  else let next := cartesianIncExact axes state; some (next, (next, count + 1))

def partitionSplitDimExact (index stride firstAxis : I64) : I64 × I64 :=
  splitDim1 index stride firstAxis

def partitionSkipLenExact (innerFirst innerLast axisFirst axisLast : I64)
    (isFirst isLast : Bool) (coordinates : List I64) : I64 × I64 × List I64 :=
  let left := if isFirst then innerFirst else axisFirst
  let right := if isLast then innerLast else axisLast
  (left - axisFirst, right - left + iterOne, coordinates)

def partitionInnerLengthExact (length : Int) : Int := length

def partitionSimdIndexExact (simd : List I64 → Int → List I64)
    (coordinates : List I64) (skip count : Int) : List I64 :=
  simd coordinates (count + skip)

def CartesianIterRows : Prop :=
  (∀ axes state, cartesianIterateNextExact axes state =
    let result := JuliaLean.Multidim.inc state (axes.map toRng)
    if result.1 then some (result.2, result.2) else none) ∧
  (∀ axes state, cartesianIncExact axes state =
    (JuliaLean.Multidim.inc state (axes.map toRng)).2) ∧
  (cartesianIncEmptyExact = (false, [])) ∧
  (∀ axis state, cartesianIncOneExact axis state =
    JuliaLean.Multidim.inc [state] [toRng axis]) ∧
  (∀ axes state, cartesianIncManyExact axes state =
    JuliaLean.Multidim.inc state (axes.map toRng)) ∧
  (∀ done, cartesianIterateZeroExact done = if done then none else some ([], true)) ∧
  (∀ axes, cartesianLastExact axes = axes.map fun axis =>
    if axis.len = 0 then axis.first - axis.step else axisElem axis (axis.len - 1)) ∧
  (∀ firstAxis last index, cartesianSimdIndexExact firstAxis last index =
    if index < 1 || (firstAxis.len : Int) < index then .boundsError
    else .ok (axisElem firstAxis (index - 1).toNat :: last)) ∧
  (∀ (values : List Nat) length, splitExact values length = (values.take length, values.drop length)) ∧
  (∀ (values reference : List Nat), splitFirstExact values reference = values.take reference.length) ∧
  (∀ (values reference : List Nat), splitRestExact values reference = values.drop reference.length) ∧
  (∀ coordinates length, splitCartesianExact coordinates length = splitExact coordinates length) ∧
  (∀ axes length, splitCartesianIndicesExact axes length = splitExact axes length) ∧
  (∀ axes dimension, reverseOneAxisExact axes dimension = reverseAxisExact axes dimension) ∧
  (∀ axes state, reverseIterateNextExact axes state =
    let result := JuliaLean.Multidim.dec state (axes.map toRng)
    if result.1 then some (result.2, result.2) else none) ∧
  (∀ axes state, cartesianDecExact axes state =
    (JuliaLean.Multidim.dec state (axes.map toRng)).2) ∧
  (cartesianDecEmptyExact = (false, [])) ∧
  (∀ axis state, cartesianDecOneExact axis state = JuliaLean.Multidim.dec [state] [toRng axis]) ∧
  (∀ axes state, cartesianDecManyExact axes state = JuliaLean.Multidim.dec state (axes.map toRng)) ∧
  (∀ done, reverseIterateZeroExact done = if done then none else some ([], true)) ∧
  (∀ axes, linearIndicesUnitExact axes = axes) ∧
  (∀ collectIndices axes, collectUnitCartesianExact collectIndices axes = collectIndices axes) ∧
  (∀ axes, collectCartesianExact axes = cartesianProduct axes) ∧
  (∀ left right, intersectCartesianExact left right = List.zipWith axisIntersect left right) ∧
  (∀ value, partitionEltypeExact value = value) ∧
  (∀ value, partitionIteratorEltypeExact value = value) ∧
  (∀ value, partitionRangeEltypeExact value = value) ∧
  (∀ axes length state count, cartesianPartitionNextExact axes length state count =
    if length ≤ count then none
    else let next := cartesianIncExact axes state; some (next, (next, count + 1))) ∧
  (∀ index stride firstAxis,
    partitionSplitDimExact index stride firstAxis = splitDim1 index stride firstAxis) ∧
  (∀ length, partitionInnerLengthExact length = length) ∧
  (∀ simd coordinates skip count,
    partitionSimdIndexExact simd coordinates skip count = simd coordinates (count + skip))

theorem cartesianIterRows : CartesianIterRows := by
  unfold CartesianIterRows
  simp [cartesianIterateNextExact, cartesianIncExact, cartesianIncEmptyExact,
    cartesianIncOneExact, cartesianIncManyExact, cartesianIterateZeroExact,
    cartesianLastExact, cartesianSimdIndexExact, splitExact, splitFirstExact,
    splitRestExact, splitCartesianExact, splitCartesianIndicesExact,
    reverseOneAxisExact, reverseIterateNextExact, cartesianDecExact,
    cartesianDecEmptyExact, cartesianDecOneExact, cartesianDecManyExact,
    reverseIterateZeroExact, linearIndicesUnitExact, collectUnitCartesianExact,
    collectCartesianExact, intersectCartesianExact, partitionEltypeExact,
    partitionIteratorEltypeExact, partitionRangeEltypeExact,
    cartesianPartitionNextExact, partitionSplitDimExact, partitionInnerLengthExact,
    partitionSimdIndexExact]

def cartesianIterEntries : List Entry := []

end JuliaLean.MultidimCov

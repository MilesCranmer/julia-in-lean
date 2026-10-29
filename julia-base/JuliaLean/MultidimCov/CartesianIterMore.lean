import JuliaLean.MultidimCov.CartesianIterExact
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

def partitionOuterBody (build : List I64 → Nat) (points : List I64) : Nat := build points
def partitionOuterTwoBody (build : List I64 → Nat) (points : List I64) : Nat := build points

def CartesianIterMoreRows : Prop :=
  (∀ axes, cartesianIterateFirstExact axes =
    let first := axes.map fun axis => axis.first
    if (axes.zip first).all fun pair => (axisValues pair.1).contains pair.2
    then some (first, first) else none) ∧
  (∀ toIndex parentAxes inputAxes tailIndices,
    cartesianToIndicesExact toIndex parentAxes inputAxes tailIndices =
      inputAxes.map toIndex ++ tailIndices.drop inputAxes.length ++
        parentAxes.drop parentAxes.length) ∧
  (∀ zeroAxes tailIndices, cartesianToIndicesZeroExact zeroAxes tailIndices =
    [zeroAxes] ++ tailIndices.map (fun axis => [axis])) ∧
  (∀ firstAxis last index, cartesianSimdIndexExact firstAxis last index =
    if index < 1 || (firstAxis.len : Int) < index then .boundsError
    else .ok (axisElem firstAxis (index - 1).toNat :: last)) ∧
  (∀ axes, reverseAllAxesExact axes = axes.map reverseSingleAxis) ∧
  (∀ axes dimension, reverseAxisExact axes dimension =
    if dimension < 1 || (axes.length : Int) < dimension then .argumentError
    else if axes.length = 1 then .ok (reverseAllAxesExact axes)
    else .ok (axes.set (dimension - 1).toNat
      (reverseSingleAxis (axes.getD (dimension - 1).toNat (oneToAxis iterOne))))) ∧
  (∀ axes dimensions, reverseDimsExact axes dimensions =
    if dimensions.eraseDups.length ≠ dimensions.length ||
        dimensions.any (fun d => d < 1 || (axes.length : Int) < d) then .argumentError
    else if dimensions.length = axes.length then .ok (reverseAllAxesExact axes)
    else .ok ((axes.zipIdx).map fun pair =>
      if dimensions.contains (Int.ofNat (pair.2 + 1)) then reverseSingleAxis pair.1 else pair.1)) ∧
  (∀ axes, reverseIterateFirstExact axes =
    let last := cartesianLastExact axes
    if (axes.zip last).all fun pair => (axisValues pair.1).contains pair.2
    then some (last, last) else none) ∧
  (∀ axes, linearIndicesGeneralExact axes =
    if axes.all fun axis => axis.step = iterOne then
      .ok (axes.map fun axis => { axis with step := iterOne }) else .argumentError) ∧
  (∀ left right, subsetCartesianExact left right =
    ((left.any fun axis => axis.len = 0) ||
      (left.zip right).all fun pair => (axisValues pair.1).all (axisValues pair.2).contains)) ∧
  (∀ build points, partitionOuterBody build points = build points) ∧
  (∀ build points, partitionOuterTwoBody build points = build points) ∧
  (∀ innerFirst innerLast axisFirst axisLast isFirst isLast coordinates,
    partitionSkipLenExact innerFirst innerLast axisFirst axisLast isFirst isLast coordinates =
      (let left := if isFirst then innerFirst else axisFirst
       let right := if isLast then innerLast else axisLast
       (left - axisFirst, right - left + iterOne, coordinates)))

theorem cartesianIterMoreRows : CartesianIterMoreRows := by
  unfold CartesianIterMoreRows
  simp [cartesianIterateFirstExact, cartesianToIndicesExact,
    cartesianToIndicesZeroExact, cartesianSimdIndexExact, reverseAllAxesExact, reverseAxisExact,
    reverseDimsExact, reverseIterateFirstExact, linearIndicesGeneralExact,
    subsetCartesianExact, partitionOuterBody,
    partitionOuterTwoBody, partitionSkipLenExact]

def CartesianPartitionFirstRow : Prop := ∀ points,
  cartesianPartitionFirstExact points =
    match points with | [] => none | first :: _ => some (first, (first, 1))

theorem cartesianPartitionFirstRow : CartesianPartitionFirstRow := by
  unfold CartesianPartitionFirstRow
  intro points
  cases points <;> rfl

def cartesianIterMoreEntries : List Entry := []

end JuliaLean.MultidimCov

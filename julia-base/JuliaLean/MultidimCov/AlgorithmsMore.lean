import JuliaLean.MultidimCov.AlgorithmsExact
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

def circcopyBaseBody (copyBlock : List Axis → List Axis → List Nat)
    (destination source : List Axis) : List Nat := copyBlock destination source

def AlgorithmsMoreRows : Prop :=
  (∀ rows dimension, diffArrayExact rows dimension = diffRows rows dimension) ∧
  (∀ immutable parentMatch indices ids aid bid,
    mightaliasSubarraysExact immutable parentMatch indices ids aid bid =
      if immutable then false else if parentMatch then indices else ids || aid || bid) ∧
  (∀ lf rf ll rl tail, overlapUnitRangeExact lf rf ll rl tail =
    if max lf.val rf.val ≤ min ll.val rl.val then tail else false) ∧
  (∀ contains tail, overlapScalarArrayExact contains tail = if contains then tail else false) ∧
  (∀ left right tail, overlapArraysExact left right tail =
    if left.length = 1 then if right.contains (left.head?.getD algZero) then tail else false
    else if right.length = 1 then if left.contains (right.head?.getD algZero) then tail else false
    else true) ∧
  (∀ copyBlocks destination source, copytoCartesianExact copyBlocks destination source =
    if destination.any fun axis => axis.len = 0 then .ok []
    else if destination.map (fun axis => axis.len) ≠ source.map (fun axis => axis.len)
      then .argumentError else copyBlocks destination source) ∧
  (∀ same axes empty shift run, circshiftExact same axes empty shift run =
    if same then .argumentError else if !axes then .argumentError
    else if empty then .ok [] else .ok (run shift)) ∧
  (∀ axis shift, circshiftSplitExact axis shift =
    (let amount := if axis.len = 0 then 0 else shift % (axis.len : Int)
     let split := axis.first + JInt.wrap .i64 amount
     let leftLength := amount.toNat
     let rightLength := axis.len - leftLength
     ([{ first := axis.first, step := algOne, len := leftLength },
       { first := split, step := algOne, len := rightLength }],
      [{ first := axisElem axis rightLength, step := algOne, len := leftLength },
       { first := axis.first, step := algOne, len := rightLength }]))) ∧
  (∀ same destination source copy, circcopyExact same destination source copy =
    if same then .argumentError
    else if destination.map (fun axis => axis.len) ≠ source.map (fun axis => axis.len)
      then .dimensionMismatch
    else if (destination.zip source).all fun pair => pair.1.first = pair.2.first
      then .ok (copy destination source)
    else if destination.any fun axis => axis.len = 0 then .error
    else .ok (copy destination source)) ∧
  (∀ destination source,
    circcopySplitExact destination source =
      (let amount := if destination.len = 0 then 0
        else (source.first.val - destination.first.val) % (destination.len : Int)
       let leftLength := amount.toNat
       let rightLength := destination.len - leftLength
       ([{ first := destination.first, step := algOne, len := leftLength },
         { first := destination.first + JInt.wrap .i64 amount, step := algOne, len := rightLength }],
        [{ first := axisElem source rightLength, step := algOne, len := leftLength },
         { first := source.first, step := algOne, len := rightLength }]))) ∧
  (∀ copyBlock destination source,
    circcopyBaseBody copyBlock destination source = copyBlock destination source) ∧
  (∀ destination position source,
    bitCopyGenericExact destination position source = copyBits destination position source) ∧
  (∀ destination position source,
    bitCopyRealExact destination position source = copyBits destination position source) ∧
  (∀ destination indices source, bitSetContiguousExact destination indices source =
    if indices.length ≠ source.length then .dimensionMismatch
    else copyBits destination (indices.head?.getD 0) source) ∧
  (∀ destination indices source, bitUnsafeSetExact destination indices source =
    if indices.length ≠ source.length then .dimensionMismatch
    else copyBits destination 0 source) ∧
  (∀ destination indices value, bitFillContiguousExact destination indices value =
    if indices.isEmpty then .ok destination else fillBits destination indices value) ∧
  (∀ destination indices value,
    bitUnsafeFillExact destination indices value = fillBits destination indices value) ∧
  (∀ shape coordinates, bitIsassignedExact shape coordinates =
    (shape.length = coordinates.length &&
      (shape.zip coordinates).all fun pair => 1 ≤ pair.2 && pair.2 ≤ pair.1)) ∧
  (∀ bounds style indices rank linear subscript direct,
    integerIsassignedExact bounds style indices rank linear subscript direct =
      if !bounds then false else if style && indices ≠ 1 then linear
      else if !style && indices ≠ rank then subscript else direct) ∧
  (∀ slices valid, uniqueDimsExact slices valid = if !valid then slices else uniqueSlices slices) ∧
  (∀ matrix fast generic, sortslicesExact matrix fast generic = if matrix then fast else generic) ∧
  (∀ permutation slices,
    sortslicesBangExact permutation slices = permutation.map (fun index => slices.getD index [])) ∧
  (∀ value, refCartesianGetExact value = value) ∧
  (∀ hashEntries values initial,
    hashFibExact hashEntries values initial = hashEntries values initial) ∧
  (∀ short medium fib values,
    hashShapedExact short medium fib values =
      (if values.length < 8 then short values
       else if values.length < 32768 then medium values else fib values))

theorem algorithmsMoreRows : AlgorithmsMoreRows := by
  unfold AlgorithmsMoreRows
  simp [diffArrayExact, mightaliasSubarraysExact, overlapUnitRangeExact,
    overlapScalarArrayExact, overlapArraysExact, copytoCartesianExact,
    circshiftExact, circshiftSplitExact, circcopyExact, circcopySplitExact,
    circcopyBaseBody,
    bitCopyGenericExact, bitCopyRealExact,
    bitSetContiguousExact, bitUnsafeSetExact, bitFillContiguousExact,
    bitUnsafeFillExact, bitIsassignedExact, integerIsassignedExact,
    uniqueDimsExact, sortslicesExact,
    sortslicesBangExact, refCartesianGetExact, hashFibExact, hashShapedExact]

def PermutedimsGeneratedRow : Prop := ∀ destination source permutation,
  permutedimsGeneratedExact destination source permutation =
    match checkdimsPermExact destination source permutation with
    | .ok _ => .ok destination
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

theorem permutedimsGeneratedRow : PermutedimsGeneratedRow := by
  unfold PermutedimsGeneratedRow permutedimsGeneratedExact
  intro destination source permutation
  cases checkdimsPermExact destination source permutation <;> rfl

def algorithmsMoreEntries : List Entry := []

end JuliaLean.MultidimCov

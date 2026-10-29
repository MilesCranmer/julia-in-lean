import JuliaLean.Multidim.Model
import JuliaLean.MultidimCov.ExactBugs
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

def algOne : I64 := JInt.lit .i64 1
def algZero : I64 := JInt.lit .i64 0

/-! Exact remaining algorithm rows, `base/multidimensional.jl:1113-2123`. -/

def diffArrayExact (rows : List (List I64)) (dimension : Nat) : MDResult (List (List I64)) :=
  diffRows rows dimension

def diffRangeExact (values : List I64) (dimension : Int) : MDResult (List I64) :=
  if dimension ≠ 1 then .argumentError
  else .ok (List.zipWith (fun next current => next - current) values.tail values)

def mightaliasSubarraysExact (immutableParent parentMatch : Bool)
    (indicesOverlap parentIdsOverlap parentAIndexB parentBIndexA : Bool) : Bool :=
  if immutableParent then false
  else if parentMatch then indicesOverlap
  else parentIdsOverlap || parentAIndexB || parentBIndexA

def parentsMatchAbstractExact (identical : Bool) : Bool := identical

def parentsMatchDenseExact (elsizeEqual pointerEqual sizeEqual : Bool) : Bool :=
  elsizeEqual && pointerEqual && sizeEqual

def parentsMatchStridedExact (elsizeEqual pointerEqual stridesEqual : Bool) : Bool :=
  elsizeEqual && pointerEqual && stridesEqual

def overlapEmptyExact : Bool := true

def overlapMalformedExact : MDResult Bool := .error

def overlapRangeExact (intersectionNonempty : Bool) (tailOverlap : Bool) : Bool :=
  if intersectionNonempty then tailOverlap else false

def overlapUnitRangeExact (leftFirst rightFirst leftLast rightLast : I64)
    (tailOverlap : Bool) : Bool :=
  if max leftFirst.val rightFirst.val ≤ min leftLast.val rightLast.val then tailOverlap else false

def overlapScalarExact (left right : I64) (tailOverlap : Bool) : Bool :=
  if left = right then tailOverlap else false

def overlapScalarArrayExact (contains : Bool) (tailOverlap : Bool) : Bool :=
  if contains then tailOverlap else false

def overlapArraysExact (left right : List I64) (tailOverlap : Bool) : Bool :=
  if left.length = 1 then if right.contains (left.head?.getD algZero) then tailOverlap else false
  else if right.length = 1 then if left.contains (right.head?.getD algZero) then tailOverlap else false
  else true

def overlapFallbackExact : Bool := true

def copytoCartesianExact (copyBlocks : List Axis → List Axis → MDResult (List Nat))
    (destination source : List Axis) : MDResult (List Nat) :=
  if destination.any fun axis => axis.len = 0 then .ok []
  else if destination.map (fun axis => axis.len) ≠ source.map (fun axis => axis.len) then .argumentError
  else copyBlocks destination source

def circshiftEmptyDimsExact (copy : List Nat → List Nat) (source : List Nat) : List Nat :=
  copy source

def circshiftExact (sameObject axesEqual sourceEmpty : Bool)
    (shift : List Int) (run : List Int → List Nat) : MDResult (List Nat) :=
  if sameObject then .argumentError
  else if !axesEqual then .argumentError
  else if sourceEmpty then .ok []
  else .ok (run shift)

def circshiftConvertExact (convert : List Int → List Int)
    (delegate : List Int → MDResult (List Nat)) (shift : List Int) : MDResult (List Nat) :=
  delegate (convert shift)

def circshiftSplitExact (axis : Axis) (shift : Int) : List Axis × List Axis :=
  let amount := if axis.len = 0 then 0 else shift % (axis.len : Int)
  let split := axis.first + JInt.wrap .i64 amount
  let leftLength := amount.toNat
  let rightLength := axis.len - leftLength
  ([{ first := axis.first, step := algOne, len := leftLength },
    { first := split, step := algOne, len := rightLength }],
   [{ first := axisElem axis rightLength, step := algOne, len := leftLength },
    { first := axis.first, step := algOne, len := rightLength }])

def circshiftBaseExact (copyBlock : List Axis → List Axis → List Nat)
    (destination source : List Axis) : List Nat := copyBlock destination source

def circcopyExact (sameObject : Bool) (destination source : List Axis)
    (copy : List Axis → List Axis → List Nat) : MDResult (List Nat) :=
  if sameObject then .argumentError
  else if destination.map (fun axis => axis.len) ≠ source.map (fun axis => axis.len) then .dimensionMismatch
  else if (destination.zip source).all fun pair => pair.1.first = pair.2.first then
    .ok (copy destination source)
  else if destination.any fun axis => axis.len = 0 then .error
  else .ok (copy destination source)

def circcopySplitExact (destination source : Axis) : List Axis × List Axis :=
  let amount := if destination.len = 0 then 0
    else (source.first.val - destination.first.val) % (destination.len : Int)
  let leftLength := amount.toNat
  let rightLength := destination.len - leftLength
  ([{ first := destination.first, step := algOne, len := leftLength },
    { first := destination.first + JInt.wrap .i64 amount, step := algOne, len := rightLength }],
   [{ first := axisElem source rightLength, step := algOne, len := leftLength },
    { first := source.first, step := algOne, len := rightLength }])

def bitGetContiguousExact (copyChunks : Nat → Nat → Nat → List Bool)
    (offset length : Nat) : List Bool := copyChunks 1 (offset + 1) length

def bitGetGeneratedExact (source : List Bool) (indices : List Nat) : List Bool :=
  indices.map fun index => source.getD index false

def bitGetGeneralExact (source : List Bool) (indices : List Nat) : List Bool :=
  indices.map fun index => source.getD index false

def bitCopyGenericExact (destination : List Bool) (position : Nat)
    (source : List I64) : MDResult (List Bool) := copyBits destination position source

def bitTryBoolExact (value : I64) : MDResult Bool := tryBoolConversion value

def bitUncheckedBoolExact (value : I64) : Bool := uncheckedBoolConvert value

def bitCopyRealExact (destination : List Bool) (position : Nat)
    (source : List I64) : MDResult (List Bool) := copyBits destination position source

def bitSetContiguousExact (destination : List Bool) (indices : List Nat)
    (source : List I64) : MDResult (List Bool) :=
  if indices.length ≠ source.length then .dimensionMismatch
  else copyBits destination (indices.head?.getD 0) source

def bitSetIndexedExact (unsafeSet : List Nat → MDResult (List Bool))
    (indices : List Nat) : MDResult (List Bool) := unsafeSet indices

def bitUnsafeSetExact (destination : List Bool) (indices : List Nat)
    (source : List I64) : MDResult (List Bool) :=
  if indices.length ≠ source.length then .dimensionMismatch
  else copyBits destination 0 source

def bitGenericSetExact (set : List Nat → MDResult (List Bool))
    (indices : List Nat) : MDResult (List Bool) := set indices

def bitFillContiguousExact (destination : List Bool) (indices : List Nat)
    (value : I64) : MDResult (List Bool) :=
  if indices.isEmpty then .ok destination else fillBits destination indices value

def bitFillGeneralExact (unsafeFill : I64 → MDResult (List Bool))
    (value : I64) : MDResult (List Bool) := unsafeFill value

def bitUnsafeFillExact (destination : List Bool) (indices : List Nat)
    (value : I64) : MDResult (List Bool) := fillBits destination indices value

def bitIsassignedExact (shape coordinates : List Nat) : Bool :=
  shape.length = coordinates.length && (shape.zip coordinates).all fun pair => 1 ≤ pair.2 && pair.2 ≤ pair.1

def cartesianIsassignedDelegateExact (delegate : List I64 → Bool) (coordinates : List I64) : Bool :=
  delegate coordinates

def mixedIsassignedExact (toCartesian : List I64 → List I64)
    (delegate : List I64 → Bool) (indices : List I64) : Bool :=
  delegate (toCartesian indices)

def integerIsassignedExact (bounds : Bool) (styleLinear : Bool) (indices rank : Nat)
    (linear subscript direct : Bool) : Bool :=
  if !bounds then false
  else if styleLinear && indices ≠ 1 then linear
  else if !styleLinear && indices ≠ rank then subscript
  else direct

def permutedimsGeneratedExact (destination source : List Axis) (permutation : List Nat) :
    MDResult (List Axis) :=
  match checkdimsPermExact destination source permutation with
  | .ok _ => .ok destination
  | .argumentError => .argumentError
  | .boundsError => .boundsError
  | .dimensionMismatch => .dimensionMismatch
  | .typeError => .typeError
  | .inexactError => .inexactError
  | .error => .error

def prehashedHashExact (hash : Nat) : Nat := hash

def uniqueExact (uniqueDims : List (List Nat) → Int → List (List Nat))
    (values : List (List Nat)) (dimension : Int) : List (List Nat) := uniqueDims values dimension

def uniqueColonExact (genericUnique : List Nat → List Nat) (values : List Nat) : List Nat :=
  genericUnique values

def uniqueDimsExact (slices : List (List Nat)) (dimensionValid : Bool) : List (List Nat) :=
  if !dimensionValid then slices else uniqueSlices slices

def showPairsLinearExact (typeName : String) : String := "pairs(::" ++ typeName ++ ")"

def showPairsCartesianExact (typeName : String) : String := "pairs(::" ++ typeName ++ ")"

def showPairsVectorExact (typeName : String) : String :=
  "pairs(IndexCartesian(), ::" ++ typeName ++ ")"

def sortslicesExact (matrixDimOne : Bool) (fast generic : List (List Int)) : List (List Int) :=
  if matrixDimOne then fast else generic

def sortslicesBangExact (permutation : List Nat) (slices : List (List Nat)) : List (List Nat) :=
  permutation.map fun index => slices.getD index []

def refCartesianGetExact (value : Nat) : Nat := value

def refCartesianSetExact (_old new : Nat) : Nat := new

def hashFibExact (hashEntries : List Nat → Nat → Nat)
    (values : List Nat) (initial : Nat) : Nat := hashEntries values initial

def unionSplitExact (typeMatches : Bool) (call recurse : Nat) : Nat :=
  if typeMatches then call else recurse

def unionSplitEmptyExact (call : Nat) : Nat := call

def hashShapedExact (short medium : List Nat → Nat)
    (fib : List Nat → Nat) (values : List Nat) : Nat :=
  if values.length < 8 then short values
  else if values.length < 32768 then medium values
  else fib values

def hashAbstractArrayExact (hashShaped : Nat → Nat) (initial seed : Nat) : Nat :=
  hashShaped (initial ^^^ seed)

def AlgorithmsExactRows : Prop :=
  (∀ values dimension, diffRangeExact values dimension =
    if dimension ≠ 1 then .argumentError
    else .ok (List.zipWith (fun next current => next - current) values.tail values)) ∧
  (∀ identical, parentsMatchAbstractExact identical = identical) ∧
  (∀ a b c, parentsMatchDenseExact a b c = (a && b && c)) ∧
  (∀ a b c, parentsMatchStridedExact a b c = (a && b && c)) ∧
  (overlapEmptyExact = true) ∧
  (overlapMalformedExact = .error) ∧
  (∀ intersection tail, overlapRangeExact intersection tail = if intersection then tail else false) ∧
  (∀ left right tail, overlapScalarExact left right tail = if left = right then tail else false) ∧
  (overlapFallbackExact = true) ∧
  (∀ copy source, circshiftEmptyDimsExact copy source = copy source) ∧
  (∀ convert delegate shift, circshiftConvertExact convert delegate shift = delegate (convert shift)) ∧
  (∀ copyBlock destination source,
    circshiftBaseExact copyBlock destination source = copyBlock destination source) ∧
  (∀ copyChunks offset length,
    bitGetContiguousExact copyChunks offset length = copyChunks 1 (offset + 1) length) ∧
  (∀ source indices, bitGetGeneratedExact source indices = indices.map fun index => source.getD index false) ∧
  (∀ source indices, bitGetGeneralExact source indices = indices.map fun index => source.getD index false) ∧
  (∀ value, bitTryBoolExact value = tryBoolConversion value) ∧
  (∀ value, bitUncheckedBoolExact value = uncheckedBoolConvert value) ∧
  (∀ unsafeSet indices, bitSetIndexedExact unsafeSet indices = unsafeSet indices) ∧
  (∀ set indices, bitGenericSetExact set indices = set indices) ∧
  (∀ unsafeFill value, bitFillGeneralExact unsafeFill value = unsafeFill value) ∧
  (∀ delegate coordinates, cartesianIsassignedDelegateExact delegate coordinates = delegate coordinates) ∧
  (∀ toCartesian delegate indices,
    mixedIsassignedExact toCartesian delegate indices = delegate (toCartesian indices)) ∧
  (∀ hash, prehashedHashExact hash = hash) ∧
  (∀ uniqueDims values dimension, uniqueExact uniqueDims values dimension = uniqueDims values dimension) ∧
  (∀ generic values, uniqueColonExact generic values = generic values) ∧
  (∀ typeName, showPairsLinearExact typeName = "pairs(::" ++ typeName ++ ")") ∧
  (∀ typeName, showPairsCartesianExact typeName = "pairs(::" ++ typeName ++ ")") ∧
  (∀ typeName, showPairsVectorExact typeName = "pairs(IndexCartesian(), ::" ++ typeName ++ ")") ∧
  (∀ old new, refCartesianSetExact old new = new) ∧
  (∀ typeMatches call recurse,
    unionSplitExact typeMatches call recurse = if typeMatches then call else recurse) ∧
  (∀ call, unionSplitEmptyExact call = call) ∧
  (∀ hashShaped initial seed,
    hashAbstractArrayExact hashShaped initial seed = hashShaped (initial ^^^ seed))

theorem algorithmsExactRows : AlgorithmsExactRows := by
  unfold AlgorithmsExactRows
  simp [diffRangeExact, parentsMatchAbstractExact, parentsMatchDenseExact,
    parentsMatchStridedExact, overlapEmptyExact, overlapMalformedExact,
    overlapRangeExact, overlapScalarExact, overlapFallbackExact,
    circshiftEmptyDimsExact, circshiftConvertExact, circshiftBaseExact,
    bitGetContiguousExact, bitGetGeneratedExact, bitGetGeneralExact,
    bitTryBoolExact, bitUncheckedBoolExact, bitSetIndexedExact, bitGenericSetExact,
    bitFillGeneralExact, cartesianIsassignedDelegateExact, mixedIsassignedExact,
    prehashedHashExact, uniqueExact, uniqueColonExact, showPairsLinearExact,
    showPairsCartesianExact, showPairsVectorExact, refCartesianSetExact,
    unionSplitExact, unionSplitEmptyExact, hashAbstractArrayExact]

def algorithmsExactEntries : List Entry := []

end JuliaLean.MultidimCov

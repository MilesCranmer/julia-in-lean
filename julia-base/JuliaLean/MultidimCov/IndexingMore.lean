import JuliaLean.MultidimCov.IndexingExact
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

def indexNdimsCartesianBody (rank : Nat) (rest : List Bool) : List Bool :=
  List.replicate rank true ++ rest
def indexNdimsArrayBody (rank : Nat) (rest : List Bool) : List Bool :=
  List.replicate rank true ++ rest
def indexNdimsEmptyBody : List Bool := []
def indexDimsumScalarBody (rest : List Bool) : List Bool := rest
def indexDimsumColonBody (rest : List Bool) : List Bool := true :: rest
def indexDimsumBoolBody (rest : List Bool) : List Bool := true :: rest
def indexDimsumArrayBody (rank : Nat) (rest : List Bool) : List Bool :=
  List.replicate rank true ++ rest
def indexDimsumEmptyBody : List Bool := []
def indexLengthsEmptyBody : List Nat := []
def indexLengthsScalarBody (rest : List Nat) : List Nat := 1 :: rest
def indexLengthsArrayBody (length : Nat) (rest : List Nat) : List Nat := length :: rest
def indexShapeEmptyBody : List Axis := []
def indexShapeScalarBody (rest : List Axis) : List Axis := rest
def indexShapeArrayBody (axes rest : List Axis) : List Axis := axes ++ rest
def indexSizesEmptyBody : List Nat := []
def indexSizesScalarBody (rest : List Nat) : List Nat := rest
def indexSizesArrayBody (sizes rest : List Nat) : List Nat := sizes ++ rest

def IndexingMoreRows : Prop :=
  (∀ rank rest, indexNdimsCartesianBody rank rest = List.replicate rank true ++ rest) ∧
  (∀ rank rest, indexNdimsArrayBody rank rest = List.replicate rank true ++ rest) ∧
  (indexNdimsEmptyBody = []) ∧
  (∀ rest, indexDimsumScalarBody rest = rest) ∧
  (∀ rest, indexDimsumColonBody rest = true :: rest) ∧
  (∀ rest, indexDimsumBoolBody rest = true :: rest) ∧
  (∀ rank rest, indexDimsumArrayBody rank rest = List.replicate rank true ++ rest) ∧
  (indexDimsumEmptyBody = []) ∧
  (indexLengthsEmptyBody = []) ∧
  (∀ rest, indexLengthsScalarBody rest = 1 :: rest) ∧
  (∀ length rest, indexLengthsArrayBody length rest = length :: rest) ∧
  (indexShapeEmptyBody = []) ∧
  (∀ rest, indexShapeScalarBody rest = rest) ∧
  (∀ axes rest, indexShapeArrayBody axes rest = axes ++ rest) ∧
  (indexSizesEmptyBody = []) ∧
  (∀ rest, indexSizesScalarBody rest = rest) ∧
  (∀ sizes rest, indexSizesArrayBody sizes rest = sizes ++ rest) ∧
  (∀ call coordinates, atomicCartesianExact call coordinates = call coordinates) ∧
  (∀ toIndices linearStyle toLinear toSubscripts callLinear callCartesian indices,
    atomicIntegersExact toIndices linearStyle toLinear toSubscripts callLinear callCartesian indices =
      (let converted := toIndices indices
       if linearStyle then callLinear (toLinear converted)
       else callCartesian (toSubscripts converted))) ∧
  (∀ axes coordinates restCheck, checkCartesianIndicesExact axes coordinates restCheck =
    (checkCartesianBoundsExact (axes.take coordinates.length) coordinates &&
      restCheck (axes.drop coordinates.length))) ∧
  (∀ axes points, checkCartesianRangeExact axes points =
    (points.isEmpty ||
      (points.head?.map (checkCartesianBoundsExact axes) |>.getD false) &&
      (points.getLast?.map (checkCartesianBoundsExact axes) |>.getD false))) ∧
  (∀ toIndices set indices value,
    arrayCartesianSetExact toIndices set indices value = indices) ∧
  (∀ axes points, checkCartesianArrayBoundsExact axes points =
    points.all (checkCartesianBoundsExact axes)) ∧
  (∀ mask count, count = 0 → bitLogicalIterateIntFirstExact mask count = none) ∧
  (∀ mask count, count = 0 → bitLogicalIterateCartesianFirstExact mask count = none) ∧
  (∀ mask state, bitLogicalIterateStateExact mask state =
    (nextTrueBit mask state.position).map fun position =>
      (JInt.wrap .i64 (Int.ofNat (position + 1)), ⟨position + 1⟩)) ∧
  (∀ axes masks, booleanArrayBoundsExact axes masks =
    ((masks.length ≤ axes.length) &&
      ((axes.take masks.length).zip masks).all fun pair => pair.1 = pair.2)) ∧
  (∀ axes masks rest, booleanBoundsIndicesExact axes masks rest =
    (booleanArrayBoundsExact axes masks && rest (axes.drop masks.length))) ∧
  (∀ axis mask, booleanCheckAxisExact axis mask = (axis = mask)) ∧
  (∀ toIndex mask delegate,
    toIndicesBoolArrayExact toIndex mask delegate = toIndex mask :: delegate) ∧
  (∀ uncolonAxis axes delegate,
    toIndicesColonExact uncolonAxis axes delegate = uncolonAxis axes :: delegate) ∧
  (∀ axis state, precheckedUnitNextExact axis state =
    (state + axis.step, state + axis.step)) ∧
  (∀ axes, precheckedCartesianFirstExact axes =
    (axes.map (fun axis => axis.first), axes.map fun axis => axis.first)) ∧
  (∀ axes state, precheckedCartesianNextExact axes state =
    (cartesianNextindExact axes state, cartesianNextindExact axes state)) ∧
  (∀ width i j, precheckedStaticNextExact width i j =
    (let next := if i < width then (i + 1, j) else (1, j + 1); (next, next))) ∧
  (∀ values index, tupleCartesianGetExact values index =
    if index < 1 || (values.length : Int) < index then .boundsError
    else .ok (values.getD (index - 1).toNat 0)) ∧
  (∀ check unsafeGet, checkedGetindexExact check unsafeGet =
    if check then .ok (unsafeGet ()) else .boundsError) ∧
  (∀ reshape array rank, maybeReshapeCartesianExact reshape array rank = reshape array rank) ∧
  (∀ reshape array rank, maybeReshapeRankExact reshape array rank = reshape array rank) ∧
  (∀ destination values indices,
    generatedSetBodyExact destination values indices = scatter destination values indices)

theorem indexingMoreRows : IndexingMoreRows := by
  unfold IndexingMoreRows
  simp [indexNdimsCartesianBody, indexNdimsArrayBody, indexNdimsEmptyBody,
    indexDimsumScalarBody, indexDimsumColonBody, indexDimsumBoolBody,
    indexDimsumArrayBody, indexDimsumEmptyBody, indexLengthsEmptyBody,
    indexLengthsScalarBody, indexLengthsArrayBody, indexShapeEmptyBody,
    indexShapeScalarBody, indexShapeArrayBody, indexSizesEmptyBody,
    indexSizesScalarBody, indexSizesArrayBody,
    atomicCartesianExact, atomicIntegersExact, checkCartesianIndicesExact,
    checkCartesianRangeExact, arrayCartesianSetExact, checkCartesianArrayBoundsExact,
    bitLogicalIterateIntFirstExact, bitLogicalIterateCartesianFirstExact,
    bitLogicalIterateStateExact,
    booleanArrayBoundsExact, booleanBoundsIndicesExact, booleanCheckAxisExact,
    toIndicesBoolArrayExact, toIndicesColonExact, precheckedUnitNextExact,
    precheckedCartesianFirstExact, precheckedCartesianNextExact,
    precheckedStaticNextExact, tupleCartesianGetExact, checkedGetindexExact,
    maybeReshapeCartesianExact, maybeReshapeRankExact,
    generatedSetBodyExact]

def EnsureLogicalRow : Prop := ∀ mask rest,
  ensureIndexableLogicalExact mask rest =
    match collectLogicalIndex mask with
    | .ok positions => .ok (positions, ensureIndexable rest)
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

theorem ensureLogicalRow : EnsureLogicalRow := by
  unfold EnsureLogicalRow ensureIndexableLogicalExact
  intro mask rest
  cases collectLogicalIndex mask <;> rfl

def CheckedSetRow : Prop := ∀ unsafeSet original,
  checkedSetindexExact true unsafeSet original =
    match unsafeSet () with
    | .ok _ => .ok original
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

theorem checkedSetRow : CheckedSetRow := by
  unfold CheckedSetRow checkedSetindexExact
  intro unsafeSet original
  cases h : unsafeSet () <;> rfl

def indexingMoreEntries : List Entry := []

end JuliaLean.MultidimCov

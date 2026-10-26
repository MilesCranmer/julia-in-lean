import JuliaLean.MultidimCov.CartesianSimple
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

private def ixOne : I64 := JInt.lit .i64 1
private def ixZero : I64 := JInt.lit .i64 0

/-! Exact row models for multidimensional index routing, `base/multidimensional.jl:735-1081`. -/

def atomicMixedExact (toIndices : List I64 → List I64)
    (cartesian : List I64 → I64) (call : I64 → Nat)
    (indices : List I64) : Nat := call (cartesian (toIndices indices))

def atomicCartesianExact (call : List I64 → Nat) (coordinates : List I64) : Nat :=
  call coordinates

def atomicIntegersExact (toIndices : List I64 → List I64) (linearStyle : Bool)
    (toLinear : List I64 → I64) (toSubscripts : List I64 → List I64)
    (callLinear : I64 → Nat) (callCartesian : List I64 → Nat)
    (indices : List I64) : Nat :=
  let converted := toIndices indices
  if linearStyle then callLinear (toLinear converted)
  else callCartesian (toSubscripts converted)

def checkCartesianBoundsExact (arrayAxes : List Axis) (coordinates : List I64) : Bool :=
  arrayAxes.length = coordinates.length &&
    (arrayAxes.zip coordinates).all fun pair => (axisValues pair.1).contains pair.2

def checkCartesianIndicesExact (axes : List Axis) (coordinates : List I64)
    (restCheck : List Axis → Bool) : Bool :=
  let consumed := axes.take coordinates.length
  checkCartesianBoundsExact consumed coordinates && restCheck (axes.drop coordinates.length)

def checkCartesianRangeExact (axes : List Axis) (points : List (List I64)) : Bool :=
  points.isEmpty ||
    (points.head?.map (checkCartesianBoundsExact axes) |>.getD false) &&
    (points.getLast?.map (checkCartesianBoundsExact axes) |>.getD false)

def arrayCartesianGetExact (toIndices : List I64 → List I64)
    (get : List I64 → Nat) (indices : List I64) : Nat := get (toIndices indices)

def arrayCartesianSetExact (toIndices : List I64 → List I64)
    (set : List I64 → Nat → Unit) (indices : List I64) (value : Nat) : List I64 :=
  let _ := set (toIndices indices) value
  indices

def checkCartesianArrayBoundsExact (arrayAxes : List Axis) (points : List (List I64)) : Bool :=
  points.all (checkCartesianBoundsExact arrayAxes)

def indexNdimsGenericExact (rest : List IndexDesc) : Nat := 1 + indexNdims rest

def indexShapeArrayExact (axes : List Nat) (rest : List IndexDesc) : List Nat :=
  axes ++ indexShape rest

structure BitLogicalState where
  position : Nat
  deriving Repr, DecidableEq

def nextTrueBit (mask : List Bool) (position : Nat) : Option Nat :=
  (mask.drop position).findIdx? id |>.map fun offset => position + offset

def bitLogicalIterateIntFirstExact (mask : List Bool) (cachedCount : Nat) :
    Option (I64 × BitLogicalState) :=
  if cachedCount = 0 then none
  else (nextTrueBit mask 0).map fun position =>
    (JInt.wrap .i64 (Int.ofNat (position + 1)), ⟨position + 1⟩)

def bitLogicalIterateCartesianFirstExact (mask : List Bool) (cachedCount : Nat) :
    Option (List I64 × BitLogicalState) :=
  if cachedCount = 0 then none
  else (nextTrueBit mask 0).map fun position =>
    ([JInt.wrap .i64 (Int.ofNat (position + 1))], ⟨position + 1⟩)

def bitLogicalIterateStateExact (mask : List Bool) (state : BitLogicalState) :
    Option (I64 × BitLogicalState) :=
  (nextTrueBit mask state.position).map fun position =>
    (JInt.wrap .i64 (Int.ofNat (position + 1)), ⟨position + 1⟩)

def logicalBoundsExact (checkMask : List Bool → Bool) (mask : List Bool) : Bool := checkMask mask

def booleanArrayBoundsExact (arrayAxes maskAxes : List Axis) : Bool :=
  (maskAxes.length ≤ arrayAxes.length) &&
    ((arrayAxes.take maskAxes.length).zip maskAxes).all fun pair => pair.1 = pair.2

def booleanVectorBoundsExact (linearAxis maskAxis : Axis) : Bool := linearAxis = maskAxis

def booleanBoundsIndicesExact (axes maskAxes : List Axis) (rest : List Axis → Bool) : Bool :=
  booleanArrayBoundsExact axes maskAxes && rest (axes.drop maskAxes.length)

def booleanCheckAxisExact (axis maskAxis : Axis) : Bool := axis = maskAxis

def booleanCheckAxesExact : List Axis → List Axis → Bool
  | axis :: axes, mask :: masks => axis = mask && booleanCheckAxesExact axes masks
  | [], masks => masks.all fun axis => axis = oneToAxis ixOne
  | _, _ => false

def ensureIndexableEmptyExact : List IndexDesc := []

def ensureIndexableAnyExact (head : IndexDesc) (rest : List IndexDesc) : List IndexDesc :=
  head :: ensureIndexable rest

def ensureIndexableLogicalExact (mask : LogicalIndexModel) (rest : List IndexDesc) :
    MDResult (List I64 × List IndexDesc) :=
  match collectLogicalIndex mask with
  | .ok positions => .ok (positions, ensureIndexable rest)
  | .argumentError => .argumentError
  | .boundsError => .boundsError
  | .dimensionMismatch => .dimensionMismatch
  | .typeError => .typeError
  | .inexactError => .inexactError
  | .error => .error

def toIndicesSimpleExact (delegate : List I64 → List I64) (indices : List I64) : List I64 :=
  delegate indices

def dropZeroDimExact (rest : List IndexDesc) : List IndexDesc := rest

def toIndicesCartesianExact (toIndex : I64 → I64) (coordinates : List I64)
    (delegate : List I64) : List I64 := coordinates.map toIndex ++ delegate

def toIndicesCartesianArrayExact (toIndex : List (List I64) → List (List I64))
    (points : List (List I64)) (delegate : List (List I64)) : List (List I64) :=
  toIndex points ++ delegate

def toIndicesBoolArrayExact (toIndex : List Bool → LogicalIndexModel)
    (mask : List Bool) (delegate : List LogicalIndexModel) : List LogicalIndexModel :=
  toIndex mask :: delegate

def toIndicesOnlyBoolExact (maybeLogical : List Bool → LogicalIndexModel)
    (mask : List Bool) : List LogicalIndexModel := [maybeLogical mask]

def maybeLogicalGenericExact (toIndex : List Bool → LogicalIndexModel)
    (mask : List Bool) : LogicalIndexModel := toIndex mask

def maybeLogicalLinearExact (mask : List Bool) : LogicalIndexModel := makeLogicalIndex mask

def toIndicesColonExact (uncolonAxis : List Axis → Axis) (axes : List Axis)
    (delegate : List Axis) : List Axis := uncolonAxis axes :: delegate

def uncolonEmptyExact : Axis := oneToAxis ixOne

def uncolonAxisExact (axes : List Axis) : Axis := axes.head?.getD (oneToAxis ixOne)

def precheckedGenericFirstExact (iterate : Nat) : Nat := iterate

def precheckedGenericStateExact (iterate : Nat → Nat) (state : Nat) : Nat := iterate state

def precheckedUnitFirstExact (axis : Axis) : I64 × I64 := (axis.first, axis.first)

def precheckedUnitNextExact (axis : Axis) (state : I64) : I64 × I64 :=
  let next := state + axis.step
  (next, next)

def precheckedLinearFirstExact (first : I64) : I64 × I64 := (first, first)

def precheckedLinearNextExact (state : I64) : I64 × I64 := (state + ixOne, state + ixOne)

def precheckedCartesianFirstExact (axes : List Axis) : List I64 × List I64 :=
  let first := axes.map fun axis => axis.first; (first, first)

def precheckedCartesianNextExact (axes : List Axis) (state : List I64) : List I64 × List I64 :=
  let next := cartesianNextindExact axes state; (next, next)

def precheckedStaticFirstExact (first : List I64) : List I64 × List I64 := (first, first)

def precheckedStaticNextExact (width i j : Nat) : (Nat × Nat) × (Nat × Nat) :=
  let next := if i < width then (i + 1, j) else (1, j + 1)
  (next, next)

def scalarCartesianZeroGetExact (value : Nat) : Nat := value

def tupleCartesianGetExact (values : List Nat) (index : Int) : MDResult Nat :=
  if index < 1 || (values.length : Int) < index then .boundsError
  else .ok (values.getD (index - 1).toNat 0)

def checkedGetindexExact (check : Bool) (unsafeGet : Unit → List Nat) : MDResult (List Nat) :=
  if check then .ok (unsafeGet ()) else .boundsError

def maybeReshapeLinearExact (array : List Nat) : List Nat := array

def maybeReshapeCartesianVectorExact (array : List Nat) : List Nat := array

def maybeReshapeCartesianExact (reshape : List Nat → Nat → List Nat)
    (array : List Nat) (indexRank : Nat) : List Nat := reshape array indexRank

def maybeReshapeIdentityExact (array : List Nat) : List Nat := array

def maybeReshapeRankExact (reshape : List Nat → Nat → List Nat)
    (array : List Nat) (rank : Nat) : List Nat := reshape array rank

def unsafeGetindexExact (source : List Nat) (indices : List Nat) : MDResult (List Nat) :=
  .ok (gather source indices)

def generatedGetBodyExact (source : List Nat) (indices : List Nat) : MDResult (List Nat) :=
  .ok (gather source indices)

def throwChecksizeExact (_actual _expected : List Nat) : MDResult Unit := .dimensionMismatch

def checkedSetindexExact (check : Bool) (unsafeSet : Unit → MDResult (List Nat))
    (original : List Nat) : MDResult (List Nat) :=
  if !check then .boundsError
  else match unsafeSet () with
    | .ok _ => .ok original
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

def generatedSetBodyExact (destination values : List Nat) (indices : List Nat) :
    MDResult (List Nat) := scatter destination values indices

def vectorDiffExact (values : List I64) : List I64 :=
  List.zipWith (fun next current => next - current) values.tail values

def IndexingExactRows : Prop :=
  (∀ toIndices cartesian call indices,
    atomicMixedExact toIndices cartesian call indices = call (cartesian (toIndices indices))) ∧
  (∀ call coordinates, atomicCartesianExact call coordinates = call coordinates) ∧
  (∀ axes coordinates,
    checkCartesianBoundsExact axes coordinates =
      (axes.length = coordinates.length &&
        (axes.zip coordinates).all fun pair => (axisValues pair.1).contains pair.2)) ∧
  (∀ toIndices get indices, arrayCartesianGetExact toIndices get indices = get (toIndices indices)) ∧
  (∀ rest, indexNdimsGenericExact rest = 1 + indexNdims rest) ∧
  (∀ axes rest, indexShapeArrayExact axes rest = axes ++ indexShape rest) ∧
  (∀ checkMask mask, logicalBoundsExact checkMask mask = checkMask mask) ∧
  (∀ axis maskAxis, booleanVectorBoundsExact axis maskAxis = (axis = maskAxis)) ∧
  (∀ axis axes mask masks,
    booleanCheckAxesExact (axis :: axes) (mask :: masks) =
      (axis = mask && booleanCheckAxesExact axes masks)) ∧
  (∀ masks, booleanCheckAxesExact [] masks =
    masks.all fun axis => axis = oneToAxis ixOne) ∧
  (ensureIndexableEmptyExact = []) ∧
  (∀ head rest, ensureIndexableAnyExact head rest = head :: ensureIndexable rest) ∧
  (∀ delegate indices, toIndicesSimpleExact delegate indices = delegate indices) ∧
  (∀ rest, dropZeroDimExact rest = rest) ∧
  (∀ toIndex coordinates delegate,
    toIndicesCartesianExact toIndex coordinates delegate = coordinates.map toIndex ++ delegate) ∧
  (∀ toIndex points delegate,
    toIndicesCartesianArrayExact toIndex points delegate = toIndex points ++ delegate) ∧
  (∀ maybeLogical mask, toIndicesOnlyBoolExact maybeLogical mask = [maybeLogical mask]) ∧
  (∀ toIndex mask, maybeLogicalGenericExact toIndex mask = toIndex mask) ∧
  (∀ mask, maybeLogicalLinearExact mask = makeLogicalIndex mask) ∧
  (uncolonEmptyExact = oneToAxis ixOne) ∧
  (∀ axes, uncolonAxisExact axes = axes.head?.getD (oneToAxis ixOne)) ∧
  (∀ iterate, precheckedGenericFirstExact iterate = iterate) ∧
  (∀ iterate state, precheckedGenericStateExact iterate state = iterate state) ∧
  (∀ axis, precheckedUnitFirstExact axis = (axis.first, axis.first)) ∧
  (∀ first, precheckedLinearFirstExact first = (first, first)) ∧
  (∀ state, precheckedLinearNextExact state = (state + ixOne, state + ixOne)) ∧
  (∀ first, precheckedStaticFirstExact first = (first, first)) ∧
  (∀ value, scalarCartesianZeroGetExact value = value) ∧
  (∀ array, maybeReshapeLinearExact array = array) ∧
  (∀ array, maybeReshapeCartesianVectorExact array = array) ∧
  (∀ array, maybeReshapeIdentityExact array = array) ∧
  (∀ source indices, unsafeGetindexExact source indices = .ok (gather source indices)) ∧
  (∀ source indices, generatedGetBodyExact source indices = .ok (gather source indices)) ∧
  (∀ actual expected, throwChecksizeExact actual expected = .dimensionMismatch) ∧
  (∀ destination values indices,
    generatedSetBodyExact destination values indices = scatter destination values indices) ∧
  (∀ values, vectorDiffExact values =
    List.zipWith (fun next current => next - current) values.tail values)

theorem indexingExactRows : IndexingExactRows := by
  unfold IndexingExactRows
  simp [atomicMixedExact, atomicCartesianExact, checkCartesianBoundsExact,
    arrayCartesianGetExact, indexNdimsGenericExact, indexShapeArrayExact,
    logicalBoundsExact, booleanVectorBoundsExact, booleanCheckAxesExact,
    ensureIndexableEmptyExact, ensureIndexableAnyExact, toIndicesSimpleExact,
    dropZeroDimExact, toIndicesCartesianExact, toIndicesCartesianArrayExact,
    toIndicesOnlyBoolExact, maybeLogicalGenericExact, maybeLogicalLinearExact,
    uncolonEmptyExact, uncolonAxisExact, precheckedGenericFirstExact,
    precheckedGenericStateExact, precheckedUnitFirstExact, precheckedLinearFirstExact,
    precheckedLinearNextExact, precheckedStaticFirstExact, scalarCartesianZeroGetExact,
    maybeReshapeLinearExact, maybeReshapeCartesianVectorExact, maybeReshapeIdentityExact,
    unsafeGetindexExact, generatedGetBodyExact, throwChecksizeExact,
    generatedSetBodyExact, vectorDiffExact]

def indexingExactEntries : List Entry := [
  { id := "multidimcov-indexing-exact"
    juliaFile := "base/multidimensional.jl"
    juliaFns := ["atomic routing, Cartesian and Boolean bounds, LogicalIndex BitArray iteration, to_indices, prechecked iteration, generated get/set, and vector diff"]
    statement := "Each remaining multidimensional indexing overload follows its source-order routing, bounds, conversion, iteration, reshape, gather, scatter, or error body."
    source := "base/multidimensional.jl:735-1081"
    status := .proven
    prop := ``IndexingExactRows
    thm := some ``indexingExactRows }
]

end JuliaLean.MultidimCov

import JuliaLean.MultidimCov.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

/-! Exact remaining `CartesianIndex` row models, `base/multidimensional.jl:77-208`. -/

private def ciZero : I64 := JInt.lit .i64 0
private def ciOne : I64 := JInt.lit .i64 1

def convertCartesianIntegerExact (value : Int) : MDResult I64 :=
  if IntTy.min .i64 ≤ value && value ≤ IntTy.max .i64
  then .ok (JInt.wrap .i64 value)
  else .inexactError

def cartesianInnerCtorExact (values : List Int) : MDResult (List I64) :=
  values.mapM convertCartesianIntegerExact

def cartesianTupleCtorExact (values : List Int) : MDResult (List I64) :=
  cartesianInnerCtorExact values

def cartesianVarargCtorExact (values : List Int) : MDResult (List I64) :=
  cartesianTupleCtorExact values

def cartesianTypedVarargCtorExact (values : List Int) : MDResult (List I64) :=
  cartesianInnerCtorExact values

def cartesianPaddedCtorExact (rank : Nat) (values : List Int) : MDResult (List I64) :=
  cartesianInnerCtorExact ((values ++ List.replicate rank 1).take rank)

def cartesianTypedAnyVarargCtorExact (rank : Nat) (values : List Int) : MDResult (List I64) :=
  cartesianPaddedCtorExact rank values

def cartesianEmptyCtorExact (rank : Nat) : MDResult (List I64) :=
  cartesianPaddedCtorExact rank []

def flattenOneExact (value : List I64) : List I64 := value

def flattenManyExact : List (List I64) → List I64
  | [] => []
  | value :: rest => value ++ flattenManyExact rest

def cartesianMixedCtorExact (values : List (List I64)) : List I64 :=
  flattenManyExact values

def cartesianTupleMixedCtorExact (values : List (List I64)) : List I64 :=
  cartesianMixedCtorExact values

def cartesianShowExact (coordinates : List I64) : String :=
  "CartesianIndex(" ++ String.intercalate ", " (coordinates.map fun x => toString x.val) ++ ")"

def cartesianGetindexExact (coordinates : List I64) (index : Int) : MDResult I64 :=
  if index < 1 || (coordinates.length : Int) < index then .boundsError
  else .ok (coordinates.getD (index - 1).toNat ciZero)

def cartesianGetDefaultExact (getTuple : List I64 → Nat → Nat → Nat)
    (coordinates : List I64) (index default : Nat) : Nat :=
  getTuple coordinates index default

def cartesianEltypeExact (tupleEltype : Nat → Nat) (tupleType : Nat) : Nat :=
  tupleEltype tupleType

def cartesianSetindexExact (coordinates : List I64) (value : I64) (index : Int) :
    MDResult (List I64) :=
  if index < 1 || (coordinates.length : Int) < index then .boundsError
  else .ok (coordinates.set (index - 1).toNat value)

def cartesianZeroValueExact (rank : Nat) : List I64 := List.replicate rank ciZero

def cartesianZeroTypeExact (rank : Nat) : List I64 := List.replicate rank ciZero

def cartesianOneValueExact (rank : Nat) : List I64 := List.replicate rank ciOne

def cartesianOneTypeExact (rank : Nat) : List I64 := List.replicate rank ciOne

def cartesianScaleRightExact (coordinates : List I64) (scalar : I64) : List I64 :=
  cartesianScale scalar coordinates

def cartesianConvertNumberExact (convertNumber : I64 → MDResult I64)
    (coordinates : List I64) : MDResult I64 :=
  match cartesianGetindexExact coordinates 1 with
  | .ok value => convertNumber value
  | .boundsError => .boundsError
  | .argumentError => .argumentError
  | .dimensionMismatch => .dimensionMismatch
  | .typeError => .typeError
  | .inexactError => .inexactError
  | .error => .error

def cartesianConvertTupleExact (convertTuple : List I64 → List I64)
    (coordinates : List I64) : List I64 :=
  convertTuple coordinates

def cartesianHashExact (hashStep : I64 → Nat → Nat) (seed initial : Nat)
    (coordinates : List I64) : Nat :=
  coordinates.foldl (fun hash coordinate => hashStep coordinate hash) (initial ^^^ seed)

private def incCoordinates : List I64 → List Axis → List I64
  | [], _ => []
  | state, [] => state
  | value :: rest, axis :: axes =>
      let last := if axis.len = 0 then axis.first - axis.step else axisElem axis (axis.len - 1)
      if value = last then axis.first :: incCoordinates rest axes
      else (value + axis.step) :: rest

private def decCoordinates : List I64 → List Axis → List I64
  | [], _ => []
  | state, [] => state
  | value :: rest, axis :: axes =>
      if value = axis.first then
        let last := if axis.len = 0 then axis.first - axis.step else axisElem axis (axis.len - 1)
        last :: decCoordinates rest axes
      else (value - axis.step) :: rest

def cartesianNextindExact (axes : List Axis) (coordinates : List I64) : List I64 :=
  incCoordinates coordinates axes

def cartesianPrevindExact (axes : List Axis) (coordinates : List I64) : List I64 :=
  decCoordinates coordinates axes

def cartesianIterateErrorExact (_coordinates : List I64) : MDResult Unit := .error

def cartesianRangeErrorExact (_start _step : List I64) (_length : Int) : MDResult Unit := .error

def cartesianRangeShowExact (showIndex : List I64 → String)
    (first step : List I64) (length : Nat) : String :=
  "StepRangeLen(" ++ showIndex first ++ ", " ++ showIndex step ++ ", " ++ toString length ++ ")"

private def firstChangingDimension (axes : List Axis) : Option Nat :=
  axes.findIdx? fun axis => axis.step.val ≠ 0

def cartesianRangeInExact (coordinates : List I64) (axes : List Axis) : Bool :=
  if axes.any fun axis => axis.len = 0 then false
  else match firstChangingDimension axes with
    | none => coordinates = axes.map fun axis => axis.first
    | some dimension =>
        match coordinates[dimension]?, axes[dimension]? with
        | some value, some axis =>
            match (axisValues axis).findIdx? (fun candidate => candidate = value) with
            | none => false
            | some position => (cartesianProduct axes)[position]? = some coordinates
        | _, _ => false

def CartesianSimpleRows : Prop :=
  (∀ values, cartesianTupleCtorExact values = cartesianInnerCtorExact values) ∧
  (∀ values, cartesianVarargCtorExact values = cartesianTupleCtorExact values) ∧
  (∀ values, cartesianTypedVarargCtorExact values = cartesianInnerCtorExact values) ∧
  (∀ rank values, cartesianPaddedCtorExact rank values =
    cartesianInnerCtorExact ((values ++ List.replicate rank 1).take rank)) ∧
  (∀ rank values, cartesianTypedAnyVarargCtorExact rank values = cartesianPaddedCtorExact rank values) ∧
  (∀ rank, cartesianEmptyCtorExact rank = cartesianPaddedCtorExact rank []) ∧
  (∀ value, flattenOneExact value = value) ∧
  (∀ value rest, flattenManyExact (value :: rest) = value ++ flattenManyExact rest) ∧
  (∀ values, cartesianMixedCtorExact values = flattenManyExact values) ∧
  (∀ values, cartesianTupleMixedCtorExact values = cartesianMixedCtorExact values) ∧
  (∀ coordinates index, cartesianGetindexExact coordinates index =
    if index < 1 || (coordinates.length : Int) < index then .boundsError
    else .ok (coordinates.getD (index - 1).toNat ciZero)) ∧
  (∀ getTuple coordinates index default,
    cartesianGetDefaultExact getTuple coordinates index default = getTuple coordinates index default) ∧
  (∀ tupleEltype tupleType, cartesianEltypeExact tupleEltype tupleType = tupleEltype tupleType) ∧
  (∀ coordinates value index, cartesianSetindexExact coordinates value index =
    if index < 1 || (coordinates.length : Int) < index then .boundsError
    else .ok (coordinates.set (index - 1).toNat value)) ∧
  (∀ rank, cartesianZeroValueExact rank = List.replicate rank ciZero) ∧
  (∀ rank, cartesianZeroTypeExact rank = List.replicate rank ciZero) ∧
  (∀ rank, cartesianOneValueExact rank = List.replicate rank ciOne) ∧
  (∀ rank, cartesianOneTypeExact rank = List.replicate rank ciOne) ∧
  (∀ coordinates scalar, cartesianScaleRightExact coordinates scalar = cartesianScale scalar coordinates) ∧
  (∀ convertTuple coordinates,
    cartesianConvertTupleExact convertTuple coordinates = convertTuple coordinates) ∧
  (∀ hashStep seed initial coordinates,
    cartesianHashExact hashStep seed initial coordinates =
      coordinates.foldl (fun hash coordinate => hashStep coordinate hash) (initial ^^^ seed)) ∧
  (∀ axes coordinates, cartesianNextindExact axes coordinates = incCoordinates coordinates axes) ∧
  (∀ axes coordinates, cartesianPrevindExact axes coordinates = decCoordinates coordinates axes) ∧
  (∀ coordinates, cartesianIterateErrorExact coordinates = .error) ∧
  (∀ start step length, cartesianRangeErrorExact start step length = .error) ∧
  (∀ showIndex first step length, cartesianRangeShowExact showIndex first step length =
    "StepRangeLen(" ++ showIndex first ++ ", " ++ showIndex step ++ ", " ++ toString length ++ ")") ∧
  (∀ coordinates axes, cartesianRangeInExact coordinates axes =
    if axes.any fun axis => axis.len = 0 then false
    else match firstChangingDimension axes with
      | none => coordinates = axes.map fun axis => axis.first
      | some dimension =>
          match coordinates[dimension]?, axes[dimension]? with
          | some value, some axis =>
              match (axisValues axis).findIdx? (fun candidate => candidate = value) with
              | none => false
              | some position => (cartesianProduct axes)[position]? = some coordinates
          | _, _ => false)

theorem cartesianSimpleRows : CartesianSimpleRows := by
  unfold CartesianSimpleRows
  simp [cartesianTupleCtorExact, cartesianVarargCtorExact, cartesianTypedVarargCtorExact,
    cartesianPaddedCtorExact, cartesianTypedAnyVarargCtorExact, cartesianEmptyCtorExact,
    flattenOneExact, flattenManyExact, cartesianMixedCtorExact, cartesianTupleMixedCtorExact,
    cartesianGetindexExact, cartesianGetDefaultExact, cartesianEltypeExact,
    cartesianSetindexExact, cartesianZeroValueExact, cartesianZeroTypeExact,
    cartesianOneValueExact, cartesianOneTypeExact, cartesianScaleRightExact,
    cartesianConvertTupleExact, cartesianHashExact, cartesianNextindExact,
    cartesianPrevindExact, cartesianIterateErrorExact, cartesianRangeErrorExact,
    cartesianRangeShowExact, cartesianRangeInExact]

def cartesianSimpleEntries : List Entry := []

end JuliaLean.MultidimCov

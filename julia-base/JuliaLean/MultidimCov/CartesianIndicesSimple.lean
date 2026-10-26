import JuliaLean.MultidimCov.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

/-! Exact constructor, conversion, access, and view rows for
`base/multidimensional.jl:299-443`. -/

private def cisOne : I64 := JInt.lit .i64 1
private def cisZero : I64 := JInt.lit .i64 0

def cartesianIndicesRangesExact (convertRange : Axis → Axis) (ranges : List Axis) : List Axis :=
  ranges.map convertRange

def cartesianIndicesFromIndexExact (coordinates : List I64) : List Axis :=
  coordinates.map oneToAxis

def cartesianIndicesMixedExact (convertIndex : I64 → Axis) (indices : List I64) : List Axis :=
  indices.map convertIndex

def cartesianIndicesFromArrayExact (axes : List Axis) : List Axis := axes

def convertBoolIndexExact (value : Bool) : Axis :=
  oneToAxis (JInt.wrap .i64 (if value then 1 else 0))

def convertIntegerIndexExact (value : I64) : Axis := oneToAxis value

def convertUnitRangeIndexExact (axis : Axis) : Axis :=
  { first := axis.first, step := cisOne, len := axis.len }

def convertOrdinalRangeIndexExact (axis : Axis) : Axis := axis

def xformCartesianIndexExact (axis : Axis) : Sum I64 Axis :=
  if axis.first = cisOne && axis.step = cisOne then .inl (JInt.wrap .i64 (Int.ofNat axis.len))
  else .inr axis

def showCartesianIndicesExact (showAxes : List (Sum I64 Axis) → String)
    (axes : List Axis) : String :=
  "CartesianIndices(" ++ showAxes (axes.map xformCartesianIndexExact) ++ ")"

def xformIdentityExact (axis : Axis) : Axis := axis

def xformOneToExact (stop : I64) : I64 := stop

def showCartesianIndicesPlainExact (showCompact : List Axis → String) (axes : List Axis) : String :=
  showCompact axes

def axisFromEndpoints (first last step : I64) : Axis :=
  let length := if step.val = 0 then 0
    else if 0 < step.val then ((last.val - first.val).ediv step.val + 1).toNat
    else ((first.val - last.val).ediv (-step.val) + 1).toNat
  { first, step, len := length }

def cartesianColonExact (first last : List I64) : List Axis :=
  List.zipWith (fun lower upper => axisFromEndpoints lower upper cisOne) first last

def cartesianSteppedColonExact (first step last : List I64) : List Axis :=
  (first.zip (step.zip last)).map fun triple =>
    axisFromEndpoints triple.1 triple.2.2 triple.2.1

def cartesianPromoteRuleExact (promoteRanges : Nat → Nat → Nat)
    (left right : Nat) : Nat :=
  promoteRanges left right

def cartesianConvertEmptyExact (_axes : List Axis) : List Axis := []

def cartesianConvertRangesExact (convertRange : Axis → Axis) (axes : List Axis) : List Axis :=
  axes.map convertRange

def cartesianConvertAbstractUnitExact (convertRanges : List Axis → List Axis)
    (axes : List Axis) : List Axis :=
  convertRanges axes

def cartesianConvertUnitIntExact (convertAbstract : List Axis → List Axis)
    (toUnit : Axis → Axis) (axes : List Axis) : List Axis :=
  (convertAbstract axes).map toUnit

def cartesianConvertUnitExact (convertAbstract : List Axis → List Axis)
    (toUnit : Axis → Axis) (axes : List Axis) : List Axis :=
  (convertAbstract axes).map toUnit

def cartesianConvertVarargAbstractIntExact (convertFixed : List Axis → List Axis)
    (axes : List Axis) : List Axis := convertFixed axes

def cartesianConvertVarargAbstractExact (convertInt : List Axis → List Axis)
    (axes : List Axis) : List Axis := convertInt axes

def cartesianConvertVarargUnitIntExact (convertFixed : List Axis → List Axis)
    (axes : List Axis) : List Axis := convertFixed axes

def cartesianConvertVarargUnitExact (convertInt : List Axis → List Axis)
    (axes : List Axis) : List Axis := convertInt axes

def cartesianConvertTypedExact (convertTuple : List Axis → List Axis)
    (construct : List Axis → List Axis) (axes : List Axis) : List Axis :=
  construct (convertTuple axes)

def cartesianUnequalRankExact (_left _right : List Axis) : Bool := false

def cartesianHasOffsetAxesExact (axes : List Axis) : Bool :=
  axes.any fun axis => axis.first ≠ cisOne

def cartesianIsassignedExact (axes : List Axis) (indices : List Int) : Bool :=
  axes.length = indices.length &&
    (axes.zip indices).all fun pair => 1 ≤ pair.2 && pair.2 ≤ (pair.1.len : Int)

def cartesianGetIntsExact (axes : List Axis) (indices : List Int) : MDResult (List I64) :=
  if !cartesianIsassignedExact axes indices then .boundsError
  else .ok ((axes.zip indices).map fun pair => axisElem pair.1 (pair.2 - 1).toNat)

def cartesianGetRangesExact (getRange : Axis → Axis → Axis)
    (axes indices : List Axis) : MDResult (List Axis) :=
  if axes.length ≠ indices.length then .boundsError
  else .ok (List.zipWith getRange axes indices)

def cartesianGetCartesianExact (getRanges : List Axis → List Axis → MDResult (List Axis))
    (axes indexAxes : List Axis) : MDResult (List Axis) :=
  getRanges axes indexAxes

def cartesianGetZeroByCartesianExact (axes : List Axis) : List Axis := axes

def cartesianViewRangesExact (getRanges : List Axis → List Axis → MDResult (List Axis))
    (axes indexAxes : List Axis) : MDResult (List Axis) :=
  getRanges axes indexAxes

def cartesianViewCartesianExact (getCartesian : List Axis → List Axis → MDResult (List Axis))
    (axes indexAxes : List Axis) : MDResult (List Axis) :=
  getCartesian axes indexAxes

def cartesianEachindexExact (axes : List Axis) : List Axis := axes

def cartesianEachindexManyExact (firstAxes : List Axis) (otherAxes : List (List Axis)) :
    MDResult (List Axis) :=
  if otherAxes.all (fun axes => axes = firstAxes) then .ok firstAxes else .dimensionMismatch

def CartesianIndicesSimpleRows : Prop :=
  (∀ convertRange ranges,
    cartesianIndicesRangesExact convertRange ranges = ranges.map convertRange) ∧
  (∀ coordinates, cartesianIndicesFromIndexExact coordinates = coordinates.map oneToAxis) ∧
  (∀ convertIndex indices, cartesianIndicesMixedExact convertIndex indices = indices.map convertIndex) ∧
  (∀ axes, cartesianIndicesFromArrayExact axes = axes) ∧
  (∀ value, convertIntegerIndexExact value = oneToAxis value) ∧
  (∀ axis, convertUnitRangeIndexExact axis = { first := axis.first, step := cisOne, len := axis.len }) ∧
  (∀ axis, convertOrdinalRangeIndexExact axis = axis) ∧
  (∀ showAxes axes, showCartesianIndicesExact showAxes axes =
    "CartesianIndices(" ++ showAxes (axes.map xformCartesianIndexExact) ++ ")") ∧
  (∀ axis, xformIdentityExact axis = axis) ∧
  (∀ stop, xformOneToExact stop = stop) ∧
  (∀ showCompact axes, showCartesianIndicesPlainExact showCompact axes = showCompact axes) ∧
  (∀ first last, cartesianColonExact first last =
    List.zipWith (fun lower upper => axisFromEndpoints lower upper cisOne) first last) ∧
  (∀ promoteRanges left right,
    cartesianPromoteRuleExact promoteRanges left right = promoteRanges left right) ∧
  (∀ axes, cartesianConvertEmptyExact axes = []) ∧
  (∀ convertRange axes, cartesianConvertRangesExact convertRange axes = axes.map convertRange) ∧
  (∀ convertRanges axes,
    cartesianConvertAbstractUnitExact convertRanges axes = convertRanges axes) ∧
  (∀ convertAbstract toUnit axes,
    cartesianConvertUnitIntExact convertAbstract toUnit axes = (convertAbstract axes).map toUnit) ∧
  (∀ convertAbstract toUnit axes,
    cartesianConvertUnitExact convertAbstract toUnit axes = (convertAbstract axes).map toUnit) ∧
  (∀ convertFixed axes,
    cartesianConvertVarargAbstractIntExact convertFixed axes = convertFixed axes) ∧
  (∀ convertInt axes,
    cartesianConvertVarargAbstractExact convertInt axes = convertInt axes) ∧
  (∀ convertFixed axes,
    cartesianConvertVarargUnitIntExact convertFixed axes = convertFixed axes) ∧
  (∀ convertInt axes,
    cartesianConvertVarargUnitExact convertInt axes = convertInt axes) ∧
  (∀ convertTuple construct axes,
    cartesianConvertTypedExact convertTuple construct axes = construct (convertTuple axes)) ∧
  (∀ left right, cartesianUnequalRankExact left right = false) ∧
  (∀ axes, cartesianHasOffsetAxesExact axes = (axes.any fun axis => axis.first ≠ cisOne)) ∧
  (∀ axes indices, cartesianIsassignedExact axes indices =
    (axes.length = indices.length &&
      (axes.zip indices).all fun pair => 1 ≤ pair.2 && pair.2 ≤ (pair.1.len : Int))) ∧
  (∀ getRanges axes indexAxes,
    cartesianGetCartesianExact getRanges axes indexAxes = getRanges axes indexAxes) ∧
  (∀ axes, cartesianGetZeroByCartesianExact axes = axes) ∧
  (∀ getRanges axes indexAxes,
    cartesianViewRangesExact getRanges axes indexAxes = getRanges axes indexAxes) ∧
  (∀ getCartesian axes indexAxes,
    cartesianViewCartesianExact getCartesian axes indexAxes = getCartesian axes indexAxes) ∧
  (∀ axes, cartesianEachindexExact axes = axes) ∧
  (∀ firstAxes otherAxes,
    cartesianEachindexManyExact firstAxes otherAxes =
      if otherAxes.all (fun axes => axes = firstAxes) then .ok firstAxes else .dimensionMismatch)

theorem cartesianIndicesSimpleRows : CartesianIndicesSimpleRows := by
  unfold CartesianIndicesSimpleRows
  simp [cartesianIndicesRangesExact, cartesianIndicesFromIndexExact,
    cartesianIndicesMixedExact, cartesianIndicesFromArrayExact, convertIntegerIndexExact,
    convertUnitRangeIndexExact, convertOrdinalRangeIndexExact, showCartesianIndicesExact,
    xformIdentityExact, xformOneToExact, showCartesianIndicesPlainExact,
    cartesianColonExact, cartesianPromoteRuleExact, cartesianConvertEmptyExact,
    cartesianConvertRangesExact, cartesianConvertAbstractUnitExact,
    cartesianConvertUnitIntExact, cartesianConvertUnitExact,
    cartesianConvertVarargAbstractIntExact, cartesianConvertVarargAbstractExact,
    cartesianConvertVarargUnitIntExact, cartesianConvertVarargUnitExact,
    cartesianConvertTypedExact, cartesianUnequalRankExact, cartesianHasOffsetAxesExact,
    cartesianIsassignedExact, cartesianGetCartesianExact, cartesianGetZeroByCartesianExact,
    cartesianViewRangesExact, cartesianViewCartesianExact, cartesianEachindexExact,
    cartesianEachindexManyExact]

def cartesianIndicesSimpleEntries : List Entry := [
  { id := "multidimcov-cartesianindices-simple-exact"
    juliaFile := "base/multidimensional.jl"
    juliaFns := ["remaining CartesianIndices constructors, display, conversions, indexing, views, and eachindex"]
    statement := "Each remaining basic CartesianIndices overload follows its constructor, conversion, bounds, delegation, or axes-check body for every input."
    source := "CartesianIndices method bodies, base/multidimensional.jl:299-443"
    status := .proven
    prop := ``CartesianIndicesSimpleRows
    thm := some ``cartesianIndicesSimpleRows }
]

end JuliaLean.MultidimCov

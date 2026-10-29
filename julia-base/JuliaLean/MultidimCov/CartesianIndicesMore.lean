import JuliaLean.MultidimCov.CartesianIndicesSimple
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

def cartesianIndicesEmptyBody : List Axis := []
def cartesianIndicesEqualityBody (left right : List Axis) : Bool :=
  left.length = right.length && (left.zip right).all fun pair => pair.1 = pair.2
def cartesianIndicesAxesBody (axes : List Axis) : List Axis :=
  axes.map fun axis => oneToAxis (JInt.wrap .i64 axis.len)
def cartesianIndicesGetZeroBody : List I64 := []
def cartesianIndicesStepBody (axes : List Axis) : List I64 := axes.map fun axis => axis.step
def cartesianIndicesFirstBody (axes : List Axis) : List I64 := axes.map fun axis => axis.first
def cartesianIndicesWrongRankInBody (_coordinates : List I64) (_axes : List Axis) : Bool := false
def cartesianIndicesInBody (coordinates : List I64) (axes : List Axis) : Bool :=
  coordinates.length = axes.length &&
    (coordinates.zip axes).all fun pair => (axisValues pair.2).contains pair.1
def cartesianIndicesCopyBody (axes : List Axis) : List Axis := axes
def cartesianSimdOuterZeroBody (axes : List Axis) : List Axis := axes
def cartesianSimdOuterBody (axes : List Axis) : List Axis := axes.tail
def cartesianSimdInnerZeroBody (_axes : List Axis) : Nat := 1
def cartesianSimdInnerBody (axes : List Axis) : Nat := axes.head?.map (fun axis => axis.len) |>.getD 0
def cartesianSimdIndexZeroBody (_axes : List Axis) : List I64 := []

def CartesianIndicesMoreRows : Prop :=
  (cartesianIndicesEmptyBody = []) ∧
  (∀ value, convertBoolIndexExact value =
    oneToAxis (JInt.wrap .i64 (if value then 1 else 0))) ∧
  (∀ first step last, cartesianSteppedColonExact first step last =
    (first.zip (step.zip last)).map fun triple =>
      axisFromEndpoints triple.1 triple.2.2 triple.2.1) ∧
  (∀ left right, cartesianIndicesEqualityBody left right =
    (left.length = right.length && (left.zip right).all fun pair => pair.1 = pair.2)) ∧
  (∀ axes, cartesianIndicesAxesBody axes =
    axes.map fun axis => oneToAxis (JInt.wrap .i64 axis.len)) ∧
  (cartesianIndicesGetZeroBody = []) ∧
  (∀ axes indices, cartesianGetIntsExact axes indices =
    if !cartesianIsassignedExact axes indices then .boundsError
    else .ok ((axes.zip indices).map fun pair => axisElem pair.1 (pair.2 - 1).toNat)) ∧
  (∀ getRange axes indices, cartesianGetRangesExact getRange axes indices =
    if axes.length ≠ indices.length then .boundsError
    else .ok (List.zipWith getRange axes indices)) ∧
  (∀ axes, cartesianIndicesStepBody axes = axes.map fun axis => axis.step) ∧
  (∀ axes, cartesianIndicesFirstBody axes = axes.map fun axis => axis.first) ∧
  (∀ coordinates axes, cartesianIndicesWrongRankInBody coordinates axes = false) ∧
  (∀ coordinates axes, cartesianIndicesInBody coordinates axes =
    (coordinates.length = axes.length &&
      (coordinates.zip axes).all fun pair => (axisValues pair.2).contains pair.1)) ∧
  (∀ axes, cartesianIndicesCopyBody axes = axes) ∧
  (∀ axes, cartesianSimdOuterZeroBody axes = axes) ∧
  (∀ axes, cartesianSimdOuterBody axes = axes.tail) ∧
  (∀ axes, cartesianSimdInnerZeroBody axes = 1) ∧
  (∀ axes, cartesianSimdInnerBody axes = (axes.head?.map fun axis => axis.len).getD 0) ∧
  (∀ axes, cartesianSimdIndexZeroBody axes = [])

theorem cartesianIndicesMoreRows : CartesianIndicesMoreRows := by
  unfold CartesianIndicesMoreRows
  simp [cartesianIndicesEmptyBody, convertBoolIndexExact,
    cartesianSteppedColonExact, cartesianIndicesEqualityBody,
    cartesianIndicesAxesBody, cartesianIndicesGetZeroBody,
    cartesianGetIntsExact, cartesianGetRangesExact, cartesianIndicesStepBody,
    cartesianIndicesFirstBody, cartesianIndicesWrongRankInBody,
    cartesianIndicesInBody, cartesianIndicesCopyBody, cartesianSimdOuterZeroBody,
    cartesianSimdOuterBody, cartesianSimdInnerZeroBody, cartesianSimdInnerBody,
    cartesianSimdIndexZeroBody]

def cartesianIndicesMoreEntries : List Entry := []

end JuliaLean.MultidimCov

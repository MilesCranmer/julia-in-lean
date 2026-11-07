import JuliaLean.base.bool

namespace JuliaLean.NumMisc.Coverage

def BoolMethodBehavior : Prop :=
  (∀ other, boolPromote other = other) ∧ boolBounds = (false, true) ∧
  (∀ x, boolNot x = !x) ∧
  (∀ x y, boolAnd x y = (x && y) ∧ boolOr x y = (x || y) ∧ boolXor x y = (x != y)) ∧
  (∀ xs, boolNand xs = !(xs.foldl (· && ·) true)) ∧
  (∀ xs, boolNor xs = !(xs.foldl (· || ·) false)) ∧
  (∀ x count, boolShiftLeft x count = (if x then 1 else 0) * 2^count) ∧
  (∀ x count, boolShiftRight x count = (if x then 1 else 0) / 2^count) ∧
  (∀ x, boolPredicates x = (false, x, !x, x, x)) ∧
  (∀ x, boolUnaryInt x = if x then 1 else 0) ∧
  (∀ x y, boolCompare x y = (y && !x, y || !x)) ∧
  (∀ x y, boolAdd x y = (if x then 1 else 0) + (if y then 1 else 0)) ∧
  (∀ x y, boolSub x y = (if x then 1 else 0) - (if y then 1 else 0)) ∧
  (∀ x y, boolMul x y = (x && y)) ∧
  (∀ x y, boolPow x y = (x || !y)) ∧
  (∀ x y, boolDiv x y = if y then .ok x else .error .divideError) ∧
  (∀ x y, boolRem x y = if y then .ok false else .error .divideError) ∧
  (∀ x onePlusY y, boolFloatAdd x onePlusY y = if x then onePlusY else y) ∧
  (∀ x y zero, boolFloatMul x y zero = if x then y else zero) ∧
  (∀ zero one, boolConvertReal zero one =
    if zero then .ok false else if one then .ok true else .error (.inexactError "Bool"))

theorem boolMethodBehavior : BoolMethodBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros <;> first | rfl | exact ⟨rfl, rfl, rfl⟩

end JuliaLean.NumMisc.Coverage

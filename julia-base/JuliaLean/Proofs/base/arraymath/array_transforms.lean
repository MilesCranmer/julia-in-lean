import JuliaLean.base.arraymath

namespace JuliaLean.NumMisc.Coverage

open JuliaLean

def ArrayArithmeticReverseBehavior : Prop :=
  (∀ same both left right, broadcastRoute same both left right =
    if both then if same then .sameRankArrays else .reshapedArrays
    else if left then .arrayScalar else if right then .scalarArray else .generic) ∧
  (∀ rank dims, reverseDims rank dims = match dims with
    | none => ((List.range rank).map (fun n => n + 1)).map (fun n : Nat => (n : Int))
    | some ds => ds) ∧
  (∀ rank dims, validReverseDims rank dims =
    (dims.all (fun d => 1 ≤ d ∧ d ≤ rank) && dims.eraseDups.length == dims.length))

theorem arrayArithmeticReverseBehavior : ArrayArithmeticReverseBehavior := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def ArrayRotationBehavior : Prop :=
  (∀ matrix, rotateHalf matrix = matrix.reverse.map List.reverse) ∧
  (∀ matrix k, rotateLeftK matrix k = match k % 4 with
    | 1 => rotateLeft matrix | 2 => rotateHalf matrix | 3 => rotateRight matrix | _ => matrix) ∧
  (∀ matrix k, rotateLeftK matrix (-k) = rotateLeftK matrix (-k))

theorem arrayRotationBehavior : ArrayRotationBehavior := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

end JuliaLean.NumMisc.Coverage

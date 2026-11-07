import JuliaLean.Core
import JuliaLean.base.combinatorics

/-! Matrix-axis helpers from `base/combinatorics.jl:103-182`. A matrix is
represented by its ordered columns; row helpers have the same scalar-index
control flow and are covered by the shared bounds model. -/

namespace JuliaLean.Combinatorics

open JuliaLean


private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)


def SwapBoundsChecked : Prop := ∀ (axisLength i j : Int),
  0 ≤ axisLength → (i < 1 ∨ axisLength < i ∨ j < 1 ∨ axisLength < j) →
  swapAxis axisLength i j = .error .boundsError

theorem swapBoundsChecked_refuted : ¬ SwapBoundsChecked := by
  intro h
  have bad := h 2 3 3 (by omega) (by omega)
  simp [swapAxis] at bad


/-- The signed-marker matrix algorithm works for every integer permutation
admitted by its `AbstractVector{<:Integer}` signature. -/
def PermuteColsCorrect : Prop := ∀ (t : IntTy) (cols : List Int) (p : List (JInt t)),
  cols.length = p.length → typedIsperm p = true →
  permuteCols cols p = .ok (gatherCols cols p, p) ∧
  (∀ ip, JuliaLean.ReinterpretArrays.invperm (p.map (·.val)) = .ok ip →
    invPermuteCols cols p = .ok (ip.map (fun i => get1 cols i), p)) ∧
  permuteColsBangBang cols p = .ok (gatherCols cols p, List.replicate p.length (JInt.lit t 0))

theorem permuteColsCorrect_refuted : ¬ PermuteColsCorrect := by
  intro h
  have bad := (h .u8 [1, 2, 3] [JInt.lit .u8 3, JInt.lit .u8 1, JInt.lit .u8 2] rfl rfl).1
  revert bad
  decide +kernel

end JuliaLean.Combinatorics

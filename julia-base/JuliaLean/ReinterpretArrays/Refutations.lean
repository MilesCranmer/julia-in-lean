import JuliaLean.ReinterpretArrays.MultInvProps
import JuliaLean.ReinterpretArrays.BytesProps
import JuliaLean.ReinterpretArrays.IndexProps

/-!
Refutations of this area's properties by concrete counterexamples.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- The constructor result for `SignedMultiplicativeInverse(Int8(-1))`. -/
def smiMinusOne : SignedMI .i8 := ⟨JInt.lit .i8 (-1), JInt.lit .i8 (-1), JInt.lit .i8 0, JInt.lit .u8 0⟩

theorem smiNew_minusOne : SmiNew (JInt.lit .i8 (-1)) smiMinusOne :=
  smiNewEval_sound _ 400 _ rfl

/-- `div(typemin(Int8), multiplicativeinverse(Int8(-1)))` returns `-128`; `div(typemin(Int8), -1)` throws. -/
theorem smiDivAll_refuted : ¬ SmiDivAll := by
  intro h
  have e := h .i8 rfl (JInt.lit .i8 (-128)) (JInt.lit .i8 (-1)) (by decide) smiMinusOne smiNew_minusOne
  have e2 : JInt.div (JInt.lit .i8 (-128)) (JInt.lit .i8 (-1)) = .error .divideError := rfl
  rw [e2] at e
  cases e

/-- `reshape(1:typemax(Int), typemax(Int), 1)` throws `ArgumentError("invalid Array dimensions")`. -/
theorem reshapeCheckComplete_refuted : ¬ ReshapeCheckComplete := by
  intro h
  have e := h (JInt.typemax .i64) [JInt.typemax .i64, JInt.lit .i64 1] (by decide) (by decide) (by decide)
  have e2 : reshapeCheck (JInt.typemax .i64) [JInt.typemax .i64, JInt.lit .i64 1] =
      .error (.argumentError "invalid Array dimensions") := rfl
  rw [e2] at e
  cases e

/-- `reinterpret(Int32, 1:2^61)`: `2^61 * 8` wraps to `0`, so the check passes and `size == (0,)`. -/
theorem raSizeExact_refuted : ¬ RaSizeExact := by
  intro h
  have e := h 8 4 (JInt.lit .i64 (2 ^ 61)) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl (JInt.lit .i64 0) rfl
  revert e
  decide

/-- `reinterpret(reshape, UInt8, reinterpret(reshape, UInt16, a))` for `a::Vector{UInt32}` of length 3
has size `(4, 3)`; applied to the `2×3` intermediate array it has size `(2, 2, 3)`. -/
theorem rrNestedSize_refuted : ¬ RrNestedSize := by
  intro h
  have e := h 4 2 1 [3] [2, 3] (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
  have e1 : rrNestedSize 4 2 1 [3] = .ok [4, 3] := rfl
  have e2 : rrSize 2 1 [2, 3] = .ok [2, 2, 3] := rfl
  rw [e1, e2] at e
  simp at e

end JuliaLean.ReinterpretArrays

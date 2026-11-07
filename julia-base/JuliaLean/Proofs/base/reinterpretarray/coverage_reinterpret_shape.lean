import JuliaLean.base.reinterpretarray
import JuliaLean.Core
import JuliaLean.base.reinterpretarray

namespace JuliaLean.ArrayCov

def ReinterpretStridesAndChecksCorrect : Prop :=
  (∀ ndims strides length get array k, reinterpret205Stride ndims strides length get array k =
      if k ≤ ndims array then get (strides array) k else length array) ∧
  (∀ sub source target readable, reinterpret234CheckReadable sub source target readable =
      if !readable && !sub target source then .error .padding else .ok ()) ∧
  (∀ sub source target writable, reinterpret241CheckWritable sub source target writable =
      if !writable && !sub source target then .error .padding else .ok ()) ∧
  (∀ style parent, reinterpret260IndexStyle style parent =
      if style parent = .linear then .linear else .cartesian)

theorem reinterpretStridesAndChecksCorrect : ReinterpretStridesAndChecksCorrect := by
  simp [ReinterpretStridesAndChecksCorrect, reinterpret205Stride,
    reinterpret234CheckReadable, reinterpret241CheckWritable, reinterpret260IndexStyle]

def ReinterpretStrideCalculationCorrect : Prop :=
  (∀ elementSize, reinterpret222CheckedStrides [] elementSize = .ok []) ∧
  (∀ stride rest elementSize, reinterpret222CheckedStrides (stride :: rest) elementSize = do
      let quotient ← JInt.div stride elementSize |>.mapError fun _ => .arithmetic
      let remainder ← JInt.remInt stride elementSize |>.mapError fun _ => .arithmetic
      if remainder.val != 0 then throw .nonIntegralStride
      let tail ← reinterpret222CheckedStrides rest elementSize
      pure (quotient :: tail)) ∧
  (∀ contiguous make size strides elsize target source reshaped array,
      reinterpret208Strides contiguous make size strides elsize target source reshaped array = do
      if contiguous array then return make (JInt.lit .i64 1) (size array)
      let parentStrides := strides array
      if target = source then return parentStrides
      let byteStrides := parentStrides.map (· * elsize array)
      if reshaped && target < source then
        return JInt.lit .i64 1 :: (← reinterpret222CheckedStrides byteStrides target)
      if byteStrides.getD 0 (JInt.lit .i64 0) != source then throw .noncontiguous
      let tail ← reinterpret222CheckedStrides byteStrides.tail target
      if reshaped then return tail else return JInt.lit .i64 1 :: tail) ∧
  (∀ style parent target source,
      reinterpret263IndexStyleReshaped style parent target source = do
      if target < source then
        if style parent = .linear then
          let k ← JInt.div source target |>.mapError fun _ => .arithmetic
          return .staticCartesian k
        return .cartesian
      return if style parent = .linear then .linear else .cartesian)

theorem reinterpretStrideCalculationCorrect : ReinterpretStrideCalculationCorrect := by
  simp [ReinterpretStrideCalculationCorrect, reinterpret222CheckedStrides,
    reinterpret208Strides, reinterpret263IndexStyleReshaped]

def ReinterpretShapeCorrect : Prop :=
  (∀ size singleton source target array, reinterpret371Size size singleton source target array = do
      let parentSize := size array
      let first := parentSize.getD 0 (JInt.lit .i64 0)
      let size1 ← if singleton then pure first else
        JInt.div (first * source) target |>.mapError fun _ => .arithmetic
      pure (size1 :: parentSize.tail)) ∧
  (∀ size source target array, reinterpret376SizeReshaped size source target array = do
      let parentSize := size array
      if target < source then
        let ratio ← JInt.div source target |>.mapError fun _ => .arithmetic
        return ratio :: parentSize
      if source < target then return parentSize.tail
      return parentSize) ∧
  (∀ axes singleton source target array, reinterpret384Axes axes singleton source target array = do
      let parentAxes := axes array
      let axis := parentAxes.getD 0 ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩
      let size1 ← if singleton then pure axis.length else
        JInt.div (axis.length * source) target |>.mapError fun _ => .arithmetic
      pure (⟨axis.first, size1⟩ :: parentAxes.tail)) ∧
  (∀ axes source target array, reinterpret390AxesReshaped axes source target array = do
      let parentAxes := axes array
      if target < source then
        let ratio ← JInt.div source target |>.mapError fun _ => .arithmetic
        return ⟨JInt.lit .i64 1, ratio⟩ :: parentAxes
      if source < target then return parentAxes.tail
      return parentAxes) ∧
  (∀ parent target source, reinterpret400Elsize parent target source =
      if target = source then parent else target) ∧
  (∀ scalar reinterpret parentGet first get source target array,
      reinterpret410GetZero scalar reinterpret parentGet first get source target array =
      if scalar target source then reinterpret target (parentGet array)
      else get array (first array)) ∧
  (∀ check parent target source array, reinterpret418CheckPtr check parent target source array =
      if target = source then false else check (parent array))

theorem reinterpretShapeCorrect : ReinterpretShapeCorrect := by
  simp [ReinterpretShapeCorrect, reinterpret371Size, reinterpret376SizeReshaped,
    reinterpret384Axes, reinterpret390AxesReshaped, reinterpret400Elsize,
    reinterpret410GetZero, reinterpret418CheckPtr]

end JuliaLean.ArrayCov

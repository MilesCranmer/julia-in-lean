import JuliaLean.base.reshapedarray
import JuliaLean.Core
import JuliaLean.Proofs.base.reshapedarray.coverage_reshaped_simple

namespace JuliaLean.ArrayCov

def ReshapedIndexMathCorrect : Prop :=
  (∀ axes index, reshaped270Ind2subEmpty axes index = [index]) ∧
  (∀ aux axes divisors index, reshaped271Ind2sub aux axes divisors index =
      aux axes divisors (index - JInt.lit .i64 1)) ∧
  (∀ first axes index, reshaped272Ind2subAuxEmpty first axes index =
      [index + first (axes.getLastD [])]) ∧
  (∀ divrem first axis axes divisor divisors index,
      reshaped273Ind2subAux divrem first (axis :: axes) (divisor :: divisors) index =
      let (quotient, remainder) := divrem index divisor
      (remainder + first axis) ::
        reshaped273Ind2subAux divrem first axes divisors quotient) ∧
  (∀ first index axes, reshaped277OffsetVector first index axes =
      index + first (axes.getD 0 []) - JInt.lit .i64 1) ∧
  (∀ index axes, reshaped278OffsetGeneral index axes = index)

theorem reshapedIndexMathCorrect : ReshapedIndexMathCorrect := by
  simp [ReshapedIndexMathCorrect, reshaped270Ind2subEmpty, reshaped271Ind2sub,
    reshaped272Ind2subAuxEmpty, reshaped273Ind2subAux, reshaped277OffsetVector,
    reshaped278OffsetGeneral]

def ReshapedAccessCorrect : Prop :=
  (∀ check fa fp assigned array index, reshaped280IsAssignedLinear check fa fp assigned array index =
      if !check array index then false
      else assigned array.parent (index - fa array + fp array)) ∧
  (∀ check size axes sub offset ind assigned array indices,
      reshaped286IsAssignedCartesian check size axes sub offset ind assigned array indices =
      if !check array indices then false
      else
        let parentAxes := axes array.parent
        assigned array.parent
          (ind parentAxes array.divisors (offset (sub (size array) indices) parentAxes))) ∧
  (∀ check fa fp get array index, reshaped294GetLinear check fa fp get array index = do
      if check array index then pure () else throw .bounds
      get array.parent (index - fa array + fp array)) ∧
  (∀ check unsafeGet array indices, reshaped300GetCartesian check unsafeGet array indices = do
      if check array indices then pure () else throw .bounds
      unsafeGet array indices) ∧
  (∀ check get array index, reshaped304GetReshapedIndex check get array index = do
      if check array.parent index then pure () else throw .bounds
      get array.parent index) ∧
  (∀ size axes sub offset ind get array indices,
      reshaped310UnsafeGet size axes sub offset ind get array indices =
      let parentAxes := axes array.parent
      get array.parent (ind parentAxes array.divisors
        (offset (sub (size array) indices) parentAxes))) ∧
  (∀ get parent index, reshaped316UnsafeGetScalar get parent index = get parent index) ∧
  (∀ get parent indices, reshaped317UnsafeGetTuple get parent indices = get parent indices) ∧
  (∀ check fa fp set array value index, reshaped319SetLinear check fa fp set array value index = do
      if check array index then pure () else throw .bounds
      let parent ← set array.parent value (index - fa array + fp array)
      pure (value, parent)) ∧
  (∀ check set array value indices, reshaped325SetCartesian check set array value indices = do
      if check array indices then pure () else throw .bounds
      set array value indices) ∧
  (∀ check set array value index, reshaped329SetReshapedIndex check set array value index = do
      if check array.parent index then pure () else throw .bounds
      let parent ← set array.parent value index
      pure (value, parent)) ∧
  (∀ size axes sub offset ind set array value indices,
      reshaped335UnsafeSet size axes sub offset ind set array value indices =
      let parentAxes := axes array.parent
      let linear := offset (sub (size array) indices) parentAxes
      (value, set array.parent value (ind parentAxes array.divisors linear)))

theorem reshapedAccessCorrect : ReshapedAccessCorrect := by
  simp [ReshapedAccessCorrect, reshaped280IsAssignedLinear,
    reshaped286IsAssignedCartesian, reshaped294GetLinear, reshaped300GetCartesian,
    reshaped304GetReshapedIndex, reshaped310UnsafeGet, reshaped316UnsafeGetScalar,
    reshaped317UnsafeGetTuple, reshaped319SetLinear, reshaped325SetCartesian,
    reshaped329SetReshapedIndex, reshaped335UnsafeSet]

end JuliaLean.ArrayCov

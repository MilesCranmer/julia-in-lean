import JuliaLean.base.array
import JuliaLean.Core
import JuliaLean.Proofs.base.array.coverage_array_core

namespace JuliaLean.ArrayCov

def ArrayGetindexCorrect : Prop :=
  (∀ bounds linear get array indices, array974GetCartesian bounds linear get array indices = do
      if bounds array indices then pure () else throw .boundsError
      get array (linear array indices)) ∧
  (∀ bounds axes similar first copy array range,
      array981GetRange bounds axes similar first copy array range = do
      if bounds array range then pure () else throw .boundsError
      let output ← similar array (axes range)
      if range.isEmpty then return output
      copy output (first output) array (range.getD 0 (JInt.lit .i64 1)) range.length) ∧
  (∀ toIndex get array range, array993GetBoolRange toIndex get array range = do
      let indices ← toIndex range
      get array indices) ∧
  (∀ similar copy array, array995GetColon similar copy array = do
      let length := array.data.length
      let output ← similar array length
      if length = 0 then return output
      copy output array length) ∧
  (∀ get literal array range, array1005GetRangeComprehension get literal array range = do
      let values ← range.mapM (get array)
      literal values)

theorem arrayGetindexCorrect : ArrayGetindexCorrect := by
  simp [ArrayGetindexCorrect, array974GetCartesian, array981GetRange,
    array993GetBoolRange, array995GetColon, array1005GetRangeComprehension]

def ArraySetindexCorrect : Prop :=
  (∀ same convert set array value index, array1031SetLinear same convert set array value index = do
      let value ← if same value then pure value else convert value
      set array value index) ∧
  (∀ bounds set array value index, array1036SetLinearTyped bounds set array value index =
      if bounds array index then .ok (set array index value) else .error .boundsError) ∧
  (∀ same convert set array value indices, array1042SetCartesian same convert set array value indices = do
      let value ← if same value then pure value else convert value
      set array value indices) ∧
  (∀ bounds linear set array value indices,
      array1047SetCartesianTyped bounds linear set array value indices =
      if bounds array indices then .ok (set array (linear array indices) value)
      else .error .boundsError) ∧
  (∀ set array value index, array1055SafeSetAny set array value index = set array index value) ∧
  (∀ set array value index, array1057SafeSetTyped set array value index = set array index value) ∧
  (∀ convert set array value index, array1059SafeSetConvert convert set array value index = do
      let value ← convert value
      pure (set array value index)) ∧
  (∀ shape bounds unaliasV unaliasI getI getV set array values indices,
      array1063Scatter shape bounds unaliasV unaliasI getI getV set array values indices = do
      shape values indices.length
      if bounds array indices then pure () else throw .boundsError
      let values := unaliasV array values
      let indices := unaliasI array indices
      pure (array1063ScatterLoop getI getV set array indices values 0 values.length)) ∧
  (∀ bounds shape copy array values range, array1078SetRange bounds shape copy array values range = do
      if bounds array range then pure () else throw .boundsError
      shape values range.length
      if range.isEmpty then return array
      copy array (range.getD 0 (JInt.lit .i64 1)) values range.length) ∧
  (∀ shape copy array values, array1088SetColon shape copy array values = do
      let length := array.data.length
      shape values length
      if length = 0 then return array
      copy array values length)

theorem arraySetindexCorrect : ArraySetindexCorrect := by
  simp [ArraySetindexCorrect, array1031SetLinear, array1036SetLinearTyped,
    array1042SetCartesian, array1047SetCartesianTyped, array1055SafeSetAny,
    array1057SafeSetTyped, array1059SafeSetConvert, array1063Scatter,
    array1078SetRange, array1088SetColon]

end JuliaLean.ArrayCov

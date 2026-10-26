import JuliaLean.Core
import JuliaLean.ArrayCov.ArrayCore

namespace JuliaLean.ArrayCov

def array974GetCartesian (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (linearIndex : DenseArrayModel → List JInt64 → JInt64)
    (getindex : DenseArrayModel → JInt64 → Jl Int)
    (array : DenseArrayModel) (indices : List JInt64) : Jl Int := do
  if checkbounds array indices then pure () else throw .boundsError
  getindex array (linearIndex array indices)

def array981GetRange (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (axes : List JInt64 → List Int)
    (similar : DenseArrayModel → List Int → Jl DenseArrayModel)
    (firstIndex : DenseArrayModel → JInt64)
    (copyto : DenseArrayModel → JInt64 → DenseArrayModel → JInt64 → Nat →
      Jl DenseArrayModel)
    (array : DenseArrayModel) (range : List JInt64) : Jl DenseArrayModel := do
  if checkbounds array range then pure () else throw .boundsError
  let output ← similar array (axes range)
  if range.isEmpty then return output
  copyto output (firstIndex output) array (range.getD 0 (JInt.lit .i64 1)) range.length

def array993GetBoolRange (toIndex : List Bool → Jl (List JInt64))
    (getindex : DenseArrayModel → List JInt64 → Jl DenseArrayModel)
    (array : DenseArrayModel) (range : List Bool) : Jl DenseArrayModel := do
  let indices ← toIndex range
  getindex array indices

def array995GetColon (similar : DenseArrayModel → Nat → Jl DenseArrayModel)
    (unsafeCopy : DenseArrayModel → DenseArrayModel → Nat → Jl DenseArrayModel)
    (array : DenseArrayModel) : Jl DenseArrayModel := do
  let length := array.data.length
  let output ← similar array length
  if length = 0 then return output
  unsafeCopy output array length

def array1005GetRangeComprehension
    (getindex : DenseArrayModel → JInt64 → Jl Int)
    (typedLiteral : List Int → Jl DenseArrayModel)
    (array : DenseArrayModel) (range : List JInt64) : Jl DenseArrayModel := do
  let values ← range.mapM (getindex array)
  typedLiteral values

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

def array1031SetLinear (isType : Int → Bool) (convert : Int → Jl Int)
    (setTyped : DenseArrayModel → Int → JInt64 → Jl DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (index : JInt64) : Jl DenseArrayModel := do
  let value ← if isType value then pure value else convert value
  setTyped array value index

def array1036SetLinearTyped (checkbounds : DenseArrayModel → JInt64 → Bool)
    (memorySet : DenseArrayModel → JInt64 → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (index : JInt64) : Jl DenseArrayModel :=
  if checkbounds array index then .ok (memorySet array index value) else .error .boundsError

def array1042SetCartesian (isType : Int → Bool) (convert : Int → Jl Int)
    (setTyped : DenseArrayModel → Int → List JInt64 → Jl DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (indices : List JInt64) : Jl DenseArrayModel := do
  let value ← if isType value then pure value else convert value
  setTyped array value indices

def array1047SetCartesianTyped (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (linearIndex : DenseArrayModel → List JInt64 → JInt64)
    (memorySet : DenseArrayModel → JInt64 → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (indices : List JInt64) : Jl DenseArrayModel :=
  if checkbounds array indices then
    .ok (memorySet array (linearIndex array indices) value)
  else .error .boundsError

def array1055SafeSetAny (memorySet : DenseArrayModel → JInt64 → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (index : JInt64) : DenseArrayModel :=
  memorySet array index value

def array1057SafeSetTyped := array1055SafeSetAny

def array1059SafeSetConvert (convert : Int → Jl Int)
    (safeSet : DenseArrayModel → Int → JInt64 → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (index : JInt64) : Jl DenseArrayModel := do
  let value ← convert value
  pure (safeSet array value index)

def array1063ScatterLoop
    (getIndex : List JInt64 → Nat → JInt64)
    (getValue : List Int → Nat → Int)
    (setindex : DenseArrayModel → JInt64 → Int → DenseArrayModel) :
    DenseArrayModel → List JInt64 → List Int → Nat → Nat → DenseArrayModel
  | array, _, _, _, 0 => array
  | array, indices, values, position, fuel + 1 =>
      array1063ScatterLoop getIndex getValue setindex
        (setindex array (getIndex indices position) (getValue values position))
        indices values (position + 1) fuel

def array1063Scatter (shapeCheck : List Int → Nat → Jl Unit)
    (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (unaliasValues : DenseArrayModel → List Int → List Int)
    (unaliasIndices : DenseArrayModel → List JInt64 → List JInt64)
    (getIndex : List JInt64 → Nat → JInt64) (getValue : List Int → Nat → Int)
    (setindex : DenseArrayModel → JInt64 → Int → DenseArrayModel)
    (array : DenseArrayModel) (values : List Int) (indices : List JInt64) :
    Jl DenseArrayModel := do
  shapeCheck values indices.length
  if checkbounds array indices then pure () else throw .boundsError
  let values := unaliasValues array values
  let indices := unaliasIndices array indices
  pure (array1063ScatterLoop getIndex getValue setindex array indices values 0 values.length)

def array1078SetRange (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (shapeCheck : DenseArrayModel → Nat → Jl Unit)
    (unsafeCopy : DenseArrayModel → JInt64 → DenseArrayModel → Nat → Jl DenseArrayModel)
    (array values : DenseArrayModel) (range : List JInt64) : Jl DenseArrayModel := do
  if checkbounds array range then pure () else throw .boundsError
  shapeCheck values range.length
  if range.isEmpty then return array
  unsafeCopy array (range.getD 0 (JInt.lit .i64 1)) values range.length

def array1088SetColon (shapeCheck : DenseArrayModel → Nat → Jl Unit)
    (unsafeCopy : DenseArrayModel → DenseArrayModel → Nat → Jl DenseArrayModel)
    (array values : DenseArrayModel) : Jl DenseArrayModel := do
  let length := array.data.length
  shapeCheck values length
  if length = 0 then return array
  unsafeCopy array values length

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

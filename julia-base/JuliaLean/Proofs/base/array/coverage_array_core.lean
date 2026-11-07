import JuliaLean.base.array
import JuliaLean.Core
import JuliaLean.Proofs.base.array.coverage_simple

namespace JuliaLean.ArrayCov

def ArraySyntaxAndVectCorrect : Prop :=
  (∀ escape recurse expression, array132SafeIndexMacro escape recurse expression =
      escape (recurse expression)) ∧
  (∀ recurse get set array indices, array135SafeIndex recurse get set (.ref array indices) =
      .call get (array :: indices)) ∧
  (∀ recurse get set array indices right,
      array135SafeIndex recurse get set (.assign (.ref array indices) right) =
      .call set (array :: recurse right :: indices.map recurse)) ∧
  (∀ recurse get set head args, array135SafeIndex recurse get set (.node head args) =
      .node head (args.map recurse)) ∧
  (∀ allocate set values, array159Vect allocate set values =
      array159VectLoop set (allocate values.length) 1 values) ∧
  (∀ promote literal values, array183VectPromoted promote literal values =
      literal (promote values) values)

theorem arraySyntaxAndVectCorrect : ArraySyntaxAndVectCorrect := by
  simp [ArraySyntaxAndVectCorrect, array132SafeIndexMacro, array135SafeIndex,
    array159Vect, array183VectPromoted]

def ArrayStorageRoutesCorrect : Prop :=
  (∀ bounds unset array index, array209UnsetIndex bounds unset array index =
      if bounds array index then .ok (unset array index) else .error .boundsError) ∧
  (∀ any datatype ptr size alignment align type,
      array219ElsizePtr any datatype ptr size alignment align type =
      if any type then .ok ptr
      else if !datatype type then .error (.methodError "sizeof")
      else .ok (align (size type) (alignment type))) ∧
  (∀ bounds sub assigned array indices, array231IsAssigned bounds sub assigned array indices =
      if !bounds array indices then false else assigned array (sub array.dims indices)) ∧
  (∀ bounds assigned array index, array239IsAssignedVector bounds assigned array index =
      if !bounds array index then false else assigned array index) ∧
  (∀ size move memory type dest src count,
      array259UnsafeCopyPtr size move memory type dest src count =
      (dest, move memory dest src (count * size type))) ∧
  (∀ ref copy memory dest doffs src soffs count,
      array276UnsafeCopyArray ref copy memory dest doffs src soffs count =
      if count.val = 0 then (dest, memory)
      else (dest, copy memory (ref dest doffs) (ref src soffs) count)) ∧
  (∀ copy dest doffs src soffs count, array288Copyto copy dest doffs src soffs count =
      copy dest doffs src soffs count) ∧
  (∀ copy dest doffs src soffs count, array290CopytoArrayMemory copy dest doffs src soffs count =
      copy dest doffs src soffs count) ∧
  (∀ copy dest doffs src soffs count, array292CopytoMemoryArray copy dest doffs src soffs count =
      copy dest doffs src soffs count) ∧
  (∀ copy dest doffs src soffs count, array296CopytoSameArray copy dest doffs src soffs count =
      copy dest doffs src soffs count)

theorem arrayStorageRoutesCorrect : ArrayStorageRoutesCorrect := by
  simp [ArrayStorageRoutesCorrect, array209UnsetIndex, array219ElsizePtr,
    array231IsAssigned, array239IsAssignedVector, array259UnsafeCopyPtr,
    array276UnsafeCopyArray, array288Copyto, array290CopytoArrayMemory,
    array292CopytoMemoryArray, array296CopytoSameArray]

def ArrayFillCopyLiteralCorrect : Prop :=
  (∀ isType convert fill array value, array368Fill isType convert fill array value = do
      let value ← if isType value then pure value else convert value
      pure (fill array value)) ∧
  (∀ set array value, array373Fill set array value =
      array373FillLoop set array 1 array.data.length value) ∧
  (∀ allocate copy array, array391Copy allocate copy array =
      let output := copy (allocate array.data.length) array array.data.length
      { output with dims := array.dims }) ∧
  (∀ sameRef sameSize setRef setSize dest src,
      array402Take sameRef sameSize setRef setSize dest src =
      let dest := if sameRef dest src then dest else setRef dest src
      if sameSize dest src then dest else setSize dest src) ∧
  (∀ allocate tupleSet foldSet isTuple values,
      array445TypedLiteral allocate tupleSet foldSet isTuple values =
      let output := allocate values.length
      if isTuple then array445LiteralLoop tupleSet output 1 values
      else array445LiteralLoop foldSet output 1 values) ∧
  (∀ allocate set values, array463AnyLiteral allocate set values =
      array463AnyLoop set (allocate values.length) 1 values) ∧
  (∀ u, array471AnyEmpty u = []) ∧
  (∀ convert memset same array value, array473FillBytes convert memset same array value = do
      let value ← if same value then pure value else convert value
      pure (memset array value array.data.length))

theorem arrayFillCopyLiteralCorrect : ArrayFillCopyLiteralCorrect := by
  simp [ArrayFillCopyLiteralCorrect, array368Fill, array373Fill, array391Copy,
    array402Take, array445TypedLiteral, array463AnyLiteral,
    array471AnyEmpty, array473FillBytes]

end JuliaLean.ArrayCov

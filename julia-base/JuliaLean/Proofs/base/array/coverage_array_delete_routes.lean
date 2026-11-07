import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

def ArrayPopRoutesCorrect : Prop :=
  (∀ get delete array, array1700Pop get delete array =
      if array.isEmpty then .error .empty else .ok (get array, delete array 1)) ∧
  (∀ get delete array index, array1741PopAt get delete array index = do
      let value ← get array index
      let array ← delete array index 1
      pure (value, array)) ∧
  (∀ get delete array index default, array1748PopAtDefault get delete array index default =
      if 1 ≤ index && index ≤ array.length then
        (get array index, delete array index 1) else (default, array)) ∧
  (∀ get delete array, array1836PopFirst get delete array =
      if array.isEmpty then .error .empty else .ok (get array, delete array 1))

theorem arrayPopRoutesCorrect : ArrayPopRoutesCorrect := by
  simp [ArrayPopRoutesCorrect, array1700Pop, array1741PopAt,
    array1748PopAtDefault, array1836PopFirst]

def ArrayDeleteRoutesCorrect : Prop :=
  (∀ delete array indices, array1945DeleteIndices delete array indices = delete array indices) ∧
  (∀ toIndices delete array indices, array1946DeleteVector toIndices delete array indices = do
      let indices ← toIndices array indices
      delete array indices) ∧
  (∀ item, array1949NowherePush item = ()) ∧
  (∀ count, array1950NowhereGrow count = ()) ∧
  (∀ assigned get push grow deleted array index,
      array1952PushDeleted assigned get push grow deleted array index =
      if assigned array index then push deleted (get array index) else grow deleted 1) ∧
  (∀ assigned get set unset array dest src,
      array1961CopyItem assigned get set unset array dest src =
      if assigned array src then set array dest (get array src) else unset array dest) ∧
  (∀ empty delete array indices, array2153SpliceIndices empty delete array indices =
      delete array indices (empty array))

theorem arrayDeleteRoutesCorrect : ArrayDeleteRoutesCorrect := by
  simp [ArrayDeleteRoutesCorrect, array1945DeleteIndices, array1946DeleteVector,
    array1949NowherePush, array1950NowhereGrow, array1952PushDeleted,
    array1961CopyItem, array2153SpliceIndices]

end JuliaLean.ArrayCov

import JuliaLean.Core

namespace JuliaLean.ArrayCov

inductive DeleteRouteError where
  | empty | bounds
  deriving Repr, DecidableEq

abbrev DeleteJl (α : Type) := Except DeleteRouteError α

def array1700Pop (getLast : List Int → Int)
    (deleteEnd : List Int → Nat → List Int) (array : List Int) : DeleteJl (Int × List Int) :=
  if array.isEmpty then .error .empty
  else .ok (getLast array, deleteEnd array 1)

def array1741PopAt (getindex : List Int → Int → DeleteJl Int)
    (deleteAt : List Int → Int → Nat → DeleteJl (List Int))
    (array : List Int) (index : Int) : DeleteJl (Int × List Int) := do
  let value ← getindex array index
  let array ← deleteAt array index 1
  pure (value, array)

def array1748PopAtDefault (getindex : List Int → Int → Int)
    (deleteAt : List Int → Int → Nat → List Int)
    (array : List Int) (index default : Int) : Int × List Int :=
  if 1 ≤ index && index ≤ array.length then
    (getindex array index, deleteAt array index 1)
  else (default, array)

def array1836PopFirst (getFirst : List Int → Int)
    (deleteBegin : List Int → Nat → List Int) (array : List Int) :
    DeleteJl (Int × List Int) :=
  if array.isEmpty then .error .empty
  else .ok (getFirst array, deleteBegin array 1)

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

def array1945DeleteIndices (delete : List Int → List Int → DeleteJl (List Int))
    (array indices : List Int) : DeleteJl (List Int) := delete array indices

def array1946DeleteVector (toIndices : List Int → List Int → DeleteJl (List Int))
    (delete : List Int → List Int → DeleteJl (List Int))
    (array indices : List Int) : DeleteJl (List Int) := do
  let indices ← toIndices array indices
  delete array indices

def array1949NowherePush (_item : Int) : Unit := ()
def array1950NowhereGrow (_count : Nat) : Unit := ()

def array1952PushDeleted (isassigned : List Int → Int → Bool)
    (getindex : List Int → Int → Int)
    (push : List Int → Int → List Int) (growEnd : List Int → Nat → List Int)
    (deleted array : List Int) (index : Int) : List Int :=
  if isassigned array index then push deleted (getindex array index)
  else growEnd deleted 1

def array1961CopyItem (isassigned : List Int → Int → Bool)
    (getindex : List Int → Int → Int) (setindex : List Int → Int → Int → List Int)
    (unset : List Int → Int → List Int) (array : List Int) (dest src : Int) : List Int :=
  if isassigned array src then setindex array dest (getindex array src)
  else unset array dest

def array2153SpliceIndices (emptyLike : List Int → List Int)
    (delete : List Int → List Int → List Int → DeleteJl (List Int × List Int))
    (array indices : List Int) : DeleteJl (List Int × List Int) :=
  let deleted := emptyLike array
  delete array indices deleted

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

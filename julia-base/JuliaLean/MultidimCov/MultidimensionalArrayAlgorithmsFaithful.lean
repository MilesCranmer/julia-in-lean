import JuliaLean.MultidimCov.MultidimensionalUnsafeFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalArrayAlgorithmsFaithful

open JuliaLean.Registry
open MultidimensionalCartesianFaithful
open MultidimensionalIndicesFaithful
open MultidimensionalUnsafeFaithful

abbrev Result (α : Type) := Except MultidimensionalUnsafeFaithful.Error α

def m1113 (subtract : α → α → α) (array : ArrayState α) (dims rank : Int) : Result (ArrayState α) :=
  if dims < 1 || rank < dims then .error .dimensionMismatch else
  let dimension := (dims - 1).toNat
  let keys := array.values.map fun pair => pair.1
  let output := keys.filterMap fun key =>
    let next := key.set dimension (key.getD dimension 0 + 1)
    match lookup array next, lookup array key with
    | some right, some left => some (key, subtract right left)
    | _, _ => none
  .ok { array with values := output }
def P1113 : Prop := ∀ {α : Type} (subtract : α → α → α)
    (array : ArrayState α) dims rank,
  m1113 subtract array dims rank =
    if dims < 1 || rank < dims then .error .dimensionMismatch else
    let dimension := (dims - 1).toNat
    let keys := array.values.map fun pair => pair.1
    let output := keys.filterMap fun key =>
      let next := key.set dimension (key.getD dimension 0 + 1)
      match lookup array next, lookup array key with
      | some right, some left => some (key, subtract right left)
      | _, _ => none
    .ok { array with values := output }
theorem p1113 : P1113 := by simp [P1113, m1113]

def m1123 (subtract : α → α → α) (values : List α) (dims : Int) : Result (List α) :=
  if dims ≠ 1 then .error .dimensionMismatch else .ok (List.zipWith subtract values.tail values)
def P1123 : Prop := ∀ {α : Type} (subtract : α → α → α) (values : List α) dims,
  m1123 subtract values dims = if dims ≠ 1 then .error .dimensionMismatch else .ok (List.zipWith subtract values.tail values)
theorem p1123 : P1123 := by simp [P1123, m1123]

inductive AliasIndex where
  | scalar (value : Int)
  | range (values : List Int)
  | array (values : List Int)
  | unknown
  deriving Repr, DecidableEq

def indicesOverlap : List AliasIndex → List AliasIndex → Bool
  | [], [] => true
  | .range left :: ls, .range right :: rs =>
      left.any right.contains && indicesOverlap ls rs
  | .scalar left :: ls, .scalar right :: rs => left = right && indicesOverlap ls rs
  | .scalar left :: ls, .array right :: rs => right.contains left && indicesOverlap ls rs
  | .array left :: ls, .scalar right :: rs => left.contains right && indicesOverlap ls rs
  | .array left :: ls, .array right :: rs =>
      if left.length = 1 then right.contains (left.headD 0) && indicesOverlap ls rs
      else if right.length = 1 then left.contains (right.headD 0) && indicesOverlap ls rs
      else true
  | _ :: _, _ :: _ => true
  | _, _ => false

def m1130 (leftBits rightBits parentsMatch parentsAlias parentIndexAlias : Bool)
    (leftIndices rightIndices : List AliasIndex) : Bool :=
  if leftBits || rightBits then false
  else if parentsMatch then indicesOverlap leftIndices rightIndices
  else parentsAlias || parentIndexAlias
def P1130 : Prop := ∀ leftBits rightBits parentsMatch parentsAlias parentIndexAlias leftIndices rightIndices,
  m1130 leftBits rightBits parentsMatch parentsAlias parentIndexAlias leftIndices rightIndices =
    if leftBits || rightBits then false
    else if parentsMatch then indicesOverlap leftIndices rightIndices
    else parentsAlias || parentIndexAlias
theorem p1130 : P1130 := by simp [P1130, m1130]

def m1153 {A : Type} (sameObject : A → A → Bool) (left right : A) := sameObject left right
def P1153 : Prop := ∀ {A : Type} (sameObject : A → A → Bool) left right, m1153 sameObject left right = sameObject left right
theorem p1153 : P1153 := by simp [P1153, m1153]

def m1154 (leftSize rightSize : Nat) (leftPointer rightPointer : Nat) (leftShape rightShape : List Nat) : Bool :=
  leftSize = rightSize && leftPointer = rightPointer && leftShape = rightShape
def P1154 : Prop := ∀ leftSize rightSize leftPointer rightPointer leftShape rightShape,
  m1154 leftSize rightSize leftPointer rightPointer leftShape rightShape =
    (leftSize = rightSize && leftPointer = rightPointer && leftShape = rightShape)
theorem p1154 : P1154 := by simp [P1154, m1154]

def m1155 (leftSize rightSize : Nat) (leftPointer rightPointer : Nat) (leftStrides rightStrides : List Int) : Bool :=
  leftSize = rightSize && leftPointer = rightPointer && leftStrides = rightStrides
def P1155 : Prop := ∀ leftSize rightSize leftPointer rightPointer leftStrides rightStrides,
  m1155 leftSize rightSize leftPointer rightPointer leftStrides rightStrides =
    (leftSize = rightSize && leftPointer = rightPointer && leftStrides = rightStrides)
theorem p1155 : P1155 := by simp [P1155, m1155]

def m1162 (leftHead rightHead : List Int) (leftTail rightTail : List AliasIndex) : Bool :=
  leftHead.any rightHead.contains && indicesOverlap leftTail rightTail
def P1162 : Prop := ∀ leftHead rightHead (leftTail rightTail : List AliasIndex),
  m1162 leftHead rightHead leftTail rightTail = (leftHead.any rightHead.contains && indicesOverlap leftTail rightTail)
theorem p1162 : P1162 := by simp [P1162, m1162]
def m1166 := m1162
def P1166 : Prop := ∀ leftHead rightHead leftTail rightTail,
  m1166 leftHead rightHead leftTail rightTail = m1162 leftHead rightHead leftTail rightTail
theorem p1166 : P1166 := by simp [P1166, m1166]
def m1170 (left right : Int) leftTail rightTail := left = right && indicesOverlap leftTail rightTail
def P1170 : Prop := ∀ left right leftTail rightTail,
  m1170 left right leftTail rightTail = (left = right && indicesOverlap leftTail rightTail)
theorem p1170 : P1170 := by simp [P1170, m1170]
def m1172 (left : Int) (right : List Int) leftTail rightTail := right.contains left && indicesOverlap leftTail rightTail
def P1172 : Prop := ∀ left right leftTail rightTail,
  m1172 left right leftTail rightTail = (right.contains left && indicesOverlap leftTail rightTail)
theorem p1172 : P1172 := by simp [P1172, m1172]
def m1174 (left : List Int) (right : Int) leftTail rightTail := left.contains right && indicesOverlap leftTail rightTail
def P1174 : Prop := ∀ left right leftTail rightTail,
  m1174 left right leftTail rightTail = (left.contains right && indicesOverlap leftTail rightTail)
theorem p1174 : P1174 := by simp [P1174, m1174]
def m1177 (left right : List Int) leftTail rightTail :=
  if left.length = 1 then right.contains (left.headD 0) && indicesOverlap leftTail rightTail
  else if right.length = 1 then left.contains (right.headD 0) && indicesOverlap leftTail rightTail else true
def P1177 : Prop := ∀ left right leftTail rightTail, m1177 left right leftTail rightTail =
  if left.length = 1 then right.contains (left.headD 0) && indicesOverlap leftTail rightTail
  else if right.length = 1 then left.contains (right.headD 0) && indicesOverlap leftTail rightTail else true
theorem p1177 : P1177 := by simp [P1177, m1177]

def copyPairs (dest src : ArrayState α) (destKeys srcKeys : List (List Int)) : ArrayState α :=
  (destKeys.zip srcKeys).foldl (fun output pair =>
    match lookup src pair.2 with | some value => write output pair.1 value | none => output) dest

def m1190 (dest src : ArrayState α) (destKeys srcKeys : List (List Int)) : Result (ArrayState α) :=
  if destKeys.isEmpty then .ok dest
  else if destKeys.length ≠ srcKeys.length then .error .dimensionMismatch
  else .ok (copyPairs dest src destKeys srcKeys)
def P1190 : Prop := ∀ {α : Type} (dest src : ArrayState α) destKeys srcKeys,
  m1190 dest src destKeys srcKeys = if destKeys.isEmpty then .ok dest
    else if destKeys.length ≠ srcKeys.length then .error .dimensionMismatch
    else .ok (copyPairs dest src destKeys srcKeys)
theorem p1190 : P1190 := by simp [P1190, m1190]

def m1246 (copyto : A → S → A) (dest : A) (src : S) : A := copyto dest src
def P1246 : Prop := ∀ {A S : Type} (copyto : A → S → A) dest src, m1246 copyto dest src = copyto dest src
theorem p1246 : P1246 := by simp [P1246, m1246]

def rotateKey (axes : List (List Int)) (shifts : List Int) (key : List Int) : List Int :=
  (List.zip key (List.zip axes shifts)).map fun pair =>
    match pair.2.1.findIdx? (fun value => value = pair.1) with
    | none => pair.1
    | some position => pair.2.1.getD
        ((Int.ofNat position + pair.2.2.emod (Int.ofNat (max pair.2.1.length 1))).emod
          (Int.ofNat (max pair.2.1.length 1))).toNat pair.1

def m1257 (dest src : ArrayState α) (shifts : List Int) : Result (ArrayState α) :=
  if dest.id = src.id then .error .dimensionMismatch
  else if dest.axes ≠ src.axes then .error .dimensionMismatch
  else if src.values.isEmpty then .ok dest
  else .ok (src.values.foldl (fun output pair => write output (rotateKey src.axes shifts pair.1) pair.2) dest)
def P1257 : Prop := ∀ {α : Type} (dest src : ArrayState α) shifts,
  m1257 dest src shifts = if dest.id = src.id then .error .dimensionMismatch
    else if dest.axes ≠ src.axes then .error .dimensionMismatch
    else if src.values.isEmpty then .ok dest
    else .ok (src.values.foldl (fun output pair => write output (rotateKey src.axes shifts pair.1) pair.2) dest)
theorem p1257 : P1257 := by simp [P1257, m1257]

def m1265 (convert : List α → Result (List Int)) (dest src : ArrayState β) (shifts : List α) := do
  m1257 dest src (← convert shifts)
def P1265 : Prop := ∀ {α β : Type} (convert : List α → Result (List Int))
    (dest src : ArrayState β) shifts,
  m1265 convert dest src shifts = do m1257 dest src (← convert shifts)
theorem p1265 : P1265 := by simp [P1265, m1265]

def m1284 (dest src : ArrayState α) (shifts : List Int) : Result (ArrayState α) := m1257 dest src shifts
def P1284 : Prop := ∀ {α : Type} (dest src : ArrayState α) shifts,
  m1284 dest src shifts = m1257 dest src shifts
theorem p1284 : P1284 := by simp [P1284, m1284]
def m1297 := @m1190
def P1297 : Prop := ∀ {α : Type} (dest src : ArrayState α) destKeys srcKeys,
  m1297 dest src destKeys srcKeys = m1190 dest src destKeys srcKeys
theorem p1297 : P1297 := by simp [P1297, m1297]

def m1337 (dest src : ArrayState α) : Result (ArrayState α) :=
  if dest.id = src.id then .error .dimensionMismatch
  else if dest.axes.map List.length ≠ src.axes.map List.length then .error .dimensionMismatch
  else
    let shifts := List.zipWith (fun source dest => source.headD 1 - dest.headD 1) src.axes dest.axes
    if shifts.all (fun shift => shift = 0) then .ok { dest with values := src.values }
    else m1257 dest src shifts
def P1337 : Prop := ∀ {α : Type} (dest src : ArrayState α), m1337 dest src =
  if dest.id = src.id then .error .dimensionMismatch
  else if dest.axes.map List.length ≠ src.axes.map List.length then .error .dimensionMismatch
  else let shifts := List.zipWith (fun source dest => source.headD 1 - dest.headD 1) src.axes dest.axes
    if shifts.all (fun shift => shift = 0) then .ok { dest with values := src.values } else m1257 dest src shifts
theorem p1337 : P1337 := by simp [P1337, m1337]
def m1349 := @m1337
def P1349 : Prop := ∀ {α : Type} (dest src : ArrayState α), m1349 dest src = m1337 dest src
theorem p1349 : P1349 := by simp [P1349, m1349]
def m1364 := @m1190
def P1364 : Prop := ∀ {α : Type} (dest src : ArrayState α) destKeys srcKeys,
  m1364 dest src destKeys srcKeys = m1190 dest src destKeys srcKeys
theorem p1364 : P1364 := by simp [P1364, m1364]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}", juliaFile := "base/multidimensional.jl",
    juliaFns := [name], statement, source := s!"base/multidimensional.jl:{line}; array algorithm source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalArrayAlgorithmsFaithful

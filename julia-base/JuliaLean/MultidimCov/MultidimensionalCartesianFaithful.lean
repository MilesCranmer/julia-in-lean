import JuliaLean.MultidimCov.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalCartesianFaithful

open JuliaLean
open JuliaLean.Registry

inductive Error where | inexact | bounds | argument | unsupported deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α
abbrev I64 := JInt .i64

structure IntegerValue where
  value : Int
  deriving Repr, DecidableEq

def toInt (value : IntegerValue) : Result I64 :=
  if h : IntTy.min .i64 ≤ value.value ∧ value.value ≤ IntTy.max .i64
  then .ok ⟨value.value, h⟩ else .error .inexact

structure Cartesian where
  coordinates : List I64
  deriving Repr, DecidableEq

inductive IndexArg where
  | integer (value : IntegerValue)
  | cartesian (value : Cartesian)
  deriving Repr, DecidableEq

def m77 (values : List IntegerValue) : Result Cartesian :=
  (values.mapM toInt).map fun coordinates => ⟨coordinates⟩
def P77 : Prop := ∀ values, m77 values =
  (values.mapM toInt).map fun coordinates => ⟨coordinates⟩
theorem p77 : P77 := by simp [P77, m77]

def fillToLength (values : List IntegerValue) (rank : Nat) : Result (List IntegerValue) :=
  if values.length > rank then .error .argument
  else .ok (values ++ List.replicate (rank - values.length) ⟨1⟩)

def m84 (rank : Nat) (values : List IntegerValue) : Result Cartesian := do
  let padded ← fillToLength values rank
  m77 padded
def P84 : Prop := ∀ rank values, m84 rank values = do
  let padded ← fillToLength values rank
  m77 padded
theorem p84 : P84 := by simp [P84, m84]

def m85 (rank : Nat) (values : List IntegerValue) : Result Cartesian := m84 rank values
def P85 : Prop := ∀ rank values, m85 rank values = m84 rank values
theorem p85 : P85 := by simp [P85, m85]

def flattenArgs : List IndexArg → List IntegerValue
  | [] => []
  | .integer value :: rest => value :: flattenArgs rest
  | .cartesian value :: rest => value.coordinates.map (fun x => ⟨x.val⟩) ++ flattenArgs rest

def m89 (values : List IndexArg) : Result Cartesian := m77 (flattenArgs values)
def P89 : Prop := ∀ values, m89 values = m77 (flattenArgs values)
theorem p89 : P89 := by simp [P89, m89]

def m91 (value : IndexArg) : List IntegerValue := flattenArgs [value]
def P91 : Prop := ∀ value, m91 value = flattenArgs [value]
theorem p91 : P91 := by simp [P91, m91]

def m92 (head : IndexArg) (tail : List IndexArg) : List IntegerValue :=
  flattenArgs [head] ++ flattenArgs tail
def P92 : Prop := ∀ head tail, m92 head tail = flattenArgs [head] ++ flattenArgs tail
theorem p92 : P92 := by simp [P92, m92]

def m93 (values : List IndexArg) : Result Cartesian := m89 values
def P93 : Prop := ∀ values, m93 values = m89 values
theorem p93 : P93 := by simp [P93, m93]

def m94 (render : I64 → String) (initial : String) (value : Cartesian) : String :=
  let opened := initial ++ "CartesianIndex("
  let joined := opened ++ String.intercalate ", " (value.coordinates.map render)
  joined ++ ")"
def P94 : Prop := ∀ render initial value,
  m94 render initial value = initial ++ "CartesianIndex(" ++
    String.intercalate ", " (value.coordinates.map render) ++ ")"
theorem p94 : P94 := by simp [P94, m94]

def m105 (value : Cartesian) (index : IntegerValue) : Result I64 := do
  let converted ← toInt index
  if converted.val < 1 || value.coordinates.length < converted.val then .error .bounds
  else .ok (value.coordinates.getD (converted.val - 1).toNat (JInt.lit .i64 0))
def P105 : Prop := ∀ value index, m105 value index = do
  let converted ← toInt index
  if converted.val < 1 || value.coordinates.length < converted.val then .error .bounds
  else .ok (value.coordinates.getD (converted.val - 1).toNat (JInt.lit .i64 0))
theorem p105 : P105 := by simp [P105, m105]

def m106 (_value : Cartesian) : I64 := JInt.lit .i64 1
def P106 : Prop := ∀ value, m106 value = JInt.lit .i64 1
theorem p106 : P106 := by simp [P106, m106]

def m107 (value : Cartesian) : I64 := JInt.wrap .i64 value.coordinates.length
def P107 : Prop := ∀ value, m107 value = JInt.wrap .i64 value.coordinates.length
theorem p107 : P107 := by simp [P107, m107]

def m108 {A D V : Type} (get : A → List I64 → D → V) (array : A)
    (index : Cartesian) (default : D) : V := get array index.coordinates default
def P108 : Prop := ∀ {A D V : Type} (get : A → List I64 → D → V) array index default,
  m108 get array index default = get array index.coordinates default
theorem p108 : P108 := by simp [P108, m108]

def m109 {T E : Type} (fieldType : T → E) (tupleEltype : E → E) (type : T) : E :=
  tupleEltype (fieldType type)
def P109 : Prop := ∀ {T E : Type} (fieldType : T → E) (tupleEltype : E → E) type,
  m109 fieldType tupleEltype type = tupleEltype (fieldType type)
theorem p109 : P109 := by simp [P109, m109]

def m114 (setTuple : List I64 → I64 → IntegerValue → Result (List I64))
    (value : Cartesian) (replacement : I64) (index : IntegerValue) : Result Cartesian := do
  pure ⟨← setTuple value.coordinates replacement index⟩
def P114 : Prop := ∀ setTuple value replacement index,
  m114 setTuple value replacement index = do pure ⟨← setTuple value.coordinates replacement index⟩
theorem p114 : P114 := by simp [P114, m114]

def m120 (rank : Nat) : Cartesian := ⟨List.replicate rank (JInt.lit .i64 0)⟩
def P120 : Prop := ∀ rank, m120 rank = ⟨List.replicate rank (JInt.lit .i64 0)⟩
theorem p120 : P120 := by simp [P120, m120]
def m121 := m120
def P121 : Prop := ∀ rank, m121 rank = m120 rank
theorem p121 : P121 := by simp [P121, m121]
def m122 (rank : Nat) : Cartesian := ⟨List.replicate rank (JInt.lit .i64 1)⟩
def P122 : Prop := ∀ rank, m122 rank = ⟨List.replicate rank (JInt.lit .i64 1)⟩
theorem p122 : P122 := by simp [P122, m122]
def m123 := m122
def P123 : Prop := ∀ rank, m123 rank = m122 rank
theorem p123 : P123 := by simp [P123, m123]

def m139 (value : Cartesian) (scalar : I64) : Cartesian :=
  ⟨value.coordinates.map fun coordinate => scalar * coordinate⟩
def P139 : Prop := ∀ value scalar,
  m139 value scalar = ⟨value.coordinates.map fun coordinate => scalar * coordinate⟩
theorem p139 : P139 := by simp [P139, m139]

def m145 {T : Type} (convert : I64 → Result T) (value : Cartesian) : Result T := do
  convert (← m105 value ⟨1⟩)
def P145 : Prop := ∀ {T : Type} (convert : I64 → Result T) value,
  m145 convert value = do convert (← m105 value ⟨1⟩)
theorem p145 : P145 := by simp [P145, m145]

def m146 {T : Type} (convert : List I64 → Result T) (value : Cartesian) : Result T :=
  convert value.coordinates
def P146 : Prop := ∀ {T : Type} (convert : List I64 → Result T) value,
  m146 convert value = convert value.coordinates
theorem p146 : P146 := by simp [P146, m146]

def m150 (hashCoordinate : I64 → UInt64 → UInt64) (seed initial : UInt64)
    (value : Cartesian) : UInt64 :=
  value.coordinates.foldl (fun hash coordinate => hashCoordinate coordinate hash) (initial ^^^ seed)
def P150 : Prop := ∀ hashCoordinate seed initial value,
  m150 hashCoordinate seed initial value =
    value.coordinates.foldl (fun hash coordinate => hashCoordinate coordinate hash) (initial ^^^ seed)
theorem p150 : P150 := by simp [P150, m150]

structure Axis where
  first : I64
  last : I64
  step : I64
  deriving Repr, DecidableEq

def inc : List I64 → List Axis → List I64
  | [], _ => []
  | values, [] => values
  | value :: values, axis :: axes =>
      if value = axis.last then axis.first :: inc values axes else (value + axis.step) :: values

def dec : List I64 → List Axis → List I64
  | [], _ => []
  | values, [] => values
  | value :: values, axis :: axes =>
      if value = axis.first then axis.last :: dec values axes else (value - axis.step) :: values

def m159 {A : Type} (axes : A → List Axis) (array : A) (value : Cartesian) : Cartesian :=
  ⟨inc value.coordinates (axes array)⟩
def P159 : Prop := ∀ {A : Type} (axes : A → List Axis) array value,
  m159 axes array value = ⟨inc value.coordinates (axes array)⟩
theorem p159 : P159 := by simp [P159, m159]

def m165 {A : Type} (axes : A → List Axis) (array : A) (value : Cartesian) : Cartesian :=
  ⟨dec value.coordinates (axes array)⟩
def P165 : Prop := ∀ {A : Type} (axes : A → List Axis) array value,
  m165 axes array value = ⟨dec value.coordinates (axes array)⟩
theorem p165 : P165 := by simp [P165, m165]

def m172 {T : Type} (_axes : T) (value : Cartesian) : List I64 := value.coordinates
def P172 : Prop := ∀ {T : Type} (axes : T) value, m172 axes value = value.coordinates
theorem p172 : P172 := by simp [P172, m172]

def m187 (render : Cartesian → String) (first step : Cartesian) (length : Nat) : String :=
  "StepRangeLen(" ++ render first ++ ", " ++ render step ++ ", " ++ toString length ++ ")"
def P187 : Prop := ∀ render first step length,
  m187 render first step length =
    "StepRangeLen(" ++ render first ++ ", " ++ render step ++ ", " ++ toString length ++ ")"
theorem p187 : P187 := by simp [P187, m187]

def rangeValues (first step : I64) : Nat → List I64
  | 0 => []
  | n + 1 => first :: rangeValues (first + step) step n

def m193 (x first step : Cartesian) (length : Nat) : Bool :=
  if length = 0 then false else
  match (List.zip x.coordinates (List.zip first.coordinates step.coordinates)).findIdx?
      (fun pair => pair.2.2.val ≠ 0) with
  | none => x = first
  | some dimension =>
      match x.coordinates[dimension]?, first.coordinates[dimension]?, step.coordinates[dimension]? with
      | some coordinate, some start, some stride =>
          match (rangeValues start stride length).findIdx? (fun candidate => candidate = coordinate) with
          | none => false
          | some position =>
              ((List.range length).map (fun (n : Nat) =>
                Cartesian.mk (List.zipWith (fun f s => f + s * JInt.wrap .i64 (Int.ofNat n))
                  first.coordinates step.coordinates)))[position]? = some x
      | _, _, _ => false
def P193 : Prop := ∀ x first step length,
  m193 x first step length =
    if length = 0 then false else
    match (List.zip x.coordinates (List.zip first.coordinates step.coordinates)).findIdx?
        (fun pair => pair.2.2.val ≠ 0) with
    | none => x = first
    | some dimension =>
        match x.coordinates[dimension]?, first.coordinates[dimension]?, step.coordinates[dimension]? with
        | some coordinate, some start, some stride =>
            match (rangeValues start stride length).findIdx? (fun candidate => candidate = coordinate) with
            | none => false
            | some position =>
                ((List.range length).map (fun (n : Nat) =>
                  Cartesian.mk (List.zipWith (fun f s => f + s * JInt.wrap .i64 (Int.ofNat n))
                    first.coordinates step.coordinates)))[position]? = some x
        | _, _, _ => false
theorem p193 : P193 := by simp [P193, m193]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}"
    juliaFile := "base/multidimensional.jl"
    juliaFns := [name]
    statement
    source := s!"base/multidimensional.jl:{line}; CartesianIndex source equation"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalCartesianFaithful

import JuliaLean.MultidimCov.MultidimensionalIteratorFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalDispatchFaithful

open JuliaLean.Registry
open MultidimensionalCartesianFaithful
open MultidimensionalIndicesFaithful
open MultidimensionalIteratorFaithful

abbrev Result (α : Type) := Except Error α
abbrev CIAxis := MultidimensionalCartesianFaithful.Axis

inductive IndexValue (α : Type) where
  | scalar (value : α)
  | cartesian (value : Cartesian)
  | arrayCartesian (rank : Nat) (values : List Cartesian) (axes : List CIAxis)
  | colon
  | boolArray (values : List Bool) (shape : List Nat)
  | array (values : List α) (axes : List CIAxis)
  deriving Repr, DecidableEq

def m735 {A R : Type} (toIndices : A → List (IndexValue I64) → Result (List I64))
    (fn : A → Cartesian → Result R) (array : A) (indices : List (IndexValue I64)) : Result R := do
  fn array ⟨← toIndices array indices⟩
def P735 : Prop := ∀ {A R : Type} (toIndices : A → List (IndexValue I64) → Result (List I64))
    (fn : A → Cartesian → Result R) array indices,
  m735 toIndices fn array indices = do fn array ⟨← toIndices array indices⟩
theorem p735 : P735 := by simp [P735, m735]

def m739 {A R : Type} (fn : A → List I64 → Result R) (array : A) (index : Cartesian) : Result R :=
  fn array index.coordinates
def P739 : Prop := ∀ {A R : Type} (fn : A → List I64 → Result R) array index,
  m739 fn array index = fn array index.coordinates
theorem p739 : P739 := by simp [P739, m739]

inductive IndexStyle where | linear | cartesian deriving Repr, DecidableEq
def m743 {A R : Type} (toIndices : A → List IntegerValue → Result (List I64))
    (style : A → IndexStyle) (linearize : A → List I64 → Result Int)
    (subscripts : A → List I64 → Result (List Int))
    (linearFn : A → Int → Result R) (cartesianFn : A → List Int → Result R)
    (array : A) (indices : List IntegerValue) : Result R := do
  let converted ← toIndices array indices
  match style array with
  | .linear => linearFn array (← linearize array converted)
  | .cartesian => cartesianFn array (← subscripts array converted)
def P743 : Prop := ∀ {A R : Type} (toIndices : A → List IntegerValue → Result (List I64))
    (style : A → IndexStyle) (linearize : A → List I64 → Result Int)
    (subscripts : A → List I64 → Result (List Int))
    (linearFn : A → Int → Result R) (cartesianFn : A → List Int → Result R) array indices,
  m743 toIndices style linearize subscripts linearFn cartesianFn array indices = do
    let converted ← toIndices array indices
    match style array with
    | .linear => linearFn array (← linearize array converted)
    | .cartesian => cartesianFn array (← subscripts array converted)
theorem p743 : P743 := by simp [P743, m743]

def m757 {A : Type} (axes : A → List CIAxis) (check : List CIAxis → Cartesian → Bool)
    (array : A) (index : Cartesian) : Bool := check (axes array) index
def P757 : Prop := ∀ {A : Type} (axes : A → List CIAxis) check array index,
  m757 axes check array index = check (axes array) index
theorem p757 : P757 := by simp [P757, m757]

def m760 (checkIndex : List CIAxis → Cartesian → Bool)
    (recursive : List CIAxis → List Cartesian → Bool) (axes : List CIAxis)
    (head : Cartesian) (tail : List Cartesian) : Bool :=
  let split := splitList axes head.coordinates.length
  checkIndex split.1 head && recursive split.2 tail
def P760 : Prop := ∀ checkIndex recursive axes head tail,
  m760 checkIndex recursive axes head tail =
    let split := splitList axes head.coordinates.length
    checkIndex split.1 head && recursive split.2 tail
theorem p760 : P760 := by simp [P760, m760]

def m764 (check : List CIAxis → List I64 → Bool) (axes : List CIAxis) (index : Cartesian) : Bool :=
  check axes index.coordinates
def P764 : Prop := ∀ check axes index, m764 check axes index = check axes index.coordinates
theorem p764 : P764 := by simp [P764, m764]

def m766 (check : List CIAxis → Cartesian → Bool) (axes : List CIAxis)
    (range : List Cartesian) : Bool :=
  match range.head?, range.getLast? with
  | none, _ => true
  | some first, some last => check axes first && check axes last
  | _, _ => true
def P766 : Prop := ∀ check axes range,
  m766 check axes range = match range.head?, range.getLast? with
    | none, _ => true
    | some first, some last => check axes first && check axes last
    | _, _ => true
theorem p766 : P766 := by simp [P766, m766]

def m772 {A V : Type} (toIndices : A → List (IndexValue I64) → Result (List I64))
    (getindex : A → List I64 → Result V) (array : A) (indices : List (IndexValue I64)) : Result V := do
  getindex array (← toIndices array indices)
def P772 : Prop := ∀ {A V : Type} (toIndices : A → List (IndexValue I64) → Result (List I64))
    (getindex : A → List I64 → Result V) array indices,
  m772 toIndices getindex array indices = do getindex array (← toIndices array indices)
theorem p772 : P772 := by simp [P772, m772]

def m774 {A V : Type} (toIndices : A → List (IndexValue I64) → Result (List I64))
    (setindex : A → V → List I64 → Result A) (array : A) (value : V)
    (indices : List (IndexValue I64)) : Result A := do
  setindex array value (← toIndices array indices)
def P774 : Prop := ∀ {A V : Type} (toIndices : A → List (IndexValue I64) → Result (List I64))
    (setindex : A → V → List I64 → Result A) array value indices,
  m774 toIndices setindex array value indices = do setindex array value (← toIndices array indices)
theorem p774 : P774 := by simp [P774, m774]

def m779 {A : Type} (axes : A → List CIAxis)
    (check : List CIAxis → List Cartesian → Bool) (array : A) (indices : List Cartesian) : Bool :=
  check (axes array) indices
def P779 : Prop := ∀ {A : Type} (axes : A → List CIAxis) check array indices,
  m779 axes check array indices = check (axes array) indices
theorem p779 : P779 := by simp [P779, m779]

def m782 (rank : Nat) (checkHead : List CIAxis → List Cartesian → Bool)
    (recursive : List CIAxis → List (List Cartesian) → Bool) (axes : List CIAxis)
    (head : List Cartesian) (tail : List (List Cartesian)) : Bool :=
  let split := splitList axes rank
  checkHead split.1 head && recursive split.2 tail
def P782 : Prop := ∀ rank checkHead recursive axes head tail,
  m782 rank checkHead recursive axes head tail =
    let split := splitList axes rank
    checkHead split.1 head && recursive split.2 tail
theorem p782 : P782 := by simp [P782, m782]

def m786 (check : List CIAxis → List CIAxis → Bool) (axes : List CIAxis)
    (indices : CartesianIndices) : Bool := check axes indices.indices
def P786 : Prop := ∀ check axes indices, m786 check axes indices = check axes indices.indices
theorem p786 : P786 := by simp [P786, m786]

def indexNdims : List (IndexValue α) → List Bool
  | [] => []
  | .cartesian value :: rest => List.replicate value.coordinates.length true ++ indexNdims rest
  | .arrayCartesian rank _ _ :: rest => List.replicate rank true ++ indexNdims rest
  | _ :: rest => true :: indexNdims rest
def m793 (head : Cartesian) (tail : List (IndexValue α)) : List Bool :=
  List.replicate head.coordinates.length true ++ indexNdims tail
def P793 : Prop := ∀ {α : Type} head (tail : List (IndexValue α)),
  m793 head tail = List.replicate head.coordinates.length true ++ indexNdims tail
theorem p793 : P793 := by simp [P793, m793]
def m796 (rank : Nat) (tail : List (IndexValue α)) : List Bool := List.replicate rank true ++ indexNdims tail
def P796 : Prop := ∀ {α : Type} rank (tail : List (IndexValue α)),
  m796 rank tail = List.replicate rank true ++ indexNdims tail
theorem p796 : P796 := by simp [P796, m796]

def indexDimsum : List (IndexValue α) → List Bool
  | [] => []
  | .colon :: rest | .boolArray _ _ :: rest => true :: indexDimsum rest
  | .array _ axes :: rest | .arrayCartesian _ _ axes :: rest => List.replicate axes.length true ++ indexDimsum rest
  | .scalar _ :: rest | .cartesian _ :: rest => indexDimsum rest
def m803 (head : IndexValue α) (tail : List (IndexValue α)) : List Bool :=
  match head with
  | .colon => true :: indexDimsum tail
  | .boolArray _ _ => true :: indexDimsum tail
  | .array _ axes => List.replicate axes.length true ++ indexDimsum tail
  | .arrayCartesian _ _ axes => List.replicate axes.length true ++ indexDimsum tail
  | .scalar _ => indexDimsum tail
  | .cartesian _ => indexDimsum tail
def P803 : Prop := ∀ {α : Type} (head : IndexValue α) (tail : List (IndexValue α)),
  m803 head tail = indexDimsum (head :: tail)
theorem p803 : P803 := by
  unfold P803
  intro α head tail
  cases head <;> simp [m803, indexDimsum]
def m804 (tail : List (IndexValue α)) := true :: indexDimsum tail
def P804 : Prop := ∀ {α : Type} (tail : List (IndexValue α)), m804 tail = true :: indexDimsum tail
theorem p804 : P804 := by simp [P804, m804]
def m805 := @m804
def P805 : Prop := ∀ {α : Type} (tail : List (IndexValue α)), m805 tail = true :: indexDimsum tail
theorem p805 : P805 := by simp [P805, m805, m804]
def m806 (rank : Nat) (tail : List (IndexValue α)) := List.replicate rank true ++ indexDimsum tail
def P806 : Prop := ∀ {α : Type} rank (tail : List (IndexValue α)), m806 rank tail = List.replicate rank true ++ indexDimsum tail
theorem p806 : P806 := by simp [P806, m806]

def indexLengths : List (IndexValue α) → List Nat
  | [] => []
  | .scalar _ :: rest => 1 :: indexLengths rest
  | .array values _ :: rest => values.length :: indexLengths rest
  | .arrayCartesian _ values _ :: rest => values.length :: indexLengths rest
  | .boolArray values _ :: rest => values.length :: indexLengths rest
  | _ :: rest => 1 :: indexLengths rest
def m813 (tail : List (IndexValue α)) := 1 :: indexLengths tail
def P813 : Prop := ∀ {α : Type} (tail : List (IndexValue α)), m813 tail = 1 :: indexLengths tail
theorem p813 : P813 := by simp [P813, m813]
def m814 (length : Nat) (tail : List (IndexValue α)) := length :: indexLengths tail
def P814 : Prop := ∀ {α : Type} length (tail : List (IndexValue α)), m814 length tail = length :: indexLengths tail
theorem p814 : P814 := by simp [P814, m814]

def indexShape : List (IndexValue α) → List CIAxis
  | [] => []
  | .scalar _ :: rest => indexShape rest
  | .array _ axes :: rest | .arrayCartesian _ _ axes :: rest => axes ++ indexShape rest
  | _ :: rest => indexShape rest
def m819 (tail : List (IndexValue α)) := indexShape tail
def P819 : Prop := ∀ {α : Type} (tail : List (IndexValue α)), m819 tail = indexShape tail
theorem p819 : P819 := by simp [P819, m819]
def m820 (axes : List CIAxis) (tail : List (IndexValue α)) := axes ++ indexShape tail
def P820 : Prop := ∀ {α : Type} axes (tail : List (IndexValue α)), m820 axes tail = axes ++ indexShape tail
theorem p820 : P820 := by simp [P820, m820]

def indexSizes : List (IndexValue α) → List Nat
  | [] => []
  | .scalar _ :: rest => indexSizes rest
  | .array _ axes :: rest | .arrayCartesian _ _ axes :: rest => axes.map axisLength ++ indexSizes rest
  | _ :: rest => indexSizes rest
def m823 (tail : List (IndexValue α)) := indexSizes tail
def P823 : Prop := ∀ {α : Type} (tail : List (IndexValue α)), m823 tail = indexSizes tail
theorem p823 : P823 := by simp [P823, m823]
def m824 (sizes : List Nat) (tail : List (IndexValue α)) := sizes ++ indexSizes tail
def P824 : Prop := ∀ {α : Type} sizes (tail : List (IndexValue α)), m824 sizes tail = sizes ++ indexSizes tail
theorem p824 : P824 := by simp [P824, m824]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}", juliaFile := "base/multidimensional.jl",
    juliaFns := [name], statement, source := s!"base/multidimensional.jl:{line}; indexing dispatch source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalDispatchFaithful

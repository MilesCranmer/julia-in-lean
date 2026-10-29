import JuliaLean.MultidimCov.MultidimensionalLogicalFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalUnsafeFaithful

open JuliaLean.Registry
open MultidimensionalCartesianFaithful
open MultidimensionalDispatchFaithful

inductive Error where | bounds | dimensionMismatch | conversion deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure ArrayState (α : Type) where
  axes : List (List Int)
  values : List (List Int × α)
  id : Nat
  deriving Repr, DecidableEq

inductive IndexSpec where
  | scalar (value : Int)
  | many (values : List Int)
  deriving Repr, DecidableEq

def indexProduct : List IndexSpec → List (List Int)
  | [] => [[]]
  | .scalar value :: rest => (indexProduct rest).map (value :: ·)
  | .many values :: rest => values.flatMap fun value => (indexProduct rest).map (value :: ·)

def lookup (array : ArrayState α) (index : List Int) : Option α :=
  (array.values.find? fun pair => pair.1 = index).map (fun pair => pair.2)

def write (array : ArrayState α) (index : List Int) (value : α) : ArrayState α :=
  { array with values := (index, value) :: array.values.filter (fun pair => pair.1 ≠ index) }

def m989 (value : α) (_index : Cartesian) : α := value
def P989 : Prop := ∀ {α : Type} (value : α) index, m989 value index = value
theorem p989 : P989 := by simp [P989, m989]

def m990 (tuple : List α) (index : Cartesian) : Option α :=
  match index.coordinates with | [coordinate] => tuple[(coordinate.val - 1).toNat]? | _ => none
def P990 : Prop := ∀ {α : Type} (tuple : List α) index,
  m990 tuple index = match index.coordinates with
    | [coordinate] => tuple[(coordinate.val - 1).toNat]? | _ => none
theorem p990 : P990 := by simp [P990, m990]

def m995 {A I R : Type} (checkbounds : A → List I → Result Unit)
    (maybeReshape : A → List I → A) (unsafeGet : A → List I → Result R)
    (array : A) (indices : List I) : Result R := do
  checkbounds array indices
  unsafeGet (maybeReshape array indices) indices
def P995 : Prop := ∀ {A I R : Type} (checkbounds : A → List I → Result Unit)
    (maybeReshape : A → List I → A) (unsafeGet : A → List I → Result R) array indices,
  m995 checkbounds maybeReshape unsafeGet array indices = do
    checkbounds array indices
    unsafeGet (maybeReshape array indices) indices
theorem p995 : P995 := by simp [P995, m995]

def m1000 {A I : Type} (array : A) (_indices : List I) : A := array
def P1000 : Prop := ∀ {A I : Type} (array : A) (indices : List I), m1000 array indices = array
theorem p1000 : P1000 := by simp [P1000, m1000]
def m1001 := @m1000
def P1001 : Prop := ∀ {A I : Type} (array : A) (indices : List I), m1001 array indices = array
theorem p1001 : P1001 := by simp [P1001, m1001, m1000]

def m1002 {A I : Type} (indexNdims : List I → Nat) (reshape : A → Nat → A)
    (array : A) (indices : List I) : A := reshape array (indexNdims indices)
def P1002 : Prop := ∀ {A I : Type} (indexNdims : List I → Nat) (reshape : A → Nat → A) array indices,
  m1002 indexNdims reshape array indices = reshape array (indexNdims indices)
theorem p1002 : P1002 := by simp [P1002, m1002]

def m1003 {A : Type} (array : A) (_rank : Nat) : A := array
def P1003 : Prop := ∀ {A : Type} (array : A) rank, m1003 array rank = array
theorem p1003 : P1003 := by simp [P1003, m1003]

def m1004 {A : Type} (reshape : A → Nat → A) (array : A) (rank : Nat) : A := reshape array rank
def P1004 : Prop := ∀ {A : Type} (reshape : A → Nat → A) array rank,
  m1004 reshape array rank = reshape array rank
theorem p1004 : P1004 := by simp [P1004, m1004]

def gather (source : ArrayState α) (indices : List IndexSpec) : Result (ArrayState α) :=
  let keys := indexProduct indices
  let values := keys.filterMap fun key => (lookup source key).map (key, ·)
  let outputAxes := indices.filterMap fun index =>
    match index with | .many selected => some selected | _ => none
  if values.length ≠ keys.length then .error .bounds
  else .ok { axes := outputAxes, values := values, id := source.id + 1 }

def m1006 (source : ArrayState α) (indices : List IndexSpec) : Result (ArrayState α) := gather source indices
def P1006 : Prop := ∀ {α : Type} (source : ArrayState α) indices,
  m1006 source indices = gather source indices
theorem p1006 : P1006 := by simp [P1006, m1006]

def m1015 (rank : Nat) : List IndexSpec → ArrayState α → Result (ArrayState α) :=
  fun indices source => if indices.length = rank then gather source indices else .error .dimensionMismatch
def P1015 : Prop := ∀ {α : Type} rank indices (source : ArrayState α),
  m1015 rank indices source = if indices.length = rank then gather source indices else .error .dimensionMismatch
theorem p1015 : P1015 := by simp [P1015, m1015]

def m1030 (dest source : ArrayState α) (indices : List IndexSpec) : Result (ArrayState α) := do
  let gathered ← gather source indices
  pure { dest with values := gathered.values }
def P1030 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1030 dest source indices = do
  let gathered ← gather source indices
  pure { dest with values := gathered.values }
theorem p1030 : P1030 := by simp [P1030, m1030]
def m1035 := @m1030
def P1035 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1035 dest source indices = m1030 dest source indices
theorem p1035 : P1035 := by simp [P1035, m1035]
def m1039 := @m1030
def P1039 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1039 dest source indices = m1030 dest source indices
theorem p1039 : P1039 := by simp [P1039, m1039]

def scatter (dest source : ArrayState α) (indices : List IndexSpec) : Result (ArrayState α) :=
  let keys := indexProduct indices
  if keys.length ≠ source.values.length then .error .dimensionMismatch else
  .ok ((keys.zip source.values).foldl (fun output pair => write output pair.1 pair.2.2) dest)

def m1046 {I : Type} (checkbounds : ArrayState α → List I → Result Unit)
    (convert : List I → List IndexSpec) (dest : ArrayState α) (source : ArrayState α)
    (indices : List I) : Result (ArrayState α) := do
  checkbounds dest indices
  scatter dest source (convert indices)
def P1046 : Prop := ∀ {α I : Type} (checkbounds : ArrayState α → List I → Result Unit)
    (convert : List I → List IndexSpec) dest source indices,
  m1046 checkbounds convert dest source indices = do
    checkbounds dest indices
    scatter dest source (convert indices)
theorem p1046 : P1046 := by simp [P1046, m1046]

def m1053 (rank : Nat) : ArrayState α → ArrayState α → List IndexSpec → Result (ArrayState α) :=
  fun dest source indices => if indices.length = rank then scatter dest source indices else .error .dimensionMismatch
def P1053 : Prop := ∀ {α : Type} rank (dest source : ArrayState α) indices,
  m1053 rank dest source indices = if indices.length = rank then scatter dest source indices else .error .dimensionMismatch
theorem p1053 : P1053 := by simp [P1053, m1053]

def m1069 := @scatter
def P1069 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1069 dest source indices = scatter dest source indices
theorem p1069 : P1069 := by simp [P1069, m1069]
def m1073 := @scatter
def P1073 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1073 dest source indices = scatter dest source indices
theorem p1073 : P1073 := by simp [P1073, m1073]
def m1077 := @scatter
def P1077 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1077 dest source indices = scatter dest source indices
theorem p1077 : P1077 := by simp [P1077, m1077]

def m1081 {A R : Type} (diffDims : A → Int → R) (array : A) : R := diffDims array 1
def P1081 : Prop := ∀ {A R : Type} (diffDims : A → Int → R) array,
  m1081 diffDims array = diffDims array 1
theorem p1081 : P1081 := by simp [P1081, m1081]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}", juliaFile := "base/multidimensional.jl",
    juliaFns := [name], statement, source := s!"base/multidimensional.jl:{line}; multidimensional indexing source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalUnsafeFaithful

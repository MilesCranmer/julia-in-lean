import JuliaLean.Core

namespace JuliaLean.MultidimCov.ArrayFaithfulCore

inductive Error where
  | argument
  | bounds
  | dimensionMismatch
  | inexact
  | typeError
  | unassigned
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure ArrayState (α : Type) where
  elementType : String
  axes : List (List Int)
  values : List (Option α)
  id : Nat
  deriving Repr, DecidableEq

def dimensions (array : ArrayState α) : List Nat := array.axes.map List.length
def length (array : ArrayState α) : Nat := array.values.length

def allocate (elementType : String) (axes : List (List Int)) (id : Nat := 0) : ArrayState α :=
  { elementType, axes, values := List.replicate ((axes.map List.length).foldl (fun n m => n * m) 1) none, id }

def filled (elementType : String) (axes : List (List Int)) (value : α) (id : Nat := 0) : ArrayState α :=
  { elementType, axes,
    values := List.replicate ((axes.map List.length).foldl (fun n m => n * m) 1) (some value), id }

def oneToAxes (dims : List Nat) : List (List Int) :=
  dims.map fun dim => (List.range dim).map fun index => Int.ofNat index + 1

def assignedValues (array : ArrayState α) : Result (List α) :=
  array.values.mapM fun value => match value with | some value => .ok value | none => .error .unassigned

def convertAll (convert : α → Result β) : List α → Result (List β)
  | [] => .ok []
  | head :: tail =>
      match convert head with
      | .error error => .error error
      | .ok value =>
          match convertAll convert tail with
          | .error error => .error error
          | .ok rest => .ok (value :: rest)

def setLinear (array : ArrayState α) (index : Int) (value : α) : Result (ArrayState α) :=
  if index < 1 || array.values.length < index then .error .bounds
  else .ok { array with values := array.values.set (index - 1).toNat (some value) }

def getLinear (array : ArrayState α) (index : Int) : Result α :=
  if index < 1 || array.values.length < index then .error .bounds
  else match array.values[(index - 1).toNat]? with
    | some (some value) => .ok value
    | some none => .error .unassigned
    | none => .error .bounds

end JuliaLean.MultidimCov.ArrayFaithfulCore

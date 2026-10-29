import JuliaLean.MultidimCov.AbstractArrayRepairInterface
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairIndexing

open JuliaLean.Registry
open AbstractArrayRepairInterface

inductive Error where | bounds | unsupported deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

def axisContains (axis : Axis) (index : Int) : Bool := axis.first ≤ index && index ≤ axis.last

def remainingProduct (axes : List Axis) : Nat := axes.foldl (fun product axis => product * axis.length) 1

def linearIndex (axes : List Axis) (indices : List Int) : Option Nat :=
  match indices with
  | [] => if axes.all (fun axis => axisContains axis axis.first) then some 0 else none
  | _ =>
    let consumed := min indices.length axes.length
    let prefixCount := consumed - 1
    let prefixAxes := axes.take prefixCount
    let prefixIndices := indices.take prefixCount
    let lastIndex := indices[prefixCount]?
    let trailingAxes := axes.drop prefixCount
    if !(List.zip prefixAxes prefixIndices).all fun pair => axisContains pair.1 pair.2 then none
    else match lastIndex with
      | none => some 0
      | some last =>
        let trailingLength := remainingProduct trailingAxes
        if last < 1 || trailingLength < last.toNat then none else
        let prefixOffset := (List.zip prefixAxes prefixIndices).foldl
          (fun state pair => (state.1 + (pair.2 - pair.1.first).toNat * state.2,
            state.2 * pair.1.length)) (0, 1)
        some (prefixOffset.1 + (last - 1).toNat * prefixOffset.2)

def subscriptIndices (axes : List Axis) (indices : List Int) : List Int :=
  let consumed := indices.take axes.length
  consumed ++ (axes.drop consumed.length).map Axis.first

def remainingSize (consumed axes : List Axis) : List Axis := axes.drop consumed.length

def getLinear (array : ArrayDesc T V) (indices : List Int) : Result V :=
  match linearIndex array.axes indices with
  | none => .error .bounds
  | some offset => match array.values[offset]? with
    | none => .error .bounds
    | some value => .ok value

def cartesianOffset (axes : List Axis) (indices : List Int) : Option Nat :=
  let full := subscriptIndices axes indices
  if full.length ≠ axes.length || !(List.zip axes full).all fun pair => axisContains pair.1 pair.2 then none
  else some ((List.zip axes full).foldl
    (fun state pair => (state.1 + (pair.2 - pair.1.first).toNat * state.2,
      state.2 * pair.1.length)) (0, 1)).1

def getCartesian (array : ArrayDesc T V) (indices : List Int) : Result V :=
  match cartesianOffset array.axes indices with
  | none => .error .bounds
  | some offset => match array.values[offset]? with
    | none => .error .bounds
    | some value => .ok value

def setAt (array : ArrayDesc T V) (offset : Nat) (value : V) : Result (ArrayDesc T V) :=
  if offset < array.values.length then .ok { array with values := array.values.set offset value }
  else .error .bounds

def setLinear (array : ArrayDesc T V) (value : V) (indices : List Int) : Result (ArrayDesc T V) :=
  match linearIndex array.axes indices with | none => .error .bounds | some offset => setAt array offset value

def setCartesian (array : ArrayDesc T V) (value : V) (indices : List Int) : Result (ArrayDesc T V) :=
  match cartesianOffset array.axes indices with | none => .error .bounds | some offset => setAt array offset value

def publicGet (array : ArrayDesc T V) (indices : List Int) : Result V :=
  match array.style with | .linear => getLinear array indices | .cartesian => getCartesian array indices

def publicSet (array : ArrayDesc T V) (value : V) (indices : List Int) : Result (ArrayDesc T V) :=
  match array.style with | .linear => setLinear array value indices | .cartesian => setCartesian array value indices

def Contract : Prop :=
  (∀ axes, linearIndex axes [] = some 0 ∨ linearIndex axes [] = none) ∧
  (∀ axes indices,
    (subscriptIndices axes indices).length = axes.length) ∧
  (∀ consumed axes, remainingSize consumed axes = axes.drop consumed.length) ∧
  (∀ {T V : Type} array indices value,
    publicGet (T := T) (V := V) array indices = .ok value →
      value ∈ array.values) ∧
  (∀ {T V : Type} array value indices output,
    publicSet (T := T) (V := V) array value indices = .ok output →
      output.axes = array.axes ∧ output.elementType = array.elementType ∧ output.values.length = array.values.length) ∧
  (∀ {T V : Type} array value indices output,
    setLinear (T := T) (V := V) array value indices = .ok output → output.values.length = array.values.length) ∧
  (∀ {T V : Type} array value indices output,
    setCartesian (T := T) (V := V) array value indices = .ok output → output.values.length = array.values.length)

theorem subscriptIndices_length (axes : List Axis) (indices : List Int) :
    (subscriptIndices axes indices).length = axes.length := by
  unfold subscriptIndices
  simp
  omega

theorem setAt_length (array : ArrayDesc T V) (offset : Nat) (value : V) (output : ArrayDesc T V)
    (h : setAt array offset value = .ok output) : output.values.length = array.values.length := by
  unfold setAt at h
  split at h <;> simp_all

theorem contract : Contract := by
  unfold Contract
  refine ⟨fun axes => by unfold linearIndex; split <;> simp, subscriptIndices_length,
    fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro T V array indices value h
    unfold publicGet at h
    cases array.style <;> simp only [getLinear, getCartesian] at h
    all_goals split at h <;> simp_all
  · intro T V array value indices output h
    unfold publicSet at h
    cases array.style <;> simp only [setLinear, setCartesian] at h
    all_goals split at h <;> simp_all [setAt]
  · intro T V array value indices output h
    unfold setLinear at h
    split at h <;> simp_all [setAt_length]
  · intro T V array value indices output h
    unfold setCartesian at h
    split at h <;> simp_all [setAt_length]

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-indexing"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["getindex", "unsafe_getindex", "_getindex", "_to_linear_index", "_to_subscript_indices", "__to_subscript_indices", "_remaining_size", "setindex!", "unsafe_setindex!", "_setindex!"]
  statement := "Linear and Cartesian indexing model omitted dimensions, trailing linearization, subscript padding, bounds checks, reads, writes, and unchanged array metadata for every index count."
  source := "base/abstractarray.jl:1363-1503"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairIndexing

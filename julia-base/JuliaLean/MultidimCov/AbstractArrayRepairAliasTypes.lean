import JuliaLean.MultidimCov.AbstractArrayRepairIndexing
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairAliasTypes

open JuliaLean.Registry
open AbstractArrayRepairInterface
open AbstractArrayRepairIndexing

inductive Error where | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

def isDisjoint (left right : List Nat) : Bool :=
  left.all fun value => !(right.contains value)

structure AliasObject (A : Type) where
  value : A
  dataIds : List Nat
  bits : Bool
  empty : Bool
  deriving Repr, DecidableEq

def mightAlias (left right : AliasObject A) : Bool :=
  !left.bits && !right.bits && !left.empty && !right.empty && !isDisjoint left.dataIds right.dataIds

def unalias (copy : A → A) (destination source : AliasObject A) : AliasObject A :=
  if mightAlias destination source then { source with value := copy source.value } else source

def unaliascopy (copy : A → A) (source : AliasObject A) : AliasObject A :=
  { source with value := copy source.value }

def dataidsObject (objectId : Nat) : List Nat := [objectId]
def dataidsPointer (pointer : Nat) : List Nat := [pointer]
def dataidsMemory (memoryIds : List Nat) : List Nat := memoryIds

def getDefault (array : ArrayDesc T V) (indices : List Int) (default : V) : V :=
  match publicGet array indices with | .ok value => value | .error _ => default

def getDefaultLazy (array : ArrayDesc T V) (indices : List Int)
    (fallback : Unit → V) : V :=
  match publicGet array indices with | .ok value => value | .error _ => fallback ()

def getBang (array : ArrayDesc T V) (indices : List (List Int)) (default : V) : List V :=
  indices.map fun index => getDefault array index default

def getBangLazy (array : ArrayDesc T V) (indices : List (List Int))
    (fallback : Unit → V) : List V :=
  indices.map fun index => getDefaultLazy array index fallback

inductive TypeTag where
  | known (name : String)
  | bottom
  | unknown
  deriving Repr, DecidableEq

def eltypeof : TypeTag → TypeTag
  | .known name => .known name
  | .bottom => .bottom
  | .unknown => .unknown

def promoteTwo (promote : TypeTag → TypeTag → TypeTag) (left right : TypeTag) :=
  promote (eltypeof left) (eltypeof right)

def promoteMany (promote : TypeTag → TypeTag → TypeTag) : List TypeTag → TypeTag
  | [] => .bottom
  | first :: rest => rest.foldl (fun current value => promote current (eltypeof value)) (eltypeof first)

def Contract : Prop :=
  (∀ left right,
    isDisjoint left right = true ↔ ∀ value ∈ left, value ∉ right) ∧
  (∀ {A : Type} left right,
    mightAlias (A := A) left right = true →
      left.bits = false ∧ right.bits = false ∧ left.empty = false ∧ right.empty = false ∧
        isDisjoint left.dataIds right.dataIds = false) ∧
  (∀ {A : Type} copy destination source,
    (unalias (A := A) copy destination source).dataIds = source.dataIds) ∧
  (∀ {A : Type} copy source,
    (unaliascopy (A := A) copy source).dataIds = source.dataIds) ∧
  (∀ objectId, dataidsObject objectId = [objectId]) ∧
  (∀ pointer, dataidsPointer pointer = [pointer]) ∧
  (∀ memoryIds, dataidsMemory memoryIds = memoryIds) ∧
  (∀ {T V : Type} array indices default,
    getDefault (T := T) (V := V) array indices default =
      match publicGet array indices with | .ok value => value | .error _ => default) ∧
  (∀ {T V : Type} array indices fallback,
    getDefaultLazy (T := T) (V := V) array indices fallback =
      match publicGet array indices with | .ok value => value | .error _ => fallback ()) ∧
  (∀ {T V : Type} array indices default,
    (getBang (T := T) (V := V) array indices default).length = indices.length) ∧
  (∀ {T V : Type} array indices fallback,
    (getBangLazy (T := T) (V := V) array indices fallback).length = indices.length) ∧
  (∀ promote left right, promoteTwo promote left right = promote (eltypeof left) (eltypeof right)) ∧
  (∀ promote types, promoteMany promote types = match types with
    | [] => .bottom
    | first :: rest => rest.foldl (fun current value => promote current (eltypeof value)) (eltypeof first))

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, ?_, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, fun _ _ _ => rfl, fun _ _ => rfl⟩
  · intro left right
    simp [isDisjoint, List.all_eq_true]
  · intro A left right h
    simp [mightAlias, isDisjoint, List.all_eq_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · intros
    simp [unalias]
  · intros
    rfl
  · intros
    simp [getBang]
  · intros
    simp [getBangLazy]

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-alias-types"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["unalias", "unaliascopy", "mightalias", "_isdisjoint", "dataids", "get", "get!", "eltypeof", "promote_eltypeof", "promote_eltype"]
  statement := "Aliasing, data identity, defaulted indexing, bulk get, element-type extraction, and promotion derive from concrete identity sets, arrays, fallback evaluation, and type tags."
  source := "base/abstractarray.jl:1566-1694"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairAliasTypes

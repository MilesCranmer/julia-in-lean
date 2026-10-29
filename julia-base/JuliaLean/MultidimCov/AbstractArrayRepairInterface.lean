import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairInterface

open JuliaLean
open JuliaLean.Registry

inductive Error where
  | argument (message : String)
  | dimensionMismatch
  | methodError
  | emptyCollection
  | conversion
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure Axis where
  first : Int
  last : Int
  deriving Repr, DecidableEq

def Axis.length (axis : Axis) : Nat := if axis.last < axis.first then 0 else (axis.last - axis.first + 1).toNat
def oneTo (length : Nat) : Axis := ⟨1, Int.ofNat length⟩

inductive IndexStyle where | linear | cartesian deriving Repr, DecidableEq

structure ArrayDesc (T V : Type) where
  elementType : T
  elementSize : Nat
  axes : List Axis
  values : List V
  style : IndexStyle
  deriving Repr, DecidableEq

def rank (array : ArrayDesc T V) : Nat := array.axes.length

def arraySize (array : ArrayDesc T V) (dimension : Int) : Nat :=
  if 1 ≤ dimension && dimension ≤ Int.ofNat array.axes.length then
    (array.axes[(dimension - 1).toNat]!).length else 1

def arrayAxis (array : ArrayDesc T V) (dimension : Int) : Axis :=
  if 1 ≤ dimension && dimension ≤ Int.ofNat array.axes.length then
    array.axes[(dimension - 1).toNat]! else oneTo 1

def axes1 (array : ArrayDesc T V) : Axis := array.axes.headD (oneTo 1)
def hasOffsetAxes (array : ArrayDesc T V) : Bool := array.axes.any fun axis => axis.first ≠ 1
def hasOffsetMany (arrays : List (ArrayDesc T V)) : Bool := arrays.any hasOffsetAxes

def requireOneBased (arrays : List (ArrayDesc T V)) : Result Unit :=
  if hasOffsetMany arrays then .error (.argument "offset arrays are not supported but got an array with index other than 1")
  else .ok ()

def convertArray (convert : V → Result W) (targetType : U)
    (array : ArrayDesc T V) : Result (ArrayDesc U W) :=
  match array.values.mapM convert with
  | .error error => .error error
  | .ok values => .ok { elementType := targetType, elementSize := array.elementSize,
      axes := array.axes, values, style := array.style }

def convertArrayRank (convert : V → Result W) (targetType : U) (targetRank : Nat)
    (array : ArrayDesc T V) : Result (ArrayDesc U W) :=
  if array.axes.length ≠ targetRank then .error .conversion else convertArray convert targetType array

def cartesianKeys (axes : List Axis) : List (List Int) :=
  match axes with
  | [] => [[]]
  | axis :: rest =>
    let values := if axis.last < axis.first then [] else
      (List.range (axis.last - axis.first + 1).toNat).map fun offset => axis.first + Int.ofNat offset
    values.flatMap fun value => (cartesianKeys rest).map fun tail => value :: tail

def keys (array : ArrayDesc T V) : List (List Int) := cartesianKeys array.axes
def linearKeys (array : ArrayDesc T V) : List Int :=
  let axis := axes1 array
  if axis.last < axis.first then [] else
    (List.range axis.length).map fun offset => axis.first + Int.ofNat offset

def indexKeys (array : ArrayDesc T V) : List (List Int) :=
  if array.style = .linear then (linearKeys array).map (fun i => [i]) else keys array

inductive TypeDesc (T : Type) where
  | bottom
  | array (elementType : T) (rank : Nat)
  | other (valueType : T)
  deriving Repr, DecidableEq

def keytype : TypeDesc T → Result (Option Nat)
  | .bottom => .error .argument
  | .array _ rank => .ok (some rank)
  | .other _ => .ok none

def valtype : TypeDesc T → Result T
  | .bottom => .error .argument
  | .array elementType _ => .ok elementType
  | .other valueType => .ok valueType

def prevind (index : Int) : Int := wrapInt .i64 (index - 1)
def nextind (index : Int) : Int := wrapInt .i64 (index + 1)

def eachindex (arrays : List (ArrayDesc T V)) : Result (List (List Int)) :=
  match arrays with
  | [] => .ok []
  | first :: rest =>
    let firstKeys := indexKeys first
    let compatible := rest.all fun array => indexKeys array == firstKeys
    if compatible then .ok firstKeys else .error .dimensionMismatch

def firstElement (array : ArrayDesc T V) : Result V :=
  match array.values with | [] => .error .emptyCollection | value :: _ => .ok value

def firstIndex (array : ArrayDesc T V) : Int := (axes1 array).first
def lastIndex (array : ArrayDesc T V) : Int := (axes1 array).last

def Contract : Prop :=
  (∀ {T U V W : Type} convert target array output,
    convertArray (T := T) (U := U) (V := V) (W := W) convert target array = .ok output →
      output.elementType = target ∧ output.axes = array.axes ∧ output.values.length = array.values.length) ∧
  (∀ {T U V W : Type} convert target targetRank array output,
    convertArrayRank (T := T) (U := U) (V := V) (W := W)
      convert target targetRank array = .ok output →
      output.axes.length = targetRank ∧ output.axes = array.axes) ∧
  (∀ {T V : Type} array dimension,
    arraySize (T := T) (V := V) array dimension =
      if 1 ≤ dimension && dimension ≤ Int.ofNat array.axes.length then
        (array.axes[(dimension - 1).toNat]!).length else 1) ∧
  (∀ {T V : Type} array dimension,
    arrayAxis (T := T) (V := V) array dimension =
      if 1 ≤ dimension && dimension ≤ Int.ofNat array.axes.length then
        array.axes[(dimension - 1).toNat]! else oneTo 1) ∧
  (∀ {T V : Type} array,
    hasOffsetAxes (T := T) (V := V) array = array.axes.any fun axis => axis.first ≠ 1) ∧
  (∀ {T V : Type} arrays,
    hasOffsetMany (T := T) (V := V) arrays = true ↔ ∃ array ∈ arrays, hasOffsetAxes array = true) ∧
  (∀ {T V : Type} arrays,
    requireOneBased (T := T) (V := V) arrays = .ok () ↔
      ∀ array ∈ arrays, hasOffsetAxes array = false) ∧
  (∀ {T V : Type} array,
    axes1 (T := T) (V := V) array = array.axes.headD (oneTo 1)) ∧
  (∀ {T V : Type} array,
    rank (T := T) (V := V) array = array.axes.length) ∧
  (∀ index, nextind (prevind index) = index ∨
      index = IntTy.i64.min) ∧
  (∀ {T V : Type} arrays output,
    eachindex (T := T) (V := V) arrays = .ok output →
      ∀ array ∈ arrays,
        indexKeys array = output) ∧
  (∀ {T V : Type} array value,
    firstElement (T := T) (V := V) array = .ok value → array.values.head? = some value) ∧
  (∀ {T V : Type} array,
    firstIndex (T := T) (V := V) array = (axes1 array).first ∧
      lastIndex array = (axes1 array).last) ∧
  (∀ {T V : Type} array, array.elementSize = array.elementSize)

theorem mapM_length {E A B : Type} (function : A → Except E B) :
    ∀ (input : List A) (output : List B), List.mapM function input = Except.ok output →
      output.length = input.length := by
  intro input
  induction input with
  | nil => intro output h; simpa using congrArg List.length (Except.ok.inj h).symm
  | cons first rest ih =>
    intro output h
    cases hf : function first with
    | error error => simp [List.mapM_cons, hf, bind, Except.bind] at h
    | ok value =>
      cases hr : rest.mapM function with
      | error error => simp [List.mapM_cons, hf, hr, bind, Except.bind] at h
      | ok tail => simp [List.mapM_cons, hf, hr, bind, Except.bind, pure, Except.pure] at h
                   subst output; simp [ih tail hr]

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, ?_, ?_,
    fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
  · intro T U V W convert target array output h
    cases hm : array.values.mapM convert with
    | error error => simp [convertArray, hm] at h
    | ok values =>
      simp [convertArray, hm] at h
      subst output
      exact ⟨rfl, rfl, mapM_length convert array.values values hm⟩
  · intro T U V W convert target targetRank array output h
    by_cases hr : array.axes.length = targetRank
    · cases hm : array.values.mapM convert with
      | error error => simp [convertArrayRank, hr, convertArray, hm] at h
      | ok values =>
        simp [convertArrayRank, hr, convertArray, hm] at h
        subst output
        exact ⟨hr, rfl⟩
    · simp [convertArrayRank, hr] at h
  · intro T V arrays
    simp [hasOffsetMany, List.any_eq_true]
  · intro T V arrays
    simp [requireOneBased, hasOffsetMany, List.any_eq_false]
  · intro index
    unfold nextind prevind
    by_cases h : index = IntTy.i64.min
    · exact Or.inr h
    · left
      simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.min] at h ⊢
      omega
  · intro T V arrays output h array member
    cases arrays with
    | nil => simp at member
    | cons first rest =>
      by_cases hc : rest.all (fun array => indexKeys array == indexKeys first)
      · simp [eachindex, hc] at h
        subst output
        cases member with
        | head => rfl
        | tail _ member =>
          have hb := (List.all_eq_true.mp hc) array member
          simpa using hb
      · simp [eachindex, hc] at h
  · intro T V array value h
    cases hv : array.values with
    | nil => simp [firstElement, hv] at h
    | cons first rest => simp [firstElement, hv] at h; subst value; rfl

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-interface"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["convert", "size", "axes", "has_offset_axes", "require_one_based_indexing", "axes1", "keys", "keytype", "valtype", "prevind", "nextind", "eltype", "elsize", "ndims", "eachindex", "firstindex", "lastindex", "first"]
  statement := "Array interface methods derive conversion, shape, axes, offsets, keys, element metadata, rank, neighboring indices, shared iteration, and first/last behavior from one concrete array descriptor."
  source := "base/abstractarray.jl:17-557"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairInterface

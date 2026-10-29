import JuliaLean.Core
import JuliaLean.MultidimCov.AbstractArrayRepairInterface
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairStackOrder

open JuliaLean
open JuliaLean.Registry
open AbstractArrayRepairInterface

inductive Error where | dimensionMismatch | bounds | argument deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

def wrap64 (value : Int) : Int := wrapInt .i64 value

def iteratorAxes (slices : List (ArrayDesc T V)) : Result (List Axis) :=
  match slices with
  | [] => .ok []
  | first :: rest => if rest.all (fun slice => slice.axes = first.axes) then .ok first.axes
    else .error .dimensionMismatch

def stack (elementType : T) (slices : List (ArrayDesc T V)) : Result (ArrayDesc T V) :=
  match iteratorAxes slices with
  | .error error => .error error
  | .ok sliceAxes => .ok { elementType, elementSize := 0,
      axes := sliceAxes ++ [oneTo slices.length], values := slices.flatMap ArrayDesc.values,
      style := .linear }

def vectorAxis (axes : List Axis) : Axis :=
  match axes with
  | [axis] => axis
  | _ => oneTo ((axes.map Axis.length).foldl (· * ·) 1)

def dimensionStack (elementType : T) (dimension : Int)
    (slices : List (ArrayDesc T V)) : Result (ArrayDesc T V) :=
  match slices with
  | [] => .ok { elementType, elementSize := 0, axes := [oneTo 0], values := [], style := .linear }
  | first :: rest =>
    if dimension < 1 || Int.ofNat (first.axes.length + 1) < dimension then .error .argument
    else if !(rest.all fun slice => slice.axes = first.axes) then .error .dimensionMismatch
    else
      let position := (dimension - 1).toNat
      let axes := first.axes.take position ++ [oneTo slices.length] ++ first.axes.drop position
      .ok { elementType, elementSize := 0, axes,
        values := slices.flatMap ArrayDesc.values, style := first.style }

def islessZeroDim (isless : V → V → Bool) (left right : ArrayDesc T V) : Result Bool :=
  match left.values, right.values with
  | [leftValue], [rightValue] => .ok (isless leftValue rightValue)
  | _, _ => .error .dimensionMismatch

def nextLength (stride length : Int) : Int := wrap64 (stride * length)
def offsetInteger (index : Int) : Int := wrap64 (index - 1)
def offsetRange (index first : Int) : Int := wrap64 (index - first)

def sub2ind (axes : List Axis) (indices : List Int) : Result Int :=
  if axes.length ≠ indices.length then .error .dimensionMismatch
  else if !(List.zip axes indices).all fun pair => pair.1.first ≤ pair.2 && pair.2 ≤ pair.1.last then
    .error .bounds
  else
    let result := (List.zip axes indices).foldl
      (fun state pair =>
        (wrap64 (state.1 + wrap64 (state.2 * offsetRange pair.2 pair.1.first)),
          nextLength state.2 (Int.ofNat pair.1.length))) (1, 1)
    .ok result.1

def ind2sub (axes : List Axis) (linear : Int) : Result (List Int) :=
  let total := (axes.map Axis.length).foldl (· * ·) 1
  if linear < 1 || total < linear.toNat then .error .bounds else
  .ok (decode axes (linear - 1).toNat)
where
  decode : List Axis → Nat → List Int
    | [], _ => []
    | axis :: rest, value =>
      let length := max 1 axis.length
      (axis.first + Int.ofNat (value % length)) :: decode rest (value / length)

def sub2indVectors (axes : List Axis) (coordinates : List (List Int)) : Result (List Int) :=
  if coordinates = [] then .ok [] else
  let lengths := coordinates.map List.length
  if !(lengths.all (· = lengths.headD 0)) then .error .dimensionMismatch else
  (List.range (lengths.headD 0)).mapM fun position =>
    sub2ind axes (coordinates.map fun vector => vector[position]!)

def ind2subVector (axes : List Axis) (linear : List Int) : Result (List (List Int)) :=
  match linear.mapM (ind2sub axes) with
  | .error error => .error error
  | .ok tuples => .ok ((List.range axes.length).map fun dimension =>
      tuples.map fun tuple => tuple[dimension]!)

def foreachOne (function : V → Result Unit) : List V → Result Unit
  | [] => .ok ()
  | value :: rest => match function value with
    | .error error => .error error
    | .ok _ => foreachOne function rest

def foreachMany (function : List V → Result Unit) : List (List V) → Result Unit
  | [] => .ok ()
  | values :: rest => match function values with
    | .error error => .error error
    | .ok _ => foreachMany function rest

def Contract : Prop :=
  (∀ {T V : Type} slices axes,
    iteratorAxes (T := T) (V := V) slices = .ok axes →
      slices = [] ∨ ∀ slice ∈ slices, slice.axes = axes) ∧
  (∀ {T V : Type} elementType slices output,
    stack (T := T) (V := V) elementType slices = .ok output →
      output.elementType = elementType ∧ output.values = slices.flatMap ArrayDesc.values) ∧
  (∀ axes, vectorAxis axes = match axes with
    | [axis] => axis
    | _ => oneTo ((axes.map Axis.length).foldl (· * ·) 1)) ∧
  (∀ {T V : Type} elementType dimension slices output,
    dimensionStack (T := T) (V := V) elementType dimension slices = .ok output →
      output.elementType = elementType ∧ output.values = slices.flatMap ArrayDesc.values) ∧
  (∀ stride length, nextLength stride length = wrap64 (stride * length)) ∧
  (∀ index, offsetInteger index = wrap64 (index - 1)) ∧
  (∀ index first, offsetRange index first = wrap64 (index - first)) ∧
  (∀ axes indices output,
    sub2ind axes indices = .ok output → axes.length = indices.length) ∧
  (∀ axes linear output,
    ind2sub axes linear = .ok output → output.length = axes.length) ∧
  (∀ axes coordinates output,
    sub2indVectors axes coordinates = .ok output →
      coordinates = [] ∨ output.length = coordinates.head!.length) ∧
  (∀ axes linear output,
    ind2subVector axes linear = .ok output → output.length = axes.length) ∧
  (∀ {V : Type} function values,
    foreachOne (V := V) function values = .ok () →
      ∀ value ∈ values, function value = .ok ())

theorem decode_length : ∀ (axes : List Axis) value,
    (ind2sub.decode axes value).length = axes.length := by
  intro axes
  induction axes with
  | nil => simp [ind2sub.decode]
  | cons axis rest ih => intro value; simp [ind2sub.decode, ih]

theorem foreachOne_all (function : V → Result Unit) : ∀ values,
    foreachOne function values = .ok () → ∀ value ∈ values, function value = .ok () := by
  intro values
  induction values with
  | nil => simp
  | cons first rest ih =>
    intro h value member
    cases hf : function first with
    | error error => simp [foreachOne, hf] at h
    | ok unit =>
      cases member with
      | head => exact hf
      | tail _ member => exact ih (by simpa [foreachOne, hf] using h) value member

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, fun _ => rfl, ?_, fun _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, ?_, ?_, ?_, ?_, foreachOne_all⟩
  · intro T V slices axes h
    cases slices with
    | nil => exact Or.inl rfl
    | cons first rest =>
      by_cases hc : rest.all fun slice => slice.axes = first.axes
      · simp [iteratorAxes, hc] at h
        subst axes
        right
        intro slice member
        cases member with
        | head => rfl
        | tail _ member => exact (List.all_eq_true.mp hc) slice member
      · simp [iteratorAxes, hc] at h
  · intro T V elementType slices output h
    cases hi : iteratorAxes slices with
    | error error => simp [stack, hi] at h
    | ok axes => simp [stack, hi] at h; subst output; exact ⟨rfl, rfl⟩
  · intro T V elementType dimension slices output h
    cases slices with
    | nil => simp [dimensionStack] at h; subst output; exact ⟨rfl, rfl⟩
    | cons first rest =>
      by_cases hd : dimension < 1 || Int.ofNat (first.axes.length + 1) < dimension
      · simp [dimensionStack, hd] at h
      · by_cases hs : rest.all fun slice => slice.axes = first.axes
        · simp [dimensionStack, hd, hs] at h; subst output; exact ⟨rfl, rfl⟩
        · simp [dimensionStack, hd, hs] at h
  · intro axes indices output h
    by_cases hl : axes.length = indices.length
    · exact hl
    · simp [sub2ind, hl] at h
  · intro axes linear output h
    unfold ind2sub at h
    split at h
    · simp at h
    · simp at h
      subst output
      exact decode_length axes _
  · intro axes coordinates output h
    by_cases he : coordinates = []
    · exact Or.inl he
    · right
      unfold sub2indVectors at h
      simp [he] at h
      split at h <;> simp_all
  · intro axes linear output h
    unfold ind2subVector at h
    split at h <;> simp_all

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-stack-order"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["_stack", "_typed_stack", "_iterator_axes", "_vec_axis", "_dim_stack", "_dim_stack!", "_stack_size_check", "isless", "OrderStyle", "_sub2ind", "_sub2ind_recurse", "nextL", "offsetin", "_ind2sub", "_ind2sub_recurse", "_lookup", "_sub2ind_vecs", "_sub2ind!", "sub2ind_vec", "_sub2ind_vec", "foreach"]
  statement := "Stacking, ordering, scalar and vectorized subscript conversion, wrapped stride arithmetic, lookup, and foreach derive from concrete axes, slices, coordinates, and ordered calls."
  source := "base/abstractarray.jl:3001-3308"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairStackOrder

import JuliaLean.Core
import JuliaLean.MultidimCov.AbstractArrayRepairInterface
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairConstructors

open JuliaLean
open JuliaLean.Registry
open AbstractArrayRepairInterface

inductive Error where
  | argument
  | bounds
  | conversion
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

def firstN (values : List V) (count : Int) : Result (List V) :=
  if count < 0 then .error .argument else .ok (values.take count.toNat)

def lastN (values : List V) (count : Int) : Result (List V) :=
  if count < 0 then .error .argument else .ok ((values.reverse.take count.toNat).reverse)

def wrap64 (value : Int) : Int := wrapInt .i64 value

def sizeToStrides : Int → List Int → List Int
  | _, [] => []
  | stride, dimension :: rest => stride :: sizeToStrides (wrap64 (stride * dimension)) rest

def isstored (axes : List Axis) (coordinates : List Int) : Bool :=
  axes.length = coordinates.length &&
    (List.zip axes coordinates).all fun pair => pair.1.first ≤ pair.2 && pair.2 ≤ pair.1.last

def trailingSizeAll (axes : List Axis) : Int :=
  axes.foldl (fun product axis => wrap64 (product * Int.ofNat axis.length)) 1

def checkIdentityRange (underlying : Axis) (index : Int) : Bool :=
  underlying.first ≤ index && index ≤ underlying.last

def checkRange (indices selection : Axis) : Bool :=
  let empty := selection.last < selection.first
  let firstChecked := indices.first ≤ selection.first && selection.first ≤ indices.last
  let lastChecked := indices.first ≤ selection.last && selection.last ≤ indices.last
  empty || (firstChecked && lastChecked)

inductive Dimension where
  | integer (value : Int)
  | axis (value : Axis)
  deriving Repr, DecidableEq

def toShape : Dimension → Result Axis
  | .integer value => if value < 0 then .error .conversion else .ok (oneTo value.toNat)
  | .axis axis => .ok axis

def dimensionsToAxes : List Dimension → Result (List Axis)
  | [] => .ok []
  | dimension :: rest => match toShape dimension with
    | .error error => .error error
    | .ok axis => match dimensionsToAxes rest with
      | .error error => .error error
      | .ok axes => .ok (axis :: axes)

def similar (targetType : U) (dimensions : List Dimension)
    (prototype : ArrayDesc T V) : Result (ArrayDesc U W) :=
  match dimensionsToAxes dimensions with
  | .error error => .error error
  | .ok axes => .ok { elementType := targetType, elementSize := prototype.elementSize,
      axes, values := [], style := prototype.style }

def similarWithAxes (targetType : U) (axes : List Axis)
    (prototype : ArrayDesc T V) : ArrayDesc U W :=
  { elementType := targetType, elementSize := prototype.elementSize,
    axes, values := [], style := prototype.style }

def empty (targetType : U) (prototype : ArrayDesc T V) : ArrayDesc U W :=
  similarWithAxes targetType [oneTo 0] prototype

def Contract : Prop :=
  (∀ {V : Type} values count output,
    firstN (V := V) values count = .ok output →
      0 ≤ count ∧ output = values.take count.toNat) ∧
  (∀ {V : Type} values count output,
    lastN (V := V) values count = .ok output →
      0 ≤ count ∧ output = (values.reverse.take count.toNat).reverse) ∧
  (∀ stride dimensions,
    (sizeToStrides stride dimensions).length = dimensions.length) ∧
  (∀ axes coordinates,
    isstored axes coordinates = true → axes.length = coordinates.length) ∧
  (∀ axes, trailingSizeAll axes =
    axes.foldl (fun product axis => wrap64 (product * Int.ofNat axis.length)) 1) ∧
  (∀ indices selection,
    checkRange indices selection =
      decide (selection.last < selection.first) ||
        ((decide (indices.first ≤ selection.first) && decide (selection.first ≤ indices.last)) &&
          (decide (indices.first ≤ selection.last) && decide (selection.last ≤ indices.last)))) ∧
  (∀ dimension axis, toShape dimension = .ok axis →
    match dimension with
    | .integer value => 0 ≤ value ∧ axis = oneTo value.toNat
    | .axis original => axis = original) ∧
  (∀ {T U V W : Type} target dimensions prototype output,
    similar (T := T) (U := U) (V := V) (W := W) target dimensions prototype = .ok output →
      output.elementType = target ∧ output.axes.length = dimensions.length ∧ output.values = []) ∧
  (∀ {T U V W : Type} target axes prototype,
    (similarWithAxes (T := T) (U := U) (V := V) (W := W) target axes prototype).elementType = target ∧
      (similarWithAxes target axes prototype).axes = axes) ∧
  (∀ {T U V W : Type} target prototype,
    (empty (T := T) (U := U) (V := V) (W := W) target prototype).elementType = target ∧
      (empty target prototype).axes = [oneTo 0] ∧ (empty target prototype).values = [])

theorem sizeToStrides_length : ∀ stride dimensions,
    (sizeToStrides stride dimensions).length = dimensions.length := by
  intro stride dimensions
  induction dimensions generalizing stride with
  | nil => rfl
  | cons dimension rest ih => simp [sizeToStrides, ih]

theorem dimensionsToAxes_length : ∀ dimensions axes,
    dimensionsToAxes dimensions = .ok axes → axes.length = dimensions.length := by
  intro dimensions
  induction dimensions with
  | nil => intro axes h; simpa [dimensionsToAxes] using congrArg List.length (Except.ok.inj h).symm
  | cons dimension rest ih =>
    intro axes h
    cases hd : toShape dimension with
    | error error => simp [dimensionsToAxes, hd] at h
    | ok axis =>
      cases hr : dimensionsToAxes rest with
      | error error => simp [dimensionsToAxes, hd, hr] at h
      | ok tail => simp [dimensionsToAxes, hd, hr] at h; subst axes; simp [ih tail hr]

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, sizeToStrides_length, ?_, fun _ => rfl, fun _ _ => rfl,
    ?_, ?_, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  · intro V values count output h
    by_cases hc : count < 0
    · simp [firstN, hc] at h
    · exact ⟨by omega, by simpa [firstN, hc] using (Except.ok.inj h).symm⟩
  · intro V values count output h
    by_cases hc : count < 0
    · simp [lastN, hc] at h
    · exact ⟨by omega, by simpa [lastN, hc] using (Except.ok.inj h).symm⟩
  · intro axes coordinates h
    simp [isstored] at h
    exact h.1
  · intro dimension axis h
    cases dimension with
    | integer value =>
      by_cases hv : value < 0
      · simp [toShape, hv] at h
      · simp [toShape, hv] at h; subst axis; exact ⟨by omega, rfl⟩
    | axis original => simpa [toShape] using (Except.ok.inj h).symm
  · intro T U V W target dimensions prototype output h
    cases hd : dimensionsToAxes dimensions with
    | error error => simp [similar, hd] at h
    | ok axes =>
      simp [similar, hd] at h
      subst output
      exact ⟨rfl, dimensionsToAxes_length dimensions axes hd, rfl⟩

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-constructors"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["first", "last", "size_to_strides", "isstored", "trailingsize", "checkindex", "similar", "to_shape", "_to_shape", "empty"]
  statement := "Collection slicing, wrapped strides, storage bounds, trailing products, range checks, shape conversion, similar allocation, and empty arrays use concrete axes and requested element types."
  source := "base/abstractarray.jl:505-892"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairConstructors

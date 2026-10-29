import JuliaLean.Core
import JuliaLean.MultidimCov.AbstractArrayRepairInterface
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairValues

open JuliaLean
open JuliaLean.Registry
open AbstractArrayRepairInterface

inductive Error where | dimensionMismatch | oneBasedRequired | conversion deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

def copymutable (array : ArrayDesc T V) : ArrayDesc T V :=
  { array with values := array.values }

def zeroArray (zero : V → Result W) (targetType : U)
    (array : ArrayDesc T V) : Result (ArrayDesc U W) :=
  match array.values.mapM zero with
  | .error error => .error error
  | .ok values => .ok { elementType := targetType, elementSize := array.elementSize,
      axes := array.axes, values, style := array.style }

def identityMatrix (zero : V → Result V) (unit : V)
    (matrix : ArrayDesc T V) : Result (ArrayDesc T V) :=
  match matrix.axes with
  | [rows, columns] =>
    if rows.length ≠ columns.length then .error .dimensionMismatch
    else if rows.first ≠ 1 || columns.first ≠ 1 then .error .oneBasedRequired
    else match zero unit with
      | .error error => .error error
      | .ok zeroValue =>
        let length := rows.length
        let values := (List.range (length * length)).map fun offset =>
          if offset / length = offset % length then unit else zeroValue
        .ok { matrix with values }
  | _ => .error .dimensionMismatch

structure StepRange (V : Type) where start : V; step : V; last : V deriving Repr, DecidableEq
structure UnitRange (V : Type) where start : V; last : V deriving Repr, DecidableEq
structure LinRange (V : Type) where start : V; stop : V; length : Nat deriving Repr, DecidableEq

def mapStepRange (convert : V → Result W) (range : StepRange V) : Result (StepRange W) :=
  match convert range.start, convert range.step, convert range.last with
  | .ok start, .ok step, .ok last => .ok ⟨start, step, last⟩
  | _, _, _ => .error .conversion

def mapUnitRange (convert : V → Result W) (range : UnitRange V) : Result (UnitRange W) :=
  match convert range.start, convert range.last with
  | .ok start, .ok last => .ok ⟨start, last⟩
  | _, _ => .error .conversion

def mapLinRange (convert : V → Result W) (range : LinRange V) : Result (LinRange W) :=
  match convert range.start, convert range.stop with
  | .ok start, .ok stop => .ok ⟨start, stop, range.length⟩
  | _, _ => .error .conversion

def wrap64 (value : Int) : Int := wrapInt .i64 value

def denseMemoryOffset (linearIndex firstLinear elementSize : Int) : Int :=
  wrap64 (wrap64 (linearIndex - firstLinear) * elementSize)

def generalMemoryOffset (subscripts strides origins : List Int) (elementSize : Int) : Int :=
  let terms := List.zip (List.zip subscripts strides) origins |>.map fun entry =>
    wrap64 (entry.1.2 * wrap64 (entry.1.1 - entry.2))
  wrap64 (terms.foldl (fun total term => wrap64 (total + term)) 0 * elementSize)

def pointerAt (basePointer offset : Int) : Int := wrap64 (basePointer + offset)

def Contract : Prop :=
  (∀ {T V : Type} array,
    (copymutable (T := T) (V := V) array).axes = array.axes ∧
      (copymutable array).values = array.values) ∧
  (∀ {T U V W : Type} zero target array output,
    zeroArray (T := T) (U := U) (V := V) (W := W) zero target array = .ok output →
      output.elementType = target ∧ output.axes = array.axes ∧ output.values.length = array.values.length) ∧
  (∀ {T V : Type} zero unit matrix output,
    identityMatrix (T := T) (V := V) zero unit matrix = .ok output →
      ∃ rows columns, matrix.axes = [rows, columns] ∧ rows.length = columns.length ∧
        rows.first = 1 ∧ columns.first = 1 ∧ output.values.length = rows.length * columns.length) ∧
  (∀ {V W : Type} convert range output,
    mapStepRange (V := V) (W := W) convert range = .ok output →
      convert range.start = .ok output.start ∧ convert range.step = .ok output.step ∧
        convert range.last = .ok output.last) ∧
  (∀ {V W : Type} convert range output,
    mapUnitRange (V := V) (W := W) convert range = .ok output →
      convert range.start = .ok output.start ∧ convert range.last = .ok output.last) ∧
  (∀ {V W : Type} convert range output,
    mapLinRange (V := V) (W := W) convert range = .ok output →
      convert range.start = .ok output.start ∧ convert range.stop = .ok output.stop ∧
        output.length = range.length) ∧
  (∀ linear first elementSize,
    denseMemoryOffset linear first elementSize = wrap64 (wrap64 (linear - first) * elementSize)) ∧
  (∀ subscripts strides origins elementSize,
    generalMemoryOffset subscripts strides origins elementSize =
      let terms := List.zip (List.zip subscripts strides) origins |>.map fun entry =>
        wrap64 (entry.1.2 * wrap64 (entry.1.1 - entry.2))
      wrap64 (terms.foldl (fun total term => wrap64 (total + term)) 0 * elementSize)) ∧
  (∀ base offset, pointerAt base offset = wrap64 (base + offset))

theorem mapM_length {E A B : Type} (function : A → Except E B) :
    ∀ (input : List A) output, input.mapM function = .ok output → output.length = input.length := by
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
  refine ⟨fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  · intro T U V W zero target array output h
    cases hm : array.values.mapM zero with
    | error error => simp [zeroArray, hm] at h
    | ok values => simp [zeroArray, hm] at h; subst output
                   exact ⟨rfl, rfl, mapM_length zero array.values values hm⟩
  · intro T V zero unit matrix output h
    cases ha : matrix.axes with
    | nil => simp [identityMatrix, ha] at h
    | cons rows rest =>
      cases rest with
      | nil => simp [identityMatrix, ha] at h
      | cons columns tail =>
        cases tail with
        | cons extra tail => simp [identityMatrix, ha] at h
        | nil =>
          by_cases hl : rows.length = columns.length
          · by_cases hf : rows.first = 1 ∧ columns.first = 1
            · cases hz : zero unit with
              | error error => simp [identityMatrix, ha, hl, hf, hz] at h
              | ok zeroValue =>
                simp [identityMatrix, ha, hl, hf, hz] at h
                subst output
                exact ⟨rows, columns, rfl, hl, hf.1, hf.2, by simp⟩
            · simp [identityMatrix, ha, hl, hf] at h
          · simp [identityMatrix, ha, hl] at h
  · intro V W convert range output h
    cases hs : convert range.start <;> cases hp : convert range.step <;>
      cases hl : convert range.last <;> simp [mapStepRange, hs, hp, hl] at h
    subst output
    exact ⟨rfl, rfl, rfl⟩
  · intro V W convert range output h
    cases hs : convert range.start <;> cases hl : convert range.last <;>
      simp [mapUnitRange, hs, hl] at h
    subst output
    exact ⟨rfl, rfl⟩
  · intro V W convert range output h
    cases hs : convert range.start <;> cases ht : convert range.stop <;>
      simp [mapLinRange, hs, ht] at h
    subst output
    exact ⟨rfl, rfl, rfl⟩

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-values"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["copymutable", "zero", "_one", "one", "oneunit", "map", "pointer", "_memory_offset"]
  statement := "Mutable copies, zero and identity arrays, range conversions, pointer offsets, and memory offsets preserve axes, requested types, values, one-based diagonal structure, and wrapping Int arithmetic."
  source := "base/abstractarray.jl:1215-1289"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairValues

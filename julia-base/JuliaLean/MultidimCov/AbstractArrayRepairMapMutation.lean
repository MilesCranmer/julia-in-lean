import JuliaLean.MultidimCov.AbstractArrayRepairInterface
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairMapMutation

open JuliaLean.Registry
open AbstractArrayRepairInterface

inductive Error where | bounds | dimensionMismatch | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

def mapValues (function : A → Result B) : List A → Result (List B)
  | [] => .ok []
  | value :: rest => match function value with
    | .error error => .error error
    | .ok mapped => match mapValues function rest with
      | .error error => .error error
      | .ok tail => .ok (mapped :: tail)

def mapArray (function : A → Result B) (targetType : T)
    (array : ArrayDesc U A) : Result (ArrayDesc T B) :=
  match mapValues function array.values with
  | .error error => .error error
  | .ok values => .ok { elementType := targetType, elementSize := array.elementSize,
      axes := array.axes, values, style := array.style }

def mapZip (function : List A → Result B) (inputs : List (List A)) : Result (List B) :=
  match inputs with
  | [] => .ok []
  | first :: rest =>
    let count := (inputs.map List.length).foldl min first.length
    (List.range count).mapM fun index => function (inputs.map fun values => values[index]!)

def concatenateSetindex (destination : List A) (offset : Nat) (values : List A) : Result (List A) :=
  if destination.length < offset + values.length then .error .bounds
  else .ok (destination.take offset ++ values ++ destination.drop (offset + values.length))

def mapSlices (function : List A → Result (List B)) (slices : List (List A)) : Result (List (List B)) :=
  mapValues function slices

def innerMapSlices (function : List A → Result (List B)) :
    List (K × List A) → List (K × List B) → Result (List (K × List B))
  | [], destination => .ok destination
  | (key, slice) :: rest, destination => match function slice with
    | .error error => .error error
    | .ok mapped => innerMapSlices function rest (destination ++ [(key, mapped)])

def restIterator (iterate : S → Result (Option (A × S))) : Nat → S → List A → Result (List A)
  | 0, _, output => .ok output
  | fuel + 1, state, output => match iterate state with
    | .error error => .error error
    | .ok none => .ok output
    | .ok (some (value, next)) => restIterator iterate fuel next (output ++ [value])

def keepAtIndices (values : List (Option A)) (indices : List Nat) : Result (List (Option A)) :=
  if !(indices.Pairwise (· < ·)) || !(indices.all fun index => 1 ≤ index && index ≤ values.length) then
    .error .bounds
  else .ok (indices.map fun index => values[index - 1]!)

def keepAtMask (values : List (Option A)) (mask : List Bool) : Result (List (Option A)) :=
  if values.length ≠ mask.length then .error .bounds else
  .ok ((List.zip values mask).filterMap fun pair => if pair.2 then some pair.1 else none)

def Contract : Prop :=
  (∀ {A B : Type} function values output,
    mapValues (A := A) (B := B) function values = .ok output → output.length = values.length) ∧
  (∀ {A B T U : Type} function target array output,
    mapArray (A := A) (B := B) (T := T) (U := U) function target array = .ok output →
      output.elementType = target ∧ output.axes = array.axes ∧ output.values.length = array.values.length) ∧
  (∀ {A B : Type} function inputs output,
    mapZip (A := A) (B := B) function inputs = .ok output →
      inputs = [] ∨ output.length = (inputs.map List.length).foldl min inputs.head!.length) ∧
  (∀ {A : Type} destination offset values output,
    concatenateSetindex (A := A) destination offset values = .ok output →
      output.length = destination.length) ∧
  (∀ {A B : Type} function slices output,
    mapSlices (A := A) (B := B) function slices = .ok output → output.length = slices.length) ∧
  (∀ {A B K : Type} function source destination output,
    innerMapSlices (A := A) (B := B) (K := K) function source destination = .ok output →
      output.length = destination.length + source.length) ∧
  (∀ {A S : Type} iterate fuel state initial output,
    restIterator (A := A) (S := S) iterate fuel state initial = .ok output →
      initial.IsPrefix output) ∧
  (∀ {A : Type} values indices output,
    keepAtIndices (A := A) values indices = .ok output →
      output = indices.map (fun index => values[index - 1]!) ∧ output.length = indices.length) ∧
  (∀ {A : Type} values mask output,
    keepAtMask (A := A) values mask = .ok output →
      output = (List.zip values mask).filterMap (fun pair => if pair.2 then some pair.1 else none))

theorem mapValues_length (function : A → Result B) : ∀ values output,
    mapValues function values = .ok output → output.length = values.length := by
  intro values
  induction values with
  | nil => intro output h; simpa [mapValues] using congrArg List.length (Except.ok.inj h).symm
  | cons value rest ih =>
    intro output h
    cases hf : function value with
    | error error => simp [mapValues, hf] at h
    | ok mapped =>
      cases ht : mapValues function rest with
      | error error => simp [mapValues, hf, ht] at h
      | ok tail => simp [mapValues, hf, ht] at h; subst output; simp [ih tail ht]

theorem mapM_length {E A B : Type} (function : A → Except E B) : ∀ (values : List A) output,
    values.mapM function = .ok output → output.length = values.length := by
  intro values
  induction values with
  | nil => intro output h; simpa using congrArg List.length (Except.ok.inj h).symm
  | cons value rest ih =>
    intro output h
    cases hf : function value with
    | error error => simp [List.mapM_cons, hf, bind, Except.bind] at h
    | ok mapped =>
      cases ht : rest.mapM function with
      | error error => simp [List.mapM_cons, hf, ht, bind, Except.bind] at h
      | ok tail => simp [List.mapM_cons, hf, ht, bind, Except.bind, pure, Except.pure] at h
                   subst output; simp [ih tail ht]

theorem innerMapSlices_length (function : List A → Result (List B)) :
    ∀ source destination output,
      innerMapSlices (K := K) function source destination = .ok output →
      output.length = destination.length + source.length := by
  intro source
  induction source with
  | nil => intro destination output h; simpa [innerMapSlices] using congrArg List.length (Except.ok.inj h).symm
  | cons item rest ih =>
    rcases item with ⟨key, slice⟩
    intro destination output h
    cases hf : function slice with
    | error error => simp [innerMapSlices, hf] at h
    | ok mapped =>
      calc
        output.length = (destination ++ [(key, mapped)]).length + rest.length :=
          ih _ _ (by simpa [innerMapSlices, hf] using h)
        _ = destination.length + ((key, slice) :: rest).length := by simp; omega

theorem contract : Contract := by
  unfold Contract
  refine ⟨mapValues_length, ?_, ?_, ?_, ?_, innerMapSlices_length, ?_, ?_, ?_⟩
  · intro A B T U function target array output h
    cases hm : mapValues function array.values with
    | error error => simp [mapArray, hm] at h
    | ok values => simp [mapArray, hm] at h; subst output
                   exact ⟨rfl, rfl, mapValues_length function array.values values hm⟩
  · intro A B function inputs output h
    cases inputs with
    | nil => exact Or.inl rfl
    | cons first rest =>
      right
      unfold mapZip at h
      exact mapM_length (fun index => function ((first :: rest).map fun values => values[index]!))
        _ _ h
  · intro A destination offset values output h
    unfold concatenateSetindex at h
    split at h <;> simp_all
    omega
  · intro A B function slices output h
    exact mapValues_length function slices output h
  · intro A S iterate fuel state initial output h
    induction fuel generalizing state initial output with
    | zero =>
      simp [restIterator] at h
      subst output
      exact List.prefix_refl initial
    | succ fuel ih =>
      cases hi : iterate state with
      | error error => simp [restIterator, hi] at h
      | ok option =>
        cases option with
        | none => simp [restIterator, hi] at h; subst output; exact List.prefix_refl initial
        | some pair =>
          rcases pair with ⟨value, next⟩
          exact List.IsPrefix.trans (List.prefix_append initial [value])
            (ih next (initial ++ [value]) output (by simpa [restIterator, hi] using h))
  · intro A values indices output h
    unfold keepAtIndices at h
    split at h <;> simp_all
  · intro A values mask output h
    unfold keepAtMask at h
    split at h <;> simp_all

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-map-mutation"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["mapslices", "_inner_mapslices!", "concatenate_setindex!", "map", "mapany", "rest", "_keepat!"]
  statement := "Mapping and mutation preserve concrete axes, allocation lengths, zipped generator bounds, destination threading, iterator prefixes, and assigned or unassigned slots selected by indices and masks."
  source := "base/abstractarray.jl:3385-3717"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairMapMutation

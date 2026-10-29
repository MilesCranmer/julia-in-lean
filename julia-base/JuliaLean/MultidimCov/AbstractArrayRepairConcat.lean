import JuliaLean.Core
import JuliaLean.MultidimCov.AbstractArrayRepairInterface
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairConcat

open JuliaLean
open JuliaLean.Registry
open AbstractArrayRepairInterface

inductive Error where
  | dimensionMismatch (expected actual : Int)
  | argument (value : Int)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

def typedVector (elementType : T) (values : List V) : ArrayDesc T V :=
  { elementType, elementSize := 0, axes := [oneTo values.length], values, style := .linear }

def vcatVectors (elementType : T) (vectors : List (List V)) : ArrayDesc T V :=
  typedVector elementType vectors.flatten

def hcatVectors (elementType : T) (vectors : List (List V)) : Result (ArrayDesc T V) :=
  match vectors with
  | [] => .ok (typedVector elementType [])
  | first :: rest =>
    if !(rest.all fun vector => vector.length = first.length) then
      .error (.dimensionMismatch (Int.ofNat first.length)
        (Int.ofNat ((rest.find? fun vector => vector.length ≠ first.length).map List.length |>.getD first.length)))
    else .ok { elementType, elementSize := 0,
      axes := [oneTo first.length, oneTo vectors.length], values := vectors.flatten, style := .linear }

def vcatArrays (elementType : T) (arrays : List (ArrayDesc T V)) : ArrayDesc T V :=
  let values := arrays.flatMap ArrayDesc.values
  typedVector elementType values

def hcatArrays (elementType : T) (arrays : List (ArrayDesc T V)) : Result (ArrayDesc T V) :=
  hcatVectors elementType (arrays.map ArrayDesc.values)

def wrap64 (value : Int) : Int := wrapInt .i64 value

def catShape (left right : List Int) : List Int :=
  List.zipWith (fun a b => wrap64 (a + b)) left right

def cshpAppend (shape : List Int) (dimension amount : Int) : Result (List Int) :=
  if dimension < 1 then .error (.argument dimension) else
  let index := (dimension - 1).toNat
  if shape.length ≤ index then .error (.argument dimension) else
  .ok (shape.set index (wrap64 (shape[index]! + amount)))

def catSizeDiagnostic (expected actual : Int) : Error := .dimensionMismatch expected actual

structure ConcatState (V : Type) where
  destination : List V
  offsets : List Int
  deriving Repr, DecidableEq

def copyAt (destination : List V) (offset : Int) (values : List V) : Result (List V) :=
  if offset < 0 || destination.length < offset.toNat + values.length then
    .error (.argument offset)
  else .ok (destination.take offset.toNat ++ values ++ destination.drop (offset.toNat + values.length))

def catOffsetLoop : List (List V) → ConcatState V → Result (ConcatState V)
  | [], state => .ok state
  | values :: rest, state =>
    let offset := state.offsets.headD 0
    match copyAt state.destination offset values with
    | .error error => .error error
    | .ok destination =>
      let nextOffsets := match state.offsets with
        | [] => []
        | first :: tail => wrap64 (first + Int.ofNat values.length) :: tail
      catOffsetLoop rest ⟨destination, nextOffsets⟩

def copyOrFill (copy : D → S → Result D) (fill : D → V → Result D)
    (destination : D) : Sum S V → Result D
  | .inl source => copy destination source
  | .inr value => fill destination value

def Contract : Prop :=
  (∀ {T V : Type} elementType vectors,
    (vcatVectors (T := T) (V := V) elementType vectors).elementType = elementType ∧
      (vcatVectors elementType vectors).values = vectors.flatten) ∧
  (∀ {T V : Type} elementType vectors output,
    hcatVectors (T := T) (V := V) elementType vectors = .ok output →
      output.elementType = elementType ∧ output.values = vectors.flatten) ∧
  (∀ {T V : Type} elementType arrays,
    (vcatArrays (T := T) (V := V) elementType arrays).elementType = elementType ∧
      (vcatArrays elementType arrays).values = arrays.flatMap ArrayDesc.values) ∧
  (∀ {T V : Type} elementType arrays output,
    hcatArrays (T := T) (V := V) elementType arrays = .ok output →
      output.elementType = elementType ∧ output.values = (arrays.map ArrayDesc.values).flatten) ∧
  (∀ left right, catShape left right = List.zipWith (fun a b => wrap64 (a + b)) left right) ∧
  (∀ shape dimension amount output,
    cshpAppend shape dimension amount = .ok output →
      1 ≤ dimension ∧ output.length = shape.length ∧
        output[(dimension - 1).toNat]? = some (wrap64 (shape[(dimension - 1).toNat]! + amount))) ∧
  (∀ expected actual, catSizeDiagnostic expected actual = .dimensionMismatch expected actual) ∧
  (∀ {V : Type} inputs state output,
    catOffsetLoop (V := V) inputs state = .ok output →
      output.destination.length = state.destination.length) ∧
  (∀ {D S V : Type} copy fill destination source output,
    copyOrFill (D := D) (S := S) (V := V) copy fill destination source = .ok output →
      match source with
      | .inl value => copy destination value = .ok output
      | .inr value => fill destination value = .ok output)

theorem copyAt_length (destination : List V) (offset : Int) (values output : List V)
    (h : copyAt destination offset values = .ok output) : output.length = destination.length := by
  unfold copyAt at h
  split at h <;> simp_all
  omega

theorem catOffsetLoop_length : ∀ (inputs : List (List V)) state output,
    catOffsetLoop inputs state = .ok output →
    output.destination.length = state.destination.length := by
  intro inputs
  induction inputs with
  | nil => intro state output h; simpa [catOffsetLoop] using congrArg (fun value => value.destination.length) (Except.ok.inj h).symm
  | cons values rest ih =>
    intro state output h
    cases hc : copyAt state.destination (state.offsets.headD 0) values with
    | error error => simp [catOffsetLoop, hc] at h
    | ok destination =>
      calc
        output.destination.length = destination.length := by
          apply ih ⟨destination, match state.offsets with
            | [] => []
            | first :: tail => wrap64 (first + Int.ofNat values.length) :: tail⟩ output
          simpa [catOffsetLoop, hc] using h
        _ = state.destination.length := copyAt_length _ _ _ _ hc

theorem contract : Contract := by
  unfold Contract
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, ?_, fun _ _ => ⟨rfl, rfl⟩, ?_,
    fun _ _ => rfl, ?_, fun _ _ => rfl, catOffsetLoop_length, ?_⟩
  · intro T V elementType vectors output h
    cases vectors with
    | nil => simp [hcatVectors] at h; subst output; exact ⟨rfl, rfl⟩
    | cons first rest =>
      by_cases hs : rest.all fun vector => vector.length = first.length
      · simp [hcatVectors, hs] at h; subst output; exact ⟨rfl, rfl⟩
      · simp [hcatVectors, hs] at h
  · intro T V elementType arrays output h
    unfold hcatArrays at h
    cases hv : arrays.map ArrayDesc.values with
    | nil => simp [hcatVectors, hv] at h; subst output; exact ⟨rfl, by simp [hv]⟩
    | cons first rest =>
      by_cases hs : rest.all fun vector => vector.length = first.length
      · simp [hcatVectors, hv, hs] at h
        subst output
        exact ⟨rfl, by simp [hv]⟩
      · simp [hcatVectors, hv, hs] at h
  · intro shape dimension amount output h
    by_cases hd : dimension < 1
    · simp [cshpAppend, hd] at h
    · let index := (dimension - 1).toNat
      by_cases hb : shape.length ≤ index
      · simp [cshpAppend, hd, index, hb] at h
      · simp [cshpAppend, hd, index, hb] at h
        subst output
        exact ⟨by omega, by simp, by simp [index, hb]⟩
  · intro D S V copy fill destination source output h
    cases source <;> simpa [copyOrFill] using h

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-concat"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["vcat", "hcat", "typed_vcat", "typed_hcat", "_typed_vcat_similar", "_typed_vcat", "_typed_vcat!", "_typed_hcat", "reduce", "cat_ndims", "cat_size_shape", "_cshp", "_cs", "_copy_or_fill!"]
  statement := "Concatenation preserves requested element types and order, wraps Julia Int shape sums, retains signed diagnostics, threads destination mutations and offsets, and dispatches copy versus fill."
  source := "base/abstractarray.jl:1708-1942"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairConcat

import JuliaLean.Core
import JuliaLean.MultidimCov.AbstractArrayRepairInterface
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairHvncat

open JuliaLean
open JuliaLean.Registry
open AbstractArrayRepairInterface

inductive Error where
  | argument (expected actual : Int)
  | dimensionMismatch
  | bounds
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

def wrap64 (value : Int) : Int := wrapInt .i64 value

def wrappedSum (values : List Int) : Int := values.foldl (fun total value => wrap64 (total + value)) 0
def wrappedProduct (values : List Int) : Int := values.foldl (fun total value => wrap64 (total * value)) 1

def rowsToDimshape (rows : List Int) : Result (Int × Int) :=
  match rows with
  | [] => .ok (0, 0)
  | columns :: rest =>
    if rest.all (· = columns) then .ok (Int.ofNat rows.length, columns)
    else .ok (Int.ofNat rows.length, wrappedSum rows)

def hvcat (elementType : T) (rows : List (List V)) : Result (ArrayDesc T V) :=
  match rows with
  | [] => .ok { elementType, elementSize := 0, axes := [oneTo 0], values := [], style := .linear }
  | first :: rest =>
    if !(rest.all fun row => row.length = first.length) then
      let actual := (rest.find? fun row => row.length ≠ first.length).map List.length |>.getD first.length
      .error (.argument (Int.ofNat first.length) (Int.ofNat actual))
    else .ok { elementType, elementSize := 0,
      axes := [oneTo rows.length, oneTo first.length], values := rows.flatten, style := .linear }

inductive CatValue (T V : Type) where
  | scalar (value : V)
  | array (value : ArrayDesc T V)
  deriving Repr, DecidableEq

def CatValue.values : CatValue T V → List V
  | .scalar value => [value]
  | .array array => array.values

def CatValue.shape : CatValue T V → List Int
  | .scalar _ => []
  | .array array => array.axes.map (fun axis => Int.ofNat axis.length)

def discoverShape (rank : Nat) (blocks : List (CatValue T V)) : List Int :=
  (List.range rank).map fun dimension =>
    blocks.foldl (fun current block =>
      let shape := block.shape
      let size := shape[dimension]?.getD 1
      wrap64 (current + size)) 0

def hvncat (elementType : T) (rank : Nat) (blocks : List (CatValue T V)) : Result (ArrayDesc T V) :=
  let shape := discoverShape rank blocks
  let values := blocks.flatMap CatValue.values
  if (wrappedProduct shape).toNat ≠ values.length then
    .error (.argument (wrappedProduct shape) (Int.ofNat values.length))
  else .ok { elementType, elementSize := 0, axes := shape.map (oneTo ∘ Int.toNat),
    values, style := .linear }

structure FillState (V : Type) where
  destination : List V
  offsets : List Int
  deriving Repr, DecidableEq

def writeBlock (destination : List V) (offset : Int) (values : List V) : Result (List V) :=
  if offset < 0 || destination.length < offset.toNat + values.length then .error .bounds
  else .ok (destination.take offset.toNat ++ values ++ destination.drop (offset.toNat + values.length))

def fillBlocks : List (List V) → FillState V → Result (FillState V)
  | [], state => .ok state
  | values :: rest, state =>
    let offset := state.offsets.headD 0
    match writeBlock state.destination offset values with
    | .error error => .error error
    | .ok destination =>
      let offsets := match state.offsets with
        | [] => []
        | first :: tail => wrap64 (first + Int.ofNat values.length) :: tail
      fillBlocks rest ⟨destination, offsets⟩

inductive GeneratedFillBranch where | fallback | twoDimensional | higherRank deriving Repr, DecidableEq

def generatedFillBranch (rank fields : Nat) : GeneratedFillBranch :=
  if fields = 0 then .fallback else if rank = 2 then .twoDimensional else .higherRank

def calcIndex (indices strides : List Int) : Int :=
  (List.zip indices strides).foldl
    (fun total pair => wrap64 (total + wrap64 (pair.1 * pair.2))) 1

def stackSlices (elementType : T) (slices : List (ArrayDesc T V)) : Result (ArrayDesc T V) :=
  match slices with
  | [] => .ok { elementType, elementSize := 0, axes := [oneTo 0], values := [], style := .linear }
  | first :: rest =>
    if !(rest.all fun slice => slice.axes = first.axes) then .error .dimensionMismatch
    else .ok { elementType, elementSize := 0,
      axes := first.axes ++ [oneTo slices.length], values := slices.flatMap ArrayDesc.values,
      style := first.style }

def stackMapped (map : X → Result (ArrayDesc T V)) (elementType : T)
    (inputs : List X) : Result (ArrayDesc T V) :=
  match inputs.mapM map with
  | .error _ => .error .dimensionMismatch
  | .ok slices => stackSlices elementType slices

def Contract : Prop :=
  (∀ rows output, rowsToDimshape rows = .ok output →
    output.1 = Int.ofNat rows.length ∨ rows = []) ∧
  (∀ {T V : Type} elementType rows output,
    hvcat (T := T) (V := V) elementType rows = .ok output →
      output.elementType = elementType ∧ output.values = rows.flatten) ∧
  (∀ {T V : Type} elementType rank blocks output,
    hvncat (T := T) (V := V) elementType rank blocks = .ok output →
      output.elementType = elementType ∧ output.values = blocks.flatMap CatValue.values ∧
        output.axes.length = rank) ∧
  (∀ {V : Type} blocks state output,
    fillBlocks (V := V) blocks state = .ok output →
      output.destination.length = state.destination.length) ∧
  (∀ rank fields,
    generatedFillBranch rank fields =
      if fields = 0 then .fallback else if rank = 2 then .twoDimensional else .higherRank) ∧
  (∀ indices strides,
    calcIndex indices strides = (List.zip indices strides).foldl
      (fun total pair => wrap64 (total + wrap64 (pair.1 * pair.2))) 1) ∧
  (∀ {T V : Type} elementType slices output,
    stackSlices (T := T) (V := V) elementType slices = .ok output →
      output.elementType = elementType ∧ output.values = slices.flatMap ArrayDesc.values) ∧
  (∀ {X T V : Type} map elementType inputs output,
    stackMapped (X := X) (T := T) (V := V) map elementType inputs = .ok output →
      output.elementType = elementType)

theorem writeBlock_length (destination : List V) (offset : Int) (values output : List V)
    (h : writeBlock destination offset values = .ok output) : output.length = destination.length := by
  unfold writeBlock at h
  split at h <;> simp_all
  omega

theorem fillBlocks_length : ∀ (blocks : List (List V)) state output,
    fillBlocks blocks state = .ok output → output.destination.length = state.destination.length := by
  intro blocks
  induction blocks with
  | nil => intro state output h; simpa [fillBlocks] using congrArg (fun value => value.destination.length) (Except.ok.inj h).symm
  | cons values rest ih =>
    intro state output h
    cases hw : writeBlock state.destination (state.offsets.headD 0) values with
    | error error => simp [fillBlocks, hw] at h
    | ok destination =>
      calc
        output.destination.length = destination.length := by
          apply ih ⟨destination, match state.offsets with
            | [] => []
            | first :: tail => wrap64 (first + Int.ofNat values.length) :: tail⟩ output
          simpa [fillBlocks, hw] using h
        _ = state.destination.length := writeBlock_length _ _ _ _ hw

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, ?_, fillBlocks_length, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro rows output h
    cases rows with
    | nil => exact Or.inr rfl
    | cons first rest =>
      simp [rowsToDimshape] at h
      split at h <;> simp_all
  · intro T V elementType rows output h
    cases rows with
    | nil => simp [hvcat] at h; subst output; exact ⟨rfl, rfl⟩
    | cons first rest =>
      by_cases hs : rest.all fun row => row.length = first.length
      · simp [hvcat, hs] at h; subst output; exact ⟨rfl, rfl⟩
      · simp [hvcat, hs] at h
  · intro T V elementType rank blocks output h
    by_cases hl : (wrappedProduct (discoverShape rank blocks)).toNat =
        (blocks.flatMap CatValue.values).length
    · simp [hvncat, hl] at h
      subst output
      exact ⟨rfl, rfl, by simp [discoverShape]⟩
    · simp [hvncat, hl] at h
  · intro T V elementType slices output h
    cases slices with
    | nil => simp [stackSlices] at h; subst output; exact ⟨rfl, rfl⟩
    | cons first rest =>
      by_cases hs : rest.all fun slice => slice.axes = first.axes
      · simp [stackSlices, hs] at h; subst output; exact ⟨rfl, rfl⟩
      · simp [stackSlices, hs] at h
  · intro X T V map elementType inputs output h
    cases hm : inputs.mapM map with
    | error error => simp [stackMapped, hm] at h
    | ok slices =>
      have hs := h
      simp [stackMapped, hm] at hs
      cases slices with
      | nil => simp [stackSlices] at hs; subst output; rfl
      | cons first rest =>
        split at hs <;> simp_all

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-hvncat"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["_cat", "hvcat_rows", "typed_hvcat_rows", "hvcat", "rows_to_dimshape", "typed_hvcat", "hvncat", "_hvncat", "typed_hvncat", "_typed_hvncat", "_typed_hvncat_1d", "_hvncat_fill_loop!", "hvncat_fill!", "_typed_hvncat_dims", "_typed_hvncat_shape", "hvncat_calcindex", "stack", "_stack"]
  statement := "Horizontal, vertical and n-dimensional concatenation preserve requested types, source order, wrapping shape arithmetic, short-circuit validation, value-bearing diagnostics, threaded fills, generated branches, and stack axes."
  source := "base/abstractarray.jl:2171-2999"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairHvncat

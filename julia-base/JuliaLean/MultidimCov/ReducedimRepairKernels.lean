import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReducedimRepairKernels

open JuliaLean.Registry

inductive Error where | dimensionMismatch | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

inductive SliceAxis (A : Type) where
  | oneTo (endpoint : Nat)
  | slice (indices : SliceAxis A)
  | generic (value : A) (firstIndex : Int)
  deriving Repr, DecidableEq

def firstSlice : SliceAxis A → SliceAxis A
  | .oneTo _ => .oneTo 1
  | .slice indices => .slice (firstSlice indices)
  | .generic value firstIndex => .generic value firstIndex

def firstReducedSlice : List (SliceAxis A) → List (SliceAxis A) → List (SliceAxis A)
  | [], [] => []
  | _ :: _, [] => []
  | [], arrayAxis :: arrayAxes => firstSlice arrayAxis :: firstReducedSlice [] arrayAxes
  | resultAxis :: resultAxes, arrayAxis :: arrayAxes =>
      let selected := match resultAxis with
        | .oneTo 1 => firstSlice arrayAxis
        | _ => resultAxis
      selected :: firstReducedSlice resultAxes arrayAxes

def mapfirst (check : R → A → Result Unit)
    (axesR : R → Result (List (SliceAxis X))) (axesA : A → Result (List (SliceAxis X)))
    (view : A → List (SliceAxis X) → Result V) (mapInto : F → R → V → Result R)
    (function : F) (result : R) (array : A) : Result R :=
  match check result array with
  | .error error => .error error
  | .ok _ => match axesR result, axesA array with
    | .ok resultAxes, .ok arrayAxes => match view array (firstReducedSlice resultAxes arrayAxes) with
      | .error error => .error error
      | .ok slice => mapInto function result slice
    | _, _ => .error (.source 2)

def copyfirst (mapfirstFn : (X → X) → R → A → Result R) (result : R) (array : A) :=
  mapfirstFn id result array

structure ReductionCell (K V : Type) where
  key : K
  accumulator : V
  inputs : List V
  deriving Repr, DecidableEq

def reduceInputs (function : V → Result V) (operator : V → V → Result V) :
    V → List V → Result V
  | accumulator, [] => .ok accumulator
  | accumulator, input :: rest => match function input with
    | .error error => .error error
    | .ok mapped => match operator accumulator mapped with
      | .error error => .error error
      | .ok next => reduceInputs function operator next rest

def reduceCells (function : V → Result V) (operator : V → V → Result V) :
    List (ReductionCell K V) → Result (List (K × V))
  | [] => .ok []
  | cell :: rest => match reduceInputs function operator cell.accumulator cell.inputs with
    | .error error => .error error
    | .ok reduced => match reduceCells function operator rest with
      | .error error => .error error
      | .ok tail => .ok ((cell.key, reduced) :: tail)

def mapreducedimKernel (check : Result Nat) (empty : Bool) (fastLinear : Bool)
    (function : V → Result V) (operator : V → V → Result V)
    (cells : List (ReductionCell K V)) : Result (List (K × V)) :=
  match check with
  | .error error => .error error
  | .ok leading => if empty then .ok (cells.map fun cell => (cell.key, cell.accumulator))
    else if fastLinear && leading > 16 then reduceCells function operator cells
    else reduceCells function operator cells

def mapreducedimWrapper (kernel : F → O → R → A → Result R)
    (function : F) (operator : O) (result : R) (array : A) : Result R :=
  match kernel function operator result array with
  | .error error => .error error
  | .ok _ => .ok result

def reducedimWrapper (mapreduce : (X → X) → O → R → A → Result R)
    (operator : O) (result : R) (array : A) := mapreduce id operator result array

def foldMapped (function : X → Result V) (operator : V → V → Result V) :
    V → List X → Result V
  | accumulator, [] => .ok accumulator
  | accumulator, value :: rest => match function value with
    | .error error => .error error
    | .ok mapped => match operator accumulator mapped with
      | .error error => .error error
      | .ok next => foldMapped function operator next rest

def mapreduceColon (function : X → Result V) (operator : V → V → Result V)
    (initial : V) (values : List X) : Result V := foldMapped function operator initial values

def mapreduceDim (underlying : F → O → N → A → D → Result R)
    (function : F) (operator : O) (initial : N) (array : A) (dims : D) :=
  underlying function operator initial array dims

def initializedMapreduceDim (initFn : F → O → A → D → Result R)
    (reduce : F → O → R → A → Result R) (function : F) (operator : O)
    (array : A) (dims : D) : Result R :=
  match initFn function operator array dims with
  | .error error => .error error
  | .ok result => reduce function operator result array

def reshapedMapreduceDim (parent : A → Result P)
    (underlying : F → O → N → P → Result R) (function : F) (operator : O)
    (initial : N) (array : A) : Result R :=
  match parent array with | .error error => .error error | .ok source => underlying function operator initial source

def reduceWrapper (mapreduce : (X → X) → O → A → K → Result R)
    (operator : O) (array : A) (keywords : K) := mapreduce id operator array keywords

def Contract : Prop :=
  (∀ {X R A : Type} mapfirstFn result array,
    copyfirst (X := X) (R := R) (A := A) mapfirstFn result array = mapfirstFn id result array) ∧
  (∀ {A : Type} resultAxes arrayAxes,
    (firstReducedSlice (A := A) resultAxes arrayAxes).length = arrayAxes.length) ∧
  (∀ {K V : Type} function operator cells output,
    reduceCells (K := K) (V := V) function operator cells = .ok output →
      output.map Prod.fst = cells.map ReductionCell.key) ∧
  (∀ {K V : Type} check empty fast function operator cells output,
    mapreducedimKernel (K := K) (V := V) check empty fast function operator cells = .ok output →
      output.map Prod.fst = cells.map ReductionCell.key) ∧
  (∀ {F O R A : Type} kernel function operator result array output,
    mapreducedimWrapper (F := F) (O := O) (R := R) (A := A)
      kernel function operator result array = .ok output → output = result) ∧
  (∀ {X V : Type} function operator initial values,
    mapreduceColon (X := X) (V := V) function operator initial values =
      foldMapped function operator initial values) ∧
  (∀ {F O N A D R : Type} underlying function operator initial array dims,
    mapreduceDim (F := F) (O := O) (N := N) (A := A) (D := D) (R := R)
      underlying function operator initial array dims = underlying function operator initial array dims) ∧
  (∀ {F O A D R : Type} initFn reduce function operator array dims output,
    initializedMapreduceDim (F := F) (O := O) (A := A) (D := D) (R := R)
      initFn reduce function operator array dims = .ok output →
      ∃ initial, initFn function operator array dims = .ok initial ∧
        reduce function operator initial array = .ok output) ∧
  (∀ {A P F O N R : Type} parent underlying function operator initial array output,
    reshapedMapreduceDim (A := A) (P := P) (F := F) (O := O) (N := N) (R := R)
      parent underlying function operator initial array = .ok output →
      ∃ source, parent array = .ok source ∧ underlying function operator initial source = .ok output) ∧
  (∀ {X O A K R : Type} mapreduce operator array keywords,
    reduceWrapper (X := X) (O := O) (A := A) (K := K) (R := R)
      mapreduce operator array keywords = mapreduce id operator array keywords)

theorem firstReducedSlice_length : ∀ (resultAxes arrayAxes : List (SliceAxis A)),
    (firstReducedSlice resultAxes arrayAxes).length = arrayAxes.length := by
  intro resultAxes arrayAxes
  induction arrayAxes generalizing resultAxes with
  | nil => cases resultAxes <;> rfl
  | cons axis axes ih => cases resultAxes <;> simp [firstReducedSlice, ih]

theorem reduceCells_keys (function : V → Result V) (operator : V → V → Result V) :
    ∀ (cells : List (ReductionCell K V)) output,
      reduceCells function operator cells = .ok output →
      output.map Prod.fst = cells.map ReductionCell.key := by
  intro cells
  induction cells with
  | nil => intro output h; simpa [reduceCells] using congrArg (List.map Prod.fst) (Except.ok.inj h).symm
  | cons cell rest ih =>
      intro output h
      cases hr : reduceInputs function operator cell.accumulator cell.inputs with
      | error error => simp [reduceCells, hr] at h
      | ok value =>
          cases ht : reduceCells function operator rest with
          | error error => simp [reduceCells, hr, ht] at h
          | ok tail =>
              simp [reduceCells, hr, ht] at h
              subst output
              simp [ih tail ht]

theorem contract : Contract := by
  unfold Contract
  refine ⟨fun _ _ _ => rfl, firstReducedSlice_length, ?_, ?_, ?_, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl, ?_, ?_, fun _ _ _ _ => rfl⟩
  · exact reduceCells_keys
  · intro K V check empty fast function operator cells output h
    cases check with
    | error error => simp [mapreducedimKernel] at h
    | ok leading =>
        cases empty
        · by_cases hf : fast && leading > 16
          · exact reduceCells_keys function operator cells output
              (by simpa [mapreducedimKernel, hf] using h)
          · exact reduceCells_keys function operator cells output
              (by simpa [mapreducedimKernel, hf] using h)
        · simp [mapreducedimKernel] at h
          subst output
          simp
  · intro F O R A kernel function operator result array output h
    cases hk : kernel function operator result array with
    | error error => simp [mapreducedimWrapper, hk] at h
    | ok changed =>
        simp [mapreducedimWrapper, hk] at h
        exact h.symm
  · intro F O A D R initFn reduce function operator array dims output h
    cases hi : initFn function operator array dims with
    | error error => simp [initializedMapreduceDim, hi] at h
    | ok initial => exact ⟨initial, rfl, by simpa [initializedMapreduceDim, hi] using h⟩
  · intro A P F O N R parent underlying function operator initial array output h
    cases hp : parent array with
    | error error => simp [reshapedMapreduceDim, hp] at h
    | ok source => exact ⟨source, rfl, by simpa [reshapedMapreduceDim, hp] using h⟩

def entries : List Entry := []

end JuliaLean.MultidimCov.ReducedimRepairKernels

import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalRepairA

open JuliaLean.Registry

inductive Error where
  | source (id : Nat)
  | errorCall (message : String)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure CartesianIndex where
  coordinates : List Int
  deriving Repr, DecidableEq

def lengthType (rank : Nat) : Nat := rank

def zeroType (rank : Nat) : CartesianIndex := ⟨List.replicate rank 0⟩
def zeroValue (typeOf : A → R) (zeroOfType : R → Result CartesianIndex)
    (value : A) : Result CartesianIndex :=
  match zeroOfType (typeOf value) with
  | .error error => .error error
  | .ok result => .ok result

def oneType (rank : Nat) : CartesianIndex := ⟨List.replicate rank 1⟩
def oneValue (typeOf : A → R) (oneOfType : R → Result CartesianIndex)
    (value : A) : Result CartesianIndex :=
  match oneOfType (typeOf value) with
  | .error error => .error error
  | .ok result => .ok result

def swappedMultiply (multiply : CartesianIndex → S → Result CartesianIndex)
    (scalar : S) (index : CartesianIndex) : Result CartesianIndex := multiply index scalar

def nextIndex (cartesianIndices : AX → Result CI)
    (nextind : CI → CartesianIndex → Result CartesianIndex)
    (axes : AX) (index : CartesianIndex) : Result CartesianIndex :=
  match cartesianIndices axes with
  | .error error => .error error
  | .ok indices => nextind indices index

def previousIndex (cartesianIndices : AX → Result CI)
    (prevind : CI → CartesianIndex → Result CartesianIndex)
    (axes : AX) (index : CartesianIndex) : Result CartesianIndex :=
  match cartesianIndices axes with
  | .error error => .error error
  | .ok indices => prevind indices index

def ind2sub (tuple : CartesianIndex → Result T) (convert : T → Result O)
    (index : CartesianIndex) : Result O :=
  match tuple index with
  | .error error => .error error
  | .ok coordinates => convert coordinates

def iterateCartesianIndex (_index : CartesianIndex) : Result O :=
  .error (.errorCall "iteration is deliberately unsupported for CartesianIndex. Use `I` rather than `I...`, or use `Tuple(I)...`")

def rangeCartesianIndex (_start _step : CartesianIndex) (_length : Int) : Result O :=
  .error (.errorCall "Cannot construct ranges of CartesianIndex. Use `CartesianIndices` instead.")

structure ShowValues (A : Type) where
  first : A
  step : A
  length : Int
  deriving Repr, DecidableEq

def showCartesianRange (first : R → Result A) (step : R → Result A)
    (length : R → Result Int) (range : R) : Result (ShowValues A) :=
  match first range with
  | .error error => .error error
  | .ok firstValue => match step range with
    | .error error => .error error
    | .ok stepValue => match length range with
      | .error error => .error error
      | .ok count => .ok ⟨firstValue, stepValue, count⟩

def Contract : Prop :=
  (∀ rank, lengthType rank = rank) ∧
  (∀ rank, (zeroType rank).coordinates = List.replicate rank 0) ∧
  (∀ {A R : Type} typeOf zeroOfType value output,
    zeroValue (A := A) (R := R) typeOf zeroOfType value = .ok output →
      zeroOfType (typeOf value) = .ok output) ∧
  (∀ rank, (oneType rank).coordinates = List.replicate rank 1) ∧
  (∀ {A R : Type} typeOf oneOfType value output,
    oneValue (A := A) (R := R) typeOf oneOfType value = .ok output →
      oneOfType (typeOf value) = .ok output) ∧
  (∀ {S : Type} multiply scalar index,
    swappedMultiply (S := S) multiply scalar index = multiply index scalar) ∧
  (∀ {AX CI : Type} construct advance axes index constructed output,
    nextIndex (AX := AX) (CI := CI) construct advance axes index = .ok output →
      construct axes = .ok constructed → advance constructed index = .ok output) ∧
  (∀ {AX CI : Type} construct retreat axes index constructed output,
    previousIndex (AX := AX) (CI := CI) construct retreat axes index = .ok output →
      construct axes = .ok constructed → retreat constructed index = .ok output) ∧
  (∀ {T O : Type} tuple convert index coordinates output,
    ind2sub (T := T) (O := O) tuple convert index = .ok output →
      tuple index = .ok coordinates → convert coordinates = .ok output) ∧
  (∀ {O : Type} index, iterateCartesianIndex (O := O) index =
    .error (.errorCall "iteration is deliberately unsupported for CartesianIndex. Use `I` rather than `I...`, or use `Tuple(I)...`")) ∧
  (∀ {O : Type} start step (length : Int), rangeCartesianIndex (O := O) start step length =
    .error (.errorCall "Cannot construct ranges of CartesianIndex. Use `CartesianIndices` instead.")) ∧
  (∀ {R A : Type} first step length range output,
    showCartesianRange (R := R) (A := A) first step length range = .ok output →
      ∃ firstValue stepValue count,
        first range = .ok firstValue ∧ step range = .ok stepValue ∧ length range = .ok count ∧
        output = ⟨firstValue, stepValue, count⟩)

theorem contract : Contract := by
  unfold Contract
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, fun _ => rfl, ?_, fun _ _ _ => rfl,
    ?_, ?_, ?_, fun _ => rfl, fun _ _ _ => rfl, ?_⟩
  · intro A R typeOf zeroOfType value output h
    cases hz : zeroOfType (typeOf value) <;> simp [zeroValue, hz] at h ⊢
    exact h.symm ▸ rfl
  · intro A R typeOf oneOfType value output h
    cases ho : oneOfType (typeOf value) <;> simp [oneValue, ho] at h ⊢
    exact h.symm ▸ rfl
  · intro AX CI construct advance axes index constructed output h hc
    rw [nextIndex, hc] at h
    exact h
  · intro AX CI construct retreat axes index constructed output h hc
    rw [previousIndex, hc] at h
    exact h
  · intro T O tuple convert index coordinates output h ht
    rw [ind2sub, ht] at h
    exact h
  · intro R A first step length range output h
    cases hf : first range with
    | error error => simp [showCartesianRange, hf] at h
    | ok firstValue =>
        cases hs : step range with
        | error error => simp [showCartesianRange, hf, hs] at h
        | ok stepValue =>
            cases hl : length range with
            | error error => simp [showCartesianRange, hf, hs, hl] at h
            | ok count =>
                simp only [showCartesianRange, hf, hs, hl] at h
                exact ⟨firstValue, stepValue, count, rfl, rfl, rfl, (Except.ok.inj h).symm⟩

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalRepairA

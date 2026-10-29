import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReducedimRepairFind

open JuliaLean.Registry

inductive Error where | argument | dimensionMismatch | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure Candidate (K V : Type) where
  key : K
  value : V
  deriving Repr, DecidableEq
structure FindCell (K V : Type) where
  key : K
  currentValue : V
  currentIndex : Option K
  candidates : List (Candidate K V)
  deriving Repr, DecidableEq

def reduceCandidates (function : V → Result V) (better : V → V → Result Bool) :
    V → Option K → List (Candidate K V) → Result (V × Option K)
  | value, index, [] => .ok (value, index)
  | value, index, candidate :: rest => match function candidate.value with
    | .error error => .error error
    | .ok mapped =>
      let choose : Result Bool := match index with | none => .ok true | some _ => better value mapped
      match choose with
      | .error error => .error error
      | .ok true => reduceCandidates function better mapped (some candidate.key) rest
      | .ok false => reduceCandidates function better value index rest

def reduceFindCells (function : V → Result V) (better : V → V → Result Bool) :
    List (FindCell K V) → Result (List (K × V × Option K))
  | [] => .ok []
  | cell :: rest => match reduceCandidates function better cell.currentValue cell.currentIndex cell.candidates with
    | .error error => .error error
    | .ok (value, index) => match reduceFindCells function better rest with
      | .error error => .error error
      | .ok tail => .ok ((cell.key, value, index) :: tail)

def findKernel (emptyValues emptyArray : Result Bool) (checkDims checkAxes : Result Unit)
    (function : V → Result V) (better : V → V → Result Bool)
    (cells : List (FindCell K V)) : Result (List (K × V × Option K)) :=
  match emptyValues with
  | .error error => .error error
  | .ok true => .ok []
  | .ok false => match emptyArray with
    | .error error => .error error
    | .ok true => .ok []
    | .ok false => match checkDims with
      | .error error => .error error
      | .ok _ => match checkAxes with
        | .error error => .error error
        | .ok _ => reduceFindCells function better cells

def findBang (isEmpty : A → Result Bool) (first : A → Result V)
    (fillValues : RV → V → Result RV) (zeroIndex : Result K)
    (fillIndices : RI → K → Result RI)
    (kernel : RV → RI → A → Result O) (values : RV) (indices : RI)
    (array : A) (initFlag : Bool) : Result O :=
  let preparedValues : Result RV := if !initFlag then .ok values else match isEmpty array with
    | .error error => .error error
    | .ok true => .ok values
    | .ok false => match first array with
      | .error error => .error error
      | .ok initial => fillValues values initial
  match preparedValues with
  | .error error => .error error
  | .ok resultValues => match zeroIndex with
    | .error error => .error error
    | .ok zero => match fillIndices indices zero with
      | .error error => .error error
      | .ok resultIndices => kernel resultValues resultIndices array

def findWrapper (underlying : A → D → Result R) (array : A) (dims : D) :=
  underlying array dims

def findIdentityWrapper (underlying : (X → X) → A → D → Result R)
    (array : A) (dims : D) := underlying id array dims

def findAllocate (reducedIndices0 : A → D → Result RI)
    (isEmpty : A → Result Bool) (reducedIndices : A → D → Result AX)
    (axisProduct : AX → Result Nat) (emptyValues : A → RI → Result RV)
    (emptyIndices : A → RI → Result RK) (first : A → Result X)
    (function : F → X → Result V) (initType : F → A → Result T)
    (filledValues : A → T → RI → V → Result RV) (zeroIndices : A → RI → Result RK)
    (kernel : F → RV → RK → A → Result (RV × RK))
    (f : F) (array : A) (region : D) : Result (RV × RK) :=
  match reducedIndices0 array region with
  | .error error => .error error
  | .ok resultAxes => match isEmpty array with
    | .error error => .error error
    | .ok true => match reducedIndices array region with
      | .error error => .error error
      | .ok fullAxes => match axisProduct fullAxes with
        | .error error => .error error
        | .ok product => if product ≠ 0 then .error .argument else
          match emptyValues array resultAxes, emptyIndices array resultAxes with
          | .ok values, .ok indices => .ok (values, indices)
          | _, _ => .error (.source 5)
    | .ok false => match first array with
      | .error error => .error error
      | .ok firstValue => match function f firstValue with
        | .error error => .error error
        | .ok mapped => match initType f array with
          | .error error => .error error
          | .ok target => match filledValues array target resultAxes mapped,
              zeroIndices array resultAxes with
            | .ok values, .ok indices => kernel f values indices array
            | _, _ => .error (.source 6)

inductive InitTarget where | promoted | missingUnion | transformed deriving Repr, DecidableEq

def findInitType (eltypeFirst eltypeSecond : A → Result T)
    (promoteUnion : T → Result P) (realtype : F → P → Result R)
    (first : A → Result X) (function : F → X → Result V)
    (valueMatches : V → R → Bool) (hasMissing : T → Bool)
    (f : F) (array : A) : Result InitTarget :=
  match eltypeFirst array with
  | .error error => .error error
  | .ok element => match promoteUnion element with
    | .error error => .error error
    | .ok promoted => match realtype f promoted with
      | .error error => .error error
      | .ok target => match first array with
        | .error error => .error error
        | .ok firstValue => match function f firstValue with
          | .error error => .error error
          | .ok mapped => if valueMatches mapped target then .ok .promoted else
            match eltypeSecond array with
            | .error error => .error error
            | .ok secondElement => if hasMissing secondElement then .ok .missingUnion else .ok .transformed

def reducedim1 (axes1Length : R → Result Nat) (result : R) : Result Bool :=
  match axes1Length result with | .error error => .error error | .ok length => .ok (length = 1)

def argumentIndex (find : A → D → Result (V × I)) (array : A) (dims : D) : Result I :=
  match find array dims with | .error error => .error error | .ok pair => .ok pair.2

def Contract : Prop :=
  (∀ {K V : Type} function better cells output,
    reduceFindCells (K := K) (V := V) function better cells = .ok output →
      output.map (fun entry => entry.1) = cells.map FindCell.key) ∧
  (∀ {K V : Type} emptyValues emptyArray checkDims checkAxes function better cells output,
    findKernel (K := K) (V := V) emptyValues emptyArray checkDims checkAxes function better cells = .ok output →
      emptyValues = .ok true ∨ emptyValues = .ok false ∧
        (emptyArray = .ok true ∨ emptyArray = .ok false ∧ output.map (fun entry => entry.1) = cells.map FindCell.key)) ∧
  (∀ {A V RV K RI O : Type} isEmpty first fillValues zeroIndex fillIndices kernel values indices array initFlag output,
    findBang (A := A) (V := V) (RV := RV) (K := K) (RI := RI) (O := O)
      isEmpty first fillValues zeroIndex fillIndices kernel values indices array initFlag = .ok output →
      ∃ preparedValues preparedIndices, kernel preparedValues preparedIndices array = .ok output) ∧
  (∀ {A D R : Type} underlying array dims,
    findWrapper (A := A) (D := D) (R := R) underlying array dims = underlying array dims) ∧
  (∀ {X A D R : Type} underlying array dims,
    findIdentityWrapper (X := X) (A := A) (D := D) (R := R) underlying array dims =
      underlying id array dims) ∧
  (∀ {A D RI AX RV RK X F V T : Type} reduced0 isEmpty reduced axesProduct emptyValues emptyIndices first function initType filledValues zeroIndices kernel f array region output,
    findAllocate (A := A) (D := D) (RI := RI) (AX := AX) (RV := RV) (RK := RK)
      (X := X) (F := F) (V := V) (T := T) reduced0 isEmpty reduced axesProduct
      emptyValues emptyIndices first function initType filledValues zeroIndices kernel f array region = .ok output →
      ∃ resultAxes, reduced0 array region = .ok resultAxes) ∧
  (∀ {A T P R F X V : Type} firstType secondType promote real first function valueMatches missing f array output,
    findInitType (A := A) (T := T) (P := P) (R := R) (F := F) (X := X) (V := V)
      firstType secondType promote real first function valueMatches missing f array = .ok output →
      ∃ element promoted target firstValue mapped,
        firstType array = .ok element ∧ promote element = .ok promoted ∧ real f promoted = .ok target ∧
        first array = .ok firstValue ∧ function f firstValue = .ok mapped ∧
        (output = .promoted ∨ ∃ secondElement, secondType array = .ok secondElement)) ∧
  (∀ {R : Type} axesLength result output,
    reducedim1 (R := R) axesLength result = .ok output →
      ∃ length, axesLength result = .ok length ∧ output = decide (length = 1)) ∧
  (∀ {A D V I : Type} find array dims output,
    argumentIndex (A := A) (D := D) (V := V) (I := I) find array dims = .ok output →
      ∃ value, find array dims = .ok (value, output))

theorem reduceFindCells_keys (function : V → Result V) (better : V → V → Result Bool) :
    ∀ cells output, reduceFindCells (K := K) function better cells = .ok output →
      output.map (fun entry => entry.1) = cells.map FindCell.key := by
  intro cells
  induction cells with
  | nil => intro output h; simpa [reduceFindCells] using congrArg (List.map fun entry => entry.1) (Except.ok.inj h).symm
  | cons cell rest ih =>
    intro output h
    cases hr : reduceCandidates function better cell.currentValue cell.currentIndex cell.candidates with
    | error error => simp [reduceFindCells, hr] at h
    | ok pair =>
      cases pair with
      | mk value index =>
        cases ht : reduceFindCells function better rest with
        | error error => simp [reduceFindCells, hr, ht] at h
        | ok tail =>
          simp [reduceFindCells, hr, ht] at h
          subst output
          simp [ih tail ht]

theorem contract : Contract := by
  unfold Contract
  refine ⟨reduceFindCells_keys, ?_, ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro K V emptyValues emptyArray checkDims checkAxes function better cells output h
    cases hv : emptyValues with
    | error error => simp [findKernel, hv] at h
    | ok valuesEmpty =>
      cases valuesEmpty with
      | true => exact Or.inl rfl
      | false =>
        cases ha : emptyArray with
        | error error => simp [findKernel, hv, ha] at h
        | ok arrayEmpty =>
          cases arrayEmpty with
          | true => exact Or.inr ⟨rfl, Or.inl rfl⟩
          | false =>
            cases hd : checkDims with
            | error error => simp [findKernel, hv, ha, hd] at h
            | ok checked =>
              cases hx : checkAxes with
              | error error => simp [findKernel, hv, ha, hd, hx] at h
              | ok checkedAxes =>
                have hreduce : reduceFindCells function better cells = .ok output := by
                  simpa [findKernel, hv, ha, hd, hx] using h
                exact Or.inr ⟨rfl, Or.inr ⟨rfl,
                  reduceFindCells_keys function better cells output hreduce⟩⟩
  · intro A V RV K RI O isEmpty first fillValues zeroIndex fillIndices kernel values indices array initFlag output h
    cases initFlag
    · cases hz : zeroIndex with
      | error error => simp [findBang, hz] at h
      | ok zero =>
        cases hi : fillIndices indices zero with
        | error error => simp [findBang, hz, hi] at h
        | ok preparedIndices => exact ⟨values, preparedIndices,
            by simpa [findBang, hz, hi] using h⟩
    · cases he : isEmpty array with
      | error error => simp [findBang, he] at h
      | ok empty =>
        cases empty
        · cases hf : first array with
          | error error => simp [findBang, he, hf] at h
          | ok firstValue =>
            cases hv : fillValues values firstValue with
            | error error => simp [findBang, he, hf, hv] at h
            | ok preparedValues =>
              cases hz : zeroIndex with
              | error error => simp [findBang, he, hf, hv, hz] at h
              | ok zero =>
                cases hi : fillIndices indices zero with
                | error error => simp [findBang, he, hf, hv, hz, hi] at h
                | ok preparedIndices => exact ⟨preparedValues, preparedIndices,
                    by simpa [findBang, he, hf, hv, hz, hi] using h⟩
        · cases hz : zeroIndex with
          | error error => simp [findBang, he, hz] at h
          | ok zero =>
            cases hi : fillIndices indices zero with
            | error error => simp [findBang, he, hz, hi] at h
            | ok preparedIndices => exact ⟨values, preparedIndices,
                by simpa [findBang, he, hz, hi] using h⟩
  · intro A D RI AX RV RK X F V T reduced0 isEmpty reduced axesProduct emptyValues emptyIndices first function initType filledValues zeroIndices kernel f array region output h
    cases hr : reduced0 array region with
    | error error => simp [findAllocate, hr] at h
    | ok resultAxes => exact ⟨resultAxes, rfl⟩
  · intro A T P R F X V firstType secondType promote real first function valueMatches missing f array output h
    cases he : firstType array with
    | error error => simp [findInitType, he] at h
    | ok element =>
      cases hp : promote element with
      | error error => simp [findInitType, he, hp] at h
      | ok promoted =>
        cases hr : real f promoted with
        | error error => simp [findInitType, he, hp, hr] at h
        | ok target =>
          cases hf : first array with
          | error error => simp [findInitType, he, hp, hr, hf] at h
          | ok firstValue =>
            cases hm : function f firstValue with
            | error error => simp [findInitType, he, hp, hr, hf, hm] at h
            | ok mapped =>
              by_cases hv : valueMatches mapped target
              · exact ⟨element, promoted, target, firstValue, mapped, rfl, hp, hr, rfl, hm, Or.inl (by simpa [findInitType, he, hp, hr, hf, hm, hv] using h.symm)⟩
              · cases hs : secondType array with
                | error error => simp [findInitType, he, hp, hr, hf, hm, hv, hs] at h
                | ok secondElement => exact ⟨element, promoted, target, firstValue, mapped,
                    rfl, hp, hr, rfl, hm, Or.inr ⟨secondElement, rfl⟩⟩
  · intro R axesLength result output h
    cases hl : axesLength result with
    | error error => simp [reducedim1, hl] at h
    | ok length => exact ⟨length, rfl, by simpa [reducedim1, hl] using h.symm⟩
  · intro A D V I find array dims output h
    cases hf : find array dims with
    | error error => simp [argumentIndex, hf] at h
    | ok pair =>
      rcases pair with ⟨value, index⟩
      simp [argumentIndex, hf] at h
      subst output
      exact ⟨value, rfl⟩

def entries : List Entry := []

end JuliaLean.MultidimCov.ReducedimRepairFind

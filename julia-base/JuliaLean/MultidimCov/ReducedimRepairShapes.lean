import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReducedimRepairShapes

open JuliaLean.Registry

inductive Error where
  | argument (message : String)
  | source (id : Nat)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure OneTo (T : Type) where endpoint : T deriving Repr, DecidableEq

def reducedOneTo (typeToken : T) (one : T → Result T) : Result (OneTo T) :=
  match one typeToken with
  | .error error => .error error
  | .ok endpoint => .ok ⟨endpoint⟩

def reducedWrapper (first : W → Result I) (makeRange : I → I → Result R)
    (oftype : W → R → Result W) (wrapper : W) : Result W :=
  match first wrapper with
  | .error error => .error error
  | .ok endpoint => match makeRange endpoint endpoint with
    | .error error => .error error
    | .ok singleton => oftype wrapper singleton

def unsupportedRange (typeName : R → String) (range : R) : Result O :=
  .error (.argument ("No method is implemented for reducing index range of type " ++
    typeName range ++ ". Please implement\nreduced_index for this index type or report this as an issue.\n"))

inductive RegionValue where
  | integer (value : Int)
  | other
  deriving Repr, DecidableEq

def checkValidRegion : List RegionValue → Result Unit
  | [] => .ok ()
  | .other :: _ => .error (.argument "reduced dimension(s) must be integers")
  | .integer value :: rest =>
      if value < 1 then .error (.argument ("region dimension(s) must be ≥ 1, got " ++ toString value))
      else checkValidRegion rest

def containsDimension (region : List RegionValue) (dimension : Nat) : Bool :=
  region.any fun value => match value with
    | .integer integer => integer = Int.ofNat dimension
    | .other => false

def reducedAxis (reduce : A → Result A) (isEmpty : A → Bool) (keepZeroDims : Bool)
    (region : List RegionValue) (axis : A) (dimension : Nat) : Result A :=
  if containsDimension region dimension && (!keepZeroDims || !isEmpty axis) then reduce axis else .ok axis

def reducedIndices (reduce : A → Result A) (isEmpty : A → Bool)
    (keepZeroDims : Bool) (axes : List A) (region : List RegionValue) : Result (List A) :=
  match checkValidRegion region with
  | .error error => .error error
  | .ok _ => transform axes 1
where
  transform : List A → Nat → Result (List A)
    | [], _ => .ok []
    | axis :: rest, dimension =>
        match reducedAxis reduce isEmpty keepZeroDims region axis dimension with
        | .error error => .error error
        | .ok transformed => match transform rest (dimension + 1) with
          | .error error => .error error
          | .ok tail => .ok (transformed :: tail)

def reducedIndicesFromArray (axes : X → Result (List A))
    (reduce : A → Result A) (isEmpty : A → Bool) (keepZeroDims : Bool)
    (array : X) (region : List RegionValue) : Result (List A) :=
  match axes array with
  | .error error => .error error
  | .ok arrayAxes => reducedIndices reduce isEmpty keepZeroDims arrayAxes region

theorem transform_length (reduce : A → Result A) (isEmpty : A → Bool)
    (keepZeroDims : Bool) (region : List RegionValue) :
    ∀ axes dimension output,
      reducedIndices.transform reduce isEmpty keepZeroDims region axes dimension = .ok output →
      output.length = axes.length := by
  intro axes
  induction axes with
  | nil => intro dimension output h; simpa [reducedIndices.transform] using congrArg List.length (Except.ok.inj h).symm
  | cons axis rest ih =>
      intro dimension output h
      cases hh : reducedAxis reduce isEmpty keepZeroDims region axis dimension with
      | error error => simp [reducedIndices.transform, hh] at h
      | ok transformed =>
          cases ht : reducedIndices.transform reduce isEmpty keepZeroDims region rest (dimension + 1) with
          | error error => simp [reducedIndices.transform, hh, ht] at h
          | ok tail =>
              simp [reducedIndices.transform, hh, ht] at h
              subst output
              simp [ih (dimension + 1) tail ht]

def Contract : Prop :=
  (∀ {T : Type} typeToken one endpoint,
    reducedOneTo (T := T) typeToken one = .ok endpoint →
      ∃ value, one typeToken = .ok value ∧ endpoint.endpoint = value) ∧
  (∀ {W I R : Type} first makeRange oftype wrapper output,
    reducedWrapper (W := W) (I := I) (R := R) first makeRange oftype wrapper = .ok output →
      ∃ endpoint singleton, first wrapper = .ok endpoint ∧
        makeRange endpoint endpoint = .ok singleton ∧ oftype wrapper singleton = .ok output) ∧
  (∀ {R O : Type} typeName range,
    unsupportedRange (R := R) (O := O) typeName range =
      .error (.argument ("No method is implemented for reducing index range of type " ++
        typeName range ++ ". Please implement\nreduced_index for this index type or report this as an issue.\n"))) ∧
  (∀ {A : Type} reduce isEmpty keepZero axes region output,
    reducedIndices (A := A) reduce isEmpty keepZero axes region = .ok output →
      output.length = axes.length) ∧
  (∀ {X A : Type} axes reduce isEmpty keepZero array region output,
    reducedIndicesFromArray (X := X) (A := A) axes reduce isEmpty keepZero array region = .ok output →
      ∃ arrayAxes, axes array = .ok arrayAxes ∧ output.length = arrayAxes.length) ∧
  (∀ region, checkValidRegion region = .ok () →
    ∀ value ∈ region, ∃ integer, value = .integer integer ∧ 1 ≤ integer)

theorem validRegion_members : ∀ region, checkValidRegion region = .ok () →
    ∀ value ∈ region, ∃ integer, value = .integer integer ∧ 1 ≤ integer := by
  intro region
  induction region with
  | nil => simp
  | cons value rest ih =>
      cases value with
      | other => simp [checkValidRegion]
      | integer integer =>
          by_cases h : integer < 1
          · simp [checkValidRegion, h]
          · intro hvalid candidate member
            simp [checkValidRegion, h] at hvalid
            cases member with
            | head => exact ⟨integer, rfl, by omega⟩
            | tail _ member => exact ih hvalid _ member

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, fun _ _ => rfl, ?_, ?_, validRegion_members⟩
  · intro T typeToken one endpoint h
    cases ho : one typeToken with
    | error error => simp [reducedOneTo, ho] at h
    | ok value =>
        simp [reducedOneTo, ho] at h
        subst endpoint
        exact ⟨value, rfl, rfl⟩
  · intro W I R first makeRange oftype wrapper output h
    cases hf : first wrapper with
    | error error => simp [reducedWrapper, hf] at h
    | ok endpoint =>
        cases hm : makeRange endpoint endpoint with
        | error error => simp [reducedWrapper, hf, hm] at h
        | ok singleton => exact ⟨endpoint, singleton, rfl, hm,
            by simpa [reducedWrapper, hf, hm] using h⟩
  · intro A reduce isEmpty keepZero axes region output h
    cases hc : checkValidRegion region with
    | error error => simp [reducedIndices, hc] at h
    | ok checked =>
        apply transform_length reduce isEmpty keepZero region axes 1 output
        simpa [reducedIndices, hc] using h
  · intro X A axes reduce isEmpty keepZero array region output h
    cases ha : axes array with
    | error error => simp [reducedIndicesFromArray, ha] at h
    | ok arrayAxes =>
        refine ⟨arrayAxes, rfl, ?_⟩
        have hr : reducedIndices reduce isEmpty keepZero arrayAxes region = .ok output := by
          simpa [reducedIndicesFromArray, ha] using h
        cases hc : checkValidRegion region with
        | error error => simp [reducedIndices, hc] at hr
        | ok checked =>
            apply transform_length reduce isEmpty keepZero region arrayAxes 1 output
            simpa [reducedIndices, hc] using hr

def entries : List Entry := []

end JuliaLean.MultidimCov.ReducedimRepairShapes

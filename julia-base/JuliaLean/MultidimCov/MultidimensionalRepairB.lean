import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalRepairB

open JuliaLean.Registry

inductive Error where | source (id : Nat) | bounds | rank deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure CartesianIndices (R : Type) where axes : List R deriving Repr, DecidableEq

def emptyConstructor (construct : List R → Result (CartesianIndices R)) : Result (CartesianIndices R) :=
  construct []

def fromCartesianIndex (tuple : I → Result T) (convertTuple : T → Result (List R))
    (construct : List R → Result (CartesianIndices R)) (index : I) : Result (CartesianIndices R) :=
  match tuple index with
  | .error error => .error error
  | .ok values => match convertTuple values with
    | .error error => .error error
    | .ok axes => construct axes

def convertBoolAxis (convertInt8 : Bool → Result I) (oneTo : I → Result R) (value : Bool) : Result R :=
  match convertInt8 value with | .error e => .error e | .ok n => oneTo n
def convertIntegerAxis (oneTo : I → Result R) (value : I) : Result R := oneTo value
def convertUnitRange (first last : S → Result I) (makeRange : I → I → Result R) (source : S) : Result R :=
  match first source with
  | .error e => .error e
  | .ok a => match last source with
    | .error e => .error e
    | .ok b => makeRange a b
def convertStepRange (first step last : S → Result I)
    (makeRange : I → I → I → Result R) (source : S) : Result R :=
  match first source with
  | .error e => .error e
  | .ok a => match step source with
    | .error e => .error e
    | .ok s => match last source with
      | .error e => .error e
      | .ok b => makeRange a s b

def showAxes (transform : R → Result X) (showFn : List X → Result O)
    (indices : CartesianIndices R) : Result O :=
  match indices.axes.mapM transform with | .error e => .error e | .ok values => showFn values

def convertCartesian (convertTuple : List R → Result (List T))
    (construct : List T → Result (CartesianIndices T)) (source : CartesianIndices R) : Result (CartesianIndices T) :=
  match convertTuple source.axes with | .error e => .error e | .ok axes => construct axes

def convertCartesianBroadcast (convertAxis : R → Result T)
    (construct : List T → Result (CartesianIndices T)) (source : CartesianIndices R) : Result (CartesianIndices T) :=
  match source.axes.mapM convertAxis with | .error e => .error e | .ok axes => construct axes

def rangesEqual (equal : R → R → Result Bool) : List R → List R → Result Bool
  | [], [] => .ok true
  | [], _ :: _ | _ :: _, [] => .error .rank
  | a :: as, b :: bs => match equal a b with
    | .error e => .error e
    | .ok false => .ok false
    | .ok true => rangesEqual equal as bs

def axesOf (axes : R → Result A) (indices : CartesianIndices R) : Result (List A) :=
  indices.axes.mapM axes

def hasOffsetAxes (hasOffset : R → Result Bool) : List R → Result Bool
  | [] => .ok false
  | axis :: rest => match hasOffset axis with
    | .error e => .error e
    | .ok true => .ok true
    | .ok false => hasOffsetAxes hasOffset rest

def getindexCoordinates (checkbounds : CartesianIndices R → List I → Result Unit)
    (getindex : R → I → Result O) (indices : CartesianIndices R) (coordinates : List I) : Result (List O) :=
  match checkbounds indices coordinates with
  | .error e => .error e
  | .ok _ =>
      if indices.axes.length = coordinates.length then
        (List.zip indices.axes coordinates).mapM fun pair => getindex pair.1 pair.2
      else .error .rank

def getindexRanges (checkbounds : CartesianIndices R → List S → Result Unit)
    (getindex : R → S → Result T) (construct : List T → Result (CartesianIndices T))
    (indices : CartesianIndices R) (selectors : List S) : Result (CartesianIndices T) :=
  match checkbounds indices selectors with
  | .error e => .error e
  | .ok _ => if indices.axes.length = selectors.length then
      match (List.zip indices.axes selectors).mapM fun pair => getindex pair.1 pair.2 with
      | .error e => .error e
      | .ok axes => construct axes
    else .error .rank

def viewRanges (view : A → List R → Result V) (construct : List R → Result (CartesianIndices R))
    (parent : A) (selectors : List R) : Result (V × CartesianIndices R) :=
  match view parent selectors with
  | .error e => .error e
  | .ok viewed => match construct selectors with
    | .error e => .error e
    | .ok indices => .ok (viewed, indices)

theorem mapM_length {E A B : Type} (f : A → Except E B) :
    ∀ (xs : List A) ys, xs.mapM f = .ok ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; change Except.ok [] = Except.ok ys at h; exact congrArg List.length (Except.ok.inj h).symm
  | cons x xs ih =>
      intro ys h
      cases hx : f x with
      | error e => simp [List.mapM_cons, hx, bind, Except.bind] at h
      | ok y =>
          cases ht : xs.mapM f with
          | error e => simp [List.mapM_cons, hx, ht, bind, Except.bind] at h
          | ok tail =>
              simp [List.mapM_cons, hx, ht, bind, Except.bind, pure, Except.pure] at h
              subst ys
              simp [ih tail ht]

def Contract : Prop :=
  (∀ {R : Type} construct, emptyConstructor (R := R) construct = construct []) ∧
  (∀ {I R : Type} convertInt8 oneTo value output,
    convertBoolAxis (I := I) (R := R) convertInt8 oneTo value = .ok output →
      ∃ converted, convertInt8 value = .ok converted ∧ oneTo converted = .ok output) ∧
  (∀ {I R : Type} oneTo value, convertIntegerAxis (I := I) (R := R) oneTo value = oneTo value) ∧
  (∀ {R X O : Type} transform showFn indices output,
    showAxes (R := R) (X := X) (O := O) transform showFn indices = .ok output →
      ∃ transformed, indices.axes.mapM transform = .ok transformed ∧ showFn transformed = .ok output) ∧
  (∀ {R T : Type} convertAxis construct source output,
    (∀ axes result, construct axes = .ok result → result.axes = axes) →
    convertCartesianBroadcast (R := R) (T := T) convertAxis construct source = .ok output →
      output.axes.length = source.axes.length) ∧
  (∀ {R A : Type} axes indices output,
    axesOf (R := R) (A := A) axes indices = .ok output → output.length = indices.axes.length) ∧
  (∀ {R I O : Type} checkbounds getindex indices coordinates output,
    getindexCoordinates (R := R) (I := I) (O := O) checkbounds getindex indices coordinates = .ok output →
      indices.axes.length = coordinates.length ∧ output.length = coordinates.length) ∧
  (∀ {R S T : Type} checkbounds getindex construct indices selectors output,
    (∀ axes result, construct axes = .ok result → result.axes = axes) →
    getindexRanges (R := R) (S := S) (T := T) checkbounds getindex construct indices selectors = .ok output →
      indices.axes.length = selectors.length ∧ output.axes.length = selectors.length)

theorem contract : Contract := by
  unfold Contract
  refine ⟨fun _ => rfl, ?_, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro I R convertInt8 oneTo value output h
    cases hc : convertInt8 value with
    | error e => simp [convertBoolAxis, hc] at h
    | ok converted => exact ⟨converted, rfl, by simpa [convertBoolAxis, hc] using h⟩
  · intro R X O transform showFn indices output h
    cases hm : indices.axes.mapM transform with
    | error e => simp [showAxes, hm] at h
    | ok transformed => exact ⟨transformed, rfl, by simpa [showAxes, hm] using h⟩
  · intro R T convertAxis construct source output hconstruct h
    cases hm : source.axes.mapM convertAxis with
    | error e => simp [convertCartesianBroadcast, hm] at h
    | ok axes =>
        have hl := mapM_length convertAxis source.axes axes hm
        cases hc : construct axes with
        | error e => simp [convertCartesianBroadcast, hm, hc] at h
        | ok result =>
            simp [convertCartesianBroadcast, hm, hc] at h
            subst output
            rw [hconstruct axes result hc]
            exact hl
  · intro R A axes indices output h
    exact mapM_length axes indices.axes output h
  · intro R I O checkbounds getindex indices coordinates output h
    cases hb : checkbounds indices coordinates with
    | error e => simp [getindexCoordinates, hb] at h
    | ok u =>
        by_cases hr : indices.axes.length = coordinates.length
        · have hz : (List.zip indices.axes coordinates).length = coordinates.length := by simp [hr]
          have hm := mapM_length (fun pair => getindex pair.1 pair.2)
            (List.zip indices.axes coordinates) output (by simpa [getindexCoordinates, hb, hr] using h)
          exact ⟨hr, by omega⟩
        · simp [getindexCoordinates, hb, hr] at h
  · intro R S T checkbounds getindex construct indices selectors output hconstruct h
    cases hb : checkbounds indices selectors with
    | error e => simp [getindexRanges, hb] at h
    | ok u =>
        by_cases hr : indices.axes.length = selectors.length
        · cases hm : (List.zip indices.axes selectors).mapM (fun pair => getindex pair.1 pair.2) with
          | error e => simp [getindexRanges, hb, hr, hm] at h
          | ok axes =>
              have hl := mapM_length (fun pair => getindex pair.1 pair.2)
                (List.zip indices.axes selectors) axes hm
              cases hc : construct axes with
              | error e => simp [getindexRanges, hb, hr, hm, hc] at h
              | ok result =>
                  simp [getindexRanges, hb, hr, hm, hc] at h
                  subst output
                  rw [hconstruct axes result hc]
                  exact ⟨hr, by simpa [hr] using hl⟩
        · simp [getindexRanges, hb, hr] at h

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalRepairB

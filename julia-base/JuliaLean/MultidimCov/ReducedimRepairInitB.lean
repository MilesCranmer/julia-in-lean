import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReducedimRepairInitB

open JuliaLean.Registry

inductive Error where
  | dimensionMismatch (message : String)
  | emptyReduction
  | source (id : Nat)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure ExtremaFlags where
  isNumber : Bool
  isNaN : Bool
  unordered : Bool
  numericType : Bool
  hasOrderedValue : Bool
  deriving Repr, DecidableEq

def extremaInit (reducedIndices : A → D → Result RI)
    (emptyReductionAxis : A → D → Result Bool) (view : A → RI → Result S)
    (isEmptySlice : S → Result Bool) (mapEmpty : F → S → Result R)
    (mapreduce : F → Opposite → S → Result V) (flags : V → ExtremaFlags)
    (nanReplacement numericExtreme filteredReduction : V → Result V)
    (targetType : F → A → V → Result T) (allocate : A → D → V → T → Result R)
    (function : F) (opposite : Opposite) (array : A) (region : D) : Result R :=
  match reducedIndices array region with
  | .error error => .error error
  | .ok reduced => match emptyReductionAxis array region with
    | .error error => .error error
    | .ok true => .error .emptyReduction
    | .ok false => match view array reduced with
      | .error error => .error error
      | .ok slice => match isEmptySlice slice with
        | .error error => .error error
        | .ok true => mapEmpty function slice
        | .ok false => match mapreduce function opposite slice with
          | .error error => .error error
          | .ok initial =>
              let state := flags initial
              let adjusted := if state.isNumber && state.isNaN then nanReplacement initial
                else if state.unordered && state.numericType then numericExtreme initial
                else if state.unordered && state.hasOrderedValue then filteredReduction initial
                else .ok initial
              match adjusted with
              | .error error => .error error
              | .ok value => match targetType function array value with
                | .error error => .error error
                | .ok target => allocate array region value target

def extremaPairInit (reducedIndices : A → D → Result RI)
    (emptyReductionAxis : A → D → Result Bool) (view : A → RI → Result S)
    (isEmptySlice : S → Result Bool) (mapEmpty : F → S → Result R)
    (mapreduceReverse : F → S → Result V) (flags : V → ExtremaFlags)
    (nanReplacement numericExtreme filteredReduction : V → Result V)
    (targetType : F → A → V → Result T) (allocate : A → D → V → T → Result R)
    (function : F) (array : A) (region : D) : Result R :=
  match reducedIndices array region with
  | .error error => .error error
  | .ok reduced => match emptyReductionAxis array region with
    | .error error => .error error
    | .ok true => .error .emptyReduction
    | .ok false => match view array reduced with
      | .error error => .error error
      | .ok slice => match isEmptySlice slice with
        | .error error => .error error
        | .ok true => mapEmpty function slice
        | .ok false => match mapreduceReverse function slice with
          | .error error => .error error
          | .ok initial =>
              let state := flags initial
              let adjusted := if state.isNumber && state.isNaN then nanReplacement initial
                else if state.unordered && state.numericType then numericExtreme initial
                else if state.unordered && state.hasOrderedValue then filteredReduction initial
                else .ok initial
              match adjusted with
              | .error error => .error error
              | .ok value => match targetType function array value with
                | .error error => .error error
                | .ok target => allocate array region value target

def absMaximumInit (zeroType : T → Result X) (function : X → Result Y)
    (zeroValue : Y → Result Y) (realtype : F → T → Result RT)
    (allocate : A → D → Y → RT → Result R) (f : F) (array : A)
    (dispatchedType : T) (region : D) : Result R :=
  match zeroType dispatchedType with
  | .error error => .error error
  | .ok zero => match function zero with
    | .error error => .error error
    | .ok mapped => match zeroValue mapped with
      | .error error => .error error
      | .ok initial => match realtype f dispatchedType with
        | .error error => .error error
        | .ok target => allocate array region initial target

def constantInit (allocate : A → D → Bool → Result R)
    (array : A) (region : D) (identity : Bool) := allocate array region identity

def specializedInit (elementType : A → Result T) (innerIdentity : T → Result X)
    (function : X → Result Y) (outerIdentity : Y → Result Y)
    (operator : Y → Y → Result Y) (allocate : A → D → Y → Result R)
    (array : A) (region : D) : Result R :=
  match elementType array with
  | .error error => .error error
  | .ok type => match innerIdentity type with
    | .error error => .error error
    | .ok inner => match function inner with
      | .error error => .error error
      | .ok mapped => match outerIdentity mapped with
        | .error error => .error error
        | .ok identity => match operator identity identity with
          | .error error => .error error
          | .ok initial => allocate array region initial

inductive IndexStyle where | linear | cartesian deriving Repr, DecidableEq
def hasFastLinearIndexing (indexStyle : A → Result IndexStyle) (array : A) : Result Bool :=
  match indexStyle array with
  | .error error => .error error
  | .ok style => .ok (style = .linear)

structure Axis where
  first : Int
  last : Int
  deriving Repr, DecidableEq

def Axis.length (axis : Axis) : Nat := if axis.last < axis.first then 0 else (axis.last - axis.first + 1).toNat

def checkReducedimsLoop : List Axis → List Axis → Nat → Bool → Result Nat
  | [], [], leading, _ => .ok leading
  | [], _ :: _, _, _ => .error (.source 1)
  | resultAxis :: resultAxes, arrayAxis :: arrayAxes, leading, hadNonreduced =>
      if resultAxis.length = 1 then
        let nextLeading := if arrayAxis.length > 1 then
          if hadNonreduced then 0 else leading * arrayAxis.length else leading
        checkReducedimsLoop resultAxes arrayAxes nextLeading hadNonreduced
      else if resultAxis = arrayAxis then
        checkReducedimsLoop resultAxes arrayAxes leading true
      else .error (.dimensionMismatch "reduction on array with incompatible indices")
  | _ :: _, [], _, _ => .error (.source 2)

def checkReducedims (resultAxes arrayAxes : List Axis) : Result Nat :=
  if resultAxes.length > arrayAxes.length then
    .error (.dimensionMismatch ("cannot reduce " ++ toString arrayAxes.length ++
      "-dimensional array to " ++ toString resultAxes.length ++ " dimensions"))
  else checkReducedimsLoop resultAxes arrayAxes 1 false

def Contract : Prop :=
  (∀ {A D RI S F Opposite R V T : Type} reduced emptyAxis view isEmpty mapEmpty mapreduce flags nan numeric filtered target allocate f opposite array region output,
    extremaInit (A := A) (D := D) (RI := RI) (S := S) (F := F) (Opposite := Opposite)
      (R := R) (V := V) (T := T) reduced emptyAxis view isEmpty mapEmpty mapreduce flags
      nan numeric filtered target allocate f opposite array region = .ok output →
      ∃ reducedAxes, reduced array region = .ok reducedAxes ∧ emptyAxis array region = .ok false) ∧
  (∀ {A D RI S F R V T : Type} reduced emptyAxis view isEmpty mapEmpty mapreduce flags nan numeric filtered target allocate f array region output,
    extremaPairInit (A := A) (D := D) (RI := RI) (S := S) (F := F) (R := R)
      (V := V) (T := T) reduced emptyAxis view isEmpty mapEmpty mapreduce flags nan numeric
      filtered target allocate f array region = .ok output →
      ∃ reducedAxes, reduced array region = .ok reducedAxes ∧ emptyAxis array region = .ok false) ∧
  (∀ {A D T X Y F RT R : Type} zeroType function zeroValue realtype allocate f array dispatched region output,
    absMaximumInit (A := A) (D := D) (T := T) (X := X) (Y := Y) (F := F) (RT := RT) (R := R)
      zeroType function zeroValue realtype allocate f array dispatched region = .ok output →
      ∃ zero mapped initial target, zeroType dispatched = .ok zero ∧ function zero = .ok mapped ∧
        zeroValue mapped = .ok initial ∧ realtype f dispatched = .ok target ∧
        allocate array region initial target = .ok output) ∧
  (∀ {A D R : Type} allocate array region identity,
    constantInit (A := A) (D := D) (R := R) allocate array region identity =
      allocate array region identity) ∧
  (∀ {A D T X Y R : Type} elementType inner function outer operator allocate array region output,
    specializedInit (A := A) (D := D) (T := T) (X := X) (Y := Y) (R := R)
      elementType inner function outer operator allocate array region = .ok output →
      ∃ type innerValue mapped identity initial,
        elementType array = .ok type ∧ inner type = .ok innerValue ∧ function innerValue = .ok mapped ∧
        outer mapped = .ok identity ∧ operator identity identity = .ok initial ∧
        allocate array region initial = .ok output) ∧
  (∀ {A : Type} indexStyle array output,
    hasFastLinearIndexing (A := A) indexStyle array = .ok output →
      ∃ style, indexStyle array = .ok style ∧ output = decide (style = .linear)) ∧
  (∀ resultAxes arrayAxes leading,
    checkReducedims resultAxes arrayAxes = .ok leading → resultAxes.length ≤ arrayAxes.length)

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, ?_, fun _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro A D RI S F Opposite R V T reduced emptyAxis view isEmpty mapEmpty mapreduce flags nan numeric filtered target allocate f opposite array region output h
    cases hr : reduced array region with
    | error error => simp [extremaInit, hr] at h
    | ok reducedAxes =>
      cases he : emptyAxis array region with
      | error error => simp [extremaInit, hr, he] at h
      | ok empty =>
        cases empty
        · exact ⟨reducedAxes, rfl, rfl⟩
        · simp [extremaInit, hr, he] at h
  · intro A D RI S F R V T reduced emptyAxis view isEmpty mapEmpty mapreduce flags nan numeric filtered target allocate f array region output h
    cases hr : reduced array region with
    | error error => simp [extremaPairInit, hr] at h
    | ok reducedAxes =>
      cases he : emptyAxis array region with
      | error error => simp [extremaPairInit, hr, he] at h
      | ok empty =>
        cases empty
        · exact ⟨reducedAxes, rfl, rfl⟩
        · simp [extremaPairInit, hr, he] at h
  · intro A D T X Y F RT R zeroType function zeroValue realtype allocate f array dispatched region output h
    cases hz : zeroType dispatched with
    | error error => simp [absMaximumInit, hz] at h
    | ok zero =>
      cases hf : function zero with
      | error error => simp [absMaximumInit, hz, hf] at h
      | ok mapped =>
        cases hi : zeroValue mapped with
        | error error => simp [absMaximumInit, hz, hf, hi] at h
        | ok initial =>
          cases ht : realtype f dispatched with
          | error error => simp [absMaximumInit, hz, hf, hi, ht] at h
          | ok target => exact ⟨zero, mapped, initial, target, rfl, hf, hi, rfl,
              by simpa [absMaximumInit, hz, hf, hi, ht] using h⟩
  · intro A D T X Y R elementType inner function outer operator allocate array region output h
    cases he : elementType array with
    | error error => simp [specializedInit, he] at h
    | ok type =>
      cases hi : inner type with
      | error error => simp [specializedInit, he, hi] at h
      | ok innerValue =>
        cases hf : function innerValue with
        | error error => simp [specializedInit, he, hi, hf] at h
        | ok mapped =>
          cases ho : outer mapped with
          | error error => simp [specializedInit, he, hi, hf, ho] at h
          | ok identity =>
            cases hp : operator identity identity with
            | error error => simp [specializedInit, he, hi, hf, ho, hp] at h
            | ok initial => exact ⟨type, innerValue, mapped, identity, initial,
                rfl, hi, hf, ho, hp, by simpa [specializedInit, he, hi, hf, ho, hp] using h⟩
  · intro A indexStyle array output h
    cases hs : indexStyle array with
    | error error => simp [hasFastLinearIndexing, hs] at h
    | ok style => exact ⟨style, rfl, by simpa [hasFastLinearIndexing, hs] using h.symm⟩
  · intro resultAxes arrayAxes leading h
    by_cases hr : resultAxes.length > arrayAxes.length
    · simp [checkReducedims, hr] at h
    · omega

def entries : List Entry := []

end JuliaLean.MultidimCov.ReducedimRepairInitB

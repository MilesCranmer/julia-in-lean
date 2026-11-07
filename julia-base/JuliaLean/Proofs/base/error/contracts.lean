import JuliaLean.base.error


namespace JuliaLean.ErrorShow


def CurrentExceptionStackExact : Prop :=
  (∀ rawNewestFirst : List String,
    currentExceptions rawNewestFirst = rawNewestFirst.reverse) ∧
  (∀ rootToCurrent : List String,
    applyExceptionAction rootToCurrent .rethrowCurrent = rootToCurrent) ∧
  (∀ rootToCurrent : List String, ∀ exception : String,
    applyExceptionAction rootToCurrent (.throwNew exception) = rootToCurrent ++ [exception]) ∧
  (∀ prior : List String, ∀ current replacement : String,
    applyExceptionAction (prior ++ [current]) (.rethrowOther replacement) =
      prior ++ [replacement])

def AssertMessageConstruction : Prop := ∀ conditionText rendered : String,
  assertResult false (.default conditionText) = some ("AssertionError: " ++ conditionText) ∧
    assertResult false (.supplied rendered) = some ("AssertionError: " ++ rendered) ∧
    assertResult true (.supplied rendered) = none

theorem currentExceptionStackExact_proven : CurrentExceptionStackExact := by
  constructor
  · intro rawNewestFirst
    rfl
  constructor
  · intro rootToCurrent
    rfl
  constructor
  · intro rootToCurrent exception
    rfl
  · intro prior current replacement
    simp [applyExceptionAction]

theorem assertMessageConstruction_proven : AssertMessageConstruction := by
  intro conditionText rendered
  simp [assertResult, AssertMessage.text]

end JuliaLean.ErrorShow

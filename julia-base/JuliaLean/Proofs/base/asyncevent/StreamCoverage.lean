import JuliaLean.base.asyncevent

namespace JuliaLean.Streams

open JuliaLean

def AsyncConstructionCoverage : Prop := ∀ timeout interval kind,
  timerSetup timeout interval =
    { timeoutMs := ceilMillis timeout + if timeout = 0 then 0 else 1,
      intervalMs := ceilMillis interval } ∧
  timerTimeout (timerSetup timeout interval) =
    (if (timerSetup timeout interval).timeoutMs = 0 then 0
     else (timerSetup timeout interval).timeoutMs - 1) ∧
  timerProperties (timerSetup timeout interval) =
    (timerTimeout (timerSetup timeout interval), (timerSetup timeout interval).intervalMs) ∧
  timerShowState (freshEvent .oneShotTimer) = "open" ∧
  callbackShouldContinue (freshEvent .asyncCondition) = false ∧
  freshEvent kind = ⟨kind, true, false⟩

def AsyncUtilityCoverage : Prop := ∀ tests polls timeout armed,
  timedwaitResult tests polls = (tests.take (polls + 1)).any id ∧
  timeoutEnqueue ⟨timeout, armed⟩ = ⟨timeout, true⟩ ∧
  timeoutDequeue ⟨timeout, armed⟩ = ⟨timeout, false⟩ ∧
  (sleepFinalState (freshEvent .oneShotTimer)).isopen = false

theorem asyncConstructionCoverage_proven : AsyncConstructionCoverage := by
  simp [AsyncConstructionCoverage, timerSetup, timerTimeout, timerProperties,
    timerShowState, callbackShouldContinue, freshEvent]
theorem asyncUtilityCoverage_proven : AsyncUtilityCoverage := by
  simp [AsyncUtilityCoverage, timedwaitResult, timeoutEnqueue, timeoutDequeue,
    sleepFinalState, freshEvent, closeEvent]

end JuliaLean.Streams

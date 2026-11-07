import JuliaLean.base.process

namespace JuliaLean.Streams

/-- `success` is true exactly for an exited process with exit code zero and no
terminating signal; a positive signal is reported as that exact signal. -/
def ProcessStatusExact : Prop := ∀ p,
  (testSuccess p = true ↔
    p.exited = true ∧ p.exitcode.val = 0 ∧ p.termsignal.val = 0) ∧
  (p.exited = true → p.termsignal.val > 0 →
    processStatus p = .signaled p.termsignal.val)

/-- `ProcessFailedException` contains exactly the failed, non-ignored
processes, in pipeline order. -/
def ProcessFailureContents : Prop := ∀ ps,
  failedProcesses ps ≠ [] →
  pipelineError ps = .error (.processFailed ((failedProcesses ps).map (·.id)))

/-- `run` and `read(cmd)` use the same exit-status check, and a successful
read returns exactly the captured bytes. -/
def RunReadStatusHandling : Prop := ∀ ps output,
  (runResult ps = .ok () → readCommand output ps = .ok output) ∧
  (∀ err, runResult ps = .error err → readCommand output ps = .error err)

/-- `kill` is a no-op after exit; otherwise the exit callback reports the exact
positive signal and a zero exit code. -/
def KillReportsSignal : Prop := ∀ p signal,
  (p.exited = true → killProcess p signal = p) ∧
  (p.exited = false → signal.val > 0 →
    (killProcess p signal).exitcode.val = 0 ∧
    processStatus (killProcess p signal) = .signaled signal.val)

theorem processStatusExact_proven : ProcessStatusExact := by
  intro p
  constructor
  · simp [testSuccess, Bool.and_eq_true, and_assoc]
  · intro hex hsig
    simp [processStatus, hex, hsig]

theorem processFailureContents_proven : ProcessFailureContents := by
  intro ps hne
  unfold pipelineError
  cases hfailed : failedProcesses ps with
  | nil => exact False.elim (hne hfailed)
  | cons p rest => rfl

theorem runReadStatusHandling_proven : RunReadStatusHandling := by
  intro ps output
  constructor
  · intro h
    simp [readCommand, h]
  · intro err h
    simp [readCommand, h]

theorem killReportsSignal_proven : KillReportsSignal := by
  intro p signal
  have hzero : (JInt.lit .i64 0).val = 0 := by decide
  constructor
  · intro hex
    simp [killProcess, hex]
  · intro hex hsignal
    simp [killProcess, hex, processStatus, hsignal, hzero]

end JuliaLean.Streams

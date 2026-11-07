import JuliaLean.base.process

namespace JuliaLean.Streams

open JuliaLean

def ProcessSpawnCoverage : Prop := ∀ cmd hasStdin hasStdout hasStderr p code signal cpus size,
  spawnModel cmd hasStdin hasStdout hasStderr =
    (let leaves := commandLeaves cmd
     if leaves.any (fun c => c.exec.isEmpty) then .error .argumentError
     else .ok ⟨leaves, hasStdin, hasStdout, hasStderr⟩) ∧
  (processExitCallback p code signal).exitcode = code ∧
  (processExitCallback p code signal).termsignal = signal ∧
  cpuMask cpus size = ((List.range size).map fun i => decide ((i + 1) ∈ cpus)) ∧
  ∀ id ignored, (processCtor id ignored).exited = false

def ProcessStdioCoverage : Prop := ∀ (α : Type) (stdios : List α) fd replacement default kind readable,
  stdioCopy stdios fd replacement default =
    (stdios ++ List.replicate (fd - stdios.length) default).set (fd - 1) replacement ∧
  setupStdio kind readable = (match kind with
    | .pipeEndpoint | .pipe => (readable, true)
    | .ioStream => (readable, false)
    | .fileRedirect | .generic => (readable, true))

def ProcessOpenCoverage : Prop := ∀ mode read write,
  parseProcessMode mode = (match mode with
    | "r" => some .read | "w" => some .write
    | "r+" | "w+" => some .readWrite | _ => none) ∧
  processOpenMode read write =
    (if read && write then .readWrite else if read then .read else if write then .write else .none) ∧
  openDoOutcome true true true = .returned ∧
  openDoOutcome false true true = .bodyError

def ProcessSequenceCoverage : Prop := ∀ ps p cmd pid i,
  processWaitAll ps = ps.all (·.exited) ∧
  processRunningAny ps = ps.any (fun p => !p.exited) ∧
  processExitedAll ps = ps.all (·.exited) ∧
  processSignaled p = decide (p.termsignal.val > 0) ∧
  cmdExecLength cmd = cmd.exec.length ∧ cmdExecAt cmd i = cmd.exec[i]? ∧
  processPid p pid = if p.exited || pid ≤ 0 then .error .ioError else .ok pid

theorem processSpawnCoverage_proven : ProcessSpawnCoverage := by
  simp [ProcessSpawnCoverage, spawnModel, processCtor, processExitCallback, cpuMask]
theorem processStdioCoverage_proven : ProcessStdioCoverage := by
  unfold ProcessStdioCoverage
  intros
  exact ⟨rfl, rfl⟩
theorem processOpenCoverage_proven : ProcessOpenCoverage := by
  unfold ProcessOpenCoverage
  intros
  exact ⟨rfl, rfl, rfl, rfl⟩
theorem processSequenceCoverage_proven : ProcessSequenceCoverage := by
  simp [ProcessSequenceCoverage, processWaitAll, processRunningAny, processExitedAll,
    processSignaled, cmdExecLength, cmdExecAt, processPid]

end JuliaLean.Streams

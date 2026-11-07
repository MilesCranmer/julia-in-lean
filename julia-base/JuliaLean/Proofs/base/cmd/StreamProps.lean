import JuliaLean.base.cmd

namespace JuliaLean.Streams

/-- Multi-stage pipelines associate from the left. -/
def PipelineLeftAssociative : Prop := ∀ a b c rest,
  pipelineMany a (b :: c :: rest) = pipelineMany (.stdoutPipe (.stdoutPipe a b) c) rest

/-- `ignorestatus(command)` accepts every command object. -/
def IgnoreStatusAllCommands : Prop := ∀ command,
  ∃ marked, ignoreStatus command = .ok marked

/-- `detach(::Cmd)` changes only the detached flag. -/
def DetachSetsFlag : Prop := ∀ cmd,
  (detachCmd cmd).flags = cmd.flags ||| detachedFlag ∧
  (detachCmd cmd).exec = cmd.exec ∧
  (detachCmd cmd).env = cmd.env ∧
  (detachCmd cmd).ignorestatus = cmd.ignorestatus

/-- `detach(command)` accepts every command object that `run` accepts. -/
def DetachAllCommands : Prop := ∀ command,
  ∃ detached, detachCommand command = .ok detached

theorem pipelineLeftAssociative_proven : PipelineLeftAssociative := by
  intro a b c rest
  rfl

theorem detachSetsFlag_proven : DetachSetsFlag := by
  intro cmd
  simp [detachCmd]

/-- `pipeline(cmd; stderr=othercmd)` constructs `ErrOrCmds`, for which master
defines no `ignorestatus` method. -/
theorem ignoreStatusAllCommands_refuted : ¬ IgnoreStatusAllCommands := by
  intro h
  let cmd : CommandM := .leaf (JuliaLean.ShellCmd.cmdOf [])
  obtain ⟨marked, hm⟩ := h (.stderrPipe cmd cmd)
  simp [ignoreStatus] at hm

/-- A two-command stdout pipeline is `OrCmds`, while master defines `detach`
only for a leaf `Cmd`. -/
theorem detachAllCommands_refuted : ¬ DetachAllCommands := by
  intro h
  let cmd : CommandM := .leaf (JuliaLean.ShellCmd.cmdOf [])
  obtain ⟨detached, hm⟩ := h (.stdoutPipe cmd cmd)
  simp [detachCommand] at hm

end JuliaLean.Streams

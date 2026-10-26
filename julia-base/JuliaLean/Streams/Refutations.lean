import JuliaLean.Streams.Props

namespace JuliaLean.Streams

/-- A closed writable-mode IOStream has `iswritable == true`, and both byte and
bulk writes return zero instead of throwing. -/
theorem closedIOStreamWriteErrors_refuted : ¬ ClosedIOStreamWriteErrors := by
  intro h
  have bad := h (closeStream (freshStream .ioStream)) [1] rfl (by decide) (by decide)
  have hw := bad.1
  simp [closeStream, freshStream, isWritable] at hw

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

import JuliaLean.Streams.Props

namespace JuliaLean.Streams

/-- Closed IOStreams reject writes. -/
theorem closedIOStreamWriteErrors_proven : ClosedIOStreamWriteErrors := by
  intro s bytes hk ho _
  have hw : isWritable s = false := by simp [isWritable, hk, ho]
  refine ⟨hw, .argumentError, ?_⟩
  simp [writeBytes, unsafeWrite, hk, hw]

/-- Prior master checked only the ios writable access bit after close. -/
def legacyIsWritable (s : StreamM) : Bool :=
  if s.kind = .ioStream then s.writable else isWritable s

def LegacyClosedIOStreamWriteErrors : Prop := ∀ s,
  s.kind = .ioStream → isOpen s = false → legacyIsWritable s = false

theorem closedIOStreamWriteErrors_refuted : ¬ LegacyClosedIOStreamWriteErrors := by
  intro h
  have bad := h (closeStream (freshStream .ioStream)) rfl (by decide)
  simp [legacyIsWritable, closeStream, freshStream] at bad

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

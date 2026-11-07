import JuliaLean.base.iostream
import JuliaLean.base.stream

namespace JuliaLean.Streams

/-- A closed IOStream is not writable and a nonempty write raises an error. -/
def ClosedIOStreamWriteErrors : Prop := ∀ s bytes,
  s.kind = .ioStream → isOpen s = false → bytes ≠ [] →
  isWritable s = false ∧ ∃ err, writeBytes s bytes = .error err

/-- Closed IOStreams reject writes. -/
theorem closedIOStreamWriteErrors_proven : ClosedIOStreamWriteErrors := by
  intro s bytes hk ho _
  have hw : isWritable s = false := by simp [isWritable, hk, ho]
  refine ⟨hw, .argumentError, ?_⟩
  simp [writeBytes, unsafeWrite, hk, hw]

def LegacyClosedIOStreamWriteErrors : Prop := ∀ s,
  s.kind = .ioStream → isOpen s = false → legacyIsWritable s = false

theorem closedIOStreamWriteErrors_refuted : ¬ LegacyClosedIOStreamWriteErrors := by
  intro h
  have bad := h (closeStream (freshStream .ioStream)) rfl (by decide)
  simp [legacyIsWritable, closeStream, freshStream] at bad

end JuliaLean.Streams

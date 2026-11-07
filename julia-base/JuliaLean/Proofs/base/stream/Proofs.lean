import JuliaLean.Proofs.base.stream.Props

namespace JuliaLean.Streams

theorem writeReadFIFO_proven : WriteReadFIFO := by
  intro kind bytes hk
  rcases hk with rfl | rfl <;>
    simp [freshStream, freshPipe, pipeWrite, closePipeWrite, writeBytes,
      unsafeWrite, isWritable, isOpen, closeStream, readAvailable]

theorem unsafeLengthsExact_proven : UnsafeLengthsExact := by
  constructor
  · intro kind memory n hn
    have hnot : ¬n > memory.length := Nat.not_lt_of_ge hn
    cases kind <;>
      simp [freshStream, unsafeWrite, hnot, isWritable, isOpen]
  · intro s n hn
    simp [unsafeRead, hn]

theorem readAvailableExact_proven : ReadAvailableExact := by
  intro s
  rfl

theorem splitUntil_reconstruct (delim : UInt8) (bytes : List UInt8) :
    let r := splitUntil delim bytes
    r.before ++ (if r.found then delim :: r.after else []) = bytes := by
  induction bytes with
  | nil => simp [splitUntil]
  | cons b bs ih =>
      by_cases h : b = delim
      · simp [splitUntil, h]
      · simp [splitUntil, h]
        exact ih

theorem delimiterHandling_proven : DelimiterHandling := by
  intro s delim keep
  dsimp
  refine ⟨splitUntil_reconstruct delim s.buffer, ?_, ?_⟩
  · rfl
  · rfl

theorem closedReadsStayClosed_proven : ClosedReadsStayClosed := by
  rintro ⟨kind, status, buffer, writable⟩ n delim keep hs
  change status = .closed at hs
  subst status
  by_cases hn : n ≤ buffer.length <;>
    simp [unsafeRead, hn, readAvailable, readUntil, readLine]

theorem closeMonotone_proven : CloseMonotone := by
  intro s
  simp [closeStream, isOpen, streamEof]

theorem closedLibuvWritesError_proven : ClosedLibuvWritesError := by
  intro kind bytes hk
  rcases hk with rfl | rfl <;>
    simp [writeBytes, unsafeWrite, freshStream, closeStream, isWritable, isOpen]




end JuliaLean.Streams

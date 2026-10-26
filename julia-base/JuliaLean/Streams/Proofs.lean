import JuliaLean.Streams.Props

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

theorem eventCloseIdempotent_proven : EventCloseIdempotent := by
  intro e
  simp [closeEvent, signalEvent, waitEvent]

theorem oneShotWaitPersistent_proven : OneShotWaitPersistent := by
  rintro ⟨kind, isopen, set⟩ hk hopen hset
  change kind = .oneShotTimer at hk
  change isopen = true at hopen
  change set = false at hset
  subst kind
  cases isopen <;> cases set <;> simp_all [signalEvent, waitEvent]

theorem pendingEventSurvivesClose_proven : PendingEventSurvivesClose := by
  intro kind hk
  rcases hk with rfl | rfl <;>
    simp [freshEvent, signalEvent, closeEvent, waitEvent]

theorem pipelineLeftAssociative_proven : PipelineLeftAssociative := by
  intro a b c rest
  rfl

theorem detachSetsFlag_proven : DetachSetsFlag := by
  intro cmd
  simp [detachCmd]

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

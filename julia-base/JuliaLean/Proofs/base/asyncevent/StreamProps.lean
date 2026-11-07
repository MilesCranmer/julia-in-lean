import JuliaLean.base.asyncevent

namespace JuliaLean.Streams

/-- Closing a Timer or AsyncCondition is idempotent and later notifications
cannot reactivate it. A closed object without a pending event makes `wait`
throw EOFError. -/
def EventCloseIdempotent : Prop := ∀ e,
  closeEvent (closeEvent e) = closeEvent e ∧
  (closeEvent e).isopen = false ∧
  signalEvent (closeEvent e) = closeEvent e ∧
  (e.set = false → waitEvent (closeEvent e) = .error .eofError)

/-- Once a one-shot timer has fired, every subsequent wait returns immediately,
including after the timer has become inactive. -/
def OneShotWaitPersistent : Prop :=
  ∀ e, e.kind = .oneShotTimer → e.isopen = true → e.set = false →
    let fired := signalEvent e
    fired.isopen = false ∧ fired.set = true ∧
    waitEvent fired = .ok fired ∧
    (match waitEvent fired with | .ok after => waitEvent after = .ok after | .error _ => False)

/-- An event already set before close can be observed one final time, matching
the callback documentation. -/
def PendingEventSurvivesClose : Prop := ∀ kind,
  kind = .repeatingTimer ∨ kind = .asyncCondition →
  let pending := closeEvent (signalEvent (freshEvent kind))
  ∃ after, waitEvent pending = .ok after ∧ after.isopen = false

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

end JuliaLean.Streams

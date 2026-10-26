import JuliaLean.ConcurrencyCov.Park

/-! Properties of `base/park.jl`. -/

namespace JuliaLean.ConcurrencyCov.Park

open JuliaLean.ConcurrencyCov

/-- The waitable protocol dispatches source and watcher operations to sticky
source registrations, object operations to their object slots, and the generic
defaults to no recheck (`base/park.jl:59-180,306-382`). -/
def WaitableProtocolSpec : Prop :=
  (∀ src floor w first, waitEnqueue (.source src floor) w first = sourceWaitEnqueue src w floor) ∧
  (∀ src floor w first, waitEnqueue (.watcher src floor) w first =
    sourceWaitEnqueue src w (WATCHER_BIT ||| max floor SAFE)) ∧
  (∀ src floor w s, waitRecheck (.source src floor) w s =
    (s.srcState src ≠ 0 && s.srcState src ≥ floor)) ∧
  (∀ src floor w s, waitRecheck (.watcher src floor) w s =
    decide (s.srcState src ≥ max floor SAFE)) ∧
  (∀ o w s, waitRecheck (.obj o false) w s = false) ∧
  (∀ src floor w why s, waitDequeue (.source src floor) w why s = s) ∧
  (∀ src floor w why s, waitDequeue (.watcher src floor) w why s = s) ∧
  (∀ src, watcherWait src = .watcher src SAFE) ∧
  (∀ (α β : Type) (f : α → β) x, uncancellableLock f x = f x)

theorem waitableProtocolSpec_proven : WaitableProtocolSpec := by
  exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl⟩

/-- Wait-entry selection uses the specialized one- and two-slot constructors,
preserves cached entries, and disarms only the entry currently stored in
`waiting_on` (`base/park.jl:90-106,370-373`). -/
def WaitEntrySpec : Prop :=
  (∀ src, acquireWaitEntry [.watcher src SAFE] true = newEntry 1) ∧
  (∀ src gov, acquireWaitEntry [.watcher src SAFE, .source gov SAFE] true = newEntry 2) ∧
  (∀ src floor, acquireWaitEntry [.source src floor] true = cachedWaitEntry) ∧
  (∀ o recheck, acquireWaitEntry [.obj o recheck] true = cachedWaitEntry) ∧
  (∀ src1 floor1 src2 floor2,
    acquireWaitEntry [.source src1 floor1, .source src2 floor2] true = cancelWaitEntry src2 floor2) ∧
  (∀ o recheck src floor,
    acquireWaitEntry [.obj o recheck, .source src floor] true = cancelWaitEntry src floor) ∧
  (∀ ws, acquireWaitEntry ws false = newEntry ws.length) ∧
  (∀ w s, s.cachedWait = some w → releaseWaitEntry w s = s) ∧
  (∀ w s, s.cachedCancel = some w → releaseWaitEntry w s = s) ∧
  (∀ w s, disarm w s =
    if s.waitingOn = some w then (true, { s with waitingOn := none }) else (false, s))

theorem waitEntrySpec_proven : WaitEntrySpec := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun ws => ?_, ?_, ?_, fun _ _ => rfl⟩
  · cases ws <;> rfl
  · intro w s h
    simp [releaseWaitEntry, h]
  · intro w s h
    simp [releaseWaitEntry, h]

/-- The recursive tuple/iterator helpers stop at the first fired waitable and
dequeue every registered waitable in source order (`base/park.jl:146-180`). -/
def WaitLoopSpec : Prop :=
  (∀ w first, enqueueUntilFired [] w first = pure none) ∧
  (∀ w s, recheckUntilFired [] w s = none) ∧
  (∀ w why s, dequeueEach [] w why s = s) ∧
  (∀ x xs w s, recheckUntilFired (x :: xs) w s =
    if waitRecheck x w s then some x else recheckUntilFired xs w s) ∧
  (∀ x xs w why s, dequeueEach (x :: xs) w why s =
    dequeueEach xs w why (waitDequeue x w why s))

theorem waitLoopSpec_proven : WaitLoopSpec := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- Parking arms before registration, self-claims after the recheck, returns
`true` when no waitable fired, and cleanup always removes the sticky-queue mark
(`base/park.jl:132-301`). -/
def ParkDriverSpec : Prop :=
  (∀ ws w first claimed, park ws w first claimed = do
    armWait w
    let fx ← enqueueUntilFired ws w first
    let s ← get
    let fx := if fx.isNone then recheckUntilFired ws w s else fx
    modify (claim claimed w)
    match fx with
    | some x =>
      let s ← get
      let (won, s) := disarm w s
      set s
      if won then
        modify (waitDequeue x w WAKE_FIRED)
        return false
      return true
    | none => return true) ∧
  (∀ ws w claimed, repark ws w claimed = do
    armWait w
    let s ← get
    let fx := recheckUntilFired ws w s
    modify (claim claimed w)
    match fx with
    | some x =>
      let s ← get
      let (won, s) := disarm w s
      set s
      if won then
        modify (waitDequeue x w WAKE_FIRED)
        return false
      return true
    | none => return true) ∧
  (∀ w why s, withdraw [] w why s = releaseWaitEntry w s) ∧
  (∀ ws w nested s e,
    waitSafeInterrupt ws w (.error e) nested s =
      (.error e, interruptedParkCleanup ws w nested s)) ∧
  (∀ ws w nested s r, waitSafeInterrupt ws w (.ok r) nested s = (.ok r, s))

theorem parkDriverSpec_proven : ParkDriverSpec := by
  exact ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- Waiting for a token under that same token is rejected before any state
change; already-cancelled tokens return their severity before parking
(`base/park.jl:400-429`). -/
def WaitTokenSpec : Prop :=
  ∀ src gov claimed wake nested, waitToken src gov claimed wake nested = do
    if gov = some src then
      throwE (.argumentError ("cannot wait for a token's cancellation under the same governing token; " ++
        "pass `cancel = nothing` to wait for it unconditionally"))
    match gov with | some g => checkcancel g | none => pure ()
    let s ← get
    let st := s.srcState src
    if st ≠ 0 then return st
    let ws := match gov with | none => [watcherWait src] | some g => [watcherWait src, .source g SAFE]
    let w ← acquireWaitEntry ws true
    let parked ← park ws w true claimed
    if !parked then
      modify (withdraw ws w WAKE_FIRED)
      let s ← get
      let st := s.srcState src
      if st ≠ 0 then return st
      match gov with | some g => checkcancel g | none => throwE .typeError
      throwE (.errorException "cancellation wait fired with no cancellation")
    let r ← waitSafeInterrupt ws w wake nested
    modify (withdraw ws w WAKE_VALUE)
    return r

theorem waitTokenSpec_proven : WaitTokenSpec := by
  intro src gov claimed wake nested
  rfl

end JuliaLean.ConcurrencyCov.Park

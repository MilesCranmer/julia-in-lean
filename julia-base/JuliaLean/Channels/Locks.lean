import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.Channels

/-- Julia ErrorException; its messages distinguish the checks in base/lock.jl. -/
inductive LockError where
  | errorException (message : String)
  deriving DecidableEq

/-- Ownership and the locked bit of `base/lock.jl:143-179`; the recursion count is UInt32. -/
structure LockState where
  lockedBy : Option Nat := none
  reentrancy_cnt : JInt .u32 := JInt.lit .u32 0
  islocked : Bool := false
  deriving DecidableEq

/-- `base/lock.jl:165-183`: reentrant increment, uncontended acquisition, or failure. -/
def lockTry (t : Nat) (s : LockState) : Bool × LockState :=
  if s.lockedBy = some t then
    (true, { s with reentrancy_cnt := s.reentrancy_cnt + JInt.lit .u32 1 })
  else if s.islocked then (false, s)
  else (true, { lockedBy := some t, reentrancy_cnt := JInt.lit .u32 1, islocked := true })

/-- `base/lock.jl:315-347`: the ownership check precedes every mutation.
Condition notification after releasing the locked bit does not change these fields. -/
def lockUnlock (t : Nat) (s : LockState) : Except LockError Unit × LockState :=
  if s.lockedBy ≠ some t then
    (.error (.errorException (if s.reentrancy_cnt.val = 0 then
      "unlock count must match lock count" else "unlock from wrong thread")), s)
  else
    let n := s.reentrancy_cnt - JInt.lit .u32 1
    (.ok (), if n.val = 0 then { lockedBy := none, reentrancy_cnt := n, islocked := false }
      else { s with reentrancy_cnt := n })

def LockUnlockNonowner : Prop := ∀ s t, s.lockedBy ≠ some t →
  ∃ msg, lockUnlock t s = (.error (.errorException msg), s)

theorem lockUnlockNonowner_proven : LockUnlockNonowner := by
  intro s t h
  refine ⟨if s.reentrancy_cnt.val = 0 then "unlock count must match lock count" else "unlock from wrong thread", ?_⟩
  simp [lockUnlock, h]

/-- Repeated owner-only `trylock`, `base/lock.jl:167-169`. -/
def reentrantCount (c : JInt .u32) : Nat → JInt .u32
  | 0 => c
  | n + 1 => reentrantCount c n + JInt.lit .u32 1

private theorem u32_wrap_add_one (x : Int) :
    JInt.wrap .u32 x + JInt.lit .u32 1 = JInt.wrap .u32 (x + 1) := by
  apply Subtype.ext
  change (x % 4294967296 + 1) % 4294967296 = (x + 1) % 4294967296
  omega

/-- Closed form of arbitrarily many UInt32 increments, without expanding the run. -/
theorem reentrantCount_closed (x : Int) (n : Nat) :
    reentrantCount (JInt.wrap .u32 x) n = JInt.wrap .u32 (x + (n : Int)) := by
  induction n with
  | zero => simp [reentrantCount]
  | succ n ih =>
    rw [reentrantCount, ih, u32_wrap_add_one]
    congr 1
    omega

/-- Owner-only acquisition trace, `base/lock.jl:165-179`; first acquisition sets one. -/
def lockAcquires (t : Nat) : Nat → LockState
  | 0 => {}
  | n + 1 => { lockedBy := some t, reentrancy_cnt := reentrantCount (JInt.lit .u32 1) n, islocked := true }

theorem lockAcquires_step (t n : Nat) :
    lockTry t (lockAcquires t n) = (true, lockAcquires t (n + 1)) := by
  cases n with
  | zero => simp [lockTry, lockAcquires, reentrantCount]
  | succ n => simp [lockTry, lockAcquires, reentrantCount]

/-- Owner-only `unlock` trace, `base/lock.jl:315-347`; errors retain the state. -/
def lockUnlocks (t : Nat) : Nat → LockState → LockState
  | 0, s => s
  | k + 1, s => lockUnlocks t k (lockUnlock t s).2

def LockReentrancyCount : Prop := ∀ t n k : Nat, 1 ≤ n → k < n →
  let s := lockUnlocks t k (lockAcquires t n)
  s.islocked = true ∧ s.lockedBy = some t

theorem lockReentrancyCount_refuted : ¬ LockReentrancyCount := by
  intro h
  have bad := h 0 4294967297 1 (by omega) (by omega)
  have count : reentrantCount (JInt.lit .u32 1) 4294967296 = JInt.lit .u32 1 := by
    rw [JInt.lit, reentrantCount_closed]
    decide
  simp only [lockUnlocks, lockAcquires, count] at bad
  have final : (lockUnlock 0 { lockedBy := some 0, reentrancy_cnt := JInt.lit .u32 1, islocked := true }).2.islocked = false := by decide
  exact Bool.noConfusion (final.symm.trans bad.1)

/-- Semaphore operations at `base/lock.jl:578-597,669-679`, with no cancellation. -/
inductive SemOp where
  | acquire | release
  deriving DecidableEq

/-- Remaining operations are a per-task program counter. Task identities are scheduler labels. -/
structure SemTask where
  id : Nat
  ops : List SemOp
  deriving DecidableEq

/-- `base/lock.jl:565-569`. Counts are natural numbers counting live permits/tasks;
`curr_cnt < sem_size` before increment prevents Julia Int overflow. Queue membership
records the wait/relock program counter; `woken` tasks have wake value `nothing`. -/
structure SemState where
  curr : Nat := 0
  ready : List SemTask := []
  parked : List SemTask := []
  woken : List SemTask := []
  deriving DecidableEq

/-- `Semaphore(sem_size)`, `base/lock.jl:569`, for positive Julia Int sizes. -/
def semInitial (inputs : List (List SemOp)) : SemState :=
  { ready := inputs.zipIdx |>.map (fun (ops, id) => ⟨id, ops⟩) }

/-- `base/lock.jl:669-679`: check, decrement, FIFO notification, and unlock.
The caller's continuation is advanced separately by `SemStep`. -/
def semRelease (s : SemState) : Except LockError Unit × SemState :=
  if s.curr = 0 then (.error (.errorException "release count must match acquire count"), s)
  else
    match s.parked with
    | [] => (.ok (), { s with curr := s.curr - 1 })
    | t :: ts => (.ok (), { s with curr := s.curr - 1, parked := ts, woken := s.woken ++ [t] })

/-- Atomic lock-protected sections, `base/lock.jl:580-595,670-677`.
Any ready task can run; a notified task reacquires in a separate later step.
Parking appends FIFO and releases the lock in the same step. -/
inductive SemStep (size : Nat) : SemState → SemState → Prop where
  | acquire {s pre post t ops} (ready : s.ready = pre ++ ⟨t, .acquire :: ops⟩ :: post)
      (free : s.curr < size) : SemStep size s
      { s with curr := s.curr + 1, ready := pre ++ ⟨t, ops⟩ :: post }
  | park {s pre post t ops} (ready : s.ready = pre ++ ⟨t, .acquire :: ops⟩ :: post)
      (full : size ≤ s.curr) : SemStep size s
      { s with ready := pre ++ post, parked := s.parked ++ [⟨t, .acquire :: ops⟩] }
  | reacquire {s pre post t ops} (wake : s.woken = pre ++ ⟨t, .acquire :: ops⟩ :: post)
      (free : s.curr < size) : SemStep size s
      { s with curr := s.curr + 1, woken := pre ++ post, ready := s.ready ++ [⟨t, ops⟩] }
  | repark {s pre post t ops} (wake : s.woken = pre ++ ⟨t, .acquire :: ops⟩ :: post)
      (full : size ≤ s.curr) : SemStep size s
      { s with woken := pre ++ post, parked := s.parked ++ [⟨t, .acquire :: ops⟩] }
  | releaseEmpty {s pre post t ops}
      (ready : s.ready = pre ++ ⟨t, .release :: ops⟩ :: post)
      (positive : 0 < s.curr) (empty : s.parked = []) : SemStep size s
      { s with curr := s.curr - 1, ready := pre ++ ⟨t, ops⟩ :: post }
  | releaseWake {s pre post t ops waiter waiters}
      (ready : s.ready = pre ++ ⟨t, .release :: ops⟩ :: post)
      (positive : 0 < s.curr) (queue : s.parked = waiter :: waiters) : SemStep size s
      { s with curr := s.curr - 1, ready := pre ++ ⟨t, ops⟩ :: post, parked := waiters, woken := s.woken ++ [waiter] }
  | releaseError {s pre post t ops}
      (ready : s.ready = pre ++ ⟨t, .release :: ops⟩ :: post)
      (zero : s.curr = 0) : SemStep size s { s with ready := pre ++ ⟨t, []⟩ :: post }

inductive SemReachable (size : Nat) (inputs : List (List SemOp)) : SemState → Prop where
  | initial : SemReachable size inputs (semInitial inputs)
  | step {s s'} : SemReachable size inputs s → SemStep size s s' → SemReachable size inputs s'

private theorem sem_invariant {size inputs s} (h : SemReachable size inputs s) :
    s.curr ≤ size ∧ (s.parked ≠ [] → size ≤ s.curr + s.woken.length) := by
  induction h with
  | initial => simp [semInitial]
  | @step s s' reach step ih =>
    cases step with
    | acquire ready free =>
      constructor
      · change s.curr + 1 ≤ size
        omega
      · intro hp
        have := ih.2 hp
        change size ≤ s.curr + 1 + s.woken.length
        omega
    | park ready full => simp only; constructor <;> omega
    | reacquire wake free =>
      have lengths := congrArg List.length wake
      simp only [List.length_append, List.length_cons] at lengths
      constructor
      · change s.curr + 1 ≤ size
        omega
      · intro hp
        have := ih.2 hp
        simp only [List.length_append]
        omega
    | repark wake full => simp only; constructor <;> omega
    | releaseEmpty ready positive empty => simp [empty]; omega
    | releaseWake ready positive queue =>
      have old := ih.2 (by simp [queue])
      simp only [List.length_append, List.length_cons, List.length_nil]
      constructor <;> omega
    | releaseError ready zero => exact ih

def SemaphoreBound : Prop := ∀ (size : JInt .i64), 0 < size.val →
  ∀ inputs s, SemReachable size.val.toNat inputs s → 0 ≤ s.curr ∧ s.curr ≤ size.val.toNat

theorem semaphoreBound_proven : SemaphoreBound := by
  intro size positive inputs s reach
  exact ⟨Nat.zero_le _, (sem_invariant reach).1⟩

def SemaphoreReleaseUnmatched : Prop := ∀ s : SemState, s.curr = 0 →
  semRelease s = (.error (.errorException "release count must match acquire count"), s)

theorem semaphoreReleaseUnmatched_proven : SemaphoreReleaseUnmatched := by
  intro s h
  simp [semRelease, h]

def SemaphoreNoLostWakeup : Prop := ∀ (size : JInt .i64), 0 < size.val →
  ∀ inputs s, SemReachable size.val.toNat inputs s →
    s.parked ≠ [] → size.val.toNat ≤ s.curr + s.woken.length

theorem semaphoreNoLostWakeup_proven : SemaphoreNoLostWakeup := by
  intro size positive inputs s reach
  exact (sem_invariant reach).2

/-- Event operations, `base/lock.jl:708-757`, without cancellation. -/
inductive EventOp where
  | wait | notify | reset
  deriving DecidableEq

/-- `slow` distinguishes the first atomic read/swap from the locked recheck. -/
structure EventTask where
  id : Nat
  ops : List EventOp
  slow : Bool := false
  deriving DecidableEq

/-- `base/lock.jl:701-705`. Queue membership is the parked/relock PC.
`released` counts wait calls that returned or received a wake value;
`notifies` counts completed notify calls. These natural numbers are observation counters. -/
structure EventState where
  set : Bool := false
  ready : List EventTask := []
  parked : List EventTask := []
  woken : List EventTask := []
  released : Nat := 0
  notifies : Nat := 0
  deriving DecidableEq

def eventInitial (inputs : List (List EventOp)) : EventState :=
  { ready := inputs.zipIdx |>.map (fun (ops, id) => ⟨id, ops, false⟩) }

/-- `base/lock.jl:708-757`: fast atomics and locked sections are separate steps;
condition wait enqueues FIFO and releases, while each wake relocks in its own step. -/
inductive EventStep (auto : Bool) : EventState → EventState → Prop where
  | waitSet {s pre post t ops slow}
      (ready : s.ready = pre ++ ⟨t, .wait :: ops, slow⟩ :: post) (set : s.set = true) :
      EventStep auto s { s with set := !auto, ready := pre ++ ⟨t, ops, false⟩ :: post, released := s.released + 1 }
  | waitMiss {s pre post t ops}
      (ready : s.ready = pre ++ ⟨t, .wait :: ops, false⟩ :: post) (unset : s.set = false) :
      EventStep auto s { s with ready := pre ++ ⟨t, .wait :: ops, true⟩ :: post }
  | park {s pre post t ops}
      (ready : s.ready = pre ++ ⟨t, .wait :: ops, true⟩ :: post) (unset : s.set = false) :
      EventStep auto s { s with ready := pre ++ post, parked := s.parked ++ [⟨t, ops, false⟩] }
  | relock {s pre post t}
      (wake : s.woken = pre ++ t :: post) :
      EventStep auto s { s with woken := pre ++ post, ready := s.ready ++ [t] }
  | notifyAutoEmpty {s pre post t ops}
      (mode : auto = true) (ready : s.ready = pre ++ ⟨t, .notify :: ops, false⟩ :: post)
      (empty : s.parked = []) :
      EventStep auto s { s with set := true, ready := pre ++ ⟨t, ops, false⟩ :: post, notifies := s.notifies + 1 }
  | notifyAutoWake {s pre post t ops waiter waiters}
      (mode : auto = true) (ready : s.ready = pre ++ ⟨t, .notify :: ops, false⟩ :: post)
      (queue : s.parked = waiter :: waiters) :
      EventStep auto s { s with ready := pre ++ ⟨t, ops, false⟩ :: post, parked := waiters, woken := s.woken ++ [waiter], released := s.released + 1, notifies := s.notifies + 1 }
  | notifyManualSet {s pre post t ops}
      (mode : auto = false) (ready : s.ready = pre ++ ⟨t, .notify :: ops, false⟩ :: post)
      (set : s.set = true) :
      EventStep auto s { s with ready := pre ++ ⟨t, ops, false⟩ :: post, notifies := s.notifies + 1 }
  | notifyManualUnset {s pre post t ops}
      (mode : auto = false) (ready : s.ready = pre ++ ⟨t, .notify :: ops, false⟩ :: post)
      (unset : s.set = false) :
      EventStep auto s { s with set := true, ready := pre ++ ⟨t, ops, false⟩ :: post, parked := [], woken := s.woken ++ s.parked, released := s.released + s.parked.length, notifies := s.notifies + 1 }
  | reset {s pre post t ops}
      (ready : s.ready = pre ++ ⟨t, .reset :: ops, false⟩ :: post) :
      EventStep auto s { s with set := false, ready := pre ++ ⟨t, ops, false⟩ :: post }

inductive EventReachable (auto : Bool) (inputs : List (List EventOp)) : EventState → Prop where
  | initial : EventReachable auto inputs (eventInitial inputs)
  | step {s s'} : EventReachable auto inputs s → EventStep auto s s' → EventReachable auto inputs s'

private theorem event_invariant {auto inputs s} (h : EventReachable auto inputs s) :
    (s.set = true → s.parked = []) ∧
    (auto = true → s.released + (if s.set then 1 else 0) ≤ s.notifies) := by
  induction h with
  | initial => simp [eventInitial]
  | @step s s' reach step ih =>
    cases step with
    | waitSet ready set =>
      have empty := ih.1 set
      cases auto <;> simp_all
    | waitMiss ready unset => exact ih
    | park ready unset => simpa [unset] using ih
    | relock wake => exact ih
    | notifyAutoEmpty mode ready empty =>
      simp_all
      omega
    | notifyAutoWake mode ready queue =>
      have unset : s.set = false := by
        cases hs : s.set with
        | false => rfl
        | true => have := ih.1 hs; simp [queue] at this
      simp_all
    | notifyManualSet mode ready set => simp_all
    | notifyManualUnset mode ready unset => simp_all
    | reset ready =>
      simp only [Bool.false_eq_true, false_implies, ite_false, Nat.add_zero, true_and]
      intro mode
      have := ih.2 mode
      omega

def EventAutoreset : Prop := ∀ inputs s, EventReachable true inputs s → s.released ≤ s.notifies

theorem eventAutoreset_proven : EventAutoreset := by
  intro inputs s reach
  have := (event_invariant reach).2 rfl
  omega

def EventNotifyReleases : Prop := ∀ inputs s, EventReachable false inputs s →
  s.set = true → s.parked = []

theorem eventNotifyReleases_proven : EventNotifyReleases := by
  intro inputs s reach
  exact (event_invariant reach).1

/-- One valid thread id's state, `base/lock.jl:765-768,973-1009`. -/
inductive OncePhase where
  | initial | concurrent | hasrun
  deriving DecidableEq

/-- Per-task PCs, including a yielding initializer and the non-yielding spin loop. -/
inductive OncePC where
  | enter | initializing (yieldsLeft : Nat) | spin | done
  deriving DecidableEq

structure OnceState where
  phase : OncePhase := .initial
  tasks : List OncePC
  current : Option Nat := none
  deriving DecidableEq

/-- `base/lock.jl:919-923,936-972`: one valid thread id starts uninitialized.
Array allocation and the brief PerThreadLock section have no cooperative yield. -/
def onceInitial (k : Nat) : OnceState := { tasks := List.replicate k .enter }

/-- `base/lock.jl:973-1013`. The current task keeps the thread until it yields
or finishes. `GC.safepoint()` in lines 978-983 does not yield to another task.
The initializer is a total function represented by a finite number of yields. -/
def onceStep (y choice : Nat) (s : OnceState) : OnceState :=
  let t := s.current.getD choice
  match s.tasks[t]? with
  | none => s
  | some .done => { s with current := none }
  | some .enter =>
    match s.phase with
    | .initial => { phase := .concurrent, tasks := s.tasks.set t (.initializing y), current := some t }
    | .concurrent => { s with tasks := s.tasks.set t .spin, current := some t }
    | .hasrun => { s with tasks := s.tasks.set t .done, current := none }
  | some (.initializing (n + 1)) =>
      { s with tasks := s.tasks.set t (.initializing n), current := none }
  | some (.initializing 0) =>
      { phase := .hasrun, tasks := s.tasks.set t .done, current := none }
  | some .spin =>
    match s.phase with
    | .concurrent => s
    | _ => { s with tasks := s.tasks.set t .done, current := none }

def onceRun (y : Nat) (schedule : Nat → Nat) : Nat → OnceState → OnceState
  | 0, s => s
  | n + 1, s => onceStep y (schedule n) (onceRun y schedule n s)

/-- Finite scheduler reachability from any number of OncePerThread callers. -/
inductive OnceReachable (y k : Nat) : OnceState → Prop where
  | initial : OnceReachable y k (onceInitial k)
  | step {s} (choice : Nat) : OnceReachable y k s → OnceReachable y k (onceStep y choice s)

theorem onceRun_reachable (k y n : Nat) (schedule : Nat → Nat) :
    OnceReachable y k (onceRun y schedule n (onceInitial k)) := by
  induction n with
  | zero => exact .initial
  | succ n ih => exact .step _ ih

/-- Only an unfinished task can be selected when the current task yields or finishes. -/
def OnceScheduleValid (k y : Nat) (schedule : Nat → Nat) : Prop :=
  ∀ n, schedule n < k ∧
    let s := onceRun y schedule n (onceInitial k)
    s.current = none → ∀ pc, s.tasks[schedule n]? = some pc → pc ≠ .done

/-- All cooperative schedules of finitely yielding successful initializers finish. -/
def OncePerThreadCompletes : Prop := ∀ k y, 1 ≤ k → ∀ schedule,
  OnceScheduleValid k y schedule →
  ∃ n, (onceRun y schedule n (onceInitial k)).tasks.all (· == .done) = true

private def onceBadSchedule (n : Nat) : Nat := if n = 0 then 0 else 1
private def onceStuck : OnceState :=
  { phase := .concurrent, tasks := [.initializing 0, .spin], current := some 1 }

private theorem onceStuck_fixed (choice : Nat) : onceStep 1 choice onceStuck = onceStuck := by
  rfl

private theorem onceBad_after (n : Nat) :
    onceRun 1 onceBadSchedule (3 + n) (onceInitial 2) = onceStuck := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3 + (n + 1) = (3 + n) + 1 by omega, onceRun, ih]
    exact onceStuck_fixed _

/-- The stuck two-caller state is reachable, is a fixpoint for every choice,
and has no completed call. -/
theorem oncePerThread_spin_reachable :
    OnceReachable 1 2 onceStuck ∧
    (∀ choice, onceStep 1 choice onceStuck = onceStuck) ∧
    onceStuck.tasks.all (· != .done) = true := by
  constructor
  · rw [← onceBad_after 0]
    exact onceRun_reachable 2 1 3 onceBadSchedule
  · exact ⟨onceStuck_fixed, by decide⟩

theorem oncePerThreadCompletes_refuted : ¬ OncePerThreadCompletes := by
  intro h
  obtain ⟨n, done⟩ := h 2 1 (by omega) onceBadSchedule (by
    intro n
    constructor
    · simp only [onceBadSchedule]
      split <;> omega
    · cases n with
      | zero => decide
      | succ n => cases n with
        | zero => decide
        | succ n => cases n with
          | zero => decide
          | succ n =>
            rw [show n + 1 + 1 + 1 = 3 + n by omega, onceBad_after]
            simp [onceStuck])
  cases n with
  | zero => contradiction
  | succ n => cases n with
    | zero => contradiction
    | succ n => cases n with
      | zero => contradiction
      | succ n =>
        rw [show n + 1 + 1 + 1 = 3 + n by omega, onceBad_after] at done
        contradiction

def lockEntries : List JuliaLean.Registry.Entry := [
  { id := "channels-lock-unlock-nonowner", juliaFile := "base/lock.jl",
    juliaFns := ["unlock(::ReentrantLock)"],
    statement := "Non-owner unlock throws ErrorException and leaves the lock unchanged.",
    source := "base/lock.jl:315-320: ownership check and error precede counter mutation.",
    status := .proven, prop := ``LockUnlockNonowner, thm := some ``lockUnlockNonowner_proven,
    notes := "1.13.2 has the same ownership check and UInt32 decrement; master adds cancellation elsewhere, excluded here." },
  { id := "channels-lock-reentrancy-wrap", juliaFile := "base/lock.jl",
    juliaFns := ["trylock(::ReentrantLock)", "unlock(::ReentrantLock)"],
    statement := "Fewer unlocks than successful owner acquisitions leave the lock held.",
    source := "base/lock.jl:155,192: Each successful trylock/lock must be matched by an unlock; lines 167-168,319-322 wrap UInt32.",
    status := .refuted, prop := ``LockReentrancyCount, thm := some ``lockReentrancyCount_refuted,
    issue := "none found (queries: issues/prs 'reentrancy_cnt', 'ReentrantLock overflow', 'ReentrantLock reentrancy count', 'ReentrantLock UInt32', 'lock recursion limit')",
    notes := "n = 2^32 + 1 acquisitions and k = 1 unlock. Closed-form modular count proof. Same on 1.13.2. Reproducer: repro/channels-lock-reentrancy-wrap.jl." },
  { id := "channels-semaphore-bound", juliaFile := "base/lock.jl", juliaFns := ["Semaphore", "acquire", "release"],
    statement := "Every reachable semaphore count is between zero and its positive size.",
    source := "base/lock.jl:559-561: allows at most sem_size acquires to be in use at any time.",
    status := .proven, prop := ``SemaphoreBound, thm := some ``semaphoreBound_proven,
    notes := "1.13.2 acquire uses the same while loop without master's cancellation setup and locked flag. No cancellation is modelled." },
  { id := "channels-semaphore-release-unmatched", juliaFile := "base/lock.jl", juliaFns := ["release(::Semaphore)"],
    statement := "Release at zero throws ErrorException without changing the count.",
    source := "base/lock.jl:672: curr_cnt > 0 || error(\"release count must match acquire count\").",
    status := .proven, prop := ``SemaphoreReleaseUnmatched, thm := some ``semaphoreReleaseUnmatched_proven,
    notes := "Release is unchanged in 1.13.2." },
  { id := "channels-semaphore-no-lost-wakeup", juliaFile := "base/lock.jl", juliaFns := ["acquire(::Semaphore)", "release(::Semaphore)"],
    statement := "A parked acquirer implies count plus notified acquirers awaiting relock is at least the semaphore size.",
    source := "Invariant from base/lock.jl:585-592,672-674: full-count wait loop; decrement followed by FIFO notify(all=false).",
    status := .proven, prop := ``SemaphoreNoLostWakeup, thm := some ``semaphoreNoLostWakeup_proven,
    notes := "Same non-cancelling behavior in 1.13.2. Woken tasks retry in separate scheduler steps." },
  { id := "channels-event-autoreset", juliaFile := "base/lock.jl", juliaFns := ["wait(::Event)", "notify(::Event)"],
    statement := "For Event(true), released wait calls never outnumber completed notify calls.",
    source := "base/lock.jl:690-691: at most one task will be released from wait for each call to notify.",
    status := .proven, prop := ``EventAutoreset, thm := some ``eventAutoreset_proven,
    notes := "1.13.2 has the same two atomic swaps and single-waiter notify; master adds cancellation and locked cleanup, excluded here." },
  { id := "channels-event-notify-releases", juliaFile := "base/lock.jl", juliaFns := ["wait(::Event)", "notify(::Event)"],
    statement := "For Event(false), a set event has no task parked in wait.",
    source := "base/lock.jl:685-688: level-triggered event; tasks queue until notify and do not block while signaled; lines 739-741 notify all.",
    status := .proven, prop := ``EventNotifyReleases, thm := some ``eventNotifyReleases_proven,
    notes := "Same non-cancelling behavior in 1.13.2. Notified tasks reacquire in later steps." },
  { id := "channels-onceperthread-yield-hang", juliaFile := "base/lock.jl", juliaFns := ["OncePerThread", "init_perthread"],
    statement := "Every cooperative schedule of finitely yielding initializers eventually finishes all calls on one thread id.",
    source := "base/lock.jl:876-879 promises calls return an initialized per-thread value; lines 974-983 spin without releasing this thread.",
    status := .refuted, prop := ``OncePerThreadCompletes, thm := some ``oncePerThreadCompletes_refuted,
    issue := "#63400",
    notes := "Two callers, one initializer yield: the second task spins forever and prevents the initializer resuming. Same spin loop in 1.13.2. Reproducer: repro/channels-onceperthread-yield-hang.jl." }
]

end JuliaLean.Channels

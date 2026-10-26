import JuliaLean.ConcurrencyCov.Common

/-!
# `base/lock.jl` and `base/locks-mt.jl` (master `bbfa0ce4150`)

A lock operation of one task is modelled as one atomic step on the lock state,
the step a task performs when no other task interferes; blocking is a step that
parks the task on the lock's wait queue (`cond_wait.waitq`). Tasks are numbered.
`GC.disable_finalizers`/`GC.enable_finalizers` change the calling task's
finalizer-inhibit counter (`ptls->finalizers_inhibited`, `src/gc-common.c:359-373`).

Cancellation tokens (master) are modelled where a source branch tests them: a
token is `none` (no token) or `some c`, `c` telling whether its source is
cancelled; a delivered cancellation is `CancellationRequest(1)`.
-/

namespace JuliaLean.ConcurrencyCov.Locks

open JuliaLean JuliaLean.ConcurrencyCov

/-- `LOCKED_BIT` and `PARKED_BIT`, lines 12-16. -/
def LOCKED : Nat := 1
def PARKED : Nat := 2

/-- The fields of `ReentrantLock` (lines 48-86) with the queue of its `cond_wait`. -/
structure RLock where
  lockedBy : Option Nat := none
  cnt : U32 := u32 0
  /-- `havelock`, two bits. -/
  havelock : Nat := 0
  waitq : List Nat := []
  deriving DecidableEq, Repr

/-- Lock plus the per-task finalizer-inhibit counters and the tasks woken by
`notify` (which retry the acquisition in their own later step). -/
structure St where
  l : RLock
  fin : Nat → Int
  woken : List Nat := []

def St.disableFin (s : St) (t : Nat) : St := { s with fin := upd s.fin t (s.fin t + 1) }
def St.enableFin (s : St) (t : Nat) : St := { s with fin := upd s.fin t (s.fin t - 1) }

/-- `current_task()`, line 10: the running task. -/
def currentTask (cur : Nat) : Nat := cur

/-- `ReentrantLock()`, line 85. -/
def reentrantLock : RLock := {}

/-- `islocked(rl)`, lines 143-145. -/
def islocked (l : RLock) : Bool := l.havelock % 2 = 1

/-- `assert_havelock(l, l.locked_by)` (line 88 with base/condition.jl:32-36). -/
def assertHavelock (t : Nat) (l : RLock) : R Unit :=
  match l.lockedBy with
  | none => .error .concurrencyViolation
  | some o => if islocked l ∧ o = t then .ok () else .error .concurrencyViolation

/-- `show(io, ::ReentrantLock)`, line 90. -/
def showLock : String := "ReentrantLock()"

/-- `show(io, ::MIME"text/plain", l)`, lines 92-102; `cur` is `current_task()`
and task `n` prints as `Task#n`. -/
def showPlain (compact : Bool) (cur : Nat) (l : RLock) : String :=
  showLock ++ (if compact then "" else match l.lockedBy with
    | some o => " (locked by " ++ (if o = cur then "current " else "") ++ s!"Task#{o})"
    | none => " (unlocked)")

/-- `_trylock(rl, ct)`, lines 173-183: the compare-and-swap of `havelock` from its
parked bit alone to that bit plus the locked bit. -/
def trylockSlow (t : Nat) (s : St) : Bool × St :=
  let s := s.disableFin t
  let state := (s.l.havelock / 2 % 2) * PARKED
  if s.l.havelock = state then
    (true, { s with l := { s.l with havelock := state + LOCKED, cnt := u32 1, lockedBy := some t } })
  else (false, s.enableFin t)

/-- `trylock(rl)`, lines 165-172. -/
def trylock (t : Nat) (s : St) : Bool × St :=
  if s.l.lockedBy = some t then
    (true, { s with l := { s.l with cnt := s.l.cnt + u32 1 } })
  else trylockSlow t s

/-- Result of one `lock` step. -/
inductive LockStep where
  | acquired (s : St)
  /-- The task parked on `cond_wait` (lines 234-250). -/
  | parked (s : St)
  /-- A cancelled token refused the acquisition (lines 213-219). -/
  | refused (e : Exn) (s : St)

/-- One pass of `slowlock`'s loop (lines 196-255) for a task that does not hold
the lock: grab it when the locked bit is clear (releasing it again and throwing
when its token was cancelled meanwhile); otherwise set the parked bit and park. -/
def slowlock (t : Nat) (tok : Option Bool) (s : St) : LockStep :=
  let state := s.l.havelock
  if state % 2 = 0 then
    let s := s.disableFin t
    let s := { s with l := { s.l with havelock := state + LOCKED, cnt := u32 1, lockedBy := some t } }
    if tok = some true then
      -- `unlock(rl)` of the just-acquired hold, then `checkcancel`
      let s := { s with l := { s.l with lockedBy := none, cnt := u32 0, havelock := state } }
      .refused (.cancellation 1) (s.enableFin t)
    else .acquired s
  else
    .parked { s with l := { s.l with havelock := LOCKED + PARKED, waitq := s.l.waitq ++ [t] } }

/-- `lock(rl; cancel)`, lines 194-257: the fast `trylock`, else `slowlock`. -/
def lock (t : Nat) (tok : Option Bool) (s : St) : LockStep :=
  match trylock t s with
  | (true, s) => .acquired s
  | (false, s) => slowlock t tok s

/-- `lock(c::GenericCondition{ReentrantLock}; cancel)`, lines 263-264, and
`_uncancellable_lock(l)`, line 299 (no token). -/
def lockCond (t : Nat) (tok : Option Bool) (s : St) : LockStep := lock t tok s
def uncancellableLock (t : Nat) (s : St) : LockStep := lock t none s

/-- `notifywaiters(rl)`, lines 327-341: wake the first waiter; the parked bit stays
set while waiters remain. -/
def notifywaiters (s : St) : St :=
  match s.l.waitq with
  | [] => { s with l := { s.l with havelock := 0 } }
  | w :: q =>
    { s with l := { s.l with waitq := q, havelock := if q.isEmpty then 0 else PARKED },
             woken := s.woken ++ [w] }

/-- `_unlock(rl)`, lines 318-346: `true` when the hold count reached zero. -/
def unlockInner (s : St) : Bool × St :=
  let n := s.l.cnt - u32 1
  let s := { s with l := { s.l with cnt := n } }
  if n.val = 0 then
    let s := { s with l := { s.l with lockedBy := none } }
    if s.l.havelock = LOCKED then (true, { s with l := { s.l with havelock := 0 } })
    else (true, notifywaiters s)
  else (false, s)

/-- `unlock(rl)`, lines 315-348. -/
def unlock (t : Nat) (s : St) : R St :=
  if s.l.lockedBy ≠ some t then
    .error (.errorException (if s.l.cnt.val = 0 then "unlock count must match lock count"
      else "unlock from wrong thread"))
  else
    match unlockInner s with
    | (true, s) => .ok (s.enableFin t)
    | (false, s) => .ok s

/-- `unlockall(rl)`, lines 350-354: the old count, after releasing every level. -/
def unlockall (t : Nat) (s : St) : R (U32 × St) := do
  let n := s.l.cnt
  let s ← unlock t { s with l := { s.l with cnt := u32 1 } }
  return (n, s)

/-- `relockall(rl, n)` after its `lock(rl; cancel=nothing)` acquired, lines 356-365. -/
def relockall (n : U32) (s : St) : R St :=
  let old := s.l.cnt
  let s := { s with l := { s.l with cnt := n } }
  if old.val = 1 then .ok s else .error .concurrencyViolation

/-- `relockall_but_one(rl, state)`, lines 301-305: `none` when nothing is relocked,
otherwise the count `relockall` restores. -/
def relockallButOne (state : U32) : Option U32 :=
  if state.val = 1 then none else some (state - u32 1)

/-- `wait_no_relock(c, tok)`, lines 266-296: with no token, or a token not yet
cancelled, the task is registered and parks; a cancelled token is refused at the
registration recheck, so the task is withdrawn and the refusal thrown. -/
inductive Parked where
  | parked
  | refused (e : Exn)
  deriving DecidableEq, Repr

def waitNoRelock (tok : Option Bool) : Parked :=
  if tok = some true then .refused (.cancellation 1) else .parked

/-! ## Closure forms, lines 367-515 -/

/-- A function run under the lock: its outcome. -/
abbrev Body := Outcome

/-- `lock(f, l)` (lines 382-389 and 392-399) when `lock` acquires: `f()` then the
`unlock` of the `finally` block. -/
def lockDo (t : Nat) (f : Body) (s : St) : R (Nat × St) :=
  match lock t none s with
  | .acquired s =>
    match unlock t s with
    | .ok s => match f with
      | .ok v => .ok (v, s)
      | .error e => .error e
    | .error e => .error e
  | .parked _ => .error (.errorException "blocked")
  | .refused e _ => .error e

/-- The state after `lockDo`. -/
def lockDoState (t : Nat) (s : St) : Option St :=
  match lock t none s with
  | .acquired s => (unlock t s).toOption
  | _ => none

/-- `trylock(f, l)`, lines 401-410: `false` (as `none`) without calling `f` when
the lock is unavailable. -/
def trylockDo (t : Nat) (f : Body) (s : St) : R (Option Nat) × St :=
  match trylock t s with
  | (false, s) => (.ok none, s)
  | (true, s) =>
    match unlock t s with
    | .ok s' => (f.map some, s')
    | .error e => (.error e, s)

/-- `@lock l expr`, lines 431-441: `lock(temp); try expr finally unlock(temp) end`. -/
def lockMacro (t : Nat) (expr : Body) (s : St) : R (Nat × St) := lockDo t expr s

/-- `@lock_nofail l expr`, lines 450-458: no `try`, so an exception from `expr`
leaves the lock held. -/
def lockNofail (t : Nat) (expr : Body) (s : St) : R Nat × St :=
  match lock t none s with
  | .acquired s =>
    match expr with
    | .ok v => match unlock t s with
      | .ok s' => (.ok v, s')
      | .error e => (.error e, s)
    | .error e => (.error e, s)
  | .parked s => (.error (.errorException "blocked"), s)
  | .refused e s => (.error e, s)

/-- `Lockable(value, lock)`, lines 485-491. -/
structure Lockable where
  value : Nat
  lock : St

/-- `Lockable(value)`, line 490: a fresh `ReentrantLock`. -/
def lockable (value : Nat) : Lockable := ⟨value, ⟨reentrantLock, fun _ => 0, []⟩⟩

/-- `getindex(l::Lockable)`, line 491. -/
def lockableGet (t : Nat) (l : Lockable) : R Nat := do
  assertHavelock t l.lock.l
  return l.value

/-- `lock(f, l::Lockable)`, lines 506-510: `f` receives the value. -/
def lockableDo (t : Nat) (f : Nat → Body) (l : Lockable) : R (Nat × St) := lockDo t (f l.value) l.lock

/-- `lock`, `trylock`, `unlock` of a `Lockable`, lines 513-515. -/
def lockableLock (t : Nat) (l : Lockable) : LockStep := lock t none l.lock
def lockableTrylock (t : Nat) (l : Lockable) : Bool × St := trylock t l.lock
def lockableUnlock (t : Nat) (l : Lockable) : R St := unlock t l.lock

/-! ## Semaphore and Event, lines 556-763 -/

/-- `Semaphore(sem_size)`, line 569, for integer sizes. -/
structure Sem where
  size : Int
  curr : Int
  deriving DecidableEq, Repr

def semaphore (sz : Int) : R Sem :=
  if 0 < sz then .ok ⟨sz, 0⟩ else .error (.argumentError "Semaphore size must be > 0")

/-- One `acquire(s)` step, lines 578-597: take a permit or wait for one. -/
def acquire (s : Sem) : Option Sem := if s.curr < s.size then some { s with curr := s.curr + 1 } else none

/-- `release(s)`, lines 669-679. -/
def release (s : Sem) : R Sem :=
  if 0 < s.curr then .ok { s with curr := s.curr - 1 }
  else .error (.errorException "release count must match acquire count")

/-- `acquire(f, s)`, lines 623-630, and `@acquire s expr`, lines 650-660: `f` runs
holding a permit, which the `finally` block returns. -/
def acquireDo (f : Body) (s : Sem) : Option (R Nat × Sem) :=
  match acquire s with
  | none => none
  | some s' => match release s' with
    | .ok s'' => some (f, s'')
    | .error e => some (.error e, s')

def acquireMacro (expr : Body) (s : Sem) : Option (R Nat × Sem) := acquireDo expr s

/-- `Event(autoreset)`, line 705. -/
structure Event where
  autoreset : Bool
  set : Bool
  deriving DecidableEq, Repr

def event (autoreset : Bool := false) : Event := ⟨autoreset, false⟩

/-- `reset(e)`, lines 755-758. -/
def reset (e : Event) : Event := { e with set := false }

/-! ## Once-per-process, -thread and -task values, lines 765-1063 -/

/-- `PerStateInitial`, `PerStateHasrun`, `PerStateErrored`, `PerStateConcurrent`. -/
inductive PerState where
  | initial | hasrun | errored | concurrent
  deriving DecidableEq, Repr

/-- A `OncePerProcess`: its stored value, state and initializer. The initializer's
successive calls return the outcomes in `inits` (index = number of earlier runs). -/
structure OnceProc where
  value : Option Nat
  state : PerState
  runs : Nat
  deriving DecidableEq, Repr

/-- The constructors at lines 808-816 all build `new(nothing, PerStateInitial, true,
initializer, ReentrantLock())`; the type parameter only differs. -/
def oncePerProcess : OnceProc := ⟨none, .initial, 0⟩

/-- `init_perprocesss(once, state)`, lines 820-845, holding `once.lock`. -/
def initPerprocess (init : Nat → Outcome) (state : PerState) (o : OnceProc) : R OnceProc :=
  if state = .errored then .error (.errorException "OncePerProcess initializer failed previously")
  else
    match o.state with
    | .initial =>
      match init o.runs with
      | .ok v => .ok { value := some v, state := .hasrun, runs := o.runs + 1 }
      | .error e => .error e
    | .errored => .error (.errorException "OncePerProcess initializer failed previously")
    | .hasrun => .ok o
    | .concurrent => .error (.errorException "invalid state for OncePerProcess")

/-- The state after a failed initializer run (the `catch` branch, line 838). -/
def initFailed (o : OnceProc) : OnceProc :=
  if o.state = .initial then { o with state := .errored, runs := o.runs + 1 } else
  if o.state = .hasrun then o else { o with state := .errored }

/-- `(once::OncePerProcess)()`, lines 817-848: the value and the new state. -/
def callOnceProc (init : Nat → Outcome) (o : OnceProc) : R Nat × OnceProc :=
  if o.state = .hasrun then (o.value.elim (.error .methodError) .ok, o)
  else
    match initPerprocess init o.state o with
    | .ok o' => (o'.value.elim (.error .methodError) .ok, o')
    | .error e => (.error e, if o.state = .errored then o else initFailed o)

/-- `copyto_monotonic!(dest, src)`, lines 850-861: assigned source slots are stored
at the same position; `dest[i]` is bounds-checked. -/
def copytoMonotonic {α : Type} (dest src : List (Option α)) : R (List (Option α)) :=
  if src.length ≤ dest.length then
    .ok ((List.range dest.length).map fun i =>
      match src[i]? with
      | some (some x) => some x
      | _ => dest[i]?.getD none)
  else .error .boundsError

/-- `fill_monotonic!(dest, x)`, lines 863-868. -/
def fillMonotonic {α : Type} (dest : List (Option α)) (x : α) : List (Option α) :=
  dest.map fun _ => some x

/-- A `OncePerThread`: per-thread states and values (`ss`, `xs`), and the number of
initializer runs. -/
structure OnceThread where
  ss : List PerState
  xs : List (Option Nat)
  runs : Nat
  deriving DecidableEq, Repr

/-- The constructors at lines 919-928 start with empty arrays. -/
def oncePerThread : OnceThread := ⟨[], [], 0⟩

/-- `getindex(once, tid)` (lines 930-1019) with `maxthreadid() = nt`, run by one
task without interference: grow the arrays to `len + nt` when needed, run the
initializer for an initial slot, and return the slot's value. -/
def onceThreadGet (init : Nat → Outcome) (nt : Nat) (tid : Int) (o : OnceThread) :
    R Nat × OnceThread :=
  if 0 < tid ∧ tid ≤ o.ss.length ∧ o.ss[(tid - 1).toNat]? = some .hasrun then
    ((o.xs[(tid - 1).toNat]?.join).elim (.error .boundsError) .ok, o)
  else if ¬ (0 < tid ∧ tid ≤ nt) then (.error (.argumentError "thread id outside of allocated range"), o)
  else
    let i := (tid - 1).toNat
    if tid ≤ o.ss.length ∧ o.ss[i]? = some .errored then
      (.error (.errorException "OncePerThread initializer failed previously"), o)
    else
      let o := if o.ss.length < tid then
          { o with ss := o.ss ++ List.replicate nt .initial, xs := o.xs ++ List.replicate nt none }
        else o
      match o.ss[i]? with
      | some .initial =>
        match init o.runs with
        | .ok v => (.ok v, { ss := o.ss.set i .hasrun, xs := o.xs.set i (some v), runs := o.runs + 1 })
        | .error e => (.error e, { o with ss := o.ss.set i .errored, runs := o.runs + 1 })
      | some .errored => (.error (.errorException "OncePerThread initializer failed previously"), o)
      | some .hasrun => ((o.xs[i]?.join).elim (.error .boundsError) .ok, o)
      | _ => (.error (.errorException "invalid state for OncePerThread"), o)

/-- `(once::OncePerThread)()`, line 929: `once[threadid()]`. -/
def callOnceThread (init : Nat → Outcome) (nt : Nat) (threadid : Int) (o : OnceThread) :
    R Nat × OnceThread := onceThreadGet init nt threadid o

/-- A `OncePerTask` call, lines 1061-1063: `get!(initializer, task_local_storage(),
once)` on the current task's storage, a map from tasks to values, and the runs. -/
structure OnceTask where
  store : Nat → Option Nat
  runs : Nat

/-- The constructors at lines 1055-1059 store only the initializer. -/
def oncePerTask : OnceTask := ⟨fun _ => none, 0⟩

def callOnceTask (init : Nat → Outcome) (task : Nat) (o : OnceTask) : R Nat × OnceTask :=
  match o.store task with
  | some v => (.ok v, o)
  | none =>
    match init o.runs with
    | .ok v => (.ok v, { store := upd o.store task (some v), runs := o.runs + 1 })
    | .error e => (.error e, { o with runs := o.runs + 1 })

/-! ## Spin locks, `base/locks-mt.jl` -/

/-- `SpinLock` / `PaddedSpinLock`: the `owned` field and the per-task finalizer
counters. -/
structure Spin where
  owned : Int
  fin : Nat → Int

/-- `SpinLock()` (line 46) and `PaddedSpinLock()` (lines 70-74). -/
def spinLock : Spin := ⟨0, fun _ => 0⟩
def paddedSpinLock : Spin := ⟨0, fun _ => 0⟩

/-- `islocked(l)`, lines 113-115. -/
def spinIslocked (l : Spin) : Bool := l.owned ≠ 0

/-- `assert_havelock(l::AbstractSpinLock)`, line 79. -/
def spinAssertHavelock (l : Spin) : R Unit :=
  if spinIslocked l then .ok () else .error .concurrencyViolation

/-- `trylock(l)`, lines 92-102. -/
def spinTrylock (t : Nat) (l : Spin) : Bool × Spin :=
  if l.owned = 0 then
    let fin := upd l.fin t (l.fin t + 1)
    let p := l.owned
    if p = 0 then (true, { owned := 1, fin })
    else (false, { owned := 1, fin := upd fin t (fin t - 1) })
  else (false, l)

/-- `lock(l)`, lines 81-90: one pass of the loop; `none` keeps spinning. -/
def spinLockStep (t : Nat) (l : Spin) : Option Spin :=
  match spinTrylock t l with
  | (true, l) => some l
  | (false, _) => none

/-- `unlock(l)`, lines 104-111. -/
def spinUnlock (t : Nat) (l : Spin) : R Spin :=
  let p := l.owned
  let l := { l with owned := 0 }
  if p = 0 then .error (.errorException "unlock count must match lock count")
  else .ok { l with fin := upd l.fin t (l.fin t - 1) }

end JuliaLean.ConcurrencyCov.Locks

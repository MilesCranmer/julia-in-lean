import JuliaLean.Core

/-!
# `Channel` as a transition system (`base/channels.jl`, master `bbfa0ce4150`)

A state holds one `Channel` and a finite list of tasks. Each task performs one
channel operation (`put!`, `take!`, one `iterate` step, `fetch`, `wait`,
`close`, `empty!`); a Julia task performing several operations in sequence is
the special case where the next task starts after the previous one finished,
so every property proven for all interleavings of single-operation tasks holds
for sequential tasks too.

The runtime scheduler is a primitive that may run any runnable task next
(`Reach`). One step of a task is one atomic section of the Julia code:

* everything a task does between acquiring and releasing the channel lock
  (`c.cond_take.lock`, a `ReentrantLock`) is one step, since every write to the
  channel state happens under that lock;
* `wait(cond)` enqueues the task FIFO on the condition's queue and releases the
  lock in the same step (`wait(::GenericCondition)`, base/condition.jl:291-405);
  the task is then `parked`;
* `notify(cond, val, all, error)` (base/condition.jl:416-434) pops waiters in
  FIFO order and makes them runnable (`woken`) with the wake value; a woken task
  re-acquires the lock and continues in its own later step;
* lock-free reads (`check_channel_state` at the start of `put!`, the fast path of
  `wait(c)`, the `isopen(c) || isready(c)` test of `iterate`) are steps of their
  own, so other tasks may run between them and the following locked section.

Cancellation tokens (master only) are not modelled: every wait uses no token, so
`claim_wait` always succeeds and a waiter is only woken by `notify`/`schedule`.
On 1.13.2 the same code without cancellation tokens has the same steps.

Counts (`length(c.data)`, `n_avail_items`) are Julia `Int`s; they count values
and tasks that exist in memory, so they stay far from `typemax(Int)` and are
modelled as `Nat`/`Int` without wrapping. `sz_max` is any `Nat` (`Channel(Inf)`
is `typemax(Int)`, which only matters through comparisons with the buffer
length).
-/

namespace JuliaLean.Channels

/-- Channel items: opaque Julia objects. Equal numbers stand for `===` objects. -/
abbrev Val := Nat

/-- Exceptions thrown by channel operations. -/
inductive Exc where
  /-- `InvalidStateException(msg, :closed)`, e.g. `closed_exception()`
  (base/channels.jl:178); `iterate` treats every such exception as the end. -/
  | closed
  /-- Any other exception passed to `close(c, excp)`. -/
  | user (n : Nat)
  /-- `ErrorException("`fetch` is not supported on an unbuffered Channel.")`
  (base/channels.jl:535). -/
  | fetchUnbuffered
  deriving DecidableEq, Repr, Inhabited

/-- The value a parked task is woken with: `notify(c, nothing)`,
`schedule(t, v)`, or `notify(c, e; error=true)`. -/
inductive Wake where
  | none
  | val (v : Val)
  | err (e : Exc)
  deriving DecidableEq, Repr

/-- The channel operation a task performs. `iter` is one call
`iterate(c)` (base/channels.jl:769-792). -/
inductive Op where
  | put (v : Val)
  | take
  | iter
  | fetch
  | wait
  | close (e : Exc)
  | empty
  deriving DecidableEq, Repr

/-- Where a parked task resumes, i.e. which `wait(cond)` call it is in.
`it` records that the `take!` was called by `iterate`. -/
inductive Park where
  /-- `wait(c.cond_put)` in `put_buffered` (base/channels.jl:430). -/
  | putBuf (v : Val)
  /-- `wait(c.cond_put)` in `put_unbuffered` (base/channels.jl:463). -/
  | putUnb (v : Val)
  /-- `wait(c.cond_take)` in `take_buffered` (base/channels.jl:580). -/
  | take (it : Bool)
  /-- `wait(c.cond_take)` in `take_unbuffered` (base/channels.jl:601). -/
  | takeUnb (it : Bool)
  /-- `wait(c.cond_take)` in `fetch_buffered` (base/channels.jl:526). -/
  | fetch
  /-- `wait(c.cond_wait)` in `wait(::Channel)` (base/channels.jl:738). -/
  | wait
  deriving DecidableEq, Repr

/-- Result of an operation: the returned value (`put!` returns `v`, `take!`
and `fetch` the item, `iterate` the item or `nothing`) or the thrown exception. -/
inductive Res where
  | ok (v : Option Val)
  | err (e : Exc)
  deriving DecidableEq, Repr

/-- A task's program counter. -/
inductive Pc where
  /-- Not started. -/
  | start
  /-- `put!` passed its lock-free `check_channel_state` (base/channels.jl:401)
  and is about to lock in `put_buffered`/`put_unbuffered`. -/
  | putLocked (v : Val)
  /-- `iterate` passed `isopen(c) || isready(c)` (base/channels.jl:770) and is
  about to call `take!`. -/
  | takeLocked (it : Bool)
  /-- `wait(c)` passed its lock-free `isready(c)` fast path
  (base/channels.jl:729) and is about to lock. -/
  | waitLocked
  /-- Blocked in a condition wait. -/
  | parked (k : Park)
  /-- Woken from a condition wait, runnable, about to re-acquire the lock. -/
  | woken (k : Park) (w : Wake)
  /-- `put_unbuffered` popped `taker` and released the lock; next it runs
  `schedule(taker, v); yield()` (base/channels.jl:484-485). -/
  | handoff (v : Val) (taker : Nat)
  /-- Finished. -/
  | done (r : Res)
  deriving DecidableEq, Repr

structure Task where
  op : Op
  pc : Pc
  deriving DecidableEq, Repr

/-- The fields of `Channel{T}` (base/channels.jl:32-52). The three conditions
share one lock; for a buffered channel `cond_wait` is `cond_take`
(base/channels.jl:49), so `wait(c)` parks on `qTake` and `qWait` stays empty. -/
structure Chan where
  /-- `sz_max`. -/
  sz : Nat
  /-- `data`. -/
  data : List Val
  /-- `state === :open`. -/
  isOpen : Bool
  /-- `excp`, meaningful once closed (`close` always sets it). -/
  excp : Exc
  /-- `n_avail_items`. -/
  nAvail : Int
  /-- `cond_take.waitq`. -/
  qTake : List Nat
  /-- `cond_put.waitq`. -/
  qPut : List Nat
  /-- `cond_wait.waitq` (unbuffered channels only). -/
  qWait : List Nat
  deriving DecidableEq, Repr

structure St where
  ch : Chan
  tasks : List Task
  /-- Ghost: items discarded by `empty!`. -/
  dropped : List Val
  deriving DecidableEq, Repr

/-! ## Task-list updates -/

/-- Set the program counter of task `i`. -/
def setPc : List Task → Nat → Pc → List Task
  | [], _, _ => []
  | t :: ts, 0, pc => { t with pc := pc } :: ts
  | t :: ts, n + 1, pc => t :: setPc ts n pc

/-- `schedule(t, w)` on a parked task `t`: it becomes runnable with wake value
`w`. A task that is not parked is left alone. -/
def wake : List Task → Nat → Wake → List Task
  | [], _, _ => []
  | t :: ts, 0, w =>
    (match t.pc with
     | .parked k => { t with pc := .woken k w }
     | _ => t) :: ts
  | t :: ts, n + 1, w => t :: wake ts n w

/-- Wake every task of a queue, in FIFO order. -/
def wakeAll (ts : List Task) (q : List Nat) (w : Wake) : List Task :=
  q.foldl (fun ts j => wake ts j w) ts

/-! ## Atomic sections -/

namespace St

def finish (s : St) (i : Nat) (r : Res) : St := { s with tasks := setPc s.tasks i (.done r) }
def goto (s : St) (i : Nat) (pc : Pc) : St := { s with tasks := setPc s.tasks i pc }
def addAvail (s : St) (d : Int) : St := { s with ch := { s.ch with nAvail := s.ch.nAvail + d } }

/-- Park task `i` on `cond_take`. -/
def parkTake (s : St) (i : Nat) (k : Park) : St :=
  { s with ch := { s.ch with qTake := s.ch.qTake ++ [i] }, tasks := setPc s.tasks i (.parked k) }
/-- Park task `i` on `cond_put`. -/
def parkPut (s : St) (i : Nat) (k : Park) : St :=
  { s with ch := { s.ch with qPut := s.ch.qPut ++ [i] }, tasks := setPc s.tasks i (.parked k) }
/-- Park task `i` on `cond_wait` (unbuffered channels). -/
def parkWait (s : St) (i : Nat) (k : Park) : St :=
  { s with ch := { s.ch with qWait := s.ch.qWait ++ [i] }, tasks := setPc s.tasks i (.parked k) }

/-- `notify(c.cond_take, w, true, false)`. -/
def notifyTakeAll (s : St) (w : Wake) : St :=
  { s with ch := { s.ch with qTake := [] }, tasks := wakeAll s.tasks s.ch.qTake w }
/-- `notify(c.cond_put, w, true, false)`. -/
def notifyPutAll (s : St) (w : Wake) : St :=
  { s with ch := { s.ch with qPut := [] }, tasks := wakeAll s.tasks s.ch.qPut w }
/-- `notify(c.cond_wait, w, true, false)`. -/
def notifyWaitAll (s : St) (w : Wake) : St :=
  { s with ch := { s.ch with qWait := [] }, tasks := wakeAll s.tasks s.ch.qWait w }
/-- `notify(c.cond_put, nothing, false, false)`: wake the first waiter, if any. -/
def notifyPutOne (s : St) : St :=
  match s.ch.qPut with
  | [] => s
  | j :: q => { s with ch := { s.ch with qPut := q }, tasks := wake s.tasks j .none }

end St

/-- What `iterate` makes of the result of its `take!`: an
`InvalidStateException` with state `:closed` ends the iteration
(base/channels.jl:773-778). -/
def finishTake (it : Bool) (r : Res) : Res :=
  if it then (match r with | .err .closed => .ok none | r => r) else r

open St

/-- The locked part of `put_buffered` from the `if length(c.data) == c.sz_max`
test on, with `n_avail_items` already incremented (base/channels.jl:425-436),
also run after each wake-up from `wait(c.cond_put)`: if the channel is closed,
`check_channel_state` throws (inside the loop when full, after it otherwise)
and the `finally` block undoes the increment (line 445); if it is full, wait;
otherwise push and `notify(c.cond_take, nothing, true, false)`. -/
def putBufBody (s : St) (i : Nat) (v : Val) : St :=
  if !s.ch.isOpen then (s.addAvail (-1)).finish i (.err s.ch.excp)
  else if s.ch.data.length = s.ch.sz then s.parkPut i (.putBuf v)
  else
    let s := { s with ch := { s.ch with data := s.ch.data ++ [v] } }
    (s.notifyTakeAll .none).finish i (.ok (some v))

/-- The locked loop of `put_unbuffered` (base/channels.jl:458-478) with
`n_avail_items` already incremented: while no taker waits, check the state,
`notify(c.cond_wait)` and wait on `cond_put`; then check the state again, pop
the first taker (whose `claim_wait` succeeds without cancellation), and in the
`finally` block decrement `n_avail_items` and unlock (lines 481-482). -/
def putUnbBody (s : St) (i : Nat) (v : Val) : St :=
  if !s.ch.isOpen then (s.addAvail (-1)).finish i (.err s.ch.excp)
  else match s.ch.qTake with
    | [] => (s.notifyWaitAll .none).parkPut i (.putUnb v)
    | t :: q => ({ s with ch := { s.ch with qTake := q } }.addAvail (-1)).goto i (.handoff v t)

/-- `take_buffered` (base/channels.jl:571-591), also run after each wake-up:
while the buffer is empty, `check_channel_state` then wait on `cond_take`;
then `popfirst!`, decrement `n_avail_items`, and
`notify(c.cond_put, nothing, false, false)`. -/
def takeBufBody (s : St) (i : Nat) (it : Bool) : St :=
  match s.ch.data with
  | [] => if !s.ch.isOpen then s.finish i (finishTake it (.err s.ch.excp)) else s.parkTake i (.take it)
  | v :: d =>
    let s := ({ s with ch := { s.ch with data := d } }.addAvail (-1)).notifyPutOne
    s.finish i (finishTake it (.ok (some v)))

/-- `take_unbuffered` up to its wait (base/channels.jl:594-601):
`check_channel_state`, `notify(c.cond_put, nothing, false, false)`, wait on
`cond_take` for the value a `put!` schedules it with. -/
def takeUnbStart (s : St) (i : Nat) (it : Bool) : St :=
  if !s.ch.isOpen then s.finish i (finishTake it (.err s.ch.excp))
  else s.notifyPutOne.parkTake i (.takeUnb it)

/-- `take!(c)` (base/channels.jl:567-570). -/
def takeBody (s : St) (i : Nat) (it : Bool) : St :=
  if s.ch.sz = 0 then takeUnbStart s i it else takeBufBody s i it

/-- `fetch_buffered` (base/channels.jl:517-534), also run after each wake-up. -/
def fetchBody (s : St) (i : Nat) : St :=
  match s.ch.data with
  | [] => if !s.ch.isOpen then s.finish i (.err s.ch.excp) else s.parkTake i .fetch
  | v :: _ => s.finish i (.ok (some v))

/-- The locked part of `wait(c::Channel)` (base/channels.jl:730-743), also run
after each wake-up: while `!isready(c)`, `check_channel_state` then wait on
`cond_wait` (which is `cond_take` for a buffered channel). -/
def waitBody (s : St) (i : Nat) : St :=
  if s.ch.nAvail > 0 then s.finish i (.ok none)
  else if !s.ch.isOpen then s.finish i (.err s.ch.excp)
  else if s.ch.sz = 0 then s.parkWait i .wait else s.parkTake i .wait

/-- `close(c, excp)` (base/channels.jl:200-212): set `excp` and the state, then
`notify_error` on `cond_take`, `cond_wait`, `cond_put`. -/
def closeBody (s : St) (i : Nat) (e : Exc) : St :=
  let s := { s with ch := { s.ch with excp := e, isOpen := false } }
  let s := s.notifyTakeAll (.err e)
  let s := s.notifyWaitAll (.err e)
  let s := s.notifyPutAll (.err e)
  s.finish i (.ok none)

/-- `empty!(c)` (base/channels.jl:267-275). -/
def emptyBody (s : St) (i : Nat) : St :=
  let n := s.ch.data.length
  let s := { s with ch := { s.ch with data := [] }, dropped := s.dropped ++ s.ch.data }
  ((s.addAvail (-(n : Int))).notifyPutAll .none).finish i (.ok none)

/-- One atomic step of task `i`, or `none` if task `i` does not exist or is not
runnable (parked or done). -/
def stepTask (s : St) (i : Nat) : Option St :=
  match s.tasks[i]? with
  | none => none
  | some t =>
    match t.op, t.pc with
    -- put!: lock-free `check_channel_state(c)` (base/channels.jl:401)
    | .put v, .start => some (if !s.ch.isOpen then s.finish i (.err s.ch.excp) else s.goto i (.putLocked v))
    -- `lock(c)`, `_increment_n_avail(c, 1)` (base/channels.jl:418, 424, 452, 455)
    | _, .putLocked v =>
      some (if s.ch.sz = 0 then putUnbBody (s.addAvail 1) i v else putBufBody (s.addAvail 1) i v)
    | _, .woken (.putBuf v) w =>
      some (match w with
        | .err e => (s.addAvail (-1)).finish i (.err e)
        | _ => putBufBody s i v)
    | _, .woken (.putUnb v) w =>
      some (match w with
        | .err e => (s.addAvail (-1)).finish i (.err e)
        | _ => putUnbBody s i v)
    -- `schedule(taker, v); yield()` (base/channels.jl:484-485)
    | _, .handoff v t => some ({ s with tasks := wake s.tasks t (.val v) }.finish i (.ok (some v)))
    | .take, .start => some (takeBody s i false)
    -- iterate: `isopen(c) || isready(c)`, else the closed branch (base/channels.jl:770-790)
    | .iter, .start =>
      some (if s.ch.isOpen || s.ch.nAvail > 0 then s.goto i (.takeLocked true)
        else s.finish i (if s.ch.excp = .closed then .ok none else .err s.ch.excp))
    | _, .takeLocked it => some (takeBody s i it)
    | _, .woken (.take it) w =>
      some (match w with
        | .err e => s.finish i (finishTake it (.err e))
        | _ => takeBufBody s i it)
    | _, .woken (.takeUnb it) w =>
      some (s.finish i (match w with
        | .err e => finishTake it (.err e)
        | .val v => .ok (some v)
        | .none => .ok none))
    | .fetch, .start => some (if s.ch.sz = 0 then s.finish i (.err .fetchUnbuffered) else fetchBody s i)
    | _, .woken .fetch w =>
      some (match w with
        | .err e => s.finish i (.err e)
        | _ => fetchBody s i)
    -- wait(c): lock-free fast path `isready(c) && return` (base/channels.jl:729)
    | .wait, .start => some (if s.ch.nAvail > 0 then s.finish i (.ok none) else s.goto i .waitLocked)
    | _, .waitLocked => some (waitBody s i)
    | _, .woken .wait w =>
      some (match w with
        | .err e => s.finish i (.err e)
        | _ => waitBody s i)
    | .close e, .start => some (closeBody s i e)
    | .empty, .start => some (emptyBody s i)
    | _, _ => none

/-- A fresh channel of size `sz` and one task per operation, none started. -/
def init (sz : Nat) (ops : List Op) : St :=
  { ch := { sz := sz, data := [], isOpen := true, excp := .closed, nAvail := 0,
            qTake := [], qPut := [], qWait := [] }
    tasks := ops.map fun op => { op := op, pc := .start }
    dropped := [] }

/-- States reachable from `s` when the scheduler may run any runnable task at
each step. -/
inductive Reach : St → St → Prop
  | refl (s : St) : Reach s s
  | step {s s' s'' : St} (i : Nat) : Reach s s' → stepTask s' i = some s'' → Reach s s''

/-- Run a schedule (a list of task ids); ids of non-runnable tasks are
skipped. Used for counterexamples and differential tests. -/
def runSched (s : St) : List Nat → St
  | [] => s
  | i :: is => runSched ((stepTask s i).getD s) is

end JuliaLean.Channels

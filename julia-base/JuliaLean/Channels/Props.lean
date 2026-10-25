import JuliaLean.Channels.Model

/-! Properties of the `Channel` model, for every channel size, every list of
task operations, and every interleaving (`Reach (init sz ops) s`). -/

namespace JuliaLean.Channels

/-- Values of the `put!` calls that returned (a buffered `put!` returns after
pushing, an unbuffered one after handing the value to a taker). -/
def putsDone (s : St) : List Val :=
  s.tasks.flatMap fun t =>
    match t.op, t.pc with
    | .put v, .done (.ok _) => [v]
    | _, _ => []

/-- Values a `take!` or `iterate` returned, or was handed by an unbuffered
`put!` (`schedule(taker, v)`) and will return when it runs. -/
def received (s : St) : List Val :=
  s.tasks.flatMap fun t =>
    match t.op, t.pc with
    | .take, .done (.ok (some v)) => [v]
    | .iter, .done (.ok (some v)) => [v]
    | _, .woken (.takeUnb _) (.val v) => [v]
    | _, _ => []

/-- No item is lost or duplicated: under every interleaving, the values of the
completed `put!` calls are, as a multiset, exactly the values received by
`take!`/`iterate`, plus those still in the buffer, plus those discarded by
`empty!`. (`put!` docstring, base/channels.jl:389-399: "Append an item `v` to
the channel"; `take!`, lines 537-541: "Removes and returns a value".) -/
def PutTakeConservation : Prop :=
  ∀ (sz : Nat) (ops : List Op) (s : St), Reach (init sz ops) s →
    List.Perm (putsDone s) (received s ++ s.ch.data ++ s.dropped)

/-- A buffered channel never holds more than `sz_max` items, and an unbuffered
one never stores any (`Channel` docstring, base/channels.jl:13-21: "an internal
buffer that can hold a maximum of `size` objects"). -/
def BufferBound : Prop :=
  ∀ (sz : Nat) (ops : List Op) (s : St), Reach (init sz ops) s → s.ch.data.length ≤ sz

/-- `fetch` does not remove: a step of a `fetch` task never changes the buffer,
and a value it returns is the first item (`fetch` docstring,
base/channels.jl:489-492: "Waits for and returns (without removing) the first
available item"). -/
def FetchKeeps : Prop :=
  ∀ (sz : Nat) (ops : List Op) (s s' : St) (i : Nat), Reach (init sz ops) s →
    (s.tasks[i]?.map Task.op) = some .fetch → stepTask s i = some s' →
      s'.ch.data = s.ch.data ∧
      ∀ v, (s'.tasks[i]?.map Task.pc) = some (.done (.ok (some v))) → s.ch.data.head? = some v

/-- `close` wakes every waiter: once a channel is closed no task is queued on
any of its conditions, and every task still blocked in a channel operation is
a taker that an unbuffered `put!` has already chosen and will hand its value
(`close` docstring, base/channels.jl:191-197; `bind`, line 282: "Any uncaught exception in
the task is propagated to all waiters"). -/
def CloseWakesWaiters : Prop :=
  ∀ (sz : Nat) (ops : List Op) (s : St), Reach (init sz ops) s → s.ch.isOpen = false →
    s.ch.qTake = [] ∧ s.ch.qPut = [] ∧ s.ch.qWait = [] ∧
    ∀ (i : Nat) (k : Park), (s.tasks[i]?.map Task.pc) = some (.parked k) →
      ∃ (j : Nat) (v : Val), (s.tasks[j]?.map Task.pc) = some (.handoff v i)

/-- `take!` on an empty closed channel throws the close exception at once
(`InvalidStateException("Channel is closed.", :closed)` after `close(c)`)
(`close` docstring, base/channels.jl:191-197: "An exception (optionally given
by `excp`), is thrown by ... `take!` and `fetch` on an empty, closed channel"). -/
def TakeClosedEmptyThrows : Prop :=
  ∀ (sz : Nat) (ops : List Op) (s : St) (i : Nat), Reach (init sz ops) s →
    s.ch.isOpen = false → s.ch.data = [] → s.tasks[i]? = some { op := .take, pc := .start } →
      ∃ s', stepTask s i = some s' ∧ (s'.tasks[i]?.map Task.pc) = some (.done (.err s.ch.excp))

/-- `iterate(c)` returns `nothing` only on a closed channel with an empty
buffer, so `for x in c` sees every item (`iterate`, base/channels.jl:769-792;
`isopen` docstring, base/channels.jl:217-218: "a `Channel` can be closed and
still have buffered elements which can be consumed"). -/
def IterateEndsDrained : Prop :=
  ∀ (sz : Nat) (ops : List Op) (s s' : St) (i : Nat), Reach (init sz ops) s →
    (s.tasks[i]?.map Task.op) = some .iter → stepTask s i = some s' →
      (s'.tasks[i]?.map Task.pc) = some (.done (.ok none)) →
        s.ch.isOpen = false ∧ s.ch.data = []

/-- Woken `put!` calls of a buffered channel that have not run yet. -/
def wokenPutBuf (s : St) : Nat :=
  s.tasks.countP fun t => match t.pc with | .woken (.putBuf _) _ => true | _ => false

/-- Woken `put!` calls of an unbuffered channel that have not run yet. -/
def wokenPutUnb (s : St) : Nat :=
  s.tasks.countP fun t => match t.pc with | .woken (.putUnb _) _ => true | _ => false

/-- No lost wake-up: a task sleeps in a channel condition only while its
operation cannot proceed, or while a woken `put!` that will let it proceed has
not run yet. Buffered: takers, fetchers and `wait(c)` sleep only on an empty
buffer; `put!` sleeps only when the buffer plus the woken `put!`s fill it.
Unbuffered: `put!` and `take!` never both sleep unless a woken `put!` will
pair with a sleeping taker; `wait(c)` sleeps only while no `put!` is pending.
(Invariant behind the "Blocks until" clauses of the `put!`, `take!`, `fetch`,
and `wait` docstrings.) -/
def NoLostWakeup : Prop :=
  ∀ (sz : Nat) (ops : List Op) (s : St), Reach (init sz ops) s →
    (0 < sz →
      (s.ch.qTake ≠ [] → s.ch.data = []) ∧
      (s.ch.qPut ≠ [] → sz ≤ s.ch.data.length + wokenPutBuf s)) ∧
    (sz = 0 →
      (s.ch.qPut ≠ [] → s.ch.qTake ≠ [] → 0 < wokenPutUnb s) ∧
      (s.ch.qWait ≠ [] → s.ch.nAvail = 0))

/-- For an unbuffered channel, `isready(c)` (`n_avail(c) > 0`) holds exactly
when some task is in a `put!` waiting for a taker (`isready` docstring,
base/channels.jl:615: "For unbuffered channels, return `true` if there are
tasks waiting on a `put!`"). -/
def IsreadyUnbuffered : Prop :=
  ∀ (ops : List Op) (s : St), Reach (init 0 ops) s →
    (0 < s.ch.nAvail ↔ ∃ (i : Nat) (v : Val),
      (s.tasks[i]?.map Task.pc) = some (.parked (.putUnb v)) ∨
      ∃ w, (s.tasks[i]?.map Task.pc) = some (.woken (.putUnb v) w))

/-- For a buffered channel, `isready(c)` implies that a value is stored
(`isready` docstring, base/channels.jl:612: "Determine whether a `Channel` has
a value stored in it"). -/
def IsreadyBufferedStored : Prop :=
  ∀ (sz : Nat) (ops : List Op) (s : St), Reach (init sz ops) s → 0 < sz →
    0 < s.ch.nAvail → s.ch.data ≠ []

end JuliaLean.Channels

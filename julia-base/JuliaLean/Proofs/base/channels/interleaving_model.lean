import JuliaLean.base.channels
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














namespace St




end St


open St












/-- States reachable from `s` when the scheduler may run any runnable task at
each step. -/
inductive Reach : St → St → Prop
  | refl (s : St) : Reach s s
  | step {s s' s'' : St} (i : Nat) : Reach s s' → stepTask s' i = some s'' → Reach s s''


end JuliaLean.Channels

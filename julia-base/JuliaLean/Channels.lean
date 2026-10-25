import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Channels.Model
import JuliaLean.Channels.Props
import JuliaLean.Channels.Refutations
import JuliaLean.Channels.Proofs
import JuliaLean.Channels.Locks
import JuliaLean.Channels.ThreadsFor

namespace JuliaLean.Channels

open JuliaLean.Registry

/-- Entries about `Channel` (base/channels.jl). -/
def channelEntries : List Entry := [
  { id := "channels-put-take-conservation", juliaFile := "base/channels.jl"
    juliaFns := ["put!(::Channel, v)", "put_buffered", "put_unbuffered", "take!(::Channel)", "take_buffered", "take_unbuffered", "iterate(::Channel)", "empty!(::Channel)", "close(::Channel)"]
    statement := "Under every interleaving of put!/take!/iterate/fetch/wait/close/empty! tasks on a channel of any size, the values of completed put! calls equal, as a multiset, the values received by take!/iterate plus those still buffered plus those discarded by empty!: no item is lost or duplicated."
    source := "base/channels.jl:389-399 (put! docstring: \"Append an item v to the channel\"), 537-541 (take!: \"Removes and returns a value\"); invariant"
    status := .proven, prop := ``PutTakeConservation, thm := some ``putTakeConservation
    notes := "Model: Channels/Model.lean, one atomic step per lock-protected section, scheduler may run any runnable task; no cancellation tokens (master only). Differential test: 1500 single-thread scenarios against 1.13.2 and nightly with a FIFO scheduler, 0 mismatches; 400 multithreaded stress trials (-t 4) found no loss or duplication." },
  { id := "channels-buffer-bound", juliaFile := "base/channels.jl"
    juliaFns := ["put_buffered", "Channel{T}(sz)"]
    statement := "A channel never stores more than sz_max items (an unbuffered one stores none), under every interleaving."
    source := "base/channels.jl:13-21 (Channel docstring: \"an internal buffer that can hold a maximum of size objects\")"
    status := .proven, prop := ``BufferBound, thm := some ``bufferBound },
  { id := "channels-fetch-keeps", juliaFile := "base/channels.jl"
    juliaFns := ["fetch(::Channel)", "fetch_buffered"]
    statement := "A step of a fetch task never changes the buffer, and a value fetch returns is the first buffered item."
    source := "base/channels.jl:489-492 (fetch docstring: \"Waits for and returns (without removing) the first available item\")"
    status := .proven, prop := ``FetchKeeps, thm := some ``fetchKeeps },
  { id := "channels-close-wakes-waiters", juliaFile := "base/channels.jl"
    juliaFns := ["close(::Channel, excp)", "notify_error"]
    statement := "Once a channel is closed no task is queued on its conditions, and every task still blocked in a channel operation is a taker already chosen by an unbuffered put! that will hand it its value."
    source := "base/channels.jl:191-197 (close docstring) and 282 (bind: \"Any uncaught exception in the task is propagated to all waiters\")"
    status := .proven, prop := ``CloseWakesWaiters, thm := some ``closeWakesWaiters },
  { id := "channels-take-closed-empty", juliaFile := "base/channels.jl"
    juliaFns := ["take!(::Channel)", "check_channel_state"]
    statement := "take! on a closed channel with an empty buffer throws the close exception (InvalidStateException after close(c)) without blocking."
    source := "base/channels.jl:191-197 (close docstring: the exception \"is thrown by ... take! and fetch on an empty, closed channel\")"
    status := .proven, prop := ``TakeClosedEmptyThrows, thm := some ``takeClosedEmptyThrows },
  { id := "channels-iterate-drains", juliaFile := "base/channels.jl"
    juliaFns := ["iterate(::Channel)"]
    statement := "iterate(c) returns nothing only when the channel is closed and its buffer is empty, so for x in c sees every item."
    source := "base/channels.jl:769-792; isopen docstring 214-218: \"a Channel can be closed and still have buffered elements which can be consumed\""
    status := .proven, prop := ``IterateEndsDrained, thm := some ``iterateEndsDrained },
  { id := "channels-no-lost-wakeup", juliaFile := "base/channels.jl"
    juliaFns := ["put_buffered", "put_unbuffered", "take_buffered", "take_unbuffered", "fetch_buffered", "wait(::Channel)", "empty!(::Channel)"]
    statement := "A task sleeps on a channel condition only while its operation cannot proceed or a woken put! that will let it proceed has not yet run (buffered: takers sleep only on an empty buffer, putters only when buffer plus woken putters fill it; unbuffered: put! and take! never both sleep unpaired; wait(c) sleeps only with no pending put!)."
    source := "invariant behind the \"Blocks until\" clauses of the put!, take!, fetch and wait docstrings (base/channels.jl:389-399, 489-512, 537-566, 703-726)"
    status := .proven, prop := ``NoLostWakeup, thm := some ``noLostWakeup },
  { id := "channels-isready-unbuffered", juliaFile := "base/channels.jl"
    juliaFns := ["isready(::Channel)", "n_avail(::Channel)", "put_unbuffered"]
    statement := "For an unbuffered channel, isready(c) holds exactly when some task is in a put! waiting for a taker."
    source := "base/channels.jl:615 (isready docstring: \"For unbuffered channels, return true if there are tasks waiting on a put!\")"
    status := .proven, prop := ``IsreadyUnbuffered, thm := some ``isreadyUnbuffered },
  { id := "channels-isready-buffered-stored", juliaFile := "base/channels.jl"
    juliaFns := ["isready(::Channel)", "n_avail(::Channel)", "put_buffered", "take_buffered"]
    statement := "For a buffered channel, isready(c) implies that a value is stored in the buffer."
    source := "base/channels.jl:612 (isready docstring: \"Determine whether a Channel has a value stored in it\")"
    status := .refuted, prop := ``IsreadyBufferedStored, thm := some ``isreadyBufferedStored_refuted
    issue := "none found; related #41833 (introduced the eager n_avail count), #31520 (queries: issues 'isready Channel', 'isready buffered channel', 'n_avail', 'Channel items available show', 'isready true take blocks'; prs 'isready Channel', 'n_avail')"
    notes := "Channel(1): put!(c, 1); a second put! blocks; take!(c) wakes it without running it, so n_avail == 1 and the buffer is empty. Same code in 1.13.2. Reproducer: repro/channels-isready-buffered-stored.jl." }
]

/-- Registry entries of this area. -/
def entries : List Entry := channelEntries ++ lockEntries ++ threadsEntries

end JuliaLean.Channels

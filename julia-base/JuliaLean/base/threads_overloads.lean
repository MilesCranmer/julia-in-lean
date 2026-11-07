import JuliaLean.Proofs.base.locks_mt.common
import JuliaLean.base.locks_mt

/-!
# Model of `base/threads_overloads.jl`

The worker, range, atomic, task, and synchronization primitives are typed
interfaces to their models in the other Base files. The loops and error paths
from this file remain explicit here.
-/

namespace JuliaLean.base.threads_overloads

abbrev M (Error World A : Type) := JuliaLean.base.locks_mt.M Error World A

inductive ScheduleKind where
  | static
  | fair
  deriving DecidableEq, Repr

structure Ops (Error World F Channel Item Schedule Atomic Task IterState Count Result : Type) where
  call : F → Item → M Error World Result
  spawn : {A : Type} → (Unit → M Error World A) → M Error World Task
  wait : Task → M Error World Result
  sync : M Error World Unit → M Error World Unit
  newAtomicBool : Bool → M Error World Atomic
  atomicLoadDefault : Atomic → M Error World Bool
  atomicStoreDefault : Atomic → Bool → M Error World Unit
  iterate : Channel → Option IterState → M Error World (Option (Item × IterState))
  rangeStartOneTo : Count → M Error World (Option Nat)
  rangeNext : Count → Nat → M Error World (Option Nat)
  scheduleKind : Schedule → Option ScheduleKind
  scheduleMethodError : Error
  fairSchedule : Schedule
  threadpoolSize : M Error World Count

abbrev Apply (Error World F Item Result : Type) := F → Item → M Error World Result

/--
Julia source: base/threads_overloads.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_apply_for_schedule(::Threads.StaticSchedule) = (f, x) -> f(x)
```
-/
def applyForStatic {Error World F Channel Item Schedule Atomic Task IterState Count Result : Type}
    (ops : Ops Error World F Channel Item Schedule Atomic Task IterState Count Result) :
    Apply Error World F Item Result :=
  fun f item => ops.call f item

/--
Julia source: base/threads_overloads.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_apply_for_schedule(::Threads.FairSchedule) = (f, x) -> wait(Threads.@spawn f(x))
```
-/
def applyForFair {Error World F Channel Item Schedule Atomic Task IterState Count Result : Type}
    (ops : Ops Error World F Channel Item Schedule Atomic Task IterState Count Result) :
    Apply Error World F Item Result := fun f item => do
  let task ← ops.spawn (fun _ => ops.call f item)
  ops.wait task

private def applyForSchedule {Error World F Channel Item Schedule Atomic Task IterState Count Result : Type}
    (ops : Ops Error World F Channel Item Schedule Atomic Task IterState Count Result)
    (schedule : Schedule) : M Error World (Apply Error World F Item Result) := do
  match ops.scheduleKind schedule with
  | some .static => pure (applyForStatic ops)
  | some .fair => pure (applyForFair ops)
  | none => throw ops.scheduleMethodError

private def workerLoop {Error World F Channel Item Schedule Atomic Task IterState Count Result : Type}
    (ops : Ops Error World F Channel Item Schedule Atomic Task IterState Count Result)
    (apply : Apply Error World F Item Result) (stop : Atomic) (f : F) (channel : Channel) :
    M Error World Unit :=
  JuliaLean.base.locks_mt.loop (fun state => do
    match ← ops.iterate channel state with
    | none => pure (.inl ())
    | some (item, next) => do
      let _ ← apply f item
      if ← ops.atomicLoadDefault stop then pure (.inl ())
      else pure (.inr (some next))) (none : Option IterState)

private def worker {Error World F Channel Item Schedule Atomic Task IterState Count Result : Type}
    (ops : Ops Error World F Channel Item Schedule Atomic Task IterState Count Result)
    (apply : Apply Error World F Item Result) (stop : Atomic) (f : F) (channel : Channel) :
    M Error World Unit :=
  tryCatch (workerLoop ops apply stop f channel) (fun error => do
    ops.atomicStoreDefault stop true
    throw error)

private def spawnWorkers {Error World F Channel Item Schedule Atomic Task IterState Count Result : Type}
    (ops : Ops Error World F Channel Item Schedule Atomic Task IterState Count Result)
    (apply : Apply Error World F Item Result) (stop : Atomic) (f : F) (channel : Channel)
    (count : Count) (cursor : Option Nat) : M Error World Unit :=
  JuliaLean.base.locks_mt.loop (fun cursor => do
    match cursor with
    | none => pure (.inl ())
    | some index => do
      let _ ← ops.spawn (fun _ => worker ops apply stop f channel)
      let next ← ops.rangeNext count index
      pure (.inr next)) cursor

/--
Julia source: base/threads_overloads.jl:41-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Threads.foreach(f, channel::Channel;
                         schedule::Threads.AbstractSchedule=Threads.FairSchedule(),
                         ntasks=Threads.threadpoolsize())
    apply = _apply_for_schedule(schedule)
    stop = Threads.Atomic{Bool}(false)
    @sync for _ in 1:ntasks
        Threads.@spawn try
            for item in channel
                $apply(f, item)
                # do `stop[] && break` after `f(item)` to avoid losing `item`.
                # this isn't super comprehensive since a task could still get
                # stuck on `take!` at `for item in channel`. We should think
                # about a more robust mechanism to avoid dropping items. See also
                # https://github.com/JuliaLang/julia/pull/34543#discussion_r422695217
                stop[] && break
            end
        catch
            @atomic stop[] = true
            rethrow()
        end
    end
    return nothing
end
```
-/
def foreach {Error World F Channel Item Schedule Atomic Task IterState Count Result : Type}
    (ops : Ops Error World F Channel Item Schedule Atomic Task IterState Count Result)
    (f : F) (channel : Channel) (schedule : Option Schedule := none)
    (ntasks : Option Count := none) : M Error World Unit := do
  let schedule := schedule.getD ops.fairSchedule
  let ntasks ← match ntasks with
    | some count => pure count
    | none => ops.threadpoolSize
  let apply ← applyForSchedule ops schedule
  let stop ← ops.newAtomicBool false
  ops.sync do
    let cursor ← ops.rangeStartOneTo ntasks
    spawnWorkers ops apply stop f channel ntasks cursor

end JuliaLean.base.threads_overloads

namespace JuliaLean.ConcurrencyCov.ThreadsOverloads

open JuliaLean.ConcurrencyCov

inductive Schedule where | static | fair
  deriving DecidableEq, Repr
inductive ApplyMode where | direct | spawnedAndWaited
  deriving DecidableEq, Repr
def applyForSchedule : Schedule → ApplyMode
  | .static => .direct
  | .fair => .spawnedAndWaited
/-- One complete execution in which all `ntasks` workers finish normally. Tasks
share the channel, so the scheduler supplies a partition of its items. -/
def threadedForeach {α : Type} (schedule : Schedule) (ntasks : Nat)
    (assignments : List (List α)) (f : α → Nat) : R (List Nat) :=
  if assignments.length != ntasks then .error (.assertionError "worker count")
  else
    let _apply := applyForSchedule schedule
    .ok (assignments.flatMap (List.map f))

end JuliaLean.ConcurrencyCov.ThreadsOverloads

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

/-! ## `base/threads_overloads.jl` -/

inductive ForeachOutcome where | ok (values : List Nat) | failed (values : List Nat)
  deriving DecidableEq, Repr

def foreachWorker (apply : Nat → R Nat) : List Nat → ForeachOutcome
  | [] => .ok []
  | item :: rest =>
    match apply item with
    | .error _ => .failed []
    | .ok value =>
      match foreachWorker apply rest with
      | .ok values => .ok (value :: values)
      | .failed values => .failed (value :: values)

def threadsForeach (apply : Nat → R Nat) (ntasks : Nat)
    (assignments : List (List Nat)) : R (List ForeachOutcome) :=
  if assignments.length != ntasks then .error (.assertionError "worker count")
  else .ok (assignments.map (foreachWorker apply))

inductive ApplyTrace where | called | spawned | waited
  deriving DecidableEq, Repr

def applyStatic (f : Nat → Nat) (x : Nat) : Nat × List ApplyTrace := (f x, [.called])

def applyFair (f : Nat → Nat) (x : Nat) : Nat × List ApplyTrace := (f x, [.spawned, .called, .waited])

end JuliaLean.ConcurrencyCov.FaithfulSmall

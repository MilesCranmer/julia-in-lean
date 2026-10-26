import JuliaLean.Tasks

/-! Deterministic model differential corpus. -/

namespace JuliaLean.Tasks.Validation

open JuliaLean.Tasks

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def event (task : Nat) (action : TaskAction) : ScheduledAction := ⟨task, action⟩

private def childResult (id : Nat) : ChildResult :=
  if id = 1 || id = 2 || id = 3 then .failure id else .success

private def parentScope : Scope := fun key =>
  if key = 0 then some 1 else if key = 1 then some 2 else none

def differential : IO Unit := do
  let initial : Scheduler := fun _ => .created
  let queued := schedulerRun [event 0 .schedule] initial
  let finished := schedulerRun [event 0 .start, event 0 (.finish 7)] queued
  require (decide (istaskstarted (initial 0) = false ∧ istaskdone (initial 0) = false ∧
    istaskfailed (initial 0) = false)) "created task observation"
  require (decide (istaskstarted (queued 0) = false ∧ istaskdone (queued 0) = false ∧
    istaskfailed (queued 0) = false)) "queued task observation"
  require (decide (istaskstarted (finished 0) = true ∧ istaskdone (finished 0) = true ∧
    istaskfailed (finished 0) = false ∧ fetchTask (finished 0) = .returned 7))
    "finished task observation"
  require (decide (waitTask (.failed 99 true) = .threw .taskFailed ∧
    fetchTask (.failed 99 true) = .threw .taskFailed)) "failed task observation"
  IO.println "task-states: created -> queued -> done; failures wrap the same task"

  let cancelled := cancellationRun [1, 1, 3, 1] 0
  require (decide (cancelled = 3 ∧ raiseCancellation 1 1 = (false, 1) ∧
    raiseCancellation 1 3 = (true, 3))) "cancellation severity"
  IO.println "cancellation: 0 -> 1 -> 3; repeated/lower requests unchanged"

  require (decide (syncEnd [1, 2, 3] childResult = [1, 2, 3])) "sync failures"
  IO.println "sync-failures: [1, 2, 3] exactly once"

  let queue := [⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩]
  let first := notifyModel false queue
  let second := notifyModel false first.remaining
  let third := notifyModel false second.remaining
  require (decide ([first.count, second.count, third.count] = [1, 1, 1] ∧
    first.woken.length + second.woken.length + third.woken.length = 3)) "notify one"
  IO.println "notify-one: counts=[1, 1, 1], completed=[1, 2, 3]"

  let inputs := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  let square := fun x : Nat => x * x
  let order := [8, 4, 0, 11, 2, 7, 1, 10, 5, 3, 9, 6]
  let expected := inputs.map fun x => some (square x)
  for workers in [0, 1, 2, 4, 3] do
    let slots := asyncmapModel square inputs workers none order
    let actual := (List.range inputs.length).map slots
    require (decide (actual = expected)) "asyncmap order"
  let batched := asyncmapModel square inputs 3 (some 2) order
  require (decide ((List.range inputs.length).map batched = expected)) "batched asyncmap order"
  IO.println "asyncmap-order: ntasks=0,1,2,4,dynamic; batch_size=2"

  let q0 : List Nat := []
  let q1 := linkedListRun [.push 1, .push 2, .push 3] q0
  let q2 := linkedListRun [.delete 2] q1
  let q3 := linkedListRun [.pop] q2
  let q4 := linkedListRun [.pop] q3
  let q5 := linkedListRun [.push 2] q4
  require (decide (q1 = [1, 2, 3] ∧ q2 = [1, 3] ∧ q3 = [1] ∧ q4 = [] ∧ q5 = [2]))
    "linked list"
  IO.println "linked-list: [1,2,3] -> [1,3] -> [1] -> [] -> [2]"

  let outer := enterScope parentScope [(0, 10)]
  let inner := enterScope outer [(0, 20), (1, 30)]
  let restored := (withScope parentScope [(0, 40)] (fun _ => .error 40)).2
  let child := createTaskScope (enterScope parentScope [(0, 50)])
  require (decide (outer 0 = some 10 ∧ outer 1 = some 2 ∧ inner 0 = some 20 ∧
    inner 1 = some 30 ∧ restored 0 = some 1 ∧ child 0 = some 50 ∧ parentScope 0 = some 1))
    "scoped values"
  IO.println "scoped-values: nested restore, exception restore, child=50 parent=1"

  let actions : List AtomicAction := [.add 2, .sub 7, .exchange 9, .cas 8 4, .cas 9 4]
  require (decide (atomicRun 3 actions = (4 : AtomicInt))) "atomic arithmetic and cas"
  require (decide (atomicUpdate (.add 1) 0x7fffffffffffffff =
    (0x8000000000000000 : AtomicInt))) "atomic wrapping add"
  require (decide (atomicUpdate (.band 2) 3 = (2 : AtomicInt) ∧
    atomicUpdate (.bnand 2) 3 = ~~~(2 : AtomicInt) ∧
    atomicUpdate (.bor 7) 5 = (7 : AtomicInt) ∧
    atomicUpdate (.bxor 7) 5 = (2 : AtomicInt) ∧
    atomicUpdate (.max 7) 5 = (7 : AtomicInt) ∧
    atomicUpdate (.min 5) 7 = (5 : AtomicInt))) "atomic bitwise and extrema"
  IO.println "atomics: cas,xchg,add,sub,and,nand,or,xor,min,max"
  IO.println "DIFFERENTIAL OK"

end JuliaLean.Tasks.Validation

def main : IO Unit := JuliaLean.Tasks.Validation.differential

import JuliaLean.Core

/-!
Executable task-state, scheduler, wait/fetch, and structured-concurrency models.
The scheduler deliberately chooses task identifiers through an explicit action
list, so every list is one possible interleaving.
-/

namespace JuliaLean.Tasks

inductive TaskState where
  | runnable
  | done
  | failed
  | abandoned
  deriving Repr, DecidableEq

/-- The observable task phases behind `base/task.jl:150-269,1234-1490`.
The Boolean on `queued` and `failed` records the runtime's independent
"has started" bit. An empty thread pool can fail a queued task before start. -/
inductive TaskPhase where
  | created
  | queued (started : Bool)
  | running
  | waiting
  | done (value : Nat)
  | failed (error : Nat) (started : Bool)
  | abandoned
  deriving Repr, DecidableEq

def taskState : TaskPhase → TaskState
  | .created | .queued _ | .running | .waiting => .runnable
  | .done _ => .done
  | .failed _ _ => .failed
  | .abandoned => .abandoned

/-- `istaskdone`, `base/task.jl:223`: every state other than runnable is done. -/
def istaskdone (t : TaskPhase) : Bool := taskState t != .runnable

/-- `istaskstarted`, `base/task.jl:240`: queued fresh tasks have not run yet. -/
def istaskstarted : TaskPhase → Bool
  | .created => false
  | .queued started => started
  | .failed _ started => started
  | .running | .waiting | .done _ | .abandoned => true

/-- `istaskfailed`, `base/task.jl:267-270`: abandoned tasks count as failed. -/
def istaskfailed (t : TaskPhase) : Bool :=
  taskState t == .failed || taskState t == .abandoned

inductive TaskAction where
  | schedule
  | start
  | yield
  | wait
  | wake
  | finish (value : Nat)
  | fail (error : Nat)
  | failEmptyPool (error : Nat)
  | abandon
  deriving Repr, DecidableEq

/-- Relevant branches of `schedule`, `yield`, `wait`, task completion, and
abandonment (`base/task.jl:1234-1490,1661-1691`). Invalid scheduler actions
leave the task unchanged, matching the model's restriction to legal steps. -/
def taskStep (action : TaskAction) (t : TaskPhase) : TaskPhase :=
  match action, t with
  | .schedule, .created => .queued false
  | .schedule, .waiting => .queued true
  | .start, .queued _ => .running
  | .yield, .running => .queued true
  | .wait, .running => .waiting
  | .wake, .waiting => .queued true
  | .finish value, .running => .done value
  | .fail error, .running => .failed error true
  | .failEmptyPool error, .queued started => .failed error started
  | .abandon, .running => .abandoned
  | _, _ => t

structure ScheduledAction where
  task : Nat
  action : TaskAction
  deriving Repr, DecidableEq

abbrev Scheduler := Nat → TaskPhase

def schedulerStep (event : ScheduledAction) (s : Scheduler) : Scheduler :=
  fun i => if i = event.task then taskStep event.action (s event.task) else s i

def schedulerRun : List ScheduledAction → Scheduler → Scheduler
  | [], s => s
  | event :: events, s => schedulerRun events (schedulerStep event s)

private theorem taskStep_terminal (action : TaskAction) (t : TaskPhase)
    (done : istaskdone t = true) : taskStep action t = t := by
  cases action <;> cases t <;> simp_all [istaskdone, taskState, taskStep]

private theorem taskStep_started (action : TaskAction) (t : TaskPhase)
    (started : istaskstarted t = true) : istaskstarted (taskStep action t) = true := by
  cases action <;> cases t <;> simp_all [istaskstarted, taskStep]

private theorem schedulerStep_terminal (event : ScheduledAction) (s : Scheduler) (i : Nat)
    (done : istaskdone (s i) = true) : schedulerStep event s i = s i := by
  by_cases h : i = event.task
  · subst i
    simp [schedulerStep, taskStep_terminal _ _ done]
  · simp [schedulerStep, h]

private theorem schedulerStep_started (event : ScheduledAction) (s : Scheduler) (i : Nat)
    (started : istaskstarted (s i) = true) :
    istaskstarted (schedulerStep event s i) = true := by
  by_cases h : i = event.task
  · subst i
    simp [schedulerStep, taskStep_started _ _ started]
  · simpa [schedulerStep, h] using started

private theorem schedulerRun_terminal (events : List ScheduledAction) (s : Scheduler) (i : Nat)
    (done : istaskdone (s i) = true) : schedulerRun events s i = s i := by
  induction events generalizing s with
  | nil => rfl
  | cons event events ih =>
      rw [schedulerRun]
      have step := schedulerStep_terminal event s i done
      have stillDone : istaskdone (schedulerStep event s i) = true := by simpa [step] using done
      exact (ih (schedulerStep event s) stillDone).trans step

private theorem schedulerRun_started (events : List ScheduledAction) (s : Scheduler) (i : Nat)
    (started : istaskstarted (s i) = true) :
    istaskstarted (schedulerRun events s i) = true := by
  induction events generalizing s with
  | nil => exact started
  | cons event events ih =>
      rw [schedulerRun]
      exact ih (schedulerStep event s) (schedulerStep_started event s i started)

/-- Every explicit scheduler interleaving preserves terminal states and the
started bit. This is the monotonicity promised by the task-state queries. -/
def TaskStateMonotone : Prop :=
  ∀ (initial : Scheduler) (events : List ScheduledAction) (i : Nat),
    (istaskdone (initial i) = true → schedulerRun events initial i = initial i) ∧
    (istaskstarted (initial i) = true →
      istaskstarted (schedulerRun events initial i) = true)

theorem taskStateMonotone_proven : TaskStateMonotone := by
  intro initial events i
  exact ⟨schedulerRun_terminal events initial i, schedulerRun_started events initial i⟩

inductive TaskError where
  | taskFailed
  deriving Repr, DecidableEq

inductive Await (α : Type) where
  | blocked
  | returned (value : α)
  | threw (error : TaskError)
  deriving Repr, DecidableEq

/-- `wait(t; throw=true)`, `base/task.jl:494-509`. -/
def waitTask : TaskPhase → Await Unit
  | .done _ => .returned ()
  | .failed _ _ | .abandoned => .threw .taskFailed
  | _ => .blocked

/-- `fetch(t)`, `base/task.jl:727-741`. -/
def fetchTask : TaskPhase → Await Nat
  | .done value => .returned value
  | .failed _ _ | .abandoned => .threw .taskFailed
  | _ => .blocked

def TaskWaitFetchContract : Prop :=
  ∀ (t : TaskPhase),
    match t with
    | .done value => waitTask t = .returned () ∧ fetchTask t = .returned value
    | .failed _ _ | .abandoned =>
        waitTask t = .threw .taskFailed ∧ fetchTask t = .threw .taskFailed
    | _ => waitTask t = .blocked ∧ fetchTask t = .blocked

theorem taskWaitFetchContract_proven : TaskWaitFetchContract := by
  intro t
  cases t <;> simp [waitTask, fetchTask]

inductive ChildResult where
  | success
  | failure (error : Nat)
  deriving Repr, DecidableEq

def childFailed : ChildResult → Bool
  | .success => false
  | .failure _ => true

/-- The task branch of `sync_end`, `base/task.jl:782-837`: wait for each
registered child and append one `TaskFailedException` when it failed. -/
def syncEnd : List Nat → (Nat → ChildResult) → List Nat
  | [], _ => []
  | child :: children, result =>
      if childFailed (result child) then child :: syncEnd children result
      else syncEnd children result

/-- A lexical `@async` registers its task once (`base/task.jl:965-979`), so a
NoDup registration list produces one report for each and only each failure. -/
def SyncReportsEachFailureOnce : Prop :=
  ∀ (children : List Nat) (result : Nat → ChildResult), children.Nodup →
    (syncEnd children result).Nodup ∧
    ∀ child, child ∈ syncEnd children result ↔
      child ∈ children ∧ childFailed (result child) = true

theorem syncReportsEachFailureOnce_proven : SyncReportsEachFailureOnce := by
  intro children result nodup
  have mem : ∀ (xs : List Nat) (x : Nat), x ∈ syncEnd xs result ↔
      x ∈ xs ∧ childFailed (result x) = true := by
    intro xs
    induction xs with
    | nil => simp [syncEnd]
    | cons y ys ih =>
        intro x
        by_cases h : childFailed (result y) = true
        · simp only [syncEnd, h, ↓reduceIte, List.mem_cons, ih]
          constructor
          · intro found
            rcases found with same | rest
            · subst x; exact ⟨Or.inl rfl, h⟩
            · exact ⟨Or.inr rest.1, rest.2⟩
          · intro expected
            rcases expected.1 with same | inRest
            · exact Or.inl same
            · exact Or.inr ⟨inRest, expected.2⟩
        · have hf : childFailed (result y) = false := by
            cases value : childFailed (result y) <;> simp_all
          simp only [syncEnd, hf, Bool.false_eq_true, ↓reduceIte, ih, List.mem_cons]
          constructor
          · intro found
            exact ⟨Or.inr found.1, found.2⟩
          · intro expected
            rcases expected.1 with same | inRest
            · subst x; exact False.elim (h expected.2)
            · exact ⟨inRest, expected.2⟩
  have unique : ∀ (xs : List Nat), xs.Nodup → (syncEnd xs result).Nodup := by
    intro xs hn
    induction xs with
    | nil => simp [syncEnd]
    | cons y ys ih =>
        have parts := List.nodup_cons.mp hn
        by_cases h : childFailed (result y) = true
        · simp [syncEnd, h, List.nodup_cons, ih parts.2, mem, parts.1]
        · have hf : childFailed (result y) = false := by
            cases value : childFailed (result y) <;> simp_all
          simpa [syncEnd, hf] using ih parts.2
  exact ⟨unique children nodup, mem children⟩

end JuliaLean.Tasks

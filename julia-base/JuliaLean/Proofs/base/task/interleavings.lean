import JuliaLean.base.task
import JuliaLean.Core

/-!
Executable task-state, scheduler, wait/fetch, and structured-concurrency models.
The scheduler deliberately chooses task identifiers through an explicit action
list, so every list is one possible interleaving.
-/

namespace JuliaLean.Tasks













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

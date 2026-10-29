import JuliaLean.CRuntime.WorldStop.ProjectionStep
import JuliaLean.CRuntime.WorldStop.Candidate

namespace JuliaLean.CRuntime.WorldStop

open Memory

/-- Established TLS/task fields; addresses 1, 2, 3 are logical allocation IDs. -/
def cachedPointerInitialMemory : Loc → Nat
  | .gcRunning => 1
  | .nThreads | .tlsSize | .gcNThreads => 3
  | .allTLS | .gcAllTLS => 1
  | .tlsSlot 1 i => if i < 3 then i + 1 else 0
  | .gcState 1 => 1
  | .gcState _ => 2
  | .safepoint 1 => 1
  | .safepoint 2 => 3
  | .safepoint _ => 2
  | .suspendCount 2 => 1
  | .currentTask p | .rootTask p => if 0 < p ∧ p ≤ 3 then p else 0
  | .tlsZeroed p | .heapReady p | .schedulerReady p | .rootFieldsReady p
  | .handlersReady p => if 0 < p ∧ p ≤ 3 then 1 else 0
  | .pageCount p => if 0 < p ∧ p ≤ 3 then 1 else 0
  | _ => 0

def canonicalInitialMemory (loc : Loc) : Nat :=
  match loc with
  | .gcRunning | .gcNThreads | .gcAllTLS => 0
  | .gcState 1 | .gcState 3 => 0
  | .safepoint 2 => 2
  | .suspendCount _ | .pageCount _ => 0
  | .pgcstack p => if 0 < p ∧ p ≤ 3 then p else 0
  | .tid p => p - 1
  | _ => cachedPointerInitialMemory loc

def canonicalRoles (t : Fin 3) : EntryPC :=
  if t.val = 0 then .collector else if t.val = 1 then .safeTarget else .controller

def canonicalInitial : Machine 3 :=
  { memory := canonicalInitialMemory
    threads := fun t =>
      { todo := entryCommands (canonicalRoles t)
        regs := fun r => match r with
          | .ptls => t.val + 1
          | .tid => if t.val = 2 then 1 else t.val
          | .waitstate => if t.val = 2 then 1 else 0
          | _ => 0
        criticalPermit := decide (t.val ≠ 1) }
    pageProtected := fun _ => false
    locks := fun _ => none
    conditions := fun _ => 0
    latest := fun loc =>
      ((List.finRange canonicalInitialEvents.size).find? fun i =>
        canonicalInitialEvents[i].action.location == some loc).map Fin.val
    moClock := fun _ => 0
    candidate := ⟨canonicalInitialEvents⟩ }

private theorem fin_three_cases (t : Fin 3) : t = 0 ∨ t = 1 ∨ t = 2 := by
  have h : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem canonicalInitial_publicEntry : PublicAPIEntry canonicalInitial canonicalRoles := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_, ?_, rfl, ?_⟩
    · intro i hi
      change i < 3 at hi
      have alternatives : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases alternatives with rfl | rfl | rfl <;> decide
    · exact (by decide : ∀ t : Fin 3, (canonicalInitial.threads t).regs .ptls ≤ 3)
    · intro impossible
      cases impossible
  · intro page
    exact ⟨rfl, rfl⟩
  · intro mutex
    rfl
  · intro t
    rcases fin_three_cases t with rfl | rfl | rfl <;>
      simp [ThreadAtPublicEntry, canonicalInitial, canonicalInitialMemory,
        canonicalRoles, cachedPointerInitialMemory]

theorem run_append (s : Machine n) (front back : List (Scheduled n)) :
    run s (front ++ back) = run (run s front) back := by
  induction front generalizing s with
  | nil => rfl
  | cons event rest ih => exact ih (advance s event)

def controllerAtResumeCall (s : Machine 3) : Bool :=
  match (project s).threads[2].todo with
  | .call _ _ .resumeThread :: _ => true
  | _ => false

def controllerAtResumeBranch (s : Machine 3) : Bool :=
  match (project s).threads[2].todo with
  | .branch file line _ _ _ :: _ => file == "src/safepoint.c" && line == 456
  | _ => false

def canonicalInitialProjection : WitnessProjection := project canonicalInitial

theorem canonicalInitial_projection : project canonicalInitial = canonicalInitialProjection := by rfl

theorem project_stage (s : Machine 3) (p out : WitnessProjection)
    (schedule : List (Scheduled 3)) (equal : project s = p)
    (supported : witnessRunSupported p schedule = true)
    (result : projectedRun p schedule = out) : project (run s schedule) = out := by
  rw [project_run s schedule (by rw [equal]; exact supported), equal, result]

theorem project_memory (s : Machine 3) (i : Nat) (h : i < 22) :
    (project s).memory[i] = s.memory witnessLocations[i] := by simp [project]

theorem project_page (s : Machine 3) (i : Nat) (h : i < 4) :
    (project s).pageProtected[i] = s.pageProtected i := by simp [project]

theorem project_lock (s : Machine 3) (i : Nat) (h : i < 7) :
    (project s).locks[i] = s.locks i := by simp [project]

theorem project_todo (s : Machine 3) (i : Nat) (h : i < 3) :
    (project s).threads[i].todo = (s.threads ⟨i, h⟩).todo := by simp [project, projectThread]

theorem project_reg (s : Machine 3) (i : Nat) (h : i < 3) (r : Reg) :
    (project s).threads[i].regs[witnessRegIndex r] = (s.threads ⟨i, h⟩).regs r := by
  simp [project, projectThread]

end JuliaLean.CRuntime.WorldStop

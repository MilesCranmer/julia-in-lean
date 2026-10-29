import JuliaLean.CRuntime.WorldStop.C11
import JuliaLean.Registry.Types

namespace JuliaLean.CRuntime.WorldStop

open Memory


/-- Raw UNSAFE source helpers contain no client critical operation.
`gc-stock.c:100-105`; `julia_threads.h:638-658`. -/
def commandHasClientCritical : Nat → Command → Bool
  | 0, _ => true
  | _ + 1, .stmt _ _ .critical => true
  | fuel + 1, .branch _ _ _ a b =>
      a.any (commandHasClientCritical fuel) || b.any (commandHasClientCritical fuel)
  | fuel + 1, .whileDo _ _ a _ b | fuel + 1, .testLoop _ _ a _ b =>
      a.any (commandHasClientCritical fuel) || b.any (commandHasClientCritical fuel)
  | _ + 1, _ => false

def rawUnsafeWindowContainsNoCriticalOperation : Prop :=
  ∀ p : Proc, (program p).any (commandHasClientCritical 64) = false

theorem rawUnsafeWindowContainsNoCriticalOperation_proven :
    rawUnsafeWindowContainsNoCriticalOperation := by
  intro p
  cases p <;> decide

/-- Source operations selected for local initialization/publication ordering.
`threading.c:369,401,415,420-424,466-479,557,598,616`;
`task.c:1553,1620-1622`; `safepoint.c:268`. -/
inductive Milestone where
  | disableAdd | tlsZero | heapInit | arrayPublish | slotWrite | countRelease
  | fieldsBegin | fieldsComplete | rootPublish | currentPublish | enableSub
  | exitRootClear | exitCurrentNull | exitSafe
  deriving DecidableEq, Repr

def selectedMilestone (file : String) (line : Nat) (op : Op) : Option Milestone :=
  match file, line, op with
  | "src/gc-stock.c", 3810, .fetchAdd (.fixed .disableCounter) 1 false => some .disableAdd
  | "src/gc-stock.c", 3808, .fetchAdd (.fixed .disableCounter) 1 true => some .enableSub
  | "src/threading.c", 369, .milestone _ _ => some .tlsZero
  | "src/threading.c", 401, .milestone _ _ => some .heapInit
  | "src/threading.c", 415, .store (.fixed .allTLS) .release _ => some .arrayPublish
  | "src/threading.c", 420, .plainStore (.tlsSlot _ _) _ => some .slotWrite
  | "src/threading.c", 422, .store (.fixed .nThreads) .release _ => some .countRelease
  | "src/task.c", 1553, .milestone (.rootFieldsReady _) _ => some .fieldsBegin
  | "src/task.c", 1620, .milestone (.rootFieldsReady _) _ => some .fieldsComplete
  | "src/task.c", 1621, .plainStore (.rootTask _) _ => some .rootPublish
  | "src/task.c", 1622, .store (.currentTask _) .relaxed _ => some .currentPublish
  | "src/threading.c", 557, .plainStore (.rootTask _) _ => some .exitRootClear
  | "src/threading.c", 598, .store (.currentTask _) .relaxed _ => some .exitCurrentNull
  | "src/safepoint.c", 268, .store (.gcState _) .release (.nat 2) => some .exitSafe
  | _, _, _ => none

private def combinePaths (a b : List (List Milestone)) : List (List Milestone) :=
  a.flatMap fun front => b.map fun suffix => front ++ suffix

/-- Branch paths of the source-control projection. Calls retain their return
continuations. Loops require empty selected body/condition paths; arbitrary
iteration counts preserve that projection. Fuel exhaustion rejects a path. -/
def projectedPaths : Nat → List Command → List (List Milestone)
  | 0, _ => []
  | _ + 1, [] => [[]]
  | fuel + 1, .stmt file line op :: tail =>
      let front := (selectedMilestone file line op).toList
      (projectedPaths fuel tail).map (front ++ ·)
  | fuel + 1, .call _ _ proc :: tail =>
      combinePaths (projectedPaths fuel (program proc)) (projectedPaths fuel tail)
  | _ + 1, .ret _ _ :: _ => [[]]
  | fuel + 1, .branch _ _ _ yes no :: tail =>
      projectedPaths fuel (yes ++ tail) ++ projectedPaths fuel (no ++ tail)
  | fuel + 1, .whileDo _ _ prelude _ body :: tail
  | fuel + 1, .testLoop _ _ prelude _ body :: tail =>
      let bodyPaths := projectedPaths fuel (prelude ++ body)
      if !bodyPaths.isEmpty && bodyPaths.all List.isEmpty then projectedPaths fuel tail else []

/-- Proof metadata for the actual selected stores. A registered count may
precede root-task construction; only root/current-task publication and the
enable decrement require completed root fields. `threading.c:420-423,476-479`.
The raw disable counter remains separately modeled in `Machine`. -/
structure PublicationFacts where
  disabled : Bool := false
  tls : Bool := false
  heap : Bool := false
  slot : Bool := false
  count : Bool := false
  fields : Bool := false
  root : Bool := false
  current : Bool := false
  enabled : Bool := false
  exitedSafe : Bool := false
  deriving DecidableEq, Repr

private def PublicationFacts.invariant (f : PublicationFacts) : Prop :=
  (f.slot = true → f.tls = true ∧ f.heap = true) ∧
  (f.count = true → f.slot = true) ∧
  (f.root = true → f.fields = true) ∧
  (f.current = true → f.fields = true) ∧
  (f.enabled = true → f.current = true ∧ f.fields = true ∧ f.disabled = false) ∧
  (f.exitedSafe = true → f.current = false ∧ f.enabled = false)

instance (f : PublicationFacts) : Decidable f.invariant := by
  unfold PublicationFacts.invariant
  infer_instance

def milestonePre (f : PublicationFacts) : Milestone → Bool
  | .disableAdd => !f.enabled
  | .tlsZero => f.disabled
  | .heapInit => f.tls
  | .arrayPublish => f.disabled && f.tls && f.heap
  | .slotWrite => f.disabled && f.tls && f.heap
  | .countRelease => f.slot
  | .fieldsBegin => f.disabled && !f.root && !f.current && !f.enabled
  | .fieldsComplete => f.disabled && f.tls && f.heap
  | .rootPublish => f.disabled && f.fields
  | .currentPublish => f.disabled && f.fields && f.root && !f.exitedSafe
  | .enableSub => f.disabled && f.current && f.fields && !f.exitedSafe
  | .exitRootClear => true
  | .exitCurrentNull => true
  | .exitSafe => !f.current && !f.enabled

def milestoneStep (f : PublicationFacts) : Milestone → PublicationFacts
  | .disableAdd => { f with disabled := true }
  | .tlsZero => { f with tls := true }
  | .heapInit => { f with heap := true }
  | .arrayPublish => f
  | .slotWrite => { f with slot := true }
  | .countRelease => { f with count := true }
  | .fieldsBegin => { f with fields := false }
  | .fieldsComplete => { f with fields := true }
  | .rootPublish => { f with root := true }
  | .currentPublish => { f with current := true }
  | .enableSub => { f with disabled := false, enabled := true }
  | .exitRootClear => { f with root := false }
  | .exitCurrentNull => { f with current := false, enabled := false }
  | .exitSafe => { f with exitedSafe := true }

set_option maxHeartbeats 3000000 in
theorem everyMilestonePreservesInvariant (f : PublicationFacts) (m : Milestone)
    (hf : f.invariant) (hm : milestonePre f m = true) :
    (milestoneStep f m).invariant := by
  cases f with
  | mk d t h s c fields root current enabled exited =>
    cases m <;> revert d t h s c fields root current enabled exited <;> decide

def checkMilestones (f : PublicationFacts) : List Milestone → Bool
  | [] => true
  | m :: rest => milestonePre f m && checkMilestones (milestoneStep f m) rest

def finishMilestones (f : PublicationFacts) : List Milestone → PublicationFacts
  | [] => f
  | m :: rest => finishMilestones (milestoneStep f m) rest

/-- Every checked source milestone prefix preserves the local invariant. -/
theorem checkedMilestones_preserve (events : List Milestone) (f : PublicationFacts)
    (hf : f.invariant) (checked : checkMilestones f events = true) :
    (finishMilestones f events).invariant := by
  induction events generalizing f with
  | nil => exact hf
  | cons m rest ih =>
    simp only [checkMilestones, Bool.and_eq_true] at checked
    exact ih (milestoneStep f m) (everyMilestonePreservesInvariant f m hf checked.1) checked.2

theorem checkedMilestones_prefix (front suffix : List Milestone) (f : PublicationFacts)
    (checked : checkMilestones f (front ++ suffix) = true) :
    checkMilestones f front = true := by
  induction front generalizing f with
  | nil => rfl
  | cons m rest ih =>
    simp only [List.cons_append, checkMilestones, Bool.and_eq_true] at checked ⊢
    exact ⟨checked.1, ih (milestoneStep f m) checked.2⟩

def adoptionStructuralOrdering : Prop :=
  projectedPaths 512 (program .adopt) ≠ [] ∧
  ∀ path, path ∈ projectedPaths 512 (program .adopt) →
    checkMilestones {} path = true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem adoptionStructuralOrdering_proven : adoptionStructuralOrdering := by
  have allPaths : (projectedPaths 512 (program .adopt)).all (checkMilestones {}) = true := by
    decide
  refine ⟨by decide, ?_⟩
  intro path member
  exact (List.all_eq_true.mp allPaths) path member

/-- Count/slot and root-before-enable invariants for every branch path of
the source adoption control projection, including either TLS-array-size and
count-publication branch. Loops may take any number of iterations because
their selected effect is empty. `threading.c:404-424,462-481`; `task.c:1620-1622`. -/
def adoptionInitializesBeforeExposure : Prop :=
  ∀ path, path ∈ projectedPaths 512 (program .adopt) →
    ∀ front suffix, path = front ++ suffix →
      (finishMilestones {} front).invariant

theorem adoptionInitializesBeforeExposure_proven : adoptionInitializesBeforeExposure := by
  intro path member front suffix split
  have checked := adoptionStructuralOrdering_proven.2 path member
  rw [split] at checked
  exact checkedMilestones_preserve front {} (by decide)
    (checkedMilestones_prefix front suffix {} checked)

/-- A release-published count is never ahead of its slot's ordinary
initialization in any adoption source prefix. Registration legitimately
precedes root-task construction. `threading.c:420-423,471-479`. -/
def publishedCountHasTLSSlot : Prop :=
  ∀ path, path ∈ projectedPaths 512 (program .adopt) →
    ∀ front suffix, path = front ++ suffix →
      (finishMilestones {} front).count = true →
      (finishMilestones {} front).slot = true

theorem publishedCountHasTLSSlot_proven : publishedCountHasTLSSlot := by
  intro path member front suffix split count
  exact (adoptionInitializesBeforeExposure_proven path member front suffix split).2.1 count

def exitInitialFacts : PublicationFacts :=
  { tls := true, heap := true, slot := true, count := true, fields := true,
    root := true, current := true, enabled := true }

def mutatesRegistration : Milestone → Bool
  | .arrayPublish | .slotWrite | .countRelease => true
  | _ => false

/-- Terminating normal thread exit preserves registration, clears
current_task, and executes the release SAFE store before returning. World
wait scans TLS entries regardless of current_task (`safepoint.c:139-148`),
so clearing liveness cannot exempt the permanent TLS slot from its wait.
`threading.c:598,611-616`; `safepoint.c:268-272`. -/
def registeredExitCannotEvadeWait : Prop :=
  projectedPaths 512 (program .exitThread) ≠ [] ∧
  ∀ path, path ∈ projectedPaths 512 (program .exitThread) →
    checkMilestones exitInitialFacts path = true ∧
    path.any mutatesRegistration = false ∧
    (finishMilestones exitInitialFacts path).exitedSafe = true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem registeredExitCannotEvadeWait_proven : registeredExitCannotEvadeWait := by
  have allPaths : (projectedPaths 512 (program .exitThread)).all (fun path =>
      checkMilestones exitInitialFacts path && !path.any mutatesRegistration &&
      (finishMilestones exitInitialFacts path).exitedSafe) = true := by decide
  refine ⟨by decide, ?_⟩
  intro path member
  have h := (List.all_eq_true.mp allPaths) path member
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1.1, ?_, h.2⟩
  cases value : path.any mutatesRegistration <;> simp_all

/-- The concrete source publication chain: array release (threading.c:415),
count release (422), acquire count (gc-stock.c:3871), then relaxed array
load (3872). The theorem derives happens-before from sequencing and the
release/acquire read-from edge, then applies C11 write-read coherence.
It quantifies over every consistent candidate and every read choice. -/
def snapshotArrayPublicationConsistent : Prop :=
  ∀ c : Memory.Candidate Loc Nat, c.consistent = true →
    ∀ publication countStore countRead read source : c.Id,
    ∀ array count observedCount observedArray : Nat,
    (c.event publication).action = .store .allTLS .release array →
    (c.event countStore).action = .store .nThreads .release count →
    (c.event countRead).action = .load .nThreads .acquire observedCount →
    (c.event read).action = .load .allTLS .relaxed observedArray →
    c.sequencedBefore publication countStore = true →
    c.readSource countRead countStore = true →
    c.sequencedBefore countRead read = true → c.readSource read source = true →
    (c.event publication).mo ≤ (c.event source).mo

theorem snapshotArrayPublicationConsistent_proven : snapshotArrayPublicationConsistent := by
  intro c consistent publication countStore countRead read source array count observedCount observedArray
    hp hc hcr hr hpc hcountRF hcrr hrf
  have beforeCount := Memory.Candidate.happensBefore_of_sequencedBefore hpc
  have countSync := Memory.Candidate.release_store_acquire_load_happensBefore hc hcr hcountRF
  have afterCount := Memory.Candidate.happensBefore_of_sequencedBefore hcrr
  have hb := Memory.Candidate.happensBefore_trans
    (Memory.Candidate.happensBefore_trans beforeCount countSync) afterCount
  apply Memory.Candidate.write_read_coherent consistent publication read source
  · simp [Memory.Candidate.isAtomicWrite, Memory.Candidate.isWrite, hp,
      Memory.Action.writeValue, Memory.Action.isPlain]
  · simp [Memory.Candidate.isAtomicRead, Memory.Candidate.isRead, hr,
      Memory.Action.readValue, Memory.Action.isPlain]
  · simp [Memory.Candidate.sameLocation, hp, hr, Memory.Action.location]
  · exact hb
  · exact hrf

/-- The public-entry prefix and cached-pointer suffix form one globally
C11-defined execution violating exclusion. `safepoint.c:396-472`;
`gc-stock.c:3821-3888`; `julia_threads.h:638-680`. -/
theorem stoppedWorldExcludesCriticalExecution_refuted :
    ¬ stoppedWorldExcludesCriticalExecution := by
  intro h
  have replay : run canonicalCheckpoint cachedPointerSchedule = canonicalOutcome :=
    canonicalOutcome_source.symm
  have noCritical := h 3 canonicalCheckpoint canonicalCheckpoint_sourceReachable cachedPointerSchedule
    (by rw [replay]; exact canonicalOutcome_defined)
    (by rw [replay]; exact canonicalOutcome_platform)
  change (run canonicalCheckpoint cachedPointerSchedule).criticalDuringGC = false at noCritical
  rw [replay, canonicalOutcome_violation.1] at noCritical
  cases noCritical

def entries : List JuliaLean.Registry.Entry := [
  { id := "cruntime-world-stop-execution-safety"
    juliaFile := "src/safepoint.c"
    juliaFns := ["jl_safepoint_resume_thread", "jl_gc_state_set", "jl_gc_safepoint_"]
    statement := "For every finite model execution reachable from an admitted PublicAPIEntry, with a globally defined C11 candidate and successful modeled protection events, no `.critical` marker or operation selected by `sourceTouchesRoots` executes during the modeled stopped-world phase."
    source := "invariant; bbfa0ce4150 src/gc-stock.c:96-105; src/julia_threads.h:638-658; src/safepoint.c:443-472"
    status := .refuted
    refutationEvidence := .modelCounterexample
    prop := ``stoppedWorldExcludesCriticalExecution
    thm := some ``stoppedWorldExcludesCriticalExecution_refuted
    issue := "none found (queries: jl_safepoint_resume_thread GC; cached safepoint pointer; resume thread during GC); #62863 related outcome through cancellation/reset, not established as duplicate"
    notes := "One 167-source-step, 88-event global C11-defined trace begins at an assumed PublicAPIEntry, reaches the stopped checkpoint after 137 steps, and completes a cached page-3 check during the modeled collection phase. The model does not prove startup or adoption reachability of that entry, does not classify arbitrary client heap execution, and assumes every modeled protection event succeeds. No native Julia failure has been demonstrated." },
  { id := "cruntime-world-stop-raw-unsafe-window"
    juliaFile := "src/julia_threads.h"
    juliaFns := ["jl_gc_state_set", "jl_gc_safepoint_", "jl_set_gc_and_wait"]
    statement := "Every modeled source helper contains no client GC-critical operation, including the raw UNSAFE publication before the mandatory safepoint check."
    source := "bbfa0ce4150 src/gc-stock.c:100-105; src/julia_threads.h:638-658"
    status := .proven
    prop := ``rawUnsafeWindowContainsNoCriticalOperation
    thm := some ``rawUnsafeWindowContainsNoCriticalOperation_proven
    notes := "Syntactic source-control-flow fact. It does not imply that a cached page-pointer check cannot incorrectly succeed during GC; execution safety has a separate refutation." },
  { id := "cruntime-world-stop-count-publication"
    juliaFile := "src/threading.c"
    juliaFns := ["jl_init_threadtls"]
    statement := "For every branch path and every source-control prefix of foreign-thread adoption, a release-published thread count has an already initialized TLS slot."
    source := "bbfa0ce4150 src/threading.c:404-424"
    status := .proven
    prop := ``publishedCountHasTLSSlot
    thm := some ``publishedCountHasTLSSlot_proven
    notes := "Source-order invariant, including optional TLS-array growth and count-publication branches. The C11 visibility consequence is stated separately with its happens-before premise." },
  { id := "cruntime-world-stop-adoption-path-ordering"
    juliaFile := "src/threading.c"
    juliaFns := ["jl_adopt_thread", "jl_init_threadtls", "jl_init_root_task"]
    statement := "Every branch path of the adoption source-control projection satisfies the initialization and publication milestone preconditions."
    source := "bbfa0ce4150 src/threading.c:369-424,466-479; src/task.c:1553-1622"
    status := .proven
    prop := ``adoptionStructuralOrdering
    thm := some ``adoptionStructuralOrdering_proven
    notes := "The structural projection covers every source branch. Its loops have no selected initialization effect, so their iteration counts do not alter the checked ordering." },
  { id := "cruntime-world-stop-adopter-initialization"
    juliaFile := "src/threading.c"
    juliaFns := ["jl_adopt_thread", "jl_init_threadtls", "jl_init_root_task", "jl_gc_enable_from_nonmutator"]
    statement := "Every source-control prefix of adoption preserves slot-before-count, initialized-fields-before-root/current-task publication, and initialized-current-task-before-reenable invariants."
    source := "bbfa0ce4150 src/threading.c:420-424,466-479; src/task.c:1553-1622; src/gc-stock.c:3805-3813"
    status := .proven
    prop := ``adoptionInitializesBeforeExposure
    thm := some ``adoptionInitializesBeforeExposure_proven
    notes := "Every selected source step preserves the invariant. Arbitrary loop iteration counts have no selected initialization effect. Local control-flow correctness and global C11 execution exclusion are separate registered properties." },
  { id := "cruntime-world-stop-exit-registration"
    juliaFile := "src/threading.c"
    juliaFns := ["jl_delete_thread", "jl_gc_safe_enter_from_nonmutator", "jl_gc_wait_for_the_world"]
    statement := "Every terminating normal exit path retains its registered TLS slot, clears current_task, and executes the release SAFE store; world wait scans registered TLS entries independently of current_task liveness."
    source := "bbfa0ce4150 src/threading.c:598,611-616; src/safepoint.c:139-148,263-273"
    status := .proven
    prop := ``registeredExitCannotEvadeWait
    thm := some ``registeredExitCannotEvadeWait_proven
    notes := "Registration and control-flow invariant for normal valid-root-task exit. Fatal wrong-task exit and signal-stack cleanup failures do not return." },
  { id := "cruntime-world-stop-snapshot-array-publication"
    juliaFile := "src/gc-stock.c"
    juliaFns := ["jl_gc_collect", "jl_init_threadtls"]
    statement := "For every C11-consistent candidate and read choice, an array release followed by the acquired count release cannot be followed by a relaxed snapshot-pointer read of an older array modification."
    source := "bbfa0ce4150 src/threading.c:415,420-423; src/gc-stock.c:3864-3872; C11 write-read coherence"
    status := .proven
    prop := ``snapshotArrayPublicationConsistent
    thm := some ``snapshotArrayPublicationConsistent_proven
    notes := "Uses the relaxed pointer load, actual array-store/count-store sequencing, count-release/acquire read-from edge, and C11 coherence. Source local slot-before-count and initialization ordering are separate invariant proofs." }
]

end JuliaLean.CRuntime.WorldStop

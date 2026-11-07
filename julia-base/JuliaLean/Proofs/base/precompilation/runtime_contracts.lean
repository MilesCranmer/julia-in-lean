import JuliaLean.base.precompilation

namespace JuliaLean.RuntimeCov.Precompilation

open JuliaLean.RuntimeCov

def edge (g : Graph) (a b : Node) : Bool := b ∈ depsOf g a

def reachable : Nat → Graph → Node → Node → Bool
  | 0, _, a, b => a = b
  | fuel + 1, g, a, b => a = b || (depsOf g a).any (reachable fuel g · b)

def cycleReported (cycles : List (List Node)) (a b : Node) : Bool :=
  cycles.any (fun c => a ∈ c && b ∈ c)

/-- Every reachable two-node cycle is included in the cycle list used by the
diagnostic. This is the obvious invariant promised by the distinction between
`cycles` and `outer_deps` at base/precompilation.jl:924-957. -/
def AllCyclesReported : Prop :=
  ∀ (g : Graph) (root a b : Node), reachable 8 g root a = true →
    reachable 8 g root b = true → edge g a b = true → edge g b a = true →
    cycleReported (scanPkg 16 g root ⟨[], [], []⟩).2.cycles a b = true

theorem allCyclesReported_refuted : ¬ AllCyclesReported := by
  intro h
  let g : Graph := [(0, [1]), (1, [0, 2]), (2, [3]), (3, [2])]
  have bad := h g 0 0 1 (by decide) (by decide) (by decide) (by decide)
  have hfalse : cycleReported (scanPkg 16 g 0 ⟨[], [], []⟩).2.cycles 0 1 = false := by rfl
  rw [hfalse] at bad
  contradiction

/-! ## Settled properties for the method families above -/

def JobserverBodies : Prop :=
  (∀ c a, setupPrecompileJobserver c a =
      if c then (.created, true) else (if a then .joined else .none, false)) ∧
  teardownPrecompileJobserver = false ∧
  (∀ m j, newWorkerLimiter m j = ⟨m, j, 0, 0, [], 0⟩) ∧
  (∀ xs n, (jobserverAcquireBaseline xs n).2 ≥ n) ∧
  (∀ xs n, (jobserverReleaseBaseline xs n).2 ≤ n)

theorem jobserverBodies_proven : JobserverBodies := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · intro c a; rfl
  · intro m j; rfl
  · intro xs n
    induction xs generalizing n with
    | nil => simp [jobserverAcquireBaseline]
    | cons x xs ih =>
      by_cases h1 : x.result = 1
      · simp [jobserverAcquireBaseline, h1]
      · by_cases h2 : x.result = -1 || x.cancelled || x.timedOut
        · simp [jobserverAcquireBaseline, h1, h2]
        · simp [jobserverAcquireBaseline, h1, h2, ih]
  · intro xs n
    induction xs generalizing n with
    | nil => cases n <;> simp [jobserverReleaseBaseline]
    | cons x xs ih =>
      cases n with
      | zero => simp [jobserverReleaseBaseline]
      | succ n =>
        simp only [jobserverReleaseBaseline]
        split <;> simp_all

def WorkerBodies : Prop :=
  (∀ w p, (acquireSlot w p).active = w.active + 1 ∧ (acquireSlot w p).seq = w.seq + 1) ∧
  (∀ w, (releaseSlot w).active = w.active - 1) ∧
  (∀ w p e, (acquireWorker w p (.error e)).2.active =
      if w.jobserver then w.active else w.active + 1) ∧
  (∀ w p xs, (acquireWorker w p (.ok xs)).2.active = w.active + 1) ∧
  (∀ w xs, (releaseWorker w xs).active = w.active - 1) ∧
  (∀ (α : Type) w p a cas (f : Rt α), (acquireWorker w p a).1 = .ok () →
      (withWorker w p a cas f).1 = f)

theorem workerBodies_proven : WorkerBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w p; exact ⟨rfl, rfl⟩
  · intro w; rfl
  · intro w p e
    cases w with
    | mk max jobserver active seq waiting ntokens =>
      cases jobserver <;> simp [acquireWorker, acquireSlot, releaseSlot]
  · intro w p xs
    cases w with
    | mk max jobserver active seq waiting ntokens =>
      cases jobserver <;> simp [acquireWorker, acquireSlot]
  · intro w xs
    by_cases h : w.jobserver = true <;> simp [releaseWorker, releaseSlot, h]
  · intro α w p a cas f h
    simp [withWorker, h]

def JobQueriesBodies : Prop :=
  newPrecompileJob.status = .pending ∧ newPrecompileJob.pid = 0 ∧
  ∀ j, (isPending j = true ↔ j.status = .pending) ∧
    (isStarted j = true ↔ j.status = .started) ∧
    (isRecompiled j = true ↔ j.status = .recompiled) ∧
    (isSoftError j = true ↔ j.status = .softError) ∧
    (isFailed j = true ↔ j.status = .failed) ∧
    (isDepFailed j = true ↔ j.status = .depFailed) ∧
    (hasPid j = true ↔ 0 < j.pid) ∧ hadPid j = j.hadPid ∧
    (isLocked j = true ↔ ¬ j.lockHolder.isEmpty) ∧ isWaiting j = j.waitingForBg

theorem jobQueriesBodies_proven : JobQueriesBodies := by
  refine ⟨rfl, rfl, ?_⟩
  intro j
  simp [isPending, isStarted, isRecompiled, isSoftError, isFailed, isDepFailed,
    hasPid, hadPid, isLocked, isWaiting]

def JobUpdatesBodies : Prop :=
  (∀ j t, (markStarted j t).status = .started ∧ (markStarted j t).startedAt = t) ∧
  (∀ j, (markRecompiled j).status = .recompiled) ∧
  (∀ j, (markSoftError j).status = .softError) ∧
  (∀ j m, (markFailed j m).status = .failed ∧ (markFailed j m).errorMsg = m) ∧
  (∀ j m, (markDepFailed j m).status = .depFailed ∧ (markDepFailed j m).errorMsg = m) ∧
  (∀ j p, (setPid j p).pid = p ∧ (setPid j p).hadPid = true) ∧
  (∀ j, (clearPid j).pid = 0) ∧
  (∀ j, (clearFailure j).status = .pending ∧ (clearFailure j).errorMsg = "" ∧
    (clearFailure j).outputBytes = 0)

theorem jobUpdatesBodies_proven : JobUpdatesBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp [markStarted, markRecompiled, markSoftError, markFailed, markDepFailed,
      setPid, clearPid, clearFailure]

def LockDelegateBodies : Prop :=
  (∀ (α : Type) (l : (Unit → α) → α) f, lockWith l f = l f) ∧
  (∀ (α : Type) (l : Unit → α), lockState l = l ()) ∧
  (∀ (α : Type) (u : Unit → α), unlockState u = u ())

theorem lockDelegateBodies_proven : LockDelegateBodies := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def CacheBytesBody : Prop :=
  (∀ jl, precompileCacheBytes jl none = match jl with
    | .error _ => 0 | .ok n => n.getD 0) ∧
  (∀ j s, precompileCacheBytes (.ok j) (some (.ok s)) = j.getD 0 + s.getD 0) ∧
  (∀ j e, precompileCacheBytes (.ok j) (some (.error e)) = j.getD 0)

theorem cacheBytesBody_proven : CacheBytesBody := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def ProgressBoundaryBodies : Prop :=
  ∀ io progress,
    startProgress io progress = "\u001b[?25l" ∧
    endProgress io progress = "\u001b[?25h\u001b[2K" ∧
    printProgressBottom io = "\u001b[S\u001b[1A\u001b[2K\u001b[1G"

theorem progressBoundaryBodies_proven : ProgressBoundaryBodies := by
  intro io progress
  exact ⟨rfl, rfl, rfl⟩

def FormattingBodies : Prop :=
  (∀ n, ansiMoveup n = "\u001b[" ++ toString n ++ "A") ∧
  (∀ s, showerror s = s ∧ showerrorWithBacktrace s = s ∧
    showPrecompileError s = "PkgPrecompileError: " ++ s) ∧
  (∀ f t c, canFancyprint f t c = f.getD (t && !c)) ∧
  (∀ i, unstableIoContext i = .contextConcrete) ∧
  (∀ h m, printpkgstyle h m = h ++ " " ++ m ++ "\n") ∧
  (∀ r, timingString r = lpad r 6 ++ " s") ∧
  formatVerboseTimingHeader =
    "   total │ include   (deps)   (comp) │ methods  img-gen     cache  ~pk-rss" ∧
  (∀ s e d c, colorString s e d c = if c then e ++ s ++ d else s) ∧
  (∀ io progress, startProgress io progress = "\u001b[?25l") ∧
  (∀ io progress, endProgress io progress = "\u001b[?25h\u001b[2K")

theorem formattingBodies_proven : FormattingBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro n; rfl
  · intro s; exact ⟨rfl, rfl, rfl⟩
  · intro f t c; rfl
  · intro i; cases i <;> rfl
  · intro h m; rfl
  · intro r; rfl
  · intro s e d c; rfl
  · intro io progress; rfl
  · intro io progress; rfl

end JuliaLean.RuntimeCov.Precompilation

import JuliaLean.RuntimeCov.Common

/-!
Pure models of methods in `base/precompilation.jl` at Julia master
`bbfa0ce4150`. Runtime calls, locks, clocks, file-system queries and process
operations are explicit inputs. Mutable Julia records are returned as updated
values.
-/

namespace JuliaLean.RuntimeCov.Precompilation

open JuliaLean.RuntimeCov

/-! ## Jobserver and worker limiter, lines 20-158 -/

inductive JobserverSetup where
  | created
  | joined
  | none
  deriving DecidableEq, Repr

/-- `setup_precompile_jobserver!`, base/precompilation.jl:20-28. The Boolean
component records whether the environment entry is present afterwards. -/
def setupPrecompileJobserver (created active : Bool) : JobserverSetup × Bool :=
  if created then (.created, true) else (if active then .joined else .none, false)

/-- `teardown_precompile_jobserver!`, base/precompilation.jl:30-34. -/
def teardownPrecompileJobserver : Bool := false

structure WorkerLimiter where
  max : Int
  jobserver : Bool
  active : Int
  seq : Int
  waiting : List (Float × Int)
  ntokens : Nat
  deriving Repr

/-- `WorkerLimiter(max, jobserver)`, base/precompilation.jl:62-63. -/
def newWorkerLimiter (max : Int) (jobserver : Bool) : WorkerLimiter :=
  ⟨max, jobserver, 0, 0, [], 0⟩

structure BaselineAttempt where
  result : Int
  cancelled : Bool
  timedOut : Bool
  deriving DecidableEq, Repr

/-- `_jobserver_acquire_baseline`, base/precompilation.jl:75-96. Each element
is one loop iteration after the runtime acquire, cancel callback and monotonic
timeout checks. -/
def jobserverAcquireBaseline : List BaselineAttempt → Nat → Bool × Nat
  | [], n => (false, n)
  | a :: rest, n =>
      if a.result = 1 then (true, n + 1)
      else if a.result = -1 || a.cancelled || a.timedOut then (false, n)
      else jobserverAcquireBaseline rest n

/-- `_jobserver_release_baseline`, base/precompilation.jl:98-108. The list
contains successive `@atomicreplace` success results. -/
def jobserverReleaseBaseline : List Bool → Nat → Bool × Nat
  | _, 0 => (false, 0)
  | [], n => (false, n)
  | success :: rest, n =>
      if success then (true, n - 1) else jobserverReleaseBaseline rest n

/-- `_acquire_slot`, base/precompilation.jl:110-122, after its priority wait
has admitted this request. -/
def acquireSlot (w : WorkerLimiter) (priority : Float) : WorkerLimiter :=
  let seq := w.seq + 1
  let key := (priority, -seq)
  { w with active := w.active + 1, seq, waiting := (w.waiting ++ [key]).erase key }

/-- `_release_slot`, base/precompilation.jl:124-130. -/
def releaseSlot (w : WorkerLimiter) : WorkerLimiter := { w with active := w.active - 1 }

/-- `Base.acquire(w::WorkerLimiter)`, base/precompilation.jl:132-143. A
baseline exception releases the process slot before it is rethrown. -/
def acquireWorker (w : WorkerLimiter) (priority : Float)
    (attempts : Rt (List BaselineAttempt)) : Rt Unit × WorkerLimiter :=
  let w := acquireSlot w priority
  if !w.jobserver then (.ok (), w) else
    match attempts with
    | .error e => (.error e, releaseSlot w)
    | .ok xs =>
        let (_, n) := jobserverAcquireBaseline xs w.ntokens
        (.ok (), { w with ntokens := n })

/-- `Base.release(w::WorkerLimiter)`, base/precompilation.jl:145-149. -/
def releaseWorker (w : WorkerLimiter) (cas : List Bool) : WorkerLimiter :=
  let w := if w.jobserver then { w with ntokens := (jobserverReleaseBaseline cas w.ntokens).2 } else w
  releaseSlot w

/-- `Base.acquire(f, w::WorkerLimiter)`, base/precompilation.jl:151-158. The
worker is released after either the callback result or exception. -/
def withWorker {α : Type} (w : WorkerLimiter) (priority : Float)
    (attempts : Rt (List BaselineAttempt)) (cas : List Bool) (f : Rt α) : Rt α × WorkerLimiter :=
  let (acquired, w) := acquireWorker w priority attempts
  match acquired with
  | .error e => (.error e, w)
  | .ok _ => (f, releaseWorker w cas)

/-! ## Per-package job state, lines 183-210 -/

inductive JobStatus where
  | pending | started | recompiled | softError | failed | depFailed
  deriving DecidableEq, Repr

structure PrecompileJob where
  status : JobStatus
  startedAt : Float
  errorMsg : String
  outputBytes : Nat
  pid : Int
  hadPid : Bool
  lockHolder : String
  waitingForBg : Bool
  verboseTiming : String
  peakRssBytes : Nat
  deriving Repr

/-- `PrecompileJob()`, base/precompilation.jl:183. -/
def newPrecompileJob : PrecompileJob :=
  ⟨.pending, 0.0, "", 0, 0, false, "", false, "", 0⟩

/-- Status and state queries, base/precompilation.jl:186-195. -/
def isPending (j : PrecompileJob) : Bool := j.status = .pending
def isStarted (j : PrecompileJob) : Bool := j.status = .started
def isRecompiled (j : PrecompileJob) : Bool := j.status = .recompiled
def isSoftError (j : PrecompileJob) : Bool := j.status = .softError
def isFailed (j : PrecompileJob) : Bool := j.status = .failed
def isDepFailed (j : PrecompileJob) : Bool := j.status = .depFailed
def hasPid (j : PrecompileJob) : Bool := j.pid > 0
def hadPid (j : PrecompileJob) : Bool := j.hadPid
def isLocked (j : PrecompileJob) : Bool := !j.lockHolder.isEmpty
def isWaiting (j : PrecompileJob) : Bool := j.waitingForBg

/-- Mutators at base/precompilation.jl:197-210. -/
def markStarted (j : PrecompileJob) (t : Float) : PrecompileJob :=
  { j with status := .started, startedAt := t }
def markRecompiled (j : PrecompileJob) : PrecompileJob := { j with status := .recompiled }
def markSoftError (j : PrecompileJob) : PrecompileJob := { j with status := .softError }
def markFailed (j : PrecompileJob) (msg : String) : PrecompileJob :=
  { j with status := .failed, errorMsg := msg }
def markDepFailed (j : PrecompileJob) (root : String) : PrecompileJob :=
  { j with status := .depFailed, errorMsg := root }
def setPid (j : PrecompileJob) (pid : Int) : PrecompileJob := { j with pid, hadPid := true }
def clearPid (j : PrecompileJob) : PrecompileJob := { j with pid := 0 }
def clearFailure (j : PrecompileJob) : PrecompileJob :=
  { j with status := .pending, errorMsg := "", outputBytes := 0 }

/-! ## Lock delegates and short formatting helpers, lines 336-486 -/

def lockWith {α : Type} (lock : (Unit → α) → α) (f : Unit → α) : α := lock f
def lockState {α : Type} (lock : Unit → α) : α := lock ()
def unlockState {α : Type} (unlock : Unit → α) : α := unlock ()

/-- `ansi_moveup`, base/precompilation.jl:354. -/
def ansiMoveup (n : Int) : String := "\u001b[" ++ toString n ++ "A"

/-- The three printing methods for `PkgPrecompileError`, lines 359-363. -/
def showerror (msg : String) : String := msg
def showerrorWithBacktrace (msg : String) : String := showerror msg
def showPrecompileError (msg : String) : String := "PkgPrecompileError: " ++ msg

/-- `can_fancyprint`, base/precompilation.jl:365. -/
def canFancyprint (forced : Option Bool) (isTty ciTrue : Bool) : Bool :=
  forced.getD (isTty && !ciTrue)

/-- The three `unstable_iocontext` methods, lines 371-373. -/
inductive IOForm where | concrete | contextConcrete | contextOther deriving DecidableEq, Repr
def unstableIoContext : IOForm → IOForm
  | .contextConcrete => .contextConcrete
  | .contextOther => .contextConcrete
  | .concrete => .contextConcrete

/-- `printpkgstyle`, base/precompilation.jl:375-380, as its emitted text. -/
def printpkgstyle (header msg : String) : String := header ++ " " ++ msg ++ "\n"

/-- `timing_string`, base/precompilation.jl:382. `rounded` is the decimal text
from `round(t, digits=1)`. -/
def timingString (rounded : String) : String := lpad rounded 6 ++ " s"

/-- `format_verbose_timing_header`, base/precompilation.jl:442. -/
def formatVerboseTimingHeader : String :=
  "   total │ include   (deps)   (comp) │ methods  img-gen     cache  ~pk-rss"

/-- `_precompile_cache_bytes`, base/precompilation.jl:446-454. Missing files
and any caught file-system error contribute zero. -/
def precompileCacheBytes (jl : Rt (Option Nat)) (so : Option (Rt (Option Nat))) : Nat :=
  match jl with
  | .error _ => 0
  | .ok j =>
      match so with
      | some (.error _) => j.getD 0
      | some (.ok s) => j.getD 0 + s.getD 0
      | none => j.getD 0

/-- `color_string`, base/precompilation.jl:458-466. -/
def colorString (s enable disable : String) (hascolor : Bool) : String :=
  if hascolor then enable ++ s ++ disable else s

/-- `start_progress`, line 486, and the one-line end/bottom helpers. -/
def startProgress (_io _progress : Nat) : String := "\u001b[?25l"
def endProgress (_io _progress : Nat) : String := "\u001b[?25h\u001b[2K"
def printProgressBottom (_io : Nat) : String := "\u001b[S\u001b[1A\u001b[2K\u001b[1G"

/-! ## Dependency-cycle scan, lines 960-992 -/

abbrev Node := Nat
abbrev Graph := List (Node × List Node)

def depsOf (g : Graph) (n : Node) : List Node :=
  match g.find? (fun p => p.1 = n) with | some p => p.2 | none => []

def lookupMark (marks : List (Node × Bool)) (n : Node) : Option Bool :=
  (marks.find? (fun p => p.1 = n)).map Prod.snd

def setMark (marks : List (Node × Bool)) (n : Node) (b : Bool) : List (Node × Bool) :=
  (n, b) :: marks.filter (fun p => p.1 != n)

def suffixFrom (n : Node) : List Node → List Node
  | [] => []
  | x :: xs => if x = n then x :: xs else suffixFrom n xs

structure ScanState where
  stack : List Node
  marks : List (Node × Bool)
  cycles : List (List Node)
  deriving DecidableEq, Repr

structure ScanFold where
  cycle : Option (List Node)
  early : Bool
  state : ScanState
  deriving DecidableEq, Repr

/-- `scan_deps!`, base/precompilation.jl:967-992. `fuel` bounds recursive graph
walks without changing any terminating finite traversal with enough fuel. -/
def scanDeps : Nat → Graph → Node → ScanState → Bool × ScanState
  | 0, _, pkg, s => (false, { s with marks := setMark s.marks pkg false })
  | fuel + 1, g, pkg, s =>
      let pushed := { s with stack := s.stack ++ [pkg] }
      let folded := (depsOf g pkg).foldl (fun (a : ScanFold) dep =>
        if a.early then a
        else if dep ∈ a.state.stack then
          let found := suffixFrom dep a.state.stack
          let best := match a.cycle with
            | none => some found
            | some old => if found.length < old.length then some found else some old
          { a with cycle := best }
        else
          let (reaches, next) :=
            match lookupMark a.state.marks dep with
            | some b => (b, a.state)
            | none => scanDeps fuel g dep a.state
          if reaches then ⟨a.cycle, true, next⟩ else ⟨a.cycle, false, next⟩)
        (⟨none, false, pushed⟩ : ScanFold)
      let popped := { folded.state with stack := folded.state.stack.dropLast }
      if folded.early then (true, { popped with marks := setMark popped.marks pkg true })
      else match folded.cycle with
        | some c =>
            let marked := { popped with marks := setMark popped.marks pkg true }
            (true, { marked with cycles := popped.cycles ++ [c] })
        | none => (false, { popped with marks := setMark popped.marks pkg false })

/-- `scan_pkg!`, base/precompilation.jl:960-966. -/
def scanPkg (fuel : Nat) (g : Graph) (pkg : Node) (s : ScanState) : Bool × ScanState :=
  match lookupMark s.marks pkg with
  | some b => (b, s)
  | none => scanDeps fuel g pkg s

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

import JuliaLean.base.precompilation

namespace JuliaLean.RuntimeCov.PrecompilationMore

open JuliaLean.RuntimeCov
open JuliaLean.RuntimeCov.Precompilation

/-! ## Settled properties -/

def FormattingMoreBodies : Prop :=
  (∀ p t cache peak r, (scanTiming p).seenInclude = false →
      formatVerboseTiming p t cache peak r = "") ∧
  (∀ s b paint, dim s b paint = if b then paint s else s) ∧
  (∀ r small paint, col r small paint =
    let s := if r.contains '.' then r else r ++ ".00"
    dim (lpad s 6 ++ "s") small paint) ∧
  (∀ p pa ta now r, (showProgress p pa ta now r).1.hasShown = true ∨
      showProgress p pa ta now r = (p, none))

theorem formattingMoreBodies_proven : FormattingMoreBodies := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p t cache peak r h; simp [formatVerboseTiming, h]
  · intro s b paint; rfl
  · intro r small paint; rfl
  · intro p pa ta now r
    by_cases h1 : (!p.alwaysReprint && p.hasShown && !pa) = true
    · simp [showProgress, h1]
    · by_cases h2 : (!p.alwaysReprint && p.hasShown && !ta) = true
      · simp [showProgress, h1, h2]
      · simp [showProgress, h1, h2]

def EnvironmentBodies : Prop :=
  (∀ p, (emptyExplicitEnv p).path = p) ∧
  (∀ a load, defaultExplicitEnv a load = match a with | none => emptyExplicitEnv | some p => load p) ∧
  (∀ f m p a, (!f || !m) = true → explicitEnv f m a p = emptyExplicitEnv a) ∧
  (∀ project seen out root,
    collectWorkspaceDepsAux 0 project seen out root = (seen, out)) ∧
  (∀ project root, collectWorkspaceDeps 0 project root = []) ∧
  (∀ d w n, fixupStdlibDeps d w n [] = (d, w, n))

theorem environmentBodies_proven : EnvironmentBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; rfl
  · intro a load; cases a <;> rfl
  · intro f m p a h
    cases f <;> cases m <;> simp [explicitEnv] at h ⊢
  · intro project seen out root; rfl
  · intro project root; rfl
  · intro d w n; rfl

def GraphBodies : Prop :=
  (∀ p n pkg, fullName p n pkg = match p pkg with | some q => q ++ " → " ++ n pkg | none => n pkg) ∧
  (∀ c cs, (excludedCircularDepsExplanation c cs).2 =
      c.filter (fun p => !cs.any (fun x => p ∈ x))) ∧
  (∀ g n out, collectAllDeps 0 g n out = out) ∧
  (∀ g seen out n, visitIndirectDeps 0 g seen out n = (seen, out)) ∧
  (∀ i, (buildDepGraph i).2.1 = i.projectDeps) ∧
  (∀ serial, detectCircularDeps [] serial = ([], [])) ∧
  (∀ g requested, (filterDepGraph g requested).length ≤ g.length) ∧
  (∀ paths checked, (preresolvedSnapshot paths checked).length ≤ paths.length) ∧
  (∀ p u ok, (checkedNow p u ok).1 = false → p ∈ u)

theorem graphBodies_proven : GraphBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p n pkg; rfl
  · intro c cs; rfl
  · intro g n out; rfl
  · intro g seen out n; rfl
  · intro i; rfl
  · intro serial; rfl
  · intro g requested; exact List.length_filter_le _ _
  · intro paths checked
    exact Nat.le_trans (List.length_filter_le _ _)
      (List.length_filterMap_le (fun p => p.2.head?.map (p.1, ·)) paths)
  · intro p u ok h
    by_cases hp : p ∈ u
    · exact hp
    · simp [checkedNow, hp] at h

def PublicBackgroundBodies : Prop :=
  (∀ a, (precompilePkgs a).timing = (a.timing || a.verbose) ∧
      (precompilePkgs a).force = (a.force || a.forceStdlibs)) ∧
  (∀ s p, isPackagePending s p = true → isPrecompilingInBackground s = true) ∧
  (∀ s p, (markCompletedPkgid s p).completed = insertUnique p s.completed) ∧
  (∀ s g, (stopBackgroundPrecompile s g).1 = true → s.taskPresent = true ∧ s.taskDone = false) ∧
  (∀ s v, (launchBackgroundPrecompile s v).monitoring = true) ∧
  (∀ c l r, precompilePkgsDispatch c l r = .launch ↔ c = false)

theorem publicBackgroundBodies_proven : PublicBackgroundBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; exact ⟨rfl, rfl⟩
  · intro s p h
    simp [isPackagePending, isPrecompilingInBackground] at h ⊢
    exact h.1
  · intro s p; rfl
  · intro s g h
    simp only [stopBackgroundPrecompile] at h
    by_cases hp : s.taskPresent = true <;> by_cases hd : s.taskDone = true <;> simp_all
  · intro s v; rfl
  · intro c l r; cases c <;> cases l <;> cases r <;> simp [precompilePkgsDispatch]

def LoadingBackgroundBodies : Prop :=
  (∀ c g p r, precompileForLoading c g p r =
    if !c then .disabled else if g then .generating else if p then .parallelDisabled
    else match r with | .ok _ => .run | .error (.errorException _) => .rethrow | .error _ => .swallowed) ∧
  (∀ s, precompileForLoadingCore s =
    let pkgs := (s.identified.filter (fun p => p ∉ s.alreadyLoaded)).foldl
      (fun a p => insertUnique p a) []
    let pkgs := s.extensions.foldl (fun a p => insertUnique p a) pkgs
    if pkgs.length ≤ 1 then [] else pkgs.filter (fun p => p ∈ s.stale)) ∧
  (∀ u r l s, available u r l s = (u ∈ r || u ∈ l || u ∈ s)) ∧
  (∀ p parent plain, label p parent plain = fullName parent plain p) ∧
  (∀ s p, waitForPendingPackage s p = isPackagePending s p) ∧
  (∀ s sig, broadcastSignal s sig = s.signalChannels) ∧
  (∀ s rem, !s.monitoring || !s.keyListening → keyboardTip s rem = "") ∧
  (∀ (α : Type) stable (io : α), monitorBackgroundPrecompile stable io = stable io) ∧
  (∀ s c e x i w, (monitorBackgroundCore s c e x i w).1 = .idle → s.taskPresent = false ∨ s.taskDone = true) ∧
  (∀ s counted, (stopMonitoringUnlessWaitedOn s counted).1 =
    decide (s.foregroundMonitors > if counted then 1 else 0)) ∧
  (∀ fuel g root, collectReachable fuel g root = collectAllDeps fuel g root [root])

theorem loadingBackgroundBodies_proven : LoadingBackgroundBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c g p r; rfl
  · intro s; rfl
  · intro u r l s; rfl
  · intro p parent plain; rfl
  · intro s p; rfl
  · intro s sig; rfl
  · intro s rem h; simp [keyboardTip, h]
  · intro α stable io; rfl
  · intro s c e x i w h
    by_cases hp : s.taskPresent = true
    · by_cases hd : s.taskDone = true
      · exact Or.inr hd
      · cases c <;> cases e <;> cases x <;> cases i <;> cases w <;>
          simp [monitorBackgroundCore, hp, hd] at h
    · have hfalse : s.taskPresent = false := by cases h : s.taskPresent <;> simp_all
      exact Or.inl hfalse
  · intro s counted; simp [stopMonitoringUnlessWaitedOn]
  · intro fuel g root; rfl

def ProcessDisplayBodies : Prop :=
  (∀ s p c r, (s && p) = false → processStats s p c r = ⟨0, 0⟩) ∧
  (∀ old sample, samplePeakRss old sample ≥ old) ∧
  (∀ s i c, (shouldStop s i c).1 = true ↔ i || c || s.done) ∧
  (∀ n, makeSignalChannel n = n + 1) ∧
  (∀ names m, formatNamesList names m =
    if names.length > m then String.intercalate ", " (names.take m) ++ ", and " ++
      toString (names.length - m) ++ " more" else String.intercalate " and " names) ∧
  (∀ l e, resolvedVersion l e = match l with | some v => some v | none => e) ∧
  (∀ h xs, unverifiedSet h xs = [] ↔ h = false ∨ xs = [])

theorem processDisplayBodies_proven : ProcessDisplayBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s p c r h; cases s <;> cases p <;> simp [processStats] at h ⊢
  · intro old sample; exact Nat.le_max_left _ _
  · intro s i c; cases i <;> cases c <;> simp [shouldStop]
  · intro n; rfl
  · intro names m; rfl
  · intro l e; cases l <;> rfl
  · intro h xs; cases h <;> simp [unverifiedSet]

def MessageBodies : Prop :=
  (∀ prev dt s peak, (pollProcessStats prev dt s peak).peakRss ≥ peak) ∧
  (∀ n f c p s m h, describePkg n f c p s m h =
    let n := if p then n else colorString n "" "" h
    let n := if s then n ++ " (serial)" else n
    let n := if m && !f.isEmpty then n ++ " `" ++ f ++ "`" else n
    if m then n ++ " " ++ c else n) ∧
  (∀ t v, (printHeader t v).2 = true) ∧
  (∀ f e o c d, f = false → explainReasons f e o c d = ([], e)) ∧
  (∀ l e, loadedVersionDiffers l e =
    match l, e with | some a, some b => a != b | _, _ => false) ∧
  (∀ d l x, ∀ p ∈ loadedVersionConflicts d l x, p ∈ d) ∧
  stackedVersionConflicts [] = [] ∧
  (∀ n c, envDisplayName n c = match n with | some x => "@" ++ x | none => c) ∧
  (∀ ds ps env od op, stackedConflictsMessage ds ps env od op =
    ds ++ (if od then " is" else " are") ++ " from " ++ env ++ ", where " ++ ps ++
      (if op then " has a different version" else " have different versions")) ∧
  (∀ h a, onlyFlagsMismatch h a = (h && !a.any id)) ∧
  (∀ n one ongoing cancelable defaultEnv,
    loadedConflictsMessage n one ongoing cancelable defaultEnv =
      n ++ (if one then " is loaded at a different version" else " are loaded at different versions") ++
      (if ongoing then " and dependents are being precompiled." else " and dependents were precompiled.") ++
      (if cancelable && ongoing then " Press c to cancel." else "") ++
      (if defaultEnv then " Restart julia." else " Restart julia with --project set.")) ∧
  (∀ q s, spawnPrintLoop q s = .noWork ↔ q || s) ∧
  (∀ ok chunks, precompilepkgsMonitorStd ok chunks = (String.join chunks, ok)) ∧
  (∀ (α : Type) fromLoading locked (run wait : α),
    maybeCachefileLock fromLoading locked run wait =
      if fromLoading && !locked then wait else run) ∧
  (∀ m c, precompileCostEstimate m c =
    match m, c with | some t, some s => t + s | some t, none => t | _, _ => 0)

theorem messageBodies_proven : MessageBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro prev dt s peak
    simp [pollProcessStats]
    split
    · exact Nat.le_refl _
    · exact Nat.le_max_left _ _
  · intro n f c p s m h; rfl
  · intro t v; rfl
  · intro f e o c d hf; simp [explainReasons, hf]
  · intro l e; cases l <;> cases e <;> rfl
  · intro d l x p hp
    simp [loadedVersionConflicts] at hp
    exact hp.1
  · intro n c; cases n <;> rfl
  · intro ds ps env od op; rfl
  · intro h a; rfl
  · intro n one ongoing cancelable defaultEnv; rfl
  · intro q s; cases q <;> cases s <;> simp [spawnPrintLoop]
  · intro ok chunks; rfl
  · intro α fromLoading locked run wait; rfl
  · intro m c; cases m <;> cases c <;> rfl

def SchedulingBodies : Prop :=
  (∀ g c, (newSchedulePriorities g c).direct = g) ∧
  (∀ p pkg, scheduleHeightCached p pkg = (schedulePriority p pkg).1) ∧
  (∀ b, isStdlibSource b = b) ∧
  (∀ d f, failedDependency d f = none ↔ ∀ x ∈ d, x ∉ f) ∧
  (∀ ps c f, (spawnPrecompileTasks ps c f).spawned.length +
      (spawnPrecompileTasks ps c f).skipped.length = ps.length) ∧
  (∀ k, drainWorkChannel k [] = k) ∧
  (∀ f i c l, reportPrecompileResults f i c l = .failed ↔ f = true) ∧
  (∀ r i (w l q f g : Bool) (e : Option Nat), (doPrecompile r i w l q f g e).tasks ≥ 1)

theorem schedulingBodies_proven : SchedulingBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g c; rfl
  · intro p pkg; rfl
  · intro b; rfl
  · intro d f; simp [failedDependency, List.find?_eq_none]
  · intro ps c f
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [spawnPrecompileTasks]
      split <;> simp_all [List.length_append] <;> omega
  · intro k; rfl
  · intro f i c l; cases f <;> cases i <;> cases c <;> cases l <;>
      simp [reportPrecompileResults]
  · intro r i w l q f g e
    exact Nat.le_max_left 1 (e.getD (if w then 1 else 2))

end JuliaLean.RuntimeCov.PrecompilationMore

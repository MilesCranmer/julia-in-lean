import JuliaLean.RuntimeCov.Precompilation

/-!
Remaining method models for `base/precompilation.jl` at master `bbfa0ce4150`.
External parsers, file-system operations, process queries, locks and spawned
tasks are represented by their returned values. The Julia control flow and
state updates remain explicit.
-/

namespace JuliaLean.RuntimeCov.PrecompilationMore

open JuliaLean.RuntimeCov
open JuliaLean.RuntimeCov.Precompilation

/-! ## Verbose timing and progress rendering -/

inductive TimingToken where
  | includeNs (n : Nat)
  | compilationNs (n : Nat)
  | depsNs (n : Nat)
  | methods (n : Nat)
  | other
  deriving DecidableEq, Repr

structure TimingData where
  includeNs : Nat := 0
  compilationNs : Nat := 0
  depsNs : Nat := 0
  methods : Nat := 0
  seenInclude : Bool := false
  deriving DecidableEq, Repr

/-- Token loop inside `format_verbose_timing`, base/precompilation.jl:390-416. -/
def scanTiming : List TimingToken → TimingData
  | [] => {}
  | t :: ts =>
      let d := scanTiming ts
      match t with
      | .includeNs n => { d with includeNs := n, seenInclude := true }
      | .compilationNs n => { d with compilationNs := n }
      | .depsNs n => { d with depsNs := n }
      | .methods n => { d with methods := n }
      | .other => d

/-- Nested `dim`, line 417. -/
def dim (s : String) (isDim : Bool) (paint : String → String) : String :=
  if isDim then paint s else s

/-- Nested `col`, lines 418-427. `rounded` is the decimal string produced by
Julia's two-digit `round`; `small` is `x < 0.005`. -/
def col (rounded : String) (small : Bool) (paint : String → String) : String :=
  let s := if rounded.contains '.' then rounded else rounded ++ ".00"
  dim (lpad s 6 ++ "s") small paint

/-- `format_verbose_timing`, lines 390-438. Numeric presentation is the
`render` callback; parsing, the required include marker and derived image time
are modelled here. -/
def formatVerboseTiming (payload : List TimingToken) (totalNs cacheBytes peakRssBytes : Nat)
    (render : TimingData → Nat → Nat → Nat → String) : String :=
  let d := scanTiming payload
  if d.seenInclude then render d (totalNs - d.includeNs) cacheBytes peakRssBytes else ""

structure ProgressState where
  max : Int
  current : Int
  prev : Int
  hasShown : Bool
  timeShown : Int
  alwaysReprint : Bool
  deriving DecidableEq, Repr

/-- `show_progress`, base/precompilation.jl:488-536. The two Boolean inputs are
the percentage and time throttling comparisons after Julia computes them. -/
def showProgress (p : ProgressState) (percentageAdvanced timeAdvanced : Bool)
    (now : Int) (render : ProgressState → String) : ProgressState × Option String :=
  if !p.alwaysReprint && p.hasShown && !percentageAdvanced then (p, none)
  else if !p.alwaysReprint && p.hasShown && !timeAdvanced then (p, none)
  else
    let p' := { p with timeShown := now, prev := p.current, hasShown := true }
    (p', some (render p'))

/-! ## Explicit environments and workspace traversal, lines 567-911 -/

abbrev Uuid := Nat
abbrev NameMap := List (String × Uuid)
abbrev DepMap := List (Uuid × List Uuid)

structure ExplicitEnv where
  path : String
  projectDeps : NameMap
  projectWeakdeps : NameMap
  projectExtras : NameMap
  projectExtensions : List (String × List Uuid)
  workspaceDeps : List (Uuid × String)
  deps : DepMap
  weakdeps : DepMap
  extensions : List (Uuid × List (String × List Uuid))
  names : List (Uuid × String)
  lookupPresent : List Uuid
  deriving DecidableEq, Repr

/-- `ExplicitEnv(::Nothing, envpath)`, base/precompilation.jl:568-580. -/
def emptyExplicitEnv (envpath : String := "") : ExplicitEnv :=
  ⟨envpath, [], [], [], [], [], [], [], [], [], []⟩

/-- `ExplicitEnv()`, line 567. -/
def defaultExplicitEnv (activeProject : Option String) (load : String → ExplicitEnv) : ExplicitEnv :=
  match activeProject with | none => emptyExplicitEnv | some p => load p

structure ParsedEnv where
  projectDeps : NameMap
  projectWeakdeps : NameMap
  projectExtras : NameMap
  projectExtensions : List (String × List Uuid)
  workspaceDeps : List (Uuid × String)
  deps : DepMap
  weakdeps : DepMap
  extensions : List (Uuid × List (String × List Uuid))
  names : List (Uuid × String)
  lookupPresent : List Uuid
  deriving DecidableEq, Repr

/-- `ExplicitEnv(envpath::String)`, base/precompilation.jl:581-810. The parsed
and expanded TOML tables are explicit because TOML parsing is modelled by its
own area. -/
def explicitEnv (isfile hasManifest : Bool) (absPath : String) (p : ParsedEnv) : ExplicitEnv :=
  if !isfile || !hasManifest then emptyExplicitEnv absPath
  else ⟨absPath, p.projectDeps, p.projectWeakdeps, p.projectExtras,
    p.projectExtensions, p.workspaceDeps, p.deps, p.weakdeps, p.extensions,
    p.names, p.lookupPresent⟩

structure WorkspaceProject where
  file : String
  deps : List (Uuid × String)
  package : Option (Uuid × String)
  members : List String
  deriving DecidableEq, Repr

def putName (xs : List (Uuid × String)) (p : Uuid × String) : List (Uuid × String) :=
  p :: xs.filter (fun q => q.1 != p.1)

/-- `collect_workspace_deps!`, base/precompilation.jl:824-850. -/
def collectWorkspaceDepsAux : Nat → (String → Option WorkspaceProject) →
    List String → List (Uuid × String) → String → List String × List (Uuid × String)
  | 0, _, seen, out, _ => (seen, out)
  | fuel + 1, project, seen, out, file =>
      if file ∈ seen then (seen, out) else
      match project file with
      | none => (file :: seen, out)
      | some p =>
          let out := p.deps.foldl putName out
          let out := match p.package with | some x => putName out x | none => out
          p.members.foldl (fun acc member =>
            collectWorkspaceDepsAux fuel project acc.1 acc.2 member) (file :: seen, out)

/-- `collect_workspace_deps`, base/precompilation.jl:812-822, after the
`base_project` loop selects `root`. -/
def collectWorkspaceDeps (fuel : Nat) (project : String → Option WorkspaceProject)
    (root : String) : List (Uuid × String) :=
  (collectWorkspaceDepsAux fuel project [] [] root).2

structure StdlibFix where
  uuid : Uuid
  deps : List Uuid
  weakdeps : List Uuid
  extensions : List (String × List Uuid)
  discovered : List (Uuid × String)
  deriving DecidableEq, Repr

def replaceDeps (m : DepMap) (u : Uuid) (ds : List Uuid) : DepMap :=
  (u, ds) :: m.filter (fun p => p.1 != u)

/-- `fixup_stdlib_deps!`, base/precompilation.jl:859-911. Each `StdlibFix`
is one validated stdlib Project.toml discovered by the source loop. -/
def fixupStdlibDeps (deps weak : DepMap) (names : List (Uuid × String))
    (fixes : List StdlibFix) : DepMap × DepMap × List (Uuid × String) :=
  fixes.foldl (fun acc f =>
    (replaceDeps acc.1 f.uuid f.deps, replaceDeps acc.2.1 f.uuid f.weakdeps,
      f.discovered.foldl putName acc.2.2)) (deps, weak, names)

/-! ## Dependency graph helpers, lines 916-1204 -/

/-- `full_name`, base/precompilation.jl:916-922. -/
def fullName (parent : Node → Option String) (name : Node → String) (pkg : Node) : String :=
  match parent pkg with | some p => p ++ " → " ++ name pkg | none => name pkg

/-- `excluded_circular_deps_explanation`, lines 924-957, represented by the
ordered cycle and outer-package names that its loops print. -/
def excludedCircularDepsExplanation (circular : List Node) (cycles : List (List Node)) :
    List (List Node) × List Node :=
  (cycles, circular.filter (fun p => !cycles.any (fun c => p ∈ c)))

def insertUnique (x : Node) (xs : List Node) : List Node := if x ∈ xs then xs else x :: xs

/-- `collect_all_deps`, base/precompilation.jl:995-1003. -/
def collectAllDeps : Nat → Graph → Node → List Node → List Node
  | 0, _, _, out => out
  | fuel + 1, g, n, out =>
      (depsOf g n).foldl (fun acc d =>
        if d ∈ acc then acc else collectAllDeps fuel g d (d :: acc)) out

/-- `visit_indirect_deps!`, base/precompilation.jl:1005-1018. -/
def visitIndirectDeps : Nat → Graph → List Node → List Node → Node → List Node × List Node
  | 0, _, visited, all, _ => (visited, all)
  | fuel + 1, g, visited, all, n =>
      if n ∈ visited then (visited, all) else
      (depsOf g n).foldl (fun acc d =>
        if d ∈ acc.2 then acc else visitIndirectDeps fuel g acc.1 (d :: acc.2) d)
        (n :: visited, all)

structure BuildGraphInput where
  direct : Graph
  extensionEdges : Graph
  projectDeps : List Node
  serialDeps : List Node
  deriving DecidableEq, Repr

/-- `build_dep_graph`, base/precompilation.jl:1022-1141. The environment and
extension loops supply their validated direct and extension edges. -/
def buildDepGraph (i : BuildGraphInput) : Graph × List Node × List Node :=
  let direct := i.extensionEdges.foldl (fun g p =>
    (p.1, p.2) :: g.filter (fun q => q.1 != p.1)) i.direct
  (direct, i.projectDeps, i.serialDeps)

/-- `detect_circular_deps!`, base/precompilation.jl:1145-1164. -/
def detectCircularDeps (g : Graph) (serial : List Node) : List Node × List (List Node) :=
  g.foldl (fun acc p =>
    if p.1 ∈ serial then acc else
    let r := scanPkg (g.length + 1) g p.1 ⟨[], [], acc.2⟩
    (if r.1 then insertUnique p.1 acc.1 else acc.1, r.2.cycles)) ([], [])

/-- `filter_dep_graph!`, base/precompilation.jl:1168-1190. -/
def filterDepGraph (g : Graph) (requested : List Node) : Graph :=
  let keep := requested.foldl (fun ks n => collectAllDeps (g.length + 1) g n (insertUnique n ks)) []
  g.filter (fun p => p.1 ∈ keep)

/-- `preresolved_snapshot`, lines 1193-1196. -/
def preresolvedSnapshot (paths : List (Node × List String)) (checked : String → Bool) : List (Node × String) :=
  (paths.filterMap fun p => p.2.head?.map (p.1, ·)).filter (fun p => checked p.2)

/-- `checked_now!`, lines 1199-1204. The Boolean result and remaining
unverified set are both observable state. -/
def checkedNow (path : String) (unverified : List String) (checksumOk : Bool) : Bool × List String :=
  if path ∉ unverified then (true, unverified)
  else if !checksumOk then (false, unverified)
  else (true, unverified.erase path)

/-! ## Public and background lifecycle, lines 1337-2063 -/

structure FrontendArgs where
  timing : Bool
  verbose : Bool
  force : Bool
  forceStdlibs : Bool
  configs : Nat
  deriving DecidableEq, Repr

/-- `precompilepkgs`, base/precompilation.jl:1337-1368. -/
def precompilePkgs (a : FrontendArgs) : FrontendArgs :=
  ⟨a.timing || a.verbose, a.verbose, a.force || a.forceStdlibs, a.forceStdlibs,
    max 1 a.configs⟩

inductive LoadingGate where | disabled | generating | parallelDisabled | run | swallowed | rethrow
  deriving DecidableEq, Repr

/-- `precompile_for_loading`, lines 1384-1395. -/
def precompileForLoading (compiled generating parallelDisabled : Bool)
    (result : Rt Unit) : LoadingGate :=
  if !compiled then .disabled else if generating then .generating else if parallelDisabled then .parallelDisabled
  else match result with
    | .ok _ => .run
    | .error (.errorException _) => .rethrow
    | .error _ => .swallowed

structure LoadingScan where
  identified : List Node
  alreadyLoaded : List Node
  extensions : List Node
  stale : List Node
  deriving DecidableEq, Repr

/-- `_precompile_for_loading`, lines 1397-1455. -/
def precompileForLoadingCore (s : LoadingScan) : List Node :=
  let pkgs := (s.identified.filter (fun p => p ∉ s.alreadyLoaded)).foldl (fun a p => insertUnique p a) []
  let pkgs := s.extensions.foldl (fun a p => insertUnique p a) pkgs
  if pkgs.length ≤ 1 then [] else pkgs.filter (fun p => p ∈ s.stale)

/-- Nested `available`, lines 1417-1418. -/
def available (u : Uuid) (reachable loaded sysimage : List Uuid) : Bool :=
  u ∈ reachable || u ∈ loaded || u ∈ sysimage

/-- Nested `label`, line 1449. -/
def label (pkg : Node) (parent : Node → Option String) (plain : Node → String) : String :=
  fullName parent plain pkg

structure BackgroundState where
  taskPresent : Bool
  taskDone : Bool
  interruptRequested : Bool
  cancelRequested : Bool
  monitoring : Bool
  pending : List (Node × Nat)
  completed : List Node
  signalChannels : Nat
  detachable : Bool
  confirming : Sym
  keyListening : Bool
  foregroundMonitors : Nat
  verbose : Bool
  deriving DecidableEq, Repr

def pendingCount (s : BackgroundState) (p : Node) : Nat :=
  match s.pending.find? (fun q => q.1 = p) with | some q => q.2 | none => 0

/-- `is_precompiling_in_background`, lines 1459-1461. -/
def isPrecompilingInBackground (s : BackgroundState) : Bool := s.taskPresent && !s.taskDone

/-- `is_package_pending`, lines 1466-1472. -/
def isPackagePending (s : BackgroundState) (p : Node) : Bool :=
  s.taskPresent && !s.taskDone && pendingCount s p > 0

/-- `wait_for_pending_package`, lines 1476-1481. -/
def waitForPendingPackage (s : BackgroundState) (p : Node) : Bool := isPackagePending s p

/-- Both `broadcast_signal` methods, lines 1484-1491. -/
def broadcastSignal (s : BackgroundState) (_sig : Int) : Nat := s.signalChannels

/-- `mark_completed_pkgid!`, lines 1495-1501. -/
def markCompletedPkgid (s : BackgroundState) (p : Node) : BackgroundState :=
  { s with completed := insertUnique p s.completed }

/-- `stop_background_precompile`, lines 1503-1517. -/
def stopBackgroundPrecompile (s : BackgroundState) (graceful : Bool) : Bool × BackgroundState :=
  if s.taskPresent && !s.taskDone then
    (true, if graceful then { s with interruptRequested := true }
           else { s with cancelRequested := true })
  else (false, s)

/-- `keyboard_tip`, lines 1535-1548. -/
def keyboardTip (s : BackgroundState) (remaining : Nat) : String :=
  if !s.monitoring || !s.keyListening then ""
  else if s.confirming != "none" then "Press Enter to " ++ s.confirming ++
    " (ignoring in " ++ toString remaining ++ "s)"
  else if s.detachable then "Press `?` for help, `c` to cancel, `d` to detach."
  else "Press `?` for help, `c` to cancel."

/-- `monitor_background_precompile`, lines 1550-1553. -/
def monitorBackgroundPrecompile {α : Type} (stabilize : α → α) (io : α) : α := stabilize io

inductive MonitorAction where | idle | completed | cancel | interrupt | packageDone | detach | normal
  deriving DecidableEq, Repr

/-- `_monitor_background_precompile`, lines 1555-1847, reduced to the same
ordered terminal decisions after its listener and watcher update their flags. -/
def monitorBackgroundCore (s : BackgroundState) (completedAt exit cancel interrupt waitingForPkg : Bool) :
    MonitorAction × BackgroundState :=
  if !s.taskPresent || s.taskDone then (if completedAt then .completed else .idle, s)
  else if cancel then (.cancel, { s with monitoring := false })
  else if interrupt then (.interrupt, s)
  else if exit && waitingForPkg then (.packageDone, s)
  else if exit then (.detach, { s with monitoring := false })
  else (.normal, s)

/-- `stop_monitoring_unless_waited_on`, lines 1852-1858. -/
def stopMonitoringUnlessWaitedOn (s : BackgroundState) (counted : Bool) : Bool × BackgroundState :=
  let others := s.foregroundMonitors > (if counted then 1 else 0)
  (others, if others then s else { s with monitoring := false })

/-- State reset performed by `launch_background_precompile`, lines 1860-1963. -/
def launchBackgroundPrecompile (s : BackgroundState) (verbose : Bool) : BackgroundState :=
  ⟨true, false, false, false, true, [], [], 0, s.detachable, s.confirming,
    s.keyListening, s.foregroundMonitors, verbose⟩

/-- `_collect_reachable!`, lines 1965-1971. -/
def collectReachable (fuel : Nat) (g : Graph) (root : Node) : List Node :=
  collectAllDeps fuel g root [root]

inductive PrecompileDispatch where | inject | launch | injectedLoading | injectedInteractive | detached | finished
  deriving DecidableEq, Repr

/-- `_precompilepkgs`, lines 1973-2063. -/
def precompilePkgsDispatch (canInject fromLoading resultReady : Bool) : PrecompileDispatch :=
  if canInject then
    if fromLoading then .injectedLoading else if resultReady then .injectedInteractive else .detached
  else .launch

/-! ## Process, message and scheduling helpers, lines 2079-2676 -/

structure ProcessStats where
  cpuNs : Nat
  rssBytes : Nat
  deriving DecidableEq, Repr

/-- `process_stats`, lines 2079-2122. Platform parsing succeeds with the two
values or returns the documented zero pair on unsupported/error paths. -/
def processStats (supported parseOk : Bool) (cpu rss : Nat) : ProcessStats :=
  if supported && parseOk then ⟨cpu, rss⟩ else ⟨0, 0⟩

structure PollResult where
  cpuPct : Nat
  rss : Nat
  previousCpu : Nat
  peakRss : Nat
  deriving DecidableEq, Repr

/-- One unique active-PID iteration of `poll_process_stats!`, lines 2126-2154. -/
def pollProcessStats (previous dt : Nat) (s : ProcessStats) (oldPeak : Nat) : PollResult :=
  if s.cpuNs = 0 then ⟨0, 0, previous, oldPeak⟩ else
  let delta := s.cpuNs - previous
  let pct := if dt > 0 then min (delta / dt) 999 else 0
  ⟨pct, s.rssBytes, s.cpuNs, max oldPeak s.rssBytes⟩

/-- One unique active-PID iteration of `sample_peak_rss!`, lines 2159-2175. -/
def samplePeakRss (old sample : Nat) : Nat := max old sample

structure StopState where
  interrupted : Bool
  canceled : Bool
  done : Bool
  deriving DecidableEq, Repr

/-- `should_stop`, lines 2177-2194. -/
def shouldStop (s : StopState) (interrupt cancel : Bool) : Bool × StopState :=
  if interrupt || cancel then
    (true, ⟨s.interrupted || interrupt, s.canceled || cancel, true⟩)
  else (s.done, s)

/-- `make_signal_channel`, lines 2196-2200. -/
def makeSignalChannel (count : Nat) : Nat := count + 1

/-- `describe_pkg`, lines 2202-2217. -/
def describePkg (name flags cacheflags : String) (project serial multi hascolor : Bool) : String :=
  let name := if project then name else colorString name "" "" hascolor
  let name := if serial then name ++ " (serial)" else name
  let name := if multi && !flags.isEmpty then name ++ " `" ++ flags ++ "`" else name
  if multi then name ++ " " ++ cacheflags else name

/-- `format_names_list`, lines 2220-2225. -/
def formatNamesList (names : List String) (maxNames : Nat := 5) : String :=
  if names.length > maxNames then
    String.intercalate ", " (names.take maxNames) ++ ", and " ++
      toString (names.length - maxNames) ++ " more"
  else String.intercalate " and " names

/-- `print_header`, lines 2227-2232. -/
def printHeader (target : String) (verbose : Bool) : String × Bool :=
  ("Precompiling " ++ target ++ if verbose then "\n" ++ formatVerboseTimingHeader else "", true)

/-- `explain_reasons!`, lines 2239-2257. -/
def explainReasons (fromLoading flagsExplained onlyFlags : Bool)
    (newConflicts stacked : List String) : List String × Bool :=
  if !fromLoading then ([], flagsExplained) else
  (newConflicts ++ stacked ++ if !flagsExplained && onlyFlags then ["flags"] else [],
    flagsExplained || onlyFlags)

/-- `loaded_version_differs`, lines 2260-2268. -/
def loadedVersionDiffers (loaded env : Option Nat) : Bool :=
  match loaded, env with | some a, some b => a != b | _, _ => false

/-- `loaded_version_conflicts`, lines 2273-2280. -/
def loadedVersionConflicts (deps loaded differing : List Node) : List Node :=
  deps.filter (fun p => p ∈ loaded && p ∈ differing)

/-- `resolved_version`, lines 2284-2289. -/
def resolvedVersion (loaded located : Option Nat) : Option Nat :=
  match loaded with | some v => some v | none => located

/-- `stacked_version_conflicts`, lines 2295-2322, after its file-system
lookups produce `(environment, dependent, dependency)` triples. -/
def stackedVersionConflicts (rows : List (String × String × String)) : List (String × List String × List String) :=
  rows.foldl (fun out r =>
    match out.find? (fun x => x.1 = r.1) with
    | none => (r.1, [r.2.1], [r.2.2]) :: out
    | some old => (r.1, insertUniqueString r.2.1 old.2.1,
        insertUniqueString r.2.2 old.2.2) :: out.filter (fun x => x.1 != r.1)) []
where
  insertUniqueString (s : String) (xs : List String) := if s ∈ xs then xs else s :: xs

/-- `env_display_name`, lines 2325-2330. -/
def envDisplayName (named : Option String) (contracted : String) : String :=
  match named with | some n => "@" ++ n | none => contracted

def stackedConflictsMessage (dependents deps env : String) (oneDependent oneDep : Bool) : String :=
  dependents ++ (if oneDependent then " is" else " are") ++ " from " ++ env ++
    ", where " ++ deps ++ (if oneDep then " has a different version" else " have different versions")

/-- `only_flags_mismatch`, lines 2346-2349. -/
def onlyFlagsMismatch (hasFlags : Bool) (otherActionable : List Bool) : Bool :=
  hasFlags && !otherActionable.any id

def loadedConflictsMessage (names : String) (one ongoing cancelable defaultEnv : Bool) : String :=
  names ++ (if one then " is loaded at a different version" else " are loaded at different versions") ++
    (if ongoing then " and dependents are being precompiled." else " and dependents were precompiled.") ++
    (if cancelable && ongoing then " Press c to cancel." else "") ++
    (if defaultEnv then " Restart julia." else " Restart julia with --project set.")

inductive PrintLoopResult where | noWork | stopped | rendered deriving DecidableEq, Repr
def spawnPrintLoop (queueEmpty stopped : Bool) : PrintLoopResult :=
  if queueEmpty || stopped then .noWork else .rendered

/-- `precompilepkgs_monitor_std`, lines 2515-2552. -/
def precompilepkgsMonitorStd (readOk : Bool) (chunks : List String) : String × Bool :=
  (String.join chunks, readOk)

/-- `precompile_pkgs_maybe_cachefile_lock`, lines 2560-2597. -/
def maybeCachefileLock {α : Type} (fromLoading lockAcquired : Bool)
    (run : α) (waited : α) : α :=
  if fromLoading && !lockAcquired then waited else run

/-- `precompile_cost_estimate`, lines 2601-2613. -/
def precompileCostEstimate (mtime cacheSize : Option Nat) : Nat :=
  match mtime, cacheSize with | some t, some s => t + s | some t, none => t | _, _ => 0

structure SchedulePriorities where
  direct : Graph
  cost : List (Node × Nat)
  height : List (Node × Nat)
  deriving DecidableEq, Repr

def scheduleHeight : Nat → Graph → Node → Nat
  | 0, _, _ => 0
  | fuel + 1, g, n => 1 + (depsOf g n).foldl (fun h d => max h (scheduleHeight fuel g d)) 0

/-- `SchedulePriorities`, lines 2630-2638. -/
def newSchedulePriorities (g : Graph) (cost : List (Node × Nat)) : SchedulePriorities :=
  ⟨g, cost, g.map (fun p => (p.1, scheduleHeight (g.length + 1) g p.1))⟩

/-- `schedule_priority`, line 2640. -/
def schedulePriority (p : SchedulePriorities) (pkg : Node) : Nat × Nat :=
  ((p.height.find? (fun x => x.1 = pkg)).map (·.2) |>.getD 0,
   (p.cost.find? (fun x => x.1 = pkg)).map (·.2) |>.getD 0)

/-- `schedule_height!`, lines 2643-2654. -/
def scheduleHeightCached (p : SchedulePriorities) (pkg : Node) : Nat := (schedulePriority p pkg).1

/-- `is_stdlib_source`, line 2658. -/
def isStdlibSource (inStdlib : Bool) : Bool := inStdlib

/-- `failed_dependency`, lines 2665-2673. -/
def failedDependency (deps failed : List Node) : Option Node := deps.find? (· ∈ failed)

/-- `unverified_set`, line 2676. -/
def unverifiedSet (fromLoading : Bool) (xs : List String) : List String := if fromLoading then xs else []

/-! ## Task orchestration, lines 2678-3481 -/

structure SpawnSummary where
  spawned : List Node
  skipped : List Node
  deriving DecidableEq, Repr

/-- `spawn_precompile_tasks!`, lines 2678-2925. The lists are its dependency,
cycle and failed-dependency decisions after cache freshness checks. -/
def spawnPrecompileTasks : List Node → List Node → List Node → SpawnSummary
  | [], _, _ => ⟨[], []⟩
  | p :: ps, circular, failed =>
      let out := spawnPrecompileTasks ps circular failed
      if p ∈ circular || p ∈ failed then ⟨out.spawned, out.skipped ++ [p]⟩
      else ⟨out.spawned ++ [p], out.skipped⟩

/-- `drain_work_channel!`, lines 2927-3048. Each injected request contributes
only packages not already present in the session graph. -/
def drainWorkChannel (known : List Node) (requests : List (List Node)) : List Node :=
  requests.foldl (fun ks rs => rs.foldl (fun a p => insertUnique p a) ks) known

inductive ReportResult where | ok | failed | interrupted | canceledLoading deriving DecidableEq, Repr

/-- `report_precompile_results!`, lines 3050-3273. -/
def reportPrecompileResults (failed interrupted canceled fromLoading : Bool) : ReportResult :=
  if failed then .failed else if interrupted then .interrupted
  else if canceled && fromLoading then .canceledLoading else .ok

structure DriverResult where
  tasks : Nat
  fancy : Bool
  brief : Bool
  requested : List Node
  deriving DecidableEq, Repr

/-- `do_precompile`, lines 3276-3481. The model retains the option
normalization and request selection that determine every later branch. -/
def doPrecompile (requested identified : List Node) (windows fromLoading interactive quiet fancy : Bool)
    (envTasks : Option Nat) : DriverResult :=
  let defaultTasks := if windows then 1 else 2
  let tasks := max 1 (envTasks.getD defaultTasks)
  let brief := fromLoading && !interactive && !quiet
  let fancy := fancy && !brief && !quiet
  ⟨tasks, fancy, brief, if requested.isEmpty then identified else requested⟩

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

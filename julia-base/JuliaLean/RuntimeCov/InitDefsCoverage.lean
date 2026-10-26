import JuliaLean.RuntimeCov.InitDefs

namespace JuliaLean.RuntimeCov.InitDefsCoverage

open JuliaLean.RuntimeCov
open JuliaLean.RuntimeCov.InitDefs

def CoreBodies : Prop :=
  (∀ n : Int, exit n = .ok n ↔ (-2147483648 ≤ n ∧ n ≤ 2147483647)) ∧
  exit0 = .ok 0 ∧
  (∀ (τ : Type) (s : Option τ), foregroundTask s = s) ∧
  (∀ (τ : Type) (prev : Option τ) (current : τ),
    asForegroundTask prev current = (some current, prev)) ∧
  (∀ b, isinteractive b = b)

theorem coreBodies_proven : CoreBodies := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · intro n
    simp only [exit, JuliaLean.IntTy.min, JuliaLean.IntTy.max,
      JuliaLean.IntTy.signed, JuliaLean.IntTy.bits]
    split <;> simp_all <;> omega
  · intro τ s; rfl
  · intro τ prev current; rfl
  · intro b; rfl

def DepotAppendBodies : Prop :=
  (∀ (b1 b2 : Str) (dp : List Str), dp.IsPrefix (appendBundled b1 b2 dp)) ∧
  (∀ (b1 b2 : Str) (dp : List Str),
    b1 ∈ appendBundled b1 b2 dp ∧ b2 ∈ appendBundled b1 b2 dp)

theorem depotAppendBodies_proven : DepotAppendBodies := by
  refine ⟨appendBundled_prefix, ?_⟩
  intro b1 b2 dp
  by_cases h1 : b1 ∈ dp
  · by_cases h2 : b2 ∈ dp
    · simp [appendBundled, h1, h2]
    · simp [appendBundled, h1, h2]
  · by_cases h2 : b2 ∈ dp ++ [b1]
    · simp [appendBundled, h1, h2]
    · simp [appendBundled, h1, h2]

def CurrentProjectBodies : Prop :=
  (∀ names join isf dirname home fuel dir p,
    currentProjectAt names join isf dirname home fuel dir = some p → isf p = true) ∧
  (∀ search, currentProject none search = none) ∧
  (∀ dir search, currentProject (some dir) search = search dir)

theorem currentProjectBodies_proven : CurrentProjectBodies := by
  refine ⟨?_, ?_, ?_⟩
  · intro names join isf dirname home fuel dir p h
    exact currentProjectAt_file names join isf dirname home fuel dir p h
  · intro search; rfl
  · intro dir search; rfl

def ActiveInitBodies : Prop :=
  (∀ c, cmdSuppressesProgram c = true ↔ c = 'e' ∨ c = 'E') ∧
  (∀ expand absUser, initActiveProject none none expand absUser = none) ∧
  (∀ env expand absUser, initActiveProject (some []) env expand absUser = none) ∧
  (∀ ok path, initNamedEnv ok path = some path ↔ ok = true)

theorem activeInitBodies_proven : ActiveInitBodies := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c; simp [cmdSuppressesProgram]
  · intro expand absUser; rfl
  · intro env expand absUser; rfl
  · intro ok path; cases ok <;> simp [initNamedEnv]

def ExpandSpecialBodies : Prop :=
  (∀ e, loadPathExpand e kAt = e.activeProjectNoSearch) ∧
  (∀ e, loadPathExpand e kDot = e.currentProject) ∧
  (∀ e, loadPathExpand e kTemp = some e.tempdir) ∧
  (∀ e, loadPathExpand e kStdlib = some e.stdlib) ∧
  (∀ e, e.programFile = none → loadPathExpand e kScript = none) ∧
  (∀ e pf, e.programFile = some pf →
    loadPathExpand e kScript = e.currentProjectAt (e.dirname pf)) ∧
  loadPathExpandNothing = none

theorem expandSpecialBodies_proven : ExpandSpecialBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro e; simp [loadPathExpand, kAt]
  · intro e; simp [loadPathExpand, kAt, kDot]
  · intro e; simp [loadPathExpand, kAt, kDot, kTemp]
  · intro e; simp [loadPathExpand, kAt, kDot, kTemp, kStdlib]
  · intro e h; simp [loadPathExpand, kAt, kDot, kTemp, kStdlib, kScript, h]
  · intro e pf h; simp [loadPathExpand, kAt, kDot, kTemp, kStdlib, kScript, h]

def ActivePathBodies : Prop :=
  (∀ expand isfile ispath isname withProject loadPath,
    activeProject none expand isfile ispath isname withProject loadPath false = none) ∧
  (∀ p callbacks, setActiveProject p callbacks = (p, callbacks)) ∧
  (∀ active manifestOf, activeManifest none active manifestOf = active.bind manifestOf) ∧
  (∀ p active manifestOf, activeManifest (some p) active manifestOf = manifestOf p) ∧
  (∀ expand path, (loadPath expand path).Nodup)

theorem activePathBodies_proven : ActivePathBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro expand isfile ispath isname withProject loadPath; rfl
  · intro p callbacks; rfl
  · intro active manifestOf; cases active <;> rfl
  · intro p active manifestOf; rfl
  · intro expand path; exact loadPath_nodup expand path

def HookBodies : Prop :=
  (∀ s f s', atexit s f = .ok s' → s'.hooks = f :: s.hooks) ∧
  (∀ s f, s.finished = true → ∃ e, atexit s f = .error e) ∧
  (∀ hasMethod code s, (runAtexitHooks hasMethod code s).1.map Prod.fst = s.hooks ∧
    (runAtexitHooks hasMethod code s).2 = ⟨[], true⟩) ∧
  (∀ hasMethod code s, atexitImpl hasMethod code s = runAtexitHooks hasMethod code s) ∧
  (∀ hooks f, postoutput hooks f = f :: hooks) ∧
  (∀ hooks, runPostoutput hooks = (hooks, [])) ∧
  (∀ hooks f, atDisableLibraryThreading true hooks f = (hooks ++ [f], [])) ∧
  (∀ hooks f, atDisableLibraryThreading false hooks f = disableLibraryThreading (hooks ++ [f])) ∧
  (∀ hooks, disableLibraryThreading hooks = ([], hooks.reverse))

theorem hookBodies_proven : HookBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s f s' h
    unfold atexit at h
    split at h
    · simp at h
    · cases h; rfl
  · intro s f h
    exact ⟨.errorException "cannot register new atexit hook; already exiting.", by simp [atexit, h]⟩
  · intro hasMethod code s; simp [runAtexitHooks, Function.comp_def]
  · intro hasMethod code s; rfl
  · intro hooks f; rfl
  · intro hooks; rfl
  · intro hooks f; rfl
  · intro hooks f; rfl
  · intro hooks; rfl

end JuliaLean.RuntimeCov.InitDefsCoverage

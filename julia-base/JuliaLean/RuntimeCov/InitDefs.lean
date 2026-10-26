import JuliaLean.RuntimeCov.Common

/-!
`base/initdefs.jl`: process exit, the foreground task, depot and load-path
initialization from the environment, named-environment expansion, the active
project and manifest, and the exit/post-output/library-threading hook lists.

Paths and environment strings are character lists (`Str`) so concrete
counterexamples evaluate by `decide`.  File-system queries, the home
directory, `expanduser`, `abspath` and `joinpath` are inputs.
-/

namespace JuliaLean.RuntimeCov.InitDefs

open JuliaLean.RuntimeCov

abbrev Str := List Char

/-- `eachsplit(str, sep)` (keeping empty pieces). -/
def splitOn (c : Char) : Str → List Str
  | [] => [[]]
  | x :: xs =>
    if x = c then [] :: splitOn c xs
    else match splitOn c xs with
      | [] => [[x]]
      | s :: ss => (x :: s) :: ss

/-- `replace(s, '#' => r, count=1)`. -/
def replaceFirst (c : Char) (r : Str) : Str → Str
  | [] => []
  | x :: xs => if x = c then r ++ xs else x :: replaceFirst c r xs

/-! ## exit, foreground task, interactivity -/

/-- `exit(n)`, base/initdefs.jl:28: converts `n` to `Int32` (an `InexactError`
outside its range) and never returns; `.ok n` is the process exit code. -/
def exit (n : Int) : Rt Int :=
  if (JuliaLean.IntTy.i32).min ≤ n ∧ n ≤ (JuliaLean.IntTy.i32).max then .ok n else .error .inexactError
/-- `exit()`, base/initdefs.jl:29. -/
def exit0 : Rt Int := exit 0

/-- `foreground_task()`, base/initdefs.jl:42: the value stored in the lockable ref. -/
def foregroundTask {τ : Type} (stored : Option τ) : Option τ := stored

/-- `@as_foreground_task expr`, base/initdefs.jl:52-66: the foreground task
while `expr` runs and after it finishes (normally or by throwing). -/
def asForegroundTask {τ : Type} (prev : Option τ) (current : τ) : Option τ × Option τ :=
  (some current, prev)

/-- `isinteractive()`, base/initdefs.jl:75. -/
def isinteractive (flag : Bool) : Bool := flag

/-! ## DEPOT_PATH -/

/-- `append_bundled_depot_path!(DEPOT_PATH)`, base/initdefs.jl:132-138, with the
two bundled depot paths as inputs. -/
def appendBundled (b1 b2 : Str) (dp : List Str) : List Str :=
  let dp := if b1 ∈ dp then dp else dp ++ [b1]
  if b2 ∈ dp then dp else dp ++ [b2]

/-- The loop of `init_depot_path`, base/initdefs.jl:150-161: `first` is
`i == 1`; the result is the depot list and `pushfirst_default`. -/
def depotLoop (eu : Str → Str) (b1 b2 : Str) : Bool → List Str → List Str → Bool → List Str × Bool
  | _, [], dp, pf => (dp, pf)
  | first, p :: ps, dp, pf =>
    if p.isEmpty then depotLoop eu b1 b2 false ps (appendBundled b1 b2 dp) pf
    else
      let q := eu p
      let dp := if q ∈ dp then dp else dp ++ [q]
      depotLoop eu b1 b2 false ps dp (if first then false else pf)

/-- `init_depot_path()`, base/initdefs.jl:140-174: `env` is
`ENV["JULIA_DEPOT_PATH"]`, `user` is `joinpath(homedir(), ".julia")`. -/
def initDepotPath (env : Option Str) (sep : Char) (eu : Str → Str) (user b1 b2 : Str) : List Str :=
  match env with
  | none => appendBundled b1 b2 [user]
  | some str =>
    if str.isEmpty then []
    else
      let (dp, pf) := depotLoop eu b1 b2 true (splitOn sep str) [] true
      if pf then user :: dp else dp

/-! ## LOAD_PATH -/

/-- `DEFAULT_LOAD_PATH`, base/initdefs.jl:193. -/
def defaultLoadPath : List Str := [['@'], ['@', 'v', '#', '.', '#'], ['@', 's', 't', 'd', 'l', 'i', 'b']]

/-- `current_project(dir)`, base/initdefs.jl:237-250: walks to parents until the
home directory or a fixed point of `dirname`; `fuel` bounds the walk (the
parent chain of a real path is finite). -/
def currentProjectAt (projectNames : List Str) (join : Str → Str → Str) (isfileCS : Str → Bool)
    (dirname : Str → Str) (home : Str) : Nat → Str → Option Str
  | 0, _ => none
  | fuel + 1, dir =>
    match projectNames.find? (fun p => isfileCS (join dir p)) with
    | some p => some (join dir p)
    | none =>
      if dir = home then none
      else
        let parent := dirname dir
        if parent = dir then none else currentProjectAt projectNames join isfileCS dirname home fuel parent

/-- `current_project()`, base/initdefs.jl:252-259: `pwd` is `none` when it
throws an `IOError`. -/
def currentProject (pwd : Option Str) (search : Str → Option Str) : Option Str :=
  match pwd with
  | none => none
  | some d => search d

/-- `parse_load_path(str)`, base/initdefs.jl:261-279. -/
def parseLoadPath (sep : Char) (curProj : Option Str) (eu : Str → Str) (str : Str) : List Str :=
  if str.isEmpty then [] else
  (splitOn sep str).foldl (fun envs env =>
    if env.isEmpty then
      defaultLoadPath.foldl (fun envs e => if e ∈ envs then envs else envs ++ [e]) envs
    else
      let env' := if env = ['@', '.'] then curProj else some env
      match env' with
      | none => envs
      | some e => let e := eu e; if e ∈ envs then envs else envs ++ [e]) []

/-- `init_load_path()`, base/initdefs.jl:281-295. -/
def initLoadPath (sep : Char) (curProj : Option Str) (eu : Str → Str) (env : Option Str) : List Str :=
  match env with
  | some s => parseLoadPath sep curProj eu s
  | none => defaultLoadPath.filterMap fun e => if e = ['@', '.'] then curProj else some e

/-- `cmd_suppresses_program(cmd)`, base/initdefs.jl:325. -/
def cmdSuppressesProgram (c : Char) : Bool := c = 'e' || c = 'E'

/-- The runtime facts used by `load_path_expand`. -/
structure ExpandEnv where
  activeProjectNoSearch : Option Str
  currentProject : Option Str
  tempdir : Str
  stdlib : Str
  programFile : Option Str
  dirname : Str → Str
  currentProjectAt : Str → Option Str
  major : Str
  minor : Str
  patch : Str
  depots : List Str
  envDir : Str → Str → Str
  isdir : Str → Bool
  absJoin : Str → Str → Str
  isfileCS : Str → Bool
  projectNames : List Str
  newNamedEnvPath : Str → Str → Str
  initNamedEnv : Str → Option Str
  abspath : Str → Str

/-- The named-environment search of `load_path_expand`, base/initdefs.jl:351-362. -/
def namedSearch (e : ExpandEnv) (name : Str) : Option Str :=
  let rec go : List Str → Option Str
    | [] =>
      match e.depots with
      | [] => none
      | d :: _ => e.initNamedEnv (e.newNamedEnvPath d name)
    | d :: ds =>
      let path := e.envDir d name
      if !e.isdir path then go ds
      else match e.projectNames.find? (fun p => e.isfileCS (e.absJoin path p)) with
        | some p => some (e.absJoin path p)
        | none => go ds
  go e.depots

def kAt : Str := ['@']
def kDot : Str := ['@', '.']
def kTemp : Str := ['@', 't', 'e', 'm', 'p']
def kStdlib : Str := ['@', 's', 't', 'd', 'l', 'i', 'b']
def kScript : Str := ['@', 's', 'c', 'r', 'i', 'p', 't']

/-- `load_path_expand(env::AbstractString)`, base/initdefs.jl:327-374. -/
def loadPathExpand (e : ExpandEnv) (env : Str) : Option Str :=
  if kAt.isPrefixOf env then
    if env = kAt then e.activeProjectNoSearch
    else if env = kDot then e.currentProject
    else if env = kTemp then some e.tempdir
    else if env = kStdlib then some e.stdlib
    else if kScript.isPrefixOf env then
      match e.programFile with
      | none => none
      | some pf =>
        let dir := e.dirname pf
        let dir := if env ≠ kScript then dir ++ env.drop kScript.length else dir
        e.currentProjectAt dir
    else
      let env := replaceFirst '#' e.major env
      let env := replaceFirst '#' e.minor env
      let env := replaceFirst '#' e.patch env
      namedSearch e (env.drop 1)
  else
    let path := e.abspath env
    if e.isdir path then
      match e.projectNames.find? (fun p => e.isfileCS (e.absJoin path p)) with
      | some p => some (e.absJoin path p)
      | none => some path
    else some path

/-- `load_path_expand(::Nothing)`, base/initdefs.jl:375. -/
def loadPathExpandNothing : Option Str := none

/-- `init_active_project()`, base/initdefs.jl:297-306: the value passed to
`set_active_project`. -/
def initActiveProject (opt env : Option Str) (expand : Str → Option Str) (absUser : Str → Str) : Option Str :=
  let project := match opt with | some p => some p | none => env
  match project with
  | none => none
  | some p => if p.isEmpty then none else if kAt.isPrefixOf p then expand p else some (absUser p)

/-- `init_named_env!(path)`, base/initdefs.jl:308-322: returns the path when
`mkpath`/`open`/`print` succeed, `nothing` (with a warning) otherwise. -/
def initNamedEnv (writeOk : Bool) (path : Str) : Option Str := if writeOk then some path else none

/-- `active_project(search_load_path)`, base/initdefs.jl:382-404. -/
def activeProject (activeRef : Option Str) (expand : Str → Option Str) (isfileCS : Str → Bool)
    (ispath : Str → Bool) (isProjectName : Str → Bool) (withProject : Str → Str)
    (loadPath : List Str) (search : Bool) : Option Str :=
  let fromRef : Option (Option Str) :=
    match activeRef with
    | none => none
    | some p =>
      if p = kAt then none
      else match expand p with
        | none => none
        | some q => some (some (if !isfileCS q && !isProjectName q then withProject q else q))
  match fromRef with
  | some r => r
  | none =>
    if !search then none
    else loadPath.foldr (fun p acc =>
      if p = kAt then acc
      else match expand p with
        | none => acc
        | some q => if isfileCS q then some q else if ispath q then acc
                    else if isProjectName q then some q else acc) none

/-- `set_active_project(projfile)`, base/initdefs.jl:414-423: stores the value
and calls each callback once in order, catching their errors. -/
def setActiveProject (projfile : Option Str) (callbacks : List Nat) : Option Str × List Nat :=
  (projfile, callbacks)

/-- `active_manifest(project_file; search_load_path)`, base/initdefs.jl:443-448. -/
def activeManifest (projectFile : Option Str) (active : Option Str) (manifestOf : Str → Option Str) :
    Option Str :=
  match (match projectFile with | some p => some p | none => active) with
  | none => none
  | some p => manifestOf p

/-- `load_path()`, base/initdefs.jl:460-469 (no cache). -/
def loadPath (expand : Str → Option Str) (lp : List Str) : List Str :=
  lp.foldl (fun paths env => match expand env with
    | some p => if p ∈ paths then paths else paths ++ [p]
    | none => paths) []

/-! ## Hooks -/

/-- The atexit state: registered hooks (front is run first) and the finished flag. -/
structure AtexitState where
  hooks : List Nat
  finished : Bool
  deriving DecidableEq, Repr

/-- `atexit(f)`, base/initdefs.jl:502-510. -/
def atexit (s : AtexitState) (f : Nat) : Rt AtexitState :=
  if s.finished then .error (.errorException "cannot register new atexit hook; already exiting.")
  else .ok { s with hooks := f :: s.hooks }

/-- `_run_atexit_hooks(exitcode)`, base/initdefs.jl:535-567: pops hooks from the
front until empty, calling each with the exit code when it has a one-argument
method; errors are printed and swallowed. Returns the calls made. -/
def runAtexitHooks (hasCintMethod : Nat → Bool) (exitcode : Int) (s : AtexitState) :
    List (Nat × Option Int) × AtexitState :=
  (s.hooks.map fun f => (f, if hasCintMethod f then some exitcode else none), ⟨[], true⟩)

/-- `_atexit(exitcode)`, base/initdefs.jl:512-533: clears the task's queue and
wait registration, then runs the hooks with cancellation disabled. -/
def atexitImpl (hasCintMethod : Nat → Bool) (exitcode : Int) (s : AtexitState) :
    List (Nat × Option Int) × AtexitState :=
  runAtexitHooks hasCintMethod exitcode s

/-- `postoutput(f)`, base/initdefs.jl:574. -/
def postoutput (hooks : List Nat) (f : Nat) : List Nat := f :: hooks
/-- `_postoutput()`, base/initdefs.jl:576-587: calls in list order and empties it. -/
def runPostoutput (hooks : List Nat) : List Nat × List Nat := (hooks, [])

/-- `at_disable_library_threading(f)`, base/initdefs.jl:597-603 and
`disable_library_threading()`, lines 605-617: the hook vector, the enabled flag,
and the hooks called (popped from the end). -/
def disableLibraryThreading (hooks : List Nat) : List Nat × List Nat := ([], hooks.reverse)
def atDisableLibraryThreading (enabled : Bool) (hooks : List Nat) (f : Nat) :
    List Nat × List Nat :=
  if enabled then (hooks ++ [f], []) else disableLibraryThreading (hooks ++ [f])

/-! ## Properties -/

theorem splitOn_no_sep (c : Char) : ∀ s : Str, c ∉ s → splitOn c s = [s]
  | [] , _ => rfl
  | x :: xs, h => by
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    have hxs : c ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitOn, hx, splitOn_no_sep c xs hxs]

theorem splitOn_append_sep (c : Char) (t : Str) : ∀ s : Str, c ∉ s →
    splitOn c (s ++ c :: t) = s :: splitOn c t
  | [], _ => by simp [splitOn]
  | x :: xs, h => by
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    have hxs : c ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitOn, hx, splitOn_append_sep c t xs hxs]

/-- The documented `JULIA_DEPOT_PATH` expansion (manual, "JULIA_DEPOT_PATH"):
unset gives the user depot then the bundled depots; the empty string gives no
depot; `"/foo:"` replaces the user depot; `":/foo"` appends after the full
default list; `":"` is the full default list. -/
def DepotPathDocumented : Prop :=
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 : Str), u ≠ b1 → u ≠ b2 → b1 ≠ b2 →
      initDepotPath none sep eu u b1 b2 = [u, b1, b2]) ∧
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 : Str), initDepotPath (some []) sep eu u b1 b2 = []) ∧
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 foo : Str), foo ≠ [] → sep ∉ foo →
      eu foo ≠ b1 → eu foo ≠ b2 → b1 ≠ b2 →
      initDepotPath (some (foo ++ [sep])) sep eu u b1 b2 = [eu foo, b1, b2]) ∧
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 foo : Str), foo ≠ [] → sep ∉ foo →
      eu foo ≠ b1 → eu foo ≠ b2 → b1 ≠ b2 →
      initDepotPath (some (sep :: foo)) sep eu u b1 b2 = [u, b1, b2, eu foo]) ∧
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 : Str), b1 ≠ b2 →
      initDepotPath (some [sep]) sep eu u b1 b2 = [u, b1, b2])

theorem depotPathDocumented_proven : DepotPathDocumented := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sep eu u b1 b2 h1 h2 h3
    simp [initDepotPath, appendBundled, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  · intro sep eu u b1 b2; simp [initDepotPath]
  · intro sep eu u b1 b2 foo hf hs h1 h2 h3
    have hsplit : splitOn sep (foo ++ [sep]) = [foo, []] := by
      rw [splitOn_append_sep sep [] foo hs]; rfl
    have hne : (foo ++ [sep]).isEmpty = false := by cases foo <;> simp_all
    have hfe : foo.isEmpty = false := by cases foo <;> simp_all
    simp only [initDepotPath, hne, hsplit, Bool.false_eq_true, ↓reduceIte]
    simp [depotLoop, hfe, appendBundled, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  · intro sep eu u b1 b2 foo hf hs h1 h2 h3
    have hsplit : splitOn sep (sep :: foo) = [[], foo] := by
      simp [splitOn, splitOn_no_sep sep foo hs]
    have hfe : foo.isEmpty = false := by cases foo <;> simp_all
    simp only [initDepotPath, hsplit, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    simp [depotLoop, hfe, appendBundled, h1, h2, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  · intro sep eu u b1 b2 h3
    have hsplit : splitOn sep [sep] = [[], []] := by simp [splitOn]
    simp only [initDepotPath, hsplit, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    simp [depotLoop, appendBundled, Ne.symm h3]

/-- Invariant: `init_depot_path` never lists a depot twice (every push is
guarded by `path in DEPOT_PATH`). -/
def DepotPathNoDuplicates : Prop :=
  ∀ (env : Option Str) (sep : Char) (eu : Str → Str) (u b1 b2 : Str),
    (initDepotPath env sep eu u b1 b2).Nodup

/-- A leading empty depot-path entry followed by the user depot lists that depot twice. -/
theorem depotPathNoDuplicates_refuted : ¬ DepotPathNoDuplicates := by
  intro h
  have := h (some [':', 'u']) ':' id ['u'] ['a'] ['b']
  revert this; decide

/-- The documented `JULIA_LOAD_PATH` expansion (manual, "JULIA_LOAD_PATH"):
the empty string gives an empty `LOAD_PATH`; `":"` gives the default load path;
`"/foo/bar:"` prepends `/foo/bar` to the defaults; unset gives the defaults. -/
def LoadPathDocumented : Prop :=
  (∀ sep cp (eu : Str → Str), parseLoadPath sep cp eu [] = []) ∧
  (∀ sep cp (eu : Str → Str), parseLoadPath sep cp eu [sep] = defaultLoadPath) ∧
  (∀ sep cp (eu : Str → Str) (foo : Str), foo ≠ [] → sep ∉ foo → foo ≠ ['@', '.'] →
      eu foo ∉ defaultLoadPath →
      parseLoadPath sep cp eu (foo ++ [sep]) = eu foo :: defaultLoadPath) ∧
  (∀ sep cp (eu : Str → Str), initLoadPath sep cp eu none = defaultLoadPath) ∧
  (∀ sep cp (eu : Str → Str) s, initLoadPath sep cp eu (some s) = parseLoadPath sep cp eu s)

theorem loadPathDocumented_proven : LoadPathDocumented := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sep cp eu; simp [parseLoadPath]
  · intro sep cp eu
    have hsplit : splitOn sep [sep] = [[], []] := by simp [splitOn]
    simp only [parseLoadPath, hsplit, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true,
      ↓reduceIte, List.foldl_cons, List.foldl_nil]
    decide
  · intro sep cp eu foo hf hs hd hn
    have hsplit : splitOn sep (foo ++ [sep]) = [foo, []] := by
      rw [splitOn_append_sep sep [] foo hs]; rfl
    have hne : (foo ++ [sep]).isEmpty = false := by cases foo <;> simp_all
    have hfe : foo.isEmpty = false := by cases foo <;> simp_all
    simp only [parseLoadPath, hne, hsplit, Bool.false_eq_true, ↓reduceIte, List.foldl_cons,
      List.foldl_nil, hfe, hd]
    simp only [defaultLoadPath] at hn ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨h1, h2, h3⟩ := hn
    have g1 : ¬ ['@'] = eu foo := fun e => h1 e.symm
    have g2 : ¬ ['@', 'v', '#', '.', '#'] = eu foo := fun e => h2 e.symm
    have g3 : ¬ ['@', 's', 't', 'd', 'l', 'i', 'b'] = eu foo := fun e => h3 e.symm
    simp [h1, h2, h3, g1, g2, g3]
  · intro sep cp eu; rfl
  · intro sep cp eu s; rfl

/-- The `LOAD_PATH` docstring: `@name` (other than the special `@`, `@.`,
`@temp`, `@stdlib` and `@script[/path]` forms) refers to the named environment
`name` in the depots. -/
def LoadPathNamedEnv : Prop :=
  ∀ (e : ExpandEnv) (name : Str),
    name ∉ [[], ['.'], ['t', 'e', 'm', 'p'], ['s', 't', 'd', 'l', 'i', 'b'], ['s', 'c', 'r', 'i', 'p', 't']] →
    ¬ (['s', 'c', 'r', 'i', 'p', 't', '/'].isPrefixOf name) → '#' ∉ name →
    loadPathExpand e ('@' :: name) = namedSearch e name

/-- The environment for the counterexample: one depot whose `environments/scripts`
holds a `Project.toml`, running without a script file. -/
def scriptsEnv : ExpandEnv where
  activeProjectNoSearch := none
  currentProject := none
  tempdir := ['t']
  stdlib := ['s']
  programFile := none
  dirname := id
  currentProjectAt := fun _ => none
  major := ['1']
  minor := ['1']
  patch := ['0']
  depots := [['d']]
  envDir := fun d n => d ++ ['/'] ++ n
  isdir := fun _ => true
  absJoin := fun p q => p ++ ['/'] ++ q
  isfileCS := fun _ => true
  projectNames := [['P']]
  newNamedEnvPath := fun d n => d ++ n
  initNamedEnv := some
  abspath := id

/-- `@scripts` is taken for `@script` followed by the relative path `s`. -/
theorem loadPathNamedEnv_refuted : ¬ LoadPathNamedEnv := by
  intro h
  have := h scriptsEnv ['s', 'c', 'r', 'i', 'p', 't', 's'] (by decide) (by decide) (by decide)
  revert this; decide

/-- Further documented behaviour of `base/initdefs.jl`. -/
def InitDefsBodies : Prop :=
  -- exit codes must fit in `Int32`
  (∀ n : Int, exit n = .ok n ↔ (-2147483648 ≤ n ∧ n ≤ 2147483647)) ∧
  exit0 = .ok 0 ∧
  (∀ (τ : Type) (s : Option τ), foregroundTask s = s) ∧
  -- the foreground task is `current_task()` inside and restored afterwards
  (∀ (τ : Type) (prev : Option τ) (c : τ), asForegroundTask prev c = (some c, prev)) ∧
  (∀ b, isinteractive b = b) ∧
  -- bundled depots are appended once, after the existing entries
  (∀ (b1 b2 : Str) (dp : List Str), dp.Nodup → b1 ≠ b2 → (appendBundled b1 b2 dp).Nodup) ∧
  (∀ (b1 b2 : Str) (dp : List Str), dp.IsPrefix (appendBundled b1 b2 dp)) ∧
  -- `current_project` only returns an existing project file in the walk
  (∀ names join isf dn home fuel dir p, currentProjectAt names join isf dn home fuel dir = some p →
      isf p = true) ∧
  (∀ s, currentProject none s = none) ∧
  (∀ c : Char, cmdSuppressesProgram c = true ↔ c = 'e' ∨ c = 'E') ∧
  -- `load_path_expand` special forms
  (∀ e : ExpandEnv, loadPathExpand e kAt = e.activeProjectNoSearch) ∧
  (∀ e : ExpandEnv, loadPathExpand e kDot = e.currentProject) ∧
  (∀ e : ExpandEnv, loadPathExpand e kTemp = some e.tempdir) ∧
  (∀ e : ExpandEnv, loadPathExpand e kStdlib = some e.stdlib) ∧
  (∀ e : ExpandEnv, e.programFile = none → loadPathExpand e kScript = none) ∧
  (∀ (e : ExpandEnv) (pf : Str), e.programFile = some pf →
      loadPathExpand e kScript = e.currentProjectAt (e.dirname pf)) ∧
  -- a named environment found in a depot is a project file there
  (∀ (e : ExpandEnv) (name p : Str), e.depots ≠ [] → namedSearch e name = some p →
      (∃ d ∈ e.depots, ∃ q ∈ e.projectNames, p = e.absJoin (e.envDir d name) q ∧
        e.isfileCS p = true) ∨
      (∃ d ds, e.depots = d :: ds ∧ e.initNamedEnv (e.newNamedEnvPath d name) = some p)) ∧
  (∀ e : ExpandEnv, e.depots = [] → ∀ name, namedSearch e name = none) ∧
  loadPathExpandNothing = none ∧
  (∀ ex au, initActiveProject none none ex au = none) ∧
  (∀ env ex au, initActiveProject (some []) env ex au = none) ∧
  (∀ w p, initNamedEnv w p = some p ↔ w = true) ∧
  (∀ ex isf isp isn wp lp, activeProject none ex isf isp isn wp lp false = none) ∧
  (∀ p cbs, (setActiveProject p cbs).1 = p ∧ (setActiveProject p cbs).2 = cbs) ∧
  (∀ a m, activeManifest none a m = (a.bind m)) ∧
  (∀ p a m, activeManifest (some p) a m = m p) ∧
  (∀ ex lp, (loadPath ex lp).Nodup) ∧
  -- atexit hooks run last-registered first, then registration fails
  (∀ s f s', atexit s f = .ok s' → s'.hooks = f :: s.hooks) ∧
  (∀ s f, s.finished = true → ∃ e, atexit s f = .error e) ∧
  (∀ hm c s, (runAtexitHooks hm c s).1.map Prod.fst = s.hooks ∧ (runAtexitHooks hm c s).2.finished = true) ∧
  (∀ hm c f1 f2 s1 s2, atexit ⟨[], false⟩ f1 = .ok s1 → atexit s1 f2 = .ok s2 →
      (runAtexitHooks hm c s2).1.map Prod.fst = [f2, f1]) ∧
  (∀ hm c s, atexitImpl hm c s = runAtexitHooks hm c s) ∧
  (∀ hs f, postoutput hs f = f :: hs) ∧
  (∀ hs, runPostoutput hs = (hs, [])) ∧
  (∀ hs f, atDisableLibraryThreading true hs f = (hs ++ [f], [])) ∧
  (∀ hs f, (atDisableLibraryThreading false hs f).2 = f :: hs.reverse)

theorem nodup_append_single (x : Str) : ∀ l : List Str, l.Nodup → x ∉ l → (l ++ [x]).Nodup
  | [], _, _ => by simp
  | a :: l, h, hx => by
    rw [List.nodup_cons] at h
    simp only [List.cons_append, List.nodup_cons]
    refine ⟨?_, nodup_append_single x l h.2 (fun m => hx (List.mem_cons_of_mem _ m))⟩
    intro hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · exact h.1 hm
    · simp at hm; subst hm; exact hx (by simp)

theorem pushUnique_nodup (x : Str) (l : List Str) (h : l.Nodup) :
    (if x ∈ l then l else l ++ [x]).Nodup := by
  split
  · exact h
  · rename_i hm; exact nodup_append_single x l h hm

theorem appendBundled_nodup (b1 b2 : Str) (dp : List Str) (h : dp.Nodup) (_hb : b1 ≠ b2) :
    (appendBundled b1 b2 dp).Nodup :=
  pushUnique_nodup b2 _ (pushUnique_nodup b1 dp h)

theorem appendBundled_prefix (b1 b2 : Str) (dp : List Str) : dp.IsPrefix (appendBundled b1 b2 dp) := by
  unfold appendBundled
  simp only
  split <;> split <;> simp

theorem currentProjectAt_file (names : List Str) (join : Str → Str → Str) (isf : Str → Bool)
    (dn : Str → Str) (home : Str) : ∀ (fuel : Nat) (dir p : Str),
    currentProjectAt names join isf dn home fuel dir = some p → isf p = true
  | 0, _, _, h => by simp [currentProjectAt] at h
  | fuel + 1, dir, p, h => by
    simp only [currentProjectAt] at h
    split at h
    · rename_i q hq
      simp at h; subst h
      have := List.find?_some hq; simpa using this
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact currentProjectAt_file names join isf dn home fuel _ p h

theorem namedSearch_go (e : ExpandEnv) (name p : Str) : ∀ ds : List Str,
    namedSearch.go e name ds = some p →
    (∃ d ∈ ds, ∃ q ∈ e.projectNames, p = e.absJoin (e.envDir d name) q ∧ e.isfileCS p = true) ∨
    (match e.depots with | [] => none | d :: _ => e.initNamedEnv (e.newNamedEnvPath d name)) = some p
  | [], h => by right; simpa [namedSearch.go] using h
  | d :: ds, h => by
    simp only [namedSearch.go] at h
    split at h
    · rcases namedSearch_go e name p ds h with ⟨d', hd, q, hq, h1⟩ | h2
      · exact Or.inl ⟨d', List.mem_cons_of_mem _ hd, q, hq, h1⟩
      · exact Or.inr h2
    · split at h
      · rename_i q hq
        simp at h; subst h
        have hfq := List.find?_some hq
        exact Or.inl ⟨d, by simp, q, List.mem_of_find?_eq_some hq, rfl, by simpa using hfq⟩
      · rcases namedSearch_go e name p ds h with ⟨d', hd, q, hq, h1⟩ | h2
        · exact Or.inl ⟨d', List.mem_cons_of_mem _ hd, q, hq, h1⟩
        · exact Or.inr h2

theorem loadPath_nodup (ex : Str → Option Str) (lp : List Str) : (loadPath ex lp).Nodup := by
  unfold loadPath
  suffices ∀ (acc : List Str), acc.Nodup → (lp.foldl (fun paths env => match ex env with
      | some p => if p ∈ paths then paths else paths ++ [p]
      | none => paths) acc).Nodup from this [] List.nodup_nil
  induction lp with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    split
    · split
      · exact h
      · rename_i p _ hm
        exact nodup_append_single p _ h hm
    · exact h

theorem initDefsBodies_proven : InitDefsBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [exit, JuliaLean.IntTy.min, JuliaLean.IntTy.max, JuliaLean.IntTy.signed,
      JuliaLean.IntTy.bits]
    split <;> simp_all <;> omega
  · rfl
  · intro _ _; rfl
  · intro _ _ _; rfl
  · intro _; rfl
  · intro b1 b2 dp h hb; exact appendBundled_nodup b1 b2 dp h hb
  · intro b1 b2 dp; exact appendBundled_prefix b1 b2 dp
  · intro names join isf dn home fuel dir p h; exact currentProjectAt_file names join isf dn home fuel dir p h
  · intro _; rfl
  · intro c; simp [cmdSuppressesProgram]
  · intro e; simp [loadPathExpand, kAt]
  · intro e; simp [loadPathExpand, kAt, kDot]
  · intro e; simp [loadPathExpand, kAt, kDot, kTemp]
  · intro e; simp [loadPathExpand, kAt, kDot, kTemp, kStdlib]
  · intro e h; simp [loadPathExpand, kAt, kDot, kTemp, kStdlib, kScript, h]
  · intro e pf h; simp [loadPathExpand, kAt, kDot, kTemp, kStdlib, kScript, h]
  · intro e name p hd h
    rcases namedSearch_go e name p e.depots h with h1 | h2
    · exact Or.inl h1
    · right
      cases hds : e.depots with
      | nil => exact absurd hds hd
      | cons d ds => rw [hds] at h2; exact ⟨d, ds, rfl, h2⟩
  · intro e hd name
    simp only [namedSearch]
    rw [hd]; simp [namedSearch.go, hd]
  · rfl
  · intro _ _; rfl
  · intro env ex au; cases env <;> simp [initActiveProject]
  · intro w p; cases w <;> simp [initNamedEnv]
  · intro ex isf isp isn wp lp; simp [activeProject]
  · intro p cbs; exact ⟨rfl, rfl⟩
  · intro a m; cases a <;> rfl
  · intro p a m; rfl
  · intro ex lp; exact loadPath_nodup ex lp
  · intro s f s' h
    unfold atexit at h
    split at h
    · simp at h
    · simp at h; subst h; rfl
  · intro s f h; simp [atexit, h]
  · intro hm c s; simp [runAtexitHooks, Function.comp_def]
  · intro hm c f1 f2 s1 s2 h1 h2
    simp [atexit] at h1
    subst h1
    simp [atexit] at h2
    subst h2
    rfl
  · intro _ _ _; rfl
  · intro _ _; rfl
  · intro _; rfl
  · intro _ _; rfl
  · intro hs f; simp [atDisableLibraryThreading, disableLibraryThreading]

end JuliaLean.RuntimeCov.InitDefs

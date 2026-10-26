import JuliaLean.Loading.CoverageExtensions

namespace JuliaLean.Loading.Coverage.Require

open JuliaLean.Loading.Coverage
open JuliaLean.Loading.Coverage.Early
open JuliaLean.Loading.Coverage.Extensions

structure DependencyRecord where
  path : String
  size : Nat
  hash : Nat
  mtime : Int
  deriving Repr, DecidableEq

def method2677 (includeFn : String → Bool → Bool → String × Option String)
    (path : String) (trackContent : Bool) := includeFn path trackContent false
def Property2677 : Prop := ∀ includeFn path track,
  (method2677 includeFn path track).1 = (includeFn path track false).1
theorem property2677 : Property2677 := by simp [Property2677, method2677]

def method2682 (previous : Option String) (path : String) (track enabled readable : Bool)
    (contentHash size mtime : Nat) : Result (String × Option DependencyRecord) :=
  if !enabled && !readable then .error .system else
  let absolute := previous.map (fun parent => parent ++ "/" ++ path) |>.getD path
  if enabled then .ok (absolute, some ⟨absolute, if track then size else 0,
    if track then contentHash else 0, if track then -1 else Int.ofNat mtime⟩)
  else .ok (absolute, none)
def Property2682 : Prop := ∀ previous path track enabled readable hash size mtime absolute
    (record : Option DependencyRecord),
  method2682 previous path track enabled readable hash size mtime = .ok (absolute, record) →
  enabled = true → record.isSome
theorem property2682 : Property2682 := by
  intro previous path track enabled readable hash size mtime absolute record h he
  subst enabled
  simp [method2682] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

def method2721 (isIdentity : Bool) (table : List ((Nat × String) × Nat))
    (moduleId : Nat) (path : String) (mapexpr : Nat) : List ((Nat × String) × Nat) :=
  if isIdentity then table else updateAssoc (moduleId, path) mapexpr table
def Property2721 : Prop := ∀ identity table moduleId path mapexpr,
  identity = false → lookupAssoc (moduleId, path) (method2721 identity table moduleId path mapexpr) = some mapexpr
theorem property2721 : Property2721 := by
  intro identity table moduleId path mapexpr h
  subst identity
  simp [method2721, updateAssoc, lookupAssoc]

def method2758 (defined : Bool) (table : α) : Option α := if defined then some table else none
def Property2758 : Prop := ∀ (α : Type) defined (table : α),
  method2758 defined table = none ↔ defined = false
theorem property2758 : Property2758 := by
  intro α defined table
  cases defined <;> simp [method2758]

def method2781 (includeFn : String → Bool → Unit) (path : String) (track : Bool) : Unit :=
  includeFn path track
def Property2781 : Prop := ∀ includeFn path track, method2781 includeFn path track = includeFn path track
theorem property2781 : Property2781 := by simp [Property2781, method2781]

def method2788 (stream : List String) : List String := stream ++ ["precompilation disabled"]
def Property2788 : Prop := ∀ stream, List.IsPrefix stream (method2788 stream)
theorem property2788 : Property2788 := by intro; simp [method2788]

def method2791 : Bool := true
def Property2791 : Prop := ∀ _ : Unit, method2791 = true
theorem property2791 : Property2791 := by intro; rfl

def method2792 (inner : Bool) : Bool := inner
def Property2792 : Prop := ∀ inner, method2792 inner = inner
theorem property2792 : Property2792 := by simp [Property2792, method2792]

def method2793 (_exception : α) : Bool := false
def Property2793 : Prop := ∀ (α : Type) (exception : α), method2793 exception = false
theorem property2793 : Property2793 := by simp [Property2793, method2793]

def method2803 (precompilable generating : Bool) : Result Unit :=
  if !precompilable && generating then .error .other else .ok ()
def Property2803 : Prop := ∀ precompilable generating,
  method2803 precompilable generating = .error .other ↔ precompilable = false ∧ generating = true
theorem property2803 : Property2803 := by
  intro precompilable generating; cases precompilable <;> cases generating <;> simp [method2803]

def method2847 (storedWorld currentWorld : Nat) (invoke : Nat → α) : α :=
  invoke (if storedWorld = 0 then currentWorld else storedWorld)
def Property2847 : Prop := ∀ (α : Type) stored current invoke,
  stored = 0 → method2847 (α := α) stored current invoke = invoke current
theorem property2847 : Property2847 := by
  intro α stored current invoke h
  subst stored
  simp [method2847]

def method2855 (locallyDefined parentDefined : Bool) : Bool × String :=
  if locallyDefined then (true, ".") else if parentDefined then (true, "..") else (false, "")
def Property2855 : Prop := ∀ locallyDefined parent,
  (method2855 locallyDefined parent).1 = false ↔ locallyDefined = false ∧ parent = false
theorem property2855 : Property2855 := by
  intro locallyDefined parent; cases locallyDefined <;> cases parent <;> simp [method2855]

inductive RequireResult where | top (moduleId : Nat) | loaded (moduleId : Nat) | missing | dependencyError
  deriving Repr, DecidableEq
def method2867 (outsideModule precompiling selfImport : Bool) (topModule : Nat)
    (identified : Option PackageId) (loaded : Nat) : RequireResult :=
  if outsideModule && precompiling then .dependencyError
  else if selfImport then .top topModule
  else match identified with | none => .missing | some _ => .loaded loaded
def Property2867 : Prop := ∀ outside precompile self top identified loaded,
  method2867 outside precompile self top identified loaded = .top top → self = true
theorem property2867 : Property2867 := by
  intro outside precompile self top identified loaded h
  cases outside <;> cases precompile <;> cases self <;> cases identified <;> simp_all [method2867]

structure ManifestVersion where
  path : String
  compatible : Bool
  dev : Bool
  deriving Repr, DecidableEq
def method2919 (manifests : List ManifestVersion) : List String × List String :=
  (manifests.filterMap fun m => if m.compatible then none else some m.path,
   manifests.filterMap fun m => if m.compatible && m.dev then some m.path else none)
def Property2919 : Prop := ∀ manifests path,
  path ∈ (method2919 manifests).1 → ∃ m ∈ manifests, m.path = path ∧ m.compatible = false
theorem property2919 : Property2919 := by
  intro manifests path h
  simp [method2919] at h
  rcases h with ⟨m, hm, hc, hp⟩
  exact ⟨m, hm, hp, hc⟩

def method2948 (unsuitable dev : List String) : List String :=
  (if unsuitable.isEmpty then [] else unsuitable) ++ (if dev.isEmpty then [] else dev)
def Property2948 : Prop := ∀ unsuitable dev path,
  path ∈ method2948 unsuitable dev → path ∈ unsuitable ∨ path ∈ dev
theorem property2948 : Property2948 := by
  intro unsuitable dev path h
  by_cases hu : unsuitable.isEmpty <;> by_cases hd : dev.isEmpty <;>
    simp_all [method2948]

def method2970 (stored current : Nat) (invoke : Nat → α) : α :=
  invoke (if stored = 0 then current else stored)
def Property2970 : Prop := ∀ (α : Type) stored current invoke,
  stored = 0 → method2970 (α := α) stored current invoke = invoke current
theorem property2970 : Property2970 := by
  intro α stored current invoke h
  subst stored
  simp [method2970]

def method2977 (cacheAlreadySet : Bool) (requireResult : α) : α × Bool :=
  (requireResult, cacheAlreadySet)
def Property2977 : Prop := ∀ (α : Type) set (result : α), (method2977 set result).1 = result
theorem property2977 : Property2977 := by simp [Property2977, method2977]

def method2994 (track alreadyLoaded : Bool) (load : α) : α × Bool := (load, track && !alreadyLoaded)
def Property2994 : Prop := ∀ (α : Type) track loaded (result : α),
  (method2994 track loaded result).1 = result
theorem property2994 : Property2994 := by simp [Property2994, method2994]

structure OriginModel where
  path : Option String
  cache : Option String
  version : Option String
  deriving Repr, DecidableEq
def method3032 : OriginModel := ⟨none, none, none⟩
def Property3032 : Prop := ∀ _ : Unit,
  method3032.path = none ∧ method3032.cache = none ∧ method3032.version = none
theorem property3032 : Property3032 := by intro; exact ⟨rfl, rfl, rfl⟩

def method3039 (pkgId : α → PackageId) (module : α) := pkgId module
def Property3039 : Prop := ∀ (α : Type) pkgId module,
  method3039 (α := α) pkgId module = pkgId module
theorem property3039 : Property3039 := by simp [Property3039, method3039]

def method3041 : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (moduleId, build) :: rest, buildId => if build == buildId then some moduleId else method3041 rest buildId
def Property3041 : Prop := ∀ modules build moduleId,
  method3041 modules build = some moduleId → (moduleId, build) ∈ modules
theorem property3041 : Property3041 := by
  intro modules build moduleId h
  induction modules with
  | nil => simp [method3041] at h
  | cons pair rest ih =>
      rcases pair with ⟨found, foundBuild⟩
      by_cases heq : foundBuild = build <;> simp_all [method3041, heq]

def method3051 (high low : Nat) : Nat := high * 2 ^ 64 + low
def Property3051 : Prop := ∀ high low, method3051 high low % 2 ^ 64 = low % 2 ^ 64
theorem property3051 : Property3051 := by
  intro; simp [method3051, Nat.add_mod]

def method3056 (key : PackageId) (moduleId buildId : Nat)
    (loaded : List (PackageId × Nat)) : List (PackageId × Nat) := updateAssoc key moduleId loaded
def Property3056 : Prop := ∀ key moduleId build loaded,
  lookupAssoc key (method3056 key moduleId build loaded) = some moduleId
theorem property3056 : Property3056 := by simp [Property3056, method3056, updateAssoc, lookupAssoc]

def method3079 (alreadyRoot : Bool) (register : Unit → Unit) : Bool :=
  if alreadyRoot then false else let _ := register (); true
def Property3079 : Prop := ∀ already register,
  method3079 already register = true → already = false
theorem property3079 : Property3079 := by
  intro already register h
  cases already <;> simp_all [method3079]

def method3102 (lookup : PackageId → Option Nat) (key : PackageId) : Result Nat :=
  match lookup key with | some m => .ok m | none => .error .bounds
def Property3102 : Prop := ∀ lookup key moduleId,
  method3102 lookup key = .ok moduleId → lookup key = some moduleId
theorem property3102 : Property3102 := by
  intro lookup key moduleId h
  cases hl : lookup key <;> simp_all [method3102]

def method3103 (identify : α → String → Option PackageId) (root : PackageId → Result Nat)
    (context : α) (name : String) : Result Nat :=
  match identify context name with | some key => root key | none => .error .bounds
def Property3103 : Prop := ∀ (α : Type) identify root context name moduleId,
  method3103 (α := α) identify root context name = .ok moduleId →
  ∃ key, identify context name = some key ∧ root key = .ok moduleId
theorem property3103 : Property3103 := by
  intro α identify root context name moduleId h
  cases hi : identify context name <;> simp_all [method3103]

def method3108 (contains : PackageId → Bool) (key : PackageId) := contains key
def Property3108 : Prop := ∀ contains key, method3108 contains key = true → contains key = true
theorem property3108 : Property3108 := by simp [Property3108, method3108]

def method3109 (lookup : PackageId → Option Nat) (key : PackageId) := lookup key
def Property3109 : Prop := ∀ lookup key result,
  method3109 lookup key = some result → lookup key = some result
theorem property3109 : Property3109 := by simp [Property3109, method3109]

def method3111 (order : List Nat) : List Nat := order
def Property3111 : Prop := ∀ order, (method3111 order).length = order.length
theorem property3111 : Property3111 := by simp [Property3111, method3111]

def method3115 (loaded : List (PackageId × Nat)) (key : PackageId) := loaded.filter (fun p => p.1 != key)
def Property3115 : Prop := ∀ loaded key, lookupAssoc key (method3115 loaded key) = none
theorem property3115 : Property3115 := by simp [Property3115, method3115, lookupAssoc]

def method3126 (origin : OriginModel) (path version : String) (generating : Bool) : OriginModel :=
  { origin with path := some path, version := if generating then some version else origin.version }
def Property3126 : Prop := ∀ origin path version generating,
  (method3126 origin path version generating).path = some path
theorem property3126 : Property3126 := by simp [Property3126, method3126]

def method3140 (located : Option LoadSpec) (cacheLoaded sourceLoaded : Option Nat) : RequireResult :=
  match located with
  | none => .missing
  | some _ => match cacheLoaded.orElse (fun _ => sourceLoaded) with
    | some moduleId => .loaded moduleId
    | none => .dependencyError
def Property3140 : Prop := ∀ located cache source moduleId,
  method3140 located cache source = .loaded moduleId → located.isSome
theorem property3140 : Property3140 := by
  intro located cache source moduleId h
  cases located <;> simp_all [method3140]

def method3305 (loaded : SerializedResult) : SerializedResult := loaded
def Property3305 : Prop := ∀ loaded, method3305 loaded = loaded
theorem property3305 : Property3305 := by simp [Property3305, method3305]

def method3367 (require : PackageId → Option String → Nat → Nat) (pkg : PackageId) : Nat :=
  require pkg none 0
def Property3367 : Prop := ∀ require pkg, method3367 require pkg = require pkg none 0
theorem property3367 : Property3367 := by simp [Property3367, method3367]

def method3368 (loadedSource loadedCache : Option Nat) : Option Nat := choose loadedCache loadedSource
def Property3368 : Prop := ∀ source cache result,
  method3368 source cache = some result → cache = some result ∨ source = some result
theorem property3368 : Property3368 := by
  intro source cache result h; cases cache <;> cases source <;> simp_all [method3368, choose]

def method3421 (override cli : Option Nat) : Option Nat := choose override cli
def Property3421 : Prop := ∀ override cli result,
  method3421 override cli = some result → override = some result ∨ cli = some result
theorem property3421 : Property3421 := by
  intro override cli result h; cases override <;> cases cli <;> simp_all [method3421, choose]

def method3444 (parseEval : String → String → α) (code filename : String) : α := parseEval code filename
def Property3444 : Prop := ∀ (α : Type) parse code filename result,
  method3444 (α := α) parse code filename = result → parse code filename = result
theorem property3444 : Property3444 := by simp [Property3444, method3444]

def method3472 (includeString : Nat → String → String → α) (moduleId : Nat)
    (text filename : String) : α := includeString moduleId text filename
def Property3472 : Prop := ∀ (α : Type) includeString moduleId text filename,
  method3472 (α := α) includeString moduleId text filename = includeString moduleId text filename
theorem property3472 : Property3472 := by simp [Property3472, method3472]

def method3475 (tlsPath : Option String) (default : Option String) : Option String := choose tlsPath default
def Property3475 : Prop := ∀ tls default result,
  method3475 tls default = some result → tls = some result ∨ default = some result
theorem property3475 : Property3475 := by
  intro tls default result h; cases tls <;> cases default <;> simp_all [method3475, choose]

def method3486 (path : Option String) (dirname : String → String) : Option String := path.map dirname
def Property3486 : Prop := ∀ path dirname result,
  method3486 path dirname = some result → ∃ source, path = some source ∧ result = dirname source
theorem property3486 : Property3486 := by
  intro path dirname result h; cases path <;> simp_all [method3486]

def method3512 (record : String → Unit) (evaluate : String → α) (path : String) : α :=
  let _ := record path; evaluate path
def Property3512 : Prop := ∀ (α : Type) record evaluate path,
  method3512 (α := α) record evaluate path = evaluate path
theorem property3512 : Property3512 := by simp [Property3512, method3512]

def method3559 (oldArgs newArgs : List String) (evaluate : List String → α) : α × List String :=
  (evaluate newArgs, oldArgs)
def Property3559 : Prop := ∀ (α : Type) oldArgs newArgs evaluate,
  (method3559 (α := α) oldArgs newArgs evaluate).2 = oldArgs
theorem property3559 : Property3559 := by simp [Property3559, method3559]

def method3568 (convert : List α → Result (List String)) (evaluate : List String → β)
    (args : List α) : Result β :=
  match convert args with | .ok values => .ok (evaluate values) | .error error => .error error
def Property3568 : Prop := ∀ (α β : Type) convert evaluate args error,
  convert args = .error error → method3568 (α := α) (β := β) convert evaluate args = .error error
theorem property3568 : Property3568 := by
  intro α β convert evaluate args error h
  simp [method3568, h]

def method3570 (setupLoadPath : Bool) (active load depot dl : List String) : List (String × List String) :=
  [("active", active), ("depot", depot), ("dl", dl)] ++ if setupLoadPath then [("load", load)] else []
def Property3570 : Prop := ∀ setup active load depot dl,
  ("depot", depot) ∈ method3570 setup active load depot dl
theorem property3570 : Property3570 := by intro; simp [method3570]

structure OutputSetup where
  depot : List String
  dl : List String
  load : List String
  concrete : List (PackageId × Nat)
  source : Option String
  deriving Repr, DecidableEq
def method3593 (depot dl load : List String) (concrete : List (PackageId × Nat))
    (source : Option String) : OutputSetup := ⟨depot, dl, load, concrete, source⟩
def Property3593 : Prop := ∀ depot dl load concrete source,
  (method3593 depot dl load concrete source).concrete = concrete
theorem property3593 : Property3593 := by simp [Property3593, method3593]

def method3672 (packageName : String) : Result Unit := .error .other
def Property3672 : Prop := ∀ name, ∃ error, method3672 name = .error error
theorem property3672 : Property3672 := by intro; exact ⟨.other, rfl⟩

def method3679 (pkg : PackageId) : String := pkg.name
def Property3679 : Prop := ∀ pkg, method3679 pkg = pkg.name
theorem property3679 : Property3679 := by simp [Property3679, method3679]

def method3680 (render : α → String) (values : List α) : List String := values.map render
def Property3680 : Prop := ∀ (α : Type) render values,
  (method3680 (α := α) render values).length = values.length
theorem property3680 : Property3680 := by simp [Property3680, method3680]

def method3681 (renderKey : PackageId → String) (renderValue : α → String)
    (pair : PackageId × α) : String := renderKey pair.1 ++ "=>" ++ renderValue pair.2
def Property3681 : Prop := ∀ (α : Type) renderKey renderValue pair,
  (method3681 (α := α) renderKey renderValue pair).startsWith (renderKey pair.1) = true
theorem property3681 : Property3681 := by intro; simp [method3681]

def method3682 : String := "nothing"
def Property3682 : Prop := ∀ _ : Unit, method3682 = "nothing"
theorem property3682 : Property3682 := by intro; rfl

structure CacheCommand where
  outputJi : String
  outputObject : Option String
  options : List String
  environment : List (String × String)
  deriving Repr, DecidableEq
def method3688 (output : String) (object : Option String) (flags coverage : List String) : CacheCommand :=
  ⟨output, object, flags ++ coverage, [("OPENBLAS_NUM_THREADS", "1"), ("JULIA_NUM_THREADS", "1")]⟩
def Property3688 : Prop := ∀ output object flags coverage,
  (method3688 output object flags coverage).outputJi = output ∧
  ("JULIA_NUM_THREADS", "1") ∈ (method3688 output object flags coverage).environment
theorem property3688 : Property3688 := by simp [Property3688, method3688]

def method3772 (stack newPackages : List PackageId) : List PackageId := stack ++ newPackages
def Property3772 : Prop := ∀ stack packages,
  List.IsPrefix stack (method3772 stack packages)
theorem property3772 : Property3772 := by intro; simp [method3772]

def method3775 (stack : List PackageId) : List String := stack.map PackageId.name
def Property3775 : Prop := ∀ stack, (method3775 stack).length = stack.length
theorem property3775 : Property3775 := by simp [Property3775, method3775]

def method3782 (projectEmpty : Bool) (manifestId : Option String) : String :=
  if projectEmpty then "" else manifestId.getD ""
def Property3782 : Prop := ∀ empty id result,
  method3782 empty id = result → result = "" ∨ id = some result
theorem property3782 : Property3782 := by
  intro empty id result h; cases empty <;> cases id <;> simp_all [method3782]

def method3790 (depot entryPath : String) : String := depot ++ "/" ++ entryPath
def Property3790 : Prop := ∀ depot entry, (method3790 depot entry).startsWith depot = true
theorem property3790 : Property3790 := by intro; simp [method3790]

def method3795 (cacheDir entryFile : String) (uuidPresent : Bool) (slug : String) : String :=
  cacheDir ++ "/" ++ entryFile ++ (if uuidPresent then "_" ++ slug else "") ++ ".ji"
def Property3795 : Prop := ∀ cache entry uuid slug,
  ∃ pre, method3795 cache entry uuid slug = pre ++ ".ji"
theorem property3795 : Property3795 := by
  intro cache entry uuid slug
  exact ⟨cache ++ "/" ++ entry ++ (if uuid then "_" ++ slug else ""), rfl⟩

def method3831 (locate : Option LoadSpec) (compile : LoadSpec → α) : Result α :=
  match locate with | none => .error .argument | some spec => .ok (compile spec)
def Property3831 : Prop := ∀ (α : Type) locate compile result,
  method3831 (α := α) locate compile = .ok result → ∃ spec, locate = some spec ∧ result = compile spec
theorem property3831 : Property3831 := by
  intro α locate compile result h; cases locate <;> simp_all [method3831]

inductive CompileResult where | success (cache : String) (object : Option String) | disabled | failed
  deriving Repr, DecidableEq
def method3840 (processSuccess cacheObjects : Bool) (cache object : String) (exitCode : Int) : CompileResult :=
  if processSuccess then .success cache (if cacheObjects then some object else none)
  else if exitCode = 125 then .disabled else .failed
def Property3840 : Prop := ∀ success objects cache object code cachePath objectPath,
  method3840 success objects cache object code = .success cachePath objectPath →
  success = true ∧ cachePath = cache
theorem property3840 : Property3840 := by
  intro success objects cache object code cachePath objectPath h
  cases success <;> cases objects <;> simp_all [method3840]
  all_goals split at h <;> contradiction

def method4004 : Nat → (String → Bool) → String → String
  | 0, _, original => original
  | fuel + 1, isPresent, original => if isPresent original then method4004 fuel isPresent (original ++ "_1") else original
def Property4004 : Prop := ∀ fuel isPresent original,
  (method4004 fuel isPresent original).length ≥ original.length
theorem property4004 : Property4004 := by
  intro fuel
  induction fuel with
  | zero => simp [method4004]
  | succ fuel ih =>
      intro isPresent original
      simp [method4004]
      split
      · have next := ih isPresent (original ++ "_1")
        simp at next
        omega
      · simp

end JuliaLean.Loading.Coverage.Require

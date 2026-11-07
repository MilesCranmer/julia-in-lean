import JuliaLean.base.loading
import JuliaLean.Proofs.base.loading.retained.CoverageExtensions

namespace JuliaLean.Loading.Coverage.Require

open JuliaLean.Loading.Coverage
open JuliaLean.Loading.Coverage.Early
open JuliaLean.Loading.Coverage.Extensions
def Property2677 : Prop := ∀ includeFn path track,
  (method2677 includeFn path track).1 = (includeFn path track false).1
theorem property2677 : Property2677 := by simp [Property2677, method2677]
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
def Property2721 : Prop := ∀ identity table moduleId path mapexpr,
  identity = false → lookupAssoc (moduleId, path) (method2721 identity table moduleId path mapexpr) = some mapexpr
theorem property2721 : Property2721 := by
  intro identity table moduleId path mapexpr h
  subst identity
  simp [method2721, updateAssoc, lookupAssoc]
def Property2758 : Prop := ∀ (α : Type) defined (table : α),
  method2758 defined table = none ↔ defined = false
theorem property2758 : Property2758 := by
  intro α defined table
  cases defined <;> simp [method2758]
def Property2781 : Prop := ∀ includeFn path track, method2781 includeFn path track = includeFn path track
theorem property2781 : Property2781 := by simp [Property2781, method2781]
def Property2788 : Prop := ∀ stream, List.IsPrefix stream (method2788 stream)
theorem property2788 : Property2788 := by intro; simp [method2788]
def Property2791 : Prop := ∀ _ : Unit, method2791 = true
theorem property2791 : Property2791 := by intro; rfl
def Property2792 : Prop := ∀ inner, method2792 inner = inner
theorem property2792 : Property2792 := by simp [Property2792, method2792]
def Property2793 : Prop := ∀ (α : Type) (exception : α), method2793 exception = false
theorem property2793 : Property2793 := by simp [Property2793, method2793]
def Property2803 : Prop := ∀ precompilable generating,
  method2803 precompilable generating = .error .other ↔ precompilable = false ∧ generating = true
theorem property2803 : Property2803 := by
  intro precompilable generating; cases precompilable <;> cases generating <;> simp [method2803]
def Property2847 : Prop := ∀ (α : Type) stored current invoke,
  stored = 0 → method2847 (α := α) stored current invoke = invoke current
theorem property2847 : Property2847 := by
  intro α stored current invoke h
  subst stored
  simp [method2847]
def Property2855 : Prop := ∀ locallyDefined parent,
  (method2855 locallyDefined parent).1 = false ↔ locallyDefined = false ∧ parent = false
theorem property2855 : Property2855 := by
  intro locallyDefined parent; cases locallyDefined <;> cases parent <;> simp [method2855]
def Property2867 : Prop := ∀ outside precompile self top identified loaded,
  method2867 outside precompile self top identified loaded = .top top → self = true
theorem property2867 : Property2867 := by
  intro outside precompile self top identified loaded h
  cases outside <;> cases precompile <;> cases self <;> cases identified <;> simp_all [method2867]
def Property2919 : Prop := ∀ manifests path,
  path ∈ (method2919 manifests).1 → ∃ m ∈ manifests, m.path = path ∧ m.compatible = false
theorem property2919 : Property2919 := by
  intro manifests path h
  simp [method2919] at h
  rcases h with ⟨m, hm, hc, hp⟩
  exact ⟨m, hm, hp, hc⟩
def Property2948 : Prop := ∀ unsuitable dev path,
  path ∈ method2948 unsuitable dev → path ∈ unsuitable ∨ path ∈ dev
theorem property2948 : Property2948 := by
  intro unsuitable dev path h
  by_cases hu : unsuitable.isEmpty <;> by_cases hd : dev.isEmpty <;>
    simp_all [method2948]
def Property2970 : Prop := ∀ (α : Type) stored current invoke,
  stored = 0 → method2970 (α := α) stored current invoke = invoke current
theorem property2970 : Property2970 := by
  intro α stored current invoke h
  subst stored
  simp [method2970]
def Property2977 : Prop := ∀ (α : Type) set (result : α), (method2977 set result).1 = result
theorem property2977 : Property2977 := by simp [Property2977, method2977]
def Property2994 : Prop := ∀ (α : Type) track loaded (result : α),
  (method2994 track loaded result).1 = result
theorem property2994 : Property2994 := by simp [Property2994, method2994]
def Property3032 : Prop := ∀ _ : Unit,
  method3032.path = none ∧ method3032.cache = none ∧ method3032.version = none
theorem property3032 : Property3032 := by intro; exact ⟨rfl, rfl, rfl⟩
def Property3039 : Prop := ∀ (α : Type) pkgId module,
  method3039 (α := α) pkgId module = pkgId module
theorem property3039 : Property3039 := by simp [Property3039, method3039]
def Property3041 : Prop := ∀ modules build moduleId,
  method3041 modules build = some moduleId → (moduleId, build) ∈ modules
theorem property3041 : Property3041 := by
  intro modules build moduleId h
  induction modules with
  | nil => simp [method3041] at h
  | cons pair rest ih =>
      rcases pair with ⟨found, foundBuild⟩
      by_cases heq : foundBuild = build <;> simp_all [method3041, heq]
def Property3051 : Prop := ∀ high low, method3051 high low % 2 ^ 64 = low % 2 ^ 64
theorem property3051 : Property3051 := by
  intro; simp [method3051, Nat.add_mod]
def Property3056 : Prop := ∀ key moduleId build loaded,
  lookupAssoc key (method3056 key moduleId build loaded) = some moduleId
theorem property3056 : Property3056 := by simp [Property3056, method3056, updateAssoc, lookupAssoc]
def Property3079 : Prop := ∀ already register,
  method3079 already register = true → already = false
theorem property3079 : Property3079 := by
  intro already register h
  cases already <;> simp_all [method3079]
def Property3102 : Prop := ∀ lookup key moduleId,
  method3102 lookup key = .ok moduleId → lookup key = some moduleId
theorem property3102 : Property3102 := by
  intro lookup key moduleId h
  cases hl : lookup key <;> simp_all [method3102]
def Property3103 : Prop := ∀ (α : Type) identify root context name moduleId,
  method3103 (α := α) identify root context name = .ok moduleId →
  ∃ key, identify context name = some key ∧ root key = .ok moduleId
theorem property3103 : Property3103 := by
  intro α identify root context name moduleId h
  cases hi : identify context name <;> simp_all [method3103]
def Property3108 : Prop := ∀ contains key, method3108 contains key = true → contains key = true
theorem property3108 : Property3108 := by simp [Property3108, method3108]
def Property3109 : Prop := ∀ lookup key result,
  method3109 lookup key = some result → lookup key = some result
theorem property3109 : Property3109 := by simp [Property3109, method3109]
def Property3111 : Prop := ∀ order, (method3111 order).length = order.length
theorem property3111 : Property3111 := by simp [Property3111, method3111]
def Property3115 : Prop := ∀ loaded key, lookupAssoc key (method3115 loaded key) = none
theorem property3115 : Property3115 := by simp [Property3115, method3115, lookupAssoc]
def Property3126 : Prop := ∀ origin path version generating,
  (method3126 origin path version generating).path = some path
theorem property3126 : Property3126 := by simp [Property3126, method3126]

def PrecompiledSelectionContract : Prop :=
  (∀ images objectPath, selectPrecompiled none images objectPath = .serial) ∧
  (∀ images objectPath, selectPrecompiled (some []) images objectPath = .precompilableError) ∧
  (∀ rest images objectPath, selectPrecompiled (some (.other :: rest)) images objectPath = .typeError) ∧
  (∀ path rest objectPath,
    selectPrecompiled (some (.string path :: rest)) false objectPath = .selected path none) ∧
  (∀ path rest objectPath object, objectPath path = .ok object →
    selectPrecompiled (some (.string path :: rest)) true objectPath = .selected path (some object)) ∧
  (∀ path rest objectPath err, objectPath path = .error err →
    selectPrecompiled (some (.string path :: rest)) true objectPath = .objectPathError err)
theorem precompiledSelectionContract_proven : PrecompiledSelectionContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro path rest objectPath object h
    simp [selectPrecompiled, h]
  · intro path rest objectPath err h
    simp [selectPrecompiled, h]

/-- The `finally` block reacquires the lock and resets the parser even when
the included code throws. The old UUID is restored when the loader changed it. -/
theorem requireSource_cleanup (packageUuid edition defaultEdition : Nat)
    (includeSource : RequireSourceState → Except String (Option Nat) × RequireSourceState)
    (initial : RequireSourceState) :
    (requireSource packageUuid edition defaultEdition includeSource initial).2.locked = true ∧
    (requireSource packageUuid edition defaultEdition includeSource initial).2.parserEdition = defaultEdition ∧
    (packageUuid ≠ initial.uuid →
      (requireSource packageUuid edition defaultEdition includeSource initial).2.uuid = initial.uuid) := by
  simp [requireSource]
  intros h h'
  exact False.elim (h h')
def Property3140 : Prop := ∀ located cache source moduleId,
  method3140 located cache source = .loaded moduleId → located.isSome
theorem property3140 : Property3140 := by
  intro located cache source moduleId h
  cases located <;> simp_all [method3140]
def Property3305 : Prop := ∀ loaded, method3305 loaded = loaded
theorem property3305 : Property3305 := by simp [Property3305, method3305]
def Property3367 : Prop := ∀ require pkg, method3367 require pkg = require pkg none 0
theorem property3367 : Property3367 := by simp [Property3367, method3367]
def Property3368 : Prop := ∀ source cache result,
  method3368 source cache = some result → cache = some result ∨ source = some result
theorem property3368 : Property3368 := by
  intro source cache result h; cases cache <;> cases source <;> simp_all [method3368, choose]
def Property3421 : Prop := ∀ override cli result,
  method3421 override cli = some result → override = some result ∨ cli = some result
theorem property3421 : Property3421 := by
  intro override cli result h; cases override <;> cases cli <;> simp_all [method3421, choose]
def Property3444 : Prop := ∀ (α : Type) parse code filename result,
  method3444 (α := α) parse code filename = result → parse code filename = result
theorem property3444 : Property3444 := by simp [Property3444, method3444]
def Property3472 : Prop := ∀ (α : Type) includeString moduleId text filename,
  method3472 (α := α) includeString moduleId text filename = includeString moduleId text filename
theorem property3472 : Property3472 := by simp [Property3472, method3472]
def Property3475 : Prop := ∀ tls default result,
  method3475 tls default = some result → tls = some result ∨ default = some result
theorem property3475 : Property3475 := by
  intro tls default result h; cases tls <;> cases default <;> simp_all [method3475, choose]
def Property3486 : Prop := ∀ path dirname result,
  method3486 path dirname = some result → ∃ source, path = some source ∧ result = dirname source
theorem property3486 : Property3486 := by
  intro path dirname result h; cases path <;> simp_all [method3486]
def Property3512 : Prop := ∀ (α : Type) record evaluate path,
  method3512 (α := α) record evaluate path = evaluate path
theorem property3512 : Property3512 := by simp [Property3512, method3512]
def Property3559 : Prop := ∀ (α : Type) oldArgs newArgs evaluate,
  (method3559 (α := α) oldArgs newArgs evaluate).2 = oldArgs
theorem property3559 : Property3559 := by simp [Property3559, method3559]
def Property3568 : Prop := ∀ (α β : Type) convert evaluate args error,
  convert args = .error error → method3568 (α := α) (β := β) convert evaluate args = .error error
theorem property3568 : Property3568 := by
  intro α β convert evaluate args error h
  simp [method3568, h]
def Property3570 : Prop := ∀ setup active load depot dl,
  ("depot", depot) ∈ method3570 setup active load depot dl
theorem property3570 : Property3570 := by intro; simp [method3570]
def Property3593 : Prop := ∀ depot dl load concrete source,
  (method3593 depot dl load concrete source).concrete = concrete
theorem property3593 : Property3593 := by simp [Property3593, method3593]
def Property3672 : Prop := ∀ name, ∃ error, method3672 name = .error error
theorem property3672 : Property3672 := by intro; exact ⟨.other, rfl⟩
def Property3679 : Prop := ∀ pkg, method3679 pkg = pkg.name
theorem property3679 : Property3679 := by simp [Property3679, method3679]
def Property3680 : Prop := ∀ (α : Type) render values,
  (method3680 (α := α) render values).length = values.length
theorem property3680 : Property3680 := by simp [Property3680, method3680]
def Property3681 : Prop := ∀ (α : Type) renderKey renderValue pair,
  (method3681 (α := α) renderKey renderValue pair).startsWith (renderKey pair.1) = true
theorem property3681 : Property3681 := by intro; simp [method3681]
def Property3682 : Prop := ∀ _ : Unit, method3682 = "nothing"
theorem property3682 : Property3682 := by intro; rfl
def Property3688 : Prop := ∀ output object flags coverage,
  (method3688 output object flags coverage).outputJi = output ∧
  ("JULIA_NUM_THREADS", "1") ∈ (method3688 output object flags coverage).environment
theorem property3688 : Property3688 := by simp [Property3688, method3688]
def Property3772 : Prop := ∀ stack packages,
  List.IsPrefix stack (method3772 stack packages)
theorem property3772 : Property3772 := by intro; simp [method3772]
def Property3775 : Prop := ∀ stack, (method3775 stack).length = stack.length
theorem property3775 : Property3775 := by simp [Property3775, method3775]
def Property3782 : Prop := ∀ empty id result,
  method3782 empty id = result → result = "" ∨ id = some result
theorem property3782 : Property3782 := by
  intro empty id result h; cases empty <;> cases id <;> simp_all [method3782]
def Property3790 : Prop := ∀ depot entry, (method3790 depot entry).startsWith depot = true
theorem property3790 : Property3790 := by intro; simp [method3790]
def Property3795 : Prop := ∀ cache entry uuid slug,
  ∃ pre, method3795 cache entry uuid slug = pre ++ ".ji"
theorem property3795 : Property3795 := by
  intro cache entry uuid slug
  exact ⟨cache ++ "/" ++ entry ++ (if uuid then "_" ++ slug else ""), rfl⟩
def Property3831 : Prop := ∀ (α : Type) locate compile result,
  method3831 (α := α) locate compile = .ok result → ∃ spec, locate = some spec ∧ result = compile spec
theorem property3831 : Property3831 := by
  intro α locate compile result h; cases locate <;> simp_all [method3831]
def Property3840 : Prop := ∀ success objects cache object code cachePath objectPath,
  method3840 success objects cache object code = .success cachePath objectPath →
  success = true ∧ cachePath = cache
theorem property3840 : Property3840 := by
  intro success objects cache object code cachePath objectPath h
  cases success <;> cases objects <;> simp_all [method3840]
  all_goals split at h <;> contradiction
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
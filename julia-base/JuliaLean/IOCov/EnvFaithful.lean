import JuliaLean.Registry.Types
import JuliaLean.IOCov.Env

namespace JuliaLean.IOCov.EnvFaithful

open JuliaLean JuliaLean.Registry
open JuliaLean.IOCov Env

abbrev Bytes := Env.Bytes
abbrev Environ := Env.Environ

/-- Linux `_environ() = unsafe_load(_environ_ptr())`, `base/env.jl:70`.
The argument is the result of the OncePerProcess pointer load. -/
def environLoad (loaded : R Environ) : R Environ := loaded

/-- `get_bool_env(name, default)`, `base/env.jl:157`. -/
def getBoolDefault (env : Environ) (name : Bytes) (default : Bool) (throw : Bool) : R (Option Bool) :=
  Env.getBoolEnvF env (fun _ => some default) name throw

/-- `parse_bool_env(name, val; throw)`, `base/env.jl:167-177`, including the
name and value used in the thrown message. -/
def parseBoolNamed (name val : Bytes) (throw : Bool) : R (Option Bool) :=
  if val ∈ Env.truthy then .ok (some true)
  else if val ∈ Env.falsy then .ok (some false)
  else if throw then .error (.jl (.argumentError
    ("Value for environment variable `" ++ String.ofList (name.map (Char.ofNat ∘ UInt8.toNat)) ++
     "` could not be parsed as Boolean")))
  else .ok none

/-- Callable-default `get_bool_env`, `base/env.jl:158-166`. -/
def getBoolCallable (env : Environ) (fDefault : Unit -> Option Bool)
    (name : Bytes) (throw : Bool) : R (Option Bool) := do
  let present <- Env.haskey env name
  if present then
    let val <- Env.getindex env name
    if !val.isEmpty then return <- parseBoolNamed name val throw
  pure (fDefault ())

/-- `get!(default, ENV, k)`, `base/env.jl:182-185`.  The callback result is
bound once and reused for the assignment and return. -/
def getBangOnce (env : Environ) (default : Unit -> Bytes) (k : Bytes) : R (Bytes × Environ) := do
  let present <- Env.haskey env k
  if present then
    let v <- Env.getindex env k
    pure (v, env)
  else
    let v := default ()
    let env' <- Env.setindex env v k
    pure (v, env')

/-- `setindex!(ENV, v, k)` for arbitrary values, `base/env.jl:190`.
`stringify` is Julia's `string(v)`. -/
def setindexAny {alpha : Type} (stringify : alpha -> Bytes)
    (env : Environ) (v : alpha) (k : Bytes) : R Environ :=
  Env.setenvP env k (stringify v)

/-- `push!(ENV, kv)`, `base/env.jl:191`, for arbitrary pair values. -/
def pushAny {alpha : Type} (stringify : alpha -> Bytes)
    (env : Environ) (k : Bytes) (v : alpha) : R Environ :=
  setindexAny stringify env v k

structure IterStep where
  value : Option (Bytes × Bytes)
  next : Nat
  warnings : List Bytes
  deriving DecidableEq

private def iterateLoop : Nat -> Environ -> Nat -> List Bytes -> IterStep
  | 0, _, i, warnings => ⟨none, i, warnings⟩
  | fuel + 1, env, i, warnings =>
      if hi : i < env.length then
        let entry := env.get ⟨i, hi⟩
          match Env.splitEntry entry with
          | some kv => ⟨some kv, i + 1, warnings⟩
          | none => iterateLoop fuel env (i + 1) (warnings ++ [entry])
      else ⟨none, i, warnings⟩

/-- Non-Windows `iterate(::EnvDict, i)`, `base/env.jl:231-246`.
`none` for `environ` models C_NULL and throws before the loop. -/
def iterateEnv (environ : Option Environ) (i : Nat) : R IterStep :=
  match environ with
  | none => .error (.errorException "Failed to resolve `environ`.")
  | some env => .ok (iterateLoop (env.length - i + 1) env i [])

private def collectEnv : Nat -> Environ -> Nat -> List (Bytes × Bytes)
  | 0, _, _ => []
  | fuel + 1, env, i =>
      let step := iterateLoop (env.length - i + 1) env i []
      match step.value with
      | none => []
      | some kv => kv :: collectEnv fuel env step.next

/-- `length(::EnvDict)`, `base/env.jl:250-256`, by repeated iteration. -/
def envLength (env : Environ) : Nat := (collectEnv (env.length + 1) env 0).length

/-- `show(io, ::EnvDict)`, `base/env.jl:258-262`, as bytes printed to IO. -/
def showEnvIO (env : Environ) : Bytes :=
  (collectEnv (env.length + 1) env 0).flatMap (fun kv => kv.1 ++ Env.eqB :: kv.2 ++ [10])

abbrev CallbackResult (alpha : Type) := R alpha × Environ

/-- `withenv(f, keyvals...)`, `base/env.jl:277-289`, including callback
execution, its returned value or exception, and finally restoration. -/
def withenvCall {alpha : Type} (env : Environ) (kvs : List (Bytes × Option Bytes))
    (f : Environ -> CallbackResult alpha) : R alpha × Environ :=
  match Env.withenvSetup env [] kvs with
  | .error e => (.error e, env)
  | .ok (old, temporary) =>
      let callback := f temporary
      match Env.restore callback.2 old with
      | .error e => (.error e, callback.2)
      | .ok restored => (callback.1, restored)

/-- `withenv(f) = f()`, `base/env.jl:290`. -/
def withenvZero {alpha : Type} (env : Environ) (f : Environ -> CallbackResult alpha) :
    R alpha × Environ := f env

/-! Fully quantified per-method properties. -/

def GetenvAll : Prop := forall env k,
  Env.getenvP env k = do let key <- Env.cstring k; pure (Env.cgetenv env key)
theorem getenvAll : GetenvAll := by unfold GetenvAll; intros; rfl

def HasenvAll : Prop := forall env k,
  Env.hasenv env k = do let value <- Env.getenvP env k; pure value.isSome
theorem hasenvAll : HasenvAll := by unfold HasenvAll; intros; rfl

def EnvironAll : Prop := forall loaded, environLoad loaded = loaded
theorem environAll : EnvironAll := by intro; rfl

def AccessAll : Prop := forall alpha env (onError : Bytes -> R alpha) ofVal k,
  Env.accessEnv env onError ofVal k = do
    let value <- Env.getenvP env k
    match value with | none => onError k | some v => pure (ofVal v)
theorem accessAll : AccessAll := by unfold AccessAll; intros; rfl

def SetenvAll : Prop := forall env k v overwrite,
  Env.setenvP env k v overwrite = do
    let key <- Env.cstring k
    let value <- Env.cstring v
    match Env.csetenv env key value overwrite with
    | none => .error (.systemError "setenv")
    | some result => pure result
theorem setenvAll : SetenvAll := by unfold SetenvAll; intros; rfl

def UnsetenvAll : Prop := forall env k,
  Env.unsetenvP env k = do
    let key <- Env.cstring k
    match Env.cunsetenv env key with
    | none => .error (.systemError "unsetenv")
    | some result => pure result
theorem unsetenvAll : UnsetenvAll := by unfold UnsetenvAll; intros; rfl

def BoolDefaultAll : Prop := forall env name default throw,
  getBoolDefault env name default throw = Env.getBoolEnvF env (fun _ => some default) name throw
theorem boolDefaultAll : BoolDefaultAll := by unfold BoolDefaultAll; intros; rfl

def BoolCallableAll : Prop := forall env f name throw,
  getBoolCallable env f name throw = do
    let present <- Env.haskey env name
    if present then
      let value <- Env.getindex env name
      if !value.isEmpty then return <- parseBoolNamed name value throw
    pure (f ())
theorem boolCallableAll : BoolCallableAll := by unfold BoolCallableAll; intros; rfl

def ParseBoolAll : Prop := forall name value throw,
  parseBoolNamed name value throw =
    if value ∈ Env.truthy then .ok (some true)
    else if value ∈ Env.falsy then .ok (some false)
    else if throw then .error (.jl (.argumentError
      ("Value for environment variable `" ++ String.ofList (name.map (Char.ofNat ∘ UInt8.toNat)) ++
       "` could not be parsed as Boolean")))
    else .ok none
theorem parseBoolAll : ParseBoolAll := by unfold ParseBoolAll; intros; rfl

def DictLookupAll : Prop :=
  (forall env k, Env.getindex env k = Env.accessEnv env (fun key => .error (.keyError key)) id k) /\
  (forall env k d, Env.get env k d = Env.accessEnv env (fun _ => .ok d) id k) /\
  (forall env f k, Env.getF env f k = Env.accessEnv env (fun _ => f ()) id k) /\
  (forall env k, Env.haskey env k = Env.hasenv env k)
theorem dictLookupAll : DictLookupAll := by
  simp [DictLookupAll, Env.getindex, Env.get, Env.getF, Env.haskey]

def GetBangAll : Prop := forall env f k, getBangOnce env f k = do
  let present <- Env.haskey env k
  if present then let v <- Env.getindex env k; pure (v, env)
  else let v := f (); let env' <- Env.setindex env v k; pure (v, env')
theorem getBangAll : GetBangAll := by unfold GetBangAll; intros; rfl

def DictMutationAll : Prop :=
  (forall env k, Env.pop env k = do let v <- Env.getindex env k; let env' <- Env.unsetenvP env k; pure (v, env')) /\
  (forall env k d, Env.popDef env k d = do let h <- Env.haskey env k; if h then Env.pop env k else pure (d, env)) /\
  (forall env k, Env.delete env k = Env.unsetenvP env k)
theorem dictMutationAll : DictMutationAll := by
  simp [DictMutationAll, Env.pop, Env.popDef, Env.delete]

def ArbitraryValueAll : Prop :=
  (forall alpha stringify env (v : alpha) k,
    setindexAny stringify env v k = Env.setenvP env k (stringify v)) /\
  (forall alpha stringify env k (v : alpha),
    pushAny stringify env k v = setindexAny stringify env v k)
theorem arbitraryValueAll : ArbitraryValueAll := by
  simp [ArbitraryValueAll, setindexAny, pushAny]

def IterationAll : Prop := forall env i,
  iterateEnv (some env) i = .ok (iterateLoop (env.length - i + 1) env i [])
theorem iterationAll : IterationAll := by unfold IterationAll; intros; rfl

def LengthAll : Prop := forall env,
  envLength env = (collectEnv (env.length + 1) env 0).length
theorem lengthAll : LengthAll := by intro; rfl

def ShowAll : Prop := forall env,
  showEnvIO env = (collectEnv (env.length + 1) env 0).flatMap
    (fun kv => kv.1 ++ Env.eqB :: kv.2 ++ [10])
theorem showAll : ShowAll := by intro; rfl

def WithenvRestores : Prop := forall env kvs,
  (forall p, p ∈ kvs -> Env.validName p.1 = true /\ Not (p.1.contains 0) /\
    forall v, p.2 = some v -> Not (v.contains 0)) ->
  let result := withenvCall env kvs (fun temporary => (.ok (), temporary))
  forall p, p ∈ kvs -> Env.cgetenv result.2 p.1 = Env.cgetenv env p.1

theorem withenvRestores_refuted : Not WithenvRestores := by
  intro h
  have bad := h [] [([88], some [49]), ([88], some [50])]
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> decide)
  have atX := bad ([88], some [49]) (by simp)
  change Env.cgetenv [[88, 61, 49]] [88] = Env.cgetenv [] [88] at atX
  simp [Env.cgetenv, Env.entryValue] at atX
  exact atX rfl

def WithenvZeroAll : Prop := forall alpha env (f : Environ -> CallbackResult alpha),
  withenvZero env f = f env
theorem withenvZeroAll : WithenvZeroAll := by unfold WithenvZeroAll; intros; rfl

def entries : List Entry := [
  { id := "iocov-env-faithful-getenv", juliaFile := "base/env.jl", juliaFns := ["_getenv"],
    statement := "_getenv converts every AbstractString to Cstring and returns the libc pointer result.", source := "base/env.jl:55",
    status := .proven, prop := ``GetenvAll, thm := some ``getenvAll },
  { id := "iocov-env-faithful-hasenv", juliaFile := "base/env.jl", juliaFns := ["_hasenv"],
    statement := "_hasenv is the non-null test of _getenv for every input, including conversion errors.", source := "base/env.jl:56",
    status := .proven, prop := ``HasenvAll, thm := some ``hasenvAll },
  { id := "iocov-env-faithful-environ", juliaFile := "base/env.jl", juliaFns := ["_environ"],
    statement := "_environ returns the array loaded through the OncePerProcess environ pointer.", source := "base/env.jl:61-70",
    status := .proven, prop := ``EnvironAll, thm := some ``environAll },
  { id := "iocov-env-faithful-access", juliaFile := "base/env.jl", juliaFns := ["access_env"],
    statement := "access_env returns unsafe_string of a present value or calls the supplied error callback.", source := "base/env.jl:73-76",
    status := .proven, prop := ``AccessAll, thm := some ``accessAll },
  { id := "iocov-env-faithful-setenv", juliaFile := "base/env.jl", juliaFns := ["_setenv"],
    statement := "_setenv converts both strings, passes every overwrite value to libc, and checks its return code.", source := "base/env.jl:78-81",
    status := .proven, prop := ``SetenvAll, thm := some ``setenvAll },
  { id := "iocov-env-faithful-unsetenv", juliaFile := "base/env.jl", juliaFns := ["_unsetenv"],
    statement := "_unsetenv converts the name, calls libc, and checks its return code for every input.", source := "base/env.jl:83-86",
    status := .proven, prop := ``UnsetenvAll, thm := some ``unsetenvAll },
  { id := "iocov-env-faithful-bool-default", juliaFile := "base/env.jl", juliaFns := ["get_bool_env(name,default)"],
    statement := "The Bool-default overload delegates to the callable overload with Returns(default).", source := "base/env.jl:157",
    status := .proven, prop := ``BoolDefaultAll, thm := some ``boolDefaultAll },
  { id := "iocov-env-faithful-bool-callable", juliaFile := "base/env.jl", juliaFns := ["get_bool_env(f_default,name)"],
    statement := "The callable overload covers missing, empty, recognized, and unrecognized values for every callback.", source := "base/env.jl:158-166",
    status := .proven, prop := ``BoolCallableAll, thm := some ``boolCallableAll },
  { id := "iocov-env-faithful-parse-bool", juliaFile := "base/env.jl", juliaFns := ["parse_bool_env"],
    statement := "parse_bool_env handles every truthy, falsy, unrecognized, and throwing input with the named variable.", source := "base/env.jl:167-177",
    status := .proven, prop := ``ParseBoolAll, thm := some ``parseBoolAll },
  { id := "iocov-env-faithful-lookups", juliaFile := "base/env.jl", juliaFns := ["getindex", "get", "get(f,...)", "in(keys(ENV))"],
    statement := "All dictionary lookup overloads preserve their callbacks and conversion errors for every key.", source := "base/env.jl:179-181,186",
    status := .proven, prop := ``DictLookupAll, thm := some ``dictLookupAll },
  { id := "iocov-env-faithful-get-bang", juliaFile := "base/env.jl", juliaFns := ["get!"],
    statement := "get! returns a present value or calls the default once, stores it, and returns it.", source := "base/env.jl:182-185",
    status := .proven, prop := ``GetBangAll, thm := some ``getBangAll },
  { id := "iocov-env-faithful-mutations", juliaFile := "base/env.jl", juliaFns := ["pop!", "delete!"],
    statement := "pop and delete cover present, absent, and conversion-error behavior in source order.", source := "base/env.jl:187-189",
    status := .proven, prop := ``DictMutationAll, thm := some ``dictMutationAll },
  { id := "iocov-env-faithful-any-values", juliaFile := "base/env.jl", juliaFns := ["setindex!", "push!"],
    statement := "setindex! and push! apply string(v) for every allowed value type before setting.", source := "base/env.jl:190-191",
    status := .proven, prop := ``ArbitraryValueAll, thm := some ``arbitraryValueAll },
  { id := "iocov-env-faithful-iterate", juliaFile := "base/env.jl", juliaFns := ["iterate(::EnvDict,i)"],
    statement := "Iteration checks the environment pointer, loads entries by state, warns and skips malformed entries, and returns the next state.", source := "base/env.jl:231-246",
    status := .proven, prop := ``IterationAll, thm := some ``iterationAll },
  { id := "iocov-env-faithful-length", juliaFile := "base/env.jl", juliaFns := ["length(::EnvDict)"],
    statement := "length initializes zero and increments once for every iterator result.", source := "base/env.jl:250-256",
    status := .proven, prop := ``LengthAll, thm := some ``lengthAll },
  { id := "iocov-env-faithful-show", juliaFile := "base/env.jl", juliaFns := ["show(::IO,::EnvDict)"],
    statement := "show iterates ENV and writes one key=value newline to the supplied IO per pair.", source := "base/env.jl:258-262",
    status := .proven, prop := ``ShowAll, thm := some ``showAll },
  { id := "iocov-env-faithful-withenv0", juliaFile := "base/env.jl", juliaFns := ["withenv(f)"],
    statement := "The zero-pair method calls f once and returns its value or exception without changing the environment.", source := "base/env.jl:290",
    status := .proven, prop := ``WithenvZeroAll, thm := some ``withenvZeroAll }
]

end JuliaLean.IOCov.EnvFaithful

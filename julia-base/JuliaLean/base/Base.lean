import JuliaLean.Core

namespace JuliaLean.MiscCov.BaseJl

variable {V T : Type}
/-- `(P::Type{Pair{A,B}})(a, b)`: each field is the argument itself when it already
has the field type and `convert(A, a)` otherwise; a conversion error propagates.
`isa v t` is `v isa t` and `convert t v` is `convert(t, v)`. -/
def pairNew (isa : V → T → Bool) (convert : T → V → M V) (A B : T) (a b : V) : M (V × V) := do
  let x <- if isa a A then pure a else convert A a
  let y <- if isa b B then pure b else convert B b
  pure (x, y)


/-! ## Small methods, `base/Base.jl:46-57,87,135-137,350-363` -/

/-- A `Memory{UInt8}`: its length and whether its data lives in a `String`
(`jl_genericmemory_owner(mem)` is then that string, otherwise `mem` itself). -/
structure Mem where
  len : Nat
  stringBacked : Bool
  deriving DecidableEq, Repr

/-- `jl_genericmemory_owner(mem) === mem`. -/
def ownsItself (m : Mem) : Bool := !m.stringBacked

/-- `array_new_memory(mem, newlen)`, `base/Base.jl:46-57`: a fresh
`typeof(mem)(undef, newlen)` when `mem` owns its data, otherwise the memory of a
fresh string of `newlen` bytes (`_string_n`, `jl_string_to_genericmemory`). -/
def arrayNewMemory (mem : Mem) (newlen : Nat) : Mem :=
  if ownsItself mem then { len := newlen, stringBacked := false }
  else { len := newlen, stringBacked := true }

/-- `sizeof(s::String) = Core.sizeof(s)`, `base/Base.jl:87`: the number of bytes. -/
def sizeofString (s : List UInt8) : Nat := s.length

/-- `isdebugbuild()`, `base/Base.jl:135-137`: `ccall(:jl_is_debugbuild, Cint, ()) != 0`. -/
def isdebugbuild (cFlag : Int) : Bool := cFlag != 0

/-- `a_method_to_overwrite_in_test() = inferencebarrier(1)`, `base/Base.jl:350`. -/
def aMethodToOverwriteInTest : Int := 1

/-- `include(mod, path)` and `include(mapexpr, mod, path)`, `base/Base.jl:354-355`,
and the two `IncludeInto` call methods, `base/Base.jl:356-357`: all four call
`_include(mapexpr, mod, path)`; `none` stands for `identity`. -/
def include1 {Mod R : Type} (inc : Option String → Mod → String → R) (mod : Mod) (p : String) : R :=
  inc none mod p
def include2 {Mod R : Type} (inc : Option String → Mod → String → R) (mapexpr : String) (mod : Mod)
    (p : String) : R := inc (some mapexpr) mod p
def includeInto1 {Mod R : Type} (inc : Option String → Mod → String → R) (m : Mod) (fname : String) : R :=
  include1 inc m fname
def includeInto2 {Mod R : Type} (inc : Option String → Mod → String → R) (m : Mod) (mapexpr fname : String) : R :=
  include2 inc mapexpr m fname

/-- `in_sysimage(pkgid) = pkgid in _sysimage_modules`, `base/Base.jl:363`. -/
def inSysimage (sysimage : List String) (pkgid : String) : Bool := sysimage.contains pkgid


/-! ## The ^C episode machinery, `base/Base.jl:409-589` -/

/-- Observable effects, in order. -/
inductive Ev where
  | cancel (src : Nat)
  | redeliver (src : Nat)
  | exit (code : Nat)
  | showError
  | spawn (pool : String)
  | atexit
  | finalizer
  | setCond (handle : Option Nat)
  | close
  | wait (task : Nat)
  | requireProfile
  | peekReport
  | heapSnapshot
  | logError
  deriving DecidableEq, Repr

/-- The state the ^C machinery reads and writes: the episode Ref
(`_sigint_episode`), the foreground task Ref, the C-side generation counter,
mirrored source and pending-press generation (`0` = none), the dispatch flag,
the cancellation severity of each source, `sigint_pass_lock`, the REPL backend
(`none` = `active_repl_backend === nothing`, otherwise whether its task is done)
and whether the root task is done. -/
structure St where
  episode : Option Nat × Nat
  foreground : Option Nat
  cGen : Nat
  cSource : Option Nat
  pendingGen : Nat
  dispatchPending : Bool
  severity : Nat → Option Nat
  locked : Bool
  backendDone : Option Bool
  rootDone : Bool
  log : List Ev

/-- `ccall(:jl_set_sigint_source, UInt64, (Any,), src)`, `src/signal-handling.c:526-545`. -/
def setSigintSource (s : St) (src : Option Nat) : St × Nat :=
  ({ s with cGen := s.cGen + 2, cSource := src }, s.cGen + 2)

/-- `sigint_new_episode!(src)`, `base/Base.jl:445-454`; returns the token's source. -/
def sigintNewEpisode (s : St) (cur src : Nat) : St × Nat :=
  let s := { s with foreground := some cur }
  let (s, gen) := setSigintSource s (some src)
  ({ s with episode := (some src, gen) }, src)

/-- `sigint_close_episode!()`, `base/Base.jl:459-464`. -/
def sigintCloseEpisode (s : St) : St :=
  let (s, gen) := setSigintSource s none
  { s with episode := (none, gen), foreground := none }

/-- `sigint_active_severity(src) = cancel_severity(src)`, `base/Base.jl:468`. -/
def sigintActiveSeverity (s : St) (src : Nat) : Option Nat := s.severity src

/-- `jl_consume_sigint_pending(gen)`, `src/signal-handling.c:550-556`. -/
def consumePending (s : St) (gen : Nat) : St × Bool :=
  if s.pendingGen = 0 ∨ s.pendingGen ≠ gen then (s, false) else ({ s with pendingGen := 0 }, true)

/-- `CANCEL_REQUEST_SAFE`, the severity `cancel!` marks. -/
def cancelSafe : Nat := 1

/-- `cancel!(src, CANCEL_REQUEST_SAFE)` on an unmarked source: mark it and log. -/
def cancel (s : St) (src : Nat) : St :=
  { s with severity := fun k => if k = src then some cancelSafe else s.severity k,
           log := s.log ++ [.cancel src] }

/-- `_sigint_dispatch_pass()`, `base/Base.jl:480-517`. -/
def dispatchPass (s : St) : St :=
  let (src, gen) := s.episode
  let (s, pending) := consumePending s gen
  match src with
  | none =>
    if !pending then s
    else match s.backendDone with
      | some false => s
      | _ => if !s.rootDone then s else { s with log := s.log ++ [.exit (128 + 2)] }
  | some src =>
    if sigintActiveSeverity s src = none then
      if !pending then s else cancel s src
    else if pending then { s with log := s.log ++ [.redeliver src] }
    else s

/-- The `while` loop of `maybe_dispatch_sigint`, `base/Base.jl:532-541`: each
`jl_claim_sigint_dispatch()` exchanges the flag with `0`. -/
def claimLoop : Nat → St → St
  | 0, s => s
  | n+1, s => if s.dispatchPending then claimLoop n (dispatchPass { s with dispatchPending := false }) else s

/-- `maybe_dispatch_sigint()`, `base/Base.jl:527-546`. -/
def maybeDispatchSigint (s : St) : St :=
  if !s.dispatchPending then s
  else if s.locked then s
  else { claimLoop 2 { s with locked := true } with locked := false }

/-- `sigint_listener(cond)`, `base/Base.jl:548-553`: one pass per wake-up, until
`_trywait` returns `false`. -/
def sigintListener (wakes : List Bool) (s : St) : St :=
  match wakes with
  | true :: w => sigintListener w (maybeDispatchSigint s)
  | _ => s


/-! ## Listener start-up, `base/Base.jl:370-407,563-589` -/

/-- `start_sigint_listener()`, `base/Base.jl:563-589`, given the size of the
interactive threadpool and the handle of the new `AsyncCondition`: the spawned
listener pools, then the `atexit` hook, the finalizer and the C registration. -/
def startSigintListener (interactive : Nat) (handle : Nat) : List Ev :=
  (if interactive > 0 then [Ev.spawn "interactive"] else []) ++
  [.spawn "default", .atexit, .finalizer, .setCond (some handle)]

/-- The `atexit` hook of `start_sigint_listener`: unregister, close, wait for every
listener that is not the current task. -/
def sigintAtexit (listeners : List Nat) (current : Nat) : List Ev :=
  [.setCond none, .close] ++ (listeners.filter (· ≠ current)).map Ev.wait

/-- `start_profile_listener()`, `base/Base.jl:390-407` (the `uv_unref` is not an
observable effect of the model). -/
def startProfileListener (handle : Nat) : List Ev :=
  [.spawn "default", .atexit, .finalizer, .setCond (some handle)]

/-- `profile_printing_listener(cond)`, `base/Base.jl:370-388`: `wakes` is the
sequence of `_trywait` results; `snapshot` the value of
`get_bool_env("JULIA_PROFILE_PEEK_HEAP_SNAPSHOT", false)`, `none` if it throws (the
error is caught and logged). -/
def profileLoop (snapshot : Option Bool) : List Bool → Bool → List Ev
  | true :: w, loaded =>
    (if loaded then [] else [Ev.requireProfile]) ++ [.peekReport] ++
    (match snapshot with
     | none => [.logError]
     | some true => [.heapSnapshot] ++ profileLoop snapshot w true
     | some false => profileLoop snapshot w true)
  | _, _ => []

def profilePrintingListener (snapshot : Option Bool) (wakes : List Bool) : List Ev :=
  profileLoop snapshot wakes false




/-! ## `__init__`, `base/Base.jl:591-623` -/

/-- The parts of `Base.__init__()` that compute state: `_sysimage_modules` becomes
the keys of `loaded_modules`, `loaded_precompiles` (emptied first) maps each package
of `loaded_modules_order` to its modules in order, and `MAX_NUM_PRECOMPILE_FILES[]` is
`parse(Int, ENV["JULIA_MAX_NUM_PRECOMPILE_FILES"])` when that variable is set
(`parseInt` is `parse(Int, _)`). Modules are given as `(pkgid, module)` pairs; the
`loaded_precompiles` dictionary is a function from package to module vector. The
remaining calls of `__init__` (stdio, load paths, listeners, logger, frontend) are
the runtime's and not modelled. -/
structure InitOut where
  sysimage : List String
  precompiles : String → List Nat
  maxFiles : Option Int

/-- `push!(get!(Vector{Module}, loaded_precompiles, PkgId(mod)), mod)`. -/
def pushPrecompile (d : String → List Nat) (p : String × Nat) : String → List Nat :=
  fun k => if k = p.1 then d k ++ [p.2] else d k

def baseInit (parseInt : String → M Int) (loadedKeys : List String) (order : List (String × Nat))
    (env : Option String) (maxFiles : Option Int) : M InitOut := do
  let pre := order.foldl pushPrecompile (fun _ => [])
  let mf <- match env with
    | some v => do let n <- parseInt v; pure (some n)
    | none => pure maxFiles
  pure { sysimage := loadedKeys, precompiles := pre, maxFiles := mf }

end JuliaLean.MiscCov.BaseJl

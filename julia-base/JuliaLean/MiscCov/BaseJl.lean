import JuliaLean.MiscCov.Basic

/-!
# `base/Base.jl` and `base/download.jl` (master `bbfa0ce4150`)

The runtime effects of these methods (C calls, task spawns, `atexit` hooks,
package loading) are recorded as an ordered event log; values the runtime
supplies (C return values, the results of `require`, environment variables) are
inputs of the model.
-/

namespace JuliaLean.MiscCov.BaseJl

/-! ## The `Pair{A,B}` constructor, `base/Base.jl:10-13` -/

section Pair
variable {V T : Type}

/-- `(P::Type{Pair{A,B}})(a, b)`: each field is the argument itself when it already
has the field type and `convert(A, a)` otherwise; a conversion error propagates.
`isa v t` is `v isa t` and `convert t v` is `convert(t, v)`. -/
def pairNew (isa : V → T → Bool) (convert : T → V → M V) (A B : T) (a b : V) : M (V × V) := do
  let x <- if isa a A then pure a else convert A a
  let y <- if isa b B then pure b else convert B b
  pure (x, y)

/-- Both fields of the constructed pair have the declared types whenever `convert`
returns a value of the requested type, no conversion runs for an argument that
already has its field type, and the first failing conversion is the error. -/
def PairContract : Prop :=
  ∀ (isa : V → T → Bool) (convert : T → V → M V),
    (∀ t v w, convert t v = .ok w → isa w t = true) →
    ∀ A B a b,
      (∀ x y, pairNew isa convert A B a b = .ok (x, y) → isa x A = true ∧ isa y B = true) ∧
      (isa a A = true → isa b B = true → pairNew isa convert A B a b = .ok (a, b)) ∧
      (∀ e, isa a A = false → convert A a = .error e → pairNew isa convert A B a b = .error e)

theorem pairContract_proven : @PairContract V T := by
  intro isa convert hconv A B a b
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    simp only [pairNew, bind, Except.bind, pure, Except.pure] at h
    cases ha : isa a A <;> cases hb : isa b B <;> simp only [ha, hb] at h
    · cases hca : convert A a <;> cases hcb : convert B b <;> simp_all
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hconv _ _ _ hca, hconv _ _ _ hcb⟩
    · cases hca : convert A a <;> simp_all
      obtain ⟨rfl, rfl⟩ := h
      exact hconv _ _ _ hca
    · cases hcb : convert B b <;> simp_all
      obtain ⟨rfl, rfl⟩ := h
      exact hconv _ _ _ hcb
    · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨ha, hb⟩
  · intro ha hb
    simp [pairNew, ha, hb, bind, Except.bind, pure, Except.pure]
  · intro e ha he
    simp [pairNew, ha, he, bind, Except.bind]

end Pair

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

/-- `array_new_memory` returns memory of exactly `newlen` bytes that keeps the storage
kind of `mem`; `sizeof` counts bytes; `isdebugbuild` is the C flag test; the
`include` methods pass `identity` unless given a `mapexpr`; `in_sysimage` is
membership. -/
def SmallContract : Prop :=
  (∀ m n, (arrayNewMemory m n).len = n ∧ (arrayNewMemory m n).stringBacked = m.stringBacked) ∧
  (∀ a b : List UInt8, sizeofString (a ++ b) = sizeofString a + sizeofString b) ∧
  (∀ c, isdebugbuild c = true ↔ c ≠ 0) ∧
  aMethodToOverwriteInTest = 1 ∧
  (∀ {Mod R : Type} (inc : Option String → Mod → String → R) m p f,
      include1 inc m p = inc none m p ∧ include2 inc f m p = inc (some f) m p ∧
      includeInto1 inc m p = inc none m p ∧ includeInto2 inc m f p = inc (some f) m p) ∧
  (∀ s p, inSysimage s p = true ↔ p ∈ s)

theorem smallContract_proven : SmallContract := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro m n; cases m with | mk l sb => cases sb <;> simp [arrayNewMemory, ownsItself]
  · intro a b; simp [sizeofString]
  · intro c; simp [isdebugbuild]
  · intro Mod R inc m p f; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro s p; simp [inSysimage]

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

/-- A press recorded for an earlier episode never cancels, redelivers or exits; a
press for the current unmarked episode cancels exactly its source at
`CANCEL_REQUEST_SAFE`; a press for a marked source is redelivered; without an
episode source, a press exits with code 130 only when no live REPL backend runs
and the root task is done; installing a new episode gives a generation greater
than any recorded press, so a press recorded before it is stale; a held lock or
a clear flag makes `maybe_dispatch_sigint` a no-op, and otherwise it leaves the
lock released and the flag clear. -/
def SigintContract : Prop :=
  (∀ s, s.pendingGen ≠ s.episode.2 → (dispatchPass s).log = s.log ∧
      (dispatchPass s).severity = s.severity ∧ (dispatchPass s).pendingGen = s.pendingGen) ∧
  (∀ s src, s.episode = (some src, s.pendingGen) → s.pendingGen ≠ 0 → s.severity src = none →
      (dispatchPass s).log = s.log ++ [.cancel src] ∧ (dispatchPass s).severity src = some cancelSafe ∧
      (dispatchPass s).pendingGen = 0) ∧
  (∀ s src sev, s.episode = (some src, s.pendingGen) → s.pendingGen ≠ 0 → s.severity src = some sev →
      (dispatchPass s).log = s.log ++ [.redeliver src]) ∧
  (∀ s, s.episode.1 = none → s.pendingGen = s.episode.2 → s.pendingGen ≠ 0 →
      ((dispatchPass s).log = s.log ++ [.exit 130] ↔ s.backendDone ≠ some false ∧ s.rootDone = true)) ∧
  (∀ s cur src, s.pendingGen ≤ s.cGen →
      (sigintNewEpisode s cur src).1.pendingGen ≠ (sigintNewEpisode s cur src).1.episode.2 ∧
      (sigintNewEpisode s cur src).1.pendingGen ≤ (sigintNewEpisode s cur src).1.cGen) ∧
  (∀ s, s.pendingGen ≤ s.cGen →
      (sigintCloseEpisode s).pendingGen ≠ (sigintCloseEpisode s).episode.2 ∧
      (sigintCloseEpisode s).foreground = none) ∧
  (∀ s, (s.dispatchPending = false ∨ s.locked = true) → maybeDispatchSigint s = s) ∧
  (∀ s, s.dispatchPending = true → s.locked = false →
      (maybeDispatchSigint s).locked = false ∧ (maybeDispatchSigint s).dispatchPending = false ∧
      (maybeDispatchSigint s).log = (dispatchPass { s with dispatchPending := false, locked := true }).log)

theorem dispatchPass_dispatchPending (s : St) :
    (dispatchPass s).dispatchPending = s.dispatchPending := by
  obtain ⟨⟨src, gen⟩, fg, cg, cs, pg, dp, sev, lk, bd, rd, lg⟩ := s
  cases src <;> simp only [dispatchPass, consumePending] <;> (repeat' split) <;> simp_all [cancel]

theorem sigintContract_proven : SigintContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s h
    obtain ⟨⟨src, gen⟩, fg, cg, cs, pg, dp, sev, lk, bd, rd, lg⟩ := s
    simp only at h
    have hc : consumePending ⟨(src, gen), fg, cg, cs, pg, dp, sev, lk, bd, rd, lg⟩ gen =
        (⟨(src, gen), fg, cg, cs, pg, dp, sev, lk, bd, rd, lg⟩, false) := by
      simp [consumePending, h]
    cases src <;> simp [dispatchPass, hc]
  · intro s src he h0 hs
    obtain ⟨⟨src', gen⟩, fg, cg, cs, pg, dp, sev, lk, bd, rd, lg⟩ := s
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only at h0 hs
    simp [dispatchPass, consumePending, h0, sigintActiveSeverity, hs, cancel]
  · intro s src sev he h0 hs
    obtain ⟨⟨src', gen⟩, fg, cg, cs, pg, dp, sevf, lk, bd, rd, lg⟩ := s
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only at h0 hs
    simp [dispatchPass, consumePending, h0, sigintActiveSeverity, hs]
  · intro s hn hg h0
    obtain ⟨⟨src, gen⟩, fg, cg, cs, pg, dp, sev, lk, bd, rd, lg⟩ := s
    simp only at hn hg h0; subst hn; subst hg
    rcases bd with _ | ⟨_ | _⟩ <;> cases rd <;> simp [dispatchPass, consumePending, h0]
  · intro s cur src h
    simp [sigintNewEpisode, setSigintSource] <;> omega
  · intro s h
    simp [sigintCloseEpisode, setSigintSource] <;> omega
  · intro s h
    rcases h with h | h <;> simp [maybeDispatchSigint, h]
  · intro s hd hl
    have hd' := dispatchPass_dispatchPending { s with dispatchPending := false, locked := true }
    simp only at hd'
    simp [maybeDispatchSigint, hd, hl, claimLoop, hd']

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

/-- One sigint listener per nonempty pool, registered with C last; the exit hook
unregisters before closing and never waits for the current task; the profile
listener loads `Profile` once on its first wake-up only, and prints one report
per wake-up. -/
def ListenerContract : Prop :=
  (∀ k h, ((startSigintListener k h).filter (fun e => match e with | .spawn _ => true | _ => false)).length =
      (if k > 0 then 2 else 1) ∧ (startSigintListener k h).getLast? = some (.setCond (some h))) ∧
  (∀ ls c, (sigintAtexit ls c).take 2 = [.setCond none, .close] ∧ Ev.wait c ∉ sigintAtexit ls c) ∧
  (∀ h, (startProfileListener h).getLast? = some (.setCond (some h))) ∧
  (∀ w, (profilePrintingListener (some false) w).count .requireProfile ≤ 1 ∧
      (profilePrintingListener (some false) w).count .peekReport = (w.takeWhile id).length)

theorem profileLoop_loaded (w : List Bool) :
    (profileLoop (some false) w true).count .requireProfile = 0 ∧
    (profileLoop (some false) w true).count .peekReport = (w.takeWhile id).length := by
  induction w with
  | nil => simp [profileLoop]
  | cons b w ih => cases b <;> simp_all [profileLoop]

theorem listenerContract_proven : ListenerContract := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k h; by_cases hk : k > 0 <;> simp [startSigintListener, hk]
  · intro ls c; simp [sigintAtexit]
  · intro h; simp [startProfileListener]
  · intro w
    cases w with
    | nil => simp [profilePrintingListener, profileLoop]
    | cons b w =>
      cases b
      · simp [profilePrintingListener, profileLoop]
      · have := profileLoop_loaded w
        simp_all [profilePrintingListener, profileLoop]

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

/-- After `__init__`, `in_sysimage(p)` holds exactly for loaded packages, every
module of `loaded_modules_order` is recorded under its package in the original
order, an unset `JULIA_MAX_NUM_PRECOMPILE_FILES` keeps the previous limit, and an
unparsable one makes `__init__` throw the parse error. -/
def InitContract : Prop :=
  (∀ parseInt keys order env mf o, baseInit parseInt keys order env mf = .ok o →
      (∀ p, inSysimage o.sysimage p = true ↔ p ∈ keys) ∧
      (∀ p, o.precompiles p = (order.filter (·.1 == p)).map (·.2))) ∧
  (∀ parseInt keys order mf, ∃ o, baseInit parseInt keys order none mf = .ok o ∧ o.maxFiles = mf) ∧
  (∀ parseInt keys order v mf e, parseInt v = .error e →
      baseInit parseInt keys order (some v) mf = .error e)

theorem foldl_pushPrecompile (order : List (String × Nat)) (d : String → List Nat) (p : String) :
    order.foldl pushPrecompile d p = d p ++ (order.filter (·.1 == p)).map (·.2) := by
  induction order generalizing d with
  | nil => simp
  | cons q order ih =>
    rw [List.foldl_cons, ih]
    by_cases h : p = q.1
    · subst h; simp [pushPrecompile, List.filter_cons]
    · have h' : (q.1 == p) = false := by simp; exact fun e => h e.symm
      simp [pushPrecompile, List.filter_cons, h, h']

theorem initContract_proven : InitContract := by
  refine ⟨?_, ?_, ?_⟩
  · intro parseInt keys order env mf o h
    cases env with
    | none =>
      simp only [baseInit, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨fun p => by simp [inSysimage], fun p => by simp [foldl_pushPrecompile]⟩
    | some v =>
      simp only [baseInit, bind, Except.bind, pure, Except.pure] at h
      cases hv : parseInt v with
      | error e => simp [hv] at h
      | ok n =>
        simp only [hv, Except.ok.injEq] at h
        subst h
        exact ⟨fun p => by simp [inSysimage], fun p => by simp [foldl_pushPrecompile]⟩
  · intro parseInt keys order mf
    exact ⟨_, rfl, rfl⟩
  · intro parseInt keys order v mf e h
    simp [baseInit, h, bind, Except.bind]

/-! ## `base/download.jl` -/

/-- `Downloads()`: `require(PkgId(UUID((0xf43a241f_c20a_4ad4, 0x852c_f6b1247861c6)),
"Downloads"))`, `base/download.jl:3-6`; the UUID is the 128-bit number with the
first tuple element as its high half. -/
def downloadsUuid : Nat := 0xf43a241f_c20a_4ad4 * 2 ^ 64 + 0x852c_f6b1247861c6

/-- The effects of `do_download(url, path)`, `base/download.jl:22-25`: the
deprecation warning, loading `Downloads`, then `Downloads.download(url, path)`;
`path = none` is `nothing`. -/
inductive DlEv where
  | depwarn (msg : String) (funcsym : String)
  | require (uuid : Nat) (name : String)
  | download (url : String) (path : Option String)
  deriving DecidableEq, Repr

def doDownload (url : String) (path : Option String) : List DlEv :=
  [.depwarn "Base.download is deprecated; use Downloads.download instead" "download",
   .require downloadsUuid "Downloads", .download url path]

/-- `download(url, path)` and `download(url)`, `base/download.jl:19-20`. -/
def download2 (url path : String) : List DlEv := doDownload url (some path)
def download1 (url : String) : List DlEv := doDownload url none

/-- The UUID is that of the `Downloads` stdlib (`f43a241f-c20a-4ad4-852c-f6b1247861c6`
in its `Project.toml`); both methods warn once, then call `Downloads.download` with the
given path, or `nothing` (a temporary file) when none is given. -/
def DownloadContract : Prop :=
  downloadsUuid = 0xf43a241fc20a4ad4852cf6b1247861c6 ∧
  (∀ url path, download2 url path = [.depwarn "Base.download is deprecated; use Downloads.download instead" "download",
      .require downloadsUuid "Downloads", .download url (some path)]) ∧
  (∀ url, (download1 url).getLast? = some (.download url none) ∧
      (download1 url).countP (fun e => match e with | .depwarn .. => true | _ => false) = 1)

theorem downloadContract_proven : DownloadContract := by
  refine ⟨by decide, fun _ _ => rfl, fun url => ⟨rfl, rfl⟩⟩

end JuliaLean.MiscCov.BaseJl

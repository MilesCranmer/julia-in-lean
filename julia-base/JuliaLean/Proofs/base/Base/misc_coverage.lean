import JuliaLean.base.Base

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

end JuliaLean.MiscCov.BaseJl

namespace JuliaLean.MiscCov

def PairContractClosed : Prop := @BaseJl.PairContract Unit Unit
theorem pairContractClosed_proven : PairContractClosed := BaseJl.pairContract_proven

end JuliaLean.MiscCov

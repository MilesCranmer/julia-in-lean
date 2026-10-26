import JuliaLean.ConcurrencyCov.Timing

/-! Properties of `base/timing.jl` and their proofs or refutations. -/

namespace JuliaLean.ConcurrencyCov.Timing

open JuliaLean JuliaLean.Float JuliaLean.ConcurrencyCov

/-- A `GC_Diff` with every field zero. -/
def zeroDiff : GcDiff :=
  ⟨i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0⟩

theorem i64_sub_self (a : I64) : a - a = i64 0 := by
  apply Subtype.ext
  show wrapInt .i64 (a.val - a.val) = wrapInt .i64 0
  simp

/-- The GC counter helpers and runtime queries return the runtime's counters,
`GC_Diff` of a snapshot with itself is zero, the allocation count is the sum of the
four allocation counters, and the reentrant compile-timing counter is restored by
a matching enable/disable pair (`base/timing.jl:79-197`). -/
def GcCountersSpec : Prop :=
  (∀ rt, gcNumQ rt = rt.gcNum) ∧
  (∀ g : GcNum, gcTotalBytes g = g.allocd + g.deferred_alloc + g.total_allocd) ∧
  (∀ new old : GcNum, (gcDiff new old).allocd = gcTotalBytes new - gcTotalBytes old ∧
    (gcDiff new old).pause = new.pause - old.pause ∧
    (gcDiff new old).full_sweep = new.full_sweep - old.full_sweep) ∧
  (∀ g : GcNum, gcDiff g g = zeroDiff) ∧
  (∀ d : GcDiff, gcAllocCount d = d.malloc + d.realloc + d.poolalloc + d.bigalloc) ∧
  (∀ rt, cumulativeCompileTimeNs rt = (rt.compileNs, rt.recompileNs)) ∧
  (∀ rt, cumulativeCompileTiming false (cumulativeCompileTiming true rt) = rt) ∧
  (∀ rt, (cumulativeCompileTiming true rt).compileTiming = rt.compileTiming + 1) ∧
  (∀ rt, gcTimeNs rt = rt.gcHrtime ∧ jitTotalBytes rt = rt.jitBytes) ∧
  (∀ rt, gcLiveBytes rt = rt.liveBytes + rt.gcNum.allocd + rt.gcNum.deferred_alloc) ∧
  (∀ rt, nMaxPools ≤ rt.pageUtil.length → (gcPageUtilizationData rt).length = 51) ∧
  (∀ rt, 5 ≤ rt.sweepReasons.length →
    (∀ v ∈ rt.sweepReasons, v.val ≤ IntTy.max .i64) →
    (fullSweepReasons rt).map (List.map Prod.fst) = .ok fullSweepReasonNames) ∧
  (∀ rt, gcBytes rt = rt.totalBytes)

theorem gcCountersSpec_proven : GcCountersSpec := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, ?_, fun _ => rfl, fun _ => rfl,
    ?_, fun _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ => rfl, ?_, ?_, fun _ => rfl⟩
  · intro g
    simp only [gcDiff, zeroDiff, i64_sub_self]
  · intro rt
    simp [cumulativeCompileTiming]
  · intro rt h
    simp [gcPageUtilizationData, nMaxPools] at h ⊢
    omega
  · intro rt hlen hval
    obtain ⟨v1, v2, v3, v4, v5, rest, hr⟩ : ∃ v1 v2 v3 v4 v5 rest,
        rt.sweepReasons = v1 :: v2 :: v3 :: v4 :: v5 :: rest := by
      match h : rt.sweepReasons, hlen with
      | v1 :: v2 :: v3 :: v4 :: v5 :: rest, _ => exact ⟨v1, v2, v3, v4, v5, rest, rfl⟩
    rw [hr] at hval
    have h1 := hval v1 (by simp)
    have h2 := hval v2 (by simp)
    have h3 := hval v3 (by simp)
    have h4 := hval v4 (by simp)
    have h5 := hval v5 (by simp)
    simp [fullSweepReasons, hr, fullSweepReasonNames, toI64, h1, h2, h3, h4, h5,
      List.mapM_cons, Except.map]
    rfl

/-- `prettyprint_getunits` returns `0` and `1` unchanged with unit 1, and otherwise
never selects a unit beyond `numunits`; `format_bytes` prints `0 bytes`/`1 byte`
and its doctests hold (`base/timing.jl:202-252`). -/
def FormatBytesSpec : Prop :=
  (∀ v n f, (v.val = 0 ∨ v.val = 1) → prettyprintGetunits v n f = .ok (.int v, i64 1)) ∧
  (∀ (v : I64) (n : Nat) (f : I64) x u, 1 ≤ n → (n : Int) ≤ IntTy.max .i64 →
    prettyprintGetunits v n f = .ok (x, u) → u.val ≤ n) ∧
  (∀ v b, (v.val = 0 ∨ v.val = 1) →
    formatBytes v b = .ok (toString v.val ++ " byte" ++ (if v.val = 1 then "" else "s"))) ∧
  formatBytes (i64 1024) = .ok "1024 bytes" ∧
  formatBytes (i64 10000) = .ok "9.766 KiB" ∧
  formatBytes (i64 10000) false = .ok "10.000 kB"

theorem prettyprint_small (v : I64) (n : Nat) (f : I64) (h : v.val = 0 ∨ v.val = 1) :
    prettyprintGetunits v n f = .ok (.int v, i64 1) := by
  simp [prettyprintGetunits, h]

theorem formatBytes_1024 : formatBytes (i64 1024) = .ok "1024 bytes" := by decide +kernel
theorem formatBytes_10000 : formatBytes (i64 10000) = .ok "9.766 KiB" := by decide +kernel
theorem formatBytes_10000_dec : formatBytes (i64 10000) false = .ok "10.000 kB" := by decide +kernel

theorem i64_val_of_nat (n : Nat) (h : (n : Int) ≤ IntTy.max .i64) : (i64 n).val = n :=
  wrapInt_of_inRange .i64 n ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits], h⟩

theorem prettyprint_unit_le (v : I64) (n : Nat) (f : I64) (x : Num) (u : I64) (hn1 : 1 ≤ n)
    (hn : (n : Int) ≤ IntTy.max .i64) (h : prettyprintGetunits v n f = .ok (x, u)) :
    u.val ≤ n := by
  unfold prettyprintGetunits at h
  by_cases hs : v.val = 0 ∨ v.val = 1
  · rw [if_pos hs] at h
    cases h
    have : (i64 1).val = 1 := by decide
    omega
  · rw [if_neg hs] at h
    obtain ⟨lv, -, h⟩ := bind_ok h
    obtain ⟨lf, -, h⟩ := bind_ok h
    obtain ⟨unit, -, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨p, -, h⟩ := bind_ok h
    cases h
    split
    · have := i64_val_of_nat n hn; omega
    · omega

theorem formatBytesSpec_proven : FormatBytesSpec := by
  refine ⟨prettyprint_small, prettyprint_unit_le, ?_, formatBytes_1024, formatBytes_10000,
    formatBytes_10000_dec⟩
  intro v b h
  rcases h with h | h
  · have hv : v = i64 0 := Subtype.ext (by rw [h]; decide)
    subst hv
    cases b <;> decide
  · have hv : v = i64 1 := Subtype.ext (by rw [h]; decide)
    subst hv
    cases b <;> decide

/-! ## Reports -/

/-- The text before the time: the description and `": "`, or padding to 10 columns. -/
def leadOf (msg : Option String) (t : String) : String :=
  match msg with
  | some m => m ++ ": "
  | none => if t.length < 10 then String.ofList (List.replicate (10 - t.length) ' ') else ""

def nl (b : Bool) : String := if b then "\n" else ""

/-- No counter clause applies. -/
def Quiet (a : TimeArgs) : Prop :=
  a.bytes.val = 0 ∧ a.allocs.val = 0 ∧ a.gctime.val ≤ 0 ∧ fpos a.compile_time = false ∧
    fpos a.recompile_time = false

/-- `time_print` writes the description or padding, the time with six decimals and
`seconds`, and no parenthesised clause when no counter is positive; a positive lock
conflict count alone is printed in parentheses with its plural
(`base/timing.jl:254-305`). -/
def TimePrintSpec : Prop :=
  (∀ a t, Quiet a → a.lock_conflicts.val ≤ 0 → writefixed (F64.div a.elapsedtime f1e9) 6 = .ok t →
    timePrint a = .ok (leadOf a.msg t ++ t ++ " seconds" ++ nl a.newline)) ∧
  (∀ a t, Quiet a → 0 < a.lock_conflicts.val → writefixed (F64.div a.elapsedtime f1e9) 6 = .ok t →
    timePrint a = .ok (leadOf a.msg t ++ t ++ " seconds" ++ " (" ++ (toString a.lock_conflicts.val ++
      " lock conflict" ++ (if a.lock_conflicts.val = 1 then "" else "s")) ++ ")" ++ nl a.newline))

theorem timePrintSpec_proven : TimePrintSpec := by
  constructor
  · intro a t ⟨hb, ha, hg, hc, hr⟩ hl hw
    have hg' : ¬ 0 < a.gctime.val := by omega
    have hl' : ¬ 0 < a.lock_conflicts.val := by omega
    cases hm : a.msg <;>
      simp [timePrint, hw, hb, ha, hg', hl', hc, hr, hm, leadOf, nl, bind, Except.bind, pure,
        Except.pure]
  · intro a t ⟨hb, ha, hg, hc, hr⟩ hl hw
    have hg' : ¬ 0 < a.gctime.val := by omega
    cases hm : a.msg <;> cases hn : a.newline <;>
      simp [timePrint, hw, hb, ha, hg', hl, hc, hr, hm, hn, leadOf, nl, bind, Except.bind, pure,
        Except.pure, String.append_assoc]

/-- `padded_nonzero_print` writes one line padded to column 20 for every label of 3
to 19 characters when printing is forced, and nothing for a zero value when it is
not (`base/timing.jl:212-217`). -/
def PaddedPrintSpec : Prop :=
  (∀ v s, 3 ≤ s.length → s.length ≤ 19 →
    paddedNonzeroPrint v s = .ok [⟨s, String.ofList (List.replicate (19 - s.length) ' '), v⟩]) ∧
  (∀ v s, v.nonzero = false → paddedNonzeroPrint v s false = .ok [])

theorem paddedPrintSpec_proven : PaddedPrintSpec := by
  constructor
  · intro v s h3 h19
    simp only [paddedNonzeroPrint, Bool.true_or, if_true, blanks]
    by_cases h0 : (19 : Int) - s.length ≤ 0
    · have : s.length = 19 := by omega
      simp [h0, this, bind, Except.bind, pure, Except.pure]
    · have h16 : (19 : Int) - s.length ≤ 16 := by omega
      have hn : ((19 : Int) - s.length).toNat = 19 - s.length := by omega
      simp [h0, h16, hn, bind, Except.bind, pure, Except.pure]
  · intro v s h
    simp [paddedNonzeroPrint, h]

/-- `true` when every `elapsed time (ns)` line carries an integer. -/
def elapsedInteger : R TimevOut → Bool
  | .ok out => out.lines.all fun l => l.label != "elapsed time (ns)" ||
      (match l.value with | .int _ => true | .flt _ => false)
  | .error _ => true

/-- `@timev` prints the elapsed time as an integer nanosecond count, as its
docstring example shows (`base/timing.jl:450-465`). -/
def TimevElapsedInteger : Prop :=
  ∀ e diff lc ct msg, elapsedInteger (timevPrint e diff lc ct msg) = true

/-- One microsecond. -/
def oneMicro : F64 := F64.ofInt 1000

theorem timevElapsedInteger_refuted : ¬ TimevElapsedInteger := by
  intro h
  have := h oneMicro zeroDiff (i64 0) (F64.zero, F64.zero) none
  revert this
  decide +kernel

/-- `true` when every counter line after the elapsed time has a nonzero value. -/
def countersNonzero : R TimevOut → Bool
  | .ok out => (out.lines.filter fun l => l.label != "elapsed time (ns)").all fun l => l.value.nonzero
  | .error _ => true

/-- `@timev` prints "any non-zero memory allocation counters" after the time line
(`base/timing.jl:435-437`): no printed counter is zero. -/
def TimevNonzeroCounters : Prop :=
  ∀ e diff lc ct msg, countersNonzero (timevPrint e diff lc ct msg) = true

theorem timevNonzeroCounters_refuted : ¬ TimevNonzeroCounters := by
  intro h
  have := h oneMicro zeroDiff (i64 0) (F64.zero, F64.zero) none
  revert this
  decide +kernel

/-! ## Measuring macros -/

theorem u64_add_sub (a d : U64) : subw (a + d) a = d := by
  apply Subtype.ext
  show wrapInt .u64 (wrapInt .u64 (a.val + d.val) - a.val) = d.val
  have ha := a.property
  have hd := d.property
  simp only [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at ha hd ⊢
  simp at ha hd ⊢
  omega

@[simp] theorem cct_true (rt : TimingRt) :
    cumulativeCompileTiming true rt = { rt with compileTiming := rt.compileTiming + 1 } := rfl
@[simp] theorem cct_false (rt : TimingRt) :
    cumulativeCompileTiming false rt = { rt with compileTiming := rt.compileTiming - 1 } := rfl

/-- The value `@timed` returns, in closed form. -/
theorem timed_fst (r : Run) (rt : TimingRt) : (timed r rt).1 = match r.outcome with
    | .error e => .error e
    | .ok v => .ok {
        value := v, time := F64.div (F64.ofJInt (subw (rt.clock + r.dt) rt.clock)) f1e9,
        bytes := (gcDiff r.gcAfter rt.gcNum).allocd,
        gctime := F64.div (F64.ofJInt (gcDiff r.gcAfter rt.gcNum).total_time) f1e9,
        gcstats := gcDiff r.gcAfter rt.gcNum,
        lock_conflicts := rt.lockConflicts + r.conflicts - rt.lockConflicts,
        compile_time := F64.div (F64.ofJInt (subw r.compileAfter.1 rt.compileNs)) f1e9,
        recompile_time := F64.div (F64.ofJInt (subw r.compileAfter.2 rt.recompileNs)) f1e9 } := by
  obtain ⟨o, dt, ga, ca, cf⟩ := r
  cases o <;> rfl

theorem timed_snd (r : Run) (rt : TimingRt) :
    (timed r rt).2.lockProfiling = rt.lockProfiling ∧
    (timed r rt).2.compileTiming = rt.compileTiming ∧ (timed r rt).2.gcNum = r.gcAfter := by
  obtain ⟨o, dt, ga, ca, cf⟩ := r
  cases o <;> simp [timed]

theorem map_ok {ε α β : Type} {f : α → β} {e : Except ε α} {b : β}
    (h : Except.map f e = .ok b) : ∃ a, e = .ok a ∧ f a = b := by
  cases e with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, by cases h; rfl⟩

theorem time_value (msg : Option String) (r : Run) (rt : TimingRt) (s : String) (x : Nat)
    (h : (time msg r rt).1 = .ok (s, x)) : r.outcome = .ok x := by
  have ht := timed_fst r rt
  unfold time at h
  generalize timed r rt = p at h ht
  obtain ⟨res, rt'⟩ := p
  cases ho : r.outcome with
  | error e => simp [ho] at ht; subst ht; cases h
  | ok v =>
    simp only [ho] at ht
    subst ht
    obtain ⟨a, -, ha⟩ := map_ok h
    cases ha
    rfl

theorem timev_value (msg : Option String) (r : Run) (rt : TimingRt) (o : TimevOut) (x : Nat)
    (h : (timev msg r rt).1 = .ok (o, x)) : r.outcome = .ok x := by
  have ht := timed_fst r rt
  unfold timev at h
  generalize timed r rt = p at h ht
  obtain ⟨res, rt'⟩ := p
  cases ho : r.outcome with
  | error e => simp [ho] at ht; subst ht; cases h
  | ok v =>
    simp only [ho] at ht
    subst ht
    obtain ⟨a, -, ha⟩ := map_ok h
    cases ha
    rfl

/-- `@timed` leaves the lock-profiling and compile-timing counters as it found them,
returns the value of the expression with the GC counter differences, the elapsed
time and the lock conflicts of the run, and propagates an exception of the
expression; `@time`, `@showtime` and `@timev` return the value of the expression;
`@elapsed` returns the elapsed seconds (`base/timing.jl:395-508,732-760`). -/
def TimedSpec : Prop :=
  (∀ r rt, (timed r rt).2.lockProfiling = rt.lockProfiling ∧
    (timed r rt).2.compileTiming = rt.compileTiming ∧ (timed r rt).2.gcNum = r.gcAfter) ∧
  (∀ r rt e, r.outcome = .error e → (timed r rt).1 = .error e) ∧
  (∀ r rt v, r.outcome = .ok v → ∃ t, (timed r rt).1 = .ok t ∧ t.value = v ∧
    t.gcstats = gcDiff r.gcAfter rt.gcNum ∧ t.bytes = t.gcstats.allocd ∧
    t.lock_conflicts = r.conflicts ∧ t.time = F64.div (F64.ofJInt r.dt) f1e9) ∧
  (∀ msg r rt s x, (time msg r rt).1 = .ok (s, x) → r.outcome = .ok x) ∧
  (∀ msg r rt e, r.outcome = .error e → (time msg r rt).1 = .error e) ∧
  (∀ text r rt, showtime text r rt = time (some text) r rt) ∧
  (∀ msg r rt o x, (timev msg r rt).1 = .ok (o, x) → r.outcome = .ok x) ∧
  (∀ r rt v, r.outcome = .ok v → (elapsed r rt).1 = .ok (F64.div (F64.ofJInt r.dt) f1e9))

theorem timedSpec_proven : TimedSpec := by
  refine ⟨timed_snd, ?_, ?_, time_value, ?_, fun _ _ _ => rfl, timev_value, ?_⟩
  · intro r rt e h
    rw [timed_fst, h]
  · intro r rt v h
    rw [timed_fst, h]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · show rt.lockConflicts + r.conflicts - rt.lockConflicts = r.conflicts
      omega
    · show F64.div (F64.ofJInt (subw (rt.clock + r.dt) rt.clock)) f1e9 = _
      rw [u64_add_sub]
  · intro msg r rt e h
    have ht := timed_fst r rt
    rw [h] at ht
    unfold time
    generalize timed r rt = p at ht
    obtain ⟨res, rt'⟩ := p
    simp only at ht
    subst ht
    rfl
  · intro r rt v h
    simp [elapsed, h, u64_add_sub]

/-- `allocated` and `allocations` return the change of the total-bytes counter and
of the allocation counters; `@lock_conflicts` returns the conflicts of the run and
restores lock profiling; `@time_imports`, `@trace_compile` and `@trace_dispatch`
raise their counter by one while the expression runs, restore it afterwards and
return the expression's outcome (`base/timing.jl:326-334,511-534,672-683,764-798`). -/
def CountersMacroSpec : Prop :=
  (∀ a rt v, a.outcome = .ok v → (allocated a rt).1 = .ok (a.bytesAfter - rt.totalBytes)) ∧
  (∀ a rt v, a.outcome = .ok v → (allocations a rt).1 = .ok (gcAllocCount (gcDiff a.gcAfter rt.gcNum))) ∧
  (∀ a rt e, a.outcome = .error e → (allocated a rt).1 = .error e ∧ (allocations a rt).1 = .error e) ∧
  (∀ r rt v, r.outcome = .ok v → (lockConflictsMacro r rt).1 = .ok r.conflicts ∧
    (lockConflictsMacro r rt).2.lockProfiling = rt.lockProfiling) ∧
  (∀ (σ : Type) (ex : σ → Outcome × σ) fin s, tryfinally ex fin s = ((ex s).1, fin (ex s).2)) ∧
  (∀ b o rt, (bracket b o rt).1 = (o, b.get rt + 1) ∧ b.get (bracket b o rt).2 = b.get rt)

theorem countersMacroSpec_proven : CountersMacroSpec := by
  refine ⟨?_, ?_, ?_, ?_, fun _ _ _ _ => rfl, ?_⟩
  · intro a rt v h; simp [allocated, h, gcBytes]
  · intro a rt v h; simp [allocations, h, gcNumQ]
  · intro a rt e h; simp [allocated, allocations, h]
  · intro r rt v h; simp [lockConflictsMacro, h] <;> omega
  · intro b o rt
    cases b <;> simp [bracket, tryfinally, Bracket.get, Bracket.add] <;> omega

/-- The dotted-operator test of `is_simply_call` (line 548-551). -/
def dottedOp (sa : String) : Bool :=
  sa.startsWith "." && !sa.endsWith "." && isOperatorName (sa.drop 1).toString

/-- `is_simply_call` accepts exactly the calls whose arguments are atoms or splatted
atoms and whose head is not a dotted operator; `@allocated`/`@allocations` measure
such a call directly, wrap any other call in a closure and count around any other
expression in place (`base/timing.jl:537-645`). -/
def MeasurerSpec : Prop :=
  (∀ e, (∀ args, e ≠ .call args) → isSimplyCall e = .ok false) ∧
  (∀ args, args.all isSimpleArg = false → isSimplyCall (.call args) = .ok false) ∧
  (∀ sa rest, (Ast.sym sa :: rest).all isSimpleArg = true →
    isSimplyCall (.call (.sym sa :: rest)) = .ok (!dottedOp sa)) ∧
  (∀ args f, isSimplyCall (.call args) = .ok true →
    genAllocationMeasurer (.call args) f = .ok (.direct f args)) ∧
  (∀ args f, isSimplyCall (.call args) = .ok false →
    genAllocationMeasurer (.call args) f = .ok (.wrapped f (.call args))) ∧
  (∀ e, (∀ args, e ≠ .call args) →
    allocatedMacro e = .ok (.inPlace "allocated" e) ∧
    allocationsMacro e = .ok (.inPlace "allocations" e))

theorem measurerSpec_proven : MeasurerSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e h
    cases e with
    | call args => exact absurd rfl (h args)
    | _ => rfl
  · intro args h
    simp only [isSimplyCall, h, Bool.not_false, ite_true]
  · intro sa rest h
    simp only [isSimplyCall, h, Bool.not_true, Bool.false_eq_true, if_false, dottedOp]
    cases hd : (sa.startsWith "." && !sa.endsWith "." && isOperatorName (sa.drop 1).toString) <;>
      simp [hd]
  · intro args f h
    simp [genAllocationMeasurer, h, bind, Except.bind, pure, Except.pure]
  · intro args f h
    simp [genAllocationMeasurer, h, bind, Except.bind, pure, Except.pure]
  · intro e h
    cases e with
    | call args => exact absurd rfl (h args)
    | _ => exact ⟨rfl, rfl⟩

end JuliaLean.ConcurrencyCov.Timing

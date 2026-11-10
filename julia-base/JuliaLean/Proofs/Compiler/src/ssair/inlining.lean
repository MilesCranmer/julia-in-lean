import JuliaLean.Registry.Types
import JuliaLean.Compiler.src.ssair.inlining
import JuliaLean.Proofs.Compiler.src.optimize

/-!
Properties of the decision helpers of `Compiler/src/ssair/inlining.jl`: which result
`early_inline_special_case` gives, the branch `handle_cases!` takes, `inline_const_if_inlineable!`,
`linear_inline_eligible`, and the `@inline`/`@noinline` call-site rules of `resolve_todo`,
`semiconcrete_result_item` and the flag bits of `jl_code_info_set_ir`.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.inlining

open JuliaLean.Registry
open JuliaLean JuliaLean.Compiler JuliaLean.Compiler.Optimize JuliaLean.Compiler.Inlining
open JuliaLean.Proofs.Compiler.src.optimize

/-! ## `early_inline_special_case` -/

/-- The part of `early_inline_special_case` after the constant case, on the answers it reads:
`n2`, `n3`, `n4` are `length(argtypes) == 2`, `== 3`, `== 4`. -/
def specialB (sp : Special) (n2 n3 n4 c sym cond tr fa bo ta eg : Bool) : EarlyResult := Id.run do
  if sp == .compilerbarrier then
    if !n3 then return .none_
    if !c then return .none_
    if !sym then return .none_
    if !cond then return .none_
    return .arg3
  else if sp == .ifelse && n4 then
    if c then
      if tr then return .arg3
      else if fa then return .arg4
    else if bo && eg then return .arg3
  else if sp == .taskResultType && n2 && ta then
    return .instanceof
  return .none_

/-- Whether the constant case replaces the call by its value. -/
def quotedCond (x : EarlyFacts) (nt : Bool) : Bool :=
  x.typeConst && x.valInlineable &&
    (if x.fIntrinsic then x.pureIntrinsic && nt else x.inPure || (x.inEffectFree && nt))

theorem early_eq (x : EarlyFacts) (flag : UInt32) :
    earlyInlineSpecialCase x flag =
      if !x.inlining then .none_
      else if x.typeConst && !x.valInlineable then .none_
      else if quotedCond x (hasFlag flag IR_FLAG_NOTHROW) then .quotedVal
      else specialB x.special (x.nargtypes == 2) (x.nargtypes == 3) (x.nargtypes == 4) x.arg2Const
        x.arg2Symbol x.arg2Conditional x.arg2True x.arg2False x.arg2Bool x.arg2Task x.args34Egal := by
  obtain ⟨inl, tc, vi, fI, pI, iP, iE, sp, n, a1, a2, a3, a4, a5, a6, a7, a8⟩ := x
  simp only [earlyInlineSpecialCase, quotedCond, specialB]
  generalize hasFlag flag IR_FLAG_NOTHROW = nt
  cases inl <;> cases tc <;> cases vi <;> cases fI <;> cases pI <;> cases iP <;> cases iE <;>
    cases nt <;> rfl

/-- The facts of `specialB`, checked over all its inputs. -/
def specialFacts (sp : Special) (n2 n3 n4 c sym cond tr fa bo ta eg : Bool) : Bool :=
  let r := specialB sp n2 n3 n4 c sym cond tr fa bo ta eg
  r != .quotedVal &&
  (r == .arg3) == ((sp == .compilerbarrier && n3 && c && sym && cond) ||
    (sp == .ifelse && n4 && ((c && tr) || (!c && bo && eg)))) &&
  (r == .arg4) == (sp == .ifelse && n4 && c && !tr && fa) &&
  (r == .instanceof) == (sp == .taskResultType && n2 && ta)

theorem specialFacts_all : ∀ sp n2 n3 n4 c sym cond tr fa bo ta eg,
    specialFacts sp n2 n3 n4 c sym cond tr fa bo ta eg = true := by
  intro sp; cases sp <;> decide

/-- `early_inline_special_case` replaces a call by something else only in the documented cases:
nothing when inlining is off; the constant result `quoted(val)` exactly when the result is a
`Const` with an inlineable value and the callee is a pure intrinsic on a `nothrow` statement, a
pure builtin, or an effect-free builtin on a `nothrow` statement; `stmt.args[3]` exactly for a
`compilerbarrier(:conditional, x)` with three argument types, or an `ifelse` with four whose
condition is `Const(true)` or a non-constant `Bool` with identical branches; `stmt.args[4]`
exactly for an `ifelse` with condition `Const(false)`; the `task_result_type` result exactly for
a `Task` argument. The statement flag matters only through its `IR_FLAG_NOTHROW` bit. -/
def EarlyInlineSpecialCaseSpec : Prop :=
  (∀ x f, x.inlining = false → earlyInlineSpecialCase x f = .none_) ∧
  (∀ x f, x.typeConst = true → x.valInlineable = false → earlyInlineSpecialCase x f = .none_) ∧
  (∀ x f, x.inlining = true →
    (earlyInlineSpecialCase x f = .quotedVal ↔
      (x.typeConst = true ∧ x.valInlineable = true ∧
        ((x.fIntrinsic = true ∧ x.pureIntrinsic = true ∧ hasFlag f IR_FLAG_NOTHROW = true) ∨
         (x.fIntrinsic = false ∧ (x.inPure = true ∨ (x.inEffectFree = true ∧ hasFlag f IR_FLAG_NOTHROW = true))))))) ∧
  (∀ x f, earlyInlineSpecialCase x f = .arg3 →
    (x.special = .compilerbarrier ∧ x.nargtypes = 3 ∧ x.arg2Const = true ∧ x.arg2Symbol = true ∧
        x.arg2Conditional = true) ∨
    (x.special = .ifelse ∧ x.nargtypes = 4 ∧
      ((x.arg2Const = true ∧ x.arg2True = true) ∨
       (x.arg2Const = false ∧ x.arg2Bool = true ∧ x.args34Egal = true)))) ∧
  (∀ x f, earlyInlineSpecialCase x f = .arg4 →
    x.special = .ifelse ∧ x.nargtypes = 4 ∧ x.arg2Const = true ∧ x.arg2True = false ∧ x.arg2False = true) ∧
  (∀ x f, earlyInlineSpecialCase x f = .instanceof →
    x.special = .taskResultType ∧ x.nargtypes = 2 ∧ x.arg2Task = true) ∧
  (∀ x f g, hasFlag f IR_FLAG_NOTHROW = hasFlag g IR_FLAG_NOTHROW →
    earlyInlineSpecialCase x f = earlyInlineSpecialCase x g)

theorem earlyInlineSpecialCaseSpec_proven : EarlyInlineSpecialCaseSpec := by
  have sp := fun (x : EarlyFacts) => specialFacts_all x.special (x.nargtypes == 2) (x.nargtypes == 3)
    (x.nargtypes == 4) x.arg2Const x.arg2Symbol x.arg2Conditional x.arg2True x.arg2False x.arg2Bool
    x.arg2Task x.args34Egal
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x f h; rw [early_eq, h]; rfl
  · intro x f h1 h2; rw [early_eq, h1, h2]; split <;> rfl
  · intro x f h
    rw [early_eq, h]
    have := sp x
    simp only [specialFacts, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    constructor
    · intro e
      split at e
      · cases e
      split at e
      · rename_i hq
        simp only [quotedCond, Bool.and_eq_true] at hq
        obtain ⟨⟨h1, h2⟩, h3⟩ := hq
        refine ⟨h1, h2, ?_⟩
        revert h3; cases x.fIntrinsic <;> simp
      · exact absurd e this.1.1.1
    · intro ⟨h1, h2, h3⟩
      rw [if_neg (by simp [h2]), if_pos]
      simp only [quotedCond, h1, h2, Bool.true_and]
      rcases h3 with ⟨h4, h5, h6⟩ | ⟨h4, h5⟩
      · simp [h4, h5, h6]
      · rw [h4]; rcases h5 with h5 | ⟨h5, h6⟩ <;> simp [h5]; simp [h6]
  · intro x f e
    rw [early_eq] at e
    split at e
    · cases e
    split at e
    · cases e
    split at e
    · cases e
    have := sp x
    simp only [specialFacts, Bool.and_eq_true, beq_iff_eq] at this
    have h := this.1.1.2
    rw [e] at h
    have h' := h.symm.trans (rfl : (EarlyResult.arg3 == EarlyResult.arg3) = true)
    simpa [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, and_assoc, or_assoc] using h'
  · intro x f e
    rw [early_eq] at e
    split at e
    · cases e
    split at e
    · cases e
    split at e
    · cases e
    have := sp x
    simp only [specialFacts, Bool.and_eq_true, beq_iff_eq] at this
    have h := this.1.2
    rw [e] at h
    have h' := h.symm.trans (rfl : (EarlyResult.arg4 == EarlyResult.arg4) = true)
    simpa [Bool.and_eq_true, beq_iff_eq, and_assoc] using h'
  · intro x f e
    rw [early_eq] at e
    split at e
    · cases e
    split at e
    · cases e
    split at e
    · cases e
    have := sp x
    simp only [specialFacts, Bool.and_eq_true, beq_iff_eq] at this
    have h := this.2
    rw [e] at h
    have h' := h.symm.trans (rfl : (EarlyResult.instanceof == EarlyResult.instanceof) = true)
    simpa [Bool.and_eq_true, beq_iff_eq, and_assoc] using h'
  · intro x f g h
    rw [early_eq, early_eq, h]

/-! ## `handle_cases!` -/

/-- `handle_cases!` takes the documented branch: it handles a single, fully covered and fully
handled case directly; otherwise, with any case or all cases handled, it union-splits with the
`handled_all_cases` and `fully_covered` it was given, giving up when `atype` or a case signature
is not a `DataType`; with nothing to inline it only adds the flags of the joint effects, so the
statement keeps every flag it had and becomes removable when the joint effects are
removable-if-unused. The order of the cases does not matter. -/
def HandleCasesSpec : Prop :=
  (∀ h fc n a sigs e flag, handleCases h fc n a sigs e flag = .single ↔ (fc = true ∧ h = true ∧ n = 1)) ∧
  (∀ h fc n a sigs e flag h' fc', handleCases h fc n a sigs e flag = .unionSplit h' fc' →
    h' = h ∧ fc' = fc ∧ a = true ∧ (∀ s ∈ sigs, s = true) ∧ (n > 0 ∨ h = true) ∧
    ¬(fc = true ∧ h = true ∧ n = 1)) ∧
  (∀ h fc n a sigs e flag f', handleCases h fc n a sigs e flag = .flags f' →
    n = 0 ∧ h = false ∧ f' = flag ||| flagsForEffects e ∧ hasFlag f' flag = true ∧
    (isRemovableIfUnused e = true → hasFlag f' IR_FLAGS_REMOVABLE = true)) ∧
  (∀ h fc n a sigs1 sigs2 e flag, sigs1.Perm sigs2 →
    handleCases h fc n a sigs1 e flag = handleCases h fc n a sigs2 e flag)

theorem handleCasesSpec_proven : HandleCasesSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h fc n a sigs e flag
    unfold handleCases
    constructor
    · intro hs
      split at hs
      · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact ⟨hc.1.1, hc.1.2, hc.2⟩
      · split at hs
        · split at hs <;> (try split at hs) <;> cases hs
        · cases hs
    · intro ⟨h1, h2, h3⟩; subst h1 h2 h3; rfl
  · intro h fc n a sigs e flag h' fc' hs
    unfold handleCases at hs
    split at hs
    · cases hs
    rename_i hns
    split at hs
    · rename_i hor
      split at hs
      · cases hs
      split at hs
      · cases hs
      cases hs
      rename_i ha hall
      simp only [Bool.not_eq_true', Bool.not_eq_false] at ha
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, id] at hall
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hor
      simp only [Bool.and_eq_true, beq_iff_eq] at hns
      exact ⟨rfl, rfl, ha, hall, hor, fun ⟨a1, a2, a3⟩ => hns ⟨⟨a1, a2⟩, a3⟩⟩
    · cases hs
  · intro h fc n a sigs e flag f' hs
    unfold handleCases at hs
    split at hs
    · cases hs
    split at hs
    · split at hs
      · cases hs
      split at hs <;> cases hs
    · cases hs
      rename_i hor
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hor
      refine ⟨by omega, hor.2, rfl, ?_, ?_⟩
      · rw [hasFlag_iff]; intro i hi
        simp [UInt32.toBitVec_or, BitVec.getLsbD_or, hi]
      · intro hr
        have h1 := (flagsForEffectsSpec_proven e).2.2.2.2.2.2.2.2.2.2.1
        rw [hr, hasFlag_iff] at h1
        rw [hasFlag_iff]; intro i hi
        simp [UInt32.toBitVec_or, BitVec.getLsbD_or, h1 i hi]
  · intro h fc n a sigs1 sigs2 e flag hp
    unfold handleCases
    have : sigs1.all id = sigs2.all id := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, id]
      exact ⟨fun h x hx => h x (hp.mem_iff.mpr hx), fun h x hx => h x (hp.mem_iff.mp hx)⟩
    rw [this]

/-! ## `inline_const_if_inlineable!` and `linear_inline_eligible` -/

/-- `inline_const_if_inlineable!` replaces the statement exactly when its type is a `Const` with an
inlineable value, leaving the flag; otherwise it keeps the statement and its flags and adds
`IR_FLAGS_REMOVABLE`. -/
def InlineConstIfInlineableSpec : Prop :=
  ∀ rc vi flag, (inlineConstIfInlineable rc vi flag).1 = (rc && vi) ∧
    (rc = true → vi = true → (inlineConstIfInlineable rc vi flag).2 = flag) ∧
    ((rc && vi) = false → hasFlag (inlineConstIfInlineable rc vi flag).2 IR_FLAGS_REMOVABLE = true ∧
      hasFlag (inlineConstIfInlineable rc vi flag).2 flag = true)

theorem inlineConstIfInlineableSpec_proven : InlineConstIfInlineableSpec := by
  intro rc vi flag
  refine ⟨?_, ?_, ?_⟩
  · unfold inlineConstIfInlineable; split <;> simp_all
  · intro h1 h2; subst h1 h2; rfl
  · intro h
    unfold inlineConstIfInlineable
    rw [if_neg (by simp [h])]
    refine ⟨hasFlag_self_or _ _, ?_⟩
    rw [hasFlag_iff]; intro i hi
    simp [UInt32.toBitVec_or, BitVec.getLsbD_or, hi]

/-- `linear_inline_eligible(ir)` holds exactly for a one-block body ending in a `ReturnNode` with
a value. -/
def LinearInlineEligibleSpec : Prop :=
  ∀ n t, linearInlineEligible n t = true ↔ (n = 1 ∧ t = .returnVal)

theorem linearInlineEligibleSpec_proven : LinearInlineEligibleSpec := by
  intro n t
  unfold linearInlineEligible
  split
  · rename_i h; simp only [bne_iff_ne, ne_eq] at h
    constructor
    · intro e; cases e
    · intro ⟨h1, _⟩; exact absurd h1 h
  · rename_i h; simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
    cases t <;> simp [h]

/-! ## `@inline` and `@noinline` at the call site -/

/-- A source the policy can inline: a `CodeInfo`, a compressed `String`, an `IRCode`, or an
`OptimizationState`. -/
def Inlinable (s : Src) : Prop := s ≠ .other ∧ ∀ b, s ≠ .uint8 b

/-- The `@inline` and `@noinline` call-site rules of the `@inline` and `@noinline` docstrings
(base/expr.jl): the innermost call-site annotation sets its own bit and not the other one (so
"the innermost annotation has the precedence"); a call in a `@noinline` region is never inlined,
by `resolve_todo` or by `semiconcrete_result_item`, even if the callee is declared `@inline`
(except that a local result that is a constant still replaces the call, the docstring's "If the
function is trivial (for example returning a constant) it might get inlined anyway"); a call in an
`@inline` region is inlined whenever inlining is enabled and there is a source the policy reads
(and a generated function's generator can run), whatever its inlining cost, so in particular
for a callee declared `@noinline`, whose cost is `MAX_INLINE_COST` ("a callsite annotation always
has the precedence over the annotation applied to the definition"); without a call-site
annotation a semi-concrete result of a `@noinline` method is not inlined, and a source of cost
`MAX_INLINE_COST` is not inlined by `resolve_todo`. -/
def CallsiteAnnotationSpec : Prop :=
  callsiteInlineBits [] = 0 ∧
  (∀ rs, isStmtInline (callsiteInlineBits (rs ++ [true])) = true ∧
    isStmtNoinline (callsiteInlineBits (rs ++ [true])) = false) ∧
  (∀ rs, isStmtNoinline (callsiteInlineBits (rs ++ [false])) = true ∧
    isStmtInline (callsiteInlineBits (rs ++ [false])) = false) ∧
  (∀ hr sc inl flag d g m s, isStmtNoinline flag = true →
    resolveTodoDecision hr sc inl flag d g m s ≠ .inline) ∧
  (∀ inl flag dn d g m, isStmtNoinline flag = true → semiconcreteDecision inl flag dn d g m ≠ .inline) ∧
  (∀ flag d g m s, isStmtInline flag = true → isStmtNoinline flag = false → Inlinable s →
    ¬(d = true ∧ g = true ∧ m = false) →
    resolveTodoDecision true false true flag d g m s = .inline) ∧
  (∀ flag dn d g m, isStmtInline flag = true → isStmtNoinline flag = false →
    ¬(d = true ∧ g = true ∧ m = false) → semiconcreteDecision true flag dn d g m = .inline) ∧
  (∀ hr inl flag d g m s, resolveTodoDecision hr true inl flag d g m s ≠ .inline) ∧
  (∀ inl flag d g m, isStmtInline flag = false → semiconcreteDecision inl flag true d g m = .compileable) ∧
  (∀ hr inl flag d g m i, isStmtInline flag = false →
    resolveTodoDecision hr false inl flag d g m (.codeInfo MAX_INLINE_COST i) = .compileable ∧
    resolveTodoDecision hr false inl flag d g m (.compressed 255 i) = .compileable)

theorem callsiteAnnotationSpec_proven : CallsiteAnnotationSpec := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rs; simp only [callsiteInlineBits, List.getLast?_concat]; decide
  · intro rs; simp only [callsiteInlineBits, List.getLast?_concat]; decide
  · intro hr sc inl flag d g m s hn
    unfold resolveTodoDecision
    split
    · decide
    split
    · decide
    rw [if_pos (by simp [hn])]; decide
  · intro inl flag dn d g m hn
    unfold semiconcreteDecision
    rw [if_pos (by simp [hn])]; decide
  · intro flag d g m s hi hn hs hgen
    unfold resolveTodoDecision
    simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.false_or, hn]
    rw [if_pos]
    unfold srcInliningPolicyMI
    rw [if_neg (by intro hc; apply hgen; cases d <;> cases g <;> cases m <;> simp_all)]
    have := (srcInliningPolicySpec_proven).2.2.2.2.2.1 s flag hi hs.1 hs.2
    exact this
  · intro flag dn d g m hi hn hgen
    unfold semiconcreteDecision
    rw [if_neg (by simp [hi, hn])]
    rw [if_pos]
    unfold srcInliningPolicyMI
    rw [if_neg (by intro hc; apply hgen; cases d <;> cases g <;> cases m <;> simp_all)]
    rfl
  · intro hr inl flag d g m s
    unfold resolveTodoDecision
    split
    · decide
    · rw [if_pos rfl]; decide
  · intro inl flag d g m hi
    unfold semiconcreteDecision
    rw [if_pos (by simp [hi])]
  · intro hr inl flag d g m i hi
    have hpol : ∀ s, (s = .codeInfo MAX_INLINE_COST i ∨ s = .compressed 255 i) →
        srcInliningPolicyMI d g m s flag = false := by
      intro s hs
      unfold srcInliningPolicyMI
      split
      · rfl
      · rcases hs with e | e <;> subst e <;> simp [srcInliningPolicy, hi, isInlineable, inliningCost,
          jlIrInliningCost] <;> decide
    have p1 := hpol _ (Or.inl rfl)
    have p2 := hpol _ (Or.inr rfl)
    constructor <;>
    · unfold resolveTodoDecision
      repeat' split
      all_goals first | rfl | simp_all

/-! ## Exact decisions

These answer the review of `coverage/review/Compiler_src_ssair_inlining.tsv`: each states every
outcome of its function as an `iff`, so the ordinary case is pinned as well as the annotated ones.
-/

/-- The constant case of `early_inline_special_case` applies. -/
def QuotedCase (x : EarlyFacts) (f : UInt32) : Prop :=
  x.typeConst = true ∧ x.valInlineable = true ∧
    ((x.fIntrinsic = true ∧ x.pureIntrinsic = true ∧ hasFlag f IR_FLAG_NOTHROW = true) ∨
     (x.fIntrinsic = false ∧ (x.inPure = true ∨ (x.inEffectFree = true ∧ hasFlag f IR_FLAG_NOTHROW = true))))

/-- `early_inline_special_case` gets past its constant case: inlining is on, the result is not a
`Const` with a value that cannot be inlined, and the constant case does not apply. -/
def EarlyPre (x : EarlyFacts) (f : UInt32) : Prop :=
  x.inlining = true ∧ ¬(x.typeConst = true ∧ x.valInlineable = false) ∧ ¬QuotedCase x f

theorem quotedCond_iff (x : EarlyFacts) (f : UInt32) :
    quotedCond x (hasFlag f IR_FLAG_NOTHROW) = true ↔ QuotedCase x f := by
  obtain ⟨inl, tc, vi, fI, pI, iP, iE, sp, n, a1, a2, a3, a4, a5, a6, a7, a8⟩ := x
  simp only [quotedCond, QuotedCase]
  generalize hasFlag f IR_FLAG_NOTHROW = nt
  cases tc <;> cases vi <;> cases fI <;> cases pI <;> cases iP <;> cases iE <;> cases nt <;> decide

theorem specialB_iff (sp : Special) (n2 n3 n4 c sym cond tr fa bo ta eg : Bool) :
    (specialB sp n2 n3 n4 c sym cond tr fa bo ta eg = .arg3 ↔
      ((sp == .compilerbarrier && n3 && c && sym && cond) ||
        (sp == .ifelse && n4 && ((c && tr) || (!c && bo && eg)))) = true) ∧
    (specialB sp n2 n3 n4 c sym cond tr fa bo ta eg = .arg4 ↔
      (sp == .ifelse && n4 && c && !tr && fa) = true) ∧
    (specialB sp n2 n3 n4 c sym cond tr fa bo ta eg = .instanceof ↔
      (sp == .taskResultType && n2 && ta) = true) := by
  have h := specialFacts_all sp n2 n3 n4 c sym cond tr fa bo ta eg
  simp only [specialFacts, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, h3⟩, h4⟩, hi⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← beq_iff_eq.mp h3]; exact beq_iff_eq.symm
  · rw [← beq_iff_eq.mp h4]; exact beq_iff_eq.symm
  · rw [← beq_iff_eq.mp hi]; exact beq_iff_eq.symm

theorem early_other (x : EarlyFacts) (f : UInt32) (r : EarlyResult) (h1 : r ≠ .none_) (h2 : r ≠ .quotedVal) :
    earlyInlineSpecialCase x f = r ↔
      EarlyPre x f ∧ specialB x.special (x.nargtypes == 2) (x.nargtypes == 3) (x.nargtypes == 4)
        x.arg2Const x.arg2Symbol x.arg2Conditional x.arg2True x.arg2False x.arg2Bool x.arg2Task
        x.args34Egal = r := by
  rw [early_eq]
  unfold EarlyPre
  rw [← quotedCond_iff]
  cases hi : x.inlining <;> cases htc : x.typeConst <;> cases hvi : x.valInlineable <;>
    cases hq : quotedCond x (hasFlag f IR_FLAG_NOTHROW) <;> simp [Ne.symm h1, Ne.symm h2]

/-- Every outcome of `early_inline_special_case` past the constant case, as an `iff`: once the
call gets past the constant case, it returns `stmt.args[3]` exactly for
`compilerbarrier(:conditional, x)` with three argument types and for an `ifelse` with four whose
condition is `Const(true)` or a non-constant `Bool` with identical branches, `stmt.args[4]` exactly
for an `ifelse` whose condition is `Const(false)`, and the `task_result_type` result exactly for a
`Task` argument; it never gets there when inlining is off, the constant case applies, or the
result is a `Const` whose value cannot be inlined. -/
def EarlyInlineSpecialCaseExact : Prop :=
  ∀ x f,
    (earlyInlineSpecialCase x f = .arg3 ↔ EarlyPre x f ∧
      ((x.special = .compilerbarrier ∧ x.nargtypes = 3 ∧ x.arg2Const = true ∧ x.arg2Symbol = true ∧
          x.arg2Conditional = true) ∨
       (x.special = .ifelse ∧ x.nargtypes = 4 ∧
          ((x.arg2Const = true ∧ x.arg2True = true) ∨
           (x.arg2Const = false ∧ x.arg2Bool = true ∧ x.args34Egal = true))))) ∧
    (earlyInlineSpecialCase x f = .arg4 ↔ EarlyPre x f ∧
      x.special = .ifelse ∧ x.nargtypes = 4 ∧ x.arg2Const = true ∧ x.arg2True = false ∧
        x.arg2False = true) ∧
    (earlyInlineSpecialCase x f = .instanceof ↔ EarlyPre x f ∧
      x.special = .taskResultType ∧ x.nargtypes = 2 ∧ x.arg2Task = true)

theorem earlyInlineSpecialCaseExact_proven : EarlyInlineSpecialCaseExact := by
  intro x f
  have hs := specialB_iff x.special (x.nargtypes == 2) (x.nargtypes == 3) (x.nargtypes == 4)
    x.arg2Const x.arg2Symbol x.arg2Conditional x.arg2True x.arg2False x.arg2Bool x.arg2Task x.args34Egal
  refine ⟨?_, ?_, ?_⟩
  · rw [early_other x f .arg3 (by decide) (by decide), hs.1]
    cases x.special <;> cases x.arg2Const <;> simp [and_assoc]
  · rw [early_other x f .arg4 (by decide) (by decide), hs.2.1]
    cases x.special <;> cases x.arg2Const <;> simp [and_assoc]
  · rw [early_other x f .instanceof (by decide) (by decide), hs.2.2]
    cases x.special <;> simp [and_assoc]

/-- Every outcome of `handle_cases!`, as an `iff`: apart from the single fully covered, fully
handled case, it pushes a `UnionSplit` with the `handled_all_cases` and `fully_covered` it was
given exactly when there is a case or all cases are handled and `atype` and every case signature
are `DataType`s; it gives up exactly when there is a case or all cases are handled and `atype` or
some case signature is not a `DataType`; and it adds `flags_for_effects(joint_effects)` to the flag
exactly when there is no case and not all cases are handled. -/
def HandleCasesExact : Prop :=
  ∀ h fc n a sigs e flag,
    (handleCases h fc n a sigs e flag = .unionSplit h fc ↔
      ¬(fc = true ∧ h = true ∧ n = 1) ∧ (0 < n ∨ h = true) ∧ a = true ∧ ∀ s ∈ sigs, s = true) ∧
    (handleCases h fc n a sigs e flag = .none_ ↔
      ¬(fc = true ∧ h = true ∧ n = 1) ∧ (0 < n ∨ h = true) ∧ ¬(a = true ∧ ∀ s ∈ sigs, s = true)) ∧
    (handleCases h fc n a sigs e flag = .flags (flag ||| flagsForEffects e) ↔ n = 0 ∧ h = false)

theorem handleCasesExact_proven : HandleCasesExact := by
  intro h fc n a sigs e flag
  have hall : sigs.all id = true ↔ ∀ s ∈ sigs, s = true := by simp [List.all_eq_true]
  unfold handleCases
  by_cases h1 : (fc && h && n == 1) = true
  · have h1' : fc = true ∧ h = true ∧ n = 1 := by simpa [Bool.and_eq_true, and_assoc] using h1
    obtain ⟨rfl, rfl, rfl⟩ := h1'
    simp
  · have h1' : ¬(fc = true ∧ h = true ∧ n = 1) := by
      intro ⟨a1, a2, a3⟩; apply h1; simp [a1, a2, a3]
    rw [if_neg h1]
    by_cases h2 : (decide (n > 0) || h) = true
    · have h2' : 0 < n ∨ h = true := by simpa using h2
      have hn : ¬(n = 0 ∧ h = false) := by
        intro ⟨b1, b2⟩; subst b1 b2; simp at h2'
      rw [if_pos h2]
      cases a <;> by_cases h3 : sigs.all id = true <;>
        simp_all
    · have h2' : n = 0 ∧ h = false := by
        cases h
        · refine ⟨?_, rfl⟩; apply Classical.byContradiction; intro hne; apply h2; simp; omega
        · simp at h2
      rw [if_neg h2]
      simp [h2']

/-- `inline_const_if_inlineable!` gives `(true, flag)` when the type is a `Const` with an inlineable
value and `(false, flag | IR_FLAGS_REMOVABLE)` otherwise, so the flag bits outside
`IR_FLAGS_REMOVABLE` (such as `IR_FLAG_INBOUNDS`, `IR_FLAG_INLINE` and `IR_FLAG_NOINLINE`) are never
changed. -/
def InlineConstIfInlineableExact : Prop :=
  ∀ rc vi flag,
    inlineConstIfInlineable rc vi flag =
      (if rc = true ∧ vi = true then (true, flag) else (false, flag ||| IR_FLAGS_REMOVABLE)) ∧
    (∀ x : UInt32, x &&& IR_FLAGS_REMOVABLE = 0 →
      (inlineConstIfInlineable rc vi flag).2 &&& x = flag &&& x)

theorem inlineConstIfInlineableExact_proven : InlineConstIfInlineableExact := by
  intro rc vi flag
  refine ⟨?_, ?_⟩
  · unfold inlineConstIfInlineable
    cases rc <;> cases vi <;> rfl
  · intro x hx
    unfold inlineConstIfInlineable
    cases rc <;> cases vi <;> simp only [Bool.and_self, Bool.and_false, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    all_goals
      rw [← UInt32.toBitVec_inj]
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      have := congrArg (fun v : UInt32 => v.toBitVec.getLsbD i) hx
      simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or] at this ⊢
      cases hf : flag.toBitVec.getLsbD i <;> cases hx' : x.toBitVec.getLsbD i <;>
        cases hr : IR_FLAGS_REMOVABLE.toBitVec.getLsbD i <;> simp_all

/-- Every outcome of `resolve_todo`'s decision, as an `iff`: a constant local result becomes a
`ConstantCase` exactly when there is a local result and it is a constant; the call is inlined
exactly when there is a non-constant local result, inlining is on, the call site is not
`@noinline` and `src_inlining_policy` accepts the source; otherwise a compileable specialization is
used (always without a local result). In particular, without a call-site annotation, a `CodeInfo`
or compressed source is inlined exactly when its cost is not `MAX_INLINE_COST`, and an `IRCode`
always is (when a generated function's generator can run). -/
def ResolveTodoExact : Prop :=
  (∀ hr sc inl flag d g m s, resolveTodoDecision hr sc inl flag d g m s = .constant ↔
    hr = true ∧ sc = true) ∧
  (∀ hr sc inl flag d g m s, resolveTodoDecision hr sc inl flag d g m s = .inline ↔
    hr = true ∧ sc = false ∧ inl = true ∧ isStmtNoinline flag = false ∧
      srcInliningPolicyMI d g m s flag = true) ∧
  (∀ sc inl flag d g m s, resolveTodoDecision false sc inl flag d g m s = .compileable) ∧
  (∀ flag d g m c i, isStmtInline flag = false → isStmtNoinline flag = false →
    ¬(d = true ∧ g = true ∧ m = false) →
    (resolveTodoDecision true false true flag d g m (.codeInfo c i) = .inline ↔ c ≠ MAX_INLINE_COST)) ∧
  (∀ flag d g m b i, isStmtInline flag = false → isStmtNoinline flag = false →
    ¬(d = true ∧ g = true ∧ m = false) →
    (resolveTodoDecision true false true flag d g m (.compressed b i) = .inline ↔ b ≠ 255)) ∧
  (∀ flag d g m, isStmtNoinline flag = false → ¬(d = true ∧ g = true ∧ m = false) →
    resolveTodoDecision true false true flag d g m .irCode = .inline)

theorem gen_ok (d g m : Bool) (h : ¬(d = true ∧ g = true ∧ m = false)) :
    (d && g && !m) = false := by
  cases d <;> cases g <;> cases m <;> simp_all

theorem resolveTodoExact_proven : ResolveTodoExact := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hr sc inl flag d g m s
    unfold resolveTodoDecision
    cases hr <;> cases sc <;> cases inl <;> cases hn : isStmtNoinline flag <;>
      cases hp : srcInliningPolicyMI d g m s flag <;> simp [hn, hp]
  · intro hr sc inl flag d g m s
    unfold resolveTodoDecision
    cases hr <;> cases sc <;> cases inl <;> cases hn : isStmtNoinline flag <;>
      cases hp : srcInliningPolicyMI d g m s flag <;> simp [hn, hp]
  · intro sc inl flag d g m s; rfl
  · intro flag d g m c i hi hn hg
    unfold resolveTodoDecision srcInliningPolicyMI
    have := gen_ok d g m hg
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.not_false, hn, Bool.or_false]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    simp [srcInliningPolicy, hi, isInlineable, inliningCost, jlIrInliningCost]
  · intro flag d g m b i hi hn hg
    unfold resolveTodoDecision srcInliningPolicyMI
    have := gen_ok d g m hg
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.not_false, hn, Bool.or_false]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    have hc := compressed_inlineable b i
    simp only [srcInliningPolicy, hi, Bool.false_or]
    rw [hc]; simp
  · intro flag d g m hn hg
    unfold resolveTodoDecision srcInliningPolicyMI
    have := gen_ok d g m hg
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.not_false, hn, Bool.or_false]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- Every outcome of `semiconcrete_result_item`'s decision, as an `iff`: the semi-concrete `IRCode`
is inlined exactly when inlining is on, the call site is not `@noinline`, the method is not declared
`@noinline` unless the call site is `@inline`, and a generated function's generator can run;
otherwise a compileable specialization is used. It never gives a constant. In particular a call
without annotations to a method without `@noinline` is inlined. -/
def SemiconcreteExact : Prop :=
  (∀ inl flag dn d g m, semiconcreteDecision inl flag dn d g m = .inline ↔
    inl = true ∧ isStmtNoinline flag = false ∧ (dn = true → isStmtInline flag = true) ∧
      ¬(d = true ∧ g = true ∧ m = false)) ∧
  (∀ inl flag dn d g m, semiconcreteDecision inl flag dn d g m ≠ .constant) ∧
  (∀ flag d g m, isStmtNoinline flag = false → ¬(d = true ∧ g = true ∧ m = false) →
    semiconcreteDecision true flag false d g m = .inline)

theorem semiconcreteExact_proven : SemiconcreteExact := by
  refine ⟨?_, ?_, ?_⟩
  · intro inl flag dn d g m
    unfold semiconcreteDecision srcInliningPolicyMI
    cases inl <;> cases hn : isStmtNoinline flag <;> cases hi : isStmtInline flag <;> cases dn <;>
      cases d <;> cases g <;> cases m <;> simp [srcInliningPolicy]
  · intro inl flag dn d g m
    unfold semiconcreteDecision
    split
    · decide
    · split <;> decide
  · intro flag d g m hn hg
    unfold semiconcreteDecision srcInliningPolicyMI
    have := gen_ok d g m hg
    rw [if_neg (by simp [hn])]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    rfl

/-! ## Registry -/

def inlFile : String := "Compiler/src/ssair/inlining.jl"

/-- Registry entries of `Compiler/src/ssair/inlining.jl`. -/
def entries : List Entry := [
  { id := "compiler-inlining-early-special-case", juliaFile := inlFile,
    juliaFns := ["early_inline_special_case(ir::IRCode, stmt::Expr, flag::UInt32, @nospecialize(type), sig::Signature, state::InliningState)"],
    statement := "early_inline_special_case does nothing when inlining is off; replaces the call by its constant result exactly when the result is a Const with an inlineable value and the callee is a pure intrinsic on a nothrow statement, a pure builtin, or an effect-free builtin on a nothrow statement; returns stmt.args[3] exactly for compilerbarrier(:conditional, x) or an ifelse whose condition is Const(true) or a non-constant Bool with identical branches, stmt.args[4] exactly for ifelse with Const(false), and the task_result_type result exactly for a Task argument. The statement flag matters only through IR_FLAG_NOTHROW.",
    source := "comments Compiler/src/ssair/inlining.jl:1787-1797 (compilerbarrier already imposed) and the effect contracts of _PURE_BUILTINS/_EFFECT_FREE_BUILTINS",
    status := .proven, prop := ``EarlyInlineSpecialCaseSpec, thm := some ``earlyInlineSpecialCaseSpec_proven },
  { id := "compiler-inlining-handle-cases", juliaFile := inlFile,
    juliaFns := ["handle_cases!(todo::Vector{Pair{Int,Any}}, ir::IRCode, idx::Int, stmt::Expr, @nospecialize(atype), cases::Vector{InliningCase}, handled_all_cases::Bool, fully_covered::Bool, joint_effects::Effects)"],
    statement := "handle_cases! handles a single fully covered, fully handled case directly; otherwise, with any case or all cases handled, it union-splits with the handled_all_cases and fully_covered it was given, giving up when atype or a case signature is not a DataType; with nothing to inline it only adds flags_for_effects(joint_effects), keeping every flag and making the statement removable when the joint effects are removable-if-unused. The order of the cases does not matter.",
    source := "comment Compiler/src/ssair/inlining.jl:1581-1583; invariant: add_flag! only adds flags",
    status := .proven, prop := ``HandleCasesSpec, thm := some ``handleCasesSpec_proven },
  { id := "compiler-inlining-const-if-inlineable", juliaFile := inlFile,
    juliaFns := ["inline_const_if_inlineable!(inst::Instruction)"],
    statement := "inline_const_if_inlineable! replaces the statement exactly when its type is a Const with an inlineable value, leaving the flag; otherwise it keeps the statement and its flags and adds IR_FLAGS_REMOVABLE.",
    source := "the function's name; invariant: add_flag! only adds flags",
    status := .proven, prop := ``InlineConstIfInlineableSpec, thm := some ``inlineConstIfInlineableSpec_proven },
  { id := "compiler-inlining-linear-eligible", juliaFile := inlFile,
    juliaFns := ["linear_inline_eligible(ir::IRCode)"],
    statement := "linear_inline_eligible(ir) holds exactly for a one-block body whose terminator is a ReturnNode with a value.",
    source := "the function's name and its use for straight-line inlining (Compiler/src/ssair/inlining.jl:1758-1764)",
    status := .proven, prop := ``LinearInlineEligibleSpec, thm := some ``linearInlineEligibleSpec_proven },
  { id := "compiler-inlining-callsite-annotations", juliaFile := inlFile,
    juliaFns := ["resolve_todo(mi::MethodInstance, call_result::Union{Nothing,LocalInferenceResult}, call_edge::Union{Nothing,MethodInstance,CodeInstance}, @nospecialize(info::CallInfo), flag::UInt32, state::InliningState)", "semiconcrete_result_item(result::SemiConcreteResult, @nospecialize(info::CallInfo), flag::UInt32, state::InliningState)"],
    statement := "The innermost call-site annotation sets its own flag bit and not the other; a call in a @noinline region is never inlined by resolve_todo or semiconcrete_result_item; a call in an @inline region is inlined whenever inlining is on, the source is one the policy reads and a generated function's generator can run, whatever its cost (so also for a @noinline callee); a constant local result is never inlined as code; without a call-site @inline a semi-concrete result of a @noinline method is not inlined and a source of cost MAX_INLINE_COST is not inlined.",
    source := "base/expr.jl @inline and @noinline docstrings (callsite annotation has the precedence over the definition; innermost annotation has the precedence; trivial functions might get inlined anyway); comment Compiler/src/ssair/inlining.jl:1526-1528",
    status := .proven, prop := ``CallsiteAnnotationSpec, thm := some ``callsiteAnnotationSpec_proven,
    notes := "Also models src/method.c:480-483 and 612-615 (jl_code_info_set_ir's inline_flags stack). resolveTodoDecision and semiconcreteDecision are not in the difftest driver (they need a call result and inlining state); the docstring examples were run end to end on the pinned Julia instead (see difftest/compiler/inlining.jl header)." },
  { id := "compiler-inlining-early-special-case-exact", juliaFile := inlFile,
    juliaFns := ["early_inline_special_case(ir::IRCode, stmt::Expr, flag::UInt32, @nospecialize(type), sig::Signature, state::InliningState)"],
    statement := "Once inlining is on, the result is not a Const with a value that cannot be inlined and the constant case does not apply, early_inline_special_case returns stmt.args[3] exactly for compilerbarrier(:conditional, x) with three argument types and for an ifelse with four whose condition is Const(true) or a non-constant Bool with identical branches, stmt.args[4] exactly for an ifelse whose condition is Const(false), and quoted(instanceof_tfunc(type)[1]) exactly for task_result_type with a Task argument; it returns none of them otherwise.",
    source := "definition and comments Compiler/src/ssair/inlining.jl:1766-1815 (compilerbarrier already imposed a barrier, so it can be eliminated)",
    status := .proven, prop := ``EarlyInlineSpecialCaseExact, thm := some ``earlyInlineSpecialCaseExact_proven,
    notes := "Each rewrite is now an iff, so a version that never performs it fails. The guard that a non-inlineable Const result returns nothing before the rewrites is part of EarlyPre (PERF_LEADS 'inlining', model-only hypothesis)." },
  { id := "compiler-inlining-handle-cases-exact", juliaFile := inlFile,
    juliaFns := ["handle_cases!(todo::Vector{Pair{Int,Any}}, ir::IRCode, idx::Int, stmt::Expr, @nospecialize(atype), cases::Vector{InliningCase}, handled_all_cases::Bool, fully_covered::Bool, joint_effects::Effects)"],
    statement := "Apart from the single fully covered, fully handled case, handle_cases! pushes UnionSplit(handled_all_cases, fully_covered, ...) exactly when there is a case or all cases are handled and atype and every case signature are DataTypes, gives up exactly when there is a case or all cases are handled and atype or some signature is not a DataType, and adds flags_for_effects(joint_effects) to the statement flag exactly when there is no case and not all cases are handled.",
    source := "definition and comment Compiler/src/ssair/inlining.jl:1578-1596",
    status := .proven, prop := ``HandleCasesExact, thm := some ``handleCasesExact_proven },
  { id := "compiler-inlining-const-if-inlineable-exact", juliaFile := inlFile,
    juliaFns := ["inline_const_if_inlineable!(inst::Instruction)"],
    statement := "inline_const_if_inlineable! gives (true, flag) when the type is a Const with an inlineable value and (false, flag | IR_FLAGS_REMOVABLE) otherwise, so no flag bit outside IR_FLAGS_REMOVABLE (IR_FLAG_INBOUNDS, IR_FLAG_INLINE, IR_FLAG_NOINLINE, ...) ever changes.",
    source := "definition Compiler/src/ssair/inlining.jl:1699-1707; add_flag!(inst, flag) is inst[:flag] |= flag (Compiler/src/ssair/ir.jl)",
    status := .proven, prop := ``InlineConstIfInlineableExact, thm := some ``inlineConstIfInlineableExact_proven },
  { id := "compiler-inlining-resolve-todo-exact", juliaFile := inlFile,
    juliaFns := ["resolve_todo(mi::MethodInstance, call_result::Union{Nothing,LocalInferenceResult}, call_edge::Union{Nothing,MethodInstance,CodeInstance}, @nospecialize(info::CallInfo), flag::UInt32, state::InliningState)"],
    statement := "resolve_todo returns a ConstantCase exactly when there is a local result and it is a constant, inlines exactly when there is a non-constant local result, inlining is on, the call site is not @noinline and src_inlining_policy accepts the source, and otherwise uses a compileable specialization (always when there is no local result). Without call-site annotations and with a generator that can run (or none), a CodeInfo or compressed source is inlined exactly when its cost is not MAX_INLINE_COST (its byte is not 0xff), and an IRCode always is.",
    source := "definition and comments Compiler/src/ssair/inlining.jl:860-900; base/expr.jl @inline/@noinline docstrings",
    status := .proven, prop := ``ResolveTodoExact, thm := some ``resolveTodoExact_proven,
    notes := "The decision only; the edge bookkeeping and the returned IR are not modelled (resolveTodoDecision is not in the difftest driver; the docstring examples were run end to end instead, see compiler-inlining-callsite-annotations)." },
  { id := "compiler-inlining-semiconcrete-exact", juliaFile := inlFile,
    juliaFns := ["semiconcrete_result_item(result::SemiConcreteResult, @nospecialize(info::CallInfo), flag::UInt32, state::InliningState)"],
    statement := "semiconcrete_result_item inlines the semi-concrete IRCode exactly when inlining is on, the call site is not @noinline, the method is not declared @noinline unless the call site is @inline, and a generated function's generator can run (or there is none); otherwise it uses a compileable specialization, never a constant. In particular an unannotated call to a method without @noinline is inlined.",
    source := "definition and comment Compiler/src/ssair/inlining.jl:1517-1538 (suppress the inlining of a @noinline method unless inlining is requested at the callsite)",
    status := .proven, prop := ``SemiconcreteExact, thm := some ``semiconcreteExact_proven,
    notes := "The decision only; not in the difftest driver (it needs a SemiConcreteResult and an inlining state)." }
]

end JuliaLean.Proofs.Compiler.src.ssair.inlining

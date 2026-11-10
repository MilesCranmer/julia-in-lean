import JuliaLean.Registry.Types
import JuliaLean.Compiler.src.optimize
import JuliaLean.Proofs.Compiler.src.optimize.Common
import JuliaLean.Proofs.Compiler.src.optimize.Encoding
import JuliaLean.Proofs.Compiler.src.optimize.Cost

/-!
Properties of the inlining cost model and the statement-flag encoding of
`Compiler/src/optimize.jl`, of the threshold logic of `Compiler/src/typeinfer.jl` and of the cost
encoding of `src/ircode.c` it uses.

The cost and threshold properties are in `optimize/Cost.lean`, the exhaustive checks of the 8-bit
cost encoding in `optimize/Encoding.lean`; this file has the flag and source properties and the
registry entries.
-/

namespace JuliaLean.Proofs.Compiler.src.optimize

open JuliaLean.Registry
open JuliaLean JuliaLean.Compiler JuliaLean.Compiler.Optimize

/-! ## Flag constants -/

/-- The single-bit `IR_FLAG_*` constants, in source order. -/
def irFlags : List UInt32 :=
  [IR_FLAG_INBOUNDS, IR_FLAG_INLINE, IR_FLAG_NOINLINE, IR_FLAG_CONSISTENT, IR_FLAG_EFFECT_FREE,
   IR_FLAG_NOTHROW, IR_FLAG_TERMINATES, IR_FLAG_NOUB, IR_FLAG_NORTCALL, IR_FLAG_RESET_SAFE,
   IR_FLAG_REFINED, IR_FLAG_UNUSED, IR_FLAG_EFIIMO, IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM, IR_FLAG_RSIIMO]

/-- The statement flags and the source flags do not collide: every `IR_FLAG_*` is one bit and no
two share it; the three flags below `NUM_IR_FLAGS` are exactly `INBOUNDS`, `INLINE` and
`NOINLINE` (the bits `decode_statement_effects_override` skips) and every other flag is above
them; `IR_FLAGS_REMOVABLE` is part of `IR_FLAGS_EFFECTS` and `IR_FLAGS_NEEDS_EA` is disjoint from
it; the C definitions of `IR_FLAG_INBOUNDS` and `IR_FLAG_RESET_SAFE` agree; the `SLOT_*` flags are
distinct bits; the two `SRC_FLAG_DECLARED_*` values are distinct, nonzero and fit the 2-bit
`inlining` field of the compressed IR; and `MIN_INLINE_COST < MAX_INLINE_COST`. -/
def IrFlagsDistinct : Prop :=
  (∀ f ∈ irFlags, f ≠ 0 ∧ f &&& (f - 1) = 0) ∧
  irFlags.Pairwise (fun a b => a &&& b = 0) ∧
  IR_FLAG_INBOUNDS ||| IR_FLAG_INLINE ||| IR_FLAG_NOINLINE = ((1 : UInt32) <<< NUM_IR_FLAGS.toUInt32) - 1 ∧
  (∀ f ∈ irFlags.drop 3, (1 : UInt32) <<< NUM_IR_FLAGS.toUInt32 ≤ f) ∧
  IR_FLAGS_REMOVABLE &&& ~~~IR_FLAGS_EFFECTS = 0 ∧
  IR_FLAGS_NEEDS_EA &&& IR_FLAGS_EFFECTS = 0 ∧
  C_IR_FLAG_INBOUNDS = IR_FLAG_INBOUNDS ∧ C_IR_FLAG_RESET_SAFE = IR_FLAG_RESET_SAFE ∧
  [SLOT_STATICUNDEF, SLOT_ASSIGNEDONCE, SLOT_USEDUNDEF].Pairwise (fun a b => a &&& b = 0) ∧
  SRC_FLAG_DECLARED_INLINE ≠ SRC_FLAG_DECLARED_NOINLINE ∧ SRC_FLAG_DECLARED_INLINE ≠ 0 ∧
  SRC_FLAG_DECLARED_NOINLINE ≠ 0 ∧ SRC_FLAG_DECLARED_INLINE &&& 3 = SRC_FLAG_DECLARED_INLINE ∧
  SRC_FLAG_DECLARED_NOINLINE &&& 3 = SRC_FLAG_DECLARED_NOINLINE ∧
  MIN_INLINE_COST < MAX_INLINE_COST

theorem irFlagsDistinct_proven : IrFlagsDistinct := by unfold IrFlagsDistinct; decide

/-- The comment at Compiler/src/optimize.jl:44 says bit 15 is "Reserved: one(UInt32) << 15 used
for RSIIMO below". -/
def RsiimoAtReservedBit : Prop := IR_FLAG_RSIIMO = (1 : UInt32) <<< 15

/-- `IR_FLAG_RSIIMO` is bit 20; no flag uses bit 15. -/
theorem rsiimoAtReservedBit_refuted : ¬ RsiimoAtReservedBit := by unfold RsiimoAtReservedBit; decide

theorem no_flag_at_15 : ∀ f ∈ irFlags, f ≠ (1 : UInt32) <<< 15 := by decide

/-! ## `has_flag`, `is_stmt_inline`, `is_stmt_noinline` -/

/-- `has_flag(curr, flag)` holds exactly when every bit of `flag` is set in `curr`; so it splits
over `|`, holds for the empty flag and after `curr | flag`, and ignores bits disjoint from
`flag`. `is_stmt_inline` and `is_stmt_noinline` read their own bit only: setting one, or any
effect bit, does not change the other. -/
def HasFlagSpec : Prop :=
  (∀ c f : UInt32, hasFlag c f = true ↔
    ∀ i, f.toBitVec.getLsbD i = true → c.toBitVec.getLsbD i = true) ∧
  (∀ c f g : UInt32, hasFlag c (f ||| g) = (hasFlag c f && hasFlag c g)) ∧
  (∀ c : UInt32, hasFlag c 0 = true) ∧
  (∀ c f : UInt32, hasFlag (c ||| f) f = true) ∧
  (∀ c x f : UInt32, x &&& f = 0 → hasFlag (c ||| x) f = hasFlag c f) ∧
  (∀ c x : UInt32, x &&& IR_FLAG_INLINE = 0 → isStmtInline (c ||| x) = isStmtInline c) ∧
  (∀ c x : UInt32, x &&& IR_FLAG_NOINLINE = 0 → isStmtNoinline (c ||| x) = isStmtNoinline c) ∧
  (∀ c : UInt32, isStmtInline (c ||| IR_FLAG_INLINE) = true ∧ isStmtNoinline (c ||| IR_FLAG_NOINLINE) = true) ∧
  IR_FLAG_NOINLINE &&& IR_FLAG_INLINE = 0 ∧ IR_FLAGS_EFFECTS &&& (IR_FLAG_INLINE ||| IR_FLAG_NOINLINE) = 0

theorem hasFlagSpec_proven : HasFlagSpec :=
  ⟨hasFlag_iff, hasFlag_or, hasFlag_zero, hasFlag_self_or, hasFlag_or_disjoint,
   fun c x h => hasFlag_or_disjoint c x _ h, fun c x h => hasFlag_or_disjoint c x _ h,
   fun c => ⟨hasFlag_self_or c _, hasFlag_self_or c _⟩, by decide, by decide⟩

/-! ## `iscallstmt` -/

/-- `iscallstmt` is true exactly for an `Expr` with head `:call`, `:invoke`, `:foreigncall` or
`:foreignglobal`. -/
def IscallstmtSpec : Prop :=
  iscallstmt none = false ∧
  ∀ h : String, iscallstmt (some h) = true ↔ h ∈ ["call", "invoke", "foreigncall", "foreignglobal"]

theorem iscallstmtSpec_proven : IscallstmtSpec := by
  refine ⟨rfl, fun h => ?_⟩
  simp only [iscallstmt, Bool.or_eq_true, beq_iff_eq, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, or_assoc]

/-! ## `flags_for_effects` -/

/-- The body of `flags_for_effects` on the answers of the ten queries it makes. -/
def ffeB (cons ef efI rs rsI nt te iam nu nr : Bool) : UInt32 :=
  let f : UInt32 := 0
  let f := if cons then f ||| IR_FLAG_CONSISTENT else f
  let f := if ef then f ||| IR_FLAG_EFFECT_FREE else if efI then f ||| IR_FLAG_EFIIMO else f
  let f := if rs && ef then f ||| IR_FLAG_RESET_SAFE else if rsI && efI then f ||| IR_FLAG_RSIIMO else f
  let f := if nt then f ||| IR_FLAG_NOTHROW else f
  let f := if te then f ||| IR_FLAG_TERMINATES else f
  let f := if iam then f ||| IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM else f
  let f := if nu then f ||| IR_FLAG_NOUB else f
  let f := if nr then f ||| IR_FLAG_NORTCALL else f
  f

theorem ffe_eq (e : Effects) : flagsForEffects e =
    ffeB (isConsistent e) (isEffectFree e) (isEffectFreeIfInaccessiblememonly e) (isResetSafe e)
      (isResetSafeIfInaccessiblememonly e) (isNothrow e) (isTerminates e)
      (isInaccessiblememOrArgmemonly e) (isNoub e) (isNortcall e) := rfl

/-- The non-effect bits `flags_for_effects` must not set. -/
def nonEffectBits : UInt32 :=
  IR_FLAG_INBOUNDS ||| IR_FLAG_INLINE ||| IR_FLAG_NOINLINE ||| IR_FLAG_REFINED ||| IR_FLAG_UNUSED

def ffeFacts (cons ef efI rs rsI nt te iam nu nr : Bool) : Bool :=
  let f := ffeB cons ef efI rs rsI nt te iam nu nr
  hasFlag f IR_FLAG_CONSISTENT == cons && hasFlag f IR_FLAG_EFFECT_FREE == ef &&
  hasFlag f IR_FLAG_EFIIMO == (!ef && efI) && hasFlag f IR_FLAG_RESET_SAFE == (rs && ef) &&
  hasFlag f IR_FLAG_RSIIMO == (!(rs && ef) && rsI && efI) && hasFlag f IR_FLAG_NOTHROW == nt &&
  hasFlag f IR_FLAG_TERMINATES == te && hasFlag f IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM == iam &&
  hasFlag f IR_FLAG_NOUB == nu && hasFlag f IR_FLAG_NORTCALL == nr &&
  hasFlag f IR_FLAGS_REMOVABLE == (ef && te && nt) && f &&& nonEffectBits == 0

theorem ffeFacts_all : ∀ a b c d e f g h i j : Bool, ffeFacts a b c d e f g h i j = true := by
  decide +kernel

/-- Each statement flag `flags_for_effects` sets is the effect query its comment names
(Compiler/src/optimize.jl:19-57): `CONSISTENT`, `EFFECT_FREE`, `NOTHROW`, `TERMINATES`,
`INACCESSIBLEMEM_OR_ARGMEM`, `NOUB`, `NORTCALL` exactly when the query holds; `EFIIMO` only for a
conditional effect_free; `RESET_SAFE` only together with effect_free and `RSIIMO` only for the
conditional pair otherwise. `IR_FLAGS_REMOVABLE` is set exactly when `is_removable_if_unused`
holds, and no non-effect flag (`INBOUNDS`, `INLINE`, `NOINLINE`, `REFINED`, `UNUSED`) is set. -/
def FlagsForEffectsSpec : Prop :=
  ∀ e : Effects,
    hasFlag (flagsForEffects e) IR_FLAG_CONSISTENT = isConsistent e ∧
    hasFlag (flagsForEffects e) IR_FLAG_EFFECT_FREE = isEffectFree e ∧
    hasFlag (flagsForEffects e) IR_FLAG_EFIIMO =
      (!isEffectFree e && isEffectFreeIfInaccessiblememonly e) ∧
    hasFlag (flagsForEffects e) IR_FLAG_RESET_SAFE = (isResetSafe e && isEffectFree e) ∧
    hasFlag (flagsForEffects e) IR_FLAG_RSIIMO =
      (!(isResetSafe e && isEffectFree e) && isResetSafeIfInaccessiblememonly e &&
        isEffectFreeIfInaccessiblememonly e) ∧
    hasFlag (flagsForEffects e) IR_FLAG_NOTHROW = isNothrow e ∧
    hasFlag (flagsForEffects e) IR_FLAG_TERMINATES = isTerminates e ∧
    hasFlag (flagsForEffects e) IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM = isInaccessiblememOrArgmemonly e ∧
    hasFlag (flagsForEffects e) IR_FLAG_NOUB = isNoub e ∧
    hasFlag (flagsForEffects e) IR_FLAG_NORTCALL = isNortcall e ∧
    hasFlag (flagsForEffects e) IR_FLAGS_REMOVABLE = isRemovableIfUnused e ∧
    flagsForEffects e &&& nonEffectBits = 0

theorem flagsForEffectsSpec_proven : FlagsForEffectsSpec := by
  intro e
  have := ffeFacts_all (isConsistent e) (isEffectFree e) (isEffectFreeIfInaccessiblememonly e)
    (isResetSafe e) (isResetSafeIfInaccessiblememonly e) (isNothrow e) (isTerminates e)
    (isInaccessiblememOrArgmemonly e) (isNoub e) (isNortcall e)
  simp only [ffeFacts, Bool.and_eq_true, beq_iff_eq] at this
  rw [ffe_eq]
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := this
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_, h12⟩
  rw [h11]; simp only [isRemovableIfUnused]

/-! ## Sources and `src_inlining_policy` -/

theorem u8_lt4 (i : UInt8) (h : i.toNat < 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 := by omega
  rcases this with h | h | h | h
  · exact Or.inl (UInt8.toNat_inj.mp h)
  · exact Or.inr (Or.inl (UInt8.toNat_inj.mp h))
  · exact Or.inr (Or.inr (Or.inl (UInt8.toNat_inj.mp h)))
  · exact Or.inr (Or.inr (Or.inr (UInt8.toNat_inj.mp h)))

theorem and3_of_lt4 (i : UInt8) (h : i.toNat < 4) : i &&& 3 = i := by
  rcases u8_lt4 i h with e | e | e | e <;> subst e <;> decide

/-- A compressed cost byte is inlineable exactly when it is not `0xff`. -/
theorem compressed_inlineable (b i : UInt8) : isInlineable (.compressed b i) = (b != 255) := by
  show (jlDecodeInliningCost b != MAX_INLINE_COST) = (b != 255)
  by_cases hb : b = 255
  · subst hb; decide
  · have hlt : b.toNat < 255 := by
      have := b.toNat_lt
      have : b.toNat ≠ 255 := fun e => hb (UInt8.toNat_inj.mp (by rw [e]; rfl))
      omega
    have h1 := dec_mono b 254 (by show b.toNat ≤ 254; omega)
    rw [dec_top.1] at h1
    have hne : jlDecodeInliningCost b ≠ MAX_INLINE_COST := by
      intro e; rw [e] at h1; simp [MAX_INLINE_COST] at h1
    rw [bne_iff_ne.mpr hne, bne_iff_ne.mpr hb]

/-- `src_inlining_policy` follows the documented rules: an `OptimizationState` is judged by its
`CodeInfo`, an `IRCode` is always inlineable, and anything other than a `CodeInfo`, a compressed
`String` or an `IRCode` (including a bare cost byte) never is. A `CodeInfo` or compressed source is
inlineable when the call site is `@inline` or its cost is not `MAX_INLINE_COST`; so `@inline` at
the call site overrides any cost. The method-instance method refuses a generated function whose
generator cannot be invoked, even at an `@inline` call site, and otherwise defers to the source.
Compressing a `CodeInfo` whose cost came from `inline_cost_clamp` or `set_inlineable!` keeps the
policy, `is_inlineable`, `is_declared_inline` and `is_declared_noinline` unchanged (for the
`inlining` values 0-3 the 2-bit field holds). A compressed cost is inlineable exactly when its
byte is not `0xff`, and `set_inlineable!(src, val)` makes `is_inlineable(src) == val`. -/
def SrcInliningPolicySpec : Prop :=
  (∀ c i f, srcInliningPolicy (.optState c i) f = srcInliningPolicy (.codeInfo c i) f) ∧
  (∀ f, srcInliningPolicy .irCode f = true) ∧
  (∀ f, srcInliningPolicy .other f = false ∧ ∀ b, srcInliningPolicy (.uint8 b) f = false) ∧
  (∀ c i f, srcInliningPolicy (.codeInfo c i) f = (isStmtInline f || inliningCost (.codeInfo c i) != MAX_INLINE_COST)) ∧
  (∀ b i f, srcInliningPolicy (.compressed b i) f = (isStmtInline f || inliningCost (.compressed b i) != MAX_INLINE_COST)) ∧
  (∀ s f, isStmtInline f = true → s ≠ .other → (∀ b, s ≠ .uint8 b) → srcInliningPolicy s f = true) ∧
  (∀ d g m s f, d = true → g = true → m = false → srcInliningPolicyMI d g m s f = false) ∧
  (∀ d g m s f, ¬(d = true ∧ g = true ∧ m = false) → srcInliningPolicyMI d g m s f = srcInliningPolicy s f) ∧
  (∀ (x : JI) i f, i.toNat < 4 →
    srcInliningPolicy (compressCodeInfo (inlineCostClamp x) i) f = srcInliningPolicy (.codeInfo (inlineCostClamp x) i) f ∧
    isInlineable (compressCodeInfo (inlineCostClamp x) i) = isInlineable (.codeInfo (inlineCostClamp x) i)) ∧
  (∀ v i f, i.toNat < 4 →
    srcInliningPolicy (compressCodeInfo (setInlineable v) i) f = srcInliningPolicy (.codeInfo (setInlineable v) i) f ∧
    isInlineable (compressCodeInfo (setInlineable v) i) = v ∧ isInlineable (.codeInfo (setInlineable v) i) = v) ∧
  (∀ c i, i.toNat < 4 →
    isDeclaredInline (compressCodeInfo c i) = isDeclaredInline (.codeInfo c i) ∧
    isDeclaredNoinline (compressCodeInfo c i) = isDeclaredNoinline (.codeInfo c i)) ∧
  (∀ b i, isInlineable (.compressed b i) = (b != 255))

theorem srcInliningPolicySpec_proven : SrcInliningPolicySpec := by
  refine ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ => ⟨rfl, fun _ => rfl⟩, fun _ _ _ => rfl,
    fun _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, compressed_inlineable⟩
  · intro s f hf h1 h2
    cases s with
    | codeInfo c i => simp [srcInliningPolicy, hf]
    | compressed b i => simp [srcInliningPolicy, hf]
    | uint8 b => exact absurd rfl (h2 b)
    | irCode => rfl
    | optState c i => simp [srcInliningPolicy, hf]
    | other => exact absurd rfl h1
  · intro d g m s f hd hg hm; subst hd hg hm; rfl
  · intro d g m s f h
    unfold srcInliningPolicyMI
    rw [if_neg]
    intro hc
    apply h
    cases d <;> cases g <;> cases m <;> simp_all
  · intro x i f _
    have h := clamp_roundtrip x
    simp only [compressCodeInfo, srcInliningPolicy, isInlineable, inliningCost, jlIrInliningCost,
      Option.getD_some, h, and_self]
  · intro v i f _
    have h0 := and3_of_lt4 i (by assumption)
    cases v
    · refine ⟨rfl, ?_, ?_⟩ <;> rfl
    · refine ⟨rfl, ?_, ?_⟩ <;> rfl
  · intro c i hi
    simp only [compressCodeInfo, isDeclaredInline, isDeclaredNoinline, jlIrFlagInlining,
      and3_of_lt4 i hi, and_self]

/-! ## `is_result_constabi_eligible` -/

/-- A result is const-ABI eligible exactly when it is a `Const` with an inlineable value whose
effects are foldable and nothrow: consistent, effect-free, terminating, `noub` (or
`noub_if_noinbounds`) and nothrow. -/
def ConstabiEligibleSpec : Prop :=
  ∀ (k v : Bool) (e : Effects), isResultConstabiEligible k e v = true ↔
    (k = true ∧ v = true ∧ isConsistent e = true ∧ isEffectFree e = true ∧ isTerminates e = true ∧
      (isNoub e = true ∨ isNoubIfNoinbounds e = true) ∧ isNothrow e = true)

theorem constabiEligibleSpec_proven : ConstabiEligibleSpec := by
  intro k v e
  simp only [isResultConstabiEligible, isFoldableNothrow, isFoldable, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_false, true_or, and_true]
  constructor
  · intro ⟨⟨hk, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hv⟩
    exact ⟨hk, hv, h1, h3, h4, h2, h5⟩
  · intro ⟨hk, hv, h1, h3, h4, h2, h5⟩
    exact ⟨⟨hk, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hv⟩

/-! ## Registry -/

def optFile : String := "Compiler/src/optimize.jl"

/-- Registry entries of `Compiler/src/optimize.jl`. -/
def entries : List Entry := [
  { id := "compiler-inlining-ir-flags-distinct", juliaFile := optFile,
    juliaFns := ["IR_FLAG_*", "IR_FLAGS_EFFECTS", "IR_FLAGS_REMOVABLE", "IR_FLAGS_NEEDS_EA", "SLOT_*", "SRC_FLAG_DECLARED_INLINE", "SRC_FLAG_DECLARED_NOINLINE", "MAX_INLINE_COST", "MIN_INLINE_COST"],
    statement := "Every IR_FLAG_* constant is a single bit and no two share one; the bits below NUM_IR_FLAGS are exactly INBOUNDS, INLINE and NOINLINE and every other flag is above them; IR_FLAGS_REMOVABLE is inside IR_FLAGS_EFFECTS and IR_FLAGS_NEEDS_EA is disjoint from it; the C IR_FLAG_INBOUNDS and IR_FLAG_RESET_SAFE match; the SLOT_* flags are distinct bits; the SRC_FLAG_DECLARED_* values are distinct, nonzero and fit the 2-bit inlining field; MIN_INLINE_COST < MAX_INLINE_COST.",
    source := "comment Compiler/src/optimize.jl:16 (sync the flag definitions with julia.h and method.c); src/julia_internal.h:2314-2316; src/julia.h:380",
    status := .proven, prop := ``IrFlagsDistinct, thm := some ``irFlagsDistinct_proven,
    notes := "No collision like EFFECT_FREE_GLOBALLY in the effects encoding. The comment at optimize.jl:44 about bit 15 is stale (compiler-inlining-rsiimo-reserved-comment); no flag uses bit 15 (no_flag_at_15)." },
  { id := "compiler-inlining-rsiimo-reserved-comment", juliaFile := optFile,
    juliaFns := ["IR_FLAG_RSIIMO"],
    statement := "IR_FLAG_RSIIMO is one(UInt32) << 15, the bit the comment at Compiler/src/optimize.jl:44 reserves for it.",
    source := "comment Compiler/src/optimize.jl:44 (Reserved: one(UInt32) << 15 used for RSIIMO below)",
    status := .refuted, prop := ``RsiimoAtReservedBit, thm := some ``rsiimoAtReservedBit_refuted,
    issue := "none found (queries: IR_FLAG_RSIIMO; RSIIMO reserved bit 15; IR_FLAG_RESET_SAFE RSIIMO; issues and prs)",
    notes := "Documentation only: IR_FLAG_RSIIMO is bit 20 (optimize.jl:57) and bit 15 is unused. Same on master eb844b8ebd." },
  { id := "compiler-inlining-has-flag", juliaFile := optFile,
    juliaFns := ["has_flag(curr::UInt32, flag::UInt32)", "is_stmt_inline(stmt_flag::UInt32)", "is_stmt_noinline(stmt_flag::UInt32)"],
    statement := "has_flag(curr, flag) holds exactly when every bit of flag is set in curr; it splits over |, holds for 0 and after curr | flag, and ignores bits disjoint from flag. is_stmt_inline and is_stmt_noinline read only their own bit, so setting the other one or any effect bit does not change them.",
    source := "invariant: has_flag tests a set of statement flags (Compiler/src/optimize.jl:73); @inline/@noinline call-site flags (src/method.c:612-615)",
    status := .proven, prop := ``HasFlagSpec, thm := some ``hasFlagSpec_proven },
  { id := "compiler-inlining-iscallstmt", juliaFile := optFile,
    juliaFns := ["iscallstmt(@nospecialize stmt)"],
    statement := "iscallstmt is true exactly for an Expr with head :call, :invoke, :foreigncall or :foreignglobal.",
    source := "the function's name and its use for statements that make calls (Compiler/src/optimize.jl:75-79)",
    status := .proven, prop := ``IscallstmtSpec, thm := some ``iscallstmtSpec_proven },
  { id := "compiler-inlining-flags-for-effects", juliaFile := optFile,
    juliaFns := ["flags_for_effects(effects::Effects)"],
    statement := "For every Effects, each flag flags_for_effects sets is the query its comment names: CONSISTENT, EFFECT_FREE, NOTHROW, TERMINATES, INACCESSIBLEMEM_OR_ARGMEM, NOUB and NORTCALL exactly when the query holds; EFIIMO only for a conditional effect_free; RESET_SAFE exactly when reset_safe and effect_free; RSIIMO only for the conditional pair otherwise. IR_FLAGS_REMOVABLE is set exactly when is_removable_if_unused holds, and no non-effect flag is set.",
    source := "comments Compiler/src/optimize.jl:19-57 and 91-99",
    status := .proven, prop := ``FlagsForEffectsSpec, thm := some ``flagsForEffectsSpec_proven,
    notes := "The flag of EFFECT_FREE_GLOBALLY statements is the effects area's compiler-effects-effect-free-globally-collision (is_effect_free_if_inaccessiblememonly reads it as conditional)." },
  { id := "compiler-inlining-cost-clamp", juliaFile := optFile,
    juliaFns := ["inline_cost_clamp(x::Int)"],
    statement := "inline_cost_clamp(x) is in MIN_INLINE_COST:MAX_INLINE_COST for every Int, is monotone and idempotent, never lowers a cost in 10:3968 and raises it there by at most 1/32, and its result survives the 8-bit encoding jl_compress_ir stores.",
    source := "invariant: the clamp prepares a cost for the compressed 8-bit field (src/ircode.c:1234 comment: range 0..3968, rounding up)",
    status := .proven, prop := ``InlineCostClampSpec, thm := some ``inlineCostClampSpec_proven,
    notes := "Uses the exhaustive facts of optimize/Encoding.lean: jl_decode(jl_encode(c)) >= c and <= c*33/32 for c <= 3968, == 0xffff above, exact below 64; jl_encode monotone; jl_encode(jl_decode(b)) == b; jl_decode strictly increasing. Smoke-tested on the pinned Julia over -200:70000 and the Int extremes." },
  { id := "compiler-inlining-clamp-finite-to-max", juliaFile := optFile,
    juliaFns := ["inline_cost_clamp(x::Int)"],
    statement := "inline_cost_clamp never turns a finite cost below MAX_INLINE_COST into MAX_INLINE_COST, the never-inline marker.",
    source := "definition: is_inlineable(src) = inlining_cost(src) != MAX_INLINE_COST (Compiler/src/optimize.jl:127); inline_cost_model compares the body cost with the threshold before clamping (optimize.jl:1932-1943)",
    status := .refuted, prop := ``ClampFiniteStaysFinite, thm := some ``clampFiniteStaysFinite_refuted,
    issue := "none found (queries: inline_cost_clamp; inline_cost_threshold 3968; jl_encode_inlining_cost; inlining cost encoding MAX_INLINE_COST; inline_cost_threshold large not inlined; issues and prs)",
    notes := "Every cost in 3969:65534 decodes to 0xffff. Not reachable with default OptimizationParams (the largest threshold, an @inline iterate with a tuple return, is 2650); with inline_cost_threshold raised above 3968, every body costing 3969 up to the threshold is reported non-inlineable and its optimized source can be discarded. Same on master eb844b8ebd." },
  { id := "compiler-inlining-statement-cost-nonneg", juliaFile := optFile,
    juliaFns := ["statement_cost(ex::Expr, line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)"],
    statement := "statement_cost is non-negative whenever inline_nonleaf_penalty and the tfunc table costs are non-negative, of any size (typemax(Int) included), on statements inference produces (no assignment to a global has an Expr right side).",
    source := "comment Compiler/src/optimize.jl:1787 (plus_saturate: inputs are non-negative)",
    status := .proven, prop := ``StatementCostNonneg, thm := some ``statementCostNonneg_proven,
    notes := "The precondition is needed: a hand-built `G = f(x)` with a global G and penalty typemax(Int) costs 3 + typemax(Int), which wraps negative (statementCost_global_assign_wraps). Lowering emits Core.setglobal! for `global G = f(x)` (also at top level; pinned, nightly, 1.13.3), and the global-write reformulation stores `p = val` with a BindingPartition p and the value operand val (optimize.jl:1446-1447; seen as `Main.G = %1` in optimized IR), never an Expr." },
  { id := "compiler-inlining-statement-cost-bounds", juliaFile := optFile,
    juliaFns := ["statement_cost(ex::Expr, line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)", "statement_or_branch_cost(@nospecialize(stmt), line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)"],
    statement := "For inline_nonleaf_penalty and table costs in 0:2^62 and statements of lowered code (an assignment's right side is not an assignment), statement_cost returns a cost in 0:2^62+3, and statement_or_branch_cost a non-negative cost.",
    source := "comment Compiler/src/optimize.jl:1787 (plus_saturate: inputs are non-negative)",
    status := .proven, prop := ``StatementCostNonnegOrdinary, thm := some ``statementCostNonnegOrdinary_proven,
    notes := "sobc_nonneg covers statement_or_branch_cost (backward branches 40, try typemax(Int)). Smoke-tested: 1044 statements of Base code, all non-negative." },
  { id := "compiler-inlining-statement-cost-nothrow", juliaFile := optFile,
    juliaFns := ["statement_cost(ex::Expr, line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)"],
    statement := "statement_cost returns a cost, without throwing, for every statement inference produces.",
    source := "invariant: the cost model runs on every IR inference produces, and an exception there is an internal error",
    status := .refuted, prop := ``StatementCostNoThrow, thm := some ``statementCostNoThrow_refuted,
    issue := "none found (queries recorded in bugs/compiler-inlining-typeassert-one-arg.yaml)",
    notes := "Bug compiler-inlining-typeassert-one-arg: a one-argument Core.typeassert call reads ex.args[3]. The ordinary case is compiler-inlining-statement-cost-nothrow-binary. Same on master eb844b8ebd." },
  { id := "compiler-inlining-statement-cost-nothrow-binary", juliaFile := optFile,
    juliaFns := ["statement_cost(ex::Expr, line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)"],
    statement := "statement_cost returns a cost, without throwing, for every statement whose typeassert calls have their two arguments.",
    source := "invariant: the cost model runs on every IR inference produces",
    status := .proven, prop := ``StatementCostNoThrowOrdinary, thm := some ``statementCostNoThrowOrdinary_proven },
  { id := "compiler-inlining-llvmcall-cost", juliaFile := optFile,
    juliaFns := ["statement_cost(ex::Expr, line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)"],
    statement := "An llvmcall whose argument count is within its T_IFUNC arity is charged its table cost T_IFUNC_COST, as the `f === Intrinsics.llvmcall` branch intends.",
    source := "comment Compiler/src/optimize.jl:1822 (llvmcall holds malformed IR, so argextype will crash on it) and add_tfunc(Core.Intrinsics.llvmcall, 3, INT_INF, llvmcall_tfunc, 10) (tfuncs.jl:329)",
    status := .refuted, prop := ``LlvmcallTableCost, thm := some ``llvmcallTableCost_refuted,
    issue := "none found (queries: llvmcall inlining cost; llvmcall statement_cost; INT_INF maxarg overflow; T_IFUNC maxarg + 1; issues and prs)",
    notes := "maxarg + 1 wraps to typemin(Int) for INT_INF, so the arity test fails and every llvmcall costs UNKNOWN_CALL_COST = 20; the llvmcall test is dead. No other intrinsic has INT_INF arity. Same on master eb844b8ebd." },
  { id := "compiler-inlining-cost-model-closed-form", juliaFile := optFile,
    juliaFns := ["inline_cost_model(ir::IRCode, params::OptimizationParams, cost_threshold::Int)", "statement_costs!(cost::Vector{Int}, body::Vector{Any}, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)", "plus_saturate(x::Int, y::Int)"],
    statement := "For statements of lowered code, a penalty in 0:2^62 and a threshold in 0:2^62-1: when statement_costs! computes the costs cs of an IRCode, inline_cost_model(ir, params, t) is MAX_INLINE_COST if the exact sum of cs exceeds t and inline_cost_clamp(sum) otherwise; statement_costs! writes one cost per statement and returns the largest (or 0).",
    source := "invariant: inline_cost_model sums the statement costs (comment optimize.jl:1787: saturating sum) and the two functions price statements with the same statement_or_branch_cost",
    status := .proven, prop := ``CostModelClosedForm, thm := some ``costModelClosedForm_proven,
    notes := "plus_saturate is not a true saturating sum (typemax(Int)-1 plus 5 gives typemax(Int)-1), but below a threshold < 2^62 the early exit makes this invisible. Smoke-tested: 120 (function, threshold) pairs on the pinned Julia." },
  { id := "compiler-inlining-cost-model-append-monotone", juliaFile := optFile,
    juliaFns := ["inline_cost_model(ir::IRCode, params::OptimizationParams, cost_threshold::Int)", "plus_saturate(x::Int, y::Int)"],
    statement := "Adding statements at the end of a body never lowers its inlining cost, for any statements, penalty and threshold.",
    source := "invariant: a larger body is no cheaper to inline",
    status := .proven, prop := ``CostModelAppendMonotone, thm := some ``costModelAppendMonotone_proven,
    notes := "Holds without sign assumptions because plus_saturate(x, y) >= x. Inserting a statement elsewhere renumbers the lines the branch costs compare with, which the model takes as input." },
  { id := "compiler-inlining-cost-model-order", juliaFile := optFile,
    juliaFns := ["inline_cost_model(ir::IRCode, params::OptimizationParams, cost_threshold::Int)", "statement_cost(ex::Expr, line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)"],
    statement := "For a branch-free body of lowered code, a penalty in 0:2^62 and a threshold in 0:2^62-1, the inlining cost does not depend on the order of the statements.",
    source := "invariant: the cost is a sum of statement costs",
    status := .proven, prop := ``CostModelOrderIndependent, thm := some ``costModelOrderIndependent_proven,
    notes := "Requires every statement's cost to be computable: with the one-argument typeassert bug, an expensive statement placed before it hides the BoundsError behind the early exit, so the outcome then depends on order." },
  { id := "compiler-inlining-try-not-inlineable", juliaFile := optFile,
    juliaFns := ["statement_or_branch_cost(@nospecialize(stmt), line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)", "inline_cost_model(ir::IRCode, params::OptimizationParams, cost_threshold::Int)"],
    statement := "A body containing an EnterNode (try/catch) always gets MAX_INLINE_COST from inline_cost_model, for any threshold below typemax(Int).",
    source := "comment Compiler/src/optimize.jl:1923-1926 (don't inline functions with try/catch)",
    status := .proven, prop := ``EnterNeverInlineable, thm := some ``enterNeverInlineable_proven },
  { id := "compiler-inlining-declared-inline-threshold", juliaFile := "Compiler/src/typeinfer.jl",
    juliaFns := ["inline_cost_model(interp::AbstractInterpreter, result::InferenceResult, inline_flag::UInt8, ir::IRCode)"],
    statement := "A @noinline method, a toplevel thunk and a non-Tuple signature always get MAX_INLINE_COST; an @inline method with a dispatch-tuple signature always gets MIN_INLINE_COST; @inline raises the threshold by 19*default (to 20x); and for parameters up to 2^56 an @inline declaration never gives a higher cost than no declaration.",
    source := "base/expr.jl @inline/@noinline docstrings; comments Compiler/src/typeinfer.jl:524 (obey @inline declaration) and 533 (increase the cost threshold 20x)",
    status := .proven, prop := ``InlineCostModelDeclared, thm := some ``inlineCostModelDeclared_proven,
    notes := "Above typemax(Int)/20 the threshold sum wraps (threshold_wraps: default 2^59 gives a negative threshold, so every @inline body is uninlineable); recorded as a lead, not a bug." },
  { id := "compiler-inlining-threshold-overflow", juliaFile := "Compiler/src/typeinfer.jl",
    juliaFns := ["inline_cost_model(interp::AbstractInterpreter, result::InferenceResult, inline_flag::UInt8, ir::IRCode)"],
    statement := "The threshold inline_cost_model passes on is never below inline_cost_threshold, since every adjustment adds a non-negative amount (inline_tupleret_bonus, 19*default, 4*default).",
    source := "comments Compiler/src/typeinfer.jl:533 (increase the cost threshold 20x) and 537 (a few functions get special treatment)",
    status := .refuted, prop := ``ThresholdAtLeastDefault, thm := some ``thresholdAtLeastDefault_refuted,
    issue := "related #60121 (closed, not merged: avoid overflow when inline_cost_threshold == typemax(Int); JuliaGPU/AMDGPU.jl#846) (queries: inline_cost_threshold; inline_cost_threshold typemax; inline_cost_threshold overflow; cost_threshold 19*default; issues and prs)",
    notes := "With inline_cost_threshold = typemax(Int), which GPUCompiler sets to force inlining, a method returning a non-concrete Tuple gets typemax(Int)+250, an @inline method typemax(Int)+19*typemax(Int), and Base.iterate/cconvert/unsafe_convert +4*typemax(Int); each wraps, and a negative threshold makes the method uninlineable. The ordinary range (parameters up to 2^56) is compiler-inlining-declared-inline-threshold. Unchanged on master eb844b8ebd." },
  { id := "compiler-inlining-src-policy", juliaFile := optFile,
    juliaFns := ["src_inlining_policy(::AbstractInterpreter, @nospecialize(src), @nospecialize(info::CallInfo), stmt_flag::UInt32)", "src_inlining_policy(interp::AbstractInterpreter, mi::MethodInstance, @nospecialize(src), @nospecialize(info::CallInfo), stmt_flag::UInt32)", "inlining_cost(@nospecialize src)", "is_inlineable(@nospecialize src)", "set_inlineable!(src::CodeInfo, val::Bool)", "is_declared_inline(@nospecialize src::MaybeCompressed)", "is_declared_noinline(@nospecialize src::MaybeCompressed)"],
    statement := "src_inlining_policy unwraps an OptimizationState, always accepts IRCode, rejects anything but CodeInfo/String/IRCode, and accepts a CodeInfo or compressed source when the call site is @inline or its cost is not MAX_INLINE_COST; the method-instance method refuses a generated function whose generator cannot run, even at an @inline call site. Compressing a CodeInfo whose cost came from inline_cost_clamp or set_inlineable! leaves the policy, is_inlineable, is_declared_inline and is_declared_noinline unchanged; a compressed cost is inlineable exactly when its byte is not 0xff; set_inlineable!(src, val) makes is_inlineable(src) == val.",
    source := "base/expr.jl @inline docstring (a callsite annotation will try to force inlining regardless of the cost model); comments Compiler/src/optimize.jl:156-157; invariant: compression keeps the inlining decision",
    status := .proven, prop := ``SrcInliningPolicySpec, thm := some ``srcInliningPolicySpec_proven,
    notes := "A bare UInt8 cost byte has an inlining_cost but is never accepted by the policy (it is not MaybeCompressed)." },
  { id := "compiler-inlining-constabi-eligible", juliaFile := "Compiler/src/typeinfer.jl",
    juliaFns := ["is_result_constabi_eligible(result::InferenceResult)"],
    statement := "A result is const-ABI eligible exactly when it is a Const with an inlineable value and its effects are consistent, effect-free, terminating, noub or noub_if_noinbounds, and nothrow.",
    source := "invariant: the constant ABI replaces the call by its value (Compiler/src/typeinfer.jl:483-486)",
    status := .proven, prop := ``ConstabiEligibleSpec, thm := some ``constabiEligibleSpec_proven }
]

end JuliaLean.Proofs.Compiler.src.optimize

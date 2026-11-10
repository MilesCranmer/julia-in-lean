import JuliaLean.Registry.Types
import JuliaLean.Proofs.Compiler.src.optimize

/-!
Exact statements for the source queries, the statement-flag queries and the statement costs of
`Compiler/src/optimize.jl`: the value each one gives on every kind of input, branch by branch.
They answer the review of `coverage/review/Compiler_src_optimize.tsv`, which found that the
earlier entries for these functions only bound or compare their results.
-/

namespace JuliaLean.Proofs.Compiler.src.optimize

open JuliaLean JuliaLean.Compiler JuliaLean.Compiler.Optimize

/-! ## `inlining_cost` and `is_inlineable` -/

theorem dec_small (b : UInt8) (h : b.toNat < 32) : jlDecodeInliningCost b = b.toUInt16 := by
  unfold jlDecodeInliningCost
  have h1 : (b == 255) = false := by
    apply beq_false_of_ne; intro e; subst e; simp at h
  have h2 : b.toNat >>> 5 = 0 := by rw [Nat.shiftRight_eq_div_pow]; omega
  simp [h1, h2]

/-- `inlining_cost(src)` on each kind of source: the `inlining_cost` field of a `CodeInfo`, the
decoded cost byte of a compressed `String` or of a bare `UInt8`, and `MAX_INLINE_COST` for
anything else (an `IRCode`, an `OptimizationState`, `nothing`). A byte below 32 decodes to
itself, the byte `0xff` to `MAX_INLINE_COST`, and compressing a `CodeInfo` whose cost is below 64
keeps the cost exactly. -/
def InliningCostExact : Prop :=
  (∀ c i, inliningCost (.codeInfo c i) = c) ∧
  (∀ b i, inliningCost (.compressed b i) = jlDecodeInliningCost b) ∧
  (∀ b, inliningCost (.uint8 b) = jlDecodeInliningCost b) ∧
  inliningCost .irCode = MAX_INLINE_COST ∧
  (∀ c i, inliningCost (.optState c i) = MAX_INLINE_COST) ∧
  inliningCost .other = MAX_INLINE_COST ∧
  (∀ b i, b.toNat < 32 →
    inliningCost (.uint8 b) = b.toUInt16 ∧ inliningCost (.compressed b i) = b.toUInt16) ∧
  (∀ i, inliningCost (.uint8 255) = MAX_INLINE_COST ∧ inliningCost (.compressed 255 i) = MAX_INLINE_COST) ∧
  (∀ c i, c.toNat < 64 → inliningCost (compressCodeInfo c i) = c)

theorem inliningCostExact_proven : InliningCostExact := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl, fun _ _ => rfl, rfl, ?_, ?_, ?_⟩
  · intro b i h; exact ⟨dec_small b h, dec_small b h⟩
  · intro i; exact ⟨rfl, rfl⟩
  · intro c i h
    show jlDecodeInliningCost (jlEncodeInliningCost c) = c
    exact UInt16.toNat_inj.mp (dec_enc_small c h)

/-- `is_inlineable(src)` on each kind of source: a `CodeInfo` exactly when its cost is not
`MAX_INLINE_COST`, a compressed `String` or a bare `UInt8` exactly when the cost byte is not
`0xff`, and never an `IRCode`, an `OptimizationState` or `nothing`. -/
def IsInlineableExact : Prop :=
  (∀ c i, isInlineable (.codeInfo c i) = (c != MAX_INLINE_COST)) ∧
  (∀ b i, isInlineable (.compressed b i) = (b != 255)) ∧
  (∀ b, isInlineable (.uint8 b) = (b != 255)) ∧
  isInlineable .irCode = false ∧
  (∀ c i, isInlineable (.optState c i) = false) ∧
  isInlineable .other = false

theorem isInlineableExact_proven : IsInlineableExact := by
  refine ⟨fun _ _ => rfl, compressed_inlineable, ?_, rfl, fun _ _ => rfl, rfl⟩
  intro b
  exact compressed_inlineable b 0

/-! ## `is_declared_inline` and `is_declared_noinline` -/

/-- `is_declared_inline(src)` is true exactly when the source's `inlining` field is
`SRC_FLAG_DECLARED_INLINE`, and `is_declared_noinline(src)` exactly when it is
`SRC_FLAG_DECLARED_NOINLINE`, for a `CodeInfo` and for a compressed `String`; every other source
is a `MethodError`. So the field values 0 (no declaration), 1 (`@inline`) and 2 (`@noinline`) give
(false, false), (true, false) and (false, true), and compressing a `CodeInfo` keeps both answers. -/
def DeclaredInlineExact : Prop :=
  (∀ c i, isDeclaredInline (.codeInfo c i) = .ok (i == SRC_FLAG_DECLARED_INLINE) ∧
    isDeclaredNoinline (.codeInfo c i) = .ok (i == SRC_FLAG_DECLARED_NOINLINE)) ∧
  (∀ b i, isDeclaredInline (.compressed b i) = .ok (i == SRC_FLAG_DECLARED_INLINE) ∧
    isDeclaredNoinline (.compressed b i) = .ok (i == SRC_FLAG_DECLARED_NOINLINE)) ∧
  (∀ s, (∀ c i, s ≠ .codeInfo c i) → (∀ b i, s ≠ .compressed b i) →
    isDeclaredInline s = .error (.methodError "is_declared_inline") ∧
    isDeclaredNoinline s = .error (.methodError "is_declared_noinline")) ∧
  (∀ c, isDeclaredInline (.codeInfo c 0) = .ok false ∧ isDeclaredNoinline (.codeInfo c 0) = .ok false ∧
    isDeclaredInline (.codeInfo c 1) = .ok true ∧ isDeclaredNoinline (.codeInfo c 1) = .ok false ∧
    isDeclaredInline (.codeInfo c 2) = .ok false ∧ isDeclaredNoinline (.codeInfo c 2) = .ok true) ∧
  (∀ c i, i.toNat < 4 →
    isDeclaredInline (compressCodeInfo c i) = .ok (i == SRC_FLAG_DECLARED_INLINE) ∧
    isDeclaredNoinline (compressCodeInfo c i) = .ok (i == SRC_FLAG_DECLARED_NOINLINE))

theorem declaredInlineExact_proven : DeclaredInlineExact := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, ?_, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · intro s h1 h2
    cases s with
    | codeInfo c i => exact absurd rfl (h1 c i)
    | compressed b i => exact absurd rfl (h2 b i)
    | uint8 _ => exact ⟨rfl, rfl⟩
    | irCode => exact ⟨rfl, rfl⟩
    | optState _ _ => exact ⟨rfl, rfl⟩
    | other => exact ⟨rfl, rfl⟩
  · intro c i hi
    have e : compressCodeInfo c i = .compressed (jlEncodeInliningCost c) i := by
      unfold compressCodeInfo; rw [and3_of_lt4 i hi]
    rw [e]; exact ⟨rfl, rfl⟩

/-! ## `is_stmt_inline` and `is_stmt_noinline` -/

theorem inline_bit (i : Nat) : IR_FLAG_INLINE.toBitVec.getLsbD i = (i == 1) := by
  have e : IR_FLAG_INLINE.toBitVec = BitVec.ofNat 32 (2 ^ 1) := by decide
  rw [e, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  by_cases h : i = 1
  · subst h; rfl
  · have h' : ¬ (1 = i) := fun e => h e.symm
    simp [h, h']

theorem noinline_bit (i : Nat) : IR_FLAG_NOINLINE.toBitVec.getLsbD i = (i == 2) := by
  have e : IR_FLAG_NOINLINE.toBitVec = BitVec.ofNat 32 (2 ^ 2) := by decide
  rw [e, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  by_cases h : i = 2
  · subst h; rfl
  · have h' : ¬ (2 = i) := fun e => h e.symm
    simp [h, h']

theorem isStmtInline_bit (f : UInt32) : isStmtInline f = f.toBitVec.getLsbD 1 := by
  apply Bool.eq_iff_iff.mpr
  unfold isStmtInline; rw [hasFlag_iff]
  constructor
  · intro h; exact h 1 (by rw [inline_bit]; rfl)
  · intro h i hi; rw [inline_bit] at hi; simp at hi; subst hi; exact h

theorem isStmtNoinline_bit (f : UInt32) : isStmtNoinline f = f.toBitVec.getLsbD 2 := by
  apply Bool.eq_iff_iff.mpr
  unfold isStmtNoinline; rw [hasFlag_iff]
  constructor
  · intro h; exact h 2 (by rw [noinline_bit]; rfl)
  · intro h i hi; rw [noinline_bit] at hi; simp at hi; subst hi; exact h

theorem bit_of_and_zero (f n : UInt32) (i : Nat) (h : f &&& n = 0) (hn : n.toBitVec.getLsbD i = true) :
    f.toBitVec.getLsbD i = false := by
  have := congrArg (fun v : UInt32 => v.toBitVec.getLsbD i) h
  simp only [UInt32.toBitVec_and, BitVec.getLsbD_and, hn, Bool.and_true] at this
  simpa using this

/-- `is_stmt_inline(flag)` is bit 1 of the flag and `is_stmt_noinline(flag)` is bit 2, the bits
`jl_code_info_set_ir` sets for a call-site `@inline` and `@noinline` (src/method.c:612-615). So both
are false for a statement without flags and for every flag set `flags_for_effects` produces, and
each is false for the other's flag. -/
def StmtInlineExact : Prop :=
  (∀ f : UInt32, isStmtInline f = f.toBitVec.getLsbD 1) ∧
  (∀ f : UInt32, isStmtNoinline f = f.toBitVec.getLsbD 2) ∧
  isStmtInline 0 = false ∧ isStmtNoinline 0 = false ∧
  isStmtInline IR_FLAG_INLINE = true ∧ isStmtNoinline IR_FLAG_INLINE = false ∧
  isStmtInline IR_FLAG_NOINLINE = false ∧ isStmtNoinline IR_FLAG_NOINLINE = true ∧
  (∀ e, isStmtInline (flagsForEffects e) = false ∧ isStmtNoinline (flagsForEffects e) = false)

theorem stmtInlineExact_proven : StmtInlineExact := by
  refine ⟨isStmtInline_bit, isStmtNoinline_bit, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  intro e
  have h := (flagsForEffectsSpec_proven e).2.2.2.2.2.2.2.2.2.2.2
  rw [isStmtInline_bit, isStmtNoinline_bit]
  exact ⟨bit_of_and_zero _ _ 1 h (by decide), bit_of_and_zero _ _ 2 h (by decide)⟩

/-! ## `statement_cost` -/

theorem argAt_of (c : CallFacts) (i : Nat) (a : ArgFacts) (h1 : 2 ≤ i) (h2 : i ≤ c.nargs)
    (ha : c.args[i - 2]? = some (some a)) : argAt c i = .ok a := by
  unfold argAt
  rw [if_neg (by omega), ha]; rfl

theorem argAt_short (c : CallFacts) (i : Nat) (h : c.nargs < i) : argAt c i = .error .boundsError := by
  unfold argAt
  rw [if_pos (Or.inr h)]; rfl

theorem div2_exact (a : JI) (h0 : 1 ≤ a.val) : JInt.div (a - ji 1) (ji 2) = .ok (ji ((a.val - 1) / 2)) := by
  have hb := ji_bounds a
  have hs : (a - ji 1).val = a.val - 1 := by
    show wrapInt .i64 (a.val - (ji 1).val) = _
    rw [ji_val 1 (by decide) (by decide)]; exact wrap64_of _ (by omega) (by omega)
  have h2 : (ji 2).val = 2 := ji_val 2 (by decide) (by decide)
  unfold JInt.div
  rw [if_neg (by rw [h2]; decide), if_neg (by rw [h2]; simp)]
  rw [hs, h2, Int.tdiv_eq_ediv_of_nonneg (by omega)]
  rfl

/-- The argument loop of the intrinsic case, on fully supplied arguments `as`: `none` when some
argument is not a dispatch element, else `n` plus the number of constant concrete arguments. -/
theorem icc_exact (c : CallFacts) (as : List ArgFacts) (has : c.args = as.map some)
    (hn : c.nargs = as.length + 1) :
    ∀ k i (n : Int), 2 ≤ i → i - 2 + k = as.length →
      intrinsicConstCount c k i n =
        .ok (if (as.drop (i - 2)).all (·.dispatchelem) then
          some (n + ((as.drop (i - 2)).countP (·.constConcrete) : Int)) else none) := by
  intro k
  induction k with
  | zero =>
    intro i n _ hk
    have e : as.drop (i - 2) = [] := List.drop_eq_nil_of_le (by omega)
    rw [e]; simp [intrinsicConstCount, pure, Except.pure]
  | succ k ih =>
    intro i n hi hk
    have hl : i - 2 < as.length := by omega
    have ha : argAt c i = .ok as[i - 2] := by
      apply argAt_of c i _ hi (by omega)
      rw [has, List.getElem?_map, List.getElem?_eq_getElem hl]; rfl
    have hd : as.drop (i - 2) = as[i - 2] :: as.drop (i - 2 + 1) := List.drop_eq_getElem_cons hl
    have e : i + 1 - 2 = i - 2 + 1 := by omega
    simp only [intrinsicConstCount, ha, bind, Except.bind]
    rw [ih (i + 1) _ (by omega) (by omega), hd, e, List.all_cons, List.countP_cons]
    cases hde : (as[i - 2]).dispatchelem
    · simp [pure, Except.pure]
    · cases hcc : (as[i - 2]).constConcrete
      · simp [pure, Except.pure]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and, Int.natCast_add]
        split <;> simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] <;> omega

/-- `statement_cost(ex, line, ...)` on each branch, for every penalty `p` and line `l`. A
`:meta`-like head costs 0, a `:foreigncall` 20 (1 for `jl_string_ptr`), a `:foreignglobal` 1, an
`:invoke` 20 (0 when its result type is `Union{}`), an assignment 3 to a global and 0 otherwise
plus the cost of an `Expr` right side priced with line `-1`, a `:copyast` 100 and any other head
0. A `:call` is priced by its recovered callee: `getfield`, `tuple` and `getglobal` cost 0;
`memoryrefget`, `const_memoryrefget` and `memoryref_isassigned` cost 1, and `memoryrefset!` and
`memoryrefunset!` 5, when the memory argument's type is known and `p` otherwise; a `typeassert` of
a constant type costs 1 and with one argument throws a `BoundsError`; any other builtin costs its
`T_FFUNC_COST` entry, or 20 without one; a non-builtin call or `invoke` costs `p` (0 when its
result is `Union{}`); an intrinsic costs 20 when it has no `T_IFUNC` entry or its argument count is
outside the entry's arity, its table cost `k` when `k` is 0, it has fewer than two arguments, it is
`llvmcall` or an argument is not a dispatch element, and `(k - 1) ÷ 2` when at least one argument
is a constant and at most one is not. -/
def StatementCostExact : Prop :=
  (∀ p l, statementCost p .metaHead l = .ok (ji 0)) ∧
  (∀ p sp l, statementCost p (.foreigncall sp) l = .ok (if sp then ji 1 else ji 20)) ∧
  (∀ p l, statementCost p .foreignglobal l = .ok (ji 1)) ∧
  (∀ p rb l, statementCost p (.invoke rb) l = .ok (if l ≠ -1 ∧ rb = true then ji 0 else ji 20)) ∧
  (∀ p g l, statementCost p (.assign g) l = .ok (if g then ji 3 else ji 0)) ∧
  (∀ p g rhs l, statementCost p (.assignExpr g rhs) l =
    (fun v => (if g then ji 3 else ji 0) + v) <$> statementCost p rhs (-1)) ∧
  (∀ p l, statementCost p .copyast l = .ok (ji 100)) ∧
  (∀ p l, statementCost p .other l = .ok (ji 0)) ∧
  (∀ c, resolveCallee c = if c.ftypIntrinsic && c.fargSSA && c.defRecoverable then c.c1 else c.c0) ∧
  (∀ p c l k t, resolveCallee c = .builtin k t → (k = .getfield ∨ k = .tuple ∨ k = .getglobal) →
    statementCost p (.call c) l = .ok (ji 0)) ∧
  (∀ p c l k t a, resolveCallee c = .builtin k t →
    (k = .memoryrefget ∨ k = .constMemoryrefget ∨ k = .memoryrefIsassigned) →
    3 ≤ c.nargs → c.args[0]? = some (some a) →
    statementCost p (.call c) l = .ok (if a.known then ji 1 else p)) ∧
  (∀ p c l k t a, resolveCallee c = .builtin k t → (k = .memoryrefset ∨ k = .memoryrefunset) →
    3 ≤ c.nargs → c.args[0]? = some (some a) →
    statementCost p (.call c) l = .ok (if a.known then ji 5 else p)) ∧
  (∀ p c l t a, resolveCallee c = .builtin .typeassert t → 3 ≤ c.nargs → c.args[1]? = some (some a) →
    statementCost p (.call c) l = .ok (if a.constType then ji 1 else t.getD UNKNOWN_CALL_COST)) ∧
  (∀ p c l t, resolveCallee c = .builtin .typeassert t → c.nargs < 3 →
    statementCost p (.call c) l = .error .boundsError) ∧
  (∀ p c l k t, resolveCallee c = .builtin k t →
    k ≠ .invoke → k ≠ .getfield → k ≠ .tuple → k ≠ .getglobal → k ≠ .typeassert →
    ((k = .memoryrefget ∨ k = .constMemoryrefget ∨ k = .memoryrefIsassigned ∨ k = .memoryrefset ∨
      k = .memoryrefunset) → c.nargs < 3) →
    statementCost p (.call c) l = .ok (t.getD UNKNOWN_CALL_COST)) ∧
  (∀ p c l, (∃ t, resolveCallee c = .builtin .invoke t) ∨ resolveCallee c = .other →
    statementCost p (.call c) l = .ok (if l ≠ -1 ∧ c.retBottom = true then ji 0 else p)) ∧
  (∀ p c l mi ma k ll, resolveCallee c = .intrinsic false mi ma k ll →
    statementCost p (.call c) l = .ok UNKNOWN_CALL_COST) ∧
  (∀ p c l mi ma k ll, resolveCallee c = .intrinsic true mi ma k ll →
    ¬((mi + ji 1).val ≤ c.nargs ∧ (c.nargs : Int) ≤ (ma + ji 1).val) →
    statementCost p (.call c) l = .ok UNKNOWN_CALL_COST) ∧
  (∀ p c l mi ma k ll, resolveCallee c = .intrinsic true mi ma k ll →
    (mi + ji 1).val ≤ c.nargs ∧ (c.nargs : Int) ≤ (ma + ji 1).val →
    (k.val = 0 ∨ c.nargs < 3 ∨ ll = true) →
    statementCost p (.call c) l = .ok k) ∧
  (∀ p c l mi ma k (as : List ArgFacts), resolveCallee c = .intrinsic true mi ma k false →
    (mi + ji 1).val ≤ c.nargs ∧ (c.nargs : Int) ≤ (ma + ji 1).val →
    1 ≤ k.val → 3 ≤ c.nargs → c.args = as.map some → c.nargs = as.length + 1 →
    statementCost p (.call c) l =
      .ok (if as.all (·.dispatchelem) = true ∧ 0 < as.countP (·.constConcrete) ∧
          c.nargs ≤ as.countP (·.constConcrete) + 2
        then ji ((k.val - 1) / 2) else k))

theorem statementCostExact_proven : StatementCostExact := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, ?_, fun _ _ _ => rfl, ?_, fun _ _ => rfl,
    fun _ _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p rb l
    by_cases hl : l = -1
    · subst hl; simp [statementCost, pure, Except.pure, UNKNOWN_CALL_COST]
    · simp [statementCost, hl, pure, Except.pure, UNKNOWN_CALL_COST]
  · intro p g rhs l
    simp only [statementCost, bind, Except.bind]
    cases statementCost p rhs (-1) <;> rfl
  · intro p c l k t hr hk
    simp only [statementCost, hr]
    rcases hk with rfl | rfl | rfl <;> rfl
  · intro p c l k t a hr hk h3 ha
    have hA : argAt c 2 = .ok a := argAt_of c 2 a (by omega) (by omega) ha
    simp only [statementCost, hr]
    rcases hk with rfl | rfl | rfl <;>
      simp [hA, h3, bind, Except.bind, pure, Except.pure]
  · intro p c l k t a hr hk h3 ha
    have hA : argAt c 2 = .ok a := argAt_of c 2 a (by omega) (by omega) ha
    simp only [statementCost, hr]
    rcases hk with rfl | rfl <;>
      simp [hA, h3, bind, Except.bind, pure, Except.pure]
  · intro p c l t a hr h3 ha
    have hA : argAt c 3 = .ok a := argAt_of c 3 a (by omega) (by omega) ha
    simp only [statementCost, hr]
    cases t <;> cases hct : a.constType <;> simp [hA, hct, bind, Except.bind, pure, Except.pure, UNKNOWN_CALL_COST]
  · intro p c l t hr h3
    have hA := argAt_short c 3 h3
    simp only [statementCost, hr]
    simp [hA, bind, Except.bind]
  · intro p c l k t hr h1 h2 h3 h4 h5 hm
    simp only [statementCost, hr]
    cases k <;> simp_all [pure, Except.pure] <;>
      first | (rw [if_neg (by omega)]; cases t <;> rfl) | (cases t <;> rfl)
  · intro p c l h
    rcases h with ⟨t, hr⟩ | hr <;> simp only [statementCost, hr] <;>
      by_cases hl : l = -1 <;> simp [hl, pure, Except.pure]
  · intro p c l mi ma k ll hr
    simp only [statementCost, hr]; rfl
  · intro p c l mi ma k ll hr har
    simp only [statementCost, hr]
    simp [har, pure, Except.pure]
  · intro p c l mi ma k ll hr har hq
    simp only [statementCost, hr]
    have hq' : (k.val == 0) = true ∨ (c.nargs : Int) < 3 ∨ ll = true := by
      rcases hq with h | h | h
      · simp [h]
      · exact Or.inr (Or.inl (by omega))
      · simp [h]
    rw [if_pos trivial, if_pos har, if_pos hq']
    rfl
  · intro p c l mi ma k as hr har hk h3 has hn
    simp only [statementCost, hr]
    rw [if_pos trivial, if_pos har, if_neg (by
      intro h; rcases h with h | h | h
      · simp at h; omega
      · omega
      · cases h)]
    rw [icc_exact c as has hn (c.nargs - 1) 2 0 (by omega) (by omega)]
    simp only [bind, Except.bind, Nat.sub_self, List.drop_zero, Int.zero_add]
    by_cases hall : as.all (·.dispatchelem) = true
    · rw [if_pos hall]
      dsimp only
      by_cases hc : 0 < as.countP (·.constConcrete) ∧ c.nargs ≤ as.countP (·.constConcrete) + 2
      · obtain ⟨hc1, hc2⟩ := hc
        rw [if_pos (show ((as.countP (·.constConcrete) : Nat) : Int) > 0 ∧
            ((as.countP (·.constConcrete) : Nat) : Int) + 2 ≥ (c.nargs : Int) from ⟨by omega, by omega⟩),
          if_pos ⟨hall, hc1, hc2⟩]
        exact div2_exact k hk
      · rw [if_neg (show ¬ (((as.countP (·.constConcrete) : Nat) : Int) > 0 ∧
            ((as.countP (·.constConcrete) : Nat) : Int) + 2 ≥ (c.nargs : Int)) from by
              intro h; obtain ⟨h1, h2⟩ := h; exact hc ⟨by omega, by omega⟩),
          if_neg (by intro h; exact hc h.2)]; rfl
    · rw [if_neg hall, if_neg (by intro h; exact hall h.1)]; rfl

/-! ## `statement_or_branch_cost` -/

/-- `statement_or_branch_cost(stmt, line, src, ...)` on each kind of statement: an `Expr` costs
its `statement_cost`; a `GotoNode` or `GotoIfNot` costs 40 when its target is before `line` and 0
otherwise, the target being the label itself in a `CodeInfo` and the first statement of block
`label` in an `IRCode`, where a label that names no block is a `BoundsError`; an `EnterNode` costs
`typemax(Int)` and any other statement 0. -/
def StatementOrBranchCostExact : Prop :=
  (∀ isIR bf p e l, statementOrBranchCost isIR bf p (.expr e) l = statementCost p e l) ∧
  (∀ bf p t l, statementOrBranchCost false bf p (.goto t) l = .ok (if t < l then ji 40 else ji 0) ∧
    statementOrBranchCost false bf p (.gotoifnot t) l = .ok (if t < l then ji 40 else ji 0)) ∧
  (∀ bf p t l d, 1 ≤ t → bf[t.toNat - 1]? = some d →
    statementOrBranchCost true bf p (.goto t) l = .ok (if d < l then ji 40 else ji 0) ∧
    statementOrBranchCost true bf p (.gotoifnot t) l = .ok (if d < l then ji 40 else ji 0)) ∧
  (∀ bf p t l, (t < 1 ∨ bf[t.toNat - 1]? = none) →
    statementOrBranchCost true bf p (.goto t) l = .error .boundsError ∧
    statementOrBranchCost true bf p (.gotoifnot t) l = .error .boundsError) ∧
  (∀ isIR bf p l, statementOrBranchCost isIR bf p .enter l = .ok (JInt.typemax .i64)) ∧
  (∀ isIR bf p l, statementOrBranchCost isIR bf p .other l = .ok (ji 0))

theorem statementOrBranchCostExact_proven : StatementOrBranchCostExact := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ => ⟨rfl, rfl⟩, ?_, ?_, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩
  · intro bf p t l d h1 hd
    have e : branchDst true bf t = .ok d := by
      unfold branchDst; rw [if_neg (by decide), if_neg (by omega), hd]; rfl
    simp only [statementOrBranchCost, e]
    exact ⟨rfl, rfl⟩
  · intro bf p t l h
    have e : branchDst true bf t = .error .boundsError := by
      unfold branchDst; rw [if_neg (by decide)]
      by_cases h1 : t < 1
      · rw [if_pos h1]; rfl
      · rw [if_neg h1]
        rcases h with h | h
        · exact absurd h h1
        · rw [h]; rfl
    simp only [statementOrBranchCost, e]
    exact ⟨rfl, rfl⟩

/-! ## `statement_costs!` -/

/-- The loop of `statement_costs!` from line `n` with running maximum `m0`. -/
theorem costsLoop_exact (isIR : Bool) (bf : List Int) (p : JI) :
    ∀ (body : List Stmt) (n : Nat) (m0 : JI),
      statementCostsLoop isIR bf p body (n : Int) m0 =
        (fun cs => (cs, cs.foldl (fun a c => if c > a then c else a) m0)) <$>
          (body.zip ((List.range' n body.length).map (fun k : Nat => (k : Int)))).mapM
            (fun q => statementOrBranchCost isIR bf p q.1 q.2) := by
  intro body
  induction body with
  | nil => intro n m0; rfl
  | cons s rest ih =>
    intro n m0
    have e : ((n : Int) + 1) = ((n + 1 : Nat) : Int) := by omega
    simp only [statementCostsLoop, List.length_cons, List.range'_succ, List.map_cons, List.zip_cons_cons,
      List.mapM_cons]
    simp only [e, ih (n + 1)]
    cases statementOrBranchCost isIR bf p s (n : Int) with
    | error _ => rfl
    | ok c =>
      simp only [bind, Except.bind]
      cases List.mapM (fun q => statementOrBranchCost isIR bf p q.1 q.2)
          (rest.zip ((List.range' (n + 1) rest.length).map (fun k : Nat => (k : Int)))) with
      | error _ => rfl
      | ok cs => rfl

/-- `statement_costs!(cost, body, ...)` writes `cost[line] = statement_or_branch_cost(body[line],
line, ...)` for `line = 1:length(body)`, in order (so the first statement whose cost throws
decides the exception), and returns the largest of those costs, or 0 when none is positive. -/
def StatementCostsExact : Prop :=
  ∀ isIR bf p body, statementCosts isIR bf p body =
    (fun cs => (cs, cs.foldl (fun a c => if c > a then c else a) (ji 0))) <$>
      (body.zip ((List.range' 1 body.length).map (fun k : Nat => (k : Int)))).mapM
        (fun q => statementOrBranchCost isIR bf p q.1 q.2)

theorem statementCostsExact_proven : StatementCostsExact := by
  intro isIR bf p body
  exact costsLoop_exact isIR bf p body 1 (ji 0)


/-! ## Registry -/

open JuliaLean.Registry in
/-- Registry entries of the exact statements for `Compiler/src/optimize.jl`. -/
def exactEntries : List Entry := [
  { id := "compiler-inlining-inlining-cost-exact", juliaFile := optFile,
    juliaFns := ["inlining_cost(@nospecialize src)"],
    statement := "inlining_cost(src) is the inlining_cost field of a CodeInfo, the decoded cost byte of a compressed String or of a bare UInt8, and MAX_INLINE_COST for an IRCode, an OptimizationState, nothing or anything else; a byte below 32 decodes to itself, 0xff to MAX_INLINE_COST, and compressing a CodeInfo with cost below 64 keeps the cost exactly.",
    source := "definition Compiler/src/optimize.jl:125-126 with jl_ir_inlining_cost (src/ircode.c:1266-1275); comment src/ircode.c:1233 (full accuracy over 0..63)",
    status := .proven, prop := ``InliningCostExact, thm := some ``inliningCostExact_proven,
    notes := "Checked on the pinned Julia by difftest/compiler/inlining_props.jl (all 256 UInt8 bytes, CodeInfo and compressed String at the encoding edges, nothing, an Int and an IRCode)." },
  { id := "compiler-inlining-is-inlineable-exact", juliaFile := optFile,
    juliaFns := ["is_inlineable(@nospecialize src)"],
    statement := "is_inlineable(src) holds for a CodeInfo exactly when its cost is not MAX_INLINE_COST, for a compressed String or a bare UInt8 exactly when the cost byte is not 0xff, and never for an IRCode, an OptimizationState or nothing.",
    source := "definition Compiler/src/optimize.jl:127 (is_inlineable(src) = inlining_cost(src) != MAX_INLINE_COST); its use on CodeInstance.inferred, which may be a UInt8 or nothing (Compiler/src/typeinfer.jl:1256)",
    status := .proven, prop := ``IsInlineableExact, thm := some ``isInlineableExact_proven,
    notes := "Checked on the pinned Julia by difftest/compiler/inlining_props.jl." },
  { id := "compiler-inlining-declared-inline-exact", juliaFile := optFile,
    juliaFns := ["is_declared_inline(@nospecialize src::MaybeCompressed)", "is_declared_noinline(@nospecialize src::MaybeCompressed)"],
    statement := "For a CodeInfo or a compressed String, is_declared_inline is true exactly when the inlining field is SRC_FLAG_DECLARED_INLINE and is_declared_noinline exactly when it is SRC_FLAG_DECLARED_NOINLINE, so the values 0, 1 and 2 give (false, false), (true, false) and (false, true); compressing a CodeInfo keeps both answers; every other source is a MethodError.",
    source := "definitions Compiler/src/optimize.jl:139-146 with jl_ir_flag_inlining (src/ircode.c:1201-1209); @inline/@noinline set the inlining field (base/expr.jl)",
    status := .proven, prop := ``DeclaredInlineExact, thm := some ``declaredInlineExact_proven,
    notes := "Checked on the pinned Julia by difftest/compiler/inlining_props.jl: code_lowered gives inlining 0, 1 and 2 for a plain, an @inline and a @noinline method, and nothing, a UInt8 and an IRCode throw MethodError." },
  { id := "compiler-inlining-stmt-inline-exact", juliaFile := optFile,
    juliaFns := ["is_stmt_inline(stmt_flag::UInt32)", "is_stmt_noinline(stmt_flag::UInt32)"],
    statement := "is_stmt_inline(flag) is bit 1 of flag and is_stmt_noinline(flag) is bit 2, so both are false for 0 and for every flag set flags_for_effects produces, is_stmt_inline(IR_FLAG_INLINE) and is_stmt_noinline(IR_FLAG_NOINLINE) are true, and each is false on the other's flag.",
    source := "definitions Compiler/src/optimize.jl:355-356; the call-site @inline/@noinline bits of jl_code_info_set_ir (src/method.c:612-615)",
    status := .proven, prop := ``StmtInlineExact, thm := some ``stmtInlineExact_proven,
    notes := "Checked on the pinned Julia by difftest/compiler/inlining_props.jl (20004 flags and 2000 random Effects)." },
  { id := "compiler-inlining-statement-cost-exact", juliaFile := optFile,
    juliaFns := ["statement_cost(ex::Expr, line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)"],
    statement := "statement_cost gives, branch by branch: 0 for a meta head, 20 for a foreigncall (1 for jl_string_ptr), 1 for a foreignglobal, 20 for an invoke (0 when its result is Union{}), 3 for an assignment to a global and 0 otherwise plus the cost of an Expr right side priced with line -1, 100 for copyast, 0 for any other head; for a call, after the documented callee recovery: 0 for getfield, tuple and getglobal; 1 (memoryrefget, const_memoryrefget, memoryref_isassigned) or 5 (memoryrefset!, memoryrefunset!) when the memory argument's type is known and inline_nonleaf_penalty otherwise; 1 for a typeassert of a constant type and a BoundsError for a one-argument typeassert; the T_FFUNC_COST entry (20 without one) for other builtins; inline_nonleaf_penalty (0 for a Union{} result) for other calls; for an intrinsic 20 without a T_IFUNC entry or outside its arity, its table cost k when k is 0, it has fewer than two arguments, it is llvmcall or an argument is not a dispatch element, and (k - 1) ÷ 2 when at least one argument is a constant and at most one is not.",
    source := "definition Compiler/src/optimize.jl:1793-1907 and its comments (getfield/tuple/getglobal are free; unknown/unhandled intrinsic and builtin cost UNKNOWN_CALL_COST)",
    status := .proven, prop := ``StatementCostExact, thm := some ``statementCostExact_proven,
    notes := "The intrinsic halving is stated for table costs k >= 1 (the add_tfunc costs are literals in 0:20). The arity test is stated with Julia's wrapping `minarg + 1`, which is what makes every llvmcall cost 20 (compiler-inlining-llvmcall-cost). Checked on the pinned Julia by difftest/compiler/inlining_props.jl on 23 constructed statements, besides the model difftest." },
  { id := "compiler-inlining-statement-or-branch-cost-exact", juliaFile := optFile,
    juliaFns := ["statement_or_branch_cost(@nospecialize(stmt), line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)"],
    statement := "statement_or_branch_cost prices an Expr by statement_cost; a GotoNode or GotoIfNot costs 40 when its target is before line and 0 otherwise, the target being the label in a CodeInfo and the first statement of block label in an IRCode, where a label naming no block is a BoundsError; an EnterNode costs typemax(Int) and any other statement 0.",
    source := "definition and comments Compiler/src/optimize.jl:1909-1930 (loops are generally always expensive; forward jumps are counted by the not-taken branch; don't inline functions with try/catch)",
    status := .proven, prop := ``StatementOrBranchCostExact, thm := some ``statementOrBranchCostExact_proven,
    notes := "Checked on the pinned Julia by difftest/compiler/inlining_props.jl: every (target, line) pair 1:6 x 1:6 on a CodeInfo, every (block, line) pair of a loop's IRCode, and out-of-range blocks 0 and n+1." },
  { id := "compiler-inlining-statement-costs-exact", juliaFile := optFile,
    juliaFns := ["statement_costs!(cost::Vector{Int}, body::Vector{Any}, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)"],
    statement := "statement_costs! computes statement_or_branch_cost(body[line], line, ...) for line = 1:length(body) in order, writes it to cost[line], and returns the largest of these costs, or 0 when none is positive; the first statement whose cost throws decides the exception.",
    source := "definition Compiler/src/optimize.jl:1945-1957",
    status := .proven, prop := ``StatementCostsExact, thm := some ``statementCostsExact_proven,
    notes := "Checked on the pinned Julia by difftest/compiler/inlining_props.jl on six functions (including a loop and a try/catch)." }
]

end JuliaLean.Proofs.Compiler.src.optimize

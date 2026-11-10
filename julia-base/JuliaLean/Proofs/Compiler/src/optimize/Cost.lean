import JuliaLean.Proofs.Compiler.src.optimize.Common
import JuliaLean.Proofs.Compiler.src.optimize.Encoding

/-!
Properties of the statement cost and of the body cost (`statement_cost`,
`statement_or_branch_cost`, `statement_costs!`, `inline_cost_model(::IRCode, ...)`) and of
`inline_cost_clamp`.

The type answers `statement_cost` reads are inputs of the model (`CallFacts`). Two of them are
numbers: the `T_IFUNC_COST` entry of an intrinsic and the `T_FFUNC_COST` entry of a builtin. The
`add_tfunc` calls of Compiler/src/tfuncs.jl give every one of them a small non-negative literal
(at most 100), and `OptimizationParams` defaults `inline_nonleaf_penalty` to 1000.
-/

namespace JuliaLean.Proofs.Compiler.src.optimize

open JuliaLean JuliaLean.Compiler JuliaLean.Compiler.Optimize

/-! ## `inline_cost_clamp` -/

theorem toNat_toUInt16 (n : Nat) (h : n < 65536) : (n.toUInt16).toNat = n := by
  simp [Nat.toUInt16, UInt16.toNat_ofNat]; omega

/-- The value `inline_cost_clamp` decodes, for `10 ≤ x ≤ 65535`. -/
theorem clamp_mid (x : JI) (h1 : 10 ≤ x.val) (h2 : x.val ≤ 65535) :
    inlineCostClamp x = jlDecodeInliningCost (jlEncodeInliningCost x.val.toNat.toUInt16) := by
  unfold inlineCostClamp
  rw [if_neg (by simp [MAX_INLINE_COST]; omega), if_neg (by simp [MIN_INLINE_COST]; omega)]

theorem clamp_low (x : JI) (h : x.val < 10) : inlineCostClamp x = MIN_INLINE_COST := by
  unfold inlineCostClamp
  rw [if_neg (by simp [MAX_INLINE_COST]; omega), if_pos (by simp [MIN_INLINE_COST]; omega)]

theorem clamp_high (x : JI) (h : 65535 < x.val) : inlineCostClamp x = MAX_INLINE_COST := by
  unfold inlineCostClamp
  rw [if_pos (by simp [MAX_INLINE_COST]; omega)]

/-- The decoded cost of `x` in `10..65535`, as a number. -/
theorem clamp_mid_val (x : JI) (h1 : 10 ≤ x.val) (h2 : x.val ≤ 65535) :
    (x.val.toNat ≤ 3968 → x.val ≤ (inlineCostClamp x).toNat ∧
      ((inlineCostClamp x).toNat : Int) * 32 ≤ x.val * 33) ∧
    (3968 < x.val.toNat → (inlineCostClamp x).toNat = 65535) := by
  rw [clamp_mid x h1 h2]
  have hn := toNat_toUInt16 x.val.toNat (by omega)
  constructor
  · intro h
    have := dec_enc_ge x.val.toNat.toUInt16 (by rw [hn]; exact h)
    rw [hn] at this; omega
  · intro h
    exact dec_enc_big x.val.toNat.toUInt16 (by rw [hn]; exact h)

/-- `inline_cost_clamp`: the result is in `MIN_INLINE_COST:MAX_INLINE_COST`, the clamp is monotone
and idempotent, it never lowers a cost in `10:3968` and raises it by at most 1/32 there, and its
result survives the 8-bit encoding `jl_compress_ir` stores (decode(encode(clamp x)) == clamp x). -/
def InlineCostClampSpec : Prop :=
  (∀ x : JI, MIN_INLINE_COST ≤ inlineCostClamp x ∧ inlineCostClamp x ≤ MAX_INLINE_COST) ∧
  (∀ x y : JI, x ≤ y → inlineCostClamp x ≤ inlineCostClamp y) ∧
  (∀ x : JI, inlineCostClamp (ji (inlineCostClamp x).toNat) = inlineCostClamp x) ∧
  (∀ x : JI, 10 ≤ x.val → x.val ≤ 3968 →
    x.val ≤ (inlineCostClamp x).toNat ∧ ((inlineCostClamp x).toNat : Int) * 32 ≤ x.val * 33) ∧
  (∀ x : JI, jlDecodeInliningCost (jlEncodeInliningCost (inlineCostClamp x)) = inlineCostClamp x)

/-- Every result of the clamp is `MAX_INLINE_COST` or a decoded byte. -/
theorem clamp_cases (x : JI) :
    inlineCostClamp x = MAX_INLINE_COST ∨ ∃ b : UInt8, inlineCostClamp x = jlDecodeInliningCost b := by
  by_cases h1 : 65535 < x.val
  · exact Or.inl (clamp_high x h1)
  by_cases h2 : x.val < 10
  · exact Or.inr ⟨10, by rw [clamp_low x h2]; decide⟩
  · exact Or.inr ⟨_, clamp_mid x (by omega) (by omega)⟩

theorem roundtrip_dec (b : UInt8) :
    jlDecodeInliningCost (jlEncodeInliningCost (jlDecodeInliningCost b)) = jlDecodeInliningCost b := by
  rw [enc_dec]

theorem roundtrip_max : jlDecodeInliningCost (jlEncodeInliningCost MAX_INLINE_COST) = MAX_INLINE_COST := by
  decide

theorem clamp_roundtrip (x : JI) :
    jlDecodeInliningCost (jlEncodeInliningCost (inlineCostClamp x)) = inlineCostClamp x := by
  rcases clamp_cases x with h | ⟨b, h⟩
  · rw [h]; exact roundtrip_max
  · rw [h]; exact roundtrip_dec b

theorem u16_le (a b : UInt16) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

theorem clamp_range (x : JI) : MIN_INLINE_COST ≤ inlineCostClamp x ∧ inlineCostClamp x ≤ MAX_INLINE_COST := by
  have hmax : ∀ c : UInt16, c ≤ MAX_INLINE_COST := fun c => by
    rw [u16_le]; have := c.toNat_lt; simp [MAX_INLINE_COST]; omega
  refine ⟨?_, hmax _⟩
  by_cases h1 : 65535 < x.val
  · rw [clamp_high x h1]; decide
  by_cases h2 : x.val < 10
  · rw [clamp_low x h2]; decide
  have := clamp_mid_val x (by omega) (by omega)
  rw [u16_le]; simp only [MIN_INLINE_COST]
  by_cases h3 : x.val.toNat ≤ 3968
  · have := this.1 h3; show 10 ≤ _; omega
  · have := this.2 (by omega); show 10 ≤ _; omega

theorem clamp_toNat (x : JI) : 10 ≤ (inlineCostClamp x).toNat ∧ (inlineCostClamp x).toNat ≤ 65535 := by
  have := clamp_range x
  exact ⟨this.1, by have := (inlineCostClamp x).toNat_lt; omega⟩

theorem clamp_mono (x y : JI) (h : x ≤ y) : inlineCostClamp x ≤ inlineCostClamp y := by
  have hxy : x.val ≤ y.val := h
  have hmax := (clamp_range x).2
  have hmin := (clamp_range y).1
  by_cases hy1 : 65535 < y.val
  · rw [clamp_high y hy1]; exact hmax
  by_cases hx2 : x.val < 10
  · rw [clamp_low x hx2]; exact hmin
  rw [clamp_mid x (by omega) (by omega), clamp_mid y (by omega) (by omega)]
  apply dec_mono
  apply enc_mono
  rw [u16_le, toNat_toUInt16 _ (by omega), toNat_toUInt16 _ (by omega)]
  omega

theorem clamp_idem (x : JI) : inlineCostClamp (ji (inlineCostClamp x).toNat) = inlineCostClamp x := by
  have hr := clamp_toNat x
  have hv : (ji (inlineCostClamp x).toNat).val = (inlineCostClamp x).toNat :=
    ji_val _ (by omega) (by omega)
  rw [clamp_mid _ (by rw [hv]; omega) (by rw [hv]; omega), hv]
  have e : ((inlineCostClamp x).toNat : Int).toNat.toUInt16 = inlineCostClamp x := by
    apply UInt16.toNat_inj.mp; rw [toNat_toUInt16 _ (by omega)]; omega
  rw [e]; exact clamp_roundtrip x

theorem inlineCostClampSpec_proven : InlineCostClampSpec := by
  refine ⟨clamp_range, clamp_mono, clamp_idem, ?_, clamp_roundtrip⟩
  intro x h1 h2
  exact (clamp_mid_val x h1 (by omega)).1 (by omega)

/-- A finite cost below `MAX_INLINE_COST` is never clamped to `MAX_INLINE_COST`, the marker for
"never inline" (`is_inlineable(src) = inlining_cost(src) != MAX_INLINE_COST`). -/
def ClampFiniteStaysFinite : Prop :=
  ∀ x : JI, x.val < 65535 → inlineCostClamp x ≠ MAX_INLINE_COST

/-- The 8-bit encoding has no finite value above 3968, so `3969` is clamped to `MAX_INLINE_COST`. -/
theorem clampFiniteStaysFinite_refuted : ¬ ClampFiniteStaysFinite := by
  intro h
  exact h (ji 3969) (by decide) (by decide)

/-! ## `statement_cost` -/

/-- A table cost in `0:B`. -/
def CostIn (B : Int) (x : JI) : Prop := 0 ≤ x.val ∧ x.val ≤ B

def CalleeIn (B : Int) : Callee → Prop
  | .intrinsic _ _ _ cost _ => CostIn B cost
  | .builtin _ (some k) => CostIn B k
  | _ => True

/-- A table cost within the range the `add_tfunc` literals use, with room to spare. -/
abbrev CalleeOK : Callee → Prop := CalleeIn (2 ^ 62)

def CalleeNonneg : Callee → Prop
  | .intrinsic _ _ _ cost _ => 0 ≤ cost.val
  | .builtin _ (some k) => 0 ≤ k.val
  | _ => True

def isAssign : SExpr → Bool
  | .assign _ | .assignExpr .. => true
  | _ => false

/-- The table costs a statement reads are in `0:2^62`, and an assignment's right side is not
itself an assignment (lowering never nests them). -/
def Ordinary : SExpr → Prop
  | .call c => CalleeOK c.c0 ∧ CalleeOK c.c1
  | .assignExpr _ rhs => isAssign rhs = false ∧ Ordinary rhs
  | _ => True

/-- The table costs a statement reads are non-negative. -/
def TablesNonneg : SExpr → Prop
  | .call c => CalleeNonneg c.c0 ∧ CalleeNonneg c.c1
  | .assignExpr _ rhs => TablesNonneg rhs
  | _ => True

theorem resolve_ok (c : CallFacts) (h0 : CalleeOK c.c0) (h1 : CalleeOK c.c1) : CalleeOK (resolveCallee c) := by
  unfold resolveCallee; split <;> assumption

theorem resolve_nonneg (c : CallFacts) (h0 : CalleeNonneg c.c0) (h1 : CalleeNonneg c.c1) :
    CalleeNonneg (resolveCallee c) := by
  unfold resolveCallee; split <;> assumption

theorem div2_val (B : Int) (hBm : B ≤ 2 ^ 63 - 1) (a : JI) (h0 : 0 ≤ a.val) (h1 : a.val ≤ B) (v : JI)
    (h : JInt.div (a - ji 1) (ji 2) = .ok v) (ha : a.val ≠ 0) : 0 ≤ v.val ∧ v.val ≤ B := by
  have hs : (a - ji 1).val = a.val - 1 := by
    show wrapInt .i64 (a.val - (ji 1).val) = _
    rw [ji_val 1 (by decide) (by decide)]; exact wrap64_of _ (by omega) (by omega)
  have h2 : (ji 2).val = 2 := ji_val 2 (by decide) (by decide)
  unfold JInt.div at h
  rw [if_neg (by rw [h2]; decide), if_neg (by rw [h2]; simp)] at h
  cases h
  show 0 ≤ wrapInt .i64 _ ∧ wrapInt .i64 _ ≤ _
  rw [hs, h2]
  have q0 : 0 ≤ (a.val - 1).tdiv 2 := Int.tdiv_nonneg (by omega) (by decide)
  have q1 : (a.val - 1).tdiv 2 ≤ a.val - 1 := by
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  rw [wrap64_of _ (by omega) (by omega)]; omega

theorem bind_ite {α : Type} (m : Jl α) (f : α → Bool) (x y v : JI)
    (h : (do let a ← m; pure (if f a then x else y) : Jl JI) = .ok v) : v = x ∨ v = y := by
  cases m with
  | error e => cases h
  | ok a =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases h; split <;> simp

theorem sel_bound (B : Int) (p : JI) (hp0 : 0 ≤ p.val) (hp : p.val ≤ B) (b : Bool) :
    0 ≤ (if b = true then ji 0 else p).val ∧ (if b = true then ji 0 else p).val ≤ B := by
  have k0 : (ji 0).val = 0 := ji_val 0 (by decide) (by decide)
  cases b
  · exact ⟨hp0, hp⟩
  · simp only [if_true]; rw [k0]; omega

/-- The bounds of a call's cost. -/
theorem callCost_bounds (B : Int) (hB20 : 20 ≤ B) (hBm : B ≤ 2 ^ 63 - 1) (p : JI) (hp0 : 0 ≤ p.val) (hp : p.val ≤ B) (c : CallFacts)
    (hc : CalleeIn B (resolveCallee c)) (line : Int) (v : JI)
    (h : statementCost p (.call c) line = .ok v) : 0 ≤ v.val ∧ v.val ≤ B := by
  have k20 : (ji 20).val = 20 := ji_val 20 (by decide) (by decide)
  have k0 : (ji 0).val = 0 := ji_val 0 (by decide) (by decide)
  have k1 : (ji 1).val = 1 := ji_val 1 (by decide) (by decide)
  have k5 : (ji 5).val = 5 := ji_val 5 (by decide) (by decide)
  simp only [statementCost] at h
  revert hc h
  cases resolveCallee c with
  | intrinsic assigned minarg maxarg cost llvmcall =>
    intro hc h
    simp only [CalleeIn, CostIn] at hc
    simp only [UNKNOWN_CALL_COST] at h
    split at h
    · split at h
      · split at h
        · cases h; exact hc
        · simp only [bind, Except.bind] at h
          split at h
          · cases h
          · split at h
            · cases h; exact hc
            · split at h
              · exact div2_val B hBm cost hc.1 hc.2 v h (by intro e; simp_all)
              · cases h; exact hc
      · cases h; rw [k20]; omega
    · cases h; rw [k20]; omega
  | builtin kind tfuncCost =>
    intro hc h
    simp only [UNKNOWN_CALL_COST] at h
    have leaf : ∀ w : JI, (match tfuncCost with | none => (pure (ji 20) : Jl JI) | some k => pure k) = .ok w →
        0 ≤ w.val ∧ w.val ≤ B := by
      intro w hw
      cases tfuncCost with
      | none => cases hw; rw [k20]; omega
      | some k => cases hw; simp only [CalleeIn, CostIn] at hc; exact hc
    split at h
    · split at h
      · cases h; rw [k0]; omega
      split at h
      · rcases bind_ite _ _ _ _ _ h with e | e <;> subst e
        · rw [k1]; omega
        · exact ⟨hp0, hp⟩
      split at h
      · rcases bind_ite _ _ _ _ _ h with e | e <;> subst e
        · rw [k5]; omega
        · exact ⟨hp0, hp⟩
      split at h
      · rcases bind_ite _ _ _ _ _ h with e | e <;> subst e
        · rw [k5]; omega
        · exact ⟨hp0, hp⟩
      split at h
      · revert h
        cases argAt c 3 with
        | error e => intro h; cases h
        | ok a =>
          simp only [bind, Except.bind]
          split
          · intro h; cases h; rw [k1]; omega
          · exact leaf v
      · exact leaf v h
    · cases h; exact sel_bound B p hp0 hp _
  | other =>
    intro _ h
    cases h; exact sel_bound B p hp0 hp _


/-- A non-assignment statement costs `0:2^62`. -/
theorem stmtCost_bounds_flat (p : JI) (hp0 : 0 ≤ p.val) (hp : p.val ≤ 2 ^ 62) (e : SExpr)
    (he : Ordinary e) (hna : isAssign e = false) (line : Int) (v : JI)
    (h : statementCost p e line = .ok v) : 0 ≤ v.val ∧ v.val ≤ 2 ^ 62 := by
  have k20 : (ji 20).val = 20 := ji_val 20 (by decide) (by decide)
  have k0 : (ji 0).val = 0 := ji_val 0 (by decide) (by decide)
  have k1 : (ji 1).val = 1 := ji_val 1 (by decide) (by decide)
  have k100 : (ji 100).val = 100 := ji_val 100 (by decide) (by decide)
  cases e with
  | call c => exact callCost_bounds (2 ^ 62) (by decide) (by decide) p hp0 hp c (resolve_ok c he.1 he.2) line v h
  | metaHead => simp only [statementCost, pure, Except.pure] at h; cases h; rw [k0]; decide
  | foreigncall sp =>
    simp only [statementCost, pure, Except.pure] at h; cases h
    cases sp
    · simp only [Bool.false_eq_true, if_false]; rw [k20]; decide
    · simp only [if_true]; rw [k1]; decide
  | foreignglobal => simp only [statementCost, pure, Except.pure] at h; cases h; rw [k1]; decide
  | invoke rb =>
    simp only [statementCost, UNKNOWN_CALL_COST, pure, Except.pure] at h; cases h
    have : ∀ b : Bool, 0 ≤ (if b = true then ji 0 else ji 20).val ∧ (if b = true then ji 0 else ji 20).val ≤ 2 ^ 62 := by
      intro b; cases b
      · simp only [Bool.false_eq_true, if_false]; rw [k20]; decide
      · simp only [if_true]; rw [k0]; decide
    exact this _
  | assign _ => simp [isAssign] at hna
  | assignExpr _ _ => simp [isAssign] at hna
  | copyast => simp only [statementCost, pure, Except.pure] at h; cases h; rw [k100]; decide
  | other => simp only [statementCost, pure, Except.pure] at h; cases h; rw [k0]; decide

/-- Every statement of lowered code costs `0:2^62 + 3`. -/
theorem stmtCost_bounds (p : JI) (hp0 : 0 ≤ p.val) (hp : p.val ≤ 2 ^ 62) (e : SExpr)
    (he : Ordinary e) (line : Int) (v : JI) (h : statementCost p e line = .ok v) :
    0 ≤ v.val ∧ v.val ≤ 2 ^ 62 + 3 := by
  have k0 : (ji 0).val = 0 := ji_val 0 (by decide) (by decide)
  have k3 : (ji 3).val = 3 := ji_val 3 (by decide) (by decide)
  cases e with
  | assign g =>
    simp only [statementCost, pure, Except.pure] at h; cases h
    split
    · rw [k3]; decide
    · rw [k0]; decide
  | assignExpr g rhs =>
    simp only [statementCost, bind, Except.bind, pure, Except.pure] at h
    revert h
    cases hr : statementCost p rhs (-1) with
    | error e => intro h; cases h
    | ok w =>
      intro h; simp only at h; cases h
      have hw := stmtCost_bounds_flat p hp0 hp rhs he.2 he.1 (-1) w hr
      have hc : 0 ≤ (if g = true then ji 3 else ji 0).val ∧ (if g = true then ji 3 else ji 0).val ≤ 3 := by
        split
        · rw [k3]; decide
        · rw [k0]; decide
      rw [add_val_of _ _ (by omega) (by omega)]; omega
  | _ =>
    have := stmtCost_bounds_flat p hp0 hp _ he rfl line v h
    omega

/-- A dynamic call as an assignment's right side: the callee is no builtin or intrinsic. -/
def dynCall : CallFacts :=
  { c0 := .other, ftypIntrinsic := false, fargSSA := false, defRecoverable := false, c1 := .other,
    nargs := 2, args := [none], retBottom := false }

/-- No assignment to a global has an `Expr` right side. Lowering emits `Core.setglobal!` calls for
global assignments (also at top level), and the global-write reformulation stores `p = val` with a
`Core.BindingPartition` `p` and the call's value operand `val`, which is never an `Expr`
(Compiler/src/optimize.jl:1446-1447). So this holds for every `CodeInfo` and `IRCode`. -/
def NoGlobalExprAssign : SExpr → Prop
  | .assignExpr g rhs => g = false ∧ NoGlobalExprAssign rhs
  | _ => True

/-- `statement_cost` is non-negative when `inline_nonleaf_penalty` and the tfunc table costs are,
for any size of them (`typemax(Int)` included), on statements of lowered code. -/
def StatementCostNonneg : Prop :=
  ∀ (p : JI) (e : SExpr) (line : Int) (v : JI), 0 ≤ p.val → TablesNonneg e → NoGlobalExprAssign e →
    statementCost p e line = .ok v → 0 ≤ v.val

theorem calleeNonneg_in (c : Callee) (h : CalleeNonneg c) : CalleeIn (2 ^ 63 - 1) c := by
  cases c with
  | intrinsic _ _ _ cost _ => exact ⟨h, (ji_bounds cost).2⟩
  | builtin _ t => cases t with
    | none => trivial
    | some k => exact ⟨h, (ji_bounds k).2⟩
  | other => trivial

theorem statementCostNonneg_proven : StatementCostNonneg := by
  intro p e
  induction e with
  | call c =>
    intro line v hp0 ht _ h
    exact (callCost_bounds (2 ^ 63 - 1) (by decide) (by decide) p hp0 (ji_bounds p).2 c
      (calleeNonneg_in _ (resolve_nonneg c ht.1 ht.2)) line v h).1
  | assign g =>
    intro line v _ _ _ h
    simp only [statementCost, pure, Except.pure] at h; cases h
    cases g <;> decide
  | assignExpr g rhs ih =>
    intro line v hp0 ht hs h
    simp only [NoGlobalExprAssign] at hs
    obtain ⟨hg, hs'⟩ := hs
    subst hg
    simp only [statementCost, bind, Except.bind, pure, Except.pure] at h
    revert h
    cases hr : statementCost p rhs (-1) with
    | error e => intro h; cases h
    | ok w =>
      intro h; simp only at h; cases h
      have hw := ih (-1) w hp0 ht hs' hr
      have k0 : (ji 0).val = 0 := ji_val 0 (by decide) (by decide)
      have hwb := (ji_bounds w).2
      simp only [Bool.false_eq_true, if_false]
      rw [add_val_of _ _ (by rw [k0]; omega) (by rw [k0]; omega), k0]; omega
  | _ =>
    intro line v _ _ _ h
    simp only [statementCost, UNKNOWN_CALL_COST, pure, Except.pure] at h
    cases h
    all_goals (repeat' split) <;> decide

/-- With `inline_nonleaf_penalty = typemax(Int)`, `G = f(x)` for a global `G` would cost
`3 + typemax(Int)`, which wraps to a negative cost. Neither lowering nor the optimizer emits such
an assignment. -/
theorem statementCost_global_assign_wraps :
    statementCost (JInt.typemax .i64) (.assignExpr true (.call dynCall)) 1 = .ok (ji (-(2 ^ 63) + 2)) := by
  decide

/-- The ordinary case: penalty and table costs in `0:2^62`, assignments not nested. -/
def StatementCostNonnegOrdinary : Prop :=
  ∀ (p : JI) (e : SExpr) (line : Int) (v : JI), 0 ≤ p.val → p.val ≤ 2 ^ 62 → Ordinary e →
    statementCost p e line = .ok v → 0 ≤ v.val ∧ v.val ≤ 2 ^ 62 + 3

theorem statementCostNonnegOrdinary_proven : StatementCostNonnegOrdinary :=
  fun p e line v hp0 hp he h => stmtCost_bounds p hp0 hp e he line v h

/-! ## Errors -/

/-- Every argument fact of a call is supplied (one per argument after the callee). -/
def Supplied : SExpr → Prop
  | .call c => c.args.length + 1 = c.nargs ∧ ∀ a ∈ c.args, a.isSome = true
  | .assignExpr _ rhs => Supplied rhs
  | _ => True

/-- A `typeassert` call has its two arguments, as `x::T` lowers to. -/
def TypeassertBinary : SExpr → Prop
  | .call c => ∀ t, resolveCallee c = .builtin .typeassert t → 3 ≤ c.nargs
  | .assignExpr _ rhs => TypeassertBinary rhs
  | _ => True

/-- `statement_cost` returns a cost for every statement whose argument facts are known. -/
def StatementCostNoThrow : Prop :=
  ∀ (p : JI) (e : SExpr) (line : Int), Supplied e → ∃ v, statementCost p e line = .ok v

def StatementCostNoThrowOrdinary : Prop :=
  ∀ (p : JI) (e : SExpr) (line : Int), Supplied e → TypeassertBinary e →
    ∃ v, statementCost p e line = .ok v

/-- `Core.typeassert(x)`: the callee and one argument. -/
def typeassertOneArg : CallFacts :=
  { c0 := .builtin .typeassert (some (ji 4)), ftypIntrinsic := false, fargSSA := false,
    defRecoverable := false, c1 := .other, nargs := 2,
    args := [some ⟨true, false, true, false⟩], retBottom := true }

theorem statementCostNoThrow_refuted : ¬ StatementCostNoThrow := by
  intro h
  have ⟨v, hv⟩ := h (ji 1000) (.call typeassertOneArg) 2 ⟨rfl, by decide⟩
  have : statementCost (ji 1000) (.call typeassertOneArg) 2 = .error .boundsError := by decide
  rw [this] at hv; cases hv

theorem argAt_ok (c : CallFacts) (hs : c.args.length + 1 = c.nargs ∧ ∀ a ∈ c.args, a.isSome = true)
    (i : Nat) (h1 : 2 ≤ i) (h2 : i ≤ c.nargs) : ∃ a, argAt c i = .ok a := by
  unfold argAt
  rw [if_neg (by omega)]
  have hl : i - 2 < c.args.length := by omega
  have hm : c.args[i - 2]? = some (c.args[i - 2]) := List.getElem?_eq_getElem hl
  have hsome := hs.2 _ (List.getElem_mem hl)
  rw [hm]
  cases e : c.args[i - 2] with
  | none => rw [e] at hsome; cases hsome
  | some a => exact ⟨a, rfl⟩

theorem icc_ok (c : CallFacts) (hs : c.args.length + 1 = c.nargs ∧ ∀ a ∈ c.args, a.isSome = true) :
    ∀ k i n, 2 ≤ i → i + k ≤ c.nargs + 1 → ∃ r, intrinsicConstCount c k i n = .ok r := by
  intro k
  induction k with
  | zero => intro i n _ _; exact ⟨_, rfl⟩
  | succ k ih =>
    intro i n h1 h2
    have ⟨a, ha⟩ := argAt_ok c hs i h1 (by omega)
    simp only [intrinsicConstCount, ha, bind, Except.bind]
    split
    · exact ⟨_, rfl⟩
    · exact ih (i + 1) _ (by omega) (by omega)

theorem div2_ok (a : JI) : ∃ v, JInt.div (a - ji 1) (ji 2) = .ok v := by
  have h2 : (ji 2).val = 2 := ji_val 2 (by decide) (by decide)
  unfold JInt.div
  rw [if_neg (by rw [h2]; decide), if_neg (by rw [h2]; simp)]
  exact ⟨_, rfl⟩

theorem callCost_ok (p : JI) (c : CallFacts)
    (hs : c.args.length + 1 = c.nargs ∧ ∀ a ∈ c.args, a.isSome = true)
    (ht : ∀ t, resolveCallee c = .builtin .typeassert t → 3 ≤ c.nargs) (line : Int) :
    ∃ v, statementCost p (.call c) line = .ok v := by
  simp only [statementCost]
  revert ht
  cases resolveCallee c with
  | intrinsic assigned minarg maxarg cost llvmcall =>
    intro _
    dsimp only
    split
    · split
      · split
        · exact ⟨_, rfl⟩
        · have hn : 1 ≤ c.nargs := by omega
          have ⟨r, hr⟩ := icc_ok c hs (c.nargs - 1) 2 0 (by omega) (by omega)
          simp only [hr, bind, Except.bind]
          split
          · exact ⟨_, rfl⟩
          · split
            · exact div2_ok cost
            · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  | builtin kind tfuncCost =>
    intro ht
    dsimp only
    have leaf : ∃ w, (match tfuncCost with | none => (pure UNKNOWN_CALL_COST : Jl JI) | some k => pure k) = .ok w := by
      cases tfuncCost <;> exact ⟨_, rfl⟩
    split
    · split
      · exact ⟨_, rfl⟩
      split
      · have ⟨a, ha⟩ := argAt_ok c hs 2 (by omega) (by omega)
        simp only [ha, bind, Except.bind]; exact ⟨_, rfl⟩
      split
      · have ⟨a, ha⟩ := argAt_ok c hs 2 (by omega) (by omega)
        simp only [ha, bind, Except.bind]; exact ⟨_, rfl⟩
      split
      · have ⟨a, ha⟩ := argAt_ok c hs 2 (by omega) (by omega)
        simp only [ha, bind, Except.bind]; exact ⟨_, rfl⟩
      split
      · rename_i hk
        have h3 := ht tfuncCost (by simp at hk; rw [hk])
        have ⟨a, ha⟩ := argAt_ok c hs 3 (by omega) h3
        simp only [ha, bind, Except.bind]
        split
        · exact ⟨_, rfl⟩
        · exact leaf
      · exact leaf
    · exact ⟨_, rfl⟩
  | other => intro _; dsimp only; exact ⟨_, rfl⟩

theorem statementCostNoThrowOrdinary_proven : StatementCostNoThrowOrdinary := by
  intro p e
  induction e with
  | call c => intro line hs ht; exact callCost_ok p c hs ht line
  | assignExpr g rhs ih =>
    intro line hs ht
    have ⟨w, hw⟩ := ih (-1) hs ht
    simp only [statementCost, hw, bind, Except.bind]
    exact ⟨_, rfl⟩
  | _ => intro _ _ _; exact ⟨_, rfl⟩

/-! ## `llvmcall` -/

/-- An `llvmcall` whose argument count is within its `T_IFUNC` arity is charged its table cost:
the `f === Intrinsics.llvmcall` test returns `cost` before the argument loop, because argextype
"will crash" on the malformed IR an llvmcall holds (Compiler/src/optimize.jl:1821-1823). The arity
test is read as the mathematical `minarg + 1 <= nargs <= maxarg + 1`. -/
def LlvmcallTableCost : Prop :=
  ∀ (p : JI) (c : CallFacts) (line : Int) (minarg maxarg cost : JI),
    resolveCallee c = .intrinsic true minarg maxarg cost true →
    minarg.val + 1 ≤ c.nargs → (c.nargs : Int) ≤ maxarg.val + 1 →
    statementCost p (.call c) line = .ok cost

/-- `llvmcall(ir, rt, at, x)`: arity 3 to `INT_INF`, table cost 10. -/
def llvmcallCall : CallFacts :=
  { c0 := .intrinsic true (ji 3) (JInt.typemax .i64) (ji 10) true, ftypIntrinsic := false,
    fargSSA := false, defRecoverable := false, c1 := .other, nargs := 5, args := [none, none, none, none],
    retBottom := false }

/-- `maxarg + 1` wraps to `typemin(Int)` for `maxarg = INT_INF`, so the arity test fails and every
llvmcall costs `UNKNOWN_CALL_COST` (20). -/
theorem llvmcallTableCost_refuted : ¬ LlvmcallTableCost := by
  intro h
  have := h (ji 1000) llvmcallCall 1 (ji 3) (JInt.typemax .i64) (ji 10) rfl (by decide) (by decide)
  have e : statementCost (ji 1000) (.call llvmcallCall) 1 = .ok (ji 20) := by decide
  rw [e] at this
  exact absurd this (by decide)


/-! ## The cost of a body -/

/-- The statements of lowered code: an `Expr` is `Ordinary`. -/
def StmtOK : Stmt → Prop
  | .expr e => Ordinary e
  | _ => True

theorem sobc_nonneg (isIR : Bool) (bf : List Int) (p : JI) (hp0 : 0 ≤ p.val) (hp : p.val ≤ 2 ^ 62)
    (s : Stmt) (hs : StmtOK s) (line : Int) (v : JI)
    (h : statementOrBranchCost isIR bf p s line = .ok v) : 0 ≤ v.val := by
  have k0 : (ji 0).val = 0 := ji_val 0 (by decide) (by decide)
  have k40 : (ji 40).val = 40 := ji_val 40 (by decide) (by decide)
  have b40 : ∀ b : Prop, [Decidable b] → 0 ≤ (if b then ji 40 else ji 0).val := by
    intro b _; split
    · rw [k40]; decide
    · rw [k0]; decide
  cases s with
  | expr e => exact (stmtCost_bounds p hp0 hp e hs line v h).1
  | goto l =>
    simp only [statementOrBranchCost, bind, Except.bind] at h
    revert h; cases branchDst isIR bf l with
    | error _ => intro h; cases h
    | ok d => intro h; simp only [pure, Except.pure] at h; cases h; exact b40 _
  | gotoifnot l =>
    simp only [statementOrBranchCost, bind, Except.bind] at h
    revert h; cases branchDst isIR bf l with
    | error _ => intro h; cases h
    | ok d => intro h; simp only [pure, Except.pure] at h; cases h; exact b40 _
  | enter => simp only [statementOrBranchCost, pure, Except.pure] at h; cases h; decide
  | other => simp only [statementOrBranchCost, pure, Except.pure] at h; cases h; rw [k0]; decide

/-- The sum of a list of costs, as an unbounded integer. -/
def sumv : List JI → Int
  | [] => 0
  | c :: cs => c.val + sumv cs

theorem sumv_nonneg : ∀ cs : List JI, (∀ c ∈ cs, 0 ≤ c.val) → 0 ≤ sumv cs
  | [], _ => by simp [sumv]
  | c :: cs, h => by
    have := sumv_nonneg cs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h c (List.mem_cons_self ..)
    simp only [sumv]; omega

/-- `MAX_INLINE_COST` above the threshold, else the clamped sum. -/
def closedForm (t : JI) (s : Int) : UInt16 :=
  if t.val < s then MAX_INLINE_COST else inlineCostClamp (JInt.wrap .i64 s)

theorem loop_closed (bf : List Int) (p t : JI) (ht0 : 0 ≤ t.val) (ht : t.val < 2 ^ 62) :
    ∀ (stmts : List Stmt) (line : Int) (b m0 : JI) (cs : List JI) (m : JI),
      0 ≤ b.val → b.val ≤ t.val →
      statementCostsLoop true bf p stmts line m0 = .ok (cs, m) → (∀ c ∈ cs, 0 ≤ c.val) →
      inlineCostLoop bf p t stmts line b = .ok (closedForm t (b.val + sumv cs)) := by
  intro stmts
  induction stmts with
  | nil =>
    intro line b m0 cs m hb hbt h _
    simp only [statementCostsLoop, pure, Except.pure] at h
    cases h
    simp only [inlineCostLoop, pure, Except.pure, closedForm, sumv, Int.add_zero]
    rw [if_neg (by omega), wrap_self]
  | cons s rest ih =>
    intro line b m0 cs m hb hbt h hcs
    simp only [statementCostsLoop, bind, Except.bind] at h
    revert h
    cases hs : statementOrBranchCost true bf p s line with
    | error _ => intro h; cases h
    | ok c =>
      dsimp only
      cases hr : statementCostsLoop true bf p rest (line + 1) (if c > m0 then c else m0) with
      | error _ => intro h; cases h
      | ok r =>
        intro h
        simp only [pure, Except.pure] at h
        cases h
        have hc0 : 0 ≤ c.val := hcs c (List.mem_cons_self ..)
        have hcs' : ∀ x ∈ r.1, 0 ≤ x.val := fun x hx => hcs x (List.mem_cons_of_mem _ hx)
        have hsum := sumv_nonneg r.1 hcs'
        simp only [inlineCostLoop, hs, bind, Except.bind]
        by_cases hgt : plusSaturate b c > t
        · rw [if_pos hgt]
          have h' : t.val < (plusSaturate b c).val := hgt
          rw [ps_gt_iff b c t hb hc0 hbt ht] at h'
          have e : closedForm t (b.val + sumv (c :: r.1)) = MAX_INLINE_COST := by
            unfold closedForm
            rw [if_pos (show t.val < b.val + sumv (c :: r.1) by simp only [sumv]; omega)]
          rw [e]; rfl
        · rw [if_neg hgt]
          have h' : ¬ t.val < (plusSaturate b c).val := hgt
          rw [ps_gt_iff b c t hb hc0 hbt ht] at h'
          have hv := ps_val_small b c hb hc0 (by omega)
          have := ih (line + 1) (plusSaturate b c) _ r.1 r.2 (by omega) (by omega) hr hcs'
          rw [this, hv]
          simp only [sumv]
          rw [Int.add_assoc]

/-- The costs `statement_costs!` writes, one per statement, and the maximum it returns. -/
theorem costs_shape (isIR : Bool) (bf : List Int) (p : JI) :
    ∀ (stmts : List Stmt) (line : Int) (m0 : JI) (cs : List JI) (m : JI),
      statementCostsLoop isIR bf p stmts line m0 = .ok (cs, m) →
      cs.length = stmts.length ∧ m0.val ≤ m.val ∧ (∀ c ∈ cs, c.val ≤ m.val) ∧
      (m = m0 ∨ m ∈ cs) := by
  intro stmts
  induction stmts with
  | nil =>
    intro line m0 cs m h
    simp only [statementCostsLoop, pure, Except.pure] at h
    cases h; simp
  | cons s rest ih =>
    intro line m0 cs m h
    simp only [statementCostsLoop, bind, Except.bind] at h
    revert h
    cases statementOrBranchCost isIR bf p s line with
    | error _ => intro h; cases h
    | ok c =>
      dsimp only
      cases hr : statementCostsLoop isIR bf p rest (line + 1) (if c > m0 then c else m0) with
      | error _ => intro h; cases h
      | ok r =>
        intro h
        simp only [pure, Except.pure] at h
        cases h
        have ⟨hl, h1, h2, h3⟩ := ih _ _ r.1 r.2 hr
        have hmx : m0.val ≤ (if c > m0 then c else m0).val ∧ c.val ≤ (if c > m0 then c else m0).val := by
          split
          · rename_i hh; have : m0.val < c.val := hh; omega
          · rename_i hh; have : ¬ m0.val < c.val := hh; omega
        refine ⟨by simp [hl], by omega, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with e | e
          · subst e; omega
          · exact h2 x e
        · rcases h3 with e | e
          · rw [e]; split
            · exact Or.inr (List.mem_cons_self ..)
            · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ e)

/-- `inline_cost_model(ir, params, t)` agrees with the costs `statement_costs!` computes on the
same IR: it is `MAX_INLINE_COST` when their exact sum exceeds `t`, and `inline_cost_clamp` of the
sum otherwise. `statement_costs!` writes one cost per statement and returns the largest one (or
0). For statements of lowered code, a penalty in `0:2^62` and a threshold in `0:2^62-1`. -/
def CostModelClosedForm : Prop :=
  ∀ (bf : List Int) (p t : JI) (stmts : List Stmt) (cs : List JI) (m : JI),
    0 ≤ p.val → p.val ≤ 2 ^ 62 → 0 ≤ t.val → t.val < 2 ^ 62 → (∀ s ∈ stmts, StmtOK s) →
    statementCosts true bf p stmts = .ok (cs, m) →
    inlineCostModel bf p t stmts = .ok (closedForm t (sumv cs)) ∧
    cs.length = stmts.length ∧ 0 ≤ m.val ∧ (∀ c ∈ cs, c.val ≤ m.val) ∧ (m.val = 0 ∨ m ∈ cs)

theorem costs_nonneg (isIR : Bool) (bf : List Int) (p : JI) (hp0 : 0 ≤ p.val) (hp : p.val ≤ 2 ^ 62) :
    ∀ (stmts : List Stmt) (line : Int) (m0 : JI) (cs : List JI) (m : JI), (∀ s ∈ stmts, StmtOK s) →
      statementCostsLoop isIR bf p stmts line m0 = .ok (cs, m) → ∀ c ∈ cs, 0 ≤ c.val := by
  intro stmts
  induction stmts with
  | nil =>
    intro line m0 cs m _ h
    simp only [statementCostsLoop, pure, Except.pure] at h
    cases h; simp
  | cons s rest ih =>
    intro line m0 cs m hst h
    simp only [statementCostsLoop, bind, Except.bind] at h
    revert h
    cases hs : statementOrBranchCost isIR bf p s line with
    | error _ => intro h; cases h
    | ok c =>
      dsimp only
      cases hr : statementCostsLoop isIR bf p rest (line + 1) (if c > m0 then c else m0) with
      | error _ => intro h; cases h
      | ok r =>
        intro h
        simp only [pure, Except.pure] at h
        cases h
        intro x hx
        rcases List.mem_cons.mp hx with e | e
        · subst e; exact sobc_nonneg isIR bf p hp0 hp s (hst s (List.mem_cons_self ..)) line _ hs
        · exact ih _ _ r.1 r.2 (fun y hy => hst y (List.mem_cons_of_mem _ hy)) hr x e

theorem costModelClosedForm_proven : CostModelClosedForm := by
  intro bf p t stmts cs m hp0 hp ht0 ht hst h
  have k0 : (ji 0).val = 0 := ji_val 0 (by decide) (by decide)
  have hcs := costs_nonneg true bf p hp0 hp stmts 1 (ji 0) cs m hst h
  have hl := loop_closed bf p t ht0 ht stmts 1 (ji 0) (ji 0) cs m (by rw [k0]; decide) (by rw [k0]; exact ht0) h hcs
  rw [k0, Int.zero_add] at hl
  have ⟨h1, h2, h3, h4⟩ := costs_shape true bf p stmts 1 (ji 0) cs m h
  rw [k0] at h2
  refine ⟨hl, h1, h2, h3, ?_⟩
  rcases h4 with e | e
  · left; rw [e, k0]
  · exact Or.inr e

/-- Adding statements at the end of a body never lowers its inlining cost (whatever the
statements, the penalty and the threshold). -/
def CostModelAppendMonotone : Prop :=
  ∀ (bf : List Int) (p t : JI) (a b : List Stmt) (x y : UInt16),
    inlineCostModel bf p t a = .ok x → inlineCostModel bf p t (a ++ b) = .ok y → x ≤ y

theorem u16_le_max (c : UInt16) : c ≤ MAX_INLINE_COST := by
  rw [u16_le]; have := c.toNat_lt; simp [MAX_INLINE_COST]; omega

theorem loop_ge_clamp (bf : List Int) (p t : JI) :
    ∀ (b : List Stmt) (line : Int) (bc : JI) (y : UInt16),
      inlineCostLoop bf p t b line bc = .ok y → inlineCostClamp bc ≤ y := by
  intro b
  induction b with
  | nil =>
    intro line bc y h
    simp only [inlineCostLoop, pure, Except.pure] at h; cases h
    exact Nat.le_refl _
  | cons s rest ih =>
    intro line bc y h
    simp only [inlineCostLoop, bind, Except.bind] at h
    revert h
    cases statementOrBranchCost true bf p s line with
    | error _ => intro h; cases h
    | ok c =>
      dsimp only
      split
      · intro h; simp only [pure, Except.pure] at h; cases h; exact u16_le_max _
      · intro h
        have := ih (line + 1) _ y h
        exact Nat.le_trans (clamp_mono bc _ (ps_ge_left bc c)) this

theorem loop_append (bf : List Int) (p t : JI) (b : List Stmt) :
    ∀ (a : List Stmt) (line : Int) (bc : JI) (x y : UInt16),
      inlineCostLoop bf p t a line bc = .ok x → inlineCostLoop bf p t (a ++ b) line bc = .ok y → x ≤ y := by
  intro a
  induction a with
  | nil =>
    intro line bc x y hx hy
    simp only [inlineCostLoop, pure, Except.pure] at hx; cases hx
    exact loop_ge_clamp bf p t b line bc y hy
  | cons s rest ih =>
    intro line bc x y hx hy
    simp only [List.cons_append, inlineCostLoop, bind, Except.bind] at hx hy
    revert hx hy
    cases statementOrBranchCost true bf p s line with
    | error _ => intro h; cases h
    | ok c =>
      dsimp only
      split
      · intro hx hy; simp only [pure, Except.pure] at hx hy; cases hx; cases hy; exact Nat.le_refl _
      · intro hx hy; exact ih (line + 1) _ x y hx hy

theorem costModelAppendMonotone_proven : CostModelAppendMonotone := by
  intro bf p t a b x y hx hy
  exact loop_append bf p t b a 1 (ji 0) x y hx hy

/-- A body with a `try` (an `EnterNode`, cost `typemax(Int)`) is never inlineable by the cost
model, for any threshold below `typemax(Int)` ("don't inline functions with try/catch",
Compiler/src/optimize.jl:1923-1927). -/
def EnterNeverInlineable : Prop :=
  ∀ (bf : List Int) (p t : JI) (stmts : List Stmt) (y : UInt16),
    Stmt.enter ∈ stmts → t.val < 2 ^ 63 - 1 → inlineCostModel bf p t stmts = .ok y → y = MAX_INLINE_COST

theorem loop_enter (bf : List Int) (p t : JI) (ht : t.val < 2 ^ 63 - 1) :
    ∀ (stmts : List Stmt) (line : Int) (bc : JI) (y : UInt16),
      Stmt.enter ∈ stmts → inlineCostLoop bf p t stmts line bc = .ok y → y = MAX_INLINE_COST := by
  intro stmts
  induction stmts with
  | nil => intro _ _ _ h; cases h
  | cons s rest ih =>
    intro line bc y hm h
    simp only [inlineCostLoop, bind, Except.bind] at h
    rcases List.mem_cons.mp hm with e | e
    · subst e
      simp only [statementOrBranchCost, pure, Except.pure] at h
      have hge := ps_ge_right bc (JInt.typemax .i64)
      have htm : (JInt.typemax .i64).val = 2 ^ 63 - 1 := by decide
      rw [if_pos (show plusSaturate bc (JInt.typemax .i64) > t by show t.val < _; omega)] at h
      cases h; rfl
    · revert h
      cases statementOrBranchCost true bf p s line with
      | error _ => intro h; cases h
      | ok c =>
        dsimp only
        split
        · intro h; simp only [pure, Except.pure] at h; cases h; rfl
        · intro h; exact ih (line + 1) _ y e h

theorem enterNeverInlineable_proven : EnterNeverInlineable :=
  fun bf p t stmts y hm ht h => loop_enter bf p t ht stmts 1 (ji 0) y hm h


/-! ## Statement order -/

theorem stmtCost_line (p : JI) : ∀ (e : SExpr) (l l' : Int), l ≠ -1 → l' ≠ -1 →
    statementCost p e l = statementCost p e l' := by
  intro e l l' hl hl'
  have h1 : (l == -1) = false := beq_eq_false_iff_ne.mpr hl
  have h2 : (l' == -1) = false := beq_eq_false_iff_ne.mpr hl'
  cases e <;> simp only [statementCost, h1, h2]

/-- Not a `GotoNode` or `GotoIfNot`. -/
def BranchFree : Stmt → Prop
  | .goto _ | .gotoifnot _ => False
  | _ => True

theorem sobc_line (isIR : Bool) (bf : List Int) (p : JI) (s : Stmt) (hs : BranchFree s) (l : Int)
    (hl : 1 ≤ l) : statementOrBranchCost isIR bf p s l = statementOrBranchCost isIR bf p s 1 := by
  cases s with
  | expr e => exact stmtCost_line p e l 1 (by omega) (by decide)
  | goto _ => exact absurd hs id
  | gotoifnot _ => exact absurd hs id
  | enter => rfl
  | other => rfl

/-- The cost of a branch-free statement, which does not depend on its position. -/
def costAt1 (bf : List Int) (p : JI) (s : Stmt) : JI :=
  match statementOrBranchCost true bf p s 1 with
  | .ok v => v
  | .error _ => ji 0

theorem costs_map (bf : List Int) (p : JI) :
    ∀ (stmts : List Stmt) (line : Int) (m0 : JI) (cs : List JI) (m : JI),
      1 ≤ line → (∀ s ∈ stmts, BranchFree s) →
      statementCostsLoop true bf p stmts line m0 = .ok (cs, m) →
      cs = stmts.map (costAt1 bf p) ∧ ∀ s ∈ stmts, statementOrBranchCost true bf p s 1 = .ok (costAt1 bf p s) := by
  intro stmts
  induction stmts with
  | nil =>
    intro line m0 cs m _ _ h
    simp only [statementCostsLoop, pure, Except.pure] at h; cases h; simp
  | cons s rest ih =>
    intro line m0 cs m hl hbf h
    simp only [statementCostsLoop, bind, Except.bind] at h
    revert h
    cases hs : statementOrBranchCost true bf p s line with
    | error _ => intro h; cases h
    | ok c =>
      dsimp only
      cases hr : statementCostsLoop true bf p rest (line + 1) (if c > m0 then c else m0) with
      | error _ => intro h; cases h
      | ok r =>
        intro h
        simp only [pure, Except.pure] at h
        cases h
        have ⟨e1, e2⟩ := ih _ _ r.1 r.2 (by omega) (fun x hx => hbf x (List.mem_cons_of_mem _ hx)) hr
        rw [sobc_line true bf p s (hbf s (List.mem_cons_self ..)) line hl] at hs
        have hc : costAt1 bf p s = c := by simp only [costAt1, hs]
        refine ⟨by simp [e1, hc], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with e | e
        · subst e; rw [hc]; exact hs
        · exact e2 x e

theorem costs_of_all (bf : List Int) (p : JI) :
    ∀ (stmts : List Stmt) (line : Int) (m0 : JI), 1 ≤ line → (∀ s ∈ stmts, BranchFree s) →
      (∀ s ∈ stmts, statementOrBranchCost true bf p s 1 = .ok (costAt1 bf p s)) →
      ∃ m, statementCostsLoop true bf p stmts line m0 = .ok (stmts.map (costAt1 bf p), m) := by
  intro stmts
  induction stmts with
  | nil => intro line m0 _ _ _; exact ⟨m0, rfl⟩
  | cons s rest ih =>
    intro line m0 hl hbf hok
    have hs := hok s (List.mem_cons_self ..)
    rw [← sobc_line true bf p s (hbf s (List.mem_cons_self ..)) line hl] at hs
    have ⟨m, hm⟩ := ih (line + 1) (if costAt1 bf p s > m0 then costAt1 bf p s else m0) (by omega)
      (fun x hx => hbf x (List.mem_cons_of_mem _ hx)) (fun x hx => hok x (List.mem_cons_of_mem _ hx))
    refine ⟨m, ?_⟩
    simp only [statementCostsLoop, hs, bind, Except.bind, hm, pure, Except.pure, List.map_cons]

theorem sumv_perm {l1 l2 : List JI} (h : l1.Perm l2) : sumv l1 = sumv l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [sumv, ih]
  | swap x y l => simp only [sumv]; omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- For a body without branches, the inlining cost does not depend on the order of its
statements: any permutation of them gets the same cost. -/
def CostModelOrderIndependent : Prop :=
  ∀ (bf : List Int) (p t : JI) (stmts1 stmts2 : List Stmt) (cs : List JI) (m : JI),
    0 ≤ p.val → p.val ≤ 2 ^ 62 → 0 ≤ t.val → t.val < 2 ^ 62 →
    (∀ s ∈ stmts1, StmtOK s ∧ BranchFree s) → stmts1.Perm stmts2 →
    statementCosts true bf p stmts1 = .ok (cs, m) →
    inlineCostModel bf p t stmts1 = inlineCostModel bf p t stmts2

theorem costModelOrderIndependent_proven : CostModelOrderIndependent := by
  intro bf p t stmts1 stmts2 cs m hp0 hp ht0 ht hst hperm h
  have hbf1 : ∀ s ∈ stmts1, BranchFree s := fun s hs => (hst s hs).2
  have hbf2 : ∀ s ∈ stmts2, BranchFree s := fun s hs => hbf1 s (hperm.mem_iff.mpr hs)
  have hok1 : ∀ s ∈ stmts1, StmtOK s := fun s hs => (hst s hs).1
  have hok2 : ∀ s ∈ stmts2, StmtOK s := fun s hs => hok1 s (hperm.mem_iff.mpr hs)
  have ⟨e1, e2⟩ := costs_map bf p stmts1 1 (ji 0) cs m (by decide) hbf1 h
  have ⟨m2, h2⟩ := costs_of_all bf p stmts2 1 (ji 0) (by decide) hbf2
    (fun s hs => e2 s (hperm.mem_iff.mpr hs))
  have c1 := (costModelClosedForm_proven bf p t stmts1 cs m hp0 hp ht0 ht hok1 h).1
  have c2 := (costModelClosedForm_proven bf p t stmts2 _ m2 hp0 hp ht0 ht hok2 h2).1
  rw [c1, c2, e1, sumv_perm (hperm.map (costAt1 bf p))]

/-! ## The threshold logic of `inline_cost_model(interp, result, inline_flag, ir)` -/

/-- Parameters in the range where no threshold sum wraps. -/
def ParamsOK (p : CostParams) : Prop :=
  0 ≤ p.inline_cost_threshold.val ∧ p.inline_cost_threshold.val ≤ 2 ^ 56 ∧
  0 ≤ p.inline_tupleret_bonus.val ∧ p.inline_tupleret_bonus.val ≤ 2 ^ 56 ∧
  0 ≤ p.inline_nonleaf_penalty.val ∧ p.inline_nonleaf_penalty.val ≤ 2 ^ 62

theorem mul_val_of (a b : JI) (h1 : -(2 ^ 63 : Int) ≤ a.val * b.val) (h2 : a.val * b.val ≤ 2 ^ 63 - 1) :
    (a * b).val = a.val * b.val := wrap64_of _ h1 h2

theorem threshold_val (p : CostParams) (hp : ParamsOK p) (r : ResultFacts) (di : Bool) :
    (costThreshold p r di).val = p.inline_cost_threshold.val +
      (if r.tupleRet then p.inline_tupleret_bonus.val else 0) +
      (if di then 19 * p.inline_cost_threshold.val else 0) +
      (if r.moduleIsTop ∧ (r.name == "iterate" ∨ r.name == "unsafe_convert" ∨ r.name == "cconvert")
        then 4 * p.inline_cost_threshold.val else 0) := by
  have ⟨d0, d1, b0, b1, _, _⟩ := hp
  have k19 : (ji 19).val = 19 := ji_val 19 (by decide) (by decide)
  have k4 : (ji 4).val = 4 := ji_val 4 (by decide) (by decide)
  have m19 : (ji 19 * p.inline_cost_threshold).val = 19 * p.inline_cost_threshold.val := by
    rw [mul_val_of _ _ (by rw [k19]; omega) (by rw [k19]; omega), k19]
  have m4 : (ji 4 * p.inline_cost_threshold).val = 4 * p.inline_cost_threshold.val := by
    rw [mul_val_of _ _ (by rw [k4]; omega) (by rw [k4]; omega), k4]
  unfold costThreshold
  dsimp only
  have s1 : (if r.tupleRet = true then p.inline_cost_threshold + p.inline_tupleret_bonus
      else p.inline_cost_threshold).val =
      p.inline_cost_threshold.val + (if r.tupleRet then p.inline_tupleret_bonus.val else 0) := by
    split
    · rw [add_val_of _ _ (by omega) (by omega)]
    · omega
  generalize hA : (if r.tupleRet = true then p.inline_cost_threshold + p.inline_tupleret_bonus
      else p.inline_cost_threshold) = A at s1
  have hA0 : 0 ≤ A.val ∧ A.val ≤ 2 ^ 57 := by
    rw [s1]; split <;> omega
  have s2 : (if di = true then A + ji 19 * p.inline_cost_threshold else A).val =
      A.val + (if di then 19 * p.inline_cost_threshold.val else 0) := by
    split
    · rw [add_val_of _ _ (by rw [m19]; omega) (by rw [m19]; omega), m19]
    · omega
  generalize hB : (if di = true then A + ji 19 * p.inline_cost_threshold else A) = B at s2
  have hB0 : 0 ≤ B.val ∧ B.val ≤ 2 ^ 57 + 19 * 2 ^ 56 := by
    rw [s2]; split <;> omega
  split
  · rw [add_val_of _ _ (by rw [m4]; omega) (by rw [m4]; omega), m4, s2, s1]
    try omega
  · rw [s2, s1]
    try omega

theorem closedForm_anti (t0 t1 : JI) (h : t0.val ≤ t1.val) (s : Int) :
    closedForm t1 s ≤ closedForm t0 s := by
  unfold closedForm
  by_cases h0 : t0.val < s
  · rw [if_pos h0]; exact u16_le_max _
  · rw [if_neg h0, if_neg (by omega)]; exact Nat.le_refl _

theorem loop_ge_min (bf : List Int) (p t : JI) (stmts : List Stmt) (line : Int) (bc : JI) (y : UInt16)
    (h : inlineCostLoop bf p t stmts line bc = .ok y) : MIN_INLINE_COST ≤ y :=
  Nat.le_trans (clamp_range bc).1 (loop_ge_clamp bf p t stmts line bc y h)

/-- `inline_cost_model(interp, result, inline_flag, ir)` follows the `@inline`/`@noinline`
declarations: a `@noinline` method, a toplevel thunk and a non-`Tuple` signature always get
`MAX_INLINE_COST`; an `@inline` method with a dispatch-tuple signature always gets
`MIN_INLINE_COST`; `@inline` raises the threshold by `19*default` (to 20x) and never makes a
method's cost higher than without the declaration (for parameters up to `2^56`, statements of
lowered code). -/
def InlineCostModelDeclared : Prop :=
  (∀ p r bf stmts, inlineCostModelResult p r SRC_FLAG_DECLARED_NOINLINE bf stmts = .ok MAX_INLINE_COST) ∧
  (∀ p r flag bf stmts, r.defIsMethod = false → inlineCostModelResult p r flag bf stmts = .ok MAX_INLINE_COST) ∧
  (∀ p r flag bf stmts, r.sigIsTuple = false → inlineCostModelResult p r flag bf stmts = .ok MAX_INLINE_COST) ∧
  (∀ p r bf stmts, r.defIsMethod = true → r.sigIsTuple = true → r.isDispatchTuple = true →
    inlineCostModelResult p r SRC_FLAG_DECLARED_INLINE bf stmts = .ok MIN_INLINE_COST) ∧
  (∀ p r, ParamsOK p → (costThreshold p r true).val =
    (costThreshold p r false).val + 19 * p.inline_cost_threshold.val) ∧
  (∀ p r bf stmts cs m x y, ParamsOK p → (∀ s ∈ stmts, StmtOK s) →
    statementCosts true bf p.inline_nonleaf_penalty stmts = .ok (cs, m) →
    inlineCostModelResult p r SRC_FLAG_DECLARED_INLINE bf stmts = .ok x →
    inlineCostModelResult p r 0 bf stmts = .ok y → x ≤ y)

theorem inlineCostModelDeclared_proven : InlineCostModelDeclared := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p r bf stmts; rfl
  · intro p r flag bf stmts h
    unfold inlineCostModelResult; split
    · rfl
    · rw [h]; rfl
  · intro p r flag bf stmts h
    unfold inlineCostModelResult; split
    · rfl
    · split
      · rfl
      · simp [h, pure, Except.pure]
  · intro p r bf stmts h1 h2 h3
    simp [inlineCostModelResult, h1, h2, h3, SRC_FLAG_DECLARED_INLINE, SRC_FLAG_DECLARED_NOINLINE,
      pure, Except.pure]
  · intro p r hp
    rw [threshold_val p hp r true, threshold_val p hp r false]
    simp only [if_true, Bool.false_eq_true, if_false]; omega
  · intro p r bf stmts cs m x y hp hst hc hx hy
    have ⟨d0, d1, b0, b1, p0, p1⟩ := hp
    have t1 := threshold_val p hp r true
    have t0 := threshold_val p hp r false
    simp only [if_true, Bool.false_eq_true, if_false] at t1 t0
    have hb0 : 0 ≤ (costThreshold p r false).val ∧ (costThreshold p r false).val < 2 ^ 62 := by
      rw [t0]; constructor <;> (repeat split) <;> omega
    have hb1 : 0 ≤ (costThreshold p r true).val ∧ (costThreshold p r true).val < 2 ^ 62 := by
      rw [t1]; constructor <;> (repeat split) <;> omega
    have hcf0 := (costModelClosedForm_proven bf _ _ stmts cs m p0 p1 hb0.1 hb0.2 hst hc).1
    have hcf1 := (costModelClosedForm_proven bf _ _ stmts cs m p0 p1 hb1.1 hb1.2 hst hc).1
    have hanti : closedForm (costThreshold p r true) (sumv cs) ≤ closedForm (costThreshold p r false) (sumv cs) :=
      closedForm_anti _ _ (by rw [t0, t1]; (repeat split) <;> omega) _
    have hmin : MIN_INLINE_COST ≤ closedForm (costThreshold p r false) (sumv cs) := by
      unfold closedForm; split
      · decide
      · exact (clamp_range _).1
    have e11 : ((1 : UInt8) == 1) = true := by decide
    have e12 : ((1 : UInt8) == 2) = false := by decide
    have e01 : ((0 : UInt8) == 1) = false := by decide
    have e02 : ((0 : UInt8) == 2) = false := by decide
    cases hdm : r.defIsMethod <;> cases hsig : r.sigIsTuple <;> cases hrt : r.rtIsBottom <;>
      cases hdt : r.isDispatchTuple <;>
      simp only [inlineCostModelResult, hdm, hsig, hrt, hdt, SRC_FLAG_DECLARED_INLINE,
        SRC_FLAG_DECLARED_NOINLINE, e11, e12, e01, e02] at hx hy <;>
      (try simp (config := { decide := true }) only [pure, Except.pure, Except.ok.injEq, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, Bool.true_and, Bool.false_and, Bool.and_true, if_true,
        if_false] at hx hy) <;>
      first
      | (subst hx; subst hy; first | exact Nat.le_refl _ | decide | exact u16_le_max _)
      | (subst hx; rw [hcf0] at hy; cases hy; exact hmin)
      | (subst hy; exact u16_le_max _)
      | (rw [hcf1] at hx; rw [hcf0] at hy; cases hx; cases hy; exact hanti)

/-- With `inline_cost_threshold = 2^59`, `cost_threshold += 19*default` wraps to a negative
threshold, so an `@inline` declaration makes every body uninlineable. Recorded as a lead only. -/
theorem threshold_wraps :
    (costThreshold ⟨ji (2 ^ 59), ji 0, ji 0⟩ ⟨true, true, false, false, false, false, ""⟩ true).val < 0 := by
  decide

/-- The threshold adjustments only add non-negative amounts (`inline_tupleret_bonus`,
`19*default`, `4*default`), so the threshold is never below `inline_cost_threshold`. -/
def ThresholdAtLeastDefault : Prop :=
  ∀ (p : CostParams) (r : ResultFacts) (di : Bool),
    0 ≤ p.inline_cost_threshold.val → 0 ≤ p.inline_tupleret_bonus.val →
    p.inline_cost_threshold.val ≤ (costThreshold p r di).val

/-- `inline_cost_threshold = typemax(Int)` (what GPUCompiler sets to force inlining, per
JuliaLang/julia#60121) with the default `inline_tupleret_bonus = 250`: a method returning a
non-concrete `Tuple` gets the threshold `typemax(Int) + 250`, which wraps to a negative number. -/
theorem thresholdAtLeastDefault_refuted : ¬ ThresholdAtLeastDefault := by
  intro h
  have := h ⟨JInt.typemax .i64, ji 1000, ji 250⟩ ⟨true, true, false, false, true, false, "f"⟩ false
    (by decide) (by decide)
  exact absurd this (by decide)

end JuliaLean.Proofs.Compiler.src.optimize

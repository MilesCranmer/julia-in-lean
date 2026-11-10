import JuliaLean.Proofs.Compiler.src.typelattice.Wrappers

/-!
Properties of `widenconst`, `widenconst_split`, `isalreadyconst`, the layered `tmeet`, the
state merge (`smerge`, `schanged`) and the sub-relations `issubconditional` and `issubalias` of
`Compiler/src/typelattice.jl`.
-/

namespace JuliaLean.Proofs.Compiler.src.typelattice

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## `widenconst` -/

/-- `widenconst(x) -> t::Type` (docstring at `Compiler/src/typelattice.jl:730-734`) on each kind
of element: a conditional widens to `Bool`, an alias to the widening of its field type, a
`PartialTypeVar` to `TypeVar`, a `PartialStruct` and a `PartialOpaque` to their `typ`, a
`PartialTask` to `Task`, a type to itself; a `TypeVar`, a `Vararg` and a `LimitedAccuracy` are
an `ErrorException` ("unhandled ..."), and any other object is a `MethodError`. -/
def WidenconstSpec : Prop :=
  ∀ n E s,
    (∀ x, x.isAnyConditional = true → (widenconst (n + 1) E x).run s = .ok (boolTy, s)) ∧
    (∀ slot d v i f, (widenconst (n + 1) E (.mustAlias slot d v i f)).run s =
      (widenconst n E f).run s) ∧
    (∀ slot v i f, (widenconst (n + 1) E (.interMustAlias slot v i f)).run s =
      (widenconst n E f).run s) ∧
    (∀ tv l u, (widenconst (n + 1) E (.partialTypeVar tv l u)).run s = .ok (tvarType, s)) ∧
    (∀ typ u f ui fi, (widenconst (n + 1) E (.partialStruct typ u f ui fi)).run s = .ok (typ, s)) ∧
    (∀ typ env p src, (widenconst (n + 1) E (.partialOpaque typ env p src)).run s = .ok (typ, s)) ∧
    (∀ ft, (widenconst (n + 1) E (.partialTask ft)).run s = .ok (taskType, s)) ∧
    (∀ v, v.isType = false → (widenconst (n + 1) E (.const v)).run s = .ok (typeOf v, s)) ∧
    (∀ t, t.isType = true → (widenconst (n + 1) E (.ty t)).run s = .ok (t, s)) ∧
    (∀ t, t.isTypevar = true → ThrowsJulia "ErrorException" (widenconst (n + 1) E (.ty t))) ∧
    (∀ t, t.isVararg = true → ThrowsJulia "ErrorException" (widenconst (n + 1) E (.ty t))) ∧
    (∀ t cs cid, ThrowsJulia "ErrorException" (widenconst (n + 1) E (.limitedAccuracy t cs cid)))

theorem widenconstSpec_proven : WidenconstSpec := by
  intro n E s
  refine ⟨?_, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, fun _ _ _ s => ⟨_, rfl⟩⟩
  · intro x hx
    cases x <;> first | rfl | (simp [LElt.isAnyConditional, LElt.isConditional,
      LElt.isInterConditional] at hx)
  · intro v hv
    show (if v.isType = true then _ else pure (typeOf v) : CM Val).run s = _
    rw [if_neg (by simp [hv])]; rfl
  · intro t ht
    show (if t.isType = true then pure t else _ : CM Val).run s = _
    rw [if_pos ht]; rfl
  · intro t ht s
    cases t <;> simp [Val.isTypevar] at ht
    exact ⟨"unhandled TypeVar", rfl⟩
  · intro t ht s
    cases t <;> simp [Val.isVararg] at ht
    exact ⟨"unhandled Vararg", rfl⟩

/-- `widenconst_split(x)` is a version of `widenconst` written for union splitting
(`Compiler/src/typelattice.jl:751-764`); it returns the same result as `widenconst` on every
element (given the one step of fuel `widenconst` needs). -/
def WidenconstSplitAgrees : Prop :=
  ∀ n E x s, 1 ≤ n → (widenconstSplit n E x).run s = (widenconst n E x).run s

theorem widenconstSplitAgrees_proven : WidenconstSplitAgrees := by
  intro n E x s hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  cases x
  case ty t =>
    cases ht : t.isType
    · unfold widenconstSplit
      simp only [ht]
      rfl
    · unfold widenconstSplit
      simp only [ht]
      show (pure t : CM Val).run s = (if t.isType = true then pure t else _ : CM Val).run s
      rw [if_pos ht]
  all_goals rfl

/-! ## `isalreadyconst` -/

/-- `isalreadyconst(t)` holds for every `Const`, and never for a lattice element that is neither
a `Const` nor a native type (a `PartialStruct` of constants, a slot wrapper, ... are not "already
constant"). A native type is already constant when it is a singleton type (its one instance is
known), and otherwise exactly when `isconstType` holds (a `Type{T}` that pins one type object). -/
def IsalreadyconstSpec : Prop :=
  ∀ n E,
    (∀ t, (t.isConst = true → ∀ s, (isalreadyconst n E t).run s = .ok (true, s)) ∧
      Returns (isalreadyconst n E t) fun r => r = true → t.isConst = true ∨ ∃ T, t = .ty T) ∧
    (∀ T s s₁, (issingletontype n E T).run s = .ok (true, s₁) →
      (isalreadyconst n E (.ty T)).run s = .ok (true, s₁)) ∧
    (∀ T s s₁, (issingletontype n E T).run s = .ok (false, s₁) →
      (isalreadyconst n E (.ty T)).run s = .ok (isconstType T, s₁))

theorem isalreadyconstSpec_proven : IsalreadyconstSpec := by
  intro n E
  refine ⟨fun t => ⟨fun h s => ?_, fun s r s' h => ?_⟩, fun T s s₁ h => ?_, fun T s s₁ h => ?_⟩
  · cases t <;> first | rfl | (simp [LElt.isConst] at h)
  · intro hr
    cases t
    case const => exact Or.inl rfl
    case ty T => exact Or.inr ⟨T, rfl⟩
    all_goals (cases h; cases hr)
  · refine (run_bind_ok h).trans ?_
    rfl
  · refine (run_bind_ok h).trans ?_
    rfl

/-! ## The layered `tmeet` -/

/-- `tmeet(::ConditionalsLattice, c::Conditional, t)`: the meet of a conditional with a type is
the conditional itself when `Bool <: t`, and `Union{}` otherwise (a `Bool` value is in `t` or not;
`Bool` has no proper subtype but `Union{}`). Which of the two is decided by `Bool <: t`, and an
element that is not a `Conditional` is met in the parent layer. -/
def TmeetConditionalSpec : Prop :=
  (∀ ops n E p v t, v.isConditional = true → t.isType = true →
    Returns (tmeet ops (n + 1) E (.conditionals p) v t) fun r => r = v ∨ r = .ty .bottom) ∧
  (∀ ops n E p v t s s₁, v.isConditional = true → t.isType = true →
    (issub n E boolTy t).run s = .ok (true, s₁) →
    (tmeet ops (n + 1) E (.conditionals p) v t).run s = .ok (v, s₁)) ∧
  (∀ ops n E p v t s s₁, v.isConditional = true → t.isType = true →
    (issub n E boolTy t).run s = .ok (false, s₁) →
    (tmeet ops (n + 1) E (.conditionals p) v t).run s = .ok (.ty .bottom, s₁)) ∧
  (∀ ops n E p v t s, v.isConditional = false → t.isType = true →
    (tmeet ops (n + 1) E (.conditionals p) v t).run s = (tmeet ops n E p v t).run s)

theorem tmeetConditionalSpec_proven : TmeetConditionalSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left
  · intro ops n E p v t s s₁ hv ht h
    rw [tmeet.eq_def]; dsimp only; rw [if_neg (by simp [ht])]; (try dsimp only)
    rw [if_pos hv, run_bind_ok h]
    rfl
  · intro ops n E p v t s s₁ hv ht h
    rw [tmeet.eq_def]; dsimp only; rw [if_neg (by simp [ht])]; (try dsimp only)
    rw [if_pos hv, run_bind_ok h]
    rfl
  · intro ops n E p v t s hv ht
    rw [tmeet.eq_def]; dsimp only; rw [if_neg (by simp [ht])]; (try dsimp only)
    rw [if_neg (by simp [hv])]
  intro ops n E p v t hv ht s r s' h
  rw [tmeet.eq_def] at h
  dsimp only at h
  rw [if_neg (by simp [ht])] at h
  try dsimp only at h
  rw [if_pos hv] at h
  obtain ⟨c, s₁, _, hk⟩ := run_bind_inv h
  cases c
  · cases hk; exact Or.inr rfl
  · cases hk; exact Or.inl rfl

/-- `tmeet(::ConstsLattice, Const(x), t)`: the meet of a constant with a closed type is the
constant when `x isa t`, and `Union{}` otherwise; for a type with free type variables the
constant is kept. Any other element is widened by `widenconst_split` and met in `JLTypeLattice`. -/
def TmeetConstsSpec : Prop :=
  ∀ ops n E v t, t.isType = true →
    (∀ x, v = .const x →
      Returns (tmeet ops (n + 1) E .consts v t) fun r => r = v ∨ r = .ty .bottom) ∧
    (v.isConst = false → ∀ s,
      (tmeet ops (n + 1) E .consts v t).run s =
        (widenconstSplit n E v >>= fun w => tmeet ops n E .jlType (.ty w) t).run s) ∧
    (∀ x s s₁, JuliaLean.Compiler.hasFreeTypevars t = false →
      (isa n E x t).run s = .ok (true, s₁) →
      (tmeet ops (n + 1) E .consts (.const x) t).run s = .ok (.const x, s₁)) ∧
    (∀ x s s₁, JuliaLean.Compiler.hasFreeTypevars t = false →
      (isa n E x t).run s = .ok (false, s₁) →
      (tmeet ops (n + 1) E .consts (.const x) t).run s = .ok (.ty .bottom, s₁)) ∧
    (∀ x s, JuliaLean.Compiler.hasFreeTypevars t = true →
      (tmeet ops (n + 1) E .consts (.const x) t).run s = .ok (.const x, s))

theorem tmeetConstsSpec_proven : TmeetConstsSpec := by
  intro ops n E v t ht
  refine ⟨fun x hx s r s' h => ?_, fun hv s => ?_, fun x s s₁ hf h => ?_, fun x s s₁ hf h => ?_,
    fun x s hf => ?_⟩
  rotate_left 2
  · rw [tmeet.eq_def]; dsimp only; rw [if_neg (by simp [ht])]; (try dsimp only)
    rw [if_pos (by simp [hf]), run_bind_ok h]
    rfl
  · rw [tmeet.eq_def]; dsimp only; rw [if_neg (by simp [ht])]; (try dsimp only)
    rw [if_pos (by simp [hf]), run_bind_ok h]
    rfl
  · rw [tmeet.eq_def]; dsimp only; rw [if_neg (by simp [ht])]; (try dsimp only)
    rw [if_neg (by simp [hf])]
    rfl
  · subst hx
    rw [tmeet.eq_def] at h
    dsimp only at h
    rw [if_neg (by simp [ht])] at h
    try dsimp only at h
    split at h
    · obtain ⟨c, s₁, _, hk⟩ := run_bind_inv h
      cases c
      · cases hk; exact Or.inr rfl
      · cases hk; exact Or.inl rfl
    · cases h; exact Or.inl rfl
  · rw [tmeet.eq_def]
    dsimp only
    rw [if_neg (by simp [ht])]
    cases v <;> first | rfl | (simp [LElt.isConst] at hv)

/-- `tmeet(::InferenceLattice, v, t)` and `tmeet(::InterConditionalsLattice, v, t)` assert that
`v` is not a `LimitedAccuracy`, respectively not a conditional ("TODO: This can probably happen
and should be handled", `Compiler/src/typelattice.jl:718,724`); every other element is passed to
the parent layer unchanged. -/
def TmeetAssertSpec : Prop :=
  ∀ ops n E p v t, t.isType = true →
    (v.isLimited = true → ThrowsJulia "AssertionError" (tmeet ops (n + 1) E (.inference p) v t)) ∧
    (v.isLimited = false → ∀ s,
      (tmeet ops (n + 1) E (.inference p) v t).run s = (tmeet ops n E p v t).run s) ∧
    (v.isAnyConditional = true →
      ThrowsJulia "AssertionError" (tmeet ops (n + 1) E (.interConditionals p) v t)) ∧
    (v.isAnyConditional = false → ∀ s,
      (tmeet ops (n + 1) E (.interConditionals p) v t).run s = (tmeet ops n E p v t).run s)

theorem tmeetAssertSpec_proven : TmeetAssertSpec := by
  intro ops n E p v t ht
  have hnt : ¬ ((!t.isType) = true) := by simp [ht]
  refine ⟨fun hv s => ⟨"!isa(v, LimitedAccuracy)", ?_⟩, fun hv s => ?_,
    fun hv s => ⟨"!isa(v, AnyConditional)", ?_⟩, fun hv s => ?_⟩
  · rw [tmeet.eq_def]; dsimp only; rw [if_neg hnt]; (try dsimp only); rw [if_pos hv]; rfl
  · rw [tmeet.eq_def]; dsimp only; rw [if_neg hnt]; (try dsimp only)
    rw [if_neg (by simp [hv])]
  · rw [tmeet.eq_def]; dsimp only; rw [if_neg hnt]; (try dsimp only); rw [if_pos hv]; rfl
  · rw [tmeet.eq_def]; dsimp only; rw [if_neg hnt]; (try dsimp only)
    rw [if_neg (by simp [hv])]

end JuliaLean.Proofs.Compiler.src.typelattice

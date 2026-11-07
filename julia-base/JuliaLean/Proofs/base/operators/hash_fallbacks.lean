import JuliaLean.base.operators

namespace JuliaLean.HashOps

open JuliaLean JuliaLean.Promotion

/-- A strict weak order, matching the `isless` contract. -/
def StrictWeak {α : Type} (lt : α → α → Bool) : Prop :=
  (∀ a, lt a a = false) ∧
  (∀ a b c, lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b c, lt a b = false → lt b a = false → lt b c = false → lt c b = false →
    lt a c = false ∧ lt c a = false)

/-- `isless(::Real,::Real)` inherits a strict weak order from `<`, and generic
`cmp` returns exactly the sign selected by the two isless calls. -/
def ComparisonFallbacks : Prop :=
  ∀ (α : Type) (o : FallbackOps α), StrictWeak o.lt →
    StrictWeak (islessFallback o) ∧
    ∀ x y, cmpFallback o x y =
      (if islessFallback o x y then -1 else if islessFallback o y x then 1 else 0)

/-- Direct equations promised by the generic operator fallbacks. -/
def OperatorFallbacks : Prop :=
  ∀ (α : Type) (o : FallbackOps α) (x y : α),
    isequalFallback o x y = o.eq x y ∧
    neFallback o x y = !o.eq x y ∧
    leFallback o x y = (o.lt x y || o.eq x y) ∧
    geFallback o x y = (o.lt y x || o.eq y x)

/-- The widen docstring's guarantee for both addition and subtraction. -/
def WidenNoLoss : Prop :=
  ∀ (t : IntTy) (x y : JInt t),
    widenAdd t x y = x.val + y.val ∧ widenSub t x y = x.val - y.val

theorem comparisonFallbacks_proven : ComparisonFallbacks := by
  intro α o h
  exact ⟨h, fun _ _ => rfl⟩

theorem operatorFallbacks_proven : OperatorFallbacks := by
  intro α o x y
  simp [isequalFallback, neFallback, leFallback, geFallback]

theorem widenNoLoss_refuted : ¬ WidenNoLoss := by
  intro h
  have bad := (h .u8 (JInt.lit .u8 0) (JInt.lit .u8 255)).2
  revert bad
  decide

end JuliaLean.HashOps

import JuliaLean.base.checked

/-!
Coverage models for active methods in `base/checked.jl` at Julia
`bbfa0ce4150`.  Arithmetic primitives and the 128-bit fallback are reused from
`JuliaLean.IntArith.Checked`; this file models the dispatch wrappers, error
helpers, Boolean special cases, and fixed-arity folds which were not themselves
the subject of an existing registry proposition.
-/

namespace JuliaLean.FloatIntCov.Checked

open JuliaLean JuliaLean.IntArith.Checked


/-- The eight promoted entry points use the common source-order promotion wrapper. -/
def PromotedCallsSourceOrder : Prop :=
  ∀ (t s : IntTy) (x : JInt t) (y : JInt s),
    promotedCalls x y =
      (promoted @checkedAdd x y, promoted @checkedSub x y,
       promoted @checkedMul x y, promoted @checkedDiv x y,
       promoted @checkedRem x y, promoted @checkedFld x y,
       promoted @checkedMod x y, promoted @checkedCld x y)

theorem promotedCallsSourceOrder : PromotedCallsSourceOrder := by
  intro t s x y
  rfl


/-- Every value reaching the fallback gets the source's no-operation error. -/
def CheckedAbsFallbackErrors : Prop :=
  ∀ (α : Type) (x : α), checkedAbsFallback x = .error (.methodError "checked_abs")

theorem checkedAbsFallbackErrors : CheckedAbsFallbackErrors := by
  intro α x
  rfl


def OverflowHelpersThrow : Prop :=
  (∀ (α β : Type) (x : α),
    throwOverflowNegation (β := β) x = .error (.overflowError "")) ∧
  (∀ (α β γ δ : Type) (op : α) (x : β) (y : γ),
    throwOverflowBinary (δ := δ) op x y = .error (.overflowError ""))

theorem overflowHelpersThrow : OverflowHelpersThrow := by
  constructor <;> intros <;> rfl


/-- The Boolean special cases are exact and never set an overflow flag. -/
def BoolSpecialCasesExact : Prop :=
  (∀ x, checkedAbsBool x = x) ∧
  (∀ x, checkedAddBool x = boolInt x) ∧
  (∀ x y, addWithOverflowBool x y = (boolInt x + boolInt y, false)) ∧
  (∀ x y, subWithOverflowBool x y = (boolInt x - boolInt y, false)) ∧
  (∀ x y, mulWithOverflowBool x y = (boolInt x * boolInt y, false))

theorem boolSpecialCasesExact : BoolSpecialCasesExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl


/-- Active overflow methods delegate to the corresponding faithful arithmetic model. -/
def WithOverflowMethodsDelegate : Prop :=
  (∀ (t : IntTy) (x y : JInt t),
    addWithOverflowMethod x y = addWithOverflow x y) ∧
  (∀ (t : IntTy) (x y : JInt t),
    subWithOverflowMethod x y = subWithOverflow x y) ∧
  (∀ (t : IntTy) (x y : JInt t),
    mulWithOverflowMethod x y = mulWithOverflow x y)

theorem withOverflowMethodsDelegate : WithOverflowMethodsDelegate := by
  repeat' apply And.intro
  all_goals intros <;> rfl


/-- Every fixed-arity method performs the first binary operation first. -/
def FixedAritySourceOrder : Prop :=
  (∀ (t : IntTy) (x : JInt t), checkedUnary x = .ok x) ∧
  (∀ (t : IntTy) (x y : JInt t) (xs : List (JInt t)),
    checkedAddList x (y :: xs) = (checkedAdd x y >>= fun z => checkedAddList z xs)) ∧
  (∀ (t : IntTy) (x y : JInt t) (xs : List (JInt t)),
    checkedMulList x (y :: xs) = (checkedMul x y >>= fun z => checkedMulList z xs))

theorem fixedAritySourceOrder : FixedAritySourceOrder := by
  constructor
  · intros
    rfl
  constructor <;> intros <;> rfl


/-- Boolean checked power is total for nonnegative exponents and only `true` accepts a negative one. -/
def CheckedPowerBoolContract : Prop :=
  ∀ (x : Bool) (p : Int),
    checkedPowerBool x p =
      if p < 0 then
        if x then .ok true else .error (.domainError "")
      else if p = 0 then .ok true
      else .ok x

theorem checkedPowerBoolContract : CheckedPowerBoolContract := by
  unfold CheckedPowerBoolContract
  intros
  rfl

/-- The generic checked-length fallback is the source's direct `length` call. -/
def CheckedLengthDelegates : Prop :=
  ∀ (α β : Type) (length : α → Jl β) (r : α), checkedLength length r = length r

theorem checkedLengthDelegates : CheckedLengthDelegates := by
  unfold CheckedLengthDelegates
  intros
  rfl

end JuliaLean.FloatIntCov.Checked

import JuliaLean.IntArith.Checked

/-!
Coverage models for active methods in `base/checked.jl` at Julia
`bbfa0ce4150`.  Arithmetic primitives and the 128-bit fallback are reused from
`JuliaLean.IntArith.Checked`; this file models the dispatch wrappers, error
helpers, Boolean special cases, and fixed-arity folds which were not themselves
the subject of an existing registry proposition.
-/

namespace JuliaLean.FloatIntCov.Checked

open JuliaLean JuliaLean.IntArith.Checked

/-- `base/checked.jl:26-33`: promote both operands, then call the operation. -/
def promotedCalls {t s : IntTy} (x : JInt t) (y : JInt s) :=
  (checkedAddMixed x y, checkedSubMixed x y, checkedMulMixed x y,
   checkedDivMixed x y, checkedRemMixed x y, checkedFldMixed x y,
   checkedModMixed x y, checkedCldMixed x y)

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

/-- `base/checked.jl:37`: the catchall reports that the operation is absent. -/
def checkedAbsFallback {α : Type} (_x : α) : Jl α :=
  .error (.methodError "checked_abs")

/-- Every value reaching the fallback gets the source's no-operation error. -/
def CheckedAbsFallbackErrors : Prop :=
  ∀ (α : Type) (x : α), checkedAbsFallback x = .error (.methodError "checked_abs")

theorem checkedAbsFallbackErrors : CheckedAbsFallbackErrors := by
  intro α x
  rfl

/-- `base/checked.jl:92-93`: the negation overflow helper always throws. -/
def throwOverflowNegation {α β : Type} (_x : α) : Jl β :=
  .error (.overflowError "")

/-- `base/checked.jl:156-157`: the binary overflow helper always throws. -/
def throwOverflowBinary {α β γ δ : Type} (_op : α) (_x : β) (_y : γ) : Jl δ :=
  .error (.overflowError "")

def OverflowHelpersThrow : Prop :=
  (∀ (α β : Type) (x : α),
    throwOverflowNegation (β := β) x = .error (.overflowError "")) ∧
  (∀ (α β γ δ : Type) (op : α) (x : β) (y : γ),
    throwOverflowBinary (δ := δ) op x y = .error (.overflowError ""))

theorem overflowHelpersThrow : OverflowHelpersThrow := by
  constructor <;> intros <;> rfl

/-- Julia's integer value of a Boolean in the arithmetic special cases. -/
def boolInt (x : Bool) : Int := if x then 1 else 0

/-- `base/checked.jl:128`. -/
def checkedAbsBool (x : Bool) : Bool := x

/-- `base/checked.jl:138`: Bool wrapping addition promotes to `Int`. -/
def addWithOverflowBool (x y : Bool) : Int × Bool :=
  (boolInt x + boolInt y, false)

/-- `base/checked.jl:179`: unary plus on Bool promotes to `Int`. -/
def checkedAddBool (x : Bool) : Int := boolInt x

/-- `base/checked.jl:202`: Bool subtraction promotes to `Int`. -/
def subWithOverflowBool (x y : Bool) : Int × Bool :=
  (boolInt x - boolInt y, false)

/-- `base/checked.jl:241`: Bool wrapping multiplication promotes to `Int`. -/
def mulWithOverflowBool (x y : Bool) : Int × Bool :=
  (boolInt x * boolInt y, false)

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

/-- The active `add_with_overflow` methods at `base/checked.jl:136-137`. -/
def addWithOverflowMethod {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  addWithOverflow x y

/-- The active `sub_with_overflow` methods at `base/checked.jl:200-201`. -/
def subWithOverflowMethod {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  subWithOverflow x y

/-- The active intrinsic and 128-bit `mul_with_overflow` methods at lines 239-240 and 259-280. -/
def mulWithOverflowMethod {t : IntTy} (x y : JInt t) : Jl (JInt t × Bool) :=
  mulWithOverflow x y

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

/-- `base/checked.jl:178,298`: a unary checked fold is the identity. -/
def checkedUnary {t : IntTy} (x : JInt t) : Jl (JInt t) := .ok x

/-- `base/checked.jl:181-192`: left-associated fixed-arity checked addition. -/
def checkedAddList {t : IntTy} : JInt t → List (JInt t) → Jl (JInt t)
  | x, [] => .ok x
  | x, y :: ys => do checkedAddList (← checkedAdd x y) ys

/-- `base/checked.jl:299-310`: left-associated fixed-arity checked multiplication. -/
def checkedMulList {t : IntTy} : JInt t → List (JInt t) → Jl (JInt t)
  | x, [] => .ok x
  | x, y :: ys => do checkedMulList (← checkedMul x y) ys

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

/-- `base/checked.jl:368`: Boolean checked powers use ordinary Boolean powers. -/
def checkedPowerBool (x : Bool) (p : Int) : Jl Bool :=
  if p < 0 then
    if x then .ok true else .error (.domainError "")
  else if p = 0 then .ok true
  else .ok x

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

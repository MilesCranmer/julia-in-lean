import JuliaLean.base.div
import JuliaLean.base.promotion
import JuliaLean.Registry.Types

/-!
Coverage models for `base/div.jl` at Julia `bbfa0ce4150`.  Fixed-width
integer paths reuse `IntArith.Division`; binary64 paths reuse `Float.F64`.
-/

namespace JuliaLean.FloatIntCov.Div

open JuliaLean
open JuliaLean.IntArith.Division
open JuliaLean.Float

private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)


def IntegerModeDispatch : Prop :=
  (∀ x y : Value, divMode x y = (divremMode x y .toZero >>= fun qr => pure qr.1)) ∧
  (∀ x y : Value, remMode x y .toZero = rem promotedRem x y) ∧
  (∀ x y : Value, remMode x y .down = mod (rem promotedRem) x y) ∧
  (∀ x y : Value, remMode x y .up = mod (rem promotedRem) x (negValue y)) ∧
  (∀ x y : Value, remMode x y .fromZero =
    if signbit x = signbit y then mod (rem promotedRem) x (negValue y) else mod (rem promotedRem) x y) ∧
  (∀ x y : Value, fldMethod x y = divMode x y .down) ∧
  (∀ x y : Value, cldMethod x y = divMode x y .up) ∧
  (∀ x y : Value, fld1Method x y = cldMethod x y) ∧
  (∀ x y : Value, fldmodMethod x y = divremMode x y .down)

theorem integerModeDispatch : IntegerModeDispatch := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-- The divrem docstring promises equality with separate div and rem calls. -/
def DivremProjectionConsistency : Prop :=
  ∀ x y : Value, ∀ m : Mode,
    divremMode x y m = do
      let q ← divMode x y m
      let r ← remMode x y m
      pure (q, r)

set_option maxRecDepth 10000 in
theorem divremProjectionConsistency_refuted : ¬ DivremProjectionConsistency := by
  intro h
  have bad := h (lit .i8 (-127)) (lit .i8 (-128)) .up
  exact (by decide : ¬(divremMode (lit .i8 (-127)) (lit .i8 (-128)) .up = do
    let q ← divMode (lit .i8 (-127)) (lit .i8 (-128)) .up
    let r ← remMode (lit .i8 (-127)) (lit .i8 (-128)) .up
    pure (q, r))) bad

def IntegerDivremSourceOrder : Prop :=
  (∀ x y : Value, directedDivrem x y .toZero = divrem promotedDivrem x y) ∧
  (∀ x y : Value, directedDivrem x y .down = do
    let q ← fld x y
    pure (q, sub x (mul q y))) ∧
  (∀ x y : Value, directedDivrem x y .up = do
    let q ← cld x y
    pure (q, sub x (mul q y))) ∧
  (∀ x y : Value, divremMode x y .fromZero =
    if signbit x = signbit y then directedDivrem x y .up else directedDivrem x y .down)

theorem integerDivremSourceOrder : IntegerDivremSourceOrder := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def NearestDivremDispatch : Prop :=
  (∀ x y : Value, divremMode x y .nearest = nearestDivrem x y .nearest) ∧
  (∀ x y : Value, divremMode x y .tiesAway = nearestDivrem x y .tiesAway) ∧
  (∀ x y : Value, divremMode x y .tiesUp = nearestDivrem x y .tiesUp)

theorem nearestDivremDispatch : NearestDivremDispatch := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def BoolDivisionIgnoresMode : Prop :=
  ∀ m x y, boolDiv m x y = if !y then .error .divideError else .ok x

theorem boolDivisionIgnoresMode : BoolDivisionIgnoresMode := by
  unfold BoolDivisionIgnoresMode
  intros
  rfl


def FloatModeDispatch : Prop :=
  (∀ x y, floatRemMode x y .toZero = F64.rem x y) ∧
  (∀ x y, floatRemMode x y .down = F64.mod x y) ∧
  (∀ x y, floatRemMode x y .up = F64.mod x (F64.neg y)) ∧
  (∀ x y, floatRemMode x y .nearest = F64.remMode x y .RoundNearest) ∧
  (∀ x y, floatRemMode x y .tiesAway = floatTieRem x y false) ∧
  (∀ x y, floatRemMode x y .tiesUp = floatTieRem x y true) ∧
  (∀ rounder x y m, floatDivMode rounder x y m =
    rounder (F64.sub (F64.div x y) (F64.div (floatRemMode x y m) y)) m)

theorem floatModeDispatch : FloatModeDispatch := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def GenericRoutesSourceOrder : Prop :=
  (∀ (α : Type) divRound (x y : α), defaultDiv divRound x y = divRound x y .toZero) ∧
  (∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α),
    genericRemMode rem mod neg sub mul divRound signbit x y .toZero = rem x y) ∧
  (∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α),
    genericRemMode rem mod neg sub mul divRound signbit x y .down = mod x y) ∧
  (∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α),
    genericRemMode rem mod neg sub mul divRound signbit x y .up = mod x (neg y)) ∧
  (∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α),
    genericRemMode rem mod neg sub mul divRound signbit x y .nearest = do
      pure (sub x (mul y (← divRound x y .nearest)))) ∧
  (∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α),
    genericRemMode rem mod neg sub mul divRound signbit x y .fromZero =
      if signbit x == signbit y then mod x (neg y) else mod x y) ∧
  (∀ (α : Type) divRound (x y : α), genericFld divRound x y = divRound x y .down) ∧
  (∀ (α : Type) divRound (x y : α), genericCld divRound x y = divRound x y .up) ∧
  (∀ (α : Type) div rem fld mod divRound remRound (x y : α),
    genericDivrem div rem fld mod divRound remRound x y .toZero = do
      pure (← div x y, ← rem x y)) ∧
  (∀ (α : Type) div rem fld mod divRound remRound (x y : α),
    genericDivrem div rem fld mod divRound remRound x y .down = do
      pure (← fld x y, ← mod x y)) ∧
  (∀ (α : Type) promote div divRound (x y : α) m,
    promotedDiv false promote div divRound x y m =
      let p := promote x y
      if m = .toZero then div p.1 p.2 .toZero else divRound p.1 p.2 m)

theorem genericRoutesSourceOrder : GenericRoutesSourceOrder := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.FloatIntCov.Div

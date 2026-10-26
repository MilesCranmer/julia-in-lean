import JuliaLean.IntArith.Division
import JuliaLean.Float.Extras

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

inductive Mode where
  | toZero | down | up | nearest | tiesAway | tiesUp | fromZero
  deriving DecidableEq, Repr

/-- `base/div.jl:326-373`: nearest integer quotient adjustments. -/
def nearestDivrem (x y : Value) (mode : Mode) : Jl (Value × Value) := do
  let (q, r) ← divrem x y
  let yh := y.int.val.tdiv 2
  let odd := y.int.val % 2 != 0
  let evenq := q.int.val % 2 = 0
  let adjustUp := match mode with
    | .nearest => odd || evenq
    | .tiesAway | .tiesUp => odd
    | _ => false
  let posAdjust := add q (lit q.ty 1)
  let negAdjust := sub q (lit q.ty 1)
  if x.int.val ≥ 0 then
    if y.int.val ≥ 0 then
      if r.int.val ≥ yh + (if adjustUp then 1 else 0) then pure (posAdjust, sub r y) else pure (q, r)
    else
      let tie := if mode = .tiesUp then 1 else if adjustUp then 1 else 0
      if r.int.val ≥ -yh + tie then pure (negAdjust, add r y) else pure (q, r)
  else if y.int.val ≥ 0 then
    let tie := if mode = .tiesUp then 1 else if adjustUp then 1 else 0
    if r.int.val ≤ -yh - tie then pure (negAdjust, add r y) else pure (q, r)
  else if r.int.val ≤ yh - (if adjustUp then 1 else 0) then pure (posAdjust, sub r y)
  else pure (q, r)

/-- `base/div.jl:290-325`: quotient first, then source-type reconstruction. -/
def directedDivrem (x y : Value) : Mode → Jl (Value × Value)
  | .toZero => divrem x y
  | .down => do
      let q ← fld x y
      pure (q, sub x (mul q y))
  | .up => do
      let q ← cld x y
      pure (q, sub x (mul q y))
  | m => nearestDivrem x y m

/-- `base/div.jl:273-286,375-377`: complete mode dispatch. -/
def divremMode (x y : Value) : Mode → Jl (Value × Value)
  | .toZero => directedDivrem x y .toZero
  | .down => directedDivrem x y .down
  | .up => directedDivrem x y .up
  | .nearest => nearestDivrem x y .nearest
  | .tiesAway => nearestDivrem x y .tiesAway
  | .tiesUp => nearestDivrem x y .tiesUp
  | .fromZero => if signbit x = signbit y then directedDivrem x y .up else directedDivrem x y .down

/-- `base/div.jl:77,127-138,196,243,252,387,391-475`. -/
def divMode (x y : Value) (m : Mode := .toZero) : Jl Value := do
  pure (← divremMode x y m).1

def negValue (x : Value) : Value := pack (-x.int)

/-- The actual remainder methods at `base/div.jl:127-138`; unlike `divrem`,
RoundUp negates the fixed-width divisor before calling mod. -/
def remMode (x y : Value) : Mode → Jl Value
  | .toZero => rem x y
  | .down => mod x y
  | .up => mod x (negValue y)
  | .nearest => do pure (← divremMode x y .nearest).2
  | .tiesAway => do pure (← divremMode x y .tiesAway).2
  | .tiesUp => do pure (← divremMode x y .tiesUp).2
  | .fromZero => if signbit x = signbit y then mod x (negValue y) else mod x y

def fldMethod (x y : Value) : Jl Value := divMode x y .down
def cldMethod (x y : Value) : Jl Value := divMode x y .up
def fld1Method (x y : Value) : Jl Value := cldMethod x y
def fldmodMethod (x y : Value) : Jl (Value × Value) := divremMode x y .down

def IntegerModeDispatch : Prop :=
  (∀ x y : Value, divMode x y = (divremMode x y .toZero >>= fun qr => pure qr.1)) ∧
  (∀ x y : Value, remMode x y .toZero = rem x y) ∧
  (∀ x y : Value, remMode x y .down = mod x y) ∧
  (∀ x y : Value, remMode x y .up = mod x (negValue y)) ∧
  (∀ x y : Value, remMode x y .fromZero =
    if signbit x = signbit y then mod x (negValue y) else mod x y) ∧
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
  (∀ x y : Value, directedDivrem x y .toZero = divrem x y) ∧
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

/-- `base/div.jl:422-430`: Bool division ignores the supplied rounding mode. -/
def boolDiv (_mode : Mode) (x y : Bool) : Jl Bool :=
  if !y then .error .divideError else .ok x

def BoolDivisionIgnoresMode : Prop :=
  ∀ m x y, boolDiv m x y = if !y then .error .divideError else .ok x

theorem boolDivisionIgnoresMode : BoolDivisionIgnoresMode := by
  unfold BoolDivisionIgnoresMode
  intros
  rfl

/-- `base/div.jl:139-149`: Float64 nearest ties-away and ties-up remainder. -/
def floatTieRem (x y : F64) (tiesUp : Bool) : F64 := Id.run do
  let r := F64.mod x y
  if F64.isnan r then return r
  if !F64.iszero r then
    let two := F64.ofInt 2
    let (m, n) := if F64.lt (F64.abs r) (F64.div F64.floatmax two)
      then (F64.abs (F64.mul two r), F64.abs y)
      else (F64.abs r, F64.abs (F64.div y two))
    if F64.lt m n then return r
    if F64.lt n m then return F64.mod x (F64.neg y)
  return if tiesUp || F64.signbit x == F64.signbit y then F64.mod x (F64.neg y) else r

/-- Binary64 remainder dispatch at `base/div.jl:127-149`. -/
def floatRemMode (x y : F64) : Mode → F64
  | .toZero => F64.rem x y
  | .down => F64.mod x y
  | .up => F64.mod x (F64.neg y)
  | .nearest => F64.remMode x y .RoundNearest
  | .tiesAway => floatTieRem x y false
  | .tiesUp => floatTieRem x y true
  | .fromZero => if F64.signbit x == F64.signbit y then F64.mod x (F64.neg y) else F64.mod x y

/-- `base/div.jl:480`, with the requested integral-rounding primitive explicit. -/
def floatDivMode (rounder : F64 → Mode → F64) (x y : F64) (m : Mode) : F64 :=
  rounder (F64.sub (F64.div x y) (F64.div (floatRemMode x y m) y)) m

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

/-- Generic compatibility/promotion routes at `base/div.jl:276-286,438-455`. -/
def defaultDiv {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) : Jl α :=
  divRound x y .toZero

def genericRemMode {α : Type} (rem mod : α → α → Jl α) (neg : α → α)
    (sub mul : α → α → α) (divRound : α → α → Mode → Jl α)
    (signbit : α → Bool) (x y : α) : Mode → Jl α
  | .toZero => rem x y
  | .down => mod x y
  | .up => mod x (neg y)
  | .nearest => do pure (sub x (mul y (← divRound x y .nearest)))
  | .fromZero => if signbit x == signbit y then mod x (neg y) else mod x y
  | m => do pure (sub x (mul y (← divRound x y m)))

def genericFld {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) : Jl α :=
  divRound x y .down

def genericCld {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) : Jl α :=
  divRound x y .up

def genericDivrem {α : Type} (div rem fld mod : α → α → Jl α)
    (divRound remRound : α → α → Mode → Jl α) (x y : α) (m : Mode) : Jl (α × α) :=
  match m with
  | .toZero => do pure (← div x y, ← rem x y)
  | .down => do pure (← fld x y, ← mod x y)
  | _ => do pure (← divRound x y m, ← remRound x y m)

def promotedDiv {α : Type} (sameType : Bool) (promote : α → α → α × α)
    (div divRound : α → α → Mode → Jl α) (x y : α) (m : Mode) : Jl α :=
  if sameType then .error (.methodError "div")
  else
    let p := promote x y
    if m = .toZero then div p.1 p.2 .toZero else divRound p.1 p.2 m

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

import JuliaLean.base.bool
import JuliaLean.Registry.Types
import JuliaLean.base.float

/-!
# Properties of `base/bool.jl`

The properties state arithmetic, ordering, and IEEE guarantees for the source-mirrored methods.
Calls into other Julia files remain typed parameters.
-/

namespace JuliaLean.Proofs.base.bool

open JuliaLean JuliaLean.Promotion JuliaLean.Registry JuliaLean.base.bool

/-! Nothing to promise: >>(x::Bool, c::UInt)@123: converts to Int and forwards to Int shift. -/
/-! Nothing to promise: <<(x::Bool, c::UInt)@124: converts to Int and forwards to Int shift. -/
/-! Nothing to promise: >>>(x::Bool, c::UInt)@125: converts to Int and forwards to Int shift. -/
/-! Nothing to promise: +(y::AbstractFloat, x::Bool)@158: forwards to the Bool-first float addition method. -/
/-! Nothing to promise: *(y::AbstractFloat, x::Bool)@164: forwards to the Bool-first float product method. -/

def BoolPromotion : Prop :=
  ∀ (T : Type) (P : Type → Prop), P T → P (promoteRuleBool T)

theorem boolPromotion_proven : BoolPromotion := by
  intro T P h
  simpa [promoteRuleBool] using h

def BoolBounds : Prop :=
  ∀ x : Bool,
    (if typeminBool then (1 : Int) else 0) ≤ (if x then (1 : Int) else 0) ∧
    (if x then (1 : Int) else 0) ≤ (if typemaxBool then (1 : Int) else 0)

theorem boolBounds_proven : BoolBounds := by
  intro x
  cases x <;> decide

def BoolLogic : Prop :=
  ∀ x y : Bool,
    (if notBool x then (1 : Nat) else 0) = (if x then 0 else 1) ∧
    (if andBool x y then (1 : Nat) else 0) =
      (if x then (1 : Nat) else 0) * (if y then (1 : Nat) else 0) ∧
    (if orBool x y then (1 : Nat) else 0) =
      Nat.max (if x then (1 : Nat) else 0) (if y then (1 : Nat) else 0) ∧
    (if xorBool x y then (1 : Nat) else 0) =
      ((if x then (1 : Nat) else 0) + (if y then (1 : Nat) else 0)) % 2 ∧
    nand (fun p : Bool × Bool => .ok (andBool p.1 p.2))
      (fun b => .ok (notBool b)) (x, y) = .ok (!(x && y)) ∧
    nor (fun p : Bool × Bool => .ok (orBool p.1 p.2))
      (fun b => .ok (notBool b)) (x, y) = .ok (!(x || y)) ∧
    (if mulBool x y then (1 : Nat) else 0) =
      (if x then (1 : Nat) else 0) * (if y then (1 : Nat) else 0) ∧
    (if mulWrapBool x y then (1 : Nat) else 0) =
      (if x then (1 : Nat) else 0) * (if y then (1 : Nat) else 0) ∧
    (if powBool x y then (1 : Nat) else 0) =
      if y then (if x then (1 : Nat) else 0) else 1

theorem boolLogic_proven : BoolLogic := by
  unfold BoolLogic
  intro x y
  cases x <;> cases y <;>
    simp [andBool, orBool, xorBool, nand, nor, notBool, mulBool, mulWrapBool,
      powBool, boolBits, boolFromBits, JuliaLean.C.jlAndInt, JuliaLean.C.jlOrInt]

def BoolOrdering : Prop :=
  ∀ x y : Bool,
    ltBool x y = decide ((if x then (1 : Int) else 0) < (if y then (1 : Int) else 0)) ∧
    leBool x y = decide ((if x then (1 : Int) else 0) ≤ (if y then (1 : Int) else 0))

theorem boolOrdering_proven : BoolOrdering := by
  intro x y
  cases x <;> cases y <;> decide

def BoolPredicates : Prop :=
  ∀ x : Bool,
    signbitBool x = false ∧
    (if signBool x then (1 : Int) else 0) = (if x then (1 : Int) else 0) ∧
    (if absBool x then (1 : Int) else 0) = (if x then (1 : Int) else 0) ∧
    (if abs2Bool x then (1 : Int) else 0) = (if x then (1 : Int) else 0) ∧
    iszeroBool x = decide ((if x then (1 : Int) else 0) = 0) ∧
    isoneBool x = decide ((if x then (1 : Int) else 0) = 1) ∧
    ispositiveBool x = decide (0 < (if x then (1 : Int) else 0))

theorem boolPredicates_proven : BoolPredicates := by
  intro x
  cases x <;> decide

def BoolIntegerArithmetic : Prop :=
  (∀ x : Bool,
    (posBool x).val = (if x then (1 : Int) else 0) ∧
    (posWrapBool x).val = (if x then (1 : Int) else 0)) ∧
  (∀ x : Bool,
    (negBool x).val = -(if x then (1 : Int) else 0) ∧
    (negWrapBool x).val = -(if x then (1 : Int) else 0)) ∧
  (∀ x y : Bool,
    (addBool x y).val = (if x then (1 : Int) else 0) + (if y then (1 : Int) else 0) ∧
    (subBool x y).val = (if x then (1 : Int) else 0) - (if y then (1 : Int) else 0) ∧
    (addWrapBool x y).val = (if x then (1 : Int) else 0) + (if y then (1 : Int) else 0) ∧
    (subWrapBool x y).val = (if x then (1 : Int) else 0) - (if y then (1 : Int) else 0))

theorem boolIntegerArithmetic_proven : BoolIntegerArithmetic := by
  unfold BoolIntegerArithmetic
  constructor
  · intro x
    cases x <;> decide
  constructor
  · intro x
    cases x <;> decide
  · intro x y
    cases x <;> cases y <;> decide

def BoolIntegerPower : Prop :=
  ∀ {α : Type} (one : α → Jl α) (x : α),
    (∀ e, one x = .error e → ∀ y : Bool, powIntegerBool one x y = .error e) ∧
    (∀ v, one x = .ok v →
      powIntegerBool one x true = .ok x ∧ powIntegerBool one x false = .ok v)

theorem boolIntegerPower_proven : BoolIntegerPower := by
  intro α one x
  constructor
  · intro e h y
    cases y <;> simp [powIntegerBool, h]
  · intro v h
    constructor <;> simp [powIntegerBool, h]

def BoolDivisionRemainder : Prop :=
  (∀ x, divBool x true = .ok x) ∧
  (∀ x, divBool x false = .error .divideError) ∧
  (∀ x, remBool x true = .ok false) ∧
  (∀ x, remBool x false = .error .divideError) ∧
  (∀ x y, modBool x y = remBool x y)

theorem boolDivisionRemainder_proven : BoolDivisionRemainder := by
  unfold BoolDivisionRemainder
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

def BoolRealConversion : Prop :=
  ∀ {α : Type} (equal : α → Int → Jl Bool) (x : α),
    (∀ e, equal x 0 = .error e → boolFromReal equal x = .error e) ∧
    (equal x 0 = .ok true → boolFromReal equal x = .ok false) ∧
    (∀ e, equal x 0 = .ok false → equal x 1 = .error e →
      boolFromReal equal x = .error e) ∧
    (equal x 0 = .ok false → equal x 1 = .ok true →
      boolFromReal equal x = .ok true) ∧
    (equal x 0 = .ok false → equal x 1 = .ok false →
      boolFromReal equal x = .error (.inexactError "Bool"))

theorem boolRealConversion_proven : BoolRealConversion := by
  intro α equal x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e h
    simp [boolFromReal, h]
  · intro h
    simp [boolFromReal, h]
  · intro e h0 h1
    simp [boolFromReal, h0, h1]
  · intro h0 h1
    simp [boolFromReal, h0, h1]
  · intro h0 h1
    simp [boolFromReal, h0, h1]

def BoolFloatAddition : Prop :=
  ∀ {α : Type} (oneunit : α → Jl α) (add : α → α → Jl α) (y : α),
    (∀ e, oneunit y = .error e →
      addBoolFloat oneunit add false y = .error e ∧
      addBoolFloat oneunit add true y = .error e) ∧
    (∀ unit, oneunit y = .ok unit →
      (∀ e, add unit y = .error e →
        addBoolFloat oneunit add false y = .error e ∧
        addBoolFloat oneunit add true y = .error e) ∧
      (∀ sum, add unit y = .ok sum →
        addBoolFloat oneunit add false y = .ok y ∧
        addBoolFloat oneunit add true y = .ok sum))

theorem boolFalseFloatAddition_proven : BoolFloatAddition := by
  intro α oneunit add y
  constructor
  · intro e h
    simp [addBoolFloat, h]
  · intro unit hu
    constructor
    · intro e he
      simp [addBoolFloat, hu, he]
    · intro sum hs
      simp [addBoolFloat, hu, hs]

def BoolFalseFloatStrongZero : Prop :=
  ∀ (T : JuliaLean.base.float.FTy)
      (zero : JuliaLean.base.float.FV T → Jl (JuliaLean.base.float.FV T))
      (copysign : JuliaLean.base.float.FV T → JuliaLean.base.float.FV T →
        Jl (JuliaLean.base.float.FV T))
      (y : JuliaLean.base.float.FV T),
    (∀ y, ∃ z, zero y = .ok z ∧ z.bits.val = 0) →
    (∀ x y, ∃ r, copysign x y = .ok r ∧
      r.bits.val % 2 ^ (T.fmt.eb + T.fmt.sb) =
        x.bits.val % 2 ^ (T.fmt.eb + T.fmt.sb) ∧
      (r.bits.val ≥ 2 ^ (T.fmt.eb + T.fmt.sb) ↔
        y.bits.val ≥ 2 ^ (T.fmt.eb + T.fmt.sb))) →
    ∃ r,
      mulBoolFloat zero copysign false y = .ok r ∧
      r.bits.val % 2 ^ (T.fmt.eb + T.fmt.sb) = 0 ∧
      (r.bits.val ≥ 2 ^ (T.fmt.eb + T.fmt.sb) ↔
        y.bits.val ≥ 2 ^ (T.fmt.eb + T.fmt.sb))

theorem boolFalseFloatStrongZero_proven : BoolFalseFloatStrongZero := by
  intro T zero copysign y hzero hcopy
  obtain ⟨z, hz, hzBits⟩ := hzero y
  obtain ⟨result, hcopyResult, hcopyMagnitude, hcopySign⟩ := hcopy z y
  refine ⟨result, ?_, ?_, hcopySign⟩
  · simp [mulBoolFloat, hz, hcopyResult]
  · simpa [hzBits] using hcopyMagnitude

structure FloatProductOps (α : Type) where
  zero : α → Jl α
  copysign : α → α → Jl α
  iszero : α → Bool
  signbit : α → Bool
  zeroLaws : ∀ x, ∃ z, zero x = .ok z ∧ iszero z = true ∧ signbit z = false
  copysignZero : ∀ x z, zero x = .ok z → iszero z = true → signbit z = false →
    ∃ result, copysign z x = .ok result ∧ iszero result = true ∧ signbit result = signbit x

def BoolAbstractFloatStrongZero : Prop :=
  ∀ {α : Type} (ops : FloatProductOps α) (x : α),
    ∃ result,
      mulBoolFloat ops.zero ops.copysign false x = .ok result ∧
      ops.iszero result = true ∧ ops.signbit result = ops.signbit x

theorem boolAbstractFloatStrongZero_proven : BoolAbstractFloatStrongZero := by
  intro α ops x
  obtain ⟨z, hz, hzZero, hzSign⟩ := ops.zeroLaws x
  obtain ⟨result, hc, hresultZero, hresultSign⟩ :=
    ops.copysignZero x z hz hzZero hzSign
  refine ⟨result, ?_, hresultZero, hresultSign⟩
  simp [mulBoolFloat, hz, hc]

/-! These adapters lift the source-mirrored IEEE zero and copysign definitions into the
error-aware callee types used by `mulBoolFloat`. -/
def flZeroCall {T : JuliaLean.base.float.FTy}
    (_x : JuliaLean.base.float.FV T) : Jl (JuliaLean.base.float.FV T) :=
  .ok (Fl.zero false)

def flCopysignCall {T : JuliaLean.base.float.FTy}
    (x y : JuliaLean.base.float.FV T) : Jl (JuliaLean.base.float.FV T) :=
  .ok (Fl.ofBits (x.magnitude + if y.signbit then 2 ^ (T.fmt.eb + T.fmt.sb) else 0))

theorem flZeroCall_source {T : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV T) :
    flZeroCall x = .ok (JuliaLean.base.float.zero_float T) := rfl

theorem flCopysignCall_source {T : JuliaLean.base.float.FTy}
    (x y : JuliaLean.base.float.FV T) :
    flCopysignCall x y = .ok (JuliaLean.base.float.copysign_float x y) := by
  cases T <;>
    simp [flCopysignCall, JuliaLean.base.float.copysign_float,
      JuliaLean.C.jlCopysignFloat, JuliaLean.C.finishFloat, JuliaLean.C.bfloat,
      JuliaLean.base.float.FTy.fmt, JuliaLean.Promotion.half,
      JuliaLean.Promotion.single, JuliaLean.Promotion.double]

theorem flSignMaskMod {f : Fmt} :
    2 ^ (f.eb + f.sb) % 2 ^ f.width = 2 ^ (f.eb + f.sb) := by
  apply Nat.mod_eq_of_lt
  have hwidth : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
    have hf : f.width = 1 + (f.eb + f.sb) := by simp [Fmt.width, Nat.add_assoc]
    rw [hf, Nat.pow_add]
  have hp : 0 < 2 ^ (f.eb + f.sb) := Nat.pow_pos (by omega)
  rw [hwidth]
  omega

def flFloatProductOps (T : JuliaLean.base.float.FTy) :
    FloatProductOps (JuliaLean.base.float.FV T) where
  zero := flZeroCall
  copysign := flCopysignCall
  iszero := Fl.iszero
  signbit := Fl.signbit
  zeroLaws := by
    intro x
    refine ⟨Fl.zero false, rfl, ?_, ?_⟩
    · simp [Fl.iszero, Fl.magnitude, Fl.zero, Fl.toBits, Fl.ofBits]
    · simp [Fl.signbit, Fl.zero, Fl.toBits, Fl.ofBits]
  copysignZero := by
    intro x z hz _ _
    simp only [flZeroCall, Except.ok.injEq] at hz
    subst z
    cases hs : x.signbit with
    | false =>
      have hnot : ¬ 2 ^ (T.fmt.eb + T.fmt.sb) ≤ x.bits.val := by
        simpa [Fl.signbit, Fl.toBits] using hs
      refine ⟨Fl.zero false, ?_, ?_, ?_⟩
      · simp [flCopysignCall, Fl.zero, Fl.magnitude, Fl.signbit, Fl.toBits, Fl.ofBits, hnot]
      · simp [Fl.iszero, Fl.magnitude, Fl.zero, Fl.toBits, Fl.ofBits]
      · simp [Fl.signbit, Fl.zero, Fl.toBits, Fl.ofBits]
    | true =>
      have hmask : 2 ^ (T.fmt.eb + T.fmt.sb) ≤ x.bits.val := by
        simpa [Fl.signbit, Fl.toBits] using hs
      refine ⟨Fl.zero true, ?_, ?_, ?_⟩
      · simp [flCopysignCall, Fl.zero, Fl.magnitude, Fl.signbit, Fl.toBits, Fl.ofBits, hmask]
      · simp [Fl.iszero, Fl.magnitude, Fl.zero, Fl.toBits, Fl.ofBits, flSignMaskMod]
      · simp [Fl.signbit, Fl.zero, Fl.toBits, Fl.ofBits, flSignMaskMod]


theorem boolAbstractFloatStrongZeroFl (T : JuliaLean.base.float.FTy)
    (x : JuliaLean.base.float.FV T) :
    ∃ result,
      mulBoolFloat (flFloatProductOps T).zero
        (flFloatProductOps T).copysign false x = .ok result ∧
      Fl.iszero result = true ∧ Fl.signbit result = Fl.signbit x := by
  simpa [flFloatProductOps] using
    (boolAbstractFloatStrongZero_proven (ops := flFloatProductOps T) x)

def entries : List Entry := [
  { id := "bool-promote-rule"
    juliaFile := "base/bool.jl"
    juliaFns := ["promote_rule(::Type{Bool}, ::Type{T})"]
    statement := "Promoting Bool with any numeric type selects that other type."
    source := "base/bool.jl:6"
    status := .proven, prop := ``BoolPromotion, thm := some ``boolPromotion_proven },
  { id := "bool-bounds"
    juliaFile := "base/bool.jl"
    juliaFns := ["typemin(::Type{Bool})", "typemax(::Type{Bool})"]
    statement := "false and true bound every Bool value under its integer ordering."
    source := "base/bool.jl:8-9"
    status := .proven, prop := ``BoolBounds, thm := some ``boolBounds_proven },
  { id := "bool-logic-truth-tables"
    juliaFile := "base/bool.jl"
    juliaFns := ["~", "&", "|", "xor", "nand", "nor", "*", "*%", "^(::Bool, ::Bool)"]
    statement := "Boolean bitwise operators, nand, nor, xor, ordinary and wrapping multiplication, and Boolean power obey their truth tables."
    source := "base/bool.jl:13-15,49,83,121,149-151"
    status := .proven, prop := ``BoolLogic, thm := some ``boolLogic_proven },
  { id := "bool-ordering"
    juliaFile := "base/bool.jl"
    juliaFns := ["<", "<="]
    statement := "Bool ordering agrees with the integer ordering under false-to-zero and true-to-one conversion."
    source := "base/bool.jl:135-136"
    status := .proven, prop := ``BoolOrdering, thm := some ``boolOrdering_proven },
  { id := "bool-numeric-predicates"
    juliaFile := "base/bool.jl"
    juliaFns := ["signbit", "sign", "abs", "abs2", "iszero", "isone", "ispositive"]
    statement := "Bool numeric predicates and magnitude functions agree with its values zero and one."
    source := "base/bool.jl:127-133"
    status := .proven, prop := ``BoolPredicates, thm := some ``boolPredicates_proven },
  { id := "bool-integer-arithmetic"
    juliaFile := "base/bool.jl"
    juliaFns := ["unary +", "unary +%", "unary -", "unary -%", "+", "-", "+%", "-%"]
    statement := "Bool unary and binary arithmetic returns the corresponding exact Int values."
    source := "base/bool.jl:140-148"
    status := .proven, prop := ``BoolIntegerArithmetic, thm := some ``boolIntegerArithmetic_proven },
  { id := "bool-integer-power"
    juliaFile := "base/bool.jl"
    juliaFns := ["^(::Integer, ::Bool)"]
    statement := "For every Julia Integer type, exponent one returns the base and exponent zero returns one(x); errors from one(x) propagate."
    source := "base/bool.jl:152"
    status := .proven, prop := ``BoolIntegerPower, thm := some ``boolIntegerPower_proven },
  { id := "bool-false-float-addition-preserves-negative-zero"
    juliaFile := "base/bool.jl"
    juliaFns := ["+(::Bool, ::AbstractFloat)"]
    statement := "For Float addition, false returns the original operand, preserving negative zero; true returns oneunit(y) + y."
    source := "base/bool.jl:154-157"
    status := .proven, prop := ``BoolFloatAddition, thm := some ``boolFalseFloatAddition_proven },
  { id := "bool-false-float-product-is-signed-zero"
    juliaFile := "base/bool.jl"
    juliaFns := ["*(::Bool, ::AbstractFloat)"]
    statement := "For Float16, Float32, and Float64, false multiplication returns a zero with the input's sign, assuming zero and copysign satisfy their documented Float bit-pattern laws, including for NaNs."
    source := "base/bool.jl:160-163"
    status := .proven, prop := ``BoolFalseFloatStrongZero, thm := some ``boolFalseFloatStrongZero_proven },
  { id := "bool-float-product-signed-zero-laws"
    juliaFile := "base/bool.jl"
    juliaFns := ["*(::Bool, ::AbstractFloat)"]
    statement := "For every floating type with zero, copysign, iszero, and signbit operations satisfying the documented signed-zero laws, false multiplication returns a zero whose sign matches the input."
    source := "base/bool.jl:160-163"
    status := .proven, prop := ``BoolAbstractFloatStrongZero, thm := some ``boolAbstractFloatStrongZero_proven },
  { id := "bool-division-remainder"
    juliaFile := "base/bool.jl"
    juliaFns := ["div", "rem", "mod"]
    statement := "Boolean division succeeds with a true denominator and throws DivideError otherwise; remainder returns false for a true denominator, and mod follows rem."
    source := "base/bool.jl:166-168"
    status := .proven, prop := ``BoolDivisionRemainder, thm := some ``boolDivisionRemainder_proven },
  { id := "bool-real-conversion-exact"
    juliaFile := "base/bool.jl"
    juliaFns := ["Bool(::Real)"]
    statement := "For every Real type, conversion accepts equality to zero or one, throws InexactError otherwise, and propagates comparison errors in order."
    source := "base/bool.jl:170"
    status := .proven, prop := ``BoolRealConversion, thm := some ``boolRealConversion_proven }
]

end JuliaLean.Proofs.base.bool

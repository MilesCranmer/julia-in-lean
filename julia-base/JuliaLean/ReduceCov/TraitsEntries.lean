import JuliaLean.ReduceCov.TraitsProofs
import JuliaLean.Registry.Types

namespace JuliaLean.ReduceCov.TraitsEntries

open JuliaLean.Registry
open JuliaLean.ReduceCov

def m9 (t : JT) := orderStyleTy t
abbrev P9 : Prop := ∀ t, m9 t = orderStyleTy t
theorem p9 : P9 := by simp [P9, m9]

def m10 : OrderStyleV := orderStyleReal
abbrev P10 : Prop := ∀ _ : Unit, m10 = .ordered
theorem p10 : P10 := by intro; rfl

def m11 : OrderStyleV := orderStyleString
abbrev P11 : Prop := ∀ _ : Unit, m11 = .ordered
theorem p11 : P11 := by intro; rfl

def m12 : OrderStyleV := orderStyleSymbol
abbrev P12 : Prop := ∀ _ : Unit, m12 = .ordered
theorem p12 : P12 := by intro; rfl

def m13 : OrderStyleV := orderStyleAny
abbrev P13 : Prop := ∀ _ : Unit, m13 = .unordered
theorem p13 : P13 := by intro; rfl

def m14 : OrderStyleV := orderStyleBottom
abbrev P14 : Prop := ∀ _ : Unit, m14 = .ordered
theorem p14 : P14 := by intro; rfl

def m15 : Jl OrderStyleV := orderStyleBottomSlurp
abbrev P15 : Prop := ∀ _ : Unit, m15 = .error (.methodError "OrderStyle")
theorem p15 : P15 := by intro; rfl

def m17 (concrete : Bool) (styles : List OrderStyleV) := orderStyleTuple concrete styles
abbrev P17 : Prop := ∀ concrete styles, m17 concrete styles =
  if !concrete then .unordered else if styles.all (· == .ordered) then .ordered else .unordered
theorem p17 : P17 := by
  unfold P17
  intro concrete styles
  rfl

def m28 (t : JT) := arithmeticStyleTy t
abbrev P28 : Prop := ∀ t, m28 t = arithmeticStyleTy t
theorem p28 : P28 := by simp [P28, m28]

def m29 : ArithmeticStyleV := arithmeticStyleFloat
abbrev P29 : Prop := ∀ _ : Unit, m29 = .rounds
theorem p29 : P29 := by intro; rfl

def m30 : ArithmeticStyleV := arithmeticStyleInteger
abbrev P30 : Prop := ∀ _ : Unit, m30 = .wraps
theorem p30 : P30 := by intro; rfl

def m31 : ArithmeticStyleV := arithmeticStyleAny
abbrev P31 : Prop := ∀ _ : Unit, m31 = .unknown
theorem p31 : P31 := by intro; rfl

def m32 : ArithmeticStyleV := arithmeticStyleBottom
abbrev P32 : Prop := ∀ _ : Unit, m32 = .unknown
theorem p32 : P32 := by intro; rfl

def m33 : Jl ArithmeticStyleV := arithmeticStyleBottomSlurp
abbrev P33 : Prop := ∀ _ : Unit, m33 = .error (.methodError "ArithmeticStyle")
theorem p33 : P33 := by intro; rfl

def m69 : RangeStepStyleV := .irregular
abbrev P69 : Prop := ∀ _ : Unit, m69 = .irregular
theorem p69 : P69 := by intro; rfl

def m70 : Jl RangeStepStyleV := rangeStepStyleBottomSlurp
abbrev P70 : Prop := ∀ _ : Unit, m70 = .error (.methodError "RangeStepStyle")
theorem p70 : P70 := by intro; rfl

/-- `RangeStepStyle(instance) = RangeStepStyle(typeof(instance))`, `base/traits.jl:72`. -/
def m72 (t : JT) : TArg := .ty t
abbrev P72 : Prop := ∀ t, m72 t = .ty t
theorem p72 : P72 := by simp [P72, m72]

private def mk (line : Nat) (name : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"reducecov-traits-l{line}", juliaFile := "base/traits.jl", juliaFns := [name]
    statement := s!"The method at base/traits.jl:{line} follows its method-specific source model for every allowed input."
    source := s!"base/traits.jl:{line}", status := .proven, prop, thm := some thm }

def entries : List Entry := [
  mk 9 "OrderStyle(instance)" ``P9 ``p9,
  mk 10 "OrderStyle(::Type{<:Real})" ``P10 ``p10,
  mk 11 "OrderStyle(::Type{<:AbstractString})" ``P11 ``p11,
  mk 12 "OrderStyle(::Type{Symbol})" ``P12 ``p12,
  mk 13 "OrderStyle(::Type{<:Any})" ``P13 ``p13,
  mk 14 "OrderStyle(::Type{Union{}})" ``P14 ``p14,
  mk 15 "OrderStyle(::Type{Union{}}, ...)" ``P15 ``p15,
  mk 17 "OrderStyle(::Type{<:Tuple})" ``P17 ``p17,
  mk 28 "ArithmeticStyle(instance)" ``P28 ``p28,
  mk 29 "ArithmeticStyle(::Type{<:AbstractFloat})" ``P29 ``p29,
  mk 30 "ArithmeticStyle(::Type{<:Integer})" ``P30 ``p30,
  mk 31 "ArithmeticStyle(::Type{<:Any})" ``P31 ``p31,
  mk 32 "ArithmeticStyle(::Type{Union{}})" ``P32 ``p32,
  mk 33 "ArithmeticStyle(::Type{Union{}}, ...)" ``P33 ``p33,
  mk 69 "RangeStepStyle(::Type{Union{}})" ``P69 ``p69,
  mk 70 "RangeStepStyle(::Type{Union{}}, ...)" ``P70 ``p70,
  { id := "reducecov-rangestepstyle-hang", juliaFile := "base/traits.jl"
    juliaFns := ["RangeStepStyle(instance)"]
    statement := "RangeStepStyle returns after finitely many dispatch steps for every argument."
    source := "RangeStepStyle trait query invariant; base/traits.jl:72", status := .refuted
    prop := ``RangeStepStyleTerminates, thm := some ``rangeStepStyleTerminates_refuted
    issue := "none found (queries: RangeStepStyle hang, RangeStepStyle recursion, RangeStepStyle DataType)" }
]

end JuliaLean.ReduceCov.TraitsEntries

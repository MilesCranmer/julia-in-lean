import JuliaLean.Promotion.Compare

/-!
`promote_rule` and `promote_type` for `Bool`, the ten `BitInteger` types and the three
`IEEEFloat` types at master `bbfa0ce4150`.
-/

namespace JuliaLean.Promotion

/-- The modelled primitive number types. -/
inductive NumTy where
  | bool
  | int (t : IntTy)
  | flt (T : FTy)
  deriving DecidableEq, Repr

def FTy.width : FTy → Nat
  | .f16 => 16 | .f32 => 32 | .f64 => 64

/-- `promote_rule(T, S)`; `none` is `Bottom` (`base/promotion.jl:355`). Rules:
`base/bool.jl:6`; integers `base/int.jl:809-822`; float/integer `base/float.jl:243-263`;
floats `base/float.jl:477-479`. -/
def promoteRule : NumTy → NumTy → Option NumTy
  | .bool, s => if s = .bool then none else some s
  | .int t, .int s =>
    if t.bits > s.bits then some (.int t)
    else if t.bits = s.bits ∧ !t.signed ∧ s.signed then some (.int t)
    else none
  | .flt T, .int _ => some (.flt T)
  | .flt T, .bool => some (.flt T)
  | .flt T, .flt S => if T.width > S.width then some (.flt T) else none
  | _, _ => none

/-- `promote_type(T, S)`; `base/promotion.jl:332-344` with `promote_result`
(`base/promotion.jl:363-366`). `none` stands for a non-concrete `typejoin`. -/
def promoteType (t s : NumTy) : Option NumTy :=
  if t = s then some t
  else match promoteRule t s, promoteRule s t with
    | some a, none => some a
    | none, some b => some b
    | some a, some b => if a = b then some a else none
    | none, none => none

end JuliaLean.Promotion

namespace JuliaLean.Promotion

/-- The promotion table of the manual (Conversion and Promotion; Integers and Floating-Point
Numbers): `Bool` promotes to the other type; two integers promote to the wider one, unsigned
winning between equal widths; any integer with a float promotes to the float; two floats
promote to the wider one. -/
def expectedPromotion : NumTy → NumTy → NumTy
  | .bool, s => s
  | t, .bool => t
  | .int t, .int s => .int (t.promote s)
  | .flt T, .int _ => .flt T
  | .int _, .flt T => .flt T
  | .flt T, .flt S => if T.width ≥ S.width then .flt T else .flt S

/-- `promote_type` gives the documented promotion for every pair of primitive number types. -/
def PromoteTypeTable : Prop := ∀ a b : NumTy, promoteType a b = some (expectedPromotion a b)

theorem promoteTypeTable_proven : PromoteTypeTable := by
  intro a b
  rcases a with _ | ⟨t⟩ | ⟨T⟩ <;> rcases b with _ | ⟨s⟩ | ⟨S⟩ <;>
    (try cases t) <;> (try cases s) <;> (try cases T) <;> (try cases S) <;> decide

end JuliaLean.Promotion

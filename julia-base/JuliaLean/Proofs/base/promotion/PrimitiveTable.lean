import JuliaLean.base.promotion

/-!
`promote_rule` and `promote_type` for `Bool`, the ten `BitInteger` types and the three
`IEEEFloat` types at master `bbfa0ce4150`.
-/


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

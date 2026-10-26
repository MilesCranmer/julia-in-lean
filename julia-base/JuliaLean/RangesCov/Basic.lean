import JuliaLean.Ranges
import JuliaLean.FloatRanges

/-!
Shared helpers for the whole-file coverage of `base/range.jl` and
`base/twiceprecision.jl` at Julia master `bbfa0ce4150`.

Integer range values reuse `JuliaLean.Ranges.Num` (a dynamically typed built-in
integer) and `JuliaLean.Ranges.Rng`; binary64 values reuse `JuliaLean.Float.F64`
and `JuliaLean.FloatRanges.TP`.
-/

namespace JuliaLean.RangesCov

open JuliaLean

abbrev Num := Ranges.Num
abbrev NType := Ranges.NType
abbrev Rng := Ranges.Rng
abbrev F64 := Float.F64
abbrev I64 := FloatRanges.I64
abbrev TP := FloatRanges.TP

/-- Julia exceptions that range methods throw beyond `JlError`: `error(msg)`
(`ErrorException`) and `DimensionMismatch`. -/
inductive Exc where
  | jl (e : JlError)
  | errorException (msg : String)
  | dimensionMismatch (msg : String)
  deriving DecidableEq, Repr

abbrev JlX (α : Type) := Except Exc α

/-- Embed a `JlError` computation. -/
def lift {α : Type} : Jl α → JlX α
  | .ok a => .ok a
  | .error e => .error (.jl e)

/-- The computation succeeds. -/
def Ok {α ε : Type} (x : Except ε α) : Prop := ∃ a, x = .ok a

/-- The computation throws an `ArgumentError`. -/
def ThrowsArg {α : Type} (x : Jl α) : Prop := ∃ m, x = .error (.argumentError m)

theorem promote_self_int (t : IntTy) : IntTy.promote t t = t := by cases t <;> rfl

theorem promote_self (a : NType) : Ranges.Num.promote a a = a := by
  cases a <;> simp [Ranges.Num.promote, promote_self_int]

theorem wrap_val {t : IntTy} (x : JInt t) : JInt.wrap t x.val = x :=
  Subtype.ext (wrapInt_of_inRange t x.val x.property)

theorem cast_self (x : Num) : Ranges.Num.cast x.ty x = .ok x := by
  rcases x with ⟨ty, v⟩
  cases ty with
  | bool =>
      cases v <;> rfl
  | bit t =>
      simp [Ranges.Num.cast, JInt.convert, Ranges.Num.val, v.property]
      rfl

theorem sub_bit (t : IntTy) (x y : JInt t) :
    Ranges.Num.sub ⟨.bit t, x⟩ ⟨.bit t, y⟩ = ⟨.bit t, x - y⟩ := by
  simp [Ranges.Num.sub, Ranges.Num.promote, promote_self_int, Ranges.Num.val, wrap_val]

theorem add_bit (t : IntTy) (x y : JInt t) :
    Ranges.Num.add ⟨.bit t, x⟩ ⟨.bit t, y⟩ = ⟨.bit t, x + y⟩ := by
  simp [Ranges.Num.add, Ranges.Num.promote, promote_self_int, Ranges.Num.val, wrap_val]

theorem mul_bit (t : IntTy) (x y : JInt t) :
    Ranges.Num.mul ⟨.bit t, x⟩ ⟨.bit t, y⟩ = ⟨.bit t, x * y⟩ := by
  simp [Ranges.Num.mul, Ranges.Num.promote, promote_self_int, Ranges.Num.val, wrap_val]

/-- A machine integer of type `t` as a dynamically typed `Num`. -/
def mkI (t : IntTy) (x : JInt t) : Num := ⟨.bit t, x⟩

section
variable {t s : IntTy} {x y : JInt t}

@[simp] theorem mkI_ty : (mkI t x).ty = .bit t := rfl
@[simp] theorem mkI_val : (mkI t x).val = x.val := rfl
theorem jsub_val : (x - y).val = wrapInt t (x.val - y.val) := rfl
theorem jadd_val : (x + y).val = wrapInt t (x.val + y.val) := rfl
theorem wrap_val' (v : Int) : (JInt.wrap t v).val = wrapInt t v := rfl
theorem wrap_one_val : (JInt.wrap t 1).val = 1 :=
  wrapInt_of_inRange t 1 (by cases t <;> decide)
theorem wrap_zero_val : (JInt.wrap t 0).val = 0 :=
  wrapInt_of_inRange t 0 (by cases t <;> decide)

theorem cast_mkI : Ranges.Num.cast (.bit t) (mkI t x) = .ok (mkI t x) := cast_self (mkI t x)

theorem cast_mkI_ok (h : s.min ≤ x.val ∧ x.val ≤ s.max) :
    Ranges.Num.cast (.bit s) (mkI t x) = .ok (mkI s ⟨x.val, h⟩) := by
  simp [Ranges.Num.cast, JInt.convert, mkI_val, h, bind, Except.bind, pure, Except.pure]
  rfl

theorem sub_mkI : Ranges.Num.sub (mkI t x) (mkI t y) = mkI t (x - y) := sub_bit t x y
theorem add_mkI : Ranges.Num.add (mkI t x) (mkI t y) = mkI t (x + y) := add_bit t x y
theorem mul_mkI : Ranges.Num.mul (mkI t x) (mkI t y) = mkI t (x * y) := mul_bit t x y
theorem one_mkI : Ranges.Num.one (.bit t) = mkI t (JInt.wrap t 1) := rfl
theorem zero_mkI : Ranges.Num.zero (.bit t) = mkI t (JInt.wrap t 0) := rfl
theorem lit_mkI (v : Int) : Ranges.Num.lit (.bit t) v = mkI t (JInt.wrap t v) := rfl

theorem mkI_inj : mkI t x = mkI t y ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

theorem mkI_eq_of_val (h : x.val = y.val) : mkI t x = mkI t y := by
  rw [Subtype.ext h]

end

end JuliaLean.RangesCov

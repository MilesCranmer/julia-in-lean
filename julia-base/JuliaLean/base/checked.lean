import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.bool
import JuliaLean.src.runtime_intrinsics_c

/-!
# Model of `base/checked.jl`

Methods are generic over each supported `BitInteger` width. Calls resolved through Julia dispatch,
including promotion, division, and the later-loaded power routine, are typed parameters.
-/
namespace JuliaLean.base.checked

open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bool

/-! ## Promotion entry points -/

/--
Julia source: base/checked.jl:26-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_add(x::Integer, y::Integer) = checked_add(promote(x,y)...)
```
-/
def checkedAddPromoted {α β γ : Type} (promote : α → β → Jl (γ × γ))
    (checkedAdd : γ → γ → Jl γ) (x : α) (y : β) : Jl γ := do
  let pair ← promote x y
  checkedAdd pair.1 pair.2

/--
Julia source: base/checked.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_sub(x::Integer, y::Integer) = checked_sub(promote(x,y)...)
```
-/
def checkedSubPromoted {α β γ : Type} (promote : α → β → Jl (γ × γ))
    (checkedSub : γ → γ → Jl γ) (x : α) (y : β) : Jl γ := do
  let pair ← promote x y
  checkedSub pair.1 pair.2

/--
Julia source: base/checked.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_mul(x::Integer, y::Integer) = checked_mul(promote(x,y)...)
```
-/
def checkedMulPromoted {α β γ : Type} (promote : α → β → Jl (γ × γ))
    (checkedMul : γ → γ → Jl γ) (x : α) (y : β) : Jl γ := do
  let pair ← promote x y
  checkedMul pair.1 pair.2

/--
Julia source: base/checked.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_div(x::Integer, y::Integer) = checked_div(promote(x,y)...)
```
-/
def checkedDivPromoted {α β γ : Type} (promote : α → β → Jl (γ × γ))
    (checkedDiv : γ → γ → Jl γ) (x : α) (y : β) : Jl γ := do
  let pair ← promote x y
  checkedDiv pair.1 pair.2

/--
Julia source: base/checked.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_rem(x::Integer, y::Integer) = checked_rem(promote(x,y)...)
```
-/
def checkedRemPromoted {α β γ : Type} (promote : α → β → Jl (γ × γ))
    (checkedRem : γ → γ → Jl γ) (x : α) (y : β) : Jl γ := do
  let pair ← promote x y
  checkedRem pair.1 pair.2

/--
Julia source: base/checked.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_fld(x::Integer, y::Integer) = checked_fld(promote(x,y)...)
```
-/
def checkedFldPromoted {α β γ : Type} (promote : α → β → Jl (γ × γ))
    (checkedFld : γ → γ → Jl γ) (x : α) (y : β) : Jl γ := do
  let pair ← promote x y
  checkedFld pair.1 pair.2

/--
Julia source: base/checked.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_mod(x::Integer, y::Integer) = checked_mod(promote(x,y)...)
```
-/
def checkedModPromoted {α β γ : Type} (promote : α → β → Jl (γ × γ))
    (checkedMod : γ → γ → Jl γ) (x : α) (y : β) : Jl γ := do
  let pair ← promote x y
  checkedMod pair.1 pair.2

/--
Julia source: base/checked.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_cld(x::Integer, y::Integer) = checked_cld(promote(x,y)...)
```
-/
def checkedCldPromoted {α β γ : Type} (promote : α → β → Jl (γ × γ))
    (checkedCld : γ → γ → Jl γ) (x : α) (y : β) : Jl γ := do
  let pair ← promote x y
  checkedCld pair.1 pair.2

/--
Julia source: base/checked.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_abs(x::T) where {T<:Integer} = no_op_err("checked_abs", T)
```
-/
def checkedAbsFallback {α : Type} (noOpError : String → Type → Jl α) (_x : α) : Jl α :=
  noOpError "checked_abs" α

/-! ## Built-in integer type sets -/

/--
Julia source: base/checked.jl:39-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const SignedInt = Union{Int8,Int16,Int32,Int64,Int128}
const UnsignedInt = Union{UInt8,UInt16,UInt32,UInt64,UInt128}
```
-/
def checkedIntegerTypeSets : List IntTy × List IntTy :=
  ([.i8, .i16, .i32, .i64, .i128], [.u8, .u16, .u32, .u64, .u128])

/--
Julia source: base/checked.jl:62-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
brokenSignedInt = Union{}
brokenUnsignedInt = Union{}
brokenSignedIntMul = Int128
brokenUnsignedIntMul = UInt128
if Core.sizeof(Ptr{Cvoid}) == 4
    brokenSignedIntMul = Union{brokenSignedIntMul, Int64}
    brokenUnsignedIntMul = Union{brokenUnsignedIntMul, UInt64}
end
const BrokenSignedInt = brokenSignedInt
const BrokenUnsignedInt = brokenUnsignedInt
const BrokenSignedIntMul = brokenSignedIntMul
const BrokenUnsignedIntMul = brokenUnsignedIntMul
```
-/
def brokenIntegerTypeSets : List IntTy × List IntTy × List IntTy × List IntTy :=
  ([], [], [.i128], [.u128])

/-! ## Checked negation and absolute value -/

/--
Julia source: base/checked.jl:80-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_neg(x)

Calculates `-x`, checking for overflow errors where applicable. For
example, standard two's complement signed integers (e.g. `Int`) cannot
represent `-typemin(Int)`, thus leading to an overflow.

The overflow protection may impose a perceptible performance penalty.
"""
function checked_neg(x::T) where T<:Integer
    checked_sub(T(0), x)
end
```
-/
def checkedNeg {α β : Type} (convert : Int → α) (checkedSub : α → α → Jl β) (x : α) : Jl β :=
  checkedSub (convert 0) x

/--
Julia source: base/checked.jl:92-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_overflowerr_negation(x) = (@noinline;
    throw(OverflowError(Base.invokelatest(string, "checked arithmetic: cannot compute -x for x = ", x, "::", typeof(x)))))
```
-/
def throwOverflowNegation {α β : Type}
    (invokelatest : (String → α → String → String → String) →
      String → α → String → String → Jl String)
    (string : String → α → String → String → String) (typeOf : α → String)
    (x : α) : Jl β := do
  let msg ← invokelatest string "checked arithmetic: cannot compute -x for x = " x "::" (typeOf x)
  .error (.overflowError msg)

/--
Julia source: base/checked.jl:94-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if BrokenSignedInt != Union{}
function checked_neg(x::BrokenSignedInt)
    r = -%(x)
    (x<0) & (r<0) && throw_overflowerr_negation(x)
    r
end
end
```
-/
def checkedNegBrokenSigned {t : IntTy} (x : JInt t)
    (throwOverflow : JInt t → Jl (JInt t)) : Jl (JInt t) := do
  let r := -x
  let xNegative := decide (x.val < 0)
  let rNegative := decide (r.val < 0)
  if Bool.and xNegative rNegative then throwOverflow x else pure r

/--
Julia source: base/checked.jl:101-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if BrokenUnsignedInt != Union{}
function checked_neg(x::T) where T<:BrokenUnsignedInt
    x != 0 && throw_overflowerr_negation(x)
    T(0)
end
end
```
-/
def checkedNegBrokenUnsigned {t : IntTy} (x : JInt t)
    (throwOverflow : JInt t → Jl (JInt t)) : Jl (JInt t) :=
  if x.val != 0 then throwOverflow x else .ok (JInt.lit t 0)

/--
Julia source: base/checked.jl:108-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_abs(x)

Calculates `abs(x)`, checking for overflow errors where applicable.
For example, standard two's complement signed integers (e.g. `Int`)
cannot represent `abs(typemin(Int))`, thus leading to an overflow.

The overflow protection may impose a perceptible performance penalty.

See also: [`abs`](@ref), [`Base.uabs`](@ref).
"""
function checked_abs end

function checked_abs(x::SignedInt)
    r = ifelse(x<0, -x, x)
    r<0 || return r
    msg = LazyString("checked arithmetic: cannot compute |x| for x = ", x, "::", typeof(x))
    throw(OverflowError(msg))
end
```
-/
def checkedAbsSigned {t : IntTy} (_signed : t.signed = true)
    (lazyString : String → JInt t → String → String → String)
    (typeOf : JInt t → String) (x : JInt t) : Jl (JInt t) := do
  let negative := x.val < 0
  let negated := -x
  let r := if negative then negated else x
  if r.val < 0 then
    .error (.overflowError
      (lazyString "checked arithmetic: cannot compute |x| for x = " x "::" (typeOf x)))
  else .ok r

/--
Julia source: base/checked.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_abs(x::UnsignedInt) = x
```
-/
def checkedAbsUnsigned {α : Type} (x : α) : α := x

/--
Julia source: base/checked.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_abs(x::Bool) = x
```
-/
def checkedAbsBool (x : Bool) : Bool := x

/-! ## Overflow-reporting helpers -/

/-- Julia's value of a Boolean when it participates in integer arithmetic. -/
def boolInt (x : Bool) : Int := if x then 1 else 0

/--
Julia source: base/checked.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_with_overflow(x::T, y::T) where {T<:SignedInt}   = checked_sadd_int(x, y)
```
-/
def addWithOverflowSigned {t : IntTy} (_signed : t.signed = true) (x y : JInt t) : JInt t × Bool :=
  let result := jlCheckedSaddInt (fromJInt x) (fromJInt y)
  (toJInt t result.1, result.2)

/--
Julia source: base/checked.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_with_overflow(x::T, y::T) where {T<:UnsignedInt} = checked_uadd_int(x, y)
```
-/
def addWithOverflowUnsigned {t : IntTy} (_unsigned : t.signed = false) (x y : JInt t) : JInt t × Bool :=
  let result := jlCheckedUaddInt (fromJInt x) (fromJInt y)
  (toJInt t result.1, result.2)

/--
Julia source: base/checked.jl:138-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_with_overflow(x::Bool, y::Bool) = (x +% y, false)
```
-/
def addWithOverflowBool (x y : Bool) : JInt .i64 × Bool :=
  (addWrapBool x y, false)

/--
Julia source: base/checked.jl:140-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if BrokenSignedInt != Union{}
function add_with_overflow(x::T, y::T) where T<:BrokenSignedInt
    r = x +% y
    # x and y have the same sign, and the result has a different sign
    f = (x<0) == (y<0) != (r<0)
    r, f
end
end
```
-/
def addWithOverflowBrokenSigned {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  let r := x + y
  let xNegative := x.val < 0
  let yNegative := y.val < 0
  let rNegative := r.val < 0
  (r, xNegative == yNegative && xNegative != rNegative)

/--
Julia source: base/checked.jl:148-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if BrokenUnsignedInt != Union{}
function add_with_overflow(x::T, y::T) where T<:BrokenUnsignedInt
    # x + y > typemax(T)
    # Note: ~y == -y-1
    x +% y, x > ~y
end
end
```
-/
-- Julia's bitwise complement on a `BitInteger`.
def bitnot {t : IntTy} (x : JInt t) : JInt t := not_int x

def addWithOverflowBrokenUnsigned {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  (x + y, x.val > (bitnot y).val)

/--
Julia source: base/checked.jl:156-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_overflowerr_binaryop(op, x, y) = (@noinline;
    throw(OverflowError(LazyString(x, " ", op, " ", y, " overflowed for type ", typeof(x)))))
```
-/
def throwOverflowBinary {α β γ δ : Type}
    (lazyString : β → String → α → String → γ → String → String → String)
    (typeOf : β → String) (op : α) (x : β) (y : γ) : Jl δ :=
  .error (.overflowError
    (lazyString x " " op " " y " overflowed for type " (typeOf x)))
/--
Julia source: base/checked.jl:159-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_add(x, y)

Calculates `x+y`, checking for overflow errors where applicable.

The overflow protection may impose a perceptible performance penalty.
"""
function checked_add(x::T, y::T) where T<:Integer
    @inline
    zb = add_with_overflow(x, y)
    # Avoid use of tuple destructuring, which uses arithmetic internally,
    # so that this can be used as a replacement for +
    z = getfield(zb, 1)
    b = getfield(zb, 2)
    b && throw_overflowerr_binaryop(:+, x, y)
    z
end
```
-/
def checkedAddSame {α β : Type} (addWithOverflow : α → α → β × Bool)
    (throwOverflow : α → α → Jl β) (x y : α) : Jl β := do
  let zb := addWithOverflow x y
  let z := zb.1
  let b := zb.2
  if b then throwOverflow x y else .ok z

/--
Julia source: base/checked.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_add(x) = x
```
-/
def checkedAddUnary {α : Type} (x : α) : α := x

/--
Julia source: base/checked.jl:179-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_add(x::Bool) = +x
```
-/
def checkedAddBool (x : Bool) : JInt .i64 := posBool x

/--
Julia source: base/checked.jl:181-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_add(x1::T, x2::T, x3::T) where {T} =
    checked_add(checked_add(x1, x2), x3)
```
-/
def checkedAdd3 {α β γ : Type} (checkedAdd2 : α → α → Jl β)
    (checkedAddMixed : β → α → Jl γ) (x1 x2 x3 : α) : Jl γ := do
  checkedAddMixed (← checkedAdd2 x1 x2) x3

/--
Julia source: base/checked.jl:183-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_add(x1::T, x2::T, x3::T, x4::T) where {T} =
    checked_add(checked_add(x1, x2), x3, x4)
```
-/
def checkedAdd4 {α β γ : Type} (checkedAdd2 : α → α → Jl β)
    (checkedAdd3 : β → α → α → Jl γ) (x1 x2 x3 x4 : α) : Jl γ := do
  checkedAdd3 (← checkedAdd2 x1 x2) x3 x4

/--
Julia source: base/checked.jl:185-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_add(x1::T, x2::T, x3::T, x4::T, x5::T) where {T} =
    checked_add(checked_add(x1, x2), x3, x4, x5)
```
-/
def checkedAdd5 {α β γ : Type} (checkedAdd2 : α → α → Jl β)
    (checkedAdd4 : β → α → α → α → Jl γ) (x1 x2 x3 x4 x5 : α) : Jl γ := do
  checkedAdd4 (← checkedAdd2 x1 x2) x3 x4 x5

/--
Julia source: base/checked.jl:187-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_add(x1::T, x2::T, x3::T, x4::T, x5::T, x6::T) where {T} =
    checked_add(checked_add(x1, x2), x3, x4, x5, x6)
```
-/
def checkedAdd6 {α β γ : Type} (checkedAdd2 : α → α → Jl β)
    (checkedAdd5 : β → α → α → α → α → Jl γ) (x1 x2 x3 x4 x5 x6 : α) : Jl γ := do
  checkedAdd5 (← checkedAdd2 x1 x2) x3 x4 x5 x6

/--
Julia source: base/checked.jl:189-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_add(x1::T, x2::T, x3::T, x4::T, x5::T, x6::T, x7::T) where {T} =
    checked_add(checked_add(x1, x2), x3, x4, x5, x6, x7)
```
-/
def checkedAdd7 {α β γ : Type} (checkedAdd2 : α → α → Jl β)
    (checkedAdd6 : β → α → α → α → α → α → Jl γ) (x1 x2 x3 x4 x5 x6 x7 : α) : Jl γ := do
  checkedAdd6 (← checkedAdd2 x1 x2) x3 x4 x5 x6 x7

/--
Julia source: base/checked.jl:191-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_add(x1::T, x2::T, x3::T, x4::T, x5::T, x6::T, x7::T, x8::T) where {T} =
    checked_add(checked_add(x1, x2), x3, x4, x5, x6, x7, x8)
```
-/
def checkedAdd8 {α β γ : Type} (checkedAdd2 : α → α → Jl β)
    (checkedAdd7 : β → α → α → α → α → α → α → Jl γ)
    (x1 x2 x3 x4 x5 x6 x7 x8 : α) : Jl γ := do
  checkedAdd7 (← checkedAdd2 x1 x2) x3 x4 x5 x6 x7 x8

/-! ## Checked subtraction -/

/--
Julia source: base/checked.jl:200-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sub_with_overflow(x::T, y::T) where {T<:SignedInt}   = checked_ssub_int(x, y)
```
-/
def subWithOverflowSigned {t : IntTy} (_signed : t.signed = true) (x y : JInt t) : JInt t × Bool :=
  let result := jlCheckedSsubInt (fromJInt x) (fromJInt y)
  (toJInt t result.1, result.2)

/--
Julia source: base/checked.jl:201-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sub_with_overflow(x::T, y::T) where {T<:UnsignedInt} = checked_usub_int(x, y)
```
-/
def subWithOverflowUnsigned {t : IntTy} (_unsigned : t.signed = false) (x y : JInt t) : JInt t × Bool :=
  let result := jlCheckedUsubInt (fromJInt x) (fromJInt y)
  (toJInt t result.1, result.2)

/--
Julia source: base/checked.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sub_with_overflow(x::Bool, y::Bool) = (x-y, false)
```
-/
def subWithOverflowBool (x y : Bool) : JInt .i64 × Bool :=
  (subBool x y, false)

/--
Julia source: base/checked.jl:204-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if BrokenSignedInt != Union{}
function sub_with_overflow(x::T, y::T) where T<:BrokenSignedInt
    r = x -% y
    # x and y have different signs, and the result has a different sign than x
    f = (x<0) != (y<0) == (r<0)
    r, f
end
end
```
-/
def subWithOverflowBrokenSigned {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  let r := x - y
  let xNegative := x.val < 0
  let yNegative := y.val < 0
  let rNegative := r.val < 0
  (r, xNegative != yNegative && yNegative == rNegative)

/--
Julia source: base/checked.jl:212-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if BrokenUnsignedInt != Union{}
function sub_with_overflow(x::T, y::T) where T<:BrokenUnsignedInt
    # x - y < 0
    x -% y, x < y
end
end
```
-/
def subWithOverflowBrokenUnsigned {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  (x - y, decide (x.val < y.val))

/--
Julia source: base/checked.jl:219-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_sub(x, y)

Calculates `x-y`, checking for overflow errors where applicable.

The overflow protection may impose a perceptible performance penalty.
"""
function checked_sub(x::T, y::T) where T<:Integer
    @inline
    z, b = sub_with_overflow(x, y)
    b && throw_overflowerr_binaryop(:-, x, y)
    z
end
```
-/
def checkedSubSame {α β : Type} (subWithOverflow : α → α → β × Bool)
    (throwOverflow : α → α → Jl β) (x y : α) : Jl β := do
  let result := subWithOverflow x y
  let z := result.1
  let b := result.2
  if b then throwOverflow x y else .ok z

/-! ## Checked multiplication -/

/--
Julia source: base/checked.jl:239-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_with_overflow(x::T, y::T) where {T<:SignedInt}   = checked_smul_int(x, y)
```
-/
def mulWithOverflowSigned {t : IntTy} (_signed : t.signed = true) (x y : JInt t) : JInt t × Bool :=
  let result := jlCheckedSmulInt (fromJInt x) (fromJInt y)
  (toJInt t result.1, result.2)

/--
Julia source: base/checked.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_with_overflow(x::T, y::T) where {T<:UnsignedInt} = checked_umul_int(x, y)
```
-/
def mulWithOverflowUnsigned {t : IntTy} (_unsigned : t.signed = false) (x y : JInt t) : JInt t × Bool :=
  let result := jlCheckedUmulInt (fromJInt x) (fromJInt y)
  (toJInt t result.1, result.2)

/--
Julia source: base/checked.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_with_overflow(x::Bool, y::Bool) = (x *% y, false)
```
-/
def mulWithOverflowBool (x y : Bool) : Bool × Bool :=
  (mulWrapBool x y, false)

/--
Julia source: base/checked.jl:243-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if BrokenSignedIntMul != Union{} && BrokenSignedIntMul != Int128
function mul_with_overflow(x::T, y::T) where T<:BrokenSignedIntMul
    r = widemul(x, y)
    f = r % T != r
    r % T, f
end
end
```
-/
def mulWithOverflowBroken {α β : Type} (wideMul : α → α → β) (remType : β → α)
    (ne : α → β → Bool) (x y : α) : α × Bool :=
  let r := wideMul x y
  let f := ne (remType r) r
  (remType r, f)

/--
Julia source: base/checked.jl:250-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if BrokenUnsignedIntMul != Union{} && BrokenUnsignedIntMul != UInt128
function mul_with_overflow(x::T, y::T) where T<:BrokenUnsignedIntMul
    r = widemul(x, y)
    f = r % T != r
    r % T, f
end
end
```
-/
def mulWithOverflowBrokenUnsigned {α β : Type} (wideMul : α → α → β) (remType : β → α)
    (ne : α → β → Bool) (x y : α) : α × Bool :=
  let r := wideMul x y
  let f := ne (remType r) r
  (remType r, f)

/--
Julia source: base/checked.jl:257-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Int128 <: BrokenSignedIntMul
    # Avoid BigInt
    function mul_with_overflow(x::T, y::T) where T<:Int128
        f = if y > 0
            # x * y > typemax(T)
            # x * y < typemin(T)
            x > fld(typemax(T), y) || x < cld(typemin(T), y)
        elseif y < 0
            # x * y > typemax(T)
            # x * y < typemin(T)
            # y == -1 can overflow fld
            x < cld(typemax(T), y) || y != -1 && x > fld(typemin(T), y)
        else
            false
        end
        x *% y, f
    end
end
```
-/
def mulWithOverflowInt128 (fld cld : JInt .i128 → JInt .i128 → Jl (JInt .i128))
    (x y : JInt .i128) : Jl (JInt .i128 × Bool) := do
  let overflow ← if y.val > 0 then do
    let high ← fld (JInt.typemax .i128) y
    if x.val > high.val then .ok true else do
      let low ← cld (JInt.typemin .i128) y
      .ok (decide (x.val < low.val))
  else if y.val < 0 then do
    let high ← cld (JInt.typemax .i128) y
    if x.val < high.val then .ok true
    else if y.val != -1 then do
      let low ← fld (JInt.typemin .i128) y
      .ok (decide (x.val > low.val))
    else .ok false
  else .ok false
  .ok (x * y, overflow)

/--
Julia source: base/checked.jl:275-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if UInt128 <: BrokenUnsignedIntMul
    # Avoid BigInt
    function mul_with_overflow(x::T, y::T) where T<:UInt128
        # x * y > typemax(T)
        x *% y, y > 0 && x > fld(typemax(T), y)
    end
end
```
-/
def mulWithOverflowUInt128 (fld : JInt .u128 → JInt .u128 → Jl (JInt .u128))
    (x y : JInt .u128) : Jl (JInt .u128 × Bool) := do
  let r := x * y
  let overflow ← if y.val > 0 then do
    let high ← fld (JInt.typemax .u128) y
    .ok (decide (x.val > high.val))
  else .ok false
  .ok (r, overflow)

/--
Julia source: base/checked.jl:283-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_mul(x, y)

Calculates `x*y`, checking for overflow errors where applicable.

The overflow protection may impose a perceptible performance penalty.
"""
function checked_mul(x::T, y::T) where T<:Integer
    @inline
    z, b = mul_with_overflow(x, y)
    b && throw_overflowerr_binaryop(:*, x, y)
    z
end
```
-/
def checkedMulSame {α β : Type} (mulWithOverflow : α → α → Jl (β × Bool))
    (throwOverflow : α → α → Jl β) (x y : α) : Jl β := do
  let result ← mulWithOverflow x y
  let z := result.1
  let b := result.2
  if b then throwOverflow x y else .ok z

/--
Julia source: base/checked.jl:297-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Handle multiple arguments
checked_mul(x) = x
```
-/
def checkedMulUnary {α : Type} (x : α) : α := x

/--
Julia source: base/checked.jl:299-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_mul(x1::T, x2::T, x3::T) where {T} =
    checked_mul(checked_mul(x1, x2), x3)
```
-/
def checkedMul3 {α β γ : Type} (checkedMul2 : α → α → Jl β)
    (checkedMulMixed : β → α → Jl γ) (x1 x2 x3 : α) : Jl γ := do
  checkedMulMixed (← checkedMul2 x1 x2) x3

/--
Julia source: base/checked.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_mul(x1::T, x2::T, x3::T, x4::T) where {T} =
    checked_mul(checked_mul(x1, x2), x3, x4)
```
-/
def checkedMul4 {α β γ : Type} (checkedMul2 : α → α → Jl β)
    (checkedMul3 : β → α → α → Jl γ) (x1 x2 x3 x4 : α) : Jl γ := do
  checkedMul3 (← checkedMul2 x1 x2) x3 x4

/--
Julia source: base/checked.jl:303-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_mul(x1::T, x2::T, x3::T, x4::T, x5::T) where {T} =
    checked_mul(checked_mul(x1, x2), x3, x4, x5)
```
-/
def checkedMul5 {α β γ : Type} (checkedMul2 : α → α → Jl β)
    (checkedMul4 : β → α → α → α → Jl γ) (x1 x2 x3 x4 x5 : α) : Jl γ := do
  checkedMul4 (← checkedMul2 x1 x2) x3 x4 x5

/--
Julia source: base/checked.jl:305-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_mul(x1::T, x2::T, x3::T, x4::T, x5::T, x6::T) where {T} =
    checked_mul(checked_mul(x1, x2), x3, x4, x5, x6)
```
-/
def checkedMul6 {α β γ : Type} (checkedMul2 : α → α → Jl β)
    (checkedMul5 : β → α → α → α → α → Jl γ) (x1 x2 x3 x4 x5 x6 : α) : Jl γ := do
  checkedMul5 (← checkedMul2 x1 x2) x3 x4 x5 x6

/--
Julia source: base/checked.jl:307-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_mul(x1::T, x2::T, x3::T, x4::T, x5::T, x6::T, x7::T) where {T} =
    checked_mul(checked_mul(x1, x2), x3, x4, x5, x6, x7)
```
-/
def checkedMul7 {α β γ : Type} (checkedMul2 : α → α → Jl β)
    (checkedMul6 : β → α → α → α → α → α → Jl γ) (x1 x2 x3 x4 x5 x6 x7 : α) : Jl γ := do
  checkedMul6 (← checkedMul2 x1 x2) x3 x4 x5 x6 x7

/--
Julia source: base/checked.jl:309-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_mul(x1::T, x2::T, x3::T, x4::T, x5::T, x6::T, x7::T, x8::T) where {T} =
    checked_mul(checked_mul(x1, x2), x3, x4, x5, x6, x7, x8)
```
-/
def checkedMul8 {α β γ : Type} (checkedMul2 : α → α → Jl β)
    (checkedMul7 : β → α → α → α → α → α → α → Jl γ)
    (x1 x2 x3 x4 x5 x6 x7 x8 : α) : Jl γ := do
  checkedMul7 (← checkedMul2 x1 x2) x3 x4 x5 x6 x7 x8

/-! ## Checked division and power -/

/--
Julia source: base/checked.jl:312-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_div(x, y)

Calculates `div(x,y)`, checking for overflow errors where applicable.

The overflow protection may impose a perceptible performance penalty.
"""
checked_div(x::T, y::T) where {T<:Integer} = div(x, y) # Base.div already checks
```
-/
def checkedDiv {α : Type} (div : α → α → Jl α) (x y : α) : Jl α := div x y

/--
Julia source: base/checked.jl:321-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_rem(x, y)

Calculates `x%y`, checking for overflow errors where applicable.

The overflow protection may impose a perceptible performance penalty.
"""
checked_rem(x::T, y::T) where {T<:Integer} = rem(x, y) # Base.rem already checks
```
-/
def checkedRem {α : Type} (rem : α → α → Jl α) (x y : α) : Jl α := rem x y

/--
Julia source: base/checked.jl:330-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_fld(x, y)

Calculates `fld(x,y)`, checking for overflow errors where applicable.

The overflow protection may impose a perceptible performance penalty.
"""
checked_fld(x::T, y::T) where {T<:Integer} = fld(x, y) # Base.fld already checks
```
-/
def checkedFld {α : Type} (fld : α → α → Jl α) (x y : α) : Jl α := fld x y

/--
Julia source: base/checked.jl:339-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_mod(x, y)

Calculates `mod(x,y)`, checking for overflow errors where applicable.

The overflow protection may impose a perceptible performance penalty.
"""
checked_mod(x::T, y::T) where {T<:Integer} = mod(x, y) # Base.mod already checks
```
-/
def checkedMod {α : Type} (mod : α → α → Jl α) (x y : α) : Jl α := mod x y

/--
Julia source: base/checked.jl:348-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_cld(x, y)

Calculates `cld(x,y)`, checking for overflow errors where applicable.

The overflow protection may impose a perceptible performance penalty.
"""
checked_cld(x::T, y::T) where {T<:Integer} = cld(x, y) # Base.cld already checks
```
-/
def checkedCld {α : Type} (cld : α → α → Jl α) (x y : α) : Jl α := cld x y

/--
Julia source: base/checked.jl:357-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_pow(x, y)

Calculates `^(x,y)`, checking for overflow errors where applicable.

The overflow protection may impose a perceptible performance penalty.
"""
checked_pow(x::Integer, y::Integer) = checked_power_by_squaring(x, y)
```
-/
def checkedPow {α β : Type} (checkedPowerBySquaring : α → β → Jl α)
    (x : α) (y : β) : Jl α := checkedPowerBySquaring x y

/--
Julia source: base/checked.jl:366-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_power_by_squaring(x_, p::Integer) = Base.power_by_squaring(x_, p; mul = checked_mul)
```
-/
def checkedPowerBySquaring {α β : Type}
    (powerBySquaring : α → β → (α → α → Jl α) → Jl α)
    (checkedMul : α → α → Jl α) (x : α) (p : β) : Jl α :=
  powerBySquaring x p checkedMul

/--
Julia source: base/checked.jl:368-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_power_by_squaring(x::Bool, p::Integer) = Base.power_by_squaring(x, p)
```
-/
def checkedPowerBySquaringBool {β : Type}
    (powerBySquaring : Bool → β → Jl Bool) (x : Bool) (p : β) : Jl Bool :=
  powerBySquaring x p

/-! ## Checked length -/

/--
Julia source: base/checked.jl:370-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.checked_length(r)

Calculates `length(r)`, but may check for overflow errors where applicable when
the result doesn't fit into `Union{Integer(eltype(r)),Int}`.
"""
checked_length(r) = length(r) # for most things, length doesn't error
```
-/
def checkedLength {α β : Type} (length : α → Jl β) (r : α) : Jl β := length r

/-! ## BitInteger call selection for specifications -/


def addWithOverflowBits {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  if h : t.signed = true then addWithOverflowSigned h x y
  else addWithOverflowUnsigned (by cases t <;> simp_all [IntTy.signed]) x y

def subWithOverflowBits {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  if h : t.signed = true then subWithOverflowSigned h x y
  else subWithOverflowUnsigned (by cases t <;> simp_all [IntTy.signed]) x y

def checkedBinaryLazyString {t : IntTy} (x : JInt t) (sp1 op sp2 : String)
    (y : JInt t) (suffix typeName : String) : String :=
  toString x.val ++ sp1 ++ op ++ sp2 ++ toString y.val ++ suffix ++ typeName
def checkedAddBits {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  checkedAddSame
    (fun a b => if h : t.signed = true then
      addWithOverflowSigned h a b
    else addWithOverflowUnsigned (by cases t <;> simp_all [IntTy.signed]) a b)
    (throwOverflowBinary checkedBinaryLazyString (fun _ => t.name) "+") x y

def checkedSubBits {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  checkedSubSame
    (fun a b => if h : t.signed = true then
      subWithOverflowSigned h a b
    else subWithOverflowUnsigned (by cases t <;> simp_all [IntTy.signed]) a b)
    (throwOverflowBinary checkedBinaryLazyString (fun _ => t.name) "-") x y

def mulWithOverflowBits {t : IntTy} (x y : JInt t) : Jl (JInt t × Bool) :=
  match t with
  | .i8 => .ok (mulWithOverflowSigned rfl x y)
  | .i16 => .ok (mulWithOverflowSigned rfl x y)
  | .i32 => .ok (mulWithOverflowSigned rfl x y)
  | .i64 => .ok (mulWithOverflowSigned rfl x y)
  | .i128 => mulWithOverflowInt128 JInt.fld JInt.cld x y
  | .u8 => .ok (mulWithOverflowUnsigned rfl x y)
  | .u16 => .ok (mulWithOverflowUnsigned rfl x y)
  | .u32 => .ok (mulWithOverflowUnsigned rfl x y)
  | .u64 => .ok (mulWithOverflowUnsigned rfl x y)
  | .u128 => mulWithOverflowUInt128 JInt.fld x y

def checkedMulBits {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  checkedMulSame mulWithOverflowBits
    (throwOverflowBinary checkedBinaryLazyString (fun _ => t.name) "*") x y

def checkedNegBits {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  checkedNeg (fun n => JInt.lit t n) checkedSubBits x

def checkedAbsBits {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  if h : t.signed = true then
    checkedAbsSigned h
      (fun pre value sep typeName => pre ++ toString value.val ++ sep ++ typeName)
      (fun _ => t.name) x
  else .ok (checkedAbsUnsigned x)

def checkedDivBits {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedDiv JInt.div x y
def checkedRemBits {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedRem JInt.remInt x y
def checkedFldBits {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedFld JInt.fld x y
def checkedModBits {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedMod JInt.mod x y
def checkedCldBits {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedCld JInt.cld x y

def promoteBits {t s : IntTy} (x : JInt t) (y : JInt s) :
    Jl (JInt (t.promote s) × JInt (t.promote s)) := do
  let a ← JInt.convert (t.promote s) x.val
  let b ← JInt.convert (t.promote s) y.val
  pure (a, b)

def checkedAddMixedBits {t s : IntTy} (x : JInt t) (y : JInt s) :=
  checkedAddPromoted promoteBits checkedAddBits x y
def checkedSubMixedBits {t s : IntTy} (x : JInt t) (y : JInt s) :=
  checkedSubPromoted promoteBits checkedSubBits x y
def checkedMulMixedBits {t s : IntTy} (x : JInt t) (y : JInt s) :=
  checkedMulPromoted promoteBits checkedMulBits x y
def checkedDivMixedBits {t s : IntTy} (x : JInt t) (y : JInt s) :=
  checkedDivPromoted promoteBits checkedDivBits x y
def checkedRemMixedBits {t s : IntTy} (x : JInt t) (y : JInt s) :=
  checkedRemPromoted promoteBits checkedRemBits x y
def checkedFldMixedBits {t s : IntTy} (x : JInt t) (y : JInt s) :=
  checkedFldPromoted promoteBits checkedFldBits x y
def checkedModMixedBits {t s : IntTy} (x : JInt t) (y : JInt s) :=
  checkedModPromoted promoteBits checkedModBits x y
def checkedCldMixedBits {t s : IntTy} (x : JInt t) (y : JInt s) :=
  checkedCldPromoted promoteBits checkedCldBits x y

def trailingZeros : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 0 then 1 + trailingZeros fuel (n / 2) else 0

def squareTimes {t : IntTy} : Nat → JInt t → (JInt t → JInt t → Jl (JInt t)) → Jl (JInt t)
  | 0, x, _mul => .ok x
  | n + 1, x, mul => do squareTimes n (← mul x x) mul

def powerLoop {t : IntTy} (width : Nat) (p : Nat) (x y : JInt t)
    (mul : JInt t → JInt t → Jl (JInt t)) : Jl (JInt t) :=
  match p with
  | 0 => .ok y
  | n + 1 => do
    let z := trailingZeros width (n + 1)
    let x ← squareTimes (z + 1) x mul
    let y ← mul y x
    powerLoop width ((n + 1) / 2 / 2 ^ z) x y mul
termination_by p
decreasing_by
  have h := Nat.div_le_self ((n + 1) / 2) (2 ^ trailingZeros width (n + 1))
  have h' := Nat.div_lt_self (by omega : 0 < n + 1) (by omega : 1 < 2)
  omega

def powerBySquaringBits {t s : IntTy} (x : JInt t) (p : JInt s)
    (mul : JInt t → JInt t → Jl (JInt t)) : Jl (JInt t) := do
  let _xSquared := x * x
  if p.val = 1 then pure x
  else if p.val = 0 then pure (JInt.lit t 1)
  else if p.val = 2 then mul x x
  else if p.val < 0 then
    if x.val = 1 then pure x
    else if (-x).val = 1 then
      pure (if p.val % 2 = 0 then JInt.lit t 1 else x)
    else .error (.domainError "")
  else
    let z := trailingZeros s.bits p.val.toNat
    let x ← squareTimes z x mul
    powerLoop s.bits (p.val.toNat / 2 / 2 ^ z) x x mul

def checkedPowerBySquaringBits {t s : IntTy} (x : JInt t) (p : JInt s) :=
  checkedPowerBySquaring powerBySquaringBits checkedMulBits x p

def checkedPowBits {t s : IntTy} (x : JInt t) (p : JInt s) :=
  checkedPow checkedPowerBySquaringBits x p
end JuliaLean.base.checked

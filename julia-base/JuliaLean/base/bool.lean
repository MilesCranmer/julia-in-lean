import JuliaLean.base.int
import JuliaLean.Runtime.Collections

/-!
# Model of `base/bool.jl`

Each Julia method is represented by a typed Lean definition in source order. Calls into later-loaded
or extensible functions are explicit parameters. Julia's dispatch is trusted.
-/

namespace JuliaLean.base.bool

open JuliaLean JuliaLean.base.int
def boolBits (x : Bool) : BitVec 1 := BitVec.ofNat 1 (if x then 1 else 0)
def boolFromBits (x : BitVec 1) : Bool := x.toNat == 1

/--
Julia source: base/bool.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Bool}, ::Type{T}) where {T<:Number} = T
```
-/
def promoteRuleBool (T : Type) : Type := T

/--
Julia source: base/bool.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{Bool}) = false
```
-/
def typeminBool : Bool := false

/--
Julia source: base/bool.jl:9-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{Bool}) = true
```
-/
def typemaxBool : Bool := true

/--
Julia source: base/bool.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(~)(x::Bool) = !x
```
-/
def notBool (x : Bool) : Bool := !x

/--
Julia source: base/bool.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(x::Bool, y::Bool) = and_int(x, y)
```
-/
def andBool (x y : Bool) : Bool :=
  boolFromBits (JuliaLean.C.jlAndInt (boolBits x) (boolBits y))

/--
Julia source: base/bool.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(x::Bool, y::Bool) = or_int(x, y)
```
-/
def orBool (x y : Bool) : Bool :=
  boolFromBits (JuliaLean.C.jlOrInt (boolBits x) (boolBits y))

/--
Julia source: base/bool.jl:17-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    xor(x, y)
    ⊻(x, y)

Bitwise exclusive or of `x` and `y`. Implements
[three-valued logic](https://en.wikipedia.org/wiki/Three-valued_logic),
returning [`missing`](@ref) if one of the arguments is `missing`.

The infix operation `a ⊻ b` is a synonym for `xor(a,b)`, and
`⊻` can be typed by tab-completing `\\xor` or `\\veebar` in the Julia REPL.

# Examples
```jldoctest
julia> xor(true, false)
true

julia> xor(true, true)
false

julia> xor(true, missing)
missing

julia> false ⊻ false
false

julia> [true; true; false] .⊻ [true; false; false]
3-element BitVector:
 0
 1
 0
```
"""
xor(x::Bool, y::Bool) = (x != y)
````
-/
def xorBool (x y : Bool) : Bool := x != y

/--
Julia source: base/bool.jl:51-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    nand(x, y)
    ⊼(x, y)

Bitwise nand (not and) of `x` and `y`. Implements
[three-valued logic](https://en.wikipedia.org/wiki/Three-valued_logic),
returning [`missing`](@ref) if one of the arguments is `missing`.

The infix operation `a ⊼ b` is a synonym for `nand(a,b)`, and
`⊼` can be typed by tab-completing `\\nand` or `\\barwedge` in the Julia REPL.

# Examples
```jldoctest
julia> nand(true, false)
true

julia> nand(true, true)
false

julia> nand(true, missing)
missing

julia> false ⊼ false
true

julia> [true; true; false] .⊼ [true; false; false]
3-element BitVector:
 0
 1
 1
```
"""
nand(x...) = ~(&)(x...)
````
-/
def nand {Args β γ : Type} (andOp : Args → Jl β) (notOp : β → Jl γ) (args : Args) : Jl γ :=
  match andOp args with
  | .ok combined => notOp combined
  | .error error => .error error

/--
Julia source: base/bool.jl:85-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    nor(x, y)
    ⊽(x, y)

Bitwise nor (not or) of `x` and `y`. Implements
[three-valued logic](https://en.wikipedia.org/wiki/Three-valued_logic),
returning [`missing`](@ref) if one of the arguments is `missing` and the
other is not `true`.

The infix operation `a ⊽ b` is a synonym for `nor(a,b)`, and
`⊽` can be typed by tab-completing `\\nor` or `\\barvee` in the Julia REPL.

# Examples
```jldoctest
julia> nor(true, false)
false

julia> nor(true, true)
false

julia> nor(true, missing)
false

julia> false ⊽ false
true

julia> false ⊽ missing
missing

julia> [true; true; false] .⊽ [true; false; false]
3-element BitVector:
 0
 0
 1
```
"""
nor(x...) = ~(|)(x...)
````
-/
def nor {Args β γ : Type} (orOp : Args → Jl β) (notOp : β → Jl γ) (args : Args) : Jl γ :=
  match orOp args with
  | .ok combined => notOp combined
  | .error error => .error error

/--
Julia source: base/bool.jl:123-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>>(x::Bool, c::UInt) = Int(x) >> c
```
-/
def shrBool (x : Bool) (c : JInt .u64) : JInt .i64 :=
  shr_BitSigned_BitUnsigned (ofBool .i64 x) c

/--
Julia source: base/bool.jl:124-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<<(x::Bool, c::UInt) = Int(x) << c
```
-/
def shlBool (x : Bool) (c : JInt .u64) : JInt .i64 :=
  shl_BitInteger_BitUnsigned (ofBool .i64 x) c

/--
Julia source: base/bool.jl:125-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>>>(x::Bool, c::UInt) = Int(x) >>> c
```
-/
def lshrBool (x : Bool) (c : JInt .u64) : JInt .i64 :=
  lshr_BitInteger_BitUnsigned (ofBool .i64 x) c

/--
Julia source: base/bool.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::Bool) = false
```
-/
def signbitBool (_x : Bool) : Bool := false

/--
Julia source: base/bool.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sign(x::Bool) = x
```
-/
def signBool (x : Bool) : Bool := x

/--
Julia source: base/bool.jl:129-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs(x::Bool) = x
```
-/
def absBool (x : Bool) : Bool := x

/--
Julia source: base/bool.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs2(x::Bool) = x
```
-/
def abs2Bool (x : Bool) : Bool := x

/--
Julia source: base/bool.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iszero(x::Bool) = !x
```
-/
def iszeroBool (x : Bool) : Bool := !x

/--
Julia source: base/bool.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isone(x::Bool) = x
```
-/
def isoneBool (x : Bool) : Bool := x

/--
Julia source: base/bool.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispositive(x::Bool) = x # could use fallback once #21712 is resolved
```
-/
def ispositiveBool (x : Bool) : Bool := x

/--
Julia source: base/bool.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x::Bool, y::Bool) = y&!x
```
-/
def ltBool (x y : Bool) : Bool := andBool y (notBool x)

/--
Julia source: base/bool.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Bool, y::Bool) = y|!x
```
-/
def leBool (x y : Bool) : Bool := orBool y (notBool x)

/--
Julia source: base/bool.jl:140-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Bool)  =    Int(x)
```
-/
def posBool (x : Bool) : JInt .i64 := ofBool .i64 x

/--
Julia source: base/bool.jl:141-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+%(x::Bool) =    Int(x)
```
-/
def posWrapBool (x : Bool) : JInt .i64 := ofBool .i64 x

/--
Julia source: base/bool.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Bool)  = -%(Int(x))
```
-/
def negBool (x : Bool) : JInt .i64 := negWrap (ofBool .i64 x)

/--
Julia source: base/bool.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(x::Bool) = -%(Int(x))
```
-/
def negWrapBool (x : Bool) : JInt .i64 := negWrap (ofBool .i64 x)

/--
Julia source: base/bool.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Bool, y::Bool) = Int(x) +% Int(y)
```
-/
def addBool (x y : Bool) : JInt .i64 := addWrap (ofBool .i64 x) (ofBool .i64 y)

/--
Julia source: base/bool.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Bool, y::Bool) = Int(x) -% Int(y)
```
-/
def subBool (x y : Bool) : JInt .i64 := subWrap (ofBool .i64 x) (ofBool .i64 y)

/--
Julia source: base/bool.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+%(x::Bool, y::Bool) = Int(x) +% Int(y)
```
-/
def addWrapBool (x y : Bool) : JInt .i64 := addWrap (ofBool .i64 x) (ofBool .i64 y)

/--
Julia source: base/bool.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(x::Bool, y::Bool) = Int(x) -% Int(y)
```
-/
def subWrapBool (x y : Bool) : JInt .i64 := subWrap (ofBool .i64 x) (ofBool .i64 y)

/--
Julia source: base/bool.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Bool, y::Bool) = x & y
```
-/
def mulBool (x y : Bool) : Bool := andBool x y

/--
Julia source: base/bool.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*%(x::Bool, y::Bool) = x & y
```
-/
def mulWrapBool (x y : Bool) : Bool := andBool x y

/--
Julia source: base/bool.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::Bool, y::Bool) = x | !y
```
-/
def powBool (x y : Bool) : Bool := orBool x (notBool y)

/--
Julia source: base/bool.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::Integer, y::Bool) = ifelse(y, x, one(x))
```
-/
def powIntegerBool {α : Type} (one : α → Jl α) (x : α) (y : Bool) : Jl α :=
  match one x with
  | .error error => .error error
  | .ok oneX => .ok (if y then x else oneX)

/--
Julia source: base/bool.jl:154-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# preserve -0.0 in `false + -0.0`
function +(x::Bool, y::T)::promote_type(Bool,T) where T<:AbstractFloat
    return ifelse(x, oneunit(y) + y, y)
end
```
-/
def addBoolFloat {α : Type} (oneunit : α → Jl α)
    (add : α → α → Jl α) (x : Bool) (y : α) : Jl α :=
  match oneunit y with
  | .error error => .error error
  | .ok unit =>
    match add unit y with
    | .error error => .error error
    | .ok sum => .ok (if x then sum else y)

/--
Julia source: base/bool.jl:158-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(y::AbstractFloat, x::Bool) = x + y
```
-/
def addFloatBool {α : Type} (oneunit : α → Jl α)
    (add : α → α → Jl α) (y : α) (x : Bool) : Jl α :=
  addBoolFloat oneunit add x y

/--
Julia source: base/bool.jl:160-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# make `false` a "strong zero": false*NaN == 0.0
function *(x::Bool, y::T)::promote_type(Bool,T) where T<:AbstractFloat
    return ifelse(x, y, copysign(zero(y), y))
end
```
-/
def mulBoolFloat {α : Type} (zero : α → Jl α)
    (copysign : α → α → Jl α) (x : Bool) (y : α) : Jl α :=
  match zero y with
  | .error error => .error error
  | .ok z =>
    match copysign z y with
    | .error error => .error error
    | .ok signedZero => .ok (if x then y else signedZero)

/--
Julia source: base/bool.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(y::AbstractFloat, x::Bool) = x * y
```
-/
def mulFloatBool {α : Type} (zero : α → Jl α)
    (copysign : α → α → Jl α) (y : α) (x : Bool) : Jl α :=
  mulBoolFloat zero copysign x y

/--
Julia source: base/bool.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::Bool, y::Bool) = y ? x : throw(DivideError())
```
-/
def divBool (x y : Bool) : Jl Bool := if y then .ok x else .error .divideError

/--
Julia source: base/bool.jl:167-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Bool, y::Bool) = y ? false : throw(DivideError())
```
-/
def remBool (_x y : Bool) : Jl Bool := if y then .ok false else .error .divideError

/--
Julia source: base/bool.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(x::Bool, y::Bool) = rem(x,y)
```
-/
def modBool (x y : Bool) : Jl Bool := remBool x y

/--
Julia source: base/bool.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Bool(x::Real) = x==0 ? false : x==1 ? true : throw(InexactError(:Bool, Bool, x))
```
-/
def boolFromReal {α : Type} (equal : α → Int → Jl Bool) (x : α) : Jl Bool :=
  match equal x 0 with
  | .error error => .error error
  | .ok true => .ok false
  | .ok false =>
    match equal x 1 with
    | .error error => .error error
    | .ok true => .ok true
    | .ok false => .error (.inexactError "Bool")

end JuliaLean.base.bool

namespace JuliaLean.base.bool.Archive20261101PrimitiveNot

/--
Julia source: base/bool.jl:13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(~)(x::Bool) = !x
```
-/
def notBool (primitiveNot : Bool → Bool) (x : Bool) : Bool :=
  primitiveNot x

/--
Julia source: base/bool.jl:131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iszero(x::Bool) = !x
```
-/
def iszeroBool (primitiveNot : Bool → Bool) (x : Bool) : Bool :=
  primitiveNot x

/--
Julia source: base/bool.jl:135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x::Bool, y::Bool) = y&!x
```
-/
def ltBool (primitiveNot : Bool → Bool) (x y : Bool) : Bool :=
  JuliaLean.base.bool.andBool y
    (primitiveNot x)

/--
Julia source: base/bool.jl:136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Bool, y::Bool) = y|!x
```
-/
def leBool (primitiveNot : Bool → Bool) (x y : Bool) : Bool :=
  JuliaLean.base.bool.orBool y
    (primitiveNot x)

/--
Julia source: base/bool.jl:151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::Bool, y::Bool) = x | !y
```
-/
def powBool (primitiveNot : Bool → Bool) (x y : Bool) : Bool :=
  JuliaLean.base.bool.orBool x
    (primitiveNot y)

end JuliaLean.base.bool.Archive20261101PrimitiveNot

namespace JuliaLean.NumMisc.Coverage

open JuliaLean

/-! ## `base/bool.jl` -/

def boolXor (x y : Bool) : Bool := x != y
def boolPromote (otherType : Nat) : Nat := otherType
def boolBounds : Bool × Bool := (false, true)
def boolNot (x : Bool) : Bool := !x
def boolAnd (x y : Bool) : Bool := x && y
def boolOr (x y : Bool) : Bool := x || y
def boolNand (xs : List Bool) : Bool := !(xs.foldl (· && ·) true)
def boolNor (xs : List Bool) : Bool := !(xs.foldl (· || ·) false)
def boolShiftLeft (x : Bool) (count : Nat) : Int := (if x then 1 else 0) * 2^count
def boolShiftRight (x : Bool) (count : Nat) : Int := (if x then 1 else 0) / 2^count
def boolPredicates (x : Bool) : Bool × Bool × Bool × Bool × Bool :=
  (false, x, !x, x, x)
def boolUnaryInt (x : Bool) : Int := if x then 1 else 0
def boolCompare (x y : Bool) : Bool × Bool := (y && !x, y || !x)
def boolAdd (x y : Bool) : Int := (if x then 1 else 0) + (if y then 1 else 0)
def boolSub (x y : Bool) : Int := (if x then 1 else 0) - (if y then 1 else 0)
def boolMul (x y : Bool) : Bool := x && y
def boolPow (x y : Bool) : Bool := x || !y
def boolDiv (x y : Bool) : Jl Bool := if y then .ok x else .error .divideError
def boolRem (_x y : Bool) : Jl Bool := if y then .ok false else .error .divideError
def boolConvertReal (zero one : Bool) : Jl Bool :=
  if zero then .ok false else if one then .ok true else .error (.inexactError "Bool")
def boolFloatAdd (x : Bool) (onePlusY y : Int) : Int := if x then onePlusY else y
def boolFloatMul (x : Bool) (y signedZero : Int) : Int := if x then y else signedZero

end JuliaLean.NumMisc.Coverage

namespace JuliaLean.MathCov.Special

open JuliaLean.Promotion JuliaLean.MathCov.FP

/-- `Bool * x` for a float: `ifelse(b, x, copysign(zero(x), x))`; `base/bool.jl:182`. -/
def boolMul {T : FTy} (b : Bool) (x : FV T) : FV T := if b then x else copysign (zero T) x

end JuliaLean.MathCov.Special

namespace JuliaLean.MathFuncs

/-- `*(x::Bool, y::AbstractFloat) = ifelse(x, y, copysign(zero(y), y))`, also used for
`y * x`; `base/bool.jl:161-164`. -/
def boolMul (copysign : Float.F64 → Float.F64 → Float.F64)
    (b : Bool) (y : Float.F64) : Float.F64 := if b then y else copysign Float.F64.zero y

end JuliaLean.MathFuncs

namespace JuliaLean.Reduce.Val

open JuliaLean.Float

/-- `x + y`; `+(::Bool, ::Bool)` is `Int(x) + Int(y)` (`base/bool.jl:145`), and a `Bool`
plus a float is `ifelse(x, oneunit(y) + y, y)` (`base/bool.jl:155-158`). -/
def plus : Val → Val → Val
  | .bool b, .f64 y | .f64 y, .bool b => .f64 (if b then F64.add F64.one y else y)
  | x, y => numBin (fun t x y => .int t (x + y)) (fun x y => .f64 (F64.add x y))
    (fun a b => .int .i64 (boolInt .i64 a + boolInt .i64 b)) x y

/-- `x * y`; `*(::Bool, ::Bool)` is `x & y` (`base/bool.jl:149`), and a `Bool` times a
float is `ifelse(x, y, copysign(zero(y), y))` (`base/bool.jl:161-164`). -/
def times : Val → Val → Val
  | .bool b, .f64 y | .f64 y, .bool b => .f64 (if b then y else F64.zero (F64.signbit y))
  | x, y => numBin (fun t x y => .int t (x * y)) (fun x y => .f64 (F64.mul x y))
    (fun a b => .bool (a && b)) x y

end JuliaLean.Reduce.Val

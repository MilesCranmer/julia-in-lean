import JuliaLean.base.int
import JuliaLean.base.range

/-!
# Model of `base/float.jl`

Typed model of every method of `base/float.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform (`Int === Int64`). Each method is a Lean definition whose docstring carries
the method's verbatim source; its body follows the Julia body call by call.

* IEEE floating-point values are `FV T = Fl T.fmt` (`JuliaLean.Promotion.IEEE`) for the three
  `IEEEFloat` types `T : FTy` (`Float16`, `Float32`, `Float64`), and fixed-width integers are
  `JInt t` (`JuliaLean.Core`, `JuliaLean.base.int`).
* Compiler intrinsics (`sitofp`, `uitofp`, `fptosi`, `fptoui`, `fptrunc`, `fpext`, `neg_float`,
  `add_float`, `sub_float`, `mul_float`, `div_float`, `muladd_float`, `trunc_llvm`, `floor_llvm`,
  `ceil_llvm`, `rint_llvm`, `eq_float`, `lt_float`, `le_float`, `fpiseq`, `abs_float`,
  `copysign_float`, `urem_int`, `bswap_int`, `bitcast`) are the C runtime models of
  `JuliaLean.src.runtime_intrinsics_c`.
-/

namespace JuliaLean.base.float

open JuliaLean JuliaLean.C JuliaLean.Promotion

/-- Julia's three `IEEEFloat` types (`Float16`, `Float32`, `Float64`). -/
inductive FTy where
  | f16 | f32 | f64
  deriving DecidableEq, Repr

namespace FTy
/-- IEEE format parameters `(eb, sb)`. -/
def fmt : FTy → Fmt
  | .f16 => half | .f32 => single | .f64 => double

/-- `Core.sizeof(T)` in bytes. -/
def bytes : FTy → Nat
  | .f16 => 2 | .f32 => 4 | .f64 => 8

/-- `uinttype(T)`. -/
def uintTy : FTy → IntTy
  | .f16 => .u16 | .f32 => .u32 | .f64 => .u64

/-- `inttype(T)`. -/
def intTy : FTy → IntTy
  | .f16 => .i16 | .f32 => .i32 | .f64 => .i64
end FTy

/-- Value of an `IEEEFloat` type `T`. -/
abbrev FV (T : FTy) := Fl T.fmt

/-! ## Intrinsics on IEEEFloat and BitInteger values -/

/-- `bitcast(T, x)` from a fixed-width integer to an `IEEEFloat`. -/
def bitcast_to_float (T : FTy) {t : IntTy} (x : JInt t) : FV T :=
  Fl.ofBits (jlBitcast (fromJInt x)).toNat

/-- `bitcast(t, x)` from an `IEEEFloat` to a fixed-width integer. -/
def bitcast_from_float (t : IntTy) {T : FTy} (x : FV T) : JInt t :=
  int.bitcastFloat t x

/-- `sitofp(T, x)`. -/
def sitofp (T : FTy) {t : IntTy} (x : JInt t) : FV T := jlSitofp T.fmt (fromJInt x)
/-- `uitofp(T, x)`. -/
def uitofp (T : FTy) {t : IntTy} (x : JInt t) : FV T := jlUitofp T.fmt (fromJInt x)
/-- `uitofp(T, x::Bool)`. -/
def uitofp_Bool (T : FTy) (x : Bool) : FV T := jlUitofp T.fmt (BitVec.ofNat 8 (if x then 1 else 0))

/-- `fptrunc(T, x)` for a narrower `IEEEFloat` type `T`. -/
def fptrunc (T : FTy) {S : FTy} (x : FV S) (h : T.fmt.width < S.fmt.width := by decide) : FV T :=
  int.okOf (jlFptrunc T.fmt x) (by
    intro e he; simp [jlFptrunc, Nat.not_le.mpr h, pure, Except.pure] at he
    split at he <;> simp at he)

/-- `fpext(T, x)` for a wider `IEEEFloat` type `T`. -/
def fpext (T : FTy) {S : FTy} (x : FV S) (h : S.fmt.width < T.fmt.width := by decide) : FV T :=
  int.okOf (jlFpext T.fmt x) (by
    intro e he; simp [jlFpext, Nat.not_le.mpr h, pure, Except.pure] at he
    split at he <;> simp at he)

/-- `fptosi(Ti, x)`. -/
def fptosi (Ti : IntTy) {T : FTy} (x : FV T) : JInt Ti := toJInt Ti (jlFptosi Ti.bits x)
/-- `fptoui(Ti, x)`. -/
def fptoui (Ti : IntTy) {T : FTy} (x : FV T) : JInt Ti := toJInt Ti (jlFptoui Ti.bits x)

/-- `trunc_llvm(x)`. -/
def trunc_llvm {T : FTy} (x : FV T) : FV T := jlTruncLlvm x
/-- `floor_llvm(x)`. -/
def floor_llvm {T : FTy} (x : FV T) : FV T := jlFloorLlvm x
/-- `ceil_llvm(x)`. -/
def ceil_llvm {T : FTy} (x : FV T) : FV T := jlCeilLlvm x
/-- `rint_llvm(x)`. -/
def rint_llvm {T : FTy} (x : FV T) : FV T := jlRintLlvm x

/-- `neg_float(x)`. -/
def neg_float {T : FTy} (x : FV T) : FV T := jlNegFloat x
/-- `add_float(x, y)`. -/
def add_float {T : FTy} (x y : FV T) : FV T := jlAddFloat x y
/-- `sub_float(x, y)`. -/
def sub_float {T : FTy} (x y : FV T) : FV T := jlSubFloat x y
/-- `mul_float(x, y)`. -/
def mul_float {T : FTy} (x y : FV T) : FV T := jlMulFloat x y
/-- `div_float(x, y)`. -/
def div_float {T : FTy} (x y : FV T) : FV T := jlDivFloat x y
/-- `muladd_float(x, y, z)`. -/
def muladd_float {T : FTy} (x y z : FV T) : FV T := jlMuladdFloat x y z

/-- `eq_float(x, y)`. -/
def eq_float {T : FTy} (x y : FV T) : Bool := jlEqFloat x y
/-- `lt_float(x, y)`. -/
def lt_float {T : FTy} (x y : FV T) : Bool := jlLtFloat x y
/-- `le_float(x, y)`. -/
def le_float {T : FTy} (x y : FV T) : Bool := jlLeFloat x y
/-- `fpiseq(x, y)`. -/
def fpiseq {T : FTy} (x y : FV T) : Bool := jlFpiseq x y
/-- `abs_float(x)`. -/
def abs_float {T : FTy} (x : FV T) : FV T := jlAbsFloat x
/-- `copysign_float(x, y)`. -/
def copysign_float {T : FTy} (x y : FV T) : FV T := jlCopysignFloat x y

/-- `urem_int(x, y)`. -/
def urem_int {t : IntTy} (x y : JInt t) : JInt t :=
  match jlUremInt (fromJInt x) (fromJInt y) with
  | .ok b => toJInt t b
  | .error _ => int.lit t 0

theorem width_mod_16 (T : FTy) : T.fmt.width % 16 = 0 := by cases T <;> decide

/-- `bswap_int(x)` on an `IEEEFloat`. -/
def bswap_int_float {T : FTy} (x : FV T) : FV T :=
  Fl.ofBits (int.okOf (jlBswapInt (BitVec.ofNat T.fmt.width x.toBits))
    (by intro e he; simp [jlBswapInt, width_mod_16 T, pure, Except.pure] at he)).toNat

/-! ## Callees from earlier and companion Base files -/

/-- `reinterpret(t, x)` from an `IEEEFloat` to a same-width `BitInteger` (`essentials.jl:694`). -/
def reinterpret_Int_Float (t : IntTy) {T : FTy} (x : FV T) : JInt t := bitcast_from_float t x
/-- `reinterpret(T, x)` from a same-width `BitInteger` to an `IEEEFloat` (`essentials.jl:694`). -/
def reinterpret_Float_Int (T : FTy) {t : IntTy} (x : JInt t) : FV T := bitcast_to_float T x

/-- `zero(T)` (`floatfuncs.jl` / `number.jl`). -/
def zero_float (T : FTy) : FV T := Fl.zero false
/-- `one(T)` (`floatfuncs.jl` / `number.jl`). -/
def one_float (T : FTy) : FV T := Fl.ofInt 1
/-- `T(Inf)`. -/
def inf_float (T : FTy) : FV T := Fl.inf false
/-- `T(NaN)`. -/
def nan_float (T : FTy) : FV T := Fl.nan
/-- `oftype(x, y)` on same-type floats (`essentials.jl`). -/
def oftype_float {T : FTy} (_x : FV T) (y : FV T) : FV T := y
/-- `x === y` on `IEEEFloat` (`boot.jl`). -/
def egal_float {T : FTy} (x y : FV T) : Bool := x.toBits == y.toBits
/-- `iszero(x)` on `IEEEFloat` (`number.jl`: `x == zero(x)`). -/
def iszero_float {T : FTy} (x : FV T) : Bool := eq_float x (zero_float T)
/-- `signbit(x)` on `IEEEFloat` (`floatfuncs.jl:15`). -/
def signbit_float {T : FTy} (x : FV T) : Bool := int.signbit (reinterpret_Int_Float T.intTy x)
/-- `isinteger(x)` on `IEEEFloat` (`floatfuncs.jl:51`: `iszero(x - trunc(x))`). -/
def isinteger_callee {T : FTy} (x : FV T) : Bool := x.isinteger
/-- `isnan(x)` callee for methods appearing before line 702. -/
def isnan_callee {T : FTy} (x : FV T) : Bool := !(eq_float x x)
/-- `isfinite(x)` callee for methods appearing before line 705. -/
def isfinite_callee {T : FTy} (x : FV T) : Bool := !(!(eq_float (sub_float x x) (sub_float x x)))
/-- `isinf(x)` callee for methods appearing before line 717. -/
def isinf_callee {T : FTy} (x : FV T) : Bool := egal_float (abs_float x) (inf_float T)
/-- `issubnormal(x)` callee for `explicit_mantissa_noinfnan` at line 504. -/
def issubnormal_callee {T : FTy} (x : FV T) : Bool := x.expField == 0 && x.frac != 0
/-- `isnegative(d)` on `BitInteger` (`number.jl` / `int.jl:186`). -/
def isnegative_int {t : IntTy} (d : JInt t) : Bool := if t.signed then int.lt d (int.lit .i64 0) else false
/-- `ispositive(d)` on `BitInteger` (`number.jl`). -/
def ispositive_int {t : IntTy} (d : JInt t) : Bool := int.lt (int.lit .i64 0) d

/-- `RoundingMode` tags (`rounding.jl`). -/
inductive RoundingMode where
  | ToZero | Down | Up | Nearest | FromZero | NearestTiesAway | NearestTiesUp
  deriving DecidableEq, Repr

/--
Julia source: base/float.jl:1-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

const IEEEFloat = Union{Float16, Float32, Float64}

import Core: Float16, Float32, Float64, AbstractFloat
import Core: Int8, Int16, Int32, Int64, Int128, UInt8, UInt16, UInt32, UInt64, UInt128

## floating point traits ##
```
-/
def IEEEFloat_types : List FTy := [.f16, .f32, .f64]
def IEEEFloat (T : FTy) : Bool := IEEEFloat_types.contains T

/--
Julia source: base/float.jl:9-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    Inf16

Positive infinity of type [`Float16`](@ref).
"""
const Inf16 = bitcast(Float16, 0x7c00)
```
-/
def Inf16 : FV .f16 := bitcast_to_float .f16 (int.lit .u16 0x7c00)

/--
Julia source: base/float.jl:16-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    NaN16

A not-a-number value of type [`Float16`](@ref).

See also: [`NaN`](@ref).
"""
const NaN16 = bitcast(Float16, 0x7e00)
```
-/
def NaN16 : FV .f16 := bitcast_to_float .f16 (int.lit .u16 0x7e00)

/--
Julia source: base/float.jl:24-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Inf32

Positive infinity of type [`Float32`](@ref).
"""
const Inf32 = bitcast(Float32, 0x7f800000)
```
-/
def Inf32 : FV .f32 := bitcast_to_float .f32 (int.lit .u32 0x7f800000)

/--
Julia source: base/float.jl:30-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    NaN32

A not-a-number value of type [`Float32`](@ref).

See also: [`NaN`](@ref).
"""
const NaN32 = bitcast(Float32, 0x7fc00000)
```
-/
def NaN32 : FV .f32 := bitcast_to_float .f32 (int.lit .u32 0x7fc00000)

/--
Julia source: base/float.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const Inf64 = bitcast(Float64, 0x7ff0000000000000)
```
-/
def Inf64 : FV .f64 := bitcast_to_float .f64 (int.lit .u64 0x7ff0000000000000)

/--
Julia source: base/float.jl:39-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const NaN64 = bitcast(Float64, 0x7ff8000000000000)

```
-/
def NaN64 : FV .f64 := bitcast_to_float .f64 (int.lit .u64 0x7ff8000000000000)

/--
Julia source: base/float.jl:41-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
const Inf = Inf64
"""
    Inf, Inf64

Positive infinity of type [`Float64`](@ref).

See also: [`isfinite`](@ref), [`typemax`](@ref), [`NaN`](@ref), [`Inf32`](@ref).

# Examples
```jldoctest
julia> π/0
Inf

julia> +1.0 / -0.0
-Inf

julia> ℯ^-Inf
0.0
```
"""
Inf, Inf64

````
-/
def Inf : FV .f64 := Inf64

/--
Julia source: base/float.jl:63-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
const NaN = NaN64
"""
    NaN, NaN64

A not-a-number value of type [`Float64`](@ref).

See also: [`isnan`](@ref), [`missing`](@ref), [`NaN32`](@ref), [`Inf`](@ref).

# Examples
```jldoctest
julia> 0/0
NaN

julia> Inf - Inf
NaN

julia> NaN == NaN, isequal(NaN, NaN), isnan(NaN)
(false, true, true)
```

!!! note
    Always use [`isnan`](@ref) or [`isequal`](@ref) for checking for `NaN`.
    Using `x === NaN` may give unexpected results:
    ```jldoctest
    julia> reinterpret(UInt32, NaN32)
    0x7fc00000

    julia> NaN32p1 = reinterpret(Float32, 0x7fc00001)
    NaN32

    julia> NaN32p1 === NaN32, isequal(NaN32p1, NaN32), isnan(NaN32p1)
    (false, true, true)
    ```
"""
NaN, NaN64

````
-/
def NaN : FV .f64 := NaN64

/--
Julia source: base/float.jl:99-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# bit patterns
reinterpret(::Type{Unsigned}, x::Float64) = reinterpret(UInt64, x)
```
-/
def reinterpret_Unsigned_Float64 (x : FV .f64) : JInt .u64 := reinterpret_Int_Float .u64 x

/--
Julia source: base/float.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinterpret(::Type{Unsigned}, x::Float32) = reinterpret(UInt32, x)
```
-/
def reinterpret_Unsigned_Float32 (x : FV .f32) : JInt .u32 := reinterpret_Int_Float .u32 x

/--
Julia source: base/float.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinterpret(::Type{Unsigned}, x::Float16) = reinterpret(UInt16, x)
```
-/
def reinterpret_Unsigned_Float16 (x : FV .f16) : JInt .u16 := reinterpret_Int_Float .u16 x

/--
Julia source: base/float.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinterpret(::Type{Signed}, x::Float64) = reinterpret(Int64, x)
```
-/
def reinterpret_Signed_Float64 (x : FV .f64) : JInt .i64 := reinterpret_Int_Float .i64 x

/--
Julia source: base/float.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinterpret(::Type{Signed}, x::Float32) = reinterpret(Int32, x)
```
-/
def reinterpret_Signed_Float32 (x : FV .f32) : JInt .i32 := reinterpret_Int_Float .i32 x

/--
Julia source: base/float.jl:105-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinterpret(::Type{Signed}, x::Float16) = reinterpret(Int16, x)

```
-/
def reinterpret_Signed_Float16 (x : FV .f16) : JInt .i16 := reinterpret_Int_Float .i16 x

/-- *dispatch*: `reinterpret(Unsigned, x)` for an `IEEEFloat`. -/
def reinterpret_Unsigned : {T : FTy} → FV T → JInt T.uintTy
  | .f64, x => reinterpret_Unsigned_Float64 x
  | .f32, x => reinterpret_Unsigned_Float32 x
  | .f16, x => reinterpret_Unsigned_Float16 x

/-- *dispatch*: `reinterpret(Signed, x)` for an `IEEEFloat`. -/
def reinterpret_Signed : {T : FTy} → FV T → JInt T.intTy
  | .f64, x => reinterpret_Signed_Float64 x
  | .f32, x => reinterpret_Signed_Float32 x
  | .f16, x => reinterpret_Signed_Float16 x

/--
Julia source: base/float.jl:107-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sign_mask(::Type{Float64}) =        0x8000_0000_0000_0000
```
-/
def sign_mask_Float64 : JInt .u64 := int.lit .u64 0x8000_0000_0000_0000

/--
Julia source: base/float.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_mask(::Type{Float64}) =    0x7ff0_0000_0000_0000
```
-/
def exponent_mask_Float64 : JInt .u64 := int.lit .u64 0x7ff0_0000_0000_0000

/--
Julia source: base/float.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_one(::Type{Float64}) =     0x3ff0_0000_0000_0000
```
-/
def exponent_one_Float64 : JInt .u64 := int.lit .u64 0x3ff0_0000_0000_0000

/--
Julia source: base/float.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_half(::Type{Float64}) =    0x3fe0_0000_0000_0000
```
-/
def exponent_half_Float64 : JInt .u64 := int.lit .u64 0x3fe0_0000_0000_0000

/--
Julia source: base/float.jl:111-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
significand_mask(::Type{Float64}) = 0x000f_ffff_ffff_ffff

```
-/
def significand_mask_Float64 : JInt .u64 := int.lit .u64 0x000f_ffff_ffff_ffff

/--
Julia source: base/float.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sign_mask(::Type{Float32}) =        0x8000_0000
```
-/
def sign_mask_Float32 : JInt .u32 := int.lit .u32 0x8000_0000

/--
Julia source: base/float.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_mask(::Type{Float32}) =    0x7f80_0000
```
-/
def exponent_mask_Float32 : JInt .u32 := int.lit .u32 0x7f80_0000

/--
Julia source: base/float.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_one(::Type{Float32}) =     0x3f80_0000
```
-/
def exponent_one_Float32 : JInt .u32 := int.lit .u32 0x3f80_0000

/--
Julia source: base/float.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_half(::Type{Float32}) =    0x3f00_0000
```
-/
def exponent_half_Float32 : JInt .u32 := int.lit .u32 0x3f00_0000

/--
Julia source: base/float.jl:117-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
significand_mask(::Type{Float32}) = 0x007f_ffff

```
-/
def significand_mask_Float32 : JInt .u32 := int.lit .u32 0x007f_ffff

/--
Julia source: base/float.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sign_mask(::Type{Float16}) =        0x8000
```
-/
def sign_mask_Float16 : JInt .u16 := int.lit .u16 0x8000

/--
Julia source: base/float.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_mask(::Type{Float16}) =    0x7c00
```
-/
def exponent_mask_Float16 : JInt .u16 := int.lit .u16 0x7c00

/--
Julia source: base/float.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_one(::Type{Float16}) =     0x3c00
```
-/
def exponent_one_Float16 : JInt .u16 := int.lit .u16 0x3c00

/--
Julia source: base/float.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_half(::Type{Float16}) =    0x3800
```
-/
def exponent_half_Float16 : JInt .u16 := int.lit .u16 0x3800

/--
Julia source: base/float.jl:123-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
significand_mask(::Type{Float16}) = 0x03ff

```
-/
def significand_mask_Float16 : JInt .u16 := int.lit .u16 0x03ff

/-- *dispatch*: `sign_mask(T)` for an `IEEEFloat` type `T`. -/
def sign_mask : (T : FTy) → JInt T.uintTy
  | .f64 => sign_mask_Float64 | .f32 => sign_mask_Float32 | .f16 => sign_mask_Float16
/-- *dispatch*: `exponent_mask(T)` for an `IEEEFloat` type `T`. -/
def exponent_mask : (T : FTy) → JInt T.uintTy
  | .f64 => exponent_mask_Float64 | .f32 => exponent_mask_Float32 | .f16 => exponent_mask_Float16
/-- *dispatch*: `exponent_one(T)` for an `IEEEFloat` type `T`. -/
def exponent_one : (T : FTy) → JInt T.uintTy
  | .f64 => exponent_one_Float64 | .f32 => exponent_one_Float32 | .f16 => exponent_one_Float16
/-- *dispatch*: `exponent_half(T)` for an `IEEEFloat` type `T`. -/
def exponent_half : (T : FTy) → JInt T.uintTy
  | .f64 => exponent_half_Float64 | .f32 => exponent_half_Float32 | .f16 => exponent_half_Float16
/-- *dispatch*: `significand_mask(T)` for an `IEEEFloat` type `T`. -/
def significand_mask : (T : FTy) → JInt T.uintTy
  | .f64 => significand_mask_Float64 | .f32 => significand_mask_Float32 | .f16 => significand_mask_Float16

/--
Julia source: base/float.jl:125-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mantissa(x::T) where {T} = reinterpret(Unsigned, x) & significand_mask(T)

```
-/
def mantissa {T : FTy} (x : FV T) : JInt T.uintTy :=
  int.band (reinterpret_Unsigned x) (significand_mask T)

/--
Julia source: base/float.jl:127-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for T in (Float16, Float32, Float64)
    sb = trailing_ones(significand_mask(T))
    em = exponent_mask(T)
    eb = Int(exponent_one(T) >> sb)
    @eval significand_bits(::Type{$T}) = $(sb)
```
-/
def significand_bits (T : FTy) : JInt .i64 :=
  int.trailing_ones_Integer int.trailing_zeros int.bnot (significand_mask T)

/--
Julia source: base/float.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval exponent_bits(::Type{$T}) = $(sizeof(T)*8 - sb - 1)
```
-/
def exponent_bits (T : FTy) : JInt .i64 :=
  int.sub (int.sub (int.mul (int.lit .i64 T.bytes) (int.lit .i64 8)) (significand_bits T)) (int.lit .i64 1)

/--
Julia source: base/float.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval exponent_bias(::Type{$T}) = $(eb)
```
-/
def exponent_bias (T : FTy) : JInt .i64 :=
  int.remT .i64 (int.shr_Int (exponent_one T) (significand_bits T))

/--
Julia source: base/float.jl:134-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    # maximum float exponent
    @eval exponent_max(::Type{$T}) = $(Int(em >> sb) - eb - 1)
```
-/
def exponent_max (T : FTy) : JInt .i64 :=
  int.sub (int.sub (int.remT .i64 (int.shr_Int (exponent_mask T) (significand_bits T))) (exponent_bias T)) (int.lit .i64 1)

/--
Julia source: base/float.jl:136-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    # maximum float exponent without bias
    @eval exponent_raw_max(::Type{$T}) = $(Int(em >> sb))
end

```
-/
def exponent_raw_max (T : FTy) : JInt .i64 :=
  int.remT .i64 (int.shr_Int (exponent_mask T) (significand_bits T))

/--
Julia source: base/float.jl:140-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    exponent_max(T)

Maximum [`exponent`](@ref) value for a floating point number of type `T`.

# Examples
```jldoctest
julia> Base.exponent_max(Float64)
1023
```

Note, `exponent_max(T) + 1` is a possible value of the exponent field
with bias, which might be used as sentinel value for `Inf` or `NaN`.
"""
function exponent_max end

"""
    exponent_raw_max(T)

Maximum value of the [`exponent`](@ref) field for a floating point number of type `T` without bias,
i.e. the maximum integer value representable by [`exponent_bits(T)`](@ref) bits.
"""
function exponent_raw_max end

"""
IEEE 754 definition of the minimum exponent.
"""
ieee754_exponent_min(::Type{T}) where {T<:IEEEFloat} = Int(1 - exponent_max(T))::Int

````
-/
def ieee754_exponent_min (T : FTy) : JInt .i64 :=
  int.sub (int.lit .i64 1) (exponent_max T)

/--
Julia source: base/float.jl:169-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exponent_min(T::Union{Type{Float16},Type{Float32},Type{Float64}}) = ieee754_exponent_min(T)

```
-/
def exponent_min (T : FTy) : JInt .i64 := ieee754_exponent_min T

/--
Julia source: base/float.jl:171-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ieee754_representation(
    ::Type{F}, sign_bit::Bool, exponent_field::Integer, significand_field::Integer
) where {F<:IEEEFloat}
    T = uinttype(F)
    ret::T = sign_bit
    ret <<= exponent_bits(F)
    ret |= exponent_field
    ret <<= significand_bits(F)
    ret |= significand_field
    return ret
end

```
-/
def ieee754_representation (F : FTy) {te ts : IntTy} (sign_bit : Bool)
    (exponent_field : JInt te) (significand_field : JInt ts) : JInt F.uintTy :=
  let ret : JInt F.uintTy := int.ofBool F.uintTy sign_bit
  let ret := int.shl_Int ret (exponent_bits F)
  let ret := int.remT F.uintTy (int.binop int.bor ret exponent_field)
  let ret := int.shl_Int ret (significand_bits F)
  let ret := int.remT F.uintTy (int.binop int.bor ret significand_field)
  ret

/--
Julia source: base/float.jl:183-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# ±floatmax(T)
function ieee754_representation(
    ::Type{F}, sign_bit::Bool, ::Val{:omega}
) where {F<:IEEEFloat}
    ieee754_representation(F, sign_bit, exponent_raw_max(F) - 1, significand_mask(F))
end

```
-/
def ieee754_representation_omega (F : FTy) (sign_bit : Bool) : JInt F.uintTy :=
  ieee754_representation F sign_bit (int.sub (exponent_raw_max F) (int.lit .i64 1)) (significand_mask F)

/--
Julia source: base/float.jl:190-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# NaN or an infinity
function ieee754_representation(
    ::Type{F}, sign_bit::Bool, significand_field::Integer, ::Val{:nan}
) where {F<:IEEEFloat}
    ieee754_representation(F, sign_bit, exponent_raw_max(F), significand_field)
end

```
-/
def ieee754_representation_nan_payload (F : FTy) {ts : IntTy} (sign_bit : Bool)
    (significand_field : JInt ts) : JInt F.uintTy :=
  ieee754_representation F sign_bit (exponent_raw_max F) significand_field

/--
Julia source: base/float.jl:197-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# NaN with default payload
function ieee754_representation(
    ::Type{F}, sign_bit::Bool, ::Val{:nan}
) where {F<:IEEEFloat}
    ieee754_representation(F, sign_bit, one(uinttype(F)) << (significand_bits(F) - 1), Val(:nan))
end

```
-/
def ieee754_representation_nan (F : FTy) (sign_bit : Bool) : JInt F.uintTy :=
  ieee754_representation_nan_payload F sign_bit
    (int.shl_Int (int.lit F.uintTy 1) (int.sub (significand_bits F) (int.lit .i64 1)))

/--
Julia source: base/float.jl:204-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Infinity
function ieee754_representation(
    ::Type{F}, sign_bit::Bool, ::Val{:inf}
) where {F<:IEEEFloat}
    ieee754_representation(F, sign_bit, false, Val(:nan))
end

```
-/
def ieee754_representation_inf (F : FTy) (sign_bit : Bool) : JInt F.uintTy :=
  ieee754_representation_nan_payload F sign_bit (int.ofBool .u8 false)

/--
Julia source: base/float.jl:211-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Subnormal or zero
function ieee754_representation(
    ::Type{F}, sign_bit::Bool, significand_field::Integer, ::Val{:subnormal}
) where {F<:IEEEFloat}
    ieee754_representation(F, sign_bit, false, significand_field)
end

```
-/
def ieee754_representation_subnormal (F : FTy) {ts : IntTy} (sign_bit : Bool)
    (significand_field : JInt ts) : JInt F.uintTy :=
  ieee754_representation F sign_bit (int.ofBool .u8 false) significand_field

/--
Julia source: base/float.jl:218-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Zero
function ieee754_representation(
    ::Type{F}, sign_bit::Bool, ::Val{:zero}
) where {F<:IEEEFloat}
    ieee754_representation(F, sign_bit, false, Val(:subnormal))
end

```
-/
def ieee754_representation_zero (F : FTy) (sign_bit : Bool) : JInt F.uintTy :=
  ieee754_representation_subnormal F sign_bit (int.ofBool .u8 false)

/--
Julia source: base/float.jl:225-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.uabs(x::Integer)

Return the absolute value of `x`, possibly returning a different type should the
operation be susceptible to overflow. This typically arises when `x` is a two's complement
signed integer, so that `abs(typemin(x)) == typemin(x) < 0`, in which case the result of
`uabs(x)` will be an unsigned integer of the same size.

See also: [`abs`](@ref), [`Base.Checked.checked_abs`](@ref).
"""
uabs(x::Integer) = abs(x)
```
-/
def uabs_Integer {I A : Type} (abs : I → A) (x : I) : A := abs x

/--
Julia source: base/float.jl:236-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uabs(x::BitSigned) = unsigned(abs(x))

```
-/
def uabs_BitSigned {t : IntTy} (x : JInt t) : JInt t.toUnsigned :=
  int.unsigned (int.abs x)

/-- *dispatch*: `Base.uabs(x)` for a `BitInteger`. -/
def uabs {t : IntTy} (x : JInt t) : JInt t.toUnsigned :=
  if t.signed then uabs_BitSigned x else int.remT t.toUnsigned (uabs_Integer int.abs x)

/--
Julia source: base/float.jl:238-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## conversions to floating-point ##

# TODO: deprecate in 2.0
Float16(x::Integer) = convert(Float16, convert(Float32, x)::Float32)

```
-/
def Float16_Integer {I : Type} (toFloat32 : I → FV .f32) (toFloat16 : FV .f32 → FV .f16) (x : I) : FV .f16 :=
  toFloat16 (toFloat32 x)

/--
Julia source: base/float.jl:243-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for t1 in (Float16, Float32, Float64)
    for st in (Int8, Int16, Int32, Int64)
        @eval begin
            (::Type{$t1})(x::($st)) = sitofp($t1, x)
```
-/
def float_BitSigned64 (t1 : FTy) {st : IntTy} (x : JInt st) : FV t1 := sitofp t1 x

/--
Julia source: base/float.jl:247-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            promote_rule(::Type{$t1}, ::Type{$st}) = $t1
        end
    end
```
-/
def promote_rule_float_BitSigned64 (t1 : FTy) (_st : IntTy) : FTy := t1

/--
Julia source: base/float.jl:250-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    for ut in (Bool, UInt8, UInt16, UInt32, UInt64)
        @eval begin
            (::Type{$t1})(x::($ut)) = uitofp($t1, x)
```
-/
def float_BitUnsigned64 (t1 : FTy) {ut : IntTy} (x : JInt ut) : FV t1 := uitofp t1 x
def float_Bool (t1 : FTy) (x : Bool) : FV t1 := uitofp_Bool t1 x

/--
Julia source: base/float.jl:253-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            promote_rule(::Type{$t1}, ::Type{$ut}) = $t1
        end
    end
end

```
-/
def promote_rule_float_BitUnsigned64 (t1 : FTy) (_ut : IntTy) : FTy := t1
def promote_rule_float_Bool (t1 : FTy) : FTy := t1

/--
Julia source: base/float.jl:258-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Float64}, ::Type{UInt128}) = Float64
```
-/
def promote_rule_Float64_UInt128 : FTy := .f64

/--
Julia source: base/float.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Float64}, ::Type{Int128}) = Float64
```
-/
def promote_rule_Float64_Int128 : FTy := .f64

/--
Julia source: base/float.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Float32}, ::Type{UInt128}) = Float32
```
-/
def promote_rule_Float32_UInt128 : FTy := .f32

/--
Julia source: base/float.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Float32}, ::Type{Int128}) = Float32
```
-/
def promote_rule_Float32_Int128 : FTy := .f32

/--
Julia source: base/float.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Float16}, ::Type{UInt128}) = Float16
```
-/
def promote_rule_Float16_UInt128 : FTy := .f16

/--
Julia source: base/float.jl:263-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Float16}, ::Type{Int128}) = Float16

```
-/
def promote_rule_Float16_Int128 : FTy := .f16

/-- *dispatch*: `promote_rule(T, S)` for an `IEEEFloat` `T` and a `BitInteger` `S`. -/
def promote_rule_float_int : FTy → IntTy → FTy
  | .f64, .u128 => promote_rule_Float64_UInt128
  | .f64, .i128 => promote_rule_Float64_Int128
  | .f32, .u128 => promote_rule_Float32_UInt128
  | .f32, .i128 => promote_rule_Float32_Int128
  | .f16, .u128 => promote_rule_Float16_UInt128
  | .f16, .i128 => promote_rule_Float16_Int128
  | T, s => if s.signed then promote_rule_float_BitSigned64 T s else promote_rule_float_BitUnsigned64 T s

/--
Julia source: base/float.jl:265-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Float64(x::UInt128)
    if x < UInt128(1) << 104 # Can fit it in two 52 bits mantissas
        low_exp = 0x1p52
        high_exp = 0x1p104
        low_bits = (x % UInt64) & Base.significand_mask(Float64)
        low_value = reinterpret(Float64, reinterpret(UInt64, low_exp) | low_bits) - low_exp
        high_bits = ((x >> 52) % UInt64)
        high_value = reinterpret(Float64, reinterpret(UInt64, high_exp) | high_bits) - high_exp
        low_value + high_value
    else # Large enough that low bits only affect rounding, pack low bits
        low_exp = 0x1p76
        high_exp = 0x1p128
        low_bits = ((x >> 12) % UInt64) >> 12 | (x % UInt64) & 0xFFFFFF
        low_value = reinterpret(Float64, reinterpret(UInt64, low_exp) | low_bits) - low_exp
        high_bits = ((x >> 76) % UInt64)
        high_value = reinterpret(Float64, reinterpret(UInt64, high_exp) | high_bits) - high_exp
        low_value + high_value
    end
end

```
-/
def Float64_UInt128 (x : JInt .u128) : FV .f64 :=
  if int.lt_BitUnsigned x (int.shl_Int (int.lit .u128 1) (int.lit .i64 104)) then
    let low_exp : FV .f64 := Fl.ofBits 0x4330_0000_0000_0000
    let high_exp : FV .f64 := Fl.ofBits 0x4670_0000_0000_0000
    let low_bits := int.band (int.remT .u64 x) (significand_mask .f64)
    let low_value := sub_float (reinterpret_Float_Int .f64 (int.bor (reinterpret_Unsigned_Float64 low_exp) low_bits)) low_exp
    let high_bits := int.remT .u64 (int.shr_Int x (int.lit .i64 52))
    let high_value := sub_float (reinterpret_Float_Int .f64 (int.bor (reinterpret_Unsigned_Float64 high_exp) high_bits)) high_exp
    add_float low_value high_value
  else
    let low_exp : FV .f64 := Fl.ofBits 0x44b0_0000_0000_0000
    let high_exp : FV .f64 := Fl.ofBits 0x47f0_0000_0000_0000
    let low_bits := int.bor (int.shr_Int (int.remT .u64 (int.shr_Int x (int.lit .i64 12))) (int.lit .i64 12))
      (int.band (int.remT .u64 x) (int.lit .u64 0xFFFFFF))
    let low_value := sub_float (reinterpret_Float_Int .f64 (int.bor (reinterpret_Unsigned_Float64 low_exp) low_bits)) low_exp
    let high_bits := int.remT .u64 (int.shr_Int x (int.lit .i64 76))
    let high_value := sub_float (reinterpret_Float_Int .f64 (int.bor (reinterpret_Unsigned_Float64 high_exp) high_bits)) high_exp
    add_float low_value high_value

/--
Julia source: base/float.jl:285-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Float64(x::Int128)
    sign_bit = ((x >> 127) % UInt64) << 63
    ux = uabs(x)
    if ux < UInt128(1) << 104 # Can fit it in two 52 bits mantissas
        low_exp = 0x1p52
        high_exp = 0x1p104
        low_bits = (ux % UInt64) & Base.significand_mask(Float64)
        low_value = reinterpret(Float64, reinterpret(UInt64, low_exp) | low_bits) - low_exp
        high_bits = ((ux >> 52) % UInt64)
        high_value = reinterpret(Float64, reinterpret(UInt64, high_exp) | high_bits) - high_exp
        reinterpret(Float64, sign_bit | reinterpret(UInt64, low_value + high_value))
    else # Large enough that low bits only affect rounding, pack low bits
        low_exp = 0x1p76
        high_exp = 0x1p128
        low_bits = ((ux >> 12) % UInt64) >> 12 | (ux % UInt64) & 0xFFFFFF
        low_value = reinterpret(Float64, reinterpret(UInt64, low_exp) | low_bits) - low_exp
        high_bits = ((ux >> 76) % UInt64)
        high_value = reinterpret(Float64, reinterpret(UInt64, high_exp) | high_bits) - high_exp
        reinterpret(Float64, sign_bit | reinterpret(UInt64, low_value + high_value))
    end
end

```
-/
def Float64_Int128 (x : JInt .i128) : FV .f64 :=
  let sign_bit := int.shl_Int (int.remT .u64 (int.shr_Int x (int.lit .i64 127))) (int.lit .i64 63)
  let ux : JInt .u128 := uabs_BitSigned x
  if int.lt_BitUnsigned ux (int.shl_Int (int.lit .u128 1) (int.lit .i64 104)) then
    let low_exp : FV .f64 := Fl.ofBits 0x4330_0000_0000_0000
    let high_exp : FV .f64 := Fl.ofBits 0x4670_0000_0000_0000
    let low_bits := int.band (int.remT .u64 ux) (significand_mask .f64)
    let low_value := sub_float (reinterpret_Float_Int .f64 (int.bor (reinterpret_Unsigned_Float64 low_exp) low_bits)) low_exp
    let high_bits := int.remT .u64 (int.shr_Int ux (int.lit .i64 52))
    let high_value := sub_float (reinterpret_Float_Int .f64 (int.bor (reinterpret_Unsigned_Float64 high_exp) high_bits)) high_exp
    reinterpret_Float_Int .f64 (int.bor sign_bit (reinterpret_Unsigned_Float64 (add_float low_value high_value)))
  else
    let low_exp : FV .f64 := Fl.ofBits 0x44b0_0000_0000_0000
    let high_exp : FV .f64 := Fl.ofBits 0x47f0_0000_0000_0000
    let low_bits := int.bor (int.shr_Int (int.remT .u64 (int.shr_Int ux (int.lit .i64 12))) (int.lit .i64 12))
      (int.band (int.remT .u64 ux) (int.lit .u64 0xFFFFFF))
    let low_value := sub_float (reinterpret_Float_Int .f64 (int.bor (reinterpret_Unsigned_Float64 low_exp) low_bits)) low_exp
    let high_bits := int.remT .u64 (int.shr_Int ux (int.lit .i64 76))
    let high_value := sub_float (reinterpret_Float_Int .f64 (int.bor (reinterpret_Unsigned_Float64 high_exp) high_bits)) high_exp
    reinterpret_Float_Int .f64 (int.bor sign_bit (reinterpret_Unsigned_Float64 (add_float low_value high_value)))

/--
Julia source: base/float.jl:307-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Float32(x::UInt128)
    x == 0 && return 0f0
    n = top_set_bit(x) # ndigits0z(x,2)
    if n <= 24
        y = ((x % UInt32) << (24-n)) & 0x007f_ffff
    else
        y = ((x >> (n-25)) % UInt32) & 0x00ff_ffff # keep 1 extra bit
        y = (y+one(UInt32))>>1 # round, ties up (extra leading bit in case of next exponent)
        y &= ~UInt32(trailing_zeros(x) == (n-25)) # fix last bit to round to even
    end
    d = ((n+126) % UInt32) << 23
    reinterpret(Float32, d + y)
end

```
-/
def Float32_UInt128 (x : JInt .u128) : FV .f32 :=
  if int.eq x (int.lit .i64 0) then zero_float .f32
  else
    let n := int.top_set_bit x
    let y :=
      if int.le_BitSigned n (int.lit .i64 24) then
        int.band (int.shl_Int (int.remT .u32 x) (int.sub (int.lit .i64 24) n)) (int.lit .u32 0x007f_ffff)
      else
        let y := int.band (int.remT .u32 (int.shr_Int x (int.sub n (int.lit .i64 25)))) (int.lit .u32 0x00ff_ffff)
        let y := int.shr_Int (int.add y (int.lit .u32 1)) (int.lit .i64 1)
        int.band y (int.bnot (int.ofBool .u32 (int.eq_int (int.trailing_zeros x) (int.sub n (int.lit .i64 25)))))
    let d := int.shl_Int (int.remT .u32 (int.add n (int.lit .i64 126))) (int.lit .i64 23)
    reinterpret_Float_Int .f32 (int.add d y)

/--
Julia source: base/float.jl:321-336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Float32(x::Int128)
    x == 0 && return 0f0
    s = ((x >>> 96) % UInt32) & 0x8000_0000 # sign bit
    x = abs(x) % UInt128
    n = top_set_bit(x) # ndigits0z(x,2)
    if n <= 24
        y = ((x % UInt32) << (24-n)) & 0x007f_ffff
    else
        y = ((x >> (n-25)) % UInt32) & 0x00ff_ffff # keep 1 extra bit
        y = (y+one(UInt32))>>1 # round, ties up (extra leading bit in case of next exponent)
        y &= ~UInt32(trailing_zeros(x) == (n-25)) # fix last bit to round to even
    end
    d = ((n+126) % UInt32) << 23
    reinterpret(Float32, s | d + y)
end

```
-/
def Float32_Int128 (x : JInt .i128) : FV .f32 :=
  if int.eq x (int.lit .i64 0) then zero_float .f32
  else
    let s := int.band (int.remT .u32 (int.lshr_Int x (int.lit .i64 96))) (int.lit .u32 0x8000_0000)
    let x := int.remT .u128 (int.abs_Signed x)
    let n := int.top_set_bit x
    let y :=
      if int.le_BitSigned n (int.lit .i64 24) then
        int.band (int.shl_Int (int.remT .u32 x) (int.sub (int.lit .i64 24) n)) (int.lit .u32 0x007f_ffff)
      else
        let y := int.band (int.remT .u32 (int.shr_Int x (int.sub n (int.lit .i64 25)))) (int.lit .u32 0x00ff_ffff)
        let y := int.shr_Int (int.add y (int.lit .u32 1)) (int.lit .i64 1)
        int.band y (int.bnot (int.ofBool .u32 (int.eq_int (int.trailing_zeros x) (int.sub n (int.lit .i64 25)))))
    let d := int.shl_Int (int.remT .u32 (int.add n (int.lit .i64 126))) (int.lit .i64 23)
    reinterpret_Float_Int .f32 (int.bor s (int.add d y))

/--
Julia source: base/float.jl:337-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# TODO: optimize
Float16(x::UInt128) = convert(Float16, Float64(x))
```
-/
def Float16_UInt128 (toFloat16 : FV .f64 → FV .f16) (x : JInt .u128) : FV .f16 :=
  toFloat16 (Float64_UInt128 x)

/--
Julia source: base/float.jl:339-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float16(x::Int128)  = convert(Float16, Float64(x))

```
-/
def Float16_Int128 (toFloat16 : FV .f64 → FV .f16) (x : JInt .i128) : FV .f16 :=
  toFloat16 (Float64_Int128 x)

/--
Julia source: base/float.jl:341-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float16(x::Float32) = fptrunc(Float16, x)
```
-/
def Float16_Float32 (x : FV .f32) : FV .f16 := fptrunc .f16 x

/--
Julia source: base/float.jl:342-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float16(x::Float64) = fptrunc(Float16, x)
```
-/
def Float16_Float64 (x : FV .f64) : FV .f16 := fptrunc .f16 x

/--
Julia source: base/float.jl:343-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float32(x::Float64) = fptrunc(Float32, x)

```
-/
def Float32_Float64 (x : FV .f64) : FV .f32 := fptrunc .f32 x

/--
Julia source: base/float.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float32(x::Float16) = fpext(Float32, x)
```
-/
def Float32_Float16 (x : FV .f16) : FV .f32 := fpext .f32 x

/--
Julia source: base/float.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float64(x::Float32) = fpext(Float64, x)
```
-/
def Float64_Float32 (x : FV .f32) : FV .f64 := fpext .f64 x

/--
Julia source: base/float.jl:347-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float64(x::Float16) = fpext(Float64, x)

```
-/
def Float64_Float16 (x : FV .f16) : FV .f64 := fpext .f64 x

/-- *dispatch*: `T(x)` for an `IEEEFloat` type `T` and a `BitInteger` `x`. -/
def floatOfInt : (T : FTy) → {t : IntTy} → JInt t → FV T
  | .f64, .u128, x => Float64_UInt128 x
  | .f64, .i128, x => Float64_Int128 x
  | .f32, .u128, x => Float32_UInt128 x
  | .f32, .i128, x => Float32_Int128 x
  | .f16, .u128, x => Float16_UInt128 Float16_Float64 x
  | .f16, .i128, x => Float16_Int128 Float16_Float64 x
  | T, .i8, x | T, .i16, x | T, .i32, x | T, .i64, x => float_BitSigned64 T x
  | T, .u8, x | T, .u16, x | T, .u32, x | T, .u64, x => float_BitUnsigned64 T x

/-- *dispatch*: `T(x)` / `convert(T, x)` between `IEEEFloat` types (`boot.jl:1195` for `T = S`). -/
def convertFloat : (T : FTy) → {S : FTy} → FV S → FV T
  | .f16, .f16, x => x
  | .f16, .f32, x => Float16_Float32 x
  | .f16, .f64, x => Float16_Float64 x
  | .f32, .f16, x => Float32_Float16 x
  | .f32, .f32, x => x
  | .f32, .f64, x => Float32_Float64 x
  | .f64, .f16, x => Float64_Float16 x
  | .f64, .f32, x => Float64_Float32 x
  | .f64, .f64, x => x

/--
Julia source: base/float.jl:349-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# lossy for the 64- and 128-bit integer types
AbstractFloat(x::Union{Bool, BitInteger}) = Float64(x)

```
-/
def AbstractFloat_BitInteger {t : IntTy} (x : JInt t) : FV .f64 := floatOfInt .f64 x
def AbstractFloat_Bool (x : Bool) : FV .f64 := float_Bool .f64 x

/--
Julia source: base/float.jl:352-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Bool(x::Float16) = x==0 ? false : x==1 ? true : throw(InexactError(:Bool, Bool, x))

```
-/
def Bool_Float16 (x : FV .f16) : Jl Bool :=
  if eq_float x (zero_float .f16) then .ok false
  else if eq_float x (one_float .f16) then .ok true
  else .error (.inexactError "Bool")

/--
Julia source: base/float.jl:354-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    float(x)

Convert a number or array to a floating point data type.

See also: [`complex`](@ref), [`oftype`](@ref), [`convert`](@ref).

# Examples
```jldoctest
julia> float(typemax(Int32))
2.147483647e9
```
"""
float(x) = AbstractFloat(x)

````
-/
def float_any {α β : Type} (AbstractFloat : α → β) (x : α) : β := AbstractFloat x
def float_BitInteger {t : IntTy} (x : JInt t) : FV .f64 := float_any AbstractFloat_BitInteger x

/--
Julia source: base/float.jl:369-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    float(T::Type)

Return an appropriate type to represent a value of type `T` as a floating point value.
Equivalent to `typeof(float(zero(T)))`.

# Examples
```jldoctest
julia> float(Complex{Int})
ComplexF64 (alias for Complex{Float64})

julia> float(Int)
Float64
```
"""
float(::Type{T}) where {T<:Number} = typeof(float(zero(T)))
````
-/
def float_Type_Number {T F R : Type} (zero : Unit → T) (float : T → F) (typeof : F → R) : R :=
  typeof (float (zero ()))

/--
Julia source: base/float.jl:385-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(::Type{T}) where {T<:AbstractFloat} = T
```
-/
def float_Type_AbstractFloat {α : Type} (T : α) : α := T

/--
Julia source: base/float.jl:386-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(::Type{Union{}}) = Union{}
```
-/
def float_Type_Bottom : Option FTy := none

/--
Julia source: base/float.jl:387-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(::Type{Union{}}, slurp...) = throw(MethodError(float, (Union{}, slurp...)))

```
-/
def float_Type_Bottom_slurp {α : Type} : Jl α := .error (.methodError "float")

/--
Julia source: base/float.jl:389-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    unsafe_trunc(T, x)

Return the nearest integral value of type `T` whose absolute value is
less than or equal to the absolute value of `x`. If the value is not representable by `T`,
an arbitrary value will be returned.
See also [`trunc`](@ref).

# Examples
```jldoctest
julia> unsafe_trunc(Int, -2.2)
-2

julia> unsafe_trunc(Int, NaN) isa Int
true
```
"""
function unsafe_trunc end

for Ti in (Int8, Int16, Int32, Int64)
    @eval begin
        unsafe_trunc(::Type{$Ti}, x::IEEEFloat) = fptosi($Ti, x)
    end
end
````
-/
def unsafe_trunc_BitSigned64 (Ti : IntTy) {T : FTy} (x : FV T) : JInt Ti := fptosi Ti x

/--
Julia source: base/float.jl:413-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for Ti in (UInt8, UInt16, UInt32, UInt64)
    @eval begin
        unsafe_trunc(::Type{$Ti}, x::IEEEFloat) = fptoui($Ti, x)
    end
end

```
-/
def unsafe_trunc_BitUnsigned64 (Ti : IntTy) {T : FTy} (x : FV T) : JInt Ti := fptoui Ti x

/--
Julia source: base/float.jl:419-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_trunc(::Type{UInt128}, x::Float64)
    xu = reinterpret(UInt64,x)
    # use `% Int` instead of `Int(...)` to preserve `:nothrow` (the shifted value
    # fits in 11 bits, but `Int(::UInt64)` would otherwise add a bounds check)
    k = ((xu >> 52) % Int) & 0x07ff - 1075
    xu = (xu & 0x000f_ffff_ffff_ffff) | 0x0010_0000_0000_0000
    if k <= 0
        UInt128(xu >> -k)
    else
        UInt128(xu) << k
    end
end
```
-/
def unsafe_trunc_UInt128_Float64 (x : FV .f64) : JInt .u128 :=
  let xu := reinterpret_Unsigned_Float64 x
  let k := int.sub (int.band (int.remT .i64 (int.shr_Int xu (int.lit .i64 52))) (int.lit .i64 0x07ff)) (int.lit .i64 1075)
  let xu := int.bor (int.band xu (int.lit .u64 0x000f_ffff_ffff_ffff)) (int.lit .u64 0x0010_0000_0000_0000)
  if int.le_BitSigned k (int.lit .i64 0) then
    int.widenTo .u128 (int.shr_Int xu (int.neg k))
  else
    int.shl_Int (int.widenTo .u128 xu) k

/--
Julia source: base/float.jl:431-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_trunc(::Type{Int128}, x::Float64)
    copysign(unsafe_trunc(UInt128,x) % Int128, x)
end

```
-/
def unsafe_trunc_Int128_Float64 (x : FV .f64) : JInt .i128 :=
  int.copysign_Float64 (int.remT .i128 (unsafe_trunc_UInt128_Float64 x)) x

/--
Julia source: base/float.jl:435-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_trunc(::Type{UInt128}, x::Float32)
    xu = reinterpret(UInt32,x)
    k = Int(xu >> 23) & 0x00ff - 150
    xu = (xu & 0x007f_ffff) | 0x0080_0000
    if k <= 0
        UInt128(xu >> -k)
    else
        UInt128(xu) << k
    end
end
```
-/
def unsafe_trunc_UInt128_Float32 (x : FV .f32) : JInt .u128 :=
  let xu := reinterpret_Unsigned_Float32 x
  let k := int.sub (int.band (int.remT .i64 (int.shr_Int xu (int.lit .i64 23))) (int.lit .i64 0x00ff)) (int.lit .i64 150)
  let xu := int.bor (int.band xu (int.lit .u32 0x007f_ffff)) (int.lit .u32 0x0080_0000)
  if int.le_BitSigned k (int.lit .i64 0) then
    int.widenTo .u128 (int.shr_Int xu (int.neg k))
  else
    int.shl_Int (int.widenTo .u128 xu) k

/--
Julia source: base/float.jl:445-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_trunc(::Type{Int128}, x::Float32)
    copysign(unsafe_trunc(UInt128,x) % Int128, x)
end

```
-/
def unsafe_trunc_Int128_Float32 (x : FV .f32) : JInt .i128 :=
  int.copysign_Float32 (int.remT .i128 (unsafe_trunc_UInt128_Float32 x)) x

/--
Julia source: base/float.jl:449-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_trunc(::Type{UInt128}, x::Float16) = unsafe_trunc(UInt128, Float32(x))
```
-/
def unsafe_trunc_UInt128_Float16 (x : FV .f16) : JInt .u128 :=
  unsafe_trunc_UInt128_Float32 (Float32_Float16 x)

/--
Julia source: base/float.jl:450-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_trunc(::Type{Int128}, x::Float16) = unsafe_trunc(Int128, Float32(x))

```
-/
def unsafe_trunc_Int128_Float16 (x : FV .f16) : JInt .i128 :=
  unsafe_trunc_Int128_Float32 (Float32_Float16 x)

/-- *dispatch*: `unsafe_trunc(Ti, x)` for a `BitInteger` type `Ti` and an `IEEEFloat` `x`. -/
def unsafe_trunc : (Ti : IntTy) → {T : FTy} → FV T → JInt Ti
  | .u128, .f64, x => unsafe_trunc_UInt128_Float64 x
  | .i128, .f64, x => unsafe_trunc_Int128_Float64 x
  | .u128, .f32, x => unsafe_trunc_UInt128_Float32 x
  | .i128, .f32, x => unsafe_trunc_Int128_Float32 x
  | .u128, .f16, x => unsafe_trunc_UInt128_Float16 x
  | .i128, .f16, x => unsafe_trunc_Int128_Float16 x
  | .i8, _, x => unsafe_trunc_BitSigned64 .i8 x
  | .i16, _, x => unsafe_trunc_BitSigned64 .i16 x
  | .i32, _, x => unsafe_trunc_BitSigned64 .i32 x
  | .i64, _, x => unsafe_trunc_BitSigned64 .i64 x
  | .u8, _, x => unsafe_trunc_BitUnsigned64 .u8 x
  | .u16, _, x => unsafe_trunc_BitUnsigned64 .u16 x
  | .u32, _, x => unsafe_trunc_BitUnsigned64 .u32 x
  | .u64, _, x => unsafe_trunc_BitUnsigned64 .u64 x

/--
Julia source: base/float.jl:452-454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# matches convert methods
# also determines trunc, floor, ceil
round(::Type{Signed},   x::IEEEFloat, r::RoundingMode) = round(Int, x, r)
```
-/
def round_Signed {T : FTy} (roundInt : FV T → RoundingMode → Jl (JInt .i64))
    (x : FV T) (r : RoundingMode) : Jl (JInt .i64) := roundInt x r

/--
Julia source: base/float.jl:455-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{Unsigned}, x::IEEEFloat, r::RoundingMode) = round(UInt, x, r)
```
-/
def round_Unsigned {T : FTy} (roundUInt : FV T → RoundingMode → Jl (JInt .u64))
    (x : FV T) (r : RoundingMode) : Jl (JInt .u64) := roundUInt x r

/--
Julia source: base/float.jl:456-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{Integer},  x::IEEEFloat, r::RoundingMode) = round(Int, x, r)

```
-/
def round_Integer {T : FTy} (roundInt : FV T → RoundingMode → Jl (JInt .i64))
    (x : FV T) (r : RoundingMode) : Jl (JInt .i64) := roundInt x r

/--
Julia source: base/float.jl:458-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(x::IEEEFloat, ::RoundingMode{:ToZero})  = trunc_llvm(x)
```
-/
def round_ToZero_llvm {T : FTy} (x : FV T) : FV T := trunc_llvm x

/--
Julia source: base/float.jl:459-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(x::IEEEFloat, ::RoundingMode{:Down})    = floor_llvm(x)
```
-/
def round_Down_llvm {T : FTy} (x : FV T) : FV T := floor_llvm x

/--
Julia source: base/float.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(x::IEEEFloat, ::RoundingMode{:Up})      = ceil_llvm(x)
```
-/
def round_Up_llvm {T : FTy} (x : FV T) : FV T := ceil_llvm x

/--
Julia source: base/float.jl:461-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(x::IEEEFloat, ::RoundingMode{:Nearest}) = rint_llvm(x)

```
-/
def round_Nearest_llvm {T : FTy} (x : FV T) : FV T := rint_llvm x

/--
Julia source: base/float.jl:463-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_up(x, ::RoundingMode{:Down}) = false
```
-/
def rounds_up_Down {α : Type} (_x : α) : Bool := false

/--
Julia source: base/float.jl:464-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_up(x, ::RoundingMode{:Up}) = true
```
-/
def rounds_up_Up {α : Type} (_x : α) : Bool := true

/--
Julia source: base/float.jl:465-465 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_up(x, ::RoundingMode{:ToZero}) = signbit(x)
```
-/
def rounds_up_ToZero {α : Type} (signbit : α → Bool) (x : α) : Bool := signbit x

/--
Julia source: base/float.jl:466-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_up(x, ::RoundingMode{:FromZero}) = !signbit(x)
```
-/
def rounds_up_FromZero {α : Type} (signbit : α → Bool) (x : α) : Bool := !(signbit x)

/-- *dispatch*: `rounds_up(x, r)` for the four directed rounding modes. -/
def rounds_up {α : Type} (signbit : α → Bool) (x : α) : RoundingMode → Bool
  | .Down => rounds_up_Down x
  | .Up => rounds_up_Up x
  | .ToZero => rounds_up_ToZero signbit x
  | .FromZero => rounds_up_FromZero signbit x
  | _ => false

/--
Julia source: base/float.jl:467-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _round_convert(::Type{T}, x_integer, x, r::Union{RoundingMode{:ToZero}, RoundingMode{:FromZero}, RoundingMode{:Up}, RoundingMode{:Down}}) where {T<:AbstractFloat}
    x_t = convert(T, x_integer)
    if rounds_up(x, r)
        x_t < x ? nextfloat(x_t) : x_t
    else
        x_t > x ? prevfloat(x_t) : x_t
    end
end

```
-/
def _round_convert {T I X : Type} (convert : I → T) (signbit : X → Bool)
    (lt gt : T → X → Bool) (nextfloat prevfloat : T → T) (x_integer : I) (x : X) (r : RoundingMode) : T :=
  let x_t := convert x_integer
  if rounds_up signbit x r then
    if lt x_t x then nextfloat x_t else x_t
  else
    if gt x_t x then prevfloat x_t else x_t

/--
Julia source: base/float.jl:476-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## floating point promotions ##
promote_rule(::Type{Float32}, ::Type{Float16}) = Float32
```
-/
def promote_rule_Float32_Float16 : FTy := .f32

/--
Julia source: base/float.jl:478-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Float64}, ::Type{Float16}) = Float64
```
-/
def promote_rule_Float64_Float16 : FTy := .f64

/--
Julia source: base/float.jl:479-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Float64}, ::Type{Float32}) = Float64

```
-/
def promote_rule_Float64_Float32 : FTy := .f64

/-- *dispatch*: `promote_rule(T, S)` between `IEEEFloat` types. -/
def promote_rule_float : FTy → FTy → Option FTy
  | .f32, .f16 => some promote_rule_Float32_Float16
  | .f64, .f16 => some promote_rule_Float64_Float16
  | .f64, .f32 => some promote_rule_Float64_Float32
  | _, _ => none

/--
Julia source: base/float.jl:481-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{Float16}) = Float32
```
-/
def widen_Float16 : FTy := .f32

/--
Julia source: base/float.jl:482-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{Float32}) = Float64

```
-/
def widen_Float32 : FTy := .f64

/-- *dispatch*: `widen(T)` for an `IEEEFloat` type `T` (`Float64` widens to `BigFloat` in `mpfr.jl`). -/
def widen_float : FTy → Option FTy
  | .f16 => some widen_Float16
  | .f32 => some widen_Float32
  | .f64 => none

/--
Julia source: base/float.jl:484-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## floating point arithmetic ##
-(x::IEEEFloat) = neg_float(x)

```
-/
def neg_IEEEFloat {T : FTy} (x : FV T) : FV T := neg_float x

/--
Julia source: base/float.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::T, y::T) where {T<:IEEEFloat} = add_float(x, y)
```
-/
def add_IEEEFloat {T : FTy} (x y : FV T) : FV T := add_float x y

/--
Julia source: base/float.jl:488-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::T, y::T) where {T<:IEEEFloat} = sub_float(x, y)
```
-/
def sub_IEEEFloat {T : FTy} (x y : FV T) : FV T := sub_float x y

/--
Julia source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::T, y::T) where {T<:IEEEFloat} = mul_float(x, y)
```
-/
def mul_IEEEFloat {T : FTy} (x y : FV T) : FV T := mul_float x y

/--
Julia source: base/float.jl:490-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
/(x::T, y::T) where {T<:IEEEFloat} = div_float(x, y)

```
-/
def div_IEEEFloat {T : FTy} (x y : FV T) : FV T := div_float x y

/--
Julia source: base/float.jl:492-497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
muladd(x::T, y::T, z::T) where {T<:IEEEFloat} = muladd_float(x, y, z)

# TODO: faster floating point div?
# TODO: faster floating point fld?
# TODO: faster floating point mod?

```
-/
def muladd_IEEEFloat {T : FTy} (x y z : FV T) : FV T := muladd_float x y z

/--
Julia source: base/float.jl:498-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unbiased_exponent(x::T) where {T<:IEEEFloat}
    return (reinterpret(Unsigned, x) & exponent_mask(T)) >> significand_bits(T)
end

```
-/
def unbiased_exponent {T : FTy} (x : FV T) : JInt T.uintTy :=
  int.shr_Int (int.band (reinterpret_Unsigned x) (exponent_mask T)) (significand_bits T)

/--
Julia source: base/float.jl:502-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function explicit_mantissa_noinfnan(x::T) where {T<:IEEEFloat}
    m = mantissa(x)
    issubnormal(x) || (m |= significand_mask(T) + uinttype(T)(1))
    return m
end

```
-/
def explicit_mantissa_noinfnan {T : FTy} (x : FV T) : JInt T.uintTy :=
  let m := mantissa x
  if issubnormal_callee x then m
  else int.bor m (int.add (significand_mask T) (int.lit T.uintTy 1))

/--
Julia source: base/float.jl:508-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _to_float(number::U, ep) where {U<:Unsigned}
    F = floattype(U)
    S = signed(U)
    epint = unsafe_trunc(S,ep)
    lz::signed(U) = unsafe_trunc(S, Core.Intrinsics.ctlz_int(number) - U(exponent_bits(F)))
    number <<= lz
    epint -= lz
    if epint >= 0
        bits = number & significand_mask(F)
        bits |= ((epint + S(1)) << significand_bits(F)) & exponent_mask(F)
    else
        bits = (number >> -epint) & significand_mask(F)
    end
    return reinterpret(F, bits)
end

```
-/
def _to_float_Unsigned {UT ST FT U S E B F : Type}
    (floattype : UT → FT) (signed : UT → ST)
    (unsafe_trunc_ep : ST → E → S) (unsafe_trunc_lz : ST → U → S)
    (ctlz : U → U) (exponent_bits : FT → B) (toU : B → U)
    (sub_u : U → U → U) (shl_u : U → S → U)
    (sub_s add_s : S → S → S) (nonnegative : S → Bool) (one_s : ST → S)
    (significand_bits : FT → B) (shl_s : S → B → S)
    (band_su : S → U → U) (band_u bor_u : U → U → U)
    (exponent_mask significand_mask : FT → U) (neg_s : S → S)
    (shr_u : U → S → U) (reinterpret : FT → U → F)
    (typeU : UT) (number : U) (ep : E) : F :=
  let f := floattype typeU
  let s := signed typeU
  let epint := unsafe_trunc_ep s ep
  let lz := unsafe_trunc_lz s (sub_u (ctlz number) (toU (exponent_bits f)))
  let number := shl_u number lz
  let epint := sub_s epint lz
  let bits :=
    if nonnegative epint then
      let bits := band_u number (significand_mask f)
      bor_u bits (band_su (shl_s (add_s epint (one_s s)) (significand_bits f)) (exponent_mask f))
    else
      band_u (shr_u number (neg_s epint)) (significand_mask f)
  reinterpret f bits
def _to_float {F : FTy} {tep : IntTy} (number : JInt F.uintTy) (ep : JInt tep) : FV F :=
  let epint := int.unsafe_trunc F.intTy ep
  let lz := int.unsafe_trunc F.intTy (int.sub (int.ctlz_int number) (int.remT F.uintTy (exponent_bits F)))
  let number := int.shl_Int number (int.widenTo .i64 lz)
  let epint := int.sub epint lz
  let bits :=
    if int.le_BitSigned (int.lit F.intTy 0) epint then
      let bits := int.band number (significand_mask F)
      int.bor bits (int.band (int.remT F.uintTy (int.shl_Int (int.add epint (int.lit F.intTy 1)) (significand_bits F))) (exponent_mask F))
    else
      int.band (int.shr_Int number (int.widenTo .i64 (int.neg epint))) (significand_mask F)
  reinterpret_Float_Int F bits

/-- The `while exp_diff > sides_zeroes_cnt` loop of `rem_internal` (lines 580-584). -/
def rem_internal_loop {T : FTy} : Nat → JInt T.uintTy → JInt T.uintTy → JInt T.uintTy → JInt T.uintTy →
    JInt T.uintTy × JInt T.uintTy
  | 0, exp_diff, _, m_x, _ => (exp_diff, m_x)
  | fuel + 1, exp_diff, sides_zeroes_cnt, m_x, m_y =>
    if int.lt_BitUnsigned sides_zeroes_cnt exp_diff then
      let exp_diff := int.sub exp_diff sides_zeroes_cnt
      let m_x := int.shl_BitInteger_BitUnsigned m_x sides_zeroes_cnt
      let m_x := urem_int m_x m_y
      rem_internal_loop fuel exp_diff sides_zeroes_cnt m_x m_y
    else (exp_diff, m_x)

/--
Julia source: base/float.jl:524-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem_internal(x::T, y::T) where {T<:IEEEFloat}
    @_terminates_locally_meta
    xuint = reinterpret(Unsigned, x)
    yuint = reinterpret(Unsigned, y)
    if xuint <= yuint
        if xuint < yuint
            return x
        end
        return zero(T)
    end

    e_x = unbiased_exponent(x)
    e_y = unbiased_exponent(y)
    # Most common case where |y| is "very normal" and |x/y| < 2^EXPONENT_WIDTH
    if e_y > (significand_bits(T)) && (e_x - e_y) <= (exponent_bits(T))
        m_x = explicit_mantissa_noinfnan(x)
        m_y = explicit_mantissa_noinfnan(y)
        d = urem_int((m_x << (e_x - e_y)),  m_y)
        iszero(d) && return zero(T)
        return _to_float(d, e_y - uinttype(T)(1))
    end
    # Both are subnormals
    if e_x == 0 && e_y == 0
        return reinterpret(T, urem_int(xuint, yuint) & significand_mask(T))
    end

    m_x = explicit_mantissa_noinfnan(x)
    e_x -= uinttype(T)(1)
    m_y = explicit_mantissa_noinfnan(y)
    lz_m_y = uinttype(T)(exponent_bits(T))
    if e_y > 0
        e_y -= uinttype(T)(1)
    else
        m_y = mantissa(y)
        lz_m_y = Core.Intrinsics.ctlz_int(m_y)
    end

    tz_m_y = Core.Intrinsics.cttz_int(m_y)
    sides_zeroes_cnt = lz_m_y + tz_m_y

    # n>0
    exp_diff = e_x - e_y
    # Shift hy right until the end or n = 0
    right_shift = min(exp_diff, tz_m_y)
    m_y >>= right_shift
    exp_diff -= right_shift
    e_y += right_shift
    # Shift hx left until the end or n = 0
    left_shift = min(exp_diff, uinttype(T)(exponent_bits(T)))
    m_x <<= left_shift
    exp_diff -= left_shift

    m_x = urem_int(m_x, m_y)
    iszero(m_x) && return zero(T)
    iszero(exp_diff) && return _to_float(m_x, e_y)

    while exp_diff > sides_zeroes_cnt
        exp_diff -= sides_zeroes_cnt
        m_x <<= sides_zeroes_cnt
        m_x = urem_int(m_x, m_y)
    end
    m_x <<= exp_diff
    m_x = urem_int(m_x, m_y)
    return _to_float(m_x, e_y)
end

```
-/
def rem_internal {T : FTy} (x y : FV T) : FV T :=
  let xuint := reinterpret_Unsigned x
  let yuint := reinterpret_Unsigned y
  if int.le_BitUnsigned xuint yuint then
    if int.lt_BitUnsigned xuint yuint then x else zero_float T
  else
    let e_x := unbiased_exponent x
    let e_y := unbiased_exponent y
    if int.lt (significand_bits T) e_y && int.le (int.sub e_x e_y) (exponent_bits T) then
      let m_x := explicit_mantissa_noinfnan x
      let m_y := explicit_mantissa_noinfnan y
      let d := urem_int (int.shl_BitInteger_BitUnsigned m_x (int.sub e_x e_y)) m_y
      if int.eq d (int.lit T.uintTy 0) then zero_float T
      else _to_float d (int.sub e_y (int.lit T.uintTy 1))
    else if int.eq e_x (int.lit .i64 0) && int.eq e_y (int.lit .i64 0) then
      reinterpret_Float_Int T (int.band (urem_int xuint yuint) (significand_mask T))
    else
      let m_x := explicit_mantissa_noinfnan x
      let e_x := int.sub e_x (int.lit T.uintTy 1)
      let (e_y, m_y, lz_m_y) :=
        if int.lt (int.lit .i64 0) e_y then
          (int.sub e_y (int.lit T.uintTy 1), explicit_mantissa_noinfnan y, int.remT T.uintTy (exponent_bits T))
        else
          let m_y := mantissa y
          (e_y, m_y, int.ctlz_int m_y)
      let tz_m_y := int.cttz_int m_y
      let sides_zeroes_cnt := int.add lz_m_y tz_m_y
      let exp_diff := int.sub e_x e_y
      let right_shift := int.ifelse (int.lt_BitUnsigned tz_m_y exp_diff) tz_m_y exp_diff
      let m_y := int.shr_BitUnsigned_BitUnsigned m_y right_shift
      let exp_diff := int.sub exp_diff right_shift
      let e_y := int.add e_y right_shift
      let eb_u := int.remT T.uintTy (exponent_bits T)
      let left_shift := int.ifelse (int.lt_BitUnsigned eb_u exp_diff) eb_u exp_diff
      let m_x := int.shl_BitInteger_BitUnsigned m_x left_shift
      let exp_diff := int.sub exp_diff left_shift
      let m_x := urem_int m_x m_y
      if int.eq m_x (int.lit T.uintTy 0) then zero_float T
      else if int.eq exp_diff (int.lit T.uintTy 0) then _to_float m_x e_y
      else
        let (exp_diff, m_x) := rem_internal_loop exp_diff.val.toNat exp_diff sides_zeroes_cnt m_x m_y
        let m_x := int.shl_BitInteger_BitUnsigned m_x exp_diff
        let m_x := urem_int m_x m_y
        _to_float m_x e_y

/--
Julia source: base/float.jl:590-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem(x::T, y::T) where {T<:IEEEFloat}
    if isfinite(x) && !iszero(x) && isfinite(y) && !iszero(y)
        return copysign(rem_internal(abs(x), abs(y)), x)
    elseif isinf(x) || isnan(y) || iszero(y)  # y can still be Inf
        return T(NaN)
    else
        return x
    end
end

```
-/
def rem_IEEEFloat {T : FTy} (x y : FV T) : FV T :=
  if isfinite_callee x && !(iszero_float x) && isfinite_callee y && !(iszero_float y) then
    copysign_float (rem_internal (abs_float x) (abs_float y)) x
  else if isinf_callee x || isnan_callee y || iszero_float y then
    nan_float T
  else
    x

/--
Julia source: base/float.jl:600-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mod(x::T, y::T) where T<:AbstractFloat
    if isinf(y) && isfinite(x)
        return x
    end
    r = rem(x,y)
    if r == 0
        copysign(r,y)
    elseif (r > 0) ⊻ (y > 0)
        r+y
    else
        r
    end
end

```
-/
def mod_generic {T : Type} (isinf isfinite : T → Bool) (rem : T → T → T)
    (eqZero : T → Bool) (copysign : T → T → T) (gtZero : T → Bool)
    (add : T → T → T) (x y : T) : T :=
  if isinf y && isfinite x then
    x
  else
    let r := rem x y
    if eqZero r then
      copysign r y
    else if xor (gtZero r) (gtZero y) then
      add r y
    else
      r
def mod_AbstractFloat {T : FTy} (x y : FV T) : FV T :=
  mod_generic isinf_callee isfinite_callee rem_IEEEFloat
    (fun r => eq_float r (zero_float T)) copysign_float
    (fun z => lt_float (zero_float T) z) add_float x y

/--
Julia source: base/float.jl:614-615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## floating point comparisons ##
==(x::T, y::T) where {T<:IEEEFloat} = eq_float(x, y)
```
-/
def eq_IEEEFloat {T : FTy} (x y : FV T) : Bool := eq_float x y

/--
Julia source: base/float.jl:616-616 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( x::T, y::T) where {T<:IEEEFloat} = lt_float(x, y)
```
-/
def lt_IEEEFloat {T : FTy} (x y : FV T) : Bool := lt_float x y

/--
Julia source: base/float.jl:617-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::T, y::T) where {T<:IEEEFloat} = le_float(x, y)

```
-/
def le_IEEEFloat {T : FTy} (x y : FV T) : Bool := le_float x y

/--
Julia source: base/float.jl:619-620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(x::T, y::T) where {T<:IEEEFloat} = fpiseq(x, y)

```
-/
def isequal_IEEEFloat {T : FTy} (x y : FV T) : Bool := fpiseq x y

/--
Julia source: base/float.jl:621-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# interpret as sign-magnitude integer
function _fpint(x)
    @inline
    IntT = inttype(typeof(x))
    ix = reinterpret(IntT, x)
    return ifelse(ix < zero(IntT), ix ⊻ typemax(IntT), ix)
end

```
-/
def _fpint {T : FTy} (x : FV T) : JInt T.intTy :=
  let ix := reinterpret_Signed x
  int.ifelse (int.lt_BitSigned ix (int.zero ix)) (int.bxor ix (int.typemax T.intTy)) ix

/--
Julia source: base/float.jl:629-635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isless(a::T, b::T) where T<:IEEEFloat
    @inline
    (isnan(a) || isnan(b)) && return !isnan(a)

    return _fpint(a) < _fpint(b)
end

```
-/
def isless_IEEEFloat {T : FTy} (a b : FV T) : Bool :=
  if isnan_callee a || isnan_callee b then !(isnan_callee a)
  else int.lt_BitSigned (_fpint a) (_fpint b)

/--
Julia source: base/float.jl:636-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Exact Float (Tf) vs Integer (Ti) comparisons
# Assumes:
# - typemax(Ti) == 2^n-1
# - typemax(Ti) can't be exactly represented by Tf:
#   => Tf(typemax(Ti)) == 2^n or Inf
# - typemin(Ti) can be exactly represented by Tf
#
# 1. convert y::Ti to float fy::Tf
# 2. perform Tf comparison x vs fy
# 3. if x == fy, check if (1) resulted in rounding:
#  a. convert fy back to Ti and compare with original y
#  b. unsafe_convert undefined behaviour if fy == Tf(typemax(Ti))
#     (but consequently x == fy > y)
for Ti in (Int64,UInt64,Int128,UInt128)
    for Tf in (Float32,Float64)
        @eval begin
            function ==(x::$Tf, y::$Ti)
                fy = ($Tf)(y)
                (x == fy) & (fy != $(Tf(typemax(Ti)))) & (y == unsafe_trunc($Ti,fy))
            end
```
-/
def eq_Tf_Ti_exact {Tf : FTy} {Ti : IntTy} (x : FV Tf) (y : JInt Ti) : Bool :=
  let fy := floatOfInt Tf y
  Bool.and (Bool.and (eq_IEEEFloat x fy) (!(eq_IEEEFloat fy (floatOfInt Tf (int.typemax Ti)))))
    (int.eq y (unsafe_trunc Ti fy))

/--
Julia source: base/float.jl:656-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            ==(y::$Ti, x::$Tf) = x==y

```
-/
def eq_Ti_Tf_exact {Tf : FTy} {Ti : IntTy} (y : JInt Ti) (x : FV Tf) : Bool :=
  eq_Tf_Ti_exact x y

/--
Julia source: base/float.jl:658-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            function <(x::$Ti, y::$Tf)
                fx = ($Tf)(x)
                (fx < y) | ((fx == y) & ((fx == $(Tf(typemax(Ti)))) | (x < unsafe_trunc($Ti,fx)) ))
            end
```
-/
def lt_Ti_Tf_exact {Tf : FTy} {Ti : IntTy} (x : JInt Ti) (y : FV Tf) : Bool :=
  let fx := floatOfInt Tf x
  Bool.or (lt_IEEEFloat fx y) (Bool.and (eq_IEEEFloat fx y)
    (Bool.or (eq_IEEEFloat fx (floatOfInt Tf (int.typemax Ti))) (int.lt x (unsafe_trunc Ti fx))))

/--
Julia source: base/float.jl:662-666 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            function <=(x::$Ti, y::$Tf)
                fx = ($Tf)(x)
                (fx < y) | ((fx == y) & ((fx == $(Tf(typemax(Ti)))) | (x <= unsafe_trunc($Ti,fx)) ))
            end

```
-/
def le_Ti_Tf_exact {Tf : FTy} {Ti : IntTy} (x : JInt Ti) (y : FV Tf) : Bool :=
  let fx := floatOfInt Tf x
  Bool.or (lt_IEEEFloat fx y) (Bool.and (eq_IEEEFloat fx y)
    (Bool.or (eq_IEEEFloat fx (floatOfInt Tf (int.typemax Ti))) (int.le x (unsafe_trunc Ti fx))))

/--
Julia source: base/float.jl:667-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            function <(x::$Tf, y::$Ti)
                fy = ($Tf)(y)
                (x < fy) | ((x == fy) & (fy < $(Tf(typemax(Ti)))) & (unsafe_trunc($Ti,fy) < y))
            end
```
-/
def lt_Tf_Ti_exact {Tf : FTy} {Ti : IntTy} (x : FV Tf) (y : JInt Ti) : Bool :=
  let fy := floatOfInt Tf y
  Bool.or (lt_IEEEFloat x fy) (Bool.and (Bool.and (eq_IEEEFloat x fy)
    (lt_IEEEFloat fy (floatOfInt Tf (int.typemax Ti)))) (int.lt (unsafe_trunc Ti fy) y))

/--
Julia source: base/float.jl:671-677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            function <=(x::$Tf, y::$Ti)
                fy = ($Tf)(y)
                (x < fy) | ((x == fy) & (fy < $(Tf(typemax(Ti)))) & (unsafe_trunc($Ti,fy) <= y))
            end
        end
    end
end
```
-/
def le_Tf_Ti_exact {Tf : FTy} {Ti : IntTy} (x : FV Tf) (y : JInt Ti) : Bool :=
  let fy := floatOfInt Tf y
  Bool.or (lt_IEEEFloat x fy) (Bool.and (Bool.and (eq_IEEEFloat x fy)
    (lt_IEEEFloat fy (floatOfInt Tf (int.typemax Ti)))) (int.le (unsafe_trunc Ti fy) y))

/--
Julia source: base/float.jl:678-680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for op in (:(==), :<, :<=)
    @eval begin
        ($op)(x::Float16, y::Union{Int128,UInt128,Int64,UInt64}) = ($op)(Float64(x), Float64(y))
```
-/
def op_Float16_WideInt {Ti : IntTy} (op : FV .f64 → FV .f64 → Bool) (x : FV .f16) (y : JInt Ti) : Bool :=
  op (Float64_Float16 x) (floatOfInt .f64 y)

/--
Julia source: base/float.jl:681-682 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($op)(x::Union{Int128,UInt128,Int64,UInt64}, y::Float16) = ($op)(Float64(x), Float64(y))

```
-/
def op_WideInt_Float16 {Ti : IntTy} (op : FV .f64 → FV .f64 → Bool) (x : JInt Ti) (y : FV .f16) : Bool :=
  op (floatOfInt .f64 x) (Float64_Float16 y)

/--
Julia source: base/float.jl:683-683 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($op)(x::Union{Float16,Float32}, y::Union{Int32,UInt32}) = ($op)(Float64(x), Float64(y))
```
-/
def op_SmallFloat_Int32 {Tf : FTy} {Ti : IntTy} (op : FV .f64 → FV .f64 → Bool) (x : FV Tf) (y : JInt Ti) : Bool :=
  op (convertFloat .f64 x) (floatOfInt .f64 y)

/--
Julia source: base/float.jl:684-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($op)(x::Union{Int32,UInt32}, y::Union{Float16,Float32}) = ($op)(Float64(x), Float64(y))

```
-/
def op_Int32_SmallFloat {Tf : FTy} {Ti : IntTy} (op : FV .f64 → FV .f64 → Bool) (x : JInt Ti) (y : FV Tf) : Bool :=
  op (floatOfInt .f64 x) (convertFloat .f64 y)

/--
Julia source: base/float.jl:686-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($op)(x::Float16, y::Union{Int16,UInt16}) = ($op)(Float32(x), Float32(y))
```
-/
def op_Float16_Int16 {Ti : IntTy} (op : FV .f32 → FV .f32 → Bool) (x : FV .f16) (y : JInt Ti) : Bool :=
  op (Float32_Float16 x) (floatOfInt .f32 y)

/--
Julia source: base/float.jl:687-691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($op)(x::Union{Int16,UInt16}, y::Float16) = ($op)(Float32(x), Float32(y))
    end
end


```
-/
def op_Int16_Float16 {Ti : IntTy} (op : FV .f32 → FV .f32 → Bool) (x : JInt Ti) (y : FV .f16) : Bool :=
  op (floatOfInt .f32 x) (Float32_Float16 y)

/-- *dispatch*: `x == y` for `x::Tf` and `y::Ti` (including the `promotion.jl:516` fallback for 8-bit `Ti`). -/
def eq_FI : {Tf : FTy} → {Ti : IntTy} → FV Tf → JInt Ti → Bool
  | .f32, .i64, x, y | .f32, .u64, x, y | .f32, .i128, x, y | .f32, .u128, x, y => eq_Tf_Ti_exact x y
  | .f64, .i64, x, y | .f64, .u64, x, y | .f64, .i128, x, y | .f64, .u128, x, y => eq_Tf_Ti_exact x y
  | .f16, .i64, x, y | .f16, .u64, x, y | .f16, .i128, x, y | .f16, .u128, x, y => op_Float16_WideInt eq_IEEEFloat x y
  | .f16, .i32, x, y | .f16, .u32, x, y | .f32, .i32, x, y | .f32, .u32, x, y => op_SmallFloat_Int32 eq_IEEEFloat x y
  | .f16, .i16, x, y | .f16, .u16, x, y => op_Float16_Int16 eq_IEEEFloat x y
  | T, _, x, y => eq_IEEEFloat x (floatOfInt T y)

/-- *dispatch*: `x < y` for `x::Tf` and `y::Ti`. -/
def lt_FI : {Tf : FTy} → {Ti : IntTy} → FV Tf → JInt Ti → Bool
  | .f32, .i64, x, y | .f32, .u64, x, y | .f32, .i128, x, y | .f32, .u128, x, y => lt_Tf_Ti_exact x y
  | .f64, .i64, x, y | .f64, .u64, x, y | .f64, .i128, x, y | .f64, .u128, x, y => lt_Tf_Ti_exact x y
  | .f16, .i64, x, y | .f16, .u64, x, y | .f16, .i128, x, y | .f16, .u128, x, y => op_Float16_WideInt lt_IEEEFloat x y
  | .f16, .i32, x, y | .f16, .u32, x, y | .f32, .i32, x, y | .f32, .u32, x, y => op_SmallFloat_Int32 lt_IEEEFloat x y
  | .f16, .i16, x, y | .f16, .u16, x, y => op_Float16_Int16 lt_IEEEFloat x y
  | T, _, x, y => lt_IEEEFloat x (floatOfInt T y)

/-- *dispatch*: `x <= y` for `x::Tf` and `y::Ti`. -/
def le_FI : {Tf : FTy} → {Ti : IntTy} → FV Tf → JInt Ti → Bool
  | .f32, .i64, x, y | .f32, .u64, x, y | .f32, .i128, x, y | .f32, .u128, x, y => le_Tf_Ti_exact x y
  | .f64, .i64, x, y | .f64, .u64, x, y | .f64, .i128, x, y | .f64, .u128, x, y => le_Tf_Ti_exact x y
  | .f16, .i64, x, y | .f16, .u64, x, y | .f16, .i128, x, y | .f16, .u128, x, y => op_Float16_WideInt le_IEEEFloat x y
  | .f16, .i32, x, y | .f16, .u32, x, y | .f32, .i32, x, y | .f32, .u32, x, y => op_SmallFloat_Int32 le_IEEEFloat x y
  | .f16, .i16, x, y | .f16, .u16, x, y => op_Float16_Int16 le_IEEEFloat x y
  | T, _, x, y => le_IEEEFloat x (floatOfInt T y)

/-- *dispatch*: `x == y` for `x::Ti` and `y::Tf`. -/
def eq_IF : {Tf : FTy} → {Ti : IntTy} → JInt Ti → FV Tf → Bool
  | .f32, .i64, x, y | .f32, .u64, x, y | .f32, .i128, x, y | .f32, .u128, x, y => eq_Ti_Tf_exact x y
  | .f64, .i64, x, y | .f64, .u64, x, y | .f64, .i128, x, y | .f64, .u128, x, y => eq_Ti_Tf_exact x y
  | .f16, .i64, x, y | .f16, .u64, x, y | .f16, .i128, x, y | .f16, .u128, x, y => op_WideInt_Float16 eq_IEEEFloat x y
  | .f16, .i32, x, y | .f16, .u32, x, y | .f32, .i32, x, y | .f32, .u32, x, y => op_Int32_SmallFloat eq_IEEEFloat x y
  | .f16, .i16, x, y | .f16, .u16, x, y => op_Int16_Float16 eq_IEEEFloat x y
  | T, _, x, y => eq_IEEEFloat (floatOfInt T x) y

/-- *dispatch*: `x < y` for `x::Ti` and `y::Tf`. -/
def lt_IF : {Tf : FTy} → {Ti : IntTy} → JInt Ti → FV Tf → Bool
  | .f32, .i64, x, y | .f32, .u64, x, y | .f32, .i128, x, y | .f32, .u128, x, y => lt_Ti_Tf_exact x y
  | .f64, .i64, x, y | .f64, .u64, x, y | .f64, .i128, x, y | .f64, .u128, x, y => lt_Ti_Tf_exact x y
  | .f16, .i64, x, y | .f16, .u64, x, y | .f16, .i128, x, y | .f16, .u128, x, y => op_WideInt_Float16 lt_IEEEFloat x y
  | .f16, .i32, x, y | .f16, .u32, x, y | .f32, .i32, x, y | .f32, .u32, x, y => op_Int32_SmallFloat lt_IEEEFloat x y
  | .f16, .i16, x, y | .f16, .u16, x, y => op_Int16_Float16 lt_IEEEFloat x y
  | T, _, x, y => lt_IEEEFloat (floatOfInt T x) y

/-- *dispatch*: `x <= y` for `x::Ti` and `y::Tf`. -/
def le_IF : {Tf : FTy} → {Ti : IntTy} → JInt Ti → FV Tf → Bool
  | .f32, .i64, x, y | .f32, .u64, x, y | .f32, .i128, x, y | .f32, .u128, x, y => le_Ti_Tf_exact x y
  | .f64, .i64, x, y | .f64, .u64, x, y | .f64, .i128, x, y | .f64, .u128, x, y => le_Ti_Tf_exact x y
  | .f16, .i64, x, y | .f16, .u64, x, y | .f16, .i128, x, y | .f16, .u128, x, y => op_WideInt_Float16 le_IEEEFloat x y
  | .f16, .i32, x, y | .f16, .u32, x, y | .f32, .i32, x, y | .f32, .u32, x, y => op_Int32_SmallFloat le_IEEEFloat x y
  | .f16, .i16, x, y | .f16, .u16, x, y => op_Int16_Float16 le_IEEEFloat x y
  | T, _, x, y => le_IEEEFloat (floatOfInt T x) y

/--
Julia source: base/float.jl:692-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs(x::IEEEFloat) = abs_float(x)

```
-/
def abs_IEEEFloat {T : FTy} (x : FV T) : FV T := abs_float x

/--
Julia source: base/float.jl:694-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    isnan(f)::Bool

Test whether a number value is a NaN, an indeterminate value which is neither an infinity
nor a finite number ("not a number").

See also: [`iszero`](@ref), [`isone`](@ref), [`isinf`](@ref), [`ismissing`](@ref).
"""
isnan(x::AbstractFloat) = (x != x)::Bool
```
-/
def isnan_AbstractFloat {α : Type} (ne : α → α → Bool) (x : α) : Bool := ne x x
def isnan_IEEEFloat {T : FTy} (x : FV T) : Bool := isnan_AbstractFloat (fun a b => !(eq_IEEEFloat a b)) x

/--
Julia source: base/float.jl:703-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isnan(x::Number) = false

```
-/
def isnan_Number {α : Type} (_x : α) : Bool := false

/--
Julia source: base/float.jl:705-705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfinite(x::AbstractFloat) = !(isnan(x - x)::Bool)
```
-/
def isfinite_AbstractFloat {α : Type} (sub : α → α → α) (isnan : α → Bool) (x : α) : Bool :=
  !(isnan (sub x x))
def isfinite_IEEEFloat {T : FTy} (x : FV T) : Bool :=
  isfinite_AbstractFloat sub_IEEEFloat isnan_IEEEFloat x

/--
Julia source: base/float.jl:706-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfinite(x::Real) = decompose(x)[3] != 0
```
-/
def isfinite_Real {R N E : Type} (decompose : R → N × E × JInt .i64) (x : R) : Bool :=
  !(int.eq (decompose x).2.2 (int.lit .i64 0))

/--
Julia source: base/float.jl:707-708 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfinite(x::Integer) = true

```
-/
def isfinite_Integer {α : Type} (_x : α) : Bool := true

/--
Julia source: base/float.jl:709-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    isinf(f)::Bool

Test whether a number is infinite.

See also: [`Inf`](@ref), [`iszero`](@ref), [`isfinite`](@ref), [`isnan`](@ref).
"""
isinf(x::Real) = !isnan(x) & !isfinite(x)
```
-/
def isinf_Real {R : Type} (isnan isfinite : R → Bool) (x : R) : Bool :=
  Bool.and (!(isnan x)) (!(isfinite x))

/--
Julia source: base/float.jl:717-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isinf(x::IEEEFloat) = abs(x) === oftype(x, Inf)

```
-/
def isinf_IEEEFloat {T : FTy} (x : FV T) : Bool :=
  egal_float (abs_IEEEFloat x) (oftype_float x (inf_float T))

/--
Julia source: base/float.jl:719-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.decompose(x::Real) -> (num::Integer, pow::Integer, den::Integer)

Return three integer values `num, pow, den`, such that the value of `x` is
mathematically equal to

    num*2^pow/den

The decompose function is the point where rational-valued `Real` subtypes that support
hashing hook into the hashing protocol. It also provides the generic definitions of
[`isfinite`](@ref) and [`isinf`](@ref) for `Real` subtypes, and it is used to compare
`AbstractFloat` values against [`Rational`](@ref) values.

The decomposition need not be canonical in the sense that it just needs to be *some*
way to express `x` in this form, not any particular way – with the restriction that
`num` and `den` may not share any odd common factors. They may, however, have powers
of two in common – the generic hashing code will normalize those as necessary.

Special values:

 - `x` is zero: `num` should be zero and `den` should have the same sign as `x`
 - `x` is infinite: `den` should be zero and `num` should have the same sign as `x`
 - `x` is not a number: `num` and `den` should both be zero

See also [`hash`](@ref).
"""
decompose(x::Integer) = x, 0, 1

```
-/
def decompose_Integer {I : Type} (x : I) : I × JInt .i64 × JInt .i64 :=
  (x, int.lit .i64 0, int.lit .i64 1)

/--
Julia source: base/float.jl:747-757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function decompose(x::Float16)::NTuple{3,Int}
    isnan(x) && return 0, 0, 0
    isinf(x) && return ifelse(x < 0, -1, 1), 0, 0
    n = reinterpret(UInt16, x)
    s = (n & 0x03ff) % Int16
    e = ((n & 0x7c00) >> 10) % Int
    s |= Int16(e != 0) << 10
    d = ifelse(signbit(x), -1, 1)
    s%Int, e - 25 + (e == 0), d
end

```
-/
def decompose_Float16 (x : FV .f16) : JInt .i64 × JInt .i64 × JInt .i64 :=
  if isnan_IEEEFloat x then (int.lit .i64 0, int.lit .i64 0, int.lit .i64 0)
  else if isinf_IEEEFloat x then
    (int.ifelse (lt_FI x (int.lit .i64 0)) (int.lit .i64 (-1)) (int.lit .i64 1), int.lit .i64 0, int.lit .i64 0)
  else
    let n := reinterpret_Unsigned_Float16 x
    let s := int.remT .i16 (int.band n (int.lit .u16 0x03ff))
    let e := int.remT .i64 (int.shr_Int (int.band n (int.lit .u16 0x7c00)) (int.lit .i64 10))
    let s := int.bor s (int.shl_Int (int.ofBool .i16 (!(int.eq e (int.lit .i64 0)))) (int.lit .i64 10))
    let d := int.ifelse (signbit_float x) (int.lit .i64 (-1)) (int.lit .i64 1)
    (int.remT .i64 s, int.add (int.sub e (int.lit .i64 25)) (int.ofBool .i64 (int.eq e (int.lit .i64 0))), d)

/--
Julia source: base/float.jl:758-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function decompose(x::Float32)::NTuple{3,Int}
    isnan(x) && return 0, 0, 0
    isinf(x) && return ifelse(x < 0, -1, 1), 0, 0
    n = reinterpret(UInt32, x)
    s = (n & 0x007fffff) % Int32
    e = ((n & 0x7f800000) >> 23) % Int
    s |= Int32(e != 0) << 23
    d = ifelse(signbit(x), -1, 1)
    s%Int, e - 150 + (e == 0), d
end

```
-/
def decompose_Float32 (x : FV .f32) : JInt .i64 × JInt .i64 × JInt .i64 :=
  if isnan_IEEEFloat x then (int.lit .i64 0, int.lit .i64 0, int.lit .i64 0)
  else if isinf_IEEEFloat x then
    (int.ifelse (lt_FI x (int.lit .i64 0)) (int.lit .i64 (-1)) (int.lit .i64 1), int.lit .i64 0, int.lit .i64 0)
  else
    let n := reinterpret_Unsigned_Float32 x
    let s := int.remT .i32 (int.band n (int.lit .u32 0x007fffff))
    let e := int.remT .i64 (int.shr_Int (int.band n (int.lit .u32 0x7f800000)) (int.lit .i64 23))
    let s := int.bor s (int.shl_Int (int.ofBool .i32 (!(int.eq e (int.lit .i64 0)))) (int.lit .i64 23))
    let d := int.ifelse (signbit_float x) (int.lit .i64 (-1)) (int.lit .i64 1)
    (int.remT .i64 s, int.add (int.sub e (int.lit .i64 150)) (int.ofBool .i64 (int.eq e (int.lit .i64 0))), d)

/--
Julia source: base/float.jl:769-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function decompose(x::Float64)::Tuple{Int64, Int, Int}
    isnan(x) && return 0, 0, 0
    isinf(x) && return ifelse(x < 0, -1, 1), 0, 0
    n = reinterpret(UInt64, x)
    s = (n & 0x000fffffffffffff) % Int64
    e = ((n & 0x7ff0000000000000) >> 52) % Int
    s |= Int64(e != 0) << 52
    d = ifelse(signbit(x), -1, 1)
    s, e - 1075 + (e == 0), d
end


```
-/
def decompose_Float64 (x : FV .f64) : JInt .i64 × JInt .i64 × JInt .i64 :=
  if isnan_IEEEFloat x then (int.lit .i64 0, int.lit .i64 0, int.lit .i64 0)
  else if isinf_IEEEFloat x then
    (int.ifelse (lt_FI x (int.lit .i64 0)) (int.lit .i64 (-1)) (int.lit .i64 1), int.lit .i64 0, int.lit .i64 0)
  else
    let n := reinterpret_Unsigned_Float64 x
    let s := int.remT .i64 (int.band n (int.lit .u64 0x000fffffffffffff))
    let e := int.remT .i64 (int.shr_Int (int.band n (int.lit .u64 0x7ff0000000000000)) (int.lit .i64 52))
    let s := int.bor s (int.shl_Int (int.ofBool .i64 (!(int.eq e (int.lit .i64 0)))) (int.lit .i64 52))
    let d := int.ifelse (signbit_float x) (int.lit .i64 (-1)) (int.lit .i64 1)
    (s, int.add (int.sub e (int.lit .i64 1075)) (int.ofBool .i64 (int.eq e (int.lit .i64 0))), d)

/-- *dispatch*: `decompose(x)` for an `IEEEFloat`. -/
def decompose : {T : FTy} → FV T → JInt .i64 × JInt .i64 × JInt .i64
  | .f16, x => decompose_Float16 x
  | .f32, x => decompose_Float32 x
  | .f64, x => decompose_Float64 x

/--
Julia source: base/float.jl:781-797 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    precision(num::AbstractFloat; base::Integer=2)
    precision(T::Type; base::Integer=2)

Get the precision of a floating point number, as defined by the effective number of bits in
the significand, or the precision of a floating-point type `T` (its current default, if
`T` is a variable-precision type like [`BigFloat`](@ref)).

If `base` is specified, then it returns the maximum corresponding
number of significand digits in that base.

!!! compat "Julia 1.8"
    The `base` keyword requires at least Julia 1.8.
"""
function precision end

_precision_with_base_2(::Type{Float16}) = 11
```
-/
def _precision_with_base_2_Float16 : JInt .i64 := int.lit .i64 11

/--
Julia source: base/float.jl:798-798 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_precision_with_base_2(::Type{Float32}) = 24
```
-/
def _precision_with_base_2_Float32 : JInt .i64 := int.lit .i64 24

/--
Julia source: base/float.jl:799-799 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_precision_with_base_2(::Type{Float64}) = 53
```
-/
def _precision_with_base_2_Float64 : JInt .i64 := int.lit .i64 53

/-- *dispatch*: `_precision_with_base_2(T)` for an `IEEEFloat` type `T`. -/
def _precision_with_base_2 : FTy → JInt .i64
  | .f16 => _precision_with_base_2_Float16
  | .f32 => _precision_with_base_2_Float32
  | .f64 => _precision_with_base_2_Float64

/--
Julia source: base/float.jl:800-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _precision(x, base::Integer)
    base > 1 || throw(DomainError(base, "`base` cannot be less than 2."))
    p = _precision_with_base_2(x)
    return base == 2 ? Int(p) : floor(Int, p / log2(base))
end
```
-/
def _precision {α : Type} {t : IntTy} (_precision_with_base_2 : α → JInt .i64)
    (floor_div_log2 : JInt .i64 → JInt t → Jl (JInt .i64)) (x : α) (base : JInt t) : Jl (JInt .i64) :=
  if !(int.lt (int.lit .i64 1) base) then
    .error (.domainError "`base` cannot be less than 2.")
  else
    let p := _precision_with_base_2 x
    if int.eq base (int.lit .i64 2) then .ok p else floor_div_log2 p base

/--
Julia source: base/float.jl:805-805 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
precision(::Type{T}; base::Integer=2) where {T<:AbstractFloat} = _precision(T, base)
```
-/
def precision_Type {α : Type} {t : IntTy} (_precision_with_base_2 : α → JInt .i64)
    (floor_div_log2 : JInt .i64 → JInt t → Jl (JInt .i64)) (T : α) (base : JInt t) : Jl (JInt .i64) :=
  _precision _precision_with_base_2 floor_div_log2 T base
def precision_Type_default (T : FTy) : JInt .i64 :=
  _precision_with_base_2 T

/--
Julia source: base/float.jl:806-806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
precision(::T; base::Integer=2) where {T<:AbstractFloat} = precision(T; base)
```
-/
def precision_AbstractFloat {F T B R : Type} (typeof : F → T)
    (precision_Type : T → B → R) (x : F) (base : B) : R :=
  precision_Type (typeof x) base
def precision_AbstractFloat_default {F T R : Type} (typeof : F → T)
    (precision_Type_default : T → R) (x : F) : R :=
  precision_Type_default (typeof x)
def precision_val {T : FTy} {t : IntTy} (floor_div_log2 : JInt .i64 → JInt t → Jl (JInt .i64))
    (x : FV T) (base : JInt t) : Jl (JInt .i64) :=
  precision_AbstractFloat (fun _ => T) (precision_Type _precision_with_base_2 floor_div_log2) x base
def precision_val_default {T : FTy} (x : FV T) : JInt .i64 :=
  precision_AbstractFloat_default (fun _ => T) precision_Type_default x

/--
Julia source: base/float.jl:807-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
precision(::Type{Union{}}, slurp...; kwargs...) = throw(MethodError(precision, (Union{}, slurp...)))


```
-/
def precision_Union {α : Type} : Jl α := .error (.methodError "precision")

/--
Julia source: base/float.jl:810-846 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _nextfloat(f::IEEEFloat, dneg::Bool, da::Integer)
    # da must be > 0
    F = typeof(f)
    fumax = reinterpret(Unsigned, F(Inf))
    U = typeof(fumax)

    isnan(f) && return f
    fi = reinterpret(Signed, f)
    fneg = fi < 0
    fu = unsigned(fi & typemax(fi))

    if da > typemax(U)
        fneg = dneg
        fu = fumax
    else
        du = da % U
        if fneg ⊻ dneg
            if du > fu
                fu = min(fumax, du - fu)
                fneg = !fneg
            else
                fu = fu - du
            end
        else
            if fumax - fu < du
                fu = fumax
            else
                fu = fu + du
            end
        end
    end
    if fneg
        fu |= sign_mask(F)
    end
    reinterpret(F, fu)
end

```
-/
def _nextfloat_generic {F : FTy} {I : Type} (gt_typemax : I → Bool)
    (rem_U : I → JInt F.uintTy) (f : FV F) (dneg : Bool) (da : I) : FV F :=
  let fumax := reinterpret_Unsigned (inf_float F)
  if isnan_IEEEFloat f then f
  else
    let fi := reinterpret_Signed f
    let fneg := int.lt fi (int.lit .i64 0)
    let fu := int.remT F.uintTy (int.unsigned (int.band fi (int.typemax F.intTy)))
    let (fneg, fu) :=
      if gt_typemax da then
        (dneg, fumax)
      else
        let du := rem_U da
        if xor fneg dneg then
          if int.lt_BitUnsigned fu du then
            let diff := int.sub du fu
            let fu := int.ifelse (int.lt_BitUnsigned diff fumax) diff fumax
            (!fneg, fu)
          else
            (fneg, int.sub fu du)
        else
          if int.lt_BitUnsigned (int.sub fumax fu) du then
            (fneg, fumax)
          else
            (fneg, int.add fu du)
    let fu := if fneg then int.bor fu (sign_mask F) else fu
    reinterpret_Float_Int F fu
def _nextfloat {F : FTy} {t : IntTy} (f : FV F) (dneg : Bool) (da : JInt t) : FV F :=
  let fumax := reinterpret_Unsigned (inf_float F)
  if isnan_IEEEFloat f then f
  else
    let fi := reinterpret_Signed f
    let fneg := int.lt fi (int.lit .i64 0)
    let fu := int.remT F.uintTy (int.unsigned (int.band fi (int.typemax F.intTy)))
    let (fneg, fu) :=
      if int.lt (int.typemax F.uintTy) da then
        (dneg, fumax)
      else
        let du := int.remT F.uintTy da
        if xor fneg dneg then
          if int.lt_BitUnsigned fu du then
            let diff := int.sub du fu
            let fu := int.ifelse (int.lt_BitUnsigned diff fumax) diff fumax
            (!fneg, fu)
          else
            (fneg, int.sub fu du)
        else
          if int.lt_BitUnsigned (int.sub fumax fu) du then
            (fneg, fumax)
          else
            (fneg, int.add fu du)
    let fu := if fneg then int.bor fu (sign_mask F) else fu
    reinterpret_Float_Int F fu

/--
Julia source: base/float.jl:847-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    nextfloat(x::AbstractFloat, n::Integer)

The result of `n` iterative applications of `nextfloat` to `x` if `n >= 0`, or `-n`
applications of [`prevfloat`](@ref) if `n < 0`.
"""
nextfloat(f::AbstractFloat, d::Integer) = _nextfloat(f, isnegative(d), uabs(d))

```
-/
def nextfloat_AbstractFloat {F I U : Type} (_nextfloat : F → Bool → U → F)
    (isnegative : I → Bool) (uabs : I → U) (f : F) (d : I) : F :=
  _nextfloat f (isnegative d) (uabs d)
def nextfloat_step {F : FTy} {t : IntTy} (f : FV F) (d : JInt t) : FV F :=
  nextfloat_AbstractFloat _nextfloat isnegative_int uabs f d

/--
Julia source: base/float.jl:855-864 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    nextfloat(x::AbstractFloat)

Return the smallest floating point number `y` of the same type as `x` such that `x < y`.
If no such `y` exists (e.g. if `x` is `Inf` or `NaN`), then return `x`.

See also: [`prevfloat`](@ref), [`eps`](@ref), [`issubnormal`](@ref).
"""
nextfloat(x::AbstractFloat) = nextfloat(x, 1)

```
-/
def nextfloat_AbstractFloat_one {F : Type} (nextfloat_step : F → JInt .i64 → F) (x : F) : F :=
  nextfloat_step x (int.lit .i64 1)
def nextfloat {F : FTy} (x : FV F) : FV F :=
  nextfloat_AbstractFloat_one nextfloat_step x

/--
Julia source: base/float.jl:865-872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    prevfloat(x::AbstractFloat, n::Integer)

The result of `n` iterative applications of `prevfloat` to `x` if `n >= 0`, or `-n`
applications of [`nextfloat`](@ref) if `n < 0`.
"""
prevfloat(x::AbstractFloat, d::Integer) = _nextfloat(x, ispositive(d), uabs(d))

```
-/
def prevfloat_AbstractFloat {F I U : Type} (_nextfloat : F → Bool → U → F)
    (ispositive : I → Bool) (uabs : I → U) (x : F) (d : I) : F :=
  _nextfloat x (ispositive d) (uabs d)
def prevfloat_step {F : FTy} {t : IntTy} (x : FV F) (d : JInt t) : FV F :=
  prevfloat_AbstractFloat _nextfloat ispositive_int uabs x d

/--
Julia source: base/float.jl:873-880 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    prevfloat(x::AbstractFloat)

Return the largest floating point number `y` of the same type as `x` such that `y < x`.
If no such `y` exists (e.g. if `x` is `-Inf` or `NaN`), then return `x`.
"""
prevfloat(x::AbstractFloat) = nextfloat(x, -1)

```
-/
def prevfloat_AbstractFloat_one {F : Type} (nextfloat_step : F → JInt .i64 → F) (x : F) : F :=
  nextfloat_step x (int.lit .i64 (-1))
def prevfloat {F : FTy} (x : FV F) : FV F :=
  prevfloat_AbstractFloat_one nextfloat_step x

/--
Julia source: base/float.jl:881-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for Ti in (Int8, Int16, Int32, Int64, Int128, UInt8, UInt16, UInt32, UInt64, UInt128)
    for Tf in (Float16, Float32, Float64)
        if Ti <: Unsigned || sizeof(Ti) < sizeof(Tf)
            # Here `Tf(typemin(Ti))-1` is exact, so we can compare the lower-bound
            # directly. `Tf(typemax(Ti))+1` is either always exactly representable, or
            # rounded to `Inf` (e.g. when `Ti==UInt128 && Tf==Float32`).
            @eval begin
                function round(::Type{$Ti},x::$Tf,::RoundingMode{:ToZero})
                    if $(Tf(typemin(Ti))-one(Tf)) < x < $(Tf(typemax(Ti))+one(Tf))
                        return unsafe_trunc($Ti,x)
                    else
                        throw(InexactError(:round, $Ti, x, RoundToZero))
                    end
                end
```
-/
def round_ToZero_small (Ti : IntTy) {Tf : FTy} (x : FV Tf) : Jl (JInt Ti) :=
  let lo := sub_IEEEFloat (floatOfInt Tf (int.typemin Ti)) (one_float Tf)
  let hi := add_IEEEFloat (floatOfInt Tf (int.typemax Ti)) (one_float Tf)
  if lt_IEEEFloat lo x && lt_IEEEFloat x hi then
    .ok (unsafe_trunc Ti x)
  else
    .error (.inexactError "round")

/--
Julia source: base/float.jl:895-905 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
                function (::Type{$Ti})(x::$Tf)
                    # When typemax(Ti) is not representable by Tf but typemax(Ti) + 1 is,
                    # then < Tf(typemax(Ti) + 1) is stricter than <= Tf(typemax(Ti)). Using
                    # the former causes us to throw on UInt64(Float64(typemax(UInt64))+1)
                    if ($(Tf(typemin(Ti))) <= x < $(Tf(typemax(Ti))+one(Tf))) && isinteger(x)
                        return unsafe_trunc($Ti,x)
                    else
                        throw(InexactError($(Expr(:quote,nameof(Ti))), $Ti, x))
                    end
                end
            end
```
-/
def intOfFloat_small (Ti : IntTy) {Tf : FTy} (x : FV Tf) : Jl (JInt Ti) :=
  let lo := floatOfInt Tf (int.typemin Ti)
  let hi := add_IEEEFloat (floatOfInt Tf (int.typemax Ti)) (one_float Tf)
  if (le_IEEEFloat lo x && lt_IEEEFloat x hi) && isinteger_callee x then
    .ok (unsafe_trunc Ti x)
  else
    .error (.inexactError Ti.name)

/--
Julia source: base/float.jl:906-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        else
            # Here `eps(Tf(typemin(Ti))) > 1`, so the only value which can be truncated to
            # `Tf(typemin(Ti)` is itself. Similarly, `Tf(typemax(Ti))` is inexact and will
            # be rounded up. For `Float16` and larger integer types, `Tf(typemin(Ti))` is
            # `-Inf`, so the lower bound is made strict to exclude it.
            lo = Tf(typemin(Ti))
            lo_cmp = lo === Tf(-Inf) ? :(<) : :(<=)
            @eval begin
                function round(::Type{$Ti},x::$Tf,::RoundingMode{:ToZero})
                    if $lo_cmp($lo, x) && x < $(Tf(typemax(Ti)))
                        return unsafe_trunc($Ti,x)
                    else
                        throw(InexactError(:round, $Ti, x, RoundToZero))
                    end
                end
```
-/
def round_ToZero_large (Ti : IntTy) {Tf : FTy} (x : FV Tf) : Jl (JInt Ti) :=
  let lo := floatOfInt Tf (int.typemin Ti)
  let hi := floatOfInt Tf (int.typemax Ti)
  let lo_ok := if egal_float lo (neg_IEEEFloat (inf_float Tf)) then lt_IEEEFloat lo x else le_IEEEFloat lo x
  if lo_ok && lt_IEEEFloat x hi then
    .ok (unsafe_trunc Ti x)
  else
    .error (.inexactError "round")

/--
Julia source: base/float.jl:921-932 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
                function (::Type{$Ti})(x::$Tf)
                    if ($(Tf(typemin(Ti))) <= x < $(Tf(typemax(Ti)))) && isinteger(x)
                        return unsafe_trunc($Ti,x)
                    else
                        throw(InexactError($(Expr(:quote,nameof(Ti))), $Ti, x))
                    end
                end
            end
        end
    end
end

```
-/
def intOfFloat_large (Ti : IntTy) {Tf : FTy} (x : FV Tf) : Jl (JInt Ti) :=
  let lo := floatOfInt Tf (int.typemin Ti)
  let hi := floatOfInt Tf (int.typemax Ti)
  if (le_IEEEFloat lo x && lt_IEEEFloat x hi) && isinteger_callee x then
    .ok (unsafe_trunc Ti x)
  else
    .error (.inexactError Ti.name)

/-- *dispatch*: `round(Ti, x::Tf, RoundToZero)` / `trunc(Ti, x::Tf)`. -/
def round_ToZero (Ti : IntTy) {Tf : FTy} (x : FV Tf) : Jl (JInt Ti) :=
  if !Ti.signed || int.sizeofT Ti < Tf.bytes then round_ToZero_small Ti x else round_ToZero_large Ti x

/-- *dispatch*: `Ti(x::Tf)` / `convert(Ti, x::Tf)`. -/
def intOfFloat (Ti : IntTy) {Tf : FTy} (x : FV Tf) : Jl (JInt Ti) :=
  if !Ti.signed || int.sizeofT Ti < Tf.bytes then intOfFloat_small Ti x else intOfFloat_large Ti x

/--
Julia source: base/float.jl:933-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    issubnormal(f)::Bool

Test whether a floating point number is subnormal.

An IEEE floating point number is [subnormal](https://en.wikipedia.org/wiki/Subnormal_number)
when its exponent bits are zero and its significand is not zero.

# Examples
```jldoctest
julia> floatmin(Float32)
1.1754944f-38

julia> issubnormal(1.0f-37)
false

julia> issubnormal(1.0f-38)
true
```
"""
function issubnormal(x::T) where {T<:IEEEFloat}
    y = reinterpret(Unsigned, x)
    (y & exponent_mask(T) == 0) & (y & significand_mask(T) != 0)
end

````
-/
def issubnormal {T : FTy} (x : FV T) : Bool :=
  let y := reinterpret_Unsigned x
  Bool.and (int.eq (int.band y (exponent_mask T)) (int.lit .i64 0))
    (!(int.eq (int.band y (significand_mask T)) (int.lit .i64 0)))

/--
Julia source: base/float.jl:958-958 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispow2(x::AbstractFloat) = !iszero(x) && frexp(x)[1] == 0.5
```
-/
def ispow2_generic {F E : Type} (iszero : F → Bool) (frexp : F → F × E)
    (eqHalf : F → FV .f64 → Bool) (x : F) : Bool :=
  !(iszero x) && eqHalf (frexp x).1 (reinterpret_Float_Int .f64 exponent_half_Float64)
def ispow2_AbstractFloat {T : FTy} {E : Type} (frexp : FV T → FV T × E) (x : FV T) : Bool :=
  ispow2_generic iszero_float frexp (fun a b => eq_IEEEFloat (convertFloat .f64 a) b) x

/--
Julia source: base/float.jl:959-959 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iseven(x::AbstractFloat) = isinteger(x) && (abs(x) > maxintfloat(x) || iseven(Integer(x)))
```
-/
def iseven_generic {F I : Type} (isinteger : F → Bool) (abs maxintfloat : F → F)
    (gt : F → F → Bool) (toInteger : F → I) (isevenInt : I → Bool) (x : F) : Bool :=
  isinteger x && (gt (abs x) (maxintfloat x) || isevenInt (toInteger x))
def iseven_AbstractFloat {T : FTy} {I : Type} (maxintfloat : FV T → FV T)
    (toInteger : FV T → I) (isevenInt : I → Bool) (x : FV T) : Bool :=
  iseven_generic isinteger_callee abs_IEEEFloat maxintfloat (fun a b => lt_IEEEFloat b a) toInteger isevenInt x

/--
Julia source: base/float.jl:960-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isodd(x::AbstractFloat) = isinteger(x) && abs(x) ≤ maxintfloat(x) && isodd(Integer(x))

```
-/
def isodd_generic {F I : Type} (isinteger : F → Bool) (abs maxintfloat : F → F)
    (le : F → F → Bool) (toInteger : F → I) (isoddInt : I → Bool) (x : F) : Bool :=
  isinteger x && le (abs x) (maxintfloat x) && isoddInt (toInteger x)
def isodd_AbstractFloat {T : FTy} {I : Type} (maxintfloat : FV T → FV T)
    (toInteger : FV T → I) (isoddInt : I → Bool) (x : FV T) : Bool :=
  isodd_generic isinteger_callee abs_IEEEFloat maxintfloat le_IEEEFloat toInteger isoddInt x

/--
Julia source: base/float.jl:962-963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval begin
    typemin(::Type{Float16}) = $(bitcast(Float16, 0xfc00))
```
-/
def typemin_Float16 : FV .f16 := bitcast_to_float .f16 (int.lit .u16 0xfc00)

/--
Julia source: base/float.jl:964-964 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    typemax(::Type{Float16}) = $(Inf16)
```
-/
def typemax_Float16 : FV .f16 := Inf16

/--
Julia source: base/float.jl:965-965 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    typemin(::Type{Float32}) = $(-Inf32)
```
-/
def typemin_Float32 : FV .f32 := neg_IEEEFloat Inf32

/--
Julia source: base/float.jl:966-966 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    typemax(::Type{Float32}) = $(Inf32)
```
-/
def typemax_Float32 : FV .f32 := Inf32

/--
Julia source: base/float.jl:967-967 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    typemin(::Type{Float64}) = $(-Inf64)
```
-/
def typemin_Float64 : FV .f64 := neg_IEEEFloat Inf64

/--
Julia source: base/float.jl:968-968 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    typemax(::Type{Float64}) = $(Inf64)
```
-/
def typemax_Float64 : FV .f64 := Inf64

/--
Julia source: base/float.jl:969-969 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    typemin(x::T) where {T<:Real} = typemin(T)
```
-/
def typemin_Real {Ty : Type} {Value : Ty → Type}
    (typeminT : (t : Ty) → Value t) (t : Ty) (_x : Value t) : Value t := typeminT t

/--
Julia source: base/float.jl:970-971 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    typemax(x::T) where {T<:Real} = typemax(T)

```
-/
def typemax_Real {Ty : Type} {Value : Ty → Type}
    (typemaxT : (t : Ty) → Value t) (t : Ty) (_x : Value t) : Value t := typemaxT t

/-- *dispatch*: `typemin(T)` for an `IEEEFloat` type `T`. -/
def typemin_float : (T : FTy) → FV T
  | .f16 => typemin_Float16 | .f32 => typemin_Float32 | .f64 => typemin_Float64
/-- *dispatch*: `typemax(T)` for an `IEEEFloat` type `T`. -/
def typemax_float : (T : FTy) → FV T
  | .f16 => typemax_Float16 | .f32 => typemax_Float32 | .f64 => typemax_Float64

/--
Julia source: base/float.jl:972-972 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    floatmin(::Type{Float16}) = $(bitcast(Float16, 0x0400))
```
-/
def floatmin_Float16 : FV .f16 := bitcast_to_float .f16 (int.lit .u16 0x0400)

/--
Julia source: base/float.jl:973-973 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    floatmin(::Type{Float32}) = $(bitcast(Float32, 0x00800000))
```
-/
def floatmin_Float32 : FV .f32 := bitcast_to_float .f32 (int.lit .u32 0x00800000)

/--
Julia source: base/float.jl:974-974 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    floatmin(::Type{Float64}) = $(bitcast(Float64, 0x0010000000000000))
```
-/
def floatmin_Float64 : FV .f64 := bitcast_to_float .f64 (int.lit .u64 0x0010000000000000)

/--
Julia source: base/float.jl:975-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    floatmax(::Type{Float16}) = $(bitcast(Float16, 0x7bff))
```
-/
def floatmax_Float16 : FV .f16 := bitcast_to_float .f16 (int.lit .u16 0x7bff)

/--
Julia source: base/float.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    floatmax(::Type{Float32}) = $(bitcast(Float32, 0x7f7fffff))
```
-/
def floatmax_Float32 : FV .f32 := bitcast_to_float .f32 (int.lit .u32 0x7f7fffff)

/--
Julia source: base/float.jl:977-978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    floatmax(::Type{Float64}) = $(bitcast(Float64, 0x7fefffffffffffff))

```
-/
def floatmax_Float64 : FV .f64 := bitcast_to_float .f64 (int.lit .u64 0x7fefffffffffffff)

/-- *dispatch*: `floatmin(T)` for an `IEEEFloat` type `T`. -/
def floatmin_float : (T : FTy) → FV T
  | .f16 => floatmin_Float16 | .f32 => floatmin_Float32 | .f64 => floatmin_Float64
/-- *dispatch*: `floatmax(T)` for an `IEEEFloat` type `T`. -/
def floatmax_float : (T : FTy) → FV T
  | .f16 => floatmax_Float16 | .f32 => floatmax_Float32 | .f64 => floatmax_Float64

/--
Julia source: base/float.jl:979-979 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eps(::Type{Float16}) = $(bitcast(Float16, 0x1400))
```
-/
def eps_Float16 : FV .f16 := bitcast_to_float .f16 (int.lit .u16 0x1400)

/--
Julia source: base/float.jl:980-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eps(::Type{Float32}) = $(bitcast(Float32, 0x34000000))
```
-/
def eps_Float32 : FV .f32 := bitcast_to_float .f32 (int.lit .u32 0x34000000)

/--
Julia source: base/float.jl:981-981 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eps(::Type{Float64}) = $(bitcast(Float64, 0x3cb0000000000000))
```
-/
def eps_Float64 : FV .f64 := bitcast_to_float .f64 (int.lit .u64 0x3cb0000000000000)

/-- *dispatch*: `eps(T)` for an `IEEEFloat` type `T`. -/
def eps_float : (T : FTy) → FV T
  | .f16 => eps_Float16 | .f32 => eps_Float32 | .f64 => eps_Float64

/--
Julia source: base/float.jl:982-984 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eps() = eps(Float64)
end

```
-/
def eps_default : FV .f64 := eps_float .f64

/--
Julia source: base/float.jl:985-986 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eps(x::AbstractFloat) = isfinite(x) ? abs(x) >= floatmin(x) ? ldexp(eps(typeof(x)), exponent(x)) : nextfloat(zero(x)) : oftype(x, NaN)

```
-/
def eps_AbstractFloat {F E : Type} (isfinite : F → Bool) (abs : F → F) (le : F → F → Bool)
    (floatmin : F → F) (epsT : F) (exponent : F → E) (ldexp : F → E → F)
    (nextfloat zero : F → F) (nan : F) (x : F) : F :=
  if isfinite x then
    if le (floatmin x) (abs x) then ldexp epsT (exponent x) else nextfloat (zero x)
  else nan

/--
Julia source: base/float.jl:987-995 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eps(x::T) where T<:IEEEFloat
    # For isfinite(x), toggling the LSB will produce either prevfloat(x) or
    # nextfloat(x) but will never change the sign or exponent.
    # For !isfinite(x), this will map Inf to NaN and NaN to NaN or Inf.
    y = reinterpret(T, reinterpret(Unsigned, x) ⊻ true)
    # The absolute difference between these values is eps(x). This is true even
    # for Inf/NaN values.
    return abs(x - y)
end
```
-/
def eps_IEEEFloat {T : FTy} (x : FV T) : FV T :=
  let y := reinterpret_Float_Int T (int.bxor (reinterpret_Unsigned x) (int.ofBool T.uintTy true))
  abs_IEEEFloat (sub_IEEEFloat x y)

/--
Julia source: base/float.jl:996-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eps(::Type{Union{}}, slurp...) = throw(MethodError(eps, (Union{}, slurp...)))

```
-/
def eps_Union {α : Type} : Jl α := .error (.methodError "eps")

/--
Julia source: base/float.jl:998-1020 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    floatmin(T = Float64)
    floatmin(::T)

Return the smallest positive normal number representable by the floating-point
type `T`.  The argument can alternatively be an instance of `T`.

See also: [`typemin`](@ref), [`maxintfloat`](@ref), [`floatmax`](@ref), [`eps`](@ref).

# Examples
```jldoctest
julia> floatmin(Float16)
Float16(6.104e-5)

julia> floatmin(1.0f0) # a Float32 instance
1.1754944f-38

julia> floatmin()
2.2250738585072014e-308
```
"""
floatmin(x::T) where {T<:AbstractFloat} = floatmin(T)

````
-/
def floatmin_AbstractFloat {Ty : Type} {Value : Ty → Type}
    (floatminT : (t : Ty) → Value t) (t : Ty) (_x : Value t) : Value t := floatminT t
def floatmin_val {T : FTy} (x : FV T) : FV T := floatmin_AbstractFloat floatmin_float T x

/--
Julia source: base/float.jl:1021-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    floatmax(T = Float64)
    floatmax(::T)

Return the largest finite number representable by the floating-point type `T`.
The argument can alternatively be an instance of `T`.

See also: [`typemax`](@ref), [`maxintfloat`](@ref), [`floatmin`](@ref), [`eps`](@ref).

# Examples
```jldoctest
julia> floatmax(Float16)
Float16(6.55e4)

julia> floatmax(1.0f0) # a Float32 instance
3.4028235f38

julia> floatmax()
1.7976931348623157e308

julia> typemax(Float64)
Inf
```
"""
floatmax(x::T) where {T<:AbstractFloat} = floatmax(T)

````
-/
def floatmax_AbstractFloat {Ty : Type} {Value : Ty → Type}
    (floatmaxT : (t : Ty) → Value t) (t : Ty) (_x : Value t) : Value t := floatmaxT t
def floatmax_val {T : FTy} (x : FV T) : FV T := floatmax_AbstractFloat floatmax_float T x

/--
Julia source: base/float.jl:1047-1047 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floatmin() = floatmin(Float64)
```
-/
def floatmin_default : FV .f64 := floatmin_float .f64

/--
Julia source: base/float.jl:1048-1048 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floatmax() = floatmax(Float64)
```
-/
def floatmax_default : FV .f64 := floatmax_float .f64

/--
Julia source: base/float.jl:1049-1049 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floatmin(::Type{Union{}}, slurp...) = throw(MethodError(floatmin, (Union{}, slurp...)))
```
-/
def floatmin_Union {α : Type} : Jl α := .error (.methodError "floatmin")

/--
Julia source: base/float.jl:1050-1131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
floatmax(::Type{Union{}}, slurp...) = throw(MethodError(floatmax, (Union{}, slurp...)))

"""
    eps(::Type{T}) where T<:AbstractFloat
    eps()

Return the *machine epsilon* of the floating point type `T` (`T = Float64` by
default). This is defined as the gap between 1 and the next largest value representable by
`typeof(one(T))`, and is equivalent to `eps(one(T))`.  (Since `eps(T)` is a
bound on the *relative error* of `T`, it is a "dimensionless" quantity like [`one`](@ref).)

# Examples
```jldoctest
julia> eps()
2.220446049250313e-16

julia> eps(Float32)
1.1920929f-7

julia> 1.0 + eps()
1.0000000000000002

julia> 1.0 + eps()/2
1.0
```

More generally, for any floating-point numeric type, `eps` corresponds to an
upper bound on the distance to the nearest floating-point value: if ``\text{fl}(x)`` is the closest
floating-point value to a number ``x`` (e.g. an arbitrary real number), then ``\text{fl}(x)``
satisfies ``|x - \text{fl}(x)| ≤ \text{eps}(x)/2``, not including overflow cases.
This allows the definition of `eps` to be extended to complex numbers,
for which ``\text{fl}(a + ib) = \text{fl}(a) + i \text{fl}(b)``.
"""
eps(::Type{<:AbstractFloat})

"""
    eps(x::AbstractFloat)

Return the *unit in last place* (ulp) of `x`. This is the distance between consecutive
representable floating point values at `x`. In most cases, if the distance on either side
of `x` is different, then the larger of the two is taken, that is

    eps(x) == max(x-prevfloat(x), nextfloat(x)-x)

The exceptions to this rule are the smallest and largest finite values
(e.g. `nextfloat(-Inf)` and `prevfloat(Inf)` for [`Float64`](@ref)), which round to the
smaller of the values.

The rationale for this behavior is that `eps` bounds the floating point rounding
error. Under the default `RoundNearest` rounding mode, if ``y`` is a real number and ``x``
is the nearest floating point number to ``y``, then

```math
|y-x| \\leq \\operatorname{eps}(x)/2.
```

See also: [`nextfloat`](@ref), [`issubnormal`](@ref), [`floatmax`](@ref).

# Examples
```jldoctest
julia> eps(1.0)
2.220446049250313e-16

julia> eps(prevfloat(2.0))
2.220446049250313e-16

julia> eps(2.0)
4.440892098500626e-16

julia> x = prevfloat(Inf)      # largest finite Float64
1.7976931348623157e308

julia> x + eps(x)/2            # rounds up
Inf

julia> x + prevfloat(eps(x)/2) # rounds down
1.7976931348623157e308
```
"""
eps(::AbstractFloat)


````
-/
def floatmax_Union {α : Type} : Jl α := .error (.methodError "floatmax")

/--
Julia source: base/float.jl:1132-1134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## byte order swaps for arbitrary-endianness serialization/deserialization ##
bswap(x::IEEEFloat) = bswap_int(x)

```
-/
def bswap_IEEEFloat {T : FTy} (x : FV T) : FV T := bswap_int_float x

/--
Julia source: base/float.jl:1135-1136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# integer size of float
uinttype(::Type{Float64}) = UInt64
```
-/
def uinttype_Float64 : IntTy := .u64

/--
Julia source: base/float.jl:1137-1137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uinttype(::Type{Float32}) = UInt32
```
-/
def uinttype_Float32 : IntTy := .u32

/--
Julia source: base/float.jl:1138-1138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uinttype(::Type{Float16}) = UInt16
```
-/
def uinttype_Float16 : IntTy := .u16

/--
Julia source: base/float.jl:1139-1139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inttype(::Type{Float64}) = Int64
```
-/
def inttype_Float64 : IntTy := .i64

/--
Julia source: base/float.jl:1140-1140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inttype(::Type{Float32}) = Int32
```
-/
def inttype_Float32 : IntTy := .i32

/--
Julia source: base/float.jl:1141-1141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inttype(::Type{Float16}) = Int16
```
-/
def inttype_Float16 : IntTy := .i16

/--
Julia source: base/float.jl:1142-1143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# float size of integer
floattype(::Type{UInt64}) = Float64
```
-/
def floattype_UInt64 : FTy := .f64

/--
Julia source: base/float.jl:1144-1144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floattype(::Type{UInt32}) = Float32
```
-/
def floattype_UInt32 : FTy := .f32

/--
Julia source: base/float.jl:1145-1145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floattype(::Type{UInt16}) = Float16
```
-/
def floattype_UInt16 : FTy := .f16

/--
Julia source: base/float.jl:1146-1146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floattype(::Type{Int64}) = Float64
```
-/
def floattype_Int64 : FTy := .f64

/--
Julia source: base/float.jl:1147-1147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floattype(::Type{Int32}) = Float32
```
-/
def floattype_Int32 : FTy := .f32

/--
Julia source: base/float.jl:1148-1150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floattype(::Type{Int16}) = Float16


```
-/
def floattype_Int16 : FTy := .f16

/-- *dispatch*: `floattype(T)` for a 16-, 32-, or 64-bit `BitInteger` type `T`. -/
def floattype : IntTy → Option FTy
  | .u64 => some floattype_UInt64
  | .u32 => some floattype_UInt32
  | .u16 => some floattype_UInt16
  | .i64 => some floattype_Int64
  | .i32 => some floattype_Int32
  | .i16 => some floattype_Int16
  | _ => none

/--
Julia source: base/float.jl:1151-1167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
## Array operations on floating point numbers ##
"""
    float(A::AbstractArray)

Return an array containing the floating-point analog of each entry in array `A`.

Equivalent to `float.(A)`, except that the return value may share memory with all or
part of `A` in accordance with the behavior of `convert(T, A)` given output type `T`.

# Examples
```jldoctest
julia> float(1:1000)
1.0:1.0:1000.0
```
"""
float(A::AbstractArray{<:AbstractFloat}) = A

````
-/
def float_AbstractArray_AbstractFloat {A : Type} (a : A) : A := a

/--
Julia source: base/float.jl:1168-1174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function float(A::AbstractArray{T}) where T
    if !isconcretetype(T)
        error("`float` not defined on abstractly-typed arrays; please convert to a more specific type")
    end
    convert(AbstractArray{typeof(float(zero(T)))}, A)
end

```
-/
def float_AbstractArray {T F Ty A B : Type} (isconcretetype : Unit → Bool)
    (zero : Unit → T) (float : T → F) (typeof : F → Ty)
    (convert : Ty → A → JuliaLean.base.range.JlX B) (a : A) : JuliaLean.base.range.JlX B :=
  if !(isconcretetype ()) then
    .error (.errorException "`float` not defined on abstractly-typed arrays; please convert to a more specific type")
  else
    convert (typeof (float (zero ()))) a

/--
Julia source: base/float.jl:1175-1175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(r::StepRange) = float(r.start):float(r.step):float(last(r))
```
-/
def float_StepRange {T S FT FS R : Type} (floatT : T → FT) (floatS : S → FS)
    (last : JuliaLean.base.range.StepRange T S → T)
    (colon : FT → FS → FT → R) (r : JuliaLean.base.range.StepRange T S) : R :=
  colon (floatT r.start) (floatS r.step) (floatT (last r))

/--
Julia source: base/float.jl:1176-1176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(r::UnitRange) = float(r.start):float(last(r))
```
-/
def float_UnitRange {T FT R : Type} (floatT : T → FT)
    (last : JuliaLean.base.range.UnitRange T → T)
    (colon : FT → FT → R) (r : JuliaLean.base.range.UnitRange T) : R :=
  colon (floatT r.start) (floatT (last r))

/--
Julia source: base/float.jl:1177-1178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(r::StepRangeLen{T}) where {T} =
    StepRangeLen{typeof(float(T(r.ref)))}(float(r.ref), float(r.step), length(r), r.offset)
```
-/
def float_StepRangeLen {T R S L FT FR FS Ty Res : Type}
    (toT : R → T) (floatT : T → FT) (typeof : FT → Ty)
    (floatR : R → FR) (floatS : S → FS)
    (length : JuliaLean.base.range.StepRangeLen T R S L → L)
    (StepRangeLen_T : Ty → FR → FS → L → L → Res)
    (r : JuliaLean.base.range.StepRangeLen T R S L) : Res :=
  StepRangeLen_T (typeof (floatT (toT r.ref))) (floatR r.ref) (floatS r.step) (length r) r.offset

/--
Julia source: base/float.jl:1179-1181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function float(r::LinRange)
    LinRange(float(r.start), float(r.stop), length(r))
end
```
-/
def float_LinRange {T L FT Res : Type} (floatT : T → FT)
    (length : JuliaLean.base.range.LinRange T L → L)
    (LinRange_ctor : FT → FT → L → Res)
    (r : JuliaLean.base.range.LinRange T L) : Res :=
  LinRange_ctor (floatT r.start) (floatT r.stop) (length r)

end JuliaLean.base.float

import JuliaLean.Core
import JuliaLean.base.float
import JuliaLean.base.int
import JuliaLean.base.intfuncs

/-!
# Model of `base/ryu/utils.jl`

Typed methods for Ryu's integer arithmetic, table generation, and output
helpers. Table construction uses natural-number arithmetic for Julia `BigInt`
expressions and `JInt` for fixed-width integer operations.
-/

namespace JuliaLean.base.ryu.Ryu

open JuliaLean JuliaLean.ParsePrint JuliaLean.base.float

abbrev FT := FTy

def uinttype : FT → IntTy := FTy.uintTy

def widenTy : IntTy → IntTy
  | .u8 => .u16 | .u16 => .u32 | .u32 => .u64 | .u64 => .u128 | t => t

def widen (T : FT) : IntTy := widenTy (uinttype T)

def exponent_max (T : FT) : Int := (JuliaLean.base.float.exponent_max T).val

def precision (T : FT) : Int := (JuliaLean.base.float.significand_bits T).val + 1

def exponent_bias (T : FT) : Int := (JuliaLean.base.float.exponent_bias T).val

def significand_bits (T : FT) : Int := (JuliaLean.base.float.significand_bits T).val

/-- Julia source: base/ryu/utils.jl:1-2 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const MANTISSA_MASK = Base.significand_mask(Float64)
const EXP_MASK = Base.exponent_mask(Float64) >> Base.significand_bits(Float64)
```
-/
def MANTISSA_MASK : JInt .u64 := JuliaLean.base.float.significand_mask_Float64

def EXP_MASK : JInt .u64 := shr JuliaLean.base.float.exponent_mask_Float64 52

/--
Julia source: base/ryu/utils.jl:4-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Note: these are smaller than the values given in Figure 4 from the paper
# see https://github.com/ulfjack/ryu/issues/119
pow5_bitcount(::Type{Float16}) = 30
pow5_bitcount(::Type{Float32}) = 61
pow5_bitcount(::Type{Float64}) = 121
```
-/
def pow5_bitcount : FT → Nat | .f16 => 30 | .f32 => 61 | .f64 => 121

/--
Julia source: base/ryu/utils.jl:10-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pow5_inv_bitcount(::Type{Float16}) = 30
pow5_inv_bitcount(::Type{Float32}) = 59
pow5_inv_bitcount(::Type{Float64}) = 122
```
-/
def pow5_inv_bitcount : FT → Nat | .f16 => 30 | .f32 => 59 | .f64 => 122

/--
Julia source: base/ryu/utils.jl:14-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
qinvbound(::Type{Float16}) = 4
qinvbound(::Type{Float32}) = 9
qinvbound(::Type{Float64}) = 21
```
-/
def qinvbound : FT → Nat | .f16 => 4 | .f32 => 9 | .f64 => 21

/--
Julia source: base/ryu/utils.jl:18-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
qbound(::Type{Float16}) = 15
qbound(::Type{Float32}) = 31
qbound(::Type{Float64}) = 63
```
-/
def qbound : FT → Nat | .f16 => 15 | .f32 => 31 | .f64 => 63

private def ashr (x : JInt .i64) (k : Nat) : JInt .i64 :=
  JuliaLean.base.int.shr_Int x (JInt.lit .i64 (Int.ofNat k))

/--
Julia source: base/ryu/utils.jl:22-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.log10pow2(e::Integer)

Compute `floor(log10(2^e))`. This is valid for all `e < 1651`.
"""
log10pow2(e) = (e * 78913) >> 18
```
-/
def log10pow2 (e : JInt .i64) : JInt .i64 :=
  ashr (e * JInt.lit .i64 78913) 18

/--
Julia source: base/ryu/utils.jl:30-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.log10pow5(e::Integer)

Compute `floor(log10(5^e))`. This is valid for all `e < 2621`.
"""
log10pow5(e) = (e * 732923) >> 20
```
-/
def log10pow5 (e : JInt .i64) : JInt .i64 :=
  ashr (e * JInt.lit .i64 732923) 20

/--
Julia source: base/ryu/utils.jl:37-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.pow5bits(e)

Compute `e == 0 ? 1 : ceil(log2(5^e))`. This is valid for `e < 3529` (if performed in `Int32` arithmetic).
"""
pow5bits(e) = ((e * 1217359) >> 19) + 1
```
-/
def pow5bits (e : JInt .i64) : JInt .i64 :=
  ashr (e * JInt.lit .i64 1217359) 19 + JInt.lit .i64 1

def promU32 : IntTy → IntTy
  | .u8 => .u32 | .u16 => .u32 | t => t

/--
Julia source: base/ryu/utils.jl:44-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
""""
     Ryu.mulshift(m::U, mul, j) where {U<:Unsigned}

Compute `(m * mul) >> j`, where `j >= 8*sizeof(U)`. The type of the results is the larger of `U` or `UInt32`.
"""
function mulshift(m::U, mul, j) where {U<:Unsigned}
    W = widen(U)
    nbits = 8*sizeof(U)
    return ((((W(m) * (mul % U)) >> nbits) + W(m) * (mul >> nbits)) >> (j - nbits)) % promote_type(U,UInt32)
end
```
-/
def mulshift (u : IntTy) (m : JInt u) (mul : JInt (widenTy u)) (j : Int) : JInt (promU32 u) :=
  let nbits := u.bits
  let wm : JInt (widenTy u) := JInt.rem (widenTy u) m
  let lo : JInt (widenTy u) := JInt.rem (widenTy u) (JInt.rem u mul)
  let hi : JInt (widenTy u) := shr mul nbits
  JInt.rem (promU32 u) (shrI (shr (wm * lo) nbits + wm * hi) (j - Int.ofNat nbits))

/--
Julia source: base/ryu/utils.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
indexforexp(e) = div(e + 15, 16)
```
-/
def indexforexp (e : JInt .i64) : Jl (JInt .i64) :=
  JInt.div (e + JInt.lit .i64 15) (JInt.lit .i64 16)

/--
Julia source: base/ryu/utils.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pow10bitsforindex(idx) = 16 * idx + 120
```
-/
def pow10bitsforindex (idx : JInt .i64) : JInt .i64 :=
  JInt.lit .i64 16 * idx + JInt.lit .i64 120

/--
Julia source: base/ryu/utils.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lengthforindex(idx) = div(((Int64(16 * idx) * 1292913986) >> 32) + 1 + 16 + 8, 9)
```
-/
def lengthforindex (idx : JInt .i64) : Jl (JInt .i64) :=
  let scaled := JInt.wrap .i64 (16 * idx.val)
  let product := JInt.wrap .i64 (scaled.val * 1292913986)
  let shifted := JuliaLean.base.int.shr_Int product (JInt.lit .i64 32)
  JInt.div (shifted + JInt.lit .i64 (1 + 16 + 8)) (JInt.lit .i64 9)

/-- `Base.power_by_squaring(UInt64(5), p; mul = *%)` is `5^p mod 2^64` for nonnegative `p`. -/
def wrappedPow5 (p : JInt .i64) : JInt .u64 := JInt.wrap .u64 (5 ^ p.val.toNat)

/--
Julia source: base/ryu/utils.jl:59-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.pow5(x, p)

Return `true` if `5^p` is a divisor of `x`.
"""
function pow5(x, p)
    # Assumptions:
    #   0 < x < (1 << 53)
    #   0 <= p <= 308
    wrapped_pow = Base.power_by_squaring(UInt64(5), p; mul=*%)

    # We are using wrapping arithmetic here, which can overflow, but we get the right answer anyway
    # by the following argument (#47511):
    # 1. False Negative
    #   No overflow occurs unless big(5)^p > typemax(UInt64), but typemax(UInt64) > (1 << 53), so
    #   z is never divisible by big(5)^p. QED.
    # 2. False Positive
    #   We ask ∃ m2, p s.t. big(5)^p && m2 % wrapped_pow == 0.
    #   By exhaustive checking `all(p->UInt64(5)^p > 1<<53, 28:308)`, so there does not exist any such
    #   `m2` that satiesfies our assumptions above. QED.
    x % wrapped_pow == 0
end
```
-/
def pow5 (x : JInt .u64) (p : JInt .i64) : Bool := x.val % (wrappedPow5 p).val == 0

/-- `Int64(1) << p`, with Julia's signed shift-count behavior. -/
def shlOne64 (p : JInt .i64) : JInt .i64 := JuliaLean.base.int.shl_Int (JInt.lit .i64 1) p

/--
Julia source: base/ryu/utils.jl:82-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.pow2(x, p)

Return `true` if `2^p` is a divisor of `x`. In other words, if the trailing `p` bits of `x` are zero.
"""
pow2(x, p) = (x & ((Int64(1) << p) - 1)) == 0
```
-/
def pow2 {u : IntTy} (x : JInt u) (p : JInt .i64) : Bool :=
  let mask : JInt .i64 := shlOne64 p - JInt.lit .i64 1
  Nat.land x.val.toNat (mask.val % 2 ^ 64).toNat == 0

/--
Julia source: base/ryu/utils.jl:89-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.decimallength(v)

The number of decimal digits of the integer `v`.
"""
function decimallength(v)
    v >= 10000000000000000 && return 17
    v >= 1000000000000000 && return 16
    v >= 100000000000000 && return 15
    v >= 10000000000000 && return 14
    v >= 1000000000000 && return 13
    v >= 100000000000 && return 12
    v >= 10000000000 && return 11
    v >= 1000000000 && return 10
    v >= 100000000 && return 9
    v >= 10000000 && return 8
    v >= 1000000 && return 7
    v >= 100000 && return 6
    v >= 10000 && return 5
    v >= 1000 && return 4
    v >= 100 && return 3
    v >= 10 && return 2
    return 1
end
```
-/
def decimallength (v : Int) : Nat :=
  if v ≥ 10000000000000000 then 17 else if v ≥ 1000000000000000 then 16
  else if v ≥ 100000000000000 then 15 else if v ≥ 10000000000000 then 14
  else if v ≥ 1000000000000 then 13 else if v ≥ 100000000000 then 12
  else if v ≥ 10000000000 then 11 else if v ≥ 1000000000 then 10
  else if v ≥ 100000000 then 9 else if v ≥ 10000000 then 8
  else if v ≥ 1000000 then 7 else if v ≥ 100000 then 6
  else if v ≥ 10000 then 5 else if v ≥ 1000 then 4
  else if v ≥ 100 then 3 else if v ≥ 10 then 2 else 1

/--
Julia source: base/ryu/utils.jl:113-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function decimallength(v::UInt32)
    v >= 100000000 && return 9
    v >= 10000000 && return 8
    v >= 1000000 && return 7
    v >= 100000 && return 6
    v >= 10000 && return 5
    v >= 1000 && return 4
    v >= 100 && return 3
    v >= 10 && return 2
    return 1
end
```
-/
def decimallength32 (v : JInt .u32) : Nat :=
  if v.val ≥ 100000000 then 9 else if v.val ≥ 10000000 then 8
  else if v.val ≥ 1000000 then 7 else if v.val ≥ 100000 then 6
  else if v.val ≥ 10000 then 5 else if v.val ≥ 1000 then 4
  else if v.val ≥ 100 then 3 else if v.val ≥ 10 then 2 else 1

/--
Julia source: base/ryu/utils.jl:124-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function decimallength(v::UInt16)
    v >= 10000 && return 5
    v >= 1000 && return 4
    v >= 100 && return 3
    v >= 10 && return 2
    return 1
end
```
-/
def decimallength16 (v : JInt .u16) : Nat :=
  if v.val ≥ 10000 then 5 else if v.val ≥ 1000 then 4
  else if v.val ≥ 100 then 3 else if v.val ≥ 10 then 2 else 1

/-- The number of binary digits of a positive natural. -/
def nbits (n : Nat) : Nat := Nat.log2 n + 1

/--
Julia source: base/ryu/utils.jl:272-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.pow5invsplit(T, i)

Compute `floor(2^k/5^i)+1`, where `k = pow5bits(i) - 1 + pow5_inv_bitcount(T)`. The result
is an unsigned integer twice as wide as `T` (i.e. a `UInt128` if `T == Float64`), with
`pow5_inv_bitcount(T)` significant bits.
"""
function pow5invsplit(::Type{T}, i) where {T<:AbstractFloat}
    W = widen(uinttype(T))
    pow = big(5)^i
    inv = div(big(1) << (ndigits(pow, base=2) - 1 + pow5_inv_bitcount(T)), pow) + 1
    return W(inv)
end
```
-/
def pow5invsplit (T : FT) (i : Nat) : Jl (JInt (widen T)) :=
  let pow := 5 ^ i
  let inv := 2 ^ (nbits pow - 1 + pow5_inv_bitcount T) / pow + 1
  JInt.convert (widen T).name (widen T) inv

/--
Julia source: base/ryu/utils.jl:301-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.pow5split(T, i)

Compute `floor(5^i/2^k)`, where `k = pow5bits(i) - pow5_bitcount(T)`. The result is an
unsigned integer twice as wide as `T` (i.e. a `UInt128` if `T == Float64`), with
`pow5_bitcount(T)` significant bits.
"""
function pow5split(::Type{T}, i) where {T<:AbstractFloat}
    W = widen(uinttype(T))
    pow = big(5)^i
    return W(pow >> (ndigits(pow, base=2) - pow5_bitcount(T)))
end
```
-/
def pow5split (T : FT) (i : Nat) : Jl (JInt (widen T)) :=
  let pow := 5 ^ i
  let shift : Int := Int.ofNat (nbits pow) - Int.ofNat (pow5_bitcount T)
  let shifted := if shift ≥ 0 then pow / 2 ^ shift.toNat else pow * 2 ^ (-shift).toNat
  JInt.convert (widen T).name (widen T) shifted

def invImax (T : FT) : Int :=
  (log10pow2 (JInt.lit .i64 (exponent_max T - precision T - 1))).val

def splitImax (T : FT) : Int :=
  let e2min := 1 - exponent_bias T - significand_bits T - 2
  1 - e2min - (log10pow5 (JInt.lit .i64 (-e2min))).val

def pow5invsplit_table (T : FT) : List (Jl (JInt (widen T))) :=
  (List.range ((invImax T).toNat + 1)).map (pow5invsplit T)

def pow5split_table (T : FT) : List (Jl (JInt (widen T))) :=
  (List.range ((splitImax T).toNat + 1)).map (pow5split T)

/--
Julia source: base/ryu/utils.jl:286-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.pow5invsplit_lookup(T, i)

[`pow5invsplit`](@ref) computed via lookup table.
"""
```
-/
def pow5invsplit_lookup (T : FT) (i : Int) : Option (Jl (JInt (widen T))) :=
  if 0 ≤ i then (pow5invsplit_table T)[i.toNat]? else none

-- UNTRANSLATED
-- Source: base/ryu/utils.jl:292-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for T in (Float64, Float32, Float16)
--     e2_max = exponent_max(T) - precision(T) - 1
--     i_max = log10pow2(e2_max)
--     table_sym = Symbol("pow5invsplit_table_", string(T))
--     @eval const $table_sym = Tuple(Any[pow5invsplit($T, i) for i = 0:$i_max])
--     @eval pow5invsplit_lookup(::Type{$T}, i) = @inbounds($table_sym[i+1])
-- end
-- /Source
-- Reason: `@eval` builds type-specific tables and lookup methods at module load; the typed table and lookup definitions above model their runtime behavior.

/--
Julia source: base/ryu/utils.jl:314-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.pow5split_lookup(T, i)

[`pow5split`](@ref) computed via lookup table.
"""
```
-/
def pow5split_lookup (T : FT) (i : Int) : Option (Jl (JInt (widen T))) :=
  if 0 ≤ i then (pow5split_table T)[i.toNat]? else none

-- UNTRANSLATED
-- Source: base/ryu/utils.jl:319-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function pow5split_lookup end
-- for T in (Float64, Float32, Float16)
--     e2_min = 1 - exponent_bias(T) - significand_bits(T) - 2
--     i_max = 1 - e2_min - log10pow5(-e2_min)
--     table_sym = Symbol("pow5split_table_", string(T))
--     @eval const $table_sym = Tuple(Any[pow5split($T, i) for i = 0:$i_max])
--     @eval pow5split_lookup(::Type{$T}, i) = @inbounds($table_sym[i+1])
-- end
-- /Source
-- Reason: `@eval` builds type-specific tables and lookup methods at module load; the typed table and lookup definitions above model their runtime behavior.

/--
Julia source: base/ryu/utils.jl:132-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mulshiftinvsplit(::Type{T}, mv, mp, mm, i, j) where {T}
    mul = pow5invsplit_lookup(T, i)
    vr = mulshift(mv, mul, j)
    vp = mulshift(mp, mul, j)
    vm = mulshift(mm, mul, j)
    return vr, vp, vm
end
```
-/
def mulshiftinvsplit (T : FT) (mv mp mm : JInt (uinttype T)) (i j : Int) :
    Option (Jl (JInt (promU32 (uinttype T)) × JInt (promU32 (uinttype T)) × JInt (promU32 (uinttype T)))) :=
  match pow5invsplit_lookup T i with
  | none => none
  | some mul => some (do
      let mul ← mul
      pure (mulshift (uinttype T) mv mul j, mulshift (uinttype T) mp mul j,
        mulshift (uinttype T) mm mul j))

/--
Julia source: base/ryu/utils.jl:140-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mulshiftsplit(::Type{T}, mv, mp, mm, i, j) where {T}
    mul = pow5split_lookup(T, i)
    vr = mulshift(mv, mul, j)
    vp = mulshift(mp, mul, j)
    vm = mulshift(mm, mul, j)
    return vr, vp, vm
end
```
-/
def mulshiftsplit (T : FT) (mv mp mm : JInt (uinttype T)) (i j : Int) :
    Option (Jl (JInt (promU32 (uinttype T)) × JInt (promU32 (uinttype T)) × JInt (promU32 (uinttype T)))) :=
  match pow5split_lookup T i with
  | none => none
  | some mul => some (do
      let mul ← mul
      pure (mulshift (uinttype T) mv mul j, mulshift (uinttype T) mp mul j,
        mulshift (uinttype T) mm mul j))

/--
Julia source: base/ryu/utils.jl:148-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.umul256(a::UInt128, bHi::UInt64, bLo::UInt64)::Tuple{UInt128, UInt128}

Compute `p = a*b` where `b = bLo + bHi<<64`, returning the result as `pLo, pHi` where `p = pLo + pHi<<128`.
"""
function umul256(a::UInt128, bHi::UInt64, bLo::UInt64)
    aLo = a % UInt64
    aHi = (a >> 64) % UInt64

    b00 = UInt128(aLo) * bLo
    b01 = UInt128(aLo) * bHi
    b10 = UInt128(aHi) * bLo
    b11 = UInt128(aHi) * bHi

    b00Lo = b00 % UInt64
    b00Hi = (b00 >> 64) % UInt64

    mid1 = b10 +% b00Hi
    mid1Lo = mid1 % UInt64
    mid1Hi = (mid1 >> 64) % UInt64

    mid2 = b01 +% mid1Lo
    mid2Lo = mid2 % UInt64
    mid2Hi = (mid2 >> 64) % UInt64

    pHi = b11 +% mid1Hi +% mid2Hi
    pLo = (UInt128(mid2Lo) << 64) | b00Lo
    return pLo, pHi
end
```
-/
def umul256 (a : JInt .u128) (bHi bLo : JInt .u64) : JInt .u128 × JInt .u128 :=
  let aLo : JInt .u64 := JInt.rem .u64 a
  let aHi : JInt .u64 := JInt.rem .u64 (shr a 64)
  let b00 : JInt .u128 := JInt.rem .u128 aLo * JInt.rem .u128 bLo
  let b01 : JInt .u128 := JInt.rem .u128 aLo * JInt.rem .u128 bHi
  let b10 : JInt .u128 := JInt.rem .u128 aHi * JInt.rem .u128 bLo
  let b11 : JInt .u128 := JInt.rem .u128 aHi * JInt.rem .u128 bHi
  let b00Lo : JInt .u64 := JInt.rem .u64 b00
  let b00Hi : JInt .u64 := JInt.rem .u64 (shr b00 64)
  let mid1 : JInt .u128 := b10 + JInt.rem .u128 b00Hi
  let mid1Lo : JInt .u64 := JInt.rem .u64 mid1
  let mid1Hi : JInt .u64 := JInt.rem .u64 (shr mid1 64)
  let mid2 : JInt .u128 := b01 + JInt.rem .u128 mid1Lo
  let mid2Lo : JInt .u64 := JInt.rem .u64 mid2
  let mid2Hi : JInt .u64 := JInt.rem .u64 (shr mid2 64)
  let pHi : JInt .u128 := b11 + JInt.rem .u128 mid1Hi + JInt.rem .u128 mid2Hi
  let pLo : JInt .u128 := bor (shl (JInt.rem .u128 mid2Lo) 64) (JInt.rem .u128 b00Lo)
  (pLo, pHi)

/--
Julia source: base/ryu/utils.jl:178-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.umul256_hi(a::UInt128, bHi::UInt64, bLo::UInt64)::UInt128

Compute `pHi = (a*b)>>128` where `b = bLo + bHi<<64`.
"""
umul256_hi(a::UInt128, bHi::UInt64, bLo::UInt64) = umul256(a, bHi, bLo)[2]
```
-/
def umul256_hi (a : JInt .u128) (bHi bLo : JInt .u64) : JInt .u128 := (umul256 a bHi bLo).2

/--
Julia source: base/ryu/utils.jl:185-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mod1e9(v::UInt128)
    # TODO: Fix LLVM to perform this optimization itself on 128 bit integers
    # return (v % 10^9) % UInt32
    multiplied = umul256_hi(v, 0x89705F4136B4A597, 0x31680A88F8953031)
    shifted = (multiplied >> 29) % UInt32
    return (v % UInt32) -% UInt32(1000000000) *% shifted
end
```
-/
def mod1e9 (v : JInt .u128) : JInt .u32 :=
  let multiplied := umul256_hi v (JInt.lit .u64 0x89705F4136B4A597) (JInt.lit .u64 0x31680A88F8953031)
  let shifted : JInt .u32 := JInt.rem .u32 (shr multiplied 29)
  JInt.rem .u32 v - JInt.lit .u32 1000000000 * shifted

/--
Julia source: base/ryu/utils.jl:193-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ryu.mulshiftmod1e9(m, mula, mulb, mulc, j)::UInt32

Compute `(m * mul) >> j % 10^9` where `mul = mula + mulb<<64 + mulc<<128`, and `j >= 128`.
"""
function mulshiftmod1e9(m, mula, mulb, mulc, j)
    b0 = UInt128(m) * mula
    b1 = UInt128(m) * mulb
    b2 = UInt128(m) * mulc
    mid = b1 +% ((b0 >> 64) % UInt64)
    s1 = b2 +% ((mid >> 64) % UInt64)
    v = s1 >> (j - 128)
    return mod1e9(v)
end
```
-/
def mulshiftmod1e9 (m mula mulb mulc : JInt .u64) (j : Int) : JInt .u32 :=
  let b0 : JInt .u128 := JInt.rem .u128 m * JInt.rem .u128 mula
  let b1 : JInt .u128 := JInt.rem .u128 m * JInt.rem .u128 mulb
  let b2 : JInt .u128 := JInt.rem .u128 m * JInt.rem .u128 mulc
  let mid : JInt .u128 := b1 + JInt.rem .u128 (JInt.rem .u64 (shr b0 64))
  let s1 : JInt .u128 := b2 + JInt.rem .u128 (JInt.rem .u64 (shr mid 64))
  mod1e9 (shrI s1 (j - 128))

/--
Julia source: base/ryu/utils.jl:208-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function append_sign(x, plus::Bool, space::Bool, buf, pos::Int)
    if signbit(x) && !isnan(x)  # suppress minus sign for signaling NaNs
        buf[pos] = UInt8('-')
        pos += 1
    elseif plus
        buf[pos] = UInt8('+')
        pos += 1
    elseif space
        buf[pos] = UInt8(' ')
        pos += 1
    end
    return pos
end
```
-/
def append_sign {T : FT} (x : FV T) (plus space : Bool)
    (buf : JuliaLean.base.intfuncs.Buffer) (pos : JInt .i64) :
    JuliaLean.base.intfuncs.Buffer × JInt .i64 :=
  if JuliaLean.base.float.signbit_float x && !JuliaLean.base.float.isnan_IEEEFloat x then
    (JuliaLean.base.intfuncs.store buf pos.val 45, pos + JInt.lit .i64 1)
  else if plus then
    (JuliaLean.base.intfuncs.store buf pos.val 43, pos + JInt.lit .i64 1)
  else if space then
    (JuliaLean.base.intfuncs.store buf pos.val 32, pos + JInt.lit .i64 1)
  else (buf, pos)

/--
Julia source: base/ryu/utils.jl:223-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
import Base: append_c_digits_fast as append_c_digits, append_nine_digits
```
-/
structure AppendDigitsOps (U : Type) where
  value : U → Int
  divrem : U → Nat → Jl (U × Nat)
  toUInt : U → JInt .u64
  append : JInt .i64 → JInt .u64 → JuliaLean.base.intfuncs.Buffer → JInt .i64 →
    Jl (JuliaLean.base.intfuncs.Buffer × JInt .i64)
  appendNine : JInt .u32 → JuliaLean.base.intfuncs.Buffer → JInt .i64 →
    Jl (JuliaLean.base.intfuncs.Buffer × JInt .i64)

/--
Julia source: base/ryu/utils.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function append_d_digits(olength::Int, digits::Unsigned, buf, pos::Int, decchar)
    newpos = append_c_digits(olength, digits, buf, pos + 1)
    @inbounds buf[pos] = buf[pos + 1]
    @inbounds buf[pos + 1] = decchar
    return newpos # == pos + olength + 1
end
```
-/
def append_d_digits {U : Type} (ops : AppendDigitsOps U) (olength : JInt .i64)
    (digits : U) (buf : JuliaLean.base.intfuncs.Buffer) (pos : JInt .i64)
    (decchar : JInt .u8) : Jl (JuliaLean.base.intfuncs.Buffer × JInt .i64) := do
  let (buf, newpos) ← JuliaLean.base.intfuncs.appendCDigitsFast ops.value ops.divrem
    ops.toUInt ops.append ops.appendNine olength digits buf (pos + JInt.lit .i64 1)
  let firstByte := buf.bytes.getD pos.val.toNat 0
  let buf := JuliaLean.base.intfuncs.store buf pos.val firstByte
  let buf := JuliaLean.base.intfuncs.store buf (pos.val + 1) decchar.val.toNat
  pure (buf, newpos)

/--
Julia source: base/ryu/utils.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const BIG_MASK = (big(1) << 64) - 1
```
-/
def BIG_MASK : Nat := 2 ^ 64 - 1

/--
Julia source: base/ryu/utils.jl:234-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const POW10_SPLIT = collect(Iterators.flatten(map(0:63) do idx
    pow10bits = pow10bitsforindex(idx)
    map(0:lengthforindex(idx)-1) do i
        v = (div(big(1) << pow10bits, big(10)^(9 * i)) + 1) % ((big(10)^9) << 136)
        return (UInt64(v & BIG_MASK), UInt64((v >> 64) & BIG_MASK), UInt64((v >> 128) & BIG_MASK))
    end
end))
```
-/
def pow10SplitLength (idx : Nat) : Nat :=
  ((16 * idx * 1292913986 / 2 ^ 32 + 1 + 16 + 8) / 9)

def pow10SplitEntry (idx i : Nat) : JInt .u64 × JInt .u64 × JInt .u64 :=
  let pow10bits := 16 * idx + 120
  let v := (2 ^ pow10bits / 10 ^ (9 * i) + 1) % (10 ^ 9 * 2 ^ 136)
  let mask := BIG_MASK + 1
  (JInt.wrap .u64 (Int.ofNat (v % mask)),
    JInt.wrap .u64 (Int.ofNat (v / 2 ^ 64 % mask)),
    JInt.wrap .u64 (Int.ofNat (v / 2 ^ 128 % mask)))

def POW10_SPLIT : List (JInt .u64 × JInt .u64 × JInt .u64) :=
  (List.range 64).flatMap fun idx =>
    (List.range (pow10SplitLength idx)).map fun i => pow10SplitEntry idx i

private structure InvState where
  split : List (Nat × Nat × Nat)
  minBlock : Option Nat

def invV (idx i : Nat) : Nat :=
  let p := 10 ^ (9 * (i + 1))
  let s : Int := -(120 - 16 * Int.ofNat idx)
  let q := if s ≥ 0 then p / 2 ^ s.toNat else p * 2 ^ (-s).toNat
  q % (10 ^ 9 * 2 ^ (120 + 16))

def invLoop (idx : Nat) : Nat → Nat → InvState → InvState
  | 0, _, state => state
  | fuel + 1, i, state =>
    let v := invV idx i
    if state.minBlock.isNone && (v * 2 ^ (54 + 8)) / 2 ^ 128 == 0 then
      invLoop idx fuel (i + 1) state
    else
      let state := if state.minBlock.isNone then { state with minBlock := some i } else state
      if v == 0 then state
      else invLoop idx fuel (i + 1)
        { state with split := state.split ++
          [(v % 2 ^ 64, v / 2 ^ 64 % 2 ^ 64, v / 2 ^ 128 % 2 ^ 64)] }

def genStep (fuel : Nat) (acc : List Nat × List Nat × List (Nat × Nat × Nat)) (idx : Nat) :
    List Nat × List Nat × List (Nat × Nat × Nat) :=
  let state := invLoop idx fuel 0 ⟨acc.2.2, none⟩
  (acc.1 ++ [acc.2.2.length], acc.2.1 ++ [state.minBlock.getD 0xff], state.split)

/--
Julia source: base/ryu/utils.jl:242-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function generateinversetables()
    POW10_OFFSET_2 = Vector{UInt16}(undef, 68 + 1)
    MIN_BLOCK_2 = fill(0xff, 68 + 1)
    POW10_SPLIT_2 = Tuple{UInt64, UInt64, UInt64}[]
    lowerCutoff = big(1) << (54 + 8)
    for idx = 0:67
        POW10_OFFSET_2[idx + 1] = length(POW10_SPLIT_2)
        i = 0
        while true
            v = ((big(10)^(9 * (i + 1)) >> (-(120 - 16 * idx))) % (big(10)^9) << (120 + 16))
            if MIN_BLOCK_2[idx + 1] == 0xff && ((v * lowerCutoff) >> 128) == 0
                i += 1
                continue
            end
            if MIN_BLOCK_2[idx + 1] == 0xff
                MIN_BLOCK_2[idx + 1] = i
            end
            v == 0 && break
            push!(POW10_SPLIT_2, ((v & BIG_MASK) % UInt64, ((v >> 64) & BIG_MASK) % UInt64, ((v >> 128) & BIG_MASK) % UInt64))
            i += 1
        end
    end
    POW10_OFFSET_2[end] = length(POW10_SPLIT_2)
    MIN_BLOCK_2[end] = 0x00

    return POW10_OFFSET_2, MIN_BLOCK_2, POW10_SPLIT_2
end
```
-/
def generateinversetables (n fuel : Nat) : List Nat × List Nat × List (Nat × Nat × Nat) :=
  let result := (List.range n).foldl (genStep fuel) ([], [], [])
  (result.1 ++ [result.2.2.length], result.2.1 ++ [0], result.2.2)

def inverseTables := generateinversetables 68 256

/--
Julia source: base/ryu/utils.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const POW10_OFFSET_2, MIN_BLOCK_2, POW10_SPLIT_2 = generateinversetables()
```
-/
def POW10_OFFSET_2 : List (JInt .u16) :=
  inverseTables.1.map fun n => JInt.wrap .u16 (Int.ofNat n)

def MIN_BLOCK_2 : List (JInt .u8) :=
  inverseTables.2.1.map fun n => JInt.wrap .u8 (Int.ofNat n)

def POW10_SPLIT_2 : List (JInt .u64 × JInt .u64 × JInt .u64) :=
  inverseTables.2.2.map fun (a, b, c) =>
    (JInt.wrap .u64 (Int.ofNat a), JInt.wrap .u64 (Int.ofNat b), JInt.wrap .u64 (Int.ofNat c))

/--
Julia source: base/ryu/utils.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const DIGIT_TABLE16 = Base._dec_d100
```
-/
def DIGIT_TABLE16 : List (JInt .u16) := JuliaLean.base.intfuncs.decimalPairs

/--
Julia source: base/ryu/utils.jl:330-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const POW10_OFFSET = UInt16[
  0, 2, 5, 8, 12, 16, 21, 26, 32, 39,
  46, 54, 62, 71, 80, 90, 100, 111, 122, 134,
  146, 159, 173, 187, 202, 217, 233, 249, 266, 283,
  301, 319, 338, 357, 377, 397, 418, 440, 462, 485,
  508, 532, 556, 581, 606, 632, 658, 685, 712, 740,
  769, 798, 828, 858, 889, 920, 952, 984, 1017, 1050,
  1084, 1118, 1153, 1188
]
```
-/
def POW10_OFFSET : List (JInt .u16) :=
  [0, 2, 5, 8, 12, 16, 21, 26, 32, 39, 46, 54, 62, 71, 80, 90,
    100, 111, 122, 134, 146, 159, 173, 187, 202, 217, 233, 249,
    266, 283, 301, 319, 338, 357, 377, 397, 418, 440, 462, 485,
    508, 532, 556, 581, 606, 632, 658, 685, 712, 740, 769, 798,
    828, 858, 889, 920, 952, 984, 1017, 1050, 1084, 1118, 1153, 1188]
    |>.map (fun n => JInt.wrap .u16 (Int.ofNat n))

end JuliaLean.base.ryu.Ryu

/-!
# `base/ryu/utils.jl` (master `bbfa0ce4150`)

The helpers of the Ryu printing algorithm. Julia integer values are `JInt`
values of the Julia type; unsigned operations wrap exactly where Julia wraps.
`BigInt` computations (`pow5split`, `pow5invsplit`, `generateinversetables`)
are `Nat` arithmetic, which is what `BigInt` arithmetic on these nonnegative
values is. `Base.power_by_squaring(UInt64(5), p; mul = *%)` is wrapping
multiplication in the ring of integers modulo `2^64`, so its value is
`5^p mod 2^64`.
-/

namespace JuliaLean.MiscCov.RyuUtils

open JuliaLean JuliaLean.ParsePrint

/-- `Float16`, `Float32`, `Float64`. -/
inductive FT where
  | f16 | f32 | f64
  deriving DecidableEq, Repr

/-- `uinttype(T)`. -/
def FT.uint : FT → IntTy
  | .f16 => .u16 | .f32 => .u32 | .f64 => .u64

/-- `widen(uinttype(T))`. -/
def FT.wide : FT → IntTy
  | .f16 => .u32 | .f32 => .u64 | .f64 => .u128

/-- `exponent_max(T)`, `precision(T)`, `exponent_bias(T)`, `significand_bits(T)`. -/
def FT.exponentMax : FT → Int | .f16 => 15 | .f32 => 127 | .f64 => 1023
def FT.precision : FT → Int | .f16 => 11 | .f32 => 24 | .f64 => 53
def FT.exponentBias : FT → Int | .f16 => 15 | .f32 => 127 | .f64 => 1023
def FT.significandBits : FT → Int | .f16 => 10 | .f32 => 23 | .f64 => 52

/-- `base/ryu/utils.jl:6-8`. -/
def pow5Bitcount : FT → Nat | .f16 => 30 | .f32 => 61 | .f64 => 121
/-- `base/ryu/utils.jl:10-12`. -/
def pow5InvBitcount : FT → Nat | .f16 => 30 | .f32 => 59 | .f64 => 122
/-- `base/ryu/utils.jl:14-16`. -/
def qinvbound : FT → Nat | .f16 => 4 | .f32 => 9 | .f64 => 21
/-- `base/ryu/utils.jl:18-20`. -/
def qbound : FT → Nat | .f16 => 15 | .f32 => 31 | .f64 => 63

/-- `x >> k` on a signed `Int` (`ashr_int`) for a nonnegative count: floor division. -/
def ashr (x : JInt t) (k : Nat) : JInt t := JInt.wrap t (x.val / 2 ^ k)

/-- `log10pow2(e) = (e * 78913) >> 18`, `base/ryu/utils.jl:27`, on `e::Int`. -/
def log10pow2 (e : JInt .i64) : JInt .i64 := ashr (e * JInt.lit .i64 78913) 18

/-- `log10pow5(e) = (e * 732923) >> 20`, `base/ryu/utils.jl:35`. -/
def log10pow5 (e : JInt .i64) : JInt .i64 := ashr (e * JInt.lit .i64 732923) 20

/-- `pow5bits(e) = ((e * 1217359) >> 19) + 1`, `base/ryu/utils.jl:42`. -/
def pow5bits (e : JInt .i64) : JInt .i64 := ashr (e * JInt.lit .i64 1217359) 19 + JInt.lit .i64 1

/-- `promote_type(U, UInt32)` for the unsigned `U` of `mulshift`. -/
def promU32 : IntTy → IntTy
  | .u8 => .u32 | .u16 => .u32 | t => t

/-- `widen(U)`. -/
def widenTy : IntTy → IntTy
  | .u8 => .u16 | .u16 => .u32 | .u32 => .u64 | .u64 => .u128 | t => t

/-- `mulshift(m::U, mul, j)`, `base/ryu/utils.jl:49-53`, for `mul` of type `widen(U)`
(the type of the lookup tables it is called with):
`((((W(m) * (mul % U)) >> nbits) + W(m) * (mul >> nbits)) >> (j - nbits)) % promote_type(U,UInt32)`. -/
def mulshift (u : IntTy) (m : JInt u) (mul : JInt (widenTy u)) (j : Int) : JInt (promU32 u) :=
  let nbits := u.bits
  let wm : JInt (widenTy u) := JInt.rem (widenTy u) m
  let lo : JInt (widenTy u) := JInt.rem (widenTy u) (JInt.rem u mul)
  let hi : JInt (widenTy u) := shr mul nbits
  JInt.rem (promU32 u) (shrI (shr (wm * lo) nbits + wm * hi) (j - nbits))

/-- `indexforexp(e) = div(e + 15, 16)`, `base/ryu/utils.jl:55` (`e ≥ 0` at every call). -/
def indexforexp (e : JInt .i64) : Jl (JInt .i64) := JInt.div (e + JInt.lit .i64 15) (JInt.lit .i64 16)

/-- `pow10bitsforindex(idx) = 16 * idx + 120`, `base/ryu/utils.jl:56`. -/
def pow10bitsforindex (idx : JInt .i64) : JInt .i64 := JInt.lit .i64 16 * idx + JInt.lit .i64 120

/-- `lengthforindex(idx)`, `base/ryu/utils.jl:57`:
`div(((Int64(16 * idx) * 1292913986) >> 32) + 1 + 16 + 8, 9)`. -/
def lengthforindex (idx : JInt .i64) : Jl (JInt .i64) :=
  JInt.div (ashr (JInt.lit .i64 16 * idx * JInt.lit .i64 1292913986) 32 + JInt.lit .i64 1 +
    JInt.lit .i64 16 + JInt.lit .i64 8) (JInt.lit .i64 9)

/-- `Base.power_by_squaring(UInt64(5), p; mul = *%)`: `5^p mod 2^64` for `p ≥ 0`. -/
def wrappedPow5 (p : JInt .i64) : JInt .u64 := JInt.wrap .u64 (5 ^ p.val.toNat)

/-- `pow5(x, p) = x % wrapped_pow == 0`, `base/ryu/utils.jl:64-80`; `x::UInt64`.
`wrapped_pow` is never zero (it is odd), so `%` does not throw. -/
def pow5 (x : JInt .u64) (p : JInt .i64) : Bool :=
  x.val % (wrappedPow5 p).val == 0

/-- `Int64(1) << p` for `p ≥ 0` (`shl_int`): zero once the count reaches 64. -/
def shlOne64 (p : Nat) : JInt .i64 := JInt.wrap .i64 (if p < 64 then 2 ^ p else 0)

/-- `pow2(x, p) = (x & ((Int64(1) << p) - 1)) == 0`, `base/ryu/utils.jl:87`, for an
unsigned `x` (`UInt64` or `UInt32`) and `p ≥ 0`. `x & mask` reinterprets the `Int64`
mask in the common type, whose low bits are the two's-complement bits of the mask. -/
def pow2 {u : IntTy} (x : JInt u) (p : Nat) : Bool :=
  let mask : JInt .i64 := shlOne64 p - JInt.lit .i64 1
  Nat.land x.val.toNat (mask.val % 2 ^ 64).toNat == 0

/-- `decimallength(v)`, `base/ryu/utils.jl:94-112` (the method for other integers). -/
def decimallength (v : Int) : Nat :=
  if v ≥ 10000000000000000 then 17 else if v ≥ 1000000000000000 then 16
  else if v ≥ 100000000000000 then 15 else if v ≥ 10000000000000 then 14
  else if v ≥ 1000000000000 then 13 else if v ≥ 100000000000 then 12
  else if v ≥ 10000000000 then 11 else if v ≥ 1000000000 then 10
  else if v ≥ 100000000 then 9 else if v ≥ 10000000 then 8
  else if v ≥ 1000000 then 7 else if v ≥ 100000 then 6
  else if v ≥ 10000 then 5 else if v ≥ 1000 then 4
  else if v ≥ 100 then 3 else if v ≥ 10 then 2 else 1

/-- `decimallength(v::UInt32)`, `base/ryu/utils.jl:113-123`. -/
def decimallength32 (v : JInt .u32) : Nat :=
  let v := v.val
  if v ≥ 100000000 then 9 else if v ≥ 10000000 then 8
  else if v ≥ 1000000 then 7 else if v ≥ 100000 then 6
  else if v ≥ 10000 then 5 else if v ≥ 1000 then 4
  else if v ≥ 100 then 3 else if v ≥ 10 then 2 else 1

/-- `decimallength(v::UInt16)`, `base/ryu/utils.jl:124-130`. -/
def decimallength16 (v : JInt .u16) : Nat :=
  let v := v.val
  if v ≥ 10000 then 5 else if v ≥ 1000 then 4
  else if v ≥ 100 then 3 else if v ≥ 10 then 2 else 1


/-! ### 256-bit products and `mod1e9` -/

/-- `umul256(a, bHi, bLo)`, `base/ryu/utils.jl:153-176`. Returns `(pLo, pHi)`. -/
def umul256 (a : JInt .u128) (bHi bLo : JInt .u64) : JInt .u128 × JInt .u128 :=
  let aLo : JInt .u64 := JInt.rem .u64 a
  let aHi : JInt .u64 := JInt.rem .u64 (shr a 64)
  let b00 : JInt .u128 := JInt.rem .u128 aLo * JInt.rem .u128 bLo
  let b01 : JInt .u128 := JInt.rem .u128 aLo * JInt.rem .u128 bHi
  let b10 : JInt .u128 := JInt.rem .u128 aHi * JInt.rem .u128 bLo
  let b11 : JInt .u128 := JInt.rem .u128 aHi * JInt.rem .u128 bHi
  let b00Lo : JInt .u64 := JInt.rem .u64 b00
  let b00Hi : JInt .u64 := JInt.rem .u64 (shr b00 64)
  let mid1 : JInt .u128 := b10 + JInt.rem .u128 b00Hi
  let mid1Lo : JInt .u64 := JInt.rem .u64 mid1
  let mid1Hi : JInt .u64 := JInt.rem .u64 (shr mid1 64)
  let mid2 : JInt .u128 := b01 + JInt.rem .u128 mid1Lo
  let mid2Lo : JInt .u64 := JInt.rem .u64 mid2
  let mid2Hi : JInt .u64 := JInt.rem .u64 (shr mid2 64)
  let pHi : JInt .u128 := b11 + JInt.rem .u128 mid1Hi + JInt.rem .u128 mid2Hi
  let pLo : JInt .u128 := bor (shl (JInt.rem .u128 mid2Lo) 64) (JInt.rem .u128 b00Lo)
  (pLo, pHi)

/-- `umul256_hi(a, bHi, bLo) = umul256(a, bHi, bLo)[2]`, `base/ryu/utils.jl:183`. -/
def umul256Hi (a : JInt .u128) (bHi bLo : JInt .u64) : JInt .u128 := (umul256 a bHi bLo).2

/-- `mod1e9(v::UInt128)`, `base/ryu/utils.jl:185-191`. -/
def mod1e9 (v : JInt .u128) : JInt .u32 :=
  let multiplied := umul256Hi v (JInt.lit .u64 0x89705F4136B4A597) (JInt.lit .u64 0x31680A88F8953031)
  let shifted : JInt .u32 := JInt.rem .u32 (shr multiplied 29)
  JInt.rem .u32 v - JInt.lit .u32 1000000000 * shifted

/-- `mulshiftmod1e9(m, mula, mulb, mulc, j)`, `base/ryu/utils.jl:198-206`, with
`m::UInt64` and `UInt64` limbs (as at every call site, `base/ryu/fixed.jl:60,110`
and `base/ryu/exp.jl:68,108`). -/
def mulshiftmod1e9 (m mula mulb mulc : JInt .u64) (j : Int) : JInt .u32 :=
  let b0 : JInt .u128 := JInt.rem .u128 m * JInt.rem .u128 mula
  let b1 : JInt .u128 := JInt.rem .u128 m * JInt.rem .u128 mulb
  let b2 : JInt .u128 := JInt.rem .u128 m * JInt.rem .u128 mulc
  let mid : JInt .u128 := b1 + JInt.rem .u128 (JInt.rem .u64 (shr b0 64))
  let s1 : JInt .u128 := b2 + JInt.rem .u128 (JInt.rem .u64 (shr mid 64))
  let v := shrI s1 (j - 128)
  mod1e9 v

/-! ### Output helpers -/

/-- The sign bit and NaN test of a float, by its bit pattern of `bits` bits. -/
structure FloatBits where
  signbit : Bool
  isnan : Bool

/-- `append_sign(x, plus, space, buf, pos)`, `base/ryu/utils.jl:208-220`: the
written byte (if any) and the returned position. -/
def appendSign (x : FloatBits) (plus space : Bool) (pos : Int) : Option Nat × Int :=
  if x.signbit && !x.isnan then (some 45, pos + 1)
  else if plus then (some 43, pos + 1)
  else if space then (some 32, pos + 1)
  else (none, pos)


/-- `append_d_digits(olength, digits, buf, pos, decchar)`, `base/ryu/utils.jl:225-230`. -/
def appendDDigits (olength : Nat) (digits : Nat) (buf : Buf) (pos : Int) (decchar : Nat) : Buf × Int :=
  let r := appendCDigits olength digits buf (pos + 1)
  let buf := r.1.set pos (r.1 (pos + 1))
  let buf := buf.set (pos + 1) decchar
  (buf, r.2)

/-! ### Tables -/

/-- `ndigits(n, base = 2)` for `n > 0`. -/
def nbits (n : Nat) : Nat := Nat.log2 n + 1

/-- `pow5invsplit(T, i)`, `base/ryu/utils.jl:279-284`:
`W(div(big(1) << (ndigits(pow, base=2) - 1 + pow5_inv_bitcount(T)), pow) + 1)`. -/
def pow5invsplit (T : FT) (i : Nat) : Jl (JInt T.wide) :=
  let pow := 5 ^ i
  let inv := 2 ^ (nbits pow - 1 + pow5InvBitcount T) / pow + 1
  JInt.convert (T.wide.name) T.wide inv

/-- `pow5split(T, i)`, `base/ryu/utils.jl:308-312`: `W(pow >> (ndigits(pow, base=2) -
pow5_bitcount(T)))`; a negative `BigInt` shift count shifts left. -/
def pow5split (T : FT) (i : Nat) : Jl (JInt T.wide) :=
  let pow := 5 ^ i
  let s : Int := (nbits pow : Int) - pow5Bitcount T
  JInt.convert (T.wide.name) T.wide (if s ≥ 0 then pow / 2 ^ s.toNat else pow * 2 ^ (-s).toNat)

/-- The last table index of `pow5invsplit_lookup(T, ·)`, `base/ryu/utils.jl:294-295`:
`log10pow2(exponent_max(T) - precision(T) - 1)`. -/
def invImax (T : FT) : Int := (log10pow2 (JInt.lit .i64 (T.exponentMax - T.precision - 1))).val

/-- The last table index of `pow5split_lookup(T, ·)`, `base/ryu/utils.jl:322-323`:
`1 - e2_min - log10pow5(-e2_min)` with `e2_min = 1 - exponent_bias(T) - significand_bits(T) - 2`. -/
def splitImax (T : FT) : Int :=
  let e2min := 1 - T.exponentBias - T.significandBits - 2
  1 - e2min - (log10pow5 (JInt.lit .i64 (-e2min))).val

/-- The table `pow5invsplit_table_T`: `Tuple(Any[pow5invsplit(T, i) for i = 0:i_max])`
(every element converts, as the table builds at bootstrap). -/
def invTable (T : FT) : List (Jl (JInt T.wide)) :=
  (List.range ((invImax T).toNat + 1)).map (pow5invsplit T)

def splitTable (T : FT) : List (Jl (JInt T.wide)) :=
  (List.range ((splitImax T).toNat + 1)).map (pow5split T)

/-- `pow5invsplit_lookup(T, i) = @inbounds(table[i+1])`, `base/ryu/utils.jl:297`;
`none` is an access outside the table. -/
def pow5invsplitLookup (T : FT) (i : Int) : Option (Jl (JInt T.wide)) :=
  if 0 ≤ i then (invTable T)[i.toNat]? else none

/-- `pow5split_lookup(T, i)`, `base/ryu/utils.jl:325`. -/
def pow5splitLookup (T : FT) (i : Int) : Option (Jl (JInt T.wide)) :=
  if 0 ≤ i then (splitTable T)[i.toNat]? else none

/-- `mulshiftinvsplit(T, mv, mp, mm, i, j)`, `base/ryu/utils.jl:132-138`, with the
table entry `mul`. -/
def mulshiftinvsplit (u : IntTy) (mul : JInt (widenTy u)) (mv mp mm : JInt u) (j : Int) :
    JInt (promU32 u) × JInt (promU32 u) × JInt (promU32 u) :=
  (mulshift u mv mul j, mulshift u mp mul j, mulshift u mm mul j)

/-- `mulshiftsplit(T, mv, mp, mm, i, j)`, `base/ryu/utils.jl:140-146`. -/
def mulshiftsplit (u : IntTy) (mul : JInt (widenTy u)) (mv mp mm : JInt u) (j : Int) :
    JInt (promU32 u) × JInt (promU32 u) × JInt (promU32 u) :=
  (mulshift u mv mul j, mulshift u mp mul j, mulshift u mm mul j)

/-! ### `generateinversetables()`, `base/ryu/utils.jl:242-268` -/

/-- The state of the `while true` loop for one `idx`: the table so far, `i`, and
`MIN_BLOCK_2[idx + 1]` (`none` while it is `0xff`). -/
structure InvState where
  split : List (Nat × Nat × Nat)
  minBlock : Option Nat
  deriving Repr

def bigMask : Nat := 2 ^ 64 - 1

/-- `v = ((big(10)^(9 * (i + 1)) >> (-(120 - 16 * idx))) % (big(10)^9) << (120 + 16))`;
a negative `BigInt` shift count shifts left. -/
def invV (idx i : Nat) : Nat :=
  let p := 10 ^ (9 * (i + 1))
  let s : Int := -(120 - 16 * (idx : Int))
  let q := if s ≥ 0 then p / 2 ^ s.toNat else p * 2 ^ (-s).toNat
  q % (10 ^ 9 * 2 ^ (120 + 16))

/-- The `while true` loop body, `base/ryu/utils.jl:250-262`, on fuel. -/
def invLoop (idx : Nat) : Nat → Nat → InvState → InvState
  | 0, _, s => s
  | fuel + 1, i, s =>
    let v := invV idx i
    if s.minBlock.isNone && (v * 2 ^ (54 + 8)) / 2 ^ 128 == 0 then invLoop idx fuel (i + 1) s
    else
      let s := if s.minBlock.isNone then { s with minBlock := some i } else s
      if v == 0 then s
      else invLoop idx fuel (i + 1)
        { s with split := s.split ++ [((v &&& bigMask) % 2 ^ 64, ((v >>> 64) &&& bigMask) % 2 ^ 64,
          ((v >>> 128) &&& bigMask) % 2 ^ 64)] }

/-- One iteration `idx` of the `for` loop: push the current length of `POW10_SPLIT_2` to
`POW10_OFFSET_2`, run the `while` loop from `i = 0`, push `MIN_BLOCK_2[idx + 1]`.
`fuel` bounds the `while` loop. -/
def genStep (fuel : Nat) (acc : List Nat × List Nat × List (Nat × Nat × Nat)) (idx : Nat) :
    List Nat × List Nat × List (Nat × Nat × Nat) :=
  let s := invLoop idx fuel 0 ⟨acc.2.2, none⟩
  (acc.1 ++ [acc.2.2.length], acc.2.1 ++ [s.minBlock.getD 0xff], s.split)

/-- The results `(POW10_OFFSET_2, MIN_BLOCK_2, POW10_SPLIT_2)` for `idx = 0:n-1`; Julia
uses `n = 68`. After the loop the final offset and a `MIN_BLOCK_2` of 0 are pushed. -/
def generateinversetables (n fuel : Nat) : List Nat × List Nat × List (Nat × Nat × Nat) :=
  let r := (List.range n).foldl (genStep fuel) ([], [], [])
  (r.1 ++ [r.2.2.length], r.2.1 ++ [0], r.2.2)

end JuliaLean.MiscCov.RyuUtils

namespace JuliaLean.Printf

open JuliaLean JuliaLean.Float
/-- A digit of `b"0123456789abcdef"` or `b"0123456789ABCDEF"`, `Printf.jl:281-282`. -/
def hexdig (upper : Bool) (d : Nat) : Nat := if d < 10 then 48 + d else (if upper then 55 else 87) + d

/-- The `k` low base-`b` digits of `m`, most significant first. -/
def lowDigits (b : Nat) (upper : Bool) : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, m => lowDigits b upper k (m / b) ++ [hexdig upper (m % b)]

/-- Number of base-`b` digits of `m`, at least one (`fuel` bounds the recursion). -/
def ndig (b : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, m => if m < b then 1 else 1 + ndig b fuel (m / b)

/-- `ndigits(m, base=b, pad=1)` for `b ≥ 2`. -/
def ndigits (b m : Nat) : Nat := ndig b m m

/-- `string(m, base=b)` digits. -/
def digits (b : Nat) (upper : Bool) (m : Nat) : Bytes := lowDigits b upper (ndigits b m) m

/-! ## Decimal rounding of exact values (the specification of Ryu and MPFR digits) -/

/-- `n / d` rounded to an integer, ties to even. -/
def rhe (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q

/-- `n / d * 10^k` rounded to an integer, ties to even. -/
def rheScaled (n d : Nat) (k : Int) : Nat :=
  if k ≥ 0 then rhe (n * 10 ^ k.toNat) d else rhe n (d * 10 ^ (-k).toNat)

/-- `floor(log10(n / d))` for positive `n`, `d`. -/
def flog10 (n d : Nat) : Int :=
  let k : Int := (ndigits 10 n : Int) - (ndigits 10 d : Int)
  let below := if k ≥ 0 then decide (n < d * 10 ^ k.toNat) else decide (n * 10 ^ (-k).toNat < d)
  if below then k - 1 else k

/-- Positive `n / d` rounded to `prec + 1` significant digits: `(m, e)` with
`10^prec ≤ m < 10^(prec+1)` and value `≈ m * 10^(e - prec)`. -/
def sci (n d prec : Nat) : Nat × Int :=
  let e := flog10 n d
  let m := rheScaled n d ((prec : Int) - e)
  if m == 10 ^ (prec + 1) then (10 ^ prec, e + 1) else (m, e)

/-- Zero characters. -/
def zeros (n : Nat) : Bytes := List.replicate n 48

/-- `m` written with at least `k` digits. -/
def padDigits (k m : Nat) : Bytes := let ds := digits 10 false m; zeros (k - ds.length) ++ ds

end JuliaLean.Printf
/-!
Float64 shortest printing, `base/ryu/shortest.jl` and `base/ryu/utils.jl` at
master `bbfa0ce4150` (unchanged in behaviour from 1.13.2, which differs only in
spelling `-%`/`*%` as `-`/`*`, with the same wrapping semantics).

`reduceShortest` mirrors `reduce_shortest(::Float64, maxsignif)`
(`base/ryu/shortest.jl:7-226`) branch by branch, with `T == Float64`: the
`Float32`/`Float16` refinements of `b_lastdigit` (lines 51-57, 74-80) are not
taken. Unsigned arithmetic is `JInt .u64`/`.u128`/`.u32`, wrapping exactly where
Julia wraps. The exponent bookkeeping (`e`, `ef`, `e2`, `q`, `k`, `i`, `j`,
`e10`) is `Int` arithmetic on values bounded by a few thousand, so Julia's `Int`
never wraps there; `>>` on these nonnegative `Int`s is floor division.

Each Julia `while true` loop is a fuel-bounded recursion. Every iteration divides
a `UInt64` by ten, so 24 iterations exceed the at most 20 a nonzero `UInt64`
allows; the remaining loops stop once a value's last digit is nonzero.

The lookup tables `pow5invsplit_lookup`/`pow5split_lookup` are the closed
formulas that generate them (`base/ryu/utils.jl:279-326`), evaluated directly.
`writeshortest` mirrors `base/ryu/shortest.jl:228-464` for `Float64`, for which
`typed` has no effect. The output is the list of written bytes.
-/

namespace JuliaLean.ParsePrint.Ryu

open JuliaLean JuliaLean.Float JuliaLean.ParsePrint
abbrev U64 := JInt .u64
abbrev U128 := JInt .u128
abbrev U32 := JInt .u32

/-- `base/ryu/utils.jl:27`: `floor(log10(2^e))`. -/
def log10pow2 (e : Int) : Int := (e * 78913) / 2^18
/-- `base/ryu/utils.jl:35`: `floor(log10(5^e))`. -/
def log10pow5 (e : Int) : Int := (e * 732923) / 2^20
/-- `base/ryu/utils.jl:42`: `ceil(log2(5^e))`, one for zero. -/
def pow5bits (e : Int) : Int := ((e * 1217359) / 2^19) + 1

/-- `ndigits(n, base=2)` for a positive integer. -/
def nbits (n : Nat) : Nat := Nat.log2 n + 1

/-- `base/ryu/utils.jl:279-284` with `pow5_inv_bitcount(Float64) = 122`. -/
def pow5invsplit (i : Int) : U128 :=
  let pow := 5 ^ i.toNat
  JInt.wrap .u128 (2 ^ (nbits pow - 1 + 122) / pow + 1)

/-- `base/ryu/utils.jl:308-312` with `pow5_bitcount(Float64) = 121`; a negative
`BigInt` shift is a left shift. -/
def pow5split (i : Int) : U128 :=
  let pow := 5 ^ i.toNat
  let s : Int := (nbits pow : Int) - 121
  JInt.wrap .u128 (if s ≥ 0 then pow / 2 ^ s.toNat else pow * 2 ^ (-s).toNat)

/-- `base/ryu/utils.jl:49-53`: `(m * mul) >> j` through a 128-bit product; `j ≥ 64`. -/
def mulshift (m : U64) (mul : U128) (j : Int) : U64 :=
  let wm : U128 := JInt.rem .u128 m
  let lo : U128 := JInt.rem .u128 (JInt.rem .u64 mul)
  let hi : U128 := shr mul 64
  JInt.rem .u64 (shrI (shr (wm * lo) 64 + wm * hi) (j - 64))

/-- `base/ryu/utils.jl:64-80`: wrapping `5^p` by squaring is `5^p mod 2^64`, never zero. -/
def pow5 (x : U64) (p : Int) : Bool :=
  x.val % (JInt.wrap .u64 (5 ^ p.toNat)).val == 0

/-- `base/ryu/utils.jl:87`: `(x & ((Int64(1) << p) - 1)) == 0` for `0 ≤ p < 63`. -/
def pow2 (x : U64) (p : Int) : Bool :=
  (band x (JInt.rem .u64 (JInt.lit .i64 (2 ^ p.toNat - 1)))).val == 0

/-- `base/ryu/utils.jl:94-112`. -/
def decimallength (v : U64) : Nat :=
  let v := v.val
  if v ≥ 10000000000000000 then 17 else if v ≥ 1000000000000000 then 16
  else if v ≥ 100000000000000 then 15 else if v ≥ 10000000000000 then 14
  else if v ≥ 1000000000000 then 13 else if v ≥ 100000000000 then 12
  else if v ≥ 10000000000 then 11 else if v ≥ 1000000000 then 10
  else if v ≥ 100000000 then 9 else if v ≥ 10000000 then 8
  else if v ≥ 1000000 then 7 else if v ≥ 100000 then 6
  else if v ≥ 10000 then 5 else if v ≥ 1000 then 4
  else if v ≥ 100 then 3 else if v ≥ 10 then 2 else 1


/-! ### Output bytes -/


def chDot : Nat := 46
def chMinus : Nat := 45
def chPlus : Nat := 43
def chSpace : Nat := 32
def chE : Nat := 101

/-- `base/ryu/utils.jl:208-220`: the sign, suppressed for NaNs. -/
def appendSign (x : F64) (plus space : Bool) : List Nat :=
  if F64.signbit x && !F64.isnan x then [chMinus]
  else if plus then [chPlus] else if space then [chSpace] else []



/-- `n` zero characters. -/
def zeros (n : Nat) : List Nat := List.replicate n chZero
end JuliaLean.ParsePrint.Ryu

import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.parsers.Parsers
import JuliaLean.base.parsers.ints

/-!
# Model of `base/parsers/floats.jl`

The floating-point parser of `Base.Parsers` in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`,
behind `parse` and `tryparse` for `Float16`, `Float32` and `Float64`. A byte buffer is the list of
its bytes, read as in `JuliaLean.base.parsers.ints`; a `Vector{UInt64}` of limbs is a list,
updated by returning the new list. Integer arithmetic is the installed `JuliaLean.base.int`
model at Julia's types (`Int` arithmetic wraps as `Int64`), and floating-point arithmetic,
conversion and reinterpretation are the installed `JuliaLean.base.float` model.
-/

namespace JuliaLean.base.parsers.floats

open JuliaLean
open JuliaLean.Promotion hiding FV FTy
open JuliaLean.base.io (M whileLoop liftJl)
open JuliaLean.base.float (FV)
open JuliaLean.base.parsers.Parsers
open JuliaLean.base.parsers.ints

abbrev U128 := JInt .u128

def u128 (n : Int) : U128 := JInt.lit .u128 n
/-- `x % T`. -/
def remT {t : IntTy} (u : IntTy) (x : JInt t) : JInt u := JuliaLean.base.int.remT u x
/-- A `Bool` promoted to an integer type. -/
def ofBool (t : IntTy) (b : Bool) : JInt t := JInt.lit t (if b then 1 else 0)
/-- `x[i]` of a list, one-based, with a default outside it (`@inbounds` reads in range, `get`). -/
def getL {α : Type} (xs : List α) (i : I64) (d : α) : α := xs.getD (i.val - 1).toNat d
def setL {α : Type} (xs : List α) (i : I64) (v : α) : List α := xs.set (i.val - 1).toNat v

section
variable {World : Type}

/-- `T(x)` for an integer type `T`: `InexactError` when `x` does not fit. -/
def convertTo (name : String) (t : IntTy) {s : IntTy} (x : JInt s) : M World (JInt t) :=
  liftJl (JInt.convert name t x.val)

/--
Julia source: base/parsers/floats.jl:1-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

# Decimal numbers are converted with Clinger's exact fast path when the significand and
# the power of ten are both exact in `T`, and otherwise with the Eisel–Lemire algorithm,
# as implemented in fast_float: one or two 64×64-bit products with a 128-bit power of five
# give the correctly rounded result for any significand of at most 19 digits (Mushtak &
# Lemire, "Fast Number Parsing Without Fallback"). A longer significand is rounded from its
# first 19 digits, unless the value is so close to a midpoint between two floats that all of
# its digits must be compared with the midpoint. A hexadecimal float is a binary fraction,
# so its first 16 hexadecimal digits, and whether any later one is nonzero, decide it.

# Arithmetic on unsigned integers of any size, stored as little-endian 64-bit limbs

# x = x * m + a
function mulsmall!(x::Vector{UInt64}, m::UInt64, a::UInt64 = zero(UInt64))
    for k in eachindex(x)
        p = widemul(x[k], m) + a
        x[k] = p % UInt64
        a = (p >> 64) % UInt64
    end
    iszero(a) || push!(x, a)
    return x
end
```
-/
def mulsmall (x : List U64) (m : U64) (a : U64 := u64 0) : List U64 :=
  let (x, a) := x.foldl (fun ((done, a) : List U64 × U64) xk =>
    let p := add (mul (widen .u128 xk) (widen .u128 m)) (widen .u128 a)
    (done ++ [remT .u64 p], remT .u64 (shr p (lit64 64)))) ([], a)
  if a.val == 0 then x else x ++ [a]

/--
Julia source: base/parsers/floats.jl:24-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# x = x ÷ 5
function div5!(x::Vector{UInt64})
    r = zero(UInt128)
    for k in reverse(eachindex(x))
        n = r << 64 | x[k]
        x[k] = (n ÷ 5) % UInt64
        r = n % 5
    end
    return x
end
```
-/
def div5 (x : List U64) : M World (List U64) := do
  let mut x := x
  let mut r := u128 0
  for k in (indexRange (lit64 1) (lit64 x.length)).reverse do
    let n := bor (shl r (lit64 64)) (widen .u128 (getL x k (u64 0)))
    x := setL x k (remT .u64 (← liftJl (JuliaLean.base.int.div_UInt128 n (u128 5))))
    r := ← liftJl (JuliaLean.base.int.rem_UInt128 n (u128 5))
  return x

/--
Julia source: base/parsers/floats.jl:34-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The 128 most significant bits of x
function top128(x::Vector{UInt64})
    k = findlast(!iszero, x)
    s = leading_zeros(x[k])
    limb(i) = i >= 1 ? x[i] : zero(UInt64)
    hi = s == 0 ? limb(k) : limb(k) << s | limb(k - 1) >> (64 - s)
    lo = s == 0 ? limb(k - 1) : limb(k - 1) << s | limb(k - 2) >> (64 - s)
    return UInt128(hi) << 64 | lo
end

```
-/
def top128 (x : List U64) : M World U128 := do
  let k ← match ((indexRange (lit64 1) (lit64 x.length)).reverse.find?
      (fun k => (getL x k (u64 0)).val != 0)) with
    | some k => pure k
    | none => throw (.jl (.methodError "getindex"))
  let s := JuliaLean.base.int.leading_zeros (getL x k (u64 0))
  let limb := fun (i : I64) => if i.val ≥ 1 then getL x i (u64 0) else u64 0
  let hi := if s.val == 0 then limb k
    else bor (shl (limb k) s) (shr (limb (sub k (lit64 1))) (sub (lit64 64) s))
  let lo := if s.val == 0 then limb (sub k (lit64 1))
    else bor (shl (limb (sub k (lit64 1))) s) (shr (limb (sub k (lit64 2))) (sub (lit64 64) s))
  return bor (shl (widen .u128 hi) (lit64 64)) (widen .u128 lo)

/--
Julia source: base/parsers/floats.jl:44-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# fast_float's 128-bit significands of 5^q, for every q a `Float64` needs: the top 128 bits
# of 5^q, or of floor(2^1024 / 5^-q) for q < 0, plus one for -27 <= q < 0. The proof that
# no fallback is needed holds for exactly these values.
const POW5_MIN, POW5_MAX = -342, 308
```
-/
def POW5_MIN : I64 := lit64 (-342)
def POW5_MAX : I64 := lit64 308

/--
Julia source: base/parsers/floats.jl:48-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pow5table()
    table = Vector{UInt128}(undef, POW5_MAX - POW5_MIN + 1)
    x = UInt64[1]
    for q in 0:POW5_MAX
        table[q - POW5_MIN + 1] = top128(x)
        mulsmall!(x, UInt64(5))
    end
    x = zeros(UInt64, 17)
    x[17] = 1
    for q in -1:-1:POW5_MIN
        table[q - POW5_MIN + 1] = top128(div5!(x)) + (q >= -27)
    end
    return table
end
```
-/
def pow5table : M World (List U128) := do
  let mut positive : List U128 := []
  let mut x : List U64 := [u64 1]
  for _q in indexRange (lit64 0) POW5_MAX do
    positive := positive ++ [← top128 x]
    x := mulsmall x (u64 5)
  let mut y : List U64 := (List.replicate 16 (u64 0)) ++ [u64 1]
  let mut negative : List U128 := []
  for q in (indexRange POW5_MIN (lit64 (-1))).reverse do
    y ← div5 y
    negative := (add (← top128 y) (ofBool .u128 (q.val ≥ -27))) :: negative
  return negative ++ positive

/--
Julia source: base/parsers/floats.jl:62-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const POW5 = pow5table()

```
-/
def POW5 : M World (List U128) := pow5table

/-- Julia's `IEEEFloat` types. -/
abbrev FTy := JuliaLean.base.float.FTy

/--
Julia source: base/parsers/floats.jl:64-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The powers of ten outside of which every nonzero 64-bit significand rounds to zero or
# overflows, and those for which a product can fall exactly halfway between two floats.
pow10range(::Type{Float64}) = (-342, 308)
pow10range(::Type{Float32}) = (-64, 38)
pow10range(::Type{Float16}) = (-26, 4)
```
-/
def pow10range : FTy → I64 × I64
  | .f64 => (lit64 (-342), lit64 308)
  | .f32 => (lit64 (-64), lit64 38)
  | .f16 => (lit64 (-26), lit64 4)

/--
Julia source: base/parsers/floats.jl:69-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
halfwayrange(::Type{Float64}) = (-4, 23)
halfwayrange(::Type{Float32}) = (-17, 10)
halfwayrange(::Type{Float16}) = (-26, 5)

```
-/
def halfwayrange : FTy → I64 × I64
  | .f64 => (lit64 (-4), lit64 23)
  | .f32 => (lit64 (-17), lit64 10)
  | .f16 => (lit64 (-26), lit64 5)

/--
Julia source: base/parsers/floats.jl:73-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function mul64(a::UInt64, b::UInt64)
    p = widemul(a, b)
    return (p >> 64) % UInt64, p % UInt64
end

```
-/
def mul64 (a b : U64) : U64 × U64 :=
  let p := mul (widen .u128 a) (widen .u128 b)
  (remT .u64 (shr p (lit64 64)), remT .u64 p)

def significand_bits (T : FTy) : I64 := JuliaLean.base.float.significand_bits T
def exponent_bias (T : FTy) : I64 := JuliaLean.base.float.exponent_bias T
def exponent_raw_max (T : FTy) : I64 := JuliaLean.base.float.exponent_raw_max T

/--
Julia source: base/parsers/floats.jl:78-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The bits of a `T` from its significand m, of `significand_bits(T) + 1` bits or one more
# if rounding carried, and its biased exponent e: those of infinity if it overflows. For
# e <= 0, m is all of a subnormal's bits, which are floatmin's if rounding carried.
@inline function packbits(::Type{T}, m::UInt64, e::Int) where {T}
    mbits = significand_bits(T)
    e <= 0 && return m
    if m >= UInt64(2) << mbits
        m >>= 1
        e += 1
    end
    e >= exponent_raw_max(T) && return UInt64(exponent_raw_max(T)) << mbits
    return UInt64(e) << mbits | (m & (UInt64(1) << mbits - 1))
end

```
-/
def packbits (T : FTy) (m : U64) (e : I64) : M World U64 := do
  let mbits := significand_bits T
  if e.val ≤ 0 then return m
  let (m, e) := if m.val ≥ (shl (u64 2) mbits).val then (shr m (lit64 1), add e (lit64 1))
    else (m, e)
  if e.val ≥ (exponent_raw_max T).val then
    return shl (← convertTo "UInt64" .u64 (exponent_raw_max T)) mbits
  return bor (shl (← convertTo "UInt64" .u64 e) mbits) (band m (sub (shl (u64 1) mbits) (u64 1)))

/--
Julia source: base/parsers/floats.jl:92-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The bits of the `T` nearest to w * 10^q, for w > 0: zero if it rounds to zero, and those
# of infinity if it overflows.
@inline function eisellemire(::Type{T}, w::UInt64, q::Int) where {T}
    mbits = significand_bits(T)
    qmin, qmax = pow10range(T)
    q < qmin && return zero(UInt64)
    q > qmax && return UInt64(exponent_raw_max(T)) << mbits
    lz = leading_zeros(w)
    w <<= lz
    # w * 5^q, refined by the next 64 bits of 5^q if the bits below those kept are all ones
    @inbounds p5 = POW5[q - POW5_MIN + 1]
    hi, lo = mul64(w, (p5 >> 64) % UInt64)
    mask = typemax(UInt64) >> (mbits + 3)
    if hi & mask == mask
        hi2, _ = mul64(w, p5 % UInt64)
        lo += hi2
        hi += lo < hi2
    end
    upper = (hi >> 63) % Int
    shift = upper + 64 - mbits - 3
    m = hi >> shift                              # the significand and a rounding bit
    e = ((217706 * q) >> 16) + 63 + upper - lz + exponent_bias(T)
    if e <= 0                                    # a subnormal has fewer significand bits
        shift += 1 - e
        shift >= 64 && return zero(UInt64)
        m = hi >> shift
    end
    hlo, hhi = halfwayrange(T)
    if lo <= 1 && hlo <= q <= hhi && m & 3 == 1 && m << shift == hi
        m &= ~UInt64(1)                          # exactly halfway: round to even
    end
    return packbits(T, (m + (m & 1)) >> 1, e)
end

```
-/
def eisellemire (T : FTy) (w : U64) (q : I64) : M World U64 := do
  let mbits := significand_bits T
  let (qmin, qmax) := pow10range T
  if q.val < qmin.val then return u64 0
  if q.val > qmax.val then return shl (← convertTo "UInt64" .u64 (exponent_raw_max T)) mbits
  let lz := JuliaLean.base.int.leading_zeros w
  let w := shl w lz
  let p5 := getL (← POW5) (add (sub q POW5_MIN) (lit64 1)) (u128 0)
  let (hi, lo) := mul64 w (remT .u64 (shr p5 (lit64 64)))
  let mask := shr (u64 0xffffffffffffffff) (add mbits (lit64 3))
  let (hi, lo) := if (band hi mask).val == mask.val then
      let (hi2, _) := mul64 w (remT .u64 p5)
      let lo := add lo hi2
      (add hi (ofBool .u64 (lo.val < hi2.val)), lo)
    else (hi, lo)
  let upper := remT .i64 (shr hi (lit64 63))
  let shift := sub (sub (add upper (lit64 64)) mbits) (lit64 3)
  let m := shr hi shift
  let e := add (sub (add (add (shr (mul (lit64 217706) q) (lit64 16)) (lit64 63)) upper) lz)
    (exponent_bias T)
  let mut shift := shift
  let mut m := m
  if e.val ≤ 0 then
    shift := add shift (sub (lit64 1) e)
    if shift.val ≥ 64 then return u64 0
    m := shr hi shift
  let (hlo, hhi) := halfwayrange T
  if lo.val ≤ 1 && hlo.val ≤ q.val && q.val ≤ hhi.val && (band m (u64 3)).val == 1 &&
      (shl m shift).val == hi.val then
    m := band m (bnot (u64 1))
  packbits T (shr (add m (band m (u64 1))) (lit64 1)) e

/-- The type `eltype(exactpow10s(T))` computes in. -/
def computeTy : FTy → FTy
  | .f64 => .f64
  | _ => .f32

/--
Julia source: base/parsers/floats.jl:126-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The powers of ten that are exact in `T`, for Clinger's fast path, in the type it computes
# in. `Float16` computes in `Float32`, which gives the same rounding for every w <= 2^11.
const EXACT_POW10_64 = ntuple(k -> Float64(UInt128(10)^(k - 1)), 23)
const EXACT_POW10_32 = ntuple(k -> Float32(UInt64(10)^(k - 1)), 11)
const EXACT_POW10_16 = EXACT_POW10_32[1:5]
```
-/
def EXACT_POW10_64 : List (FV .f64) :=
  (List.range 23).map (fun k => JuliaLean.base.float.Float64_UInt128 (JInt.wrap .u128 (10 ^ k)))
def EXACT_POW10_32 : List (FV .f32) :=
  (List.range 11).map (fun k => JuliaLean.base.float.float_BitUnsigned64 .f32 (JInt.wrap .u64 (10 ^ k)))
def EXACT_POW10_16 : List (FV .f32) := EXACT_POW10_32.take 5

/--
Julia source: base/parsers/floats.jl:131-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exactpow10s(::Type{Float64}) = EXACT_POW10_64
exactpow10s(::Type{Float32}) = EXACT_POW10_32
exactpow10s(::Type{Float16}) = EXACT_POW10_16

```
-/
def exactpow10s : (T : FTy) → List (FV (computeTy T))
  | .f64 => EXACT_POW10_64
  | .f32 => EXACT_POW10_32
  | .f16 => EXACT_POW10_16

/--
Julia source: base/parsers/floats.jl:135-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function frombits(::Type{T}, bits::UInt64, neg::Bool) where {T}
    iszero(bits) && return UNDERFLOW
    bits == UInt64(exponent_raw_max(T)) << significand_bits(T) && return OVERFLOW
    x = reinterpret(T, bits % uinttype(T))
    return neg ? -x : x
end

```
-/
def frombits (T : FTy) (bits : U64) (neg : Bool) : M World (ParseResult (FV T)) := do
  if bits.val == 0 then return .failure UNDERFLOW
  if bits.val == (shl (← convertTo "UInt64" .u64 (exponent_raw_max T)) (significand_bits T)).val then
    return .failure OVERFLOW
  let x := JuliaLean.base.float.bitcast_to_float T (remT T.uintTy bits)
  return .value (if neg then JuliaLean.base.float.neg_IEEEFloat x else x)

def zeroFloat (T : FTy) (neg : Bool) : FV T :=
  let z := JuliaLean.base.float.zero_float T
  if neg then JuliaLean.base.float.neg_IEEEFloat z else z

/--
Julia source: base/parsers/floats.jl:142-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# w * 10^q as a `T`, negated if `neg`, for a significand w of at most 19 digits
@inline function fromdecimal(::Type{T}, w::UInt64, q::Int, neg::Bool) where {T}
    iszero(w) && return neg ? -zero(T) : zero(T)
    p10 = exactpow10s(T)
    if abs(q) < length(p10) && w <= UInt64(1) << (significand_bits(T) + 1)
        # both factors are exact, so one rounding gives the nearest float
        S = eltype(p10)
        x = T(q < 0 ? S(w) / (@inbounds p10[1 - q]) : S(w) * (@inbounds p10[q + 1]))
        T === Float16 && isinf(x) && return OVERFLOW
        return neg ? -x : x
    end
    return frombits(T, eisellemire(T, w, q), neg)
end

```
-/
def fromdecimal (T : FTy) (w : U64) (q : I64) (neg : Bool) : M World (ParseResult (FV T)) := do
  if w.val == 0 then return .value (zeroFloat T neg)
  let p10 := exactpow10s T
  if (JuliaLean.base.int.abs q).val < p10.length &&
      w.val ≤ (shl (u64 1) (add (significand_bits T) (lit64 1))).val then
    let S := computeTy T
    let sw : FV S := JuliaLean.base.float.float_BitUnsigned64 S w
    let zero := JuliaLean.base.float.zero_float S
    let y := if q.val < 0 then JuliaLean.base.float.div_IEEEFloat sw (getL p10 (sub (lit64 1) q) zero)
      else JuliaLean.base.float.mul_IEEEFloat sw (getL p10 (add q (lit64 1)) zero)
    let x := JuliaLean.base.float.convertFloat T y
    if (match T with | .f16 => true | _ => false) && JuliaLean.base.float.isinf_IEEEFloat x then return .failure OVERFLOW
    return .value (if neg then JuliaLean.base.float.neg_IEEEFloat x else x)
  frombits T (← eisellemire T w q) neg

/--
Julia source: base/parsers/floats.jl:156-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# x = x * b^n, for b = 2 or 5
function mulpow!(x::Vector{UInt64}, b::Int, n::Int)
    step = b == 2 ? 63 : 27                      # the largest powers that fit in a limb
    while n > 0
        k = min(n, step)
        mulsmall!(x, UInt64(b)^k)
        n -= k
    end
    return x
end

```
-/
def mulpow (x : List U64) (b n : I64) : List U64 :=
  go x n (n.val.toNat + 1)
where
  go (x : List U64) (n : I64) : Nat → List U64
    | 0 => x
    | fuel + 1 =>
      if !(n.val > 0) then x
      else
        let step := if b.val == 2 then lit64 63 else lit64 27
        let k := if n.val ≤ step.val then n else step
        go (mulsmall x (JInt.wrap .u64 (b.val ^ k.val.toNat))) (sub n k) fuel

/--
Julia source: base/parsers/floats.jl:167-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# How the number with the digits in `buf[k:l]`, skipping a '.', times 10^p compares with the
# midpoint between the `T`s with bits `bits` and `bits + 1`: -1, 0 or 1. A midpoint has at
# most 768 significant digits, so the first 800 decide unless they are equal, when any later
# nonzero digit makes the number larger.
@noinline function cmpmidpoint(::Type{T}, buf::AbstractVector{UInt8}, k::Int, l::Int,
                               p::Int, bits::UInt64) where {T}
    x = UInt64[0]
    w, nw, n = zero(UInt64), 0, 0                # w has the nw digits not yet in x
    sticky = false
    for i in k:l
        d = (@inbounds buf[i]) - UInt8('0')
        d <= 0x09 || continue
        if n < 800
            w = 10w + d
            nw += 1
            n += 1
            nw == 19 && (mulsmall!(x, UInt64(10)^19, w); w = zero(UInt64); nw = 0)
        else
            sticky |= !iszero(d)
            p += 1
        end
    end
    mulsmall!(x, UInt64(10)^nw, w)
    # the midpoint is y * 2^e
    mbits = significand_bits(T)
    be = Int(bits >> mbits)                      # the biased exponent
    m = bits & (UInt64(1) << mbits - 1)
    be > 0 && (m |= UInt64(1) << mbits)
    e = max(be, 1) - exponent_bias(T) - mbits - 1
    y = UInt64[2m + 1]
    # x * 5^p * 2^p against y * 2^e, as integers
    p >= 0 ? mulpow!(x, 5, p) : mulpow!(y, 5, -p)
    e >= p ? mulpow!(y, 2, e - p) : mulpow!(x, 2, p - e)
    for i in max(length(x), length(y)):-1:1
        a, b = get(x, i, zero(UInt64)), get(y, i, zero(UInt64))
        a == b || return a < b ? -1 : 1
    end
    return Int(sticky)
end

```
-/
def cmpmidpoint (T : FTy) (buf : List Byte) (k l p : I64) (bits : U64) : M World I64 := do
  let mut x : List U64 := [u64 0]
  let mut w := u64 0
  let mut nw := lit64 0
  let mut n := lit64 0
  let mut sticky := false
  let mut p := p
  for i in indexRange k l do
    let d := sub (byteAt buf i) (u8 0x30)
    if !(d.val ≤ 9) then continue
    if n.val < 800 then
      w := add (mul (u64 10) w) (widen .u64 d)
      nw := add nw (lit64 1)
      n := add n (lit64 1)
      if nw.val == 19 then
        x := mulsmall x (JInt.wrap .u64 (10 ^ 19)) w
        w := u64 0
        nw := lit64 0
    else
      sticky := sticky || d.val != 0
      p := add p (lit64 1)
  x := mulsmall x (JInt.wrap .u64 (10 ^ nw.val.toNat)) w
  let mbits := significand_bits T
  let be ← convertTo "Int64" .i64 (shr bits mbits)
  let mut m := band bits (sub (shl (u64 1) mbits) (u64 1))
  if be.val > 0 then m := bor m (shl (u64 1) mbits)
  let e := sub (sub (sub (if be.val ≥ 1 then be else lit64 1) (exponent_bias T)) mbits) (lit64 1)
  let mut y : List U64 := [add (mul (u64 2) m) (u64 1)]
  if p.val ≥ 0 then x := mulpow x (lit64 5) p else y := mulpow y (lit64 5) (JuliaLean.base.int.neg p)
  if e.val ≥ p.val then y := mulpow y (lit64 2) (sub e p) else x := mulpow x (lit64 2) (sub p e)
  let top := lit64 (max x.length y.length)
  for i in (indexRange (lit64 1) top).reverse do
    let a := getL x i (u64 0)
    let b := getL y i (u64 0)
    if a.val != b.val then return (if a.val < b.val then lit64 (-1) else lit64 1)
  return ofBool .i64 sticky

/--
Julia source: base/parsers/floats.jl:207-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The decimal digits at the start of `buf[i:j]` accumulated into w, modulo 2^64, and the
# index after them
@inline function scandigits(buf::AbstractVector{UInt8}, i::Int, j::Int, w::UInt64)
    while j - i >= 7
        x = load8(buf, i)
        isdigits8(x) || break
        w = w * 100_000_000 + digits8(x)
        i += 8
    end
    while i <= j
        d = (@inbounds buf[i]) - UInt8('0')
        d <= 0x09 || break
        w = 10w + d
        i += 1
    end
    return w, i
end

```
-/
def scandigits (buf : List Byte) (i j : I64) (w : U64) : M World (U64 × I64) := do
  let (w, i) ← whileLoop (fun ((w, i) : U64 × I64) => do
    if !((sub j i).val ≥ 7) then return Sum.inl (w, i)
    let x := load8 buf i
    if !isdigits8 x then return Sum.inl (w, i)
    return Sum.inr (add (mul w (u64 100000000)) (digits8 x), add i (lit64 8))) (w, i)
  whileLoop (fun ((w, i) : U64 × I64) => do
    if !(i.val ≤ j.val) then return Sum.inl (w, i)
    let d := sub (byteAt buf i) (u8 0x30)
    if !(d.val ≤ 9) then return Sum.inl (w, i)
    return Sum.inr (add (mul (u64 10) w) (widen .u64 d), add i (lit64 1))) (w, i)

/--
Julia source: base/parsers/floats.jl:225-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The exponent at the start of `buf[i:j]`, decimal digits after an optional sign: its value,
# which stops growing far past every float's range, the index after it, and whether it has
# any digits
@inline function scanexponent(buf::AbstractVector{UInt8}, i::Int, j::Int)
    i <= j || return 0, i, false
    b = @inbounds buf[i]
    neg = b == UInt8('-')
    (neg || b == UInt8('+')) && (i += 1)
    e = 0
    k = i
    while i <= j
        d = (@inbounds buf[i]) - UInt8('0')
        d <= 0x09 || break
        e < 100_000_000 && (e = 10e + d)
        i += 1
    end
    return neg ? -e : e, i, i > k
end

```
-/
def scanexponent (buf : List Byte) (i j : I64) : M World (I64 × I64 × Bool) := do
  if !(i.val ≤ j.val) then return (lit64 0, i, false)
  let b := byteAt buf i
  let neg := b.val == 0x2d
  let i := if neg || b.val == 0x2b then add i (lit64 1) else i
  let k := i
  let (e, i) ← whileLoop (fun ((e, i) : I64 × I64) => do
    if !(i.val ≤ j.val) then return Sum.inl (e, i)
    let d := sub (byteAt buf i) (u8 0x30)
    if !(d.val ≤ 9) then return Sum.inl (e, i)
    let e := if e.val < 100000000 then add (mul (lit64 10) e) (widen .i64 d) else e
    return Sum.inr (e, add i (lit64 1))) (lit64 0, i)
  return (if neg then JuliaLean.base.int.neg e else e, i, i.val > k.val)

/--
Julia source: base/parsers/floats.jl:244-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The bits of the `T` nearest to (m + f) * 2^e, for m > 0 and some 0 <= f < 1 that is
# nonzero if `sticky`: zero if it rounds to zero, and those of infinity if it overflows.
@inline function hexbits(::Type{T}, m::UInt64, e::Int, sticky::Bool) where {T}
    mbits = significand_bits(T)
    lz = leading_zeros(m)
    m <<= lz
    e += 63 - lz + exponent_bias(T)              # the biased exponent of m's leading bit
    # the bits below the result's last one, more for a subnormal
    shift = 63 - mbits + max(1 - e, 0)
    shift > 64 && return zero(UInt64)            # below half of the smallest subnormal
    rest = m & (UInt64(1) << shift - 1)
    half = UInt64(1) << (shift - 1)
    m >>= shift
    m += rest > half || (rest == half && (sticky || isodd(m)))
    return packbits(T, m, e)
end

```
-/
def hexbits (T : FTy) (m : U64) (e : I64) (sticky : Bool) : M World U64 := do
  let mbits := significand_bits T
  let lz := JuliaLean.base.int.leading_zeros m
  let m := shl m lz
  let e := add e (add (sub (lit64 63) lz) (exponent_bias T))
  let below := sub (lit64 1) e
  let shift := add (sub (lit64 63) mbits) (if below.val ≥ 0 then below else lit64 0)
  if shift.val > 64 then return u64 0
  let rest := band m (sub (shl (u64 1) shift) (u64 1))
  let half := shl (u64 1) (sub shift (lit64 1))
  let m := shr m shift
  let m := add m (ofBool .u64 (rest.val > half.val ||
    (rest.val == half.val && (sticky || m.val % 2 == 1))))
  packbits T m e

/--
Julia source: base/parsers/floats.jl:261-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The hexadecimal digits at the start of `buf[i:j]`, shifted into m while it has room for
# them: the new m, the index after the last digit it took, whether a digit it had no room
# for is nonzero, and the index after the digits
@inline function scanhex(buf::AbstractVector{UInt8}, i::Int, j::Int, m::UInt64,
                         sticky::Bool)
    while j - i >= 7 && m >> 32 == 0             # eight at a time while m has room
        w = load8(buf, i)
        ishexdigits8(w) || break
        m = m << 32 | hexdigits8(w)
        i += 8
    end
    k = i
    while i <= j
        b = @inbounds buf[i]
        d, h = b - UInt8('0'), (b | 0x20) - UInt8('a')
        (d <= 0x09) | (h <= 0x05) || break
        if m >> 60 == 0
            m = m << 4 | ifelse(d <= 0x09, d, h + 0x0a)
            k += 1
        else
            sticky |= d != 0x00
        end
        i += 1
    end
    return m, k, sticky, i
end

```
-/
def scanhex (buf : List Byte) (i j : I64) (m : U64) (sticky : Bool) :
    M World (U64 × I64 × Bool × I64) := do
  let (m, i) ← whileLoop (fun ((m, i) : U64 × I64) => do
    if !((sub j i).val ≥ 7 && (shr m (lit64 32)).val == 0) then return Sum.inl (m, i)
    let w := load8 buf i
    if !ishexdigits8 w then return Sum.inl (m, i)
    return Sum.inr (bor (shl m (lit64 32)) (hexdigits8 w), add i (lit64 8))) (m, i)
  let k := i
  whileLoop (fun ((m, k, sticky, i) : U64 × I64 × Bool × I64) => do
    if !(i.val ≤ j.val) then return Sum.inl (m, k, sticky, i)
    let b := byteAt buf i
    let d := sub b (u8 0x30)
    let h := sub (bor b (u8 0x20)) (u8 0x61)
    if !(d.val ≤ 9 || h.val ≤ 5) then return Sum.inl (m, k, sticky, i)
    if (shr m (lit64 60)).val == 0 then
      let digit := if d.val ≤ 9 then d else add h (u8 0x0a)
      return Sum.inr (bor (shl m (lit64 4)) (widen .u64 digit), add k (lit64 1), sticky,
        add i (lit64 1))
    else
      return Sum.inr (m, k, sticky || d.val != 0, add i (lit64 1))) (m, k, sticky, i)

/--
Julia source: base/parsers/floats.jl:288-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A hexadecimal float, from the digits after its "0x"
@noinline function parsehex(::Type{T}, buf::AbstractVector{UInt8}, i::Int, j::Int,
                            neg::Bool) where {T}
    m, k, sticky, l = scanhex(buf, i, j, zero(UInt64), false)
    e = 4 * (l - k)                              # integer digits m had no room for
    nd = l - i
    if l <= j && (@inbounds buf[l]) == UInt8('.')
        m, k, sticky, i = scanhex(buf, l + 1, j, m, sticky)
        e -= 4 * (k - l - 1)                     # fraction digits in m
        nd += i - l - 1
        l = i
    end
    nd > 0 || return INVALID
    if l <= j && (@inbounds buf[l]) | 0x20 == UInt8('p')
        x, l, ok = scanexponent(buf, l + 1, j)
        ok || return INVALID
        e += x
    end
    l > j || return INVALID
    iszero(m) && return neg ? -zero(T) : zero(T)
    return frombits(T, hexbits(T, m, e, sticky), neg)
end

```
-/
def parsehex (T : FTy) (buf : List Byte) (i j : I64) (neg : Bool) :
    M World (ParseResult (FV T)) := do
  let (m, k, sticky, l) ← scanhex buf i j (u64 0) false
  let mut e := mul (lit64 4) (sub l k)
  let mut nd := sub l i
  let mut m := m
  let mut sticky := sticky
  let mut l := l
  if l.val ≤ j.val && (byteAt buf l).val == 0x2e then
    let (m', k', sticky', i') ← scanhex buf (add l (lit64 1)) j m sticky
    m := m'
    sticky := sticky'
    e := sub e (mul (lit64 4) (sub (sub k' l) (lit64 1)))
    nd := add nd (sub (sub i' l) (lit64 1))
    l := i'
  if !(nd.val > 0) then return .failure INVALID
  if l.val ≤ j.val && (bor (byteAt buf l) (u8 0x20)).val == 0x70 then
    let (x, l', ok) ← scanexponent buf (add l (lit64 1)) j
    if !ok then return .failure INVALID
    l := l'
    e := add e x
  if !(l.val > j.val) then return .failure INVALID
  if m.val == 0 then return .value (zeroFloat T neg)
  frombits T (← hexbits T m e sticky) neg

/-- The code units of an ASCII `String` literal. -/
def wordBytes (word : String) : List Byte := word.toUTF8.toList.map (fun b => u8 b.toNat)

/--
Julia source: base/parsers/floats.jl:311-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Whether the bytes from `buf[i]` on spell the lowercase ASCII `word`, in any case
@inline function matchword(buf::AbstractVector{UInt8}, i::Int, word::String)
    for k in 1:ncodeunits(word)
        (@inbounds buf[i + k - 1]) | 0x20 == codeunit(word, k) || return false
    end
    return true
end

```
-/
def matchword (buf : List Byte) (i : I64) (word : String) : Bool :=
  let bytes := wordBytes word
  (List.range bytes.length).all (fun k =>
    (bor (byteAt buf (sub (add i (lit64 (k + 1))) (lit64 1))) (u8 0x20)).val ==
      (bytes.getD k (u8 0)).val)

/--
Julia source: base/parsers/floats.jl:319-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Whether `b` may be inside the parentheses of `nan(...)`: an ASCII letter or digit, or '_'
isnanchar(b::UInt8) =
    b - UInt8('0') <= 0x09 || (b | 0x20) - UInt8('a') <= 0x19 || b == UInt8('_')

```
-/
def isnanchar (b : Byte) : Bool :=
  (sub b (u8 0x30)).val ≤ 9 || (sub (bor b (u8 0x20)) (u8 0x61)).val ≤ 0x19 || b.val == 0x5f

/--
Julia source: base/parsers/floats.jl:323-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The NaN for `buf[i:j]`, what follows "nan(" in `nan(chars)`. As in glibc, chars that C's
# `strtoull` reads in full as an unsigned integer (decimal, `0x` hexadecimal or `0` octal)
# set the NaN's payload, its significand bits below the quiet bit.
function nanpayload(::Type{T}, buf::AbstractVector{UInt8}, i::Int, j::Int) where {T}
    (@inbounds buf[j]) == UInt8(')') || return INVALID
    j -= 1
    for k in i:j
        isnanchar(@inbounds buf[k]) || return INVALID
    end
    base = 10
    if i <= j && (@inbounds buf[i]) == UInt8('0')
        base = 8
        if i < j && (@inbounds buf[i + 1]) | 0x20 == UInt8('x')
            i, base = i + 2, 16
        end
    end
    p = parseint(UInt64, buf, i, j, base, false)
    payload = p isa UInt64 ? p : p === OVERFLOW ? typemax(UInt64) : zero(UInt64)
    U = uinttype(T)
    mask = one(U) << (significand_bits(T) - 1) - one(U)
    return reinterpret(T, reinterpret(U, T(NaN)) | (payload % U & mask))
end

```
-/
def nanpayload (T : FTy) (buf : List Byte) (i j : I64) : M World (ParseResult (FV T)) := do
  if (byteAt buf j).val != 0x29 then return .failure INVALID
  let j := sub j (lit64 1)
  for k in indexRange i j do
    if !isnanchar (byteAt buf k) then return .failure INVALID
  let (i, base) :=
    if i.val ≤ j.val && (byteAt buf i).val == 0x30 then
      if i.val < j.val && (bor (byteAt buf (add i (lit64 1))) (u8 0x20)).val == 0x78 then
        (add i (lit64 2), lit64 16)
      else (i, lit64 8)
    else (i, lit64 10)
  let p ← parseintBits .u64 buf i j base false
  let payload := match p with
    | .value p => p
    | .failure f => if f = OVERFLOW then u64 0xffffffffffffffff else u64 0
  let U := T.uintTy
  let one := JInt.lit U 1
  let mask := sub (shl one (sub (significand_bits T) (lit64 1))) one
  let nan := JuliaLean.base.float.convertFloat T JuliaLean.base.float.NaN64
  return .value (JuliaLean.base.float.bitcast_to_float T
    (bor (JuliaLean.base.float.reinterpret_Unsigned nan) (band (remT U payload) mask)))

/--
Julia source: base/parsers/floats.jl:346-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `inf`, `infinity`, `nan` or `nan(chars)`, in any case
@noinline function parsespecial(::Type{T}, buf::AbstractVector{UInt8}, i::Int, j::Int,
                                neg::Bool) where {T}
    n = j - i + 1
    if (n == 3 && matchword(buf, i, "inf")) || (n == 8 && matchword(buf, i, "infinity"))
        x = T(Inf)
    elseif n == 3 && matchword(buf, i, "nan")
        x = T(NaN)
    elseif n > 4 && matchword(buf, i, "nan") && (@inbounds buf[i + 3]) == UInt8('(')
        x = nanpayload(T, buf, i + 4, j)
        x isa ParseFailure && return x
    else
        return INVALID
    end
    return neg ? -x : x
end

```
-/
def parsespecial (T : FTy) (buf : List Byte) (i j : I64) (neg : Bool) :
    M World (ParseResult (FV T)) := do
  let n := add (sub j i) (lit64 1)
  let mut x := JuliaLean.base.float.zero_float T
  if (n.val == 3 && matchword buf i "inf") || (n.val == 8 && matchword buf i "infinity") then
    x := JuliaLean.base.float.convertFloat T JuliaLean.base.float.Inf64
  else if n.val == 3 && matchword buf i "nan" then
    x := JuliaLean.base.float.convertFloat T JuliaLean.base.float.NaN64
  else if n.val > 4 && matchword buf i "nan" && (byteAt buf (add i (lit64 3))).val == 0x28 then
    match ← nanpayload T buf (add i (lit64 4)) j with
    | .failure f => return .failure f
    | .value y => x := y
  else return .failure INVALID
  return .value (if neg then JuliaLean.base.float.neg_IEEEFloat x else x)

/--
Julia source: base/parsers/floats.jl:363-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Parse the bytes `buf[i:j]` as a `T`, or return a `ParseFailure`. `i:j` must be in bounds.
@inline function parsefloat(::Type{T}, buf::AbstractVector{UInt8}, i::Int,
                            j::Int) where {T<:IEEEFloat}
    i <= j || return INVALID
    b = @inbounds buf[i]
    neg = b == UInt8('-')
    if neg || b == UInt8('+')
        i += 1
        i <= j || return INVALID
        b = @inbounds buf[i]
    end
    b - UInt8('0') <= 0x09 || b == UInt8('.') || return parsespecial(T, buf, i, j, neg)
    b == UInt8('0') && i < j && (@inbounds buf[i + 1]) | 0x20 == UInt8('x') &&
        return parsehex(T, buf, i + 2, j, neg)
    # significand: w, with nd digits, of which -q follow the decimal point
    first = i
    w, i = scandigits(buf, i, j, zero(UInt64))
    dot = i                                      # the end of the integer digits
    nd = dot - first
    q = 0
    if i <= j && (@inbounds buf[i]) == UInt8('.')
        w, i = scandigits(buf, dot + 1, j, w)
        nd += i - dot - 1
        q = dot + 1 - i
    end
    nd > 0 || return INVALID
    last = i - 1                                 # the end of the significand
    if i <= j && (@inbounds buf[i]) | 0x20 == UInt8('e')
        e, i, ok = scanexponent(buf, i + 1, j)
        ok || return INVALID
        q += e
    end
    i > j || return INVALID
    if nd > 19
        # leading zeros are not significant
        k = first
        while k <= last && (@inbounds buf[k]) in (UInt8('0'), UInt8('.'))
            (@inbounds buf[k]) == UInt8('0') && (nd -= 1)
            k += 1
        end
        if nd > 19
            # The value lies between w and w + 1 times 10^(q + nd - 19), for the first 19
            # significant digits w. When both round to the same float, so does the value;
            # otherwise it rounds to the one on its side of the midpoint between them.
            n = clamp(dot - k, 0, 19)              # the digits of w before the point
            w, _ = scandigits(buf, k, k + n - 1, zero(UInt64))
            f = max(k, dot + 1)
            w, _ = scandigits(buf, f, f + 18 - n, w)
            bits = eisellemire(T, w, q + nd - 19)
            if bits != eisellemire(T, w + 1, q + nd - 19)
                c = cmpmidpoint(T, buf, k, last, q, bits)
                bits += c > 0 || (c == 0 && isodd(bits))
            end
            return frombits(T, bits, neg)
        end
    end
    return fromdecimal(T, w, q, neg)
end

```
-/
def parsefloat (T : FTy) (buf : List Byte) (i j : I64) : M World (ParseResult (FV T)) := do
  if !(i.val ≤ j.val) then return .failure INVALID
  let b := byteAt buf i
  let neg := b.val == 0x2d
  let mut i := i
  let mut b := b
  if neg || b.val == 0x2b then
    i := add i (lit64 1)
    if !(i.val ≤ j.val) then return .failure INVALID
    b := byteAt buf i
  if !((sub b (u8 0x30)).val ≤ 9 || b.val == 0x2e) then return ← parsespecial T buf i j neg
  if b.val == 0x30 && i.val < j.val && (bor (byteAt buf (add i (lit64 1))) (u8 0x20)).val == 0x78 then
    return ← parsehex T buf (add i (lit64 2)) j neg
  let first := i
  let (w0, i0) ← scandigits buf i j (u64 0)
  i := i0
  let dot := i
  let mut nd := sub dot first
  let mut q := lit64 0
  let mut w := w0
  if i.val ≤ j.val && (byteAt buf i).val == 0x2e then
    let (w', i') ← scandigits buf (add dot (lit64 1)) j w
    w := w'
    i := i'
    nd := add nd (sub (sub i dot) (lit64 1))
    q := sub (add dot (lit64 1)) i
  if !(nd.val > 0) then return .failure INVALID
  let last := sub i (lit64 1)
  if i.val ≤ j.val && (bor (byteAt buf i) (u8 0x20)).val == 0x65 then
    let (e, i', ok) ← scanexponent buf (add i (lit64 1)) j
    if !ok then return .failure INVALID
    i := i'
    q := add q e
  if !(i.val > j.val) then return .failure INVALID
  if nd.val > 19 then
    let (k, nd') ← whileLoop (fun ((k, nd) : I64 × I64) => do
      if !(k.val ≤ last.val && ((byteAt buf k).val == 0x30 || (byteAt buf k).val == 0x2e)) then
        return Sum.inl (k, nd)
      let nd := if (byteAt buf k).val == 0x30 then sub nd (lit64 1) else nd
      return Sum.inr (add k (lit64 1), nd)) (first, nd)
    nd := nd'
    if nd.val > 19 then
      let d := sub dot k
      let n := if d.val < 0 then lit64 0 else if d.val > 19 then lit64 19 else d
      let (w0, _) ← scandigits buf k (sub (add k n) (lit64 1)) (u64 0)
      let f := if k.val ≥ (add dot (lit64 1)).val then k else add dot (lit64 1)
      let (w19, _) ← scandigits buf f (sub (add f (lit64 18)) n) w0
      let qe := sub (add q nd) (lit64 19)
      let bits ← eisellemire T w19 qe
      let bits ← if bits.val != (← eisellemire T (add w19 (u64 1)) qe).val then do
          let c ← cmpmidpoint T buf k last q bits
          pure (add bits (ofBool .u64 (c.val > 0 || (c.val == 0 && bits.val % 2 == 1))))
        else pure bits
      return ← frombits T bits neg
  fromdecimal T w q neg

/--
Julia source: base/parsers/floats.jl:422-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function parsevalue(::Type{T}, bytes::AbstractVector{UInt8}) where {T<:IEEEFloat}
    require_one_based_indexing(bytes)
    return parsefloat(T, bytes, 1, length(bytes))
end
```
-/
def parsevalue (T : FTy) (bytes : List Byte) : M World (ParseResult (FV T)) :=
  parsefloat T bytes (lit64 1) (lit64 bytes.length)

end

end JuliaLean.base.parsers.floats


namespace JuliaLean.NumMisc

/-! ## Float NaN payload grammar -/

abbrev Byte := Nat

def asciiLower (b : Byte) : Byte := if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

/-- `isnanchar`, `base/parsers/floats.jl:319-321`. -/
def isNanChar (b : Byte) : Bool :=
  (48 ≤ b && b ≤ 57) || (97 ≤ asciiLower b && asciiLower b ≤ 122) || b == 95

def digitValue (b : Byte) : Option Nat :=
  if 48 ≤ b ∧ b ≤ 57 then some (b - 48)
  else
    let b := asciiLower b
    if 97 ≤ b ∧ b ≤ 102 then some (b - 87) else none

def validDigits (base : Nat) (s : List Byte) : Bool :=
  !s.isEmpty && s.all fun b => (digitValue b).any (· < base)

/-- The numeric payload grammar documented at `base/parsers/Parsers.jl:66-71`. -/
def documentedNanPayload : List Byte → Bool
  | 48 :: x :: xs =>
      if asciiLower x == 120 then validDigits 16 xs
      else validDigits 8 (48 :: x :: xs)
  | s => validDigits 10 s

/-- `nanpayload`, `base/parsers/floats.jl:326-343`, at the acceptance level.
Allowed characters make the call succeed; a failed integer parse supplies payload zero. -/
def sourceNanPayload (s : List Byte) : Option Nat :=
  if s.all isNanChar then some (if documentedNanPayload s then 1 else 0) else none

/-- `fromdecimal(T, w, 0, neg)`, `base/parsers/floats.jl:143-151`, for nonnegative
integers exactly representable in binary64. The model records the exact integer value. -/
def fromDecimalInteger (w : Nat) : Option Nat :=
  if w ≤ 2^53 then some w else none

end JuliaLean.NumMisc

namespace JuliaLean.NumMisc.Coverage

open JuliaLean

/-! ## `base/parsers/floats.jl:15-165` -/

def limbBase : Nat := 2^64

def mulSmall : List Nat → Nat → Nat → List Nat × Nat
  | [], _, carry => ([], carry)
  | x :: xs, multiplier, carry =>
      let product := x * multiplier + carry
      let rest := mulSmall xs multiplier (product / limbBase)
      (product % limbBase :: rest.1, rest.2)

def div5BigEndian : List Nat → Nat → List Nat × Nat
  | [], remainder => ([], remainder)
  | x :: xs, remainder =>
      let combined := remainder * limbBase + x
      let rest := div5BigEndian xs (combined % 5)
      (combined / 5 :: rest.1, rest.2)

def div5Limbs (xs : List Nat) : List Nat × Nat :=
  let result := div5BigEndian xs.reverse 0
  (result.1.reverse, result.2)

def limbAt (xs : List Nat) (oneBased : Int) : Nat :=
  if oneBased ≥ 1 then xs.getD (oneBased - 1).toNat 0 else 0

def top128At (xs : List Nat) (lastNonzero leadingZeros : Nat) : Nat × Nat :=
  let k : Int := lastNonzero
  let s := leadingZeros
  let hi := if s == 0 then limbAt xs k
    else (limbAt xs k * 2^s + limbAt xs (k - 1) / 2^(64 - s)) % limbBase
  let lo := if s == 0 then limbAt xs (k - 1)
    else (limbAt xs (k - 1) * 2^s + limbAt xs (k - 2) / 2^(64 - s)) % limbBase
  (hi, lo)


def pow10Range : FloatKind → Int × Int
  | .f64 => (-342, 308)
  | .f32 => (-64, 38)
  | .f16 => (-26, 4)

def halfwayRange : FloatKind → Int × Int
  | .f64 => (-4, 23)
  | .f32 => (-17, 10)
  | .f16 => (-26, 5)

def mul64Parts (a b : Nat) : Nat × Nat :=
  let product := a * b
  (product / limbBase % limbBase, product % limbBase)

inductive PackResult where
  | finite (mantissa exponent : Nat)
  | infinity
  deriving DecidableEq, Repr

def packBitsShape (mantissaBits rawMax : Nat) (m : Nat) (e : Int) : PackResult :=
  if e ≤ 0 then .finite m 0
  else
    let carry := m ≥ 2^(mantissaBits + 1)
    let m := if carry then m / 2 else m
    let e := if carry then e + 1 else e
    if e ≥ rawMax then .infinity else .finite m e.toNat

inductive EiselPath where | zero | outOfRange | exact | general deriving DecidableEq, Repr

def eiselPath (kind : FloatKind) (w : Nat) (q : Int) : EiselPath :=
  let range := pow10Range kind
  if w == 0 then .zero
  else if q < range.1 || q > range.2 then .outOfRange
  else if q == 0 then .exact
  else .general

inductive ParsedBits where | underflow | overflow | finite (bits : Nat) deriving DecidableEq, Repr

def fromBitsShape (bits infinityBits : Nat) : ParsedBits :=
  if bits == 0 then .underflow
  else if bits == infinityBits then .overflow
  else .finite bits

inductive DecimalPath where | zero | exactPower | eisel deriving DecidableEq, Repr

def decimalPath (w : Nat) (q : Int) (exactPowers significandBits : Nat) : DecimalPath :=
  if w == 0 then .zero
  else if q.natAbs < exactPowers && w ≤ 2^(significandBits + 1) then .exactPower
  else .eisel

def powerChunks (base n : Nat) : List Nat :=
  let step := if base == 2 then 63 else 27
  (List.range ((n + step - 1) / step)).map fun k => min (n - k * step) step

def pow5TableIndices : List Int := (List.range 651).map fun i : Nat => (i : Int) - 342

def exactPow10Count : FloatKind → Nat
  | .f64 => 23
  | .f32 => 11
  | .f16 => 5

/-! ## `base/parsers/floats.jl:171-425` -/

def decimalDigit (byte : Nat) : Option Nat :=
  if 48 ≤ byte ∧ byte ≤ 57 then some (byte - 48) else none

def hexDigit (byte : Nat) : Option Nat :=
  match decimalDigit byte with
  | some d => some d
  | none =>
      let lower := asciiLower byte
      if 97 ≤ lower ∧ lower ≤ 102 then some (lower - 87) else none

def scanDigits : List Nat → Nat → Nat × Nat
  | [], word => (word, 0)
  | byte :: bytes, word =>
      match decimalDigit byte with
      | none => (word, 0)
      | some digit =>
          let result := scanDigits bytes ((10 * word + digit) % limbBase)
          (result.1, result.2 + 1)

def scanExponent (bytes : List Nat) : Int × Nat × Bool :=
  let (negative, digits) := match bytes with
    | 45 :: rest => (true, rest)
    | 43 :: rest => (false, rest)
    | rest => (false, rest)
  let rec loop : List Nat → Nat → Nat × Nat
    | [], value => (value, 0)
    | byte :: rest, value =>
        match decimalDigit byte with
        | none => (value, 0)
        | some digit =>
            let next := if value < 100000000 then 10 * value + digit else value
            let result := loop rest next
            (result.1, result.2 + 1)
  let result := loop digits 0
  ((if negative then -(result.1 : Int) else result.1), result.2, result.2 > 0)

def scanHex : List Nat → Nat → Bool → Nat × Bool × Nat
  | [], mantissa, sticky => (mantissa, sticky, 0)
  | byte :: bytes, mantissa, sticky =>
      match hexDigit byte with
      | none => (mantissa, sticky, 0)
      | some digit =>
          let room := mantissa < 2^60
          let result := scanHex bytes (if room then mantissa * 16 + digit else mantissa)
            (sticky || (!room && digit != 0))
          (result.1, result.2.1, result.2.2 + 1)

def matchWord (bytes word : List Nat) : Bool :=
  bytes.length ≥ word.length &&
    ((bytes.take word.length).zip word).all (fun pair => asciiLower pair.1 == pair.2)

inductive FloatParseRoute where | invalid | special | hexadecimal | decimal deriving DecidableEq, Repr

def floatParseRoute (bytes : List Nat) : FloatParseRoute :=
  let unsigned := match bytes with | 43 :: rest | 45 :: rest => rest | rest => rest
  match unsigned with
  | [] => .invalid
  | first :: rest =>
      if (decimalDigit first).isSome || first == 46 then
        if first == 48 && !rest.isEmpty && asciiLower rest.head! == 120 then .hexadecimal else .decimal
      else .special

def parseValueRoute (bytes : List Nat) : FloatParseRoute := floatParseRoute bytes

end JuliaLean.NumMisc.Coverage

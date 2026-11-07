import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int
import JuliaLean.base.checked
import JuliaLean.base.parsers.Parsers
import JuliaLean.base.strings.string

/-!
# Model of `base/parsers/ints.jl`

The integer parser of `Base.Parsers` in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`, behind
`parse` and `tryparse` for integer types. A byte buffer (`AbstractVector{UInt8}`, one-based) is
the list of its bytes; the parser only reads it at indices its callers keep in bounds
(`@inbounds`), and the model reads `0x00` outside. All integer arithmetic is the installed
`JuliaLean.base.int` model at Julia's types, and overflow detection is the installed
`JuliaLean.base.checked` model. Loops are `whileLoop`s of `M`; the parser touches no world state.
-/

namespace JuliaLean.base.parsers.ints

open JuliaLean
open JuliaLean.base.io (M whileLoop)
open JuliaLean.base.parsers.Parsers

abbrev I64 := JInt .i64
abbrev U64 := JInt .u64
abbrev Byte := JInt .u8

/-- `@inbounds buf[i]`. -/
def byteAt (buf : List Byte) (i : I64) : Byte := buf.getD (i.val - 1).toNat (JInt.lit .u8 0)

def lit64 (n : Int) : I64 := JInt.lit .i64 n
def u64 (n : Int) : U64 := JInt.lit .u64 n
def u8 (n : Int) : Byte := JInt.lit .u8 n

/-- `x` promoted to a wider unsigned type (exact). -/
def widen {t : IntTy} (u : IntTy) (x : JInt t) : JInt u := JInt.wrap u x.val

def add {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.add x y
def sub {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.sub x y
def mul {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.mul x y
def band {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.and_int x y
def bor {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.or_int x y
def bnot {t : IntTy} (x : JInt t) : JInt t := JuliaLean.base.int.not_int x
/-- `x >> n` and `x << n` with an `Int` count. -/
def shr {t : IntTy} (x : JInt t) (n : I64) : JInt t := JuliaLean.base.int.shr_Int x n
def shl {t : IntTy} (x : JInt t) (n : I64) : JInt t := JuliaLean.base.int.shl_Int x n

/-- The indices `i:j`. -/
def indexRange (i j : I64) : List I64 :=
  (List.range (j.val - i.val + 1).toNat).map (fun (k : Nat) => lit64 (i.val + (k : Int)))

section
variable {World : Type}

/--
Julia source: base/parsers/ints.jl:1-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

# Decimal digits are parsed eight at a time: `load8` reads eight bytes as one word,
# `isdigits8` checks that they are all ASCII digits, and `digits8` converts them to
# their value with three multiplies instead of eight multiply-adds. Hex digits are parsed
# eight at a time in the same way, with `ishexdigits8` and `hexdigits8`.

# Bytes `i:i+7` of `buf` as a little-endian word, so the first byte is the lowest.
# Storage with a stable pointer is read with one unaligned load.
@inline load8(buf::Union{Vector{UInt8}, Memory{UInt8},
                         FastContiguousSubArray{UInt8, 1, <:Union{Vector{UInt8}, Memory{UInt8}}}},
              i::Int) =
    GC.@preserve buf ltoh(unsafe_load(Ptr{UInt64}(pointer(buf, i))))
@inline load8(buf::CodeUnits{UInt8, <:DenseUTF8String}, i::Int) =
    GC.@preserve buf ltoh(unsafe_load(Ptr{UInt64}(pointer(buf.s, i))))
@inline function load8(buf::AbstractVector{UInt8}, i::Int)
    w = zero(UInt64)
    for k in 7:-1:0
        w = w << 8 | (@inbounds buf[i + k])::UInt8
    end
    return w
end

```
-/
def load8Dense (buf : List Byte) (i : I64) : U64 :=
  u64 ((List.range 8).foldl (fun (acc : Int) (k : Nat) =>
    acc + (byteAt buf (lit64 (i.val + (k : Int)))).val * 256 ^ k) 0)

def load8CodeUnits (buf : List Byte) (i : I64) : U64 := load8Dense buf i

def load8 (buf : List Byte) (i : I64) : U64 :=
  [7, 6, 5, 4, 3, 2, 1, 0].foldl
    (fun w k => bor (shl w (lit64 8)) (widen .u64 (byteAt buf (add i (lit64 k))))) (u64 0)

/--
Julia source: base/parsers/ints.jl:24-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Whether every byte of `w` is in '0':'9' (0x30:0x39): its high nibble must be 3,
# and still be 3 after adding 6, which carries 0x3a:0x3f into 0x40:0x45.
@inline isdigits8(w::UInt64) =
    ((w & 0xf0f0f0f0_f0f0f0f0) | ((w + 0x06060606_06060606) & 0xf0f0f0f0_f0f0f0f0) >> 4) ==
        0x33333333_33333333

```
-/
def isdigits8 (w : U64) : Bool :=
  (bor (band w (u64 0xf0f0f0f0f0f0f0f0))
    (shr (band (add w (u64 0x0606060606060606)) (u64 0xf0f0f0f0f0f0f0f0)) (lit64 4))).val ==
    0x3333333333333333

/--
Julia source: base/parsers/ints.jl:30-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The value of the eight ASCII digits in `w`, first digit in the lowest byte. After
# subtracting '0', adjacent digits are combined into two-digit values in bytes 0, 2, 4
# and 6, and two multiplies sum those times 10^6, 10^4, 10^2 and 1 into the upper half.
@inline function digits8(w::UInt64)
    w -= 0x30303030_30303030
    w = w * 10 + (w >> 8)
    return (((w & 0x000000ff_000000ff) * 0x000f4240_00000064) +
            (((w >> 16) & 0x000000ff_000000ff) * 0x00002710_00000001)) >> 32
end

```
-/
def digits8 (w : U64) : U64 :=
  let w := sub w (u64 0x3030303030303030)
  let w := add (mul w (u64 10)) (shr w (lit64 8))
  shr (add (mul (band w (u64 0x000000ff000000ff)) (u64 0x000f424000000064))
    (mul (band (shr w (lit64 16)) (u64 0x000000ff000000ff)) (u64 0x0000271000000001))) (lit64 32)

/--
Julia source: base/parsers/ints.jl:40-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Bytes of `w` in `lo:hi`, as their high bits, if every byte of `w` is below 0x80.
@inline bytesin(w::UInt64, lo::UInt8, hi::UInt8) =
    (w + (0x80 - lo) * 0x01010101_01010101) & ~(w + (0x7f - hi) * 0x01010101_01010101) &
        0x80808080_80808080

```
-/
def bytesin (w : U64) (lo hi : Byte) : U64 :=
  band (band (add w (mul (widen .u64 (sub (u8 0x80) lo)) (u64 0x0101010101010101)))
    (bnot (add w (mul (widen .u64 (sub (u8 0x7f) hi)) (u64 0x0101010101010101)))))
    (u64 0x8080808080808080)

/--
Julia source: base/parsers/ints.jl:45-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Whether every byte of `w` is in '0':'9', 'A':'F' or 'a':'f'; setting bit 5 lowercases letters.
@inline ishexdigits8(w::UInt64) =
    (w & 0x80808080_80808080 == 0) &
        ((bytesin(w, UInt8('0'), UInt8('9')) |
          bytesin(w | 0x20202020_20202020, UInt8('a'), UInt8('f'))) == 0x80808080_80808080)

```
-/
def ishexdigits8 (w : U64) : Bool :=
  ((band w (u64 0x8080808080808080)).val == 0) &&
    ((bor (bytesin w (u8 0x30) (u8 0x39))
      (bytesin (bor w (u64 0x2020202020202020)) (u8 0x61) (u8 0x66))).val == 0x8080808080808080)

/--
Julia source: base/parsers/ints.jl:51-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The value of the eight ASCII hex digits in `w`, first digit in the lowest byte. Letters,
# which have bit 6 set, get 9 added to their low nibble; then adjacent nibbles, bytes and
# halfwords are combined.
@inline function hexdigits8(w::UInt64)
    w = (w & 0x0f0f0f0f_0f0f0f0f) + ((w >> 6) & 0x01010101_01010101) * 9
    w = ((w << 4) | (w >> 8)) & 0x00ff00ff_00ff00ff
    w = ((w << 8) | (w >> 16)) & 0x0000ffff_0000ffff
    return ((w << 16) | (w >> 32)) & 0x00000000_ffffffff
end

```
-/
def hexdigits8 (w : U64) : U64 :=
  let w := add (band w (u64 0x0f0f0f0f0f0f0f0f))
    (mul (band (shr w (lit64 6)) (u64 0x0101010101010101)) (u64 9))
  let w := band (bor (shl w (lit64 4)) (shr w (lit64 8))) (u64 0x00ff00ff00ff00ff)
  let w := band (bor (shl w (lit64 8)) (shr w (lit64 16))) (u64 0x0000ffff0000ffff)
  band (bor (shl w (lit64 16)) (shr w (lit64 32))) (u64 0x00000000ffffffff)

/--
Julia source: base/parsers/ints.jl:61-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The value of the code unit `b` as a digit in `base` (at most 62), or `typemax(b)` if it
# is not one: '0':'9' are 0:9, 'A':'Z' are 10:35, and 'a':'z' are 10:35 up to base 36
# and 36:61 above it.
@inline function digitvalue(b::Unsigned, base::Int)
    UInt8('0') <= b <= UInt8('9') && return b - UInt8('0')
    UInt8('A') <= b <= UInt8('Z') && return b - UInt8('A') + 0x0a
    UInt8('a') <= b <= UInt8('z') && return b - UInt8('a') + (base <= 36 ? 0x0a : 0x24)
    return typemax(b)
end

```
-/
def digitvalue (b : Byte) (base : I64) : Byte :=
  if 0x30 ≤ b.val ∧ b.val ≤ 0x39 then sub b (u8 0x30)
  else if 0x41 ≤ b.val ∧ b.val ≤ 0x5a then add (sub b (u8 0x41)) (u8 0x0a)
  else if 0x61 ≤ b.val ∧ b.val ≤ 0x7a then
    add (sub b (u8 0x61)) (if base.val ≤ 36 then u8 0x0a else u8 0x24)
  else u8 0xff

/--
Julia source: base/parsers/ints.jl:71-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The failure when the digits overflow before index `i`: `OVERFLOW`, unless a later byte is
# not a digit.
function overflowfailure(buf::AbstractVector{UInt8}, i::Int, j::Int, base::Int)
    for k in i:j
        digitvalue(@inbounds(buf[k])::UInt8, base) < base || return INVALID
    end
    return OVERFLOW
end

```
-/
def overflowfailure (buf : List Byte) (i j base : I64) : M World ParseFailure := do
  for k in indexRange i j do
    if !((digitvalue (byteAt buf k) base).val < base.val) then return INVALID
  return OVERFLOW

/-- `ndigits(n; base = b)` for `n ≥ 1` and `b ≥ 2`. -/
def ndigitsNat (n b : Nat) : Nat :=
  go n (n + 1)
where
  go (m : Nat) : Nat → Nat
    | 0 => 0
    | fuel + 1 => if m < b then 1 else 1 + go (m / b) fuel

/--
Julia source: base/parsers/ints.jl:80-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# How many digits in each base cannot overflow a UInt64 (UInt128).
const SAFEDIGITS64 = ntuple(b -> b < 2 ? 0 : ndigits(typemax(UInt64); base = b) - 1, 62)
const SAFEDIGITS128 = ntuple(b -> b < 2 ? 0 : ndigits(typemax(UInt128); base = b) - 1, 62)

```
-/
def safedigits (bits : Nat) : List I64 :=
  (List.range 62).map (fun k =>
    let b := k + 1
    if b < 2 then lit64 0 else lit64 ((ndigitsNat (2 ^ bits - 1) b : Int) - 1))

def SAFEDIGITS64 : List I64 := safedigits 64
def SAFEDIGITS128 : List I64 := safedigits 128

/-- `sizeof(T) > 8 ? UInt128 : UInt64`. -/
def accumulatorType (t : IntTy) : IntTy := if t.bits > 64 then .u128 else .u64

/-- `buf[i] - UInt8('0')`. -/
def decimalDigit (buf : List Byte) (i : I64) : Byte := sub (byteAt buf i) (u8 0x30)

/--
Julia source: base/parsers/ints.jl:84-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Parse the digits `buf[i:j]`, without a sign, in `base` (2 to 62) as a `T` that is negated
# if `neg` (signed `T` only), or return a `ParseFailure`. `i:j` must be in bounds.
@inline function parseint(::Type{T}, buf::AbstractVector{UInt8}, i::Int, j::Int,
                          base::Int, neg::Bool) where {T<:BitInteger}
    i <= j || return INVALID
    U = sizeof(T) > 8 ? UInt128 : UInt64
    n::U = 0
    if base == 10
        # the first 19 (38) decimal digits cannot overflow a UInt64 (UInt128)
        k = min(j, i + (U === UInt64 ? 18 : 37))
        while k - i >= 7
            w = load8(buf, i)
            isdigits8(w) || return INVALID
            n = n * U(100_000_000) + digits8(w)
            i += 8
        end
        if U === UInt64
            while i <= k
                d = (@inbounds buf[i])::UInt8 - UInt8('0')
                d <= 0x09 || return INVALID
                n = n * U(10) + d
                i += 1
            end
        else
            # the last digits go in a UInt64, saving 128-bit multiplies
            t, p = zero(UInt64), one(UInt64)
            while i <= k
                d = (@inbounds buf[i])::UInt8 - UInt8('0')
                d <= 0x09 || return INVALID
                t = t * 10 + d
                p *= 10
                i += 1
            end
            n = n * U(p) + t
        end
    elseif sizeof(T) < 4
        # 8- and 16-bit types have too few digits for the loops below to pay off
    elseif base == 16
        # the first 16 (32) hex digits cannot overflow a UInt64 (UInt128)
        k = min(j, i + (U === UInt64 ? 15 : 31))
        while k - i >= 7
            w = load8(buf, i)
            ishexdigits8(w) || return INVALID
            n = n << 32 | hexdigits8(w)
            i += 8
        end
        while i <= k
            d = digitvalue(@inbounds(buf[i])::UInt8, 16)
            d < 0x10 || return INVALID
            n = n << 4 | d
            i += 1
        end
    else
        k = min(j, i + (U === UInt64 ? SAFEDIGITS64 : SAFEDIGITS128)[base] - 1)
        while i <= k
            d = digitvalue(@inbounds(buf[i])::UInt8, base)
            d < base || return INVALID
            n = n * (base % U) + d
            i += 1
        end
    end
    # any remaining digits, checking for overflow
    while i <= j
        d = digitvalue(@inbounds(buf[i])::UInt8, base)
        d < base || return INVALID
        n, ov_mul = mul_with_overflow(n, base % U)
        n, ov_add = add_with_overflow(n, d % U)
        ov_mul | ov_add && return overflowfailure(buf, i + 1, j, base)
        i += 1
    end
    # a negative value can reach one past `typemax(T)`
    n <= (typemax(T) % U) + neg || return OVERFLOW
    return (neg ? -n : n) % T
end

```
-/
def parseintBits (t : IntTy) (buf : List Byte) (i j base : I64) (neg : Bool) :
    M World (ParseResult (JInt t)) := do
  if !(i.val ≤ j.val) then return .failure INVALID
  let u := accumulatorType t
  let start : Option (I64 × JInt u) ← do
    if base.val == 10 then
      let k := if j.val ≤ (add i (lit64 (if u == .u64 then 18 else 37))).val then j
        else add i (lit64 (if u == .u64 then 18 else 37))
      let eights ← whileLoop (fun ((i, n) : I64 × JInt u) => do
        if !((sub k i).val ≥ 7) then return Sum.inl (some (i, n))
        let w := load8 buf i
        if !isdigits8 w then return Sum.inl none
        return Sum.inr (add i (lit64 8), add (mul n (JInt.lit u 100000000)) (widen u (digits8 w))))
        (i, JInt.lit u 0)
      match eights with
      | none => pure none
      | some (i, n) =>
        if u == .u64 then
          whileLoop (fun ((i, n) : I64 × JInt u) => do
            if !(i.val ≤ k.val) then return Sum.inl (some (i, n))
            let d := decimalDigit buf i
            if !(d.val ≤ 9) then return Sum.inl none
            return Sum.inr (add i (lit64 1), add (mul n (JInt.lit u 10)) (widen u d))) (i, n)
        else
          let tail ← whileLoop (fun ((i, t, p) : I64 × U64 × U64) => do
            if !(i.val ≤ k.val) then return Sum.inl (some (i, t, p))
            let d := decimalDigit buf i
            if !(d.val ≤ 9) then return Sum.inl none
            return Sum.inr (add i (lit64 1), add (mul t (u64 10)) (widen .u64 d), mul p (u64 10)))
            (i, u64 0, u64 1)
          match tail with
          | none => pure none
          | some (i, t, p) => pure (some (i, add (mul n (widen u p)) (widen u t)))
    else if t.bits < 32 then
      pure (some (i, JInt.lit u 0))
    else if base.val == 16 then
      let k := if j.val ≤ (add i (lit64 (if u == .u64 then 15 else 31))).val then j
        else add i (lit64 (if u == .u64 then 15 else 31))
      let eights ← whileLoop (fun ((i, n) : I64 × JInt u) => do
        if !((sub k i).val ≥ 7) then return Sum.inl (some (i, n))
        let w := load8 buf i
        if !ishexdigits8 w then return Sum.inl none
        return Sum.inr (add i (lit64 8), bor (shl n (lit64 32)) (widen u (hexdigits8 w))))
        (i, JInt.lit u 0)
      match eights with
      | none => pure none
      | some (i, n) =>
        whileLoop (fun ((i, n) : I64 × JInt u) => do
          if !(i.val ≤ k.val) then return Sum.inl (some (i, n))
          let d := digitvalue (byteAt buf i) (lit64 16)
          if !(d.val < 0x10) then return Sum.inl none
          return Sum.inr (add i (lit64 1), bor (shl n (lit64 4)) (widen u d))) (i, n)
    else
      let table := if u == .u64 then SAFEDIGITS64 else SAFEDIGITS128
      let safe ← match (if base.val ≥ 1 then table[(base.val - 1).toNat]? else none) with
        | some s => pure s
        | none => throw (.jl .boundsError)
      let bound := sub (add i safe) (lit64 1)
      let k := if j.val ≤ bound.val then j else bound
      whileLoop (fun ((i, n) : I64 × JInt u) => do
        if !(i.val ≤ k.val) then return Sum.inl (some (i, n))
        let d := digitvalue (byteAt buf i) base
        if !(d.val < base.val) then return Sum.inl none
        return Sum.inr (add i (lit64 1), add (mul n (JInt.wrap u base.val)) (widen u d)))
        (i, JInt.lit u 0)
  match start with
  | none => return .failure INVALID
  | some (i, n) =>
    let rest ← whileLoop (fun ((i, n) : I64 × JInt u) => do
      if !(i.val ≤ j.val) then return Sum.inl (Sum.inr n)
      let d := digitvalue (byteAt buf i) base
      if !(d.val < base.val) then return Sum.inl (Sum.inl INVALID)
      let (n, ovMul) ← JuliaLean.base.io.liftJl
        (JuliaLean.base.checked.mulWithOverflowBits n (JInt.wrap u base.val))
      let (n, ovAdd) := JuliaLean.base.checked.addWithOverflowBits n (JInt.wrap u d.val)
      if ovMul || ovAdd then
        return Sum.inl (Sum.inl (← overflowfailure buf (add i (lit64 1)) j base))
      return Sum.inr (add i (lit64 1), n)) (i, n)
    match rest with
    | .inl failure => return .failure failure
    | .inr n =>
      let limit := add (JInt.wrap u t.max) (JInt.wrap u (if neg then 1 else 0))
      if !(n.val ≤ limit.val) then return .failure OVERFLOW
      return .value (JInt.wrap t (if neg then JuliaLean.base.int.neg n else n).val)

/-- The operations of a generic `Integer` type `T` used by the fallback parser. -/
structure IntegerOps (World T : Type) where
  zero : T
  /-- `T(n)` for an `Int` or `UInt8` value. -/
  ofInt : Int → M World T
  neg : T → M World T
  mulWithOverflow : T → T → M World (T × Bool)
  addWithOverflow : T → T → M World (T × Bool)

/--
Julia source: base/parsers/ints.jl:159-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Other integer types accumulate in `T` itself, negatively for a negative value so that
# `typemin(T)` is reachable.
function parseint(::Type{T}, buf::AbstractVector{UInt8}, i::Int, j::Int,
                  base::Int, neg::Bool) where {T<:Integer}
    i <= j || return INVALID
    n = zero(T)
    for k in i:j
        d = digitvalue(@inbounds(buf[k])::UInt8, base)
        d < base || return INVALID
        n, ov_mul = mul_with_overflow(n, T(base))
        n, ov_add = add_with_overflow(n, neg ? -T(d) : T(d))
        ov_mul | ov_add && return overflowfailure(buf, k + 1, j, base)
    end
    return n
end

```
-/
def parseintGeneric {T : Type} (ops : IntegerOps World T) (buf : List Byte) (i j base : I64)
    (neg : Bool) : M World (ParseResult T) := do
  if !(i.val ≤ j.val) then return .failure INVALID
  let mut n := ops.zero
  for k in indexRange i j do
    let d := digitvalue (byteAt buf k) base
    if !(d.val < base.val) then return .failure INVALID
    let (n1, ovMul) ← ops.mulWithOverflow n (← ops.ofInt base.val)
    let dT ← if neg then do ops.neg (← ops.ofInt d.val) else ops.ofInt d.val
    let (n2, ovAdd) ← ops.addWithOverflow n1 dT
    n := n2
    if ovMul || ovAdd then
      return .failure (← overflowfailure buf (add k (lit64 1)) j base)
  return .value n

/-- A generic `Integer` `base` keyword: its value and its printed form. -/
structure BaseArg (World : Type) where
  value : Int
  display : M World String

def invalidBase (base : BaseArg World) : M World Unit := do
  if !(2 ≤ base.value ∧ base.value ≤ 62) then
    throw (.jl (.argumentError ("invalid base: base must be 2 ≤ base ≤ 62, got " ++ (← base.display))))

/-- `i, j = 1, length(bytes)` and the optional sign of a signed type. -/
def signPrefix (signed : Bool) (bytes : List Byte) : I64 × I64 × Bool :=
  let i := lit64 1
  let j := lit64 bytes.length
  if signed && i.val ≤ j.val then
    let b := byteAt bytes i
    if b.val == 0x2d || b.val == 0x2b then (add i (lit64 1), j, b.val == 0x2d) else (i, j, false)
  else (i, j, false)

/--
Julia source: base/parsers/ints.jl:175-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function parsevalue(::Type{T}, bytes::AbstractVector{UInt8};
                            base::Integer = 10) where {T<:Integer}
    require_one_based_indexing(bytes)
    2 <= base <= 62 ||
        throw(ArgumentError(LazyString("invalid base: base must be 2 ≤ base ≤ 62, got ", base)))
    i, j = 1, length(bytes)
    neg = false
    if T <: Signed && i <= j
        b = @inbounds bytes[i]
        if b == UInt8('-') || b == UInt8('+')
            neg = b == UInt8('-')
            i += 1
        end
    end
    return parseint(T, bytes, i, j, Int(base), neg)
end
```
-/
def parsevalueBits (t : IntTy) (bytes : List Byte) (base : BaseArg World) :
    M World (ParseResult (JInt t)) := do
  invalidBase base
  let (i, j, neg) := signPrefix t.signed bytes
  parseintBits t bytes i j (← JuliaLean.base.io.liftJl (JInt.convert "convert" .i64 base.value)) neg

/-- `parsevalue(T, bytes; base)` for an `Integer` type that is not a `BitInteger`. -/
def parsevalueGeneric {T : Type} (ops : IntegerOps World T) (signed : Bool) (bytes : List Byte)
    (base : BaseArg World) : M World (ParseResult T) := do
  invalidBase base
  let (i, j, neg) := signPrefix signed bytes
  parseintGeneric ops bytes i j (← JuliaLean.base.io.liftJl (JInt.convert "convert" .i64 base.value)) neg

end

end JuliaLean.base.parsers.ints


namespace JuliaLean.MiscCov.Parsers

open JuliaLean.MiscCov

def byte (buf : List Nat) (i : Nat) : Nat := (buf[i]?).getD 0
def u64 (x : Nat) : Nat := x % 2^64
def add64 (x y : Nat) : Nat := u64 (x + y)
def sub64 (x y : Nat) : Nat := u64 (x + 2^64 - y % 2^64)
def mul64 (x y : Nat) : Nat := u64 (x * y)

/-- The little-endian word read by all three `load8` methods. -/
def load8Word (buf : List Nat) (i : Nat) : Nat :=
  u64 ((List.range 8).foldl (fun w k => w + byte buf (i + k) * 256^k) 0)

/-- Stable-pointer `unsafe_load` overload, `base/parsers/ints.jl:10-13`. -/
def load8Stable (buf : List Nat) (i : Nat) : Nat := load8Word buf i

/-- Dense UTF-8 `CodeUnits` overload, `base/parsers/ints.jl:14-15`. -/
def load8CodeUnits (buf : List Nat) (i : Nat) : Nat := load8Word buf i

/-- Generic `AbstractVector` loop, `base/parsers/ints.jl:16-22`. -/
def load8Generic (buf : List Nat) (i : Nat) : Nat :=
  (List.range 8).reverse.foldl (fun w k => u64 (w * 256 ||| byte buf (i + k))) 0

/-- `isdigits8`, `base/parsers/ints.jl:26-28`. -/
def isdigits8 (w : Nat) : Bool :=
  let mask := 0xf0f0f0f0f0f0f0f0
  ((w &&& mask) ||| ((add64 w 0x0606060606060606 &&& mask) >>> 4)) == 0x3333333333333333

/-- `digits8`, `base/parsers/ints.jl:33-38`. -/
def digits8 (w0 : Nat) : Nat :=
  let w := sub64 w0 0x3030303030303030
  let w := add64 (mul64 w 10) (w >>> 8)
  (((mul64 (w &&& 0x000000ff000000ff) 0x000f424000000064) +
    mul64 ((w >>> 16) &&& 0x000000ff000000ff) 0x0000271000000001) % 2^64) >>> 32

/-- `bytesin`, `base/parsers/ints.jl:41-43`. -/
def bytesin (w lo hi : Nat) : Nat :=
  (mul64 (0x80 - lo) 0x0101010101010101 |> add64 w) &&&
  (Nat.xor (mul64 (0x7f - hi) 0x0101010101010101 |> add64 w) (2^64 - 1)) &&&
  0x8080808080808080

/-- `ishexdigits8`, `base/parsers/ints.jl:46-49`. -/
def ishexdigits8 (w : Nat) : Bool :=
  (w &&& 0x8080808080808080 == 0) &&
    ((bytesin w 0x30 0x39 ||| bytesin (w ||| 0x2020202020202020) 0x61 0x66) ==
      0x8080808080808080)

/-- `hexdigits8`, `base/parsers/ints.jl:54-59`. -/
def hexdigits8 (w0 : Nat) : Nat :=
  let w := add64 (w0 &&& 0x0f0f0f0f0f0f0f0f) (mul64 ((w0 >>> 6) &&& 0x0101010101010101) 9)
  let w := ((w <<< 4) ||| (w >>> 8)) &&& 0x00ff00ff00ff00ff
  let w := ((w <<< 8) ||| (w >>> 16)) &&& 0x0000ffff0000ffff
  ((w <<< 16) ||| (w >>> 32)) &&& 0x00000000ffffffff

/-- `digitvalue`, `base/parsers/ints.jl:64-69`. -/
def digitvalue (b base : Nat) : Nat :=
  if 0x30 ≤ b && b ≤ 0x39 then b - 0x30
  else if 0x41 ≤ b && b ≤ 0x5a then b - 0x41 + 10
  else if 0x61 ≤ b && b ≤ 0x7a then b - 0x61 + (if base ≤ 36 then 10 else 36)
  else 255

/-- `overflowfailure`, `base/parsers/ints.jl:73-78`. Indices are zero based here. -/
def overflowfailure (buf : List Nat) (i j base : Nat) : Failure :=
  if ((buf.drop i).take (j + 1 - i)).all (fun b => digitvalue b base < base)
  then .overflow else .invalid

def parseMagnitude (buf : List Nat) (base : Nat) : Option Nat :=
  buf.foldl (fun acc b => acc.bind fun n =>
    let d := digitvalue b base
    if d < base then some (n * base + d) else none) (some 0)

/-- Observable result of the `T<:BitInteger` method, `base/parsers/ints.jl:86-157`.
The decimal, small-type, hexadecimal and other-base branches select the same
digit accumulation with the source method's final representability check. -/
def parseintBit (bits : Nat) (signed neg : Bool) (buf : List Nat) (i j base : Nat) : Result :=
  if j < i then .failure .invalid
  else
    let digits := (buf.drop i).take (j + 1 - i)
    let parsed := if base = 10 then parseMagnitude digits 10
      else if bits < 32 then parseMagnitude digits base
      else if base = 16 then parseMagnitude digits 16
      else parseMagnitude digits base
    match parsed with
    | none => .failure .invalid
    | some n =>
      let limit := if signed then (if neg then 2^(bits - 1) else 2^(bits - 1) - 1) else 2^bits - 1
      if n ≤ limit then .value (if neg then -(n : Int) else n) else .failure .overflow

inductive IntegerKind where
  | bool | arbitrary
  deriving DecidableEq, Repr

def convertKind : IntegerKind → Nat → M Int
  | .bool, n => if n ≤ 1 then .ok n else .error .inexactError
  | .arbitrary, n => .ok n

/-- Generic `T<:Integer` method, `base/parsers/ints.jl:161-173`, including the
`T(base)` conversion before the loop body. -/
def parseintInteger (kind : IntegerKind) (buf : List Nat) (i j base : Nat) (neg : Bool) : M Result := do
  if j < i then return .failure .invalid
  let b ← convertKind kind base
  let rec loop : List Nat → Int → M Result
    | [], n => pure (.value n)
    | x :: xs, n => do
      let d := digitvalue x base
      if base ≤ d then return .failure .invalid
      let td ← convertKind kind d
      loop xs (n * b + if neg then -td else td)
  loop ((buf.drop i).take (j + 1 - i)) 0

/-- `parsevalue(::Type{T}, bytes; base)`, `base/parsers/ints.jl:175-190` for
the generic integer path. -/
def parsevalue (kind : IntegerKind) (signed : Bool) (bytes : List Nat) (base : Nat) : M Result := do
  if !(2 ≤ base && base ≤ 62) then throw (.argumentError "invalid base")
  let (neg, i) := match bytes with
    | b :: _ => if signed && (b == 0x2d || b == 0x2b) then (b == 0x2d, 1) else (false, 0)
    | [] => (false, 0)
  parseintInteger kind bytes i (bytes.length - 1) base neg

end JuliaLean.MiscCov.Parsers

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean JuliaLean.ParsePrint

/-! ### `Base.Parsers.parseint`, `base/parsers/ints.jl` -/

/-- `load8(buf, i)`: bytes `i:i+7` as a little-endian `UInt64`, `base/parsers/ints.jl:10-22`. -/
def load8 (buf : Bytes) (i : Int) : JInt .u64 :=
  let v : Nat := (List.range 8).foldr (fun (k : Nat) (acc : Nat) => acc * 256 + cuN buf (i + k)) 0
  JInt.wrap .u64 v

/-- `base/parsers/ints.jl:26-28`. -/
def isdigits8 (w : JInt .u64) : Bool :=
  let m := JInt.lit .u64 0xf0f0f0f0f0f0f0f0
  (bor (band w m) (shr (band (w + JInt.lit .u64 0x0606060606060606) m) 4)).val ==
    0x3333333333333333

/-- `base/parsers/ints.jl:33-38`. -/
def digits8 (w : JInt .u64) : JInt .u64 :=
  let w := w - JInt.lit .u64 0x3030303030303030
  let w := w * JInt.lit .u64 10 + shr w 8
  let m := JInt.lit .u64 0x000000ff000000ff
  shr (band w m * JInt.lit .u64 0x000f424000000064 +
    band (shr w 16) m * JInt.lit .u64 0x0000271000000001) 32

/-- `base/parsers/ints.jl:41-43`; `0x80 - lo` and `0x7f - hi` are `UInt8` differences. -/
def bytesin (w : JInt .u64) (lo hi : Byte) : JInt .u64 :=
  let ones := JInt.lit .u64 0x0101010101010101
  let a := w + JInt.rem .u64 (byte 0x80 - lo) * ones
  let b := w + JInt.rem .u64 (byte 0x7f - hi) * ones
  band (band a (bxor b (JInt.lit .u64 0xffffffffffffffff))) (JInt.lit .u64 0x8080808080808080)

/-- `base/parsers/ints.jl:46-49`. -/
def ishexdigits8 (w : JInt .u64) : Bool :=
  (band w (JInt.lit .u64 0x8080808080808080)).val == 0 &&
    (bor (bytesin w (byte 48) (byte 57))
      (bytesin (bor w (JInt.lit .u64 0x2020202020202020)) (byte 97) (byte 102))).val ==
      0x8080808080808080

/-- `base/parsers/ints.jl:54-59`. -/
def hexdigits8 (w : JInt .u64) : JInt .u64 :=
  let w := band w (JInt.lit .u64 0x0f0f0f0f0f0f0f0f) +
    band (shr w 6) (JInt.lit .u64 0x0101010101010101) * JInt.lit .u64 9
  let w := band (bor (shl w 4) (shr w 8)) (JInt.lit .u64 0x00ff00ff00ff00ff)
  let w := band (bor (shl w 8) (shr w 16)) (JInt.lit .u64 0x0000ffff0000ffff)
  band (bor (shl w 16) (shr w 32)) (JInt.lit .u64 0x00000000ffffffff)

/-- `digitvalue(b, base)`, `base/parsers/ints.jl:64-69`: `typemax(UInt8)` for a non-digit. -/
def digitvalue (b : Byte) (base : Int) : Byte :=
  if 48 ≤ b.val ∧ b.val ≤ 57 then b - byte 48
  else if 65 ≤ b.val ∧ b.val ≤ 90 then b - byte 65 + byte 10
  else if 97 ≤ b.val ∧ b.val ≤ 122 then b - byte 97 + byte (if base ≤ 36 then 10 else 36)
  else byte 255

/-- `overflowfailure(buf, i, j, base)`, `base/parsers/ints.jl:73-78`: `true` for
`OVERFLOW`, `false` for `INVALID`. -/
def overflowfailure (buf : Bytes) (i j : Int) (base : Int) : Bool :=
  (List.range (j - i + 1).toNat).all fun k => (digitvalue (cu buf (i + k)) base).val < base

/-- The number of base-`b` digits of `n > 0`. -/
def natDigits (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, n => if n < b then 1 else natDigits b fuel (n / b) + 1

/-- `SAFEDIGITS64[b]` and `SAFEDIGITS128[b]`: `ndigits(typemax(U); base = b) - 1`,
`base/parsers/ints.jl:81-82`. -/
def safedigits (u : IntTy) (b : Int) : Int :=
  (natDigits b.toNat 130 (2 ^ u.bits - 1) : Int) - 1
/-- The eight-at-a-time decimal loop, `base/parsers/ints.jl:94-99`; `none` is `INVALID`. -/
def dec8Loop {u : IntTy} (buf : Bytes) (k : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if k - i ≥ 7 then
      let w := load8 buf i
      if !isdigits8 w then none
      else dec8Loop buf k f (n * JInt.lit u 100000000 + JInt.rem u (digits8 w), i + 8)
    else some (n, i)

/-- The remaining decimal digits into a `UInt64`, `base/parsers/ints.jl:101-106`. -/
def dec1Loop {u : IntTy} (buf : Bytes) (k : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if i ≤ k then
      let d := cu buf i - byte 48
      if d.val > 9 then none
      else dec1Loop buf k f (n * JInt.lit u 10 + JInt.rem u d, i + 1)
    else some (n, i)

/-- The last decimal digits of a 128-bit value in a `UInt64` with its power of ten,
`base/parsers/ints.jl:109-116`. -/
def decTPLoop (buf : Bytes) (k : Int) :
    Nat → JInt .u64 × JInt .u64 × Int → Option (JInt .u64 × JInt .u64 × Int)
  | 0, s => some s
  | f+1, (t, p, i) =>
    if i ≤ k then
      let d := cu buf i - byte 48
      if d.val > 9 then none
      else decTPLoop buf k f (t * JInt.lit .u64 10 + JInt.rem .u64 d, p * JInt.lit .u64 10, i + 1)
    else some (t, p, i)

/-- The eight-at-a-time hexadecimal loop, `base/parsers/ints.jl:124-129`. -/
def hex8Loop {u : IntTy} (buf : Bytes) (k : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if k - i ≥ 7 then
      let w := load8 buf i
      if !ishexdigits8 w then none
      else hex8Loop buf k f (bor (shl n 32) (JInt.rem u (hexdigits8 w)), i + 8)
    else some (n, i)

/-- The remaining safe hexadecimal digits, `base/parsers/ints.jl:130-135`. -/
def hex1Loop {u : IntTy} (buf : Bytes) (k : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if i ≤ k then
      let d := digitvalue (cu buf i) 16
      if d.val ≥ 16 then none
      else hex1Loop buf k f (bor (shl n 4) (JInt.rem u d), i + 1)
    else some (n, i)

/-- The safe digits of another base, `base/parsers/ints.jl:137-143`. -/
def safeLoop {u : IntTy} (buf : Bytes) (k base : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if i ≤ k then
      let d := digitvalue (cu buf i) base
      if d.val ≥ base then none
      else safeLoop buf k base f (n * JInt.wrap u base + JInt.rem u d, i + 1)
    else some (n, i)

/-- The checked loop over the remaining digits, `base/parsers/ints.jl:146-153`:
`.inl n` when all digits fit, `.inr r` for an early `ParseFailure`. -/
def checkedLoop {u : IntTy} (t : IntTy) (buf : Bytes) (j base : Int) :
    Nat → JInt u × Int → Jl (Sum (JInt u) (PR t))
  | 0, (n, _) => pure (.inl n)
  | f+1, (n, i) =>
    if i ≤ j then
      let d := digitvalue (cu buf i) base
      if d.val ≥ base then pure (.inr .invalid)
      else do
        let (n, ovMul) ← JuliaLean.IntArith.Checked.mulWithOverflow n (JInt.wrap u base)
        let (n, ovAdd) := JuliaLean.IntArith.Checked.addWithOverflow n (JInt.rem u d)
        if ovMul || ovAdd then
          pure (.inr (if overflowfailure buf (i + 1) j base then .overflow else .invalid))
        else checkedLoop t buf j base f (n, i + 1)
    else pure (.inl n)

/-- `U` in `Parsers.parseint`: `UInt128` for 128-bit `T`, else `UInt64`
(`base/parsers/ints.jl:89`). -/
def uTy (t : IntTy) : IntTy := if t.bits > 64 then .u128 else .u64

/-- The digits of `Parsers.parseint` that cannot overflow `U`, accumulated without
checks, `base/parsers/ints.jl:90-144`: `none` is `INVALID`; otherwise the value so
far and the index of the next digit. -/
def safePrefix (t : IntTy) (buf : Bytes) (i j base : Int) : Option (JInt (uTy t) × Int) :=
  let u := uTy t
  let fuel := buf.length + 1
  if base == 10 then
    let k := min j (i + (if u == .u64 then 18 else 37))
    match dec8Loop buf k fuel (JInt.lit u 0, i) with
    | none => none
    | some (n, i) =>
      if u == .u64 then dec1Loop buf k fuel (n, i)
      else match decTPLoop buf k fuel (JInt.lit .u64 0, JInt.lit .u64 1, i) with
        | none => none
        | some (t, p, i) => some (n * JInt.rem u p + JInt.rem u t, i)
  else if t.bits < 32 then some (JInt.lit u 0, i)
  else if base == 16 then
    let k := min j (i + (if u == .u64 then 15 else 31))
    match hex8Loop buf k fuel (JInt.lit u 0, i) with
    | none => none
    | some s => hex1Loop buf k fuel s
  else
    let k := min j (i + safedigits u base - 1)
    safeLoop buf k base fuel (JInt.lit u 0, i)

/-- `Parsers.parseint(T, buf, i, j, base, neg)` for `T <: BitInteger`,
`base/parsers/ints.jl:86-157`. -/
def parseint (t : IntTy) (buf : Bytes) (i j base : Int) (neg : Bool) : Jl (PR t) :=
  if ¬ i ≤ j then pure .invalid else
  match safePrefix t buf i j base with
  | none => pure .invalid
  | some s => do
    match ← checkedLoop t buf j base (buf.length + 1) s with
    | .inr r => pure r
    | .inl n =>
      -- a negative value can reach one past `typemax(T)`
      if n.val ≤ (JInt.rem (uTy t) (JInt.typemax t) + ofBool (uTy t) neg).val then
        pure (.val (JInt.rem t (if neg then -n else n)))
      else pure .overflow

end JuliaLean.ParsePrint.IntParse

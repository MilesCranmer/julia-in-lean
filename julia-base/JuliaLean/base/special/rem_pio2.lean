import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.math

/-!
Argument reduction modulo π/2 for Float64, `base/special/rem_pio2.jl`, Julia master
`bbfa0ce4150`. Unsigned machine integers are `Nat` bit patterns reduced modulo their
width wherever Julia wraps. A reduced remainder `DoubleFloat64(hi, lo)` is the pair
`(hi, lo)`.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `INV_2PI`, the first 19 64-bit words of the binary expansion of 1/2π;
`base/special/rem_pio2.jl:27-46`. -/
def inv2pi : List Nat := [
  0x28be60db9391054a, 0x7f09d5f47d4d3770, 0x36d8a5664f10e410, 0x7f9458eaf7aef158,
  0x6dc91b8e909374b8, 0x01924bba82746487, 0x3f877ac72c4a69cf, 0xba208d7d4baed121,
  0x3a671c09ad17df90, 0x4e64758e60d4ce7d, 0x272117e2ef7e4a0e, 0xc7fe25fff7816603,
  0xfbcbc462d6829b47, 0xdb4d9fb3c9f2c26d, 0xd3d18fd9a797fa8b, 0x5d49eeb1faf97c5e,
  0xcf41ce7de294a4ba, 0x9afed7ec47e35742, 0x1580cc11bf1edaea]

/-- `INV_2PI[i+1]` for a zero-based index `i`; an index outside the table, which Julia
reads under `@inbounds` only for inputs below the Payne-Hanek range, gives 0;
`base/special/rem_pio2.jl:170-177`. -/
private def inv2piAt (i : Int) : Nat :=
  if i < 0 then 0 else inv2pi.getD i.toNat 0

/-- `highword(x::Float64)`: the upper 32 bits as a `UInt32`; `base/math.jl:1275-1276`. -/
private def highword (x : F64) : Nat := bitsOf x / 2^32

/-- `poshighword(x::Float64)`: `highword(x) & 0x7fffffff`; `base/math.jl:1288-1289`. -/
private def poshighword (x : F64) : Nat := highword x % 2^31

/-- `x >> c` for a `UInt128` `x` and an `Int` count `c`, a left shift when `c < 0`;
`base/int.jl:611-612`. -/
private def shr128 (x : Nat) (c : Int) : Nat :=
  if c ≥ 0 then x >>> c.toNat else (x <<< (-c).toNat) % 2^128

/-- `x << c` for a `UInt128` `x` and an `Int` count `c`, a right shift when `c < 0`;
`base/int.jl:613-614`. -/
private def shl128 (x : Nat) (c : Int) : Nat := shr128 x (-c)

/-- `Base.top_set_bit(x)` for a nonzero unsigned `x`: `8sizeof(x) - leading_zeros(x)`;
`base/int.jl:569`. -/
private def topSetBit (x : Nat) : Int := (Nat.log2 x + 1 : Nat)

/-- `unsafe_trunc(Int, fn)` (`fptosi`) for an integer-valued finite `fn`;
`base/float.jl:410`. -/
private def unsafeTruncInt (fn : F64) : Int :=
  let r := F64.toRat fn
  Int.tdiv r.1 r.2

/-- `cody_waite_2c_pio2(x, fn, n)`: two-constant Cody-Waite reduction by `fn*π/2`.
Every call passes a literal `fn` into this `@inline` function, so both factors of each
`muladd(-fn, c, z)` are compile-time constants, and LLVM folds such an `fmuladd` into the
rounded product `-fn*c` followed by one rounded addition, which this model mirrors;
`base/special/rem_pio2.jl:48-56`. -/
def codyWaite2cPio2 (x fn : F64) (n : Int) : Int × F64 × F64 :=
  let pio21 := lit 0x3ff921fb54400000
  let pio21t := lit 0x3dd0b4611a626331
  let z := F64.add (F64.mul (F64.neg fn) pio21) x
  let y1 := F64.add (F64.mul (F64.neg fn) pio21t) z
  let y2 := F64.add (F64.mul (F64.neg fn) pio21t) (F64.sub z y1)
  (n, y1, y2)

/-- `cody_waite_ext_pio2(x, xhp)`: Cody-Waite reduction with up to three constant pairs;
`2/pi` is the Float64 `2/Float64(π)` with bits `0x3fe45f306dc9c883`; `i` is a `UInt32`
difference; `base/special/rem_pio2.jl:58-95`. -/
def codyWaiteExtPio2 (x : F64) (xhp : Nat) : Int × F64 × F64 :=
  let pio21 := lit 0x3ff921fb54400000
  let pio21t := lit 0x3dd0b4611a626331
  let pio22 := lit 0x3dd0b4611a600000
  let pio22t := lit 0x3ba3198a2e037073
  let pio23 := lit 0x3ba3198a2e000000
  let pio23t := lit 0x397b839a252049c1
  let fn := F64.round (F64.mul x (lit 0x3fe45f306dc9c883)) .RoundNearest
  let r := F64.muladd (F64.neg fn) pio21 x
  let w := F64.mul fn pio21t
  let j := xhp >>> 20
  let y1 := F64.sub r w
  let i := (j + 2^32 - (highword y1 >>> 20) % 2^11) % 2^32
  let (r, w, y1) :=
    if i > 16 then
      let t := r
      let w := F64.mul fn pio22
      let r := F64.sub t w
      let w := F64.muladd fn pio22t (F64.neg (F64.sub (F64.sub t r) w))
      let y1 := F64.sub r w
      let i := (j + 2^32 - (highword y1 >>> 20) % 2^11) % 2^32
      if i > 49 then
        let t := r
        let w := F64.mul fn pio23
        let r := F64.sub t w
        let w := F64.muladd fn pio23t (F64.neg (F64.sub (F64.sub t r) w))
        (r, w, F64.sub r w)
      else (r, w, y1)
    else (r, w, y1)
  let y2 := F64.sub (F64.sub r y1) w
  (unsafeTruncInt fn, y1, y2)

/-- `fromfraction(f::Int128)`: `(z1, z2)` with `z1 + z2 == f / 2^128`, splitting the
magnitude after its leading 26 bits; `base/special/rem_pio2.jl:105-128`. -/
def fromfraction (f : Int) : F64 × F64 :=
  if f == 0 then (F64.zero, F64.zero)
  else
    let s := if f < 0 then 2^63 else 0
    let x := f.natAbs % 2^128
    let n1 := topSetBit x
    let m1 := ((shr128 x (n1 - 26) % 2^64) <<< 27) % 2^64
    let d1 := ((n1 - 128 + 1021) % 2^64).toNat <<< 52 % 2^64
    let z1 := ofBitsU (Nat.lor s ((d1 + m1) % 2^64))
    let x2 := (x + 2^128 - shl128 m1 (n1 - 53)) % 2^128
    if x2 == 0 then (z1, F64.zero)
    else
      let n2 := topSetBit x2
      let m2 := shr128 x2 (n2 - 53) % 2^64
      let d2 := ((n2 - 128 + 1021) % 2^64).toNat <<< 52 % 2^64
      let z2 := ofBitsU (Nat.lor s ((d2 + m2) % 2^64))
      (z1, z2)

/-- `paynehanek(x::Float64)`: Payne-Hanek reduction with a 192-bit window of 1/2π,
returning the quadrant `q ∈ 0:4` and the remainder as `(y_hi, y_lo)`; `flipsign` on the
`UInt128` `w` is wrapping negation (`base/number.jl:255`);
`base/special/rem_pio2.jl:130-211`. -/
def paynehanek (x : F64) : Int × F64 × F64 :=
  let u := bitsOf x
  let X := Nat.lor (u % 2^52) (2^52)
  let rawExponent : Int := ((u % 2^63) >>> 52 : Nat)
  let k := rawExponent - 1023 - 52
  let idx := k >>> 6
  let shift := (k - idx * 64).toNat
  let (a1, a2, a3) :=
    if shift == 0 then (inv2piAt idx, inv2piAt (idx + 1), inv2piAt (idx + 2))
    else
      (Nat.lor (if idx < 0 then 0 else (inv2piAt idx <<< shift) % 2^64)
          (inv2piAt (idx + 1) >>> (64 - shift)),
        Nat.lor ((inv2piAt (idx + 1) <<< shift) % 2^64) (inv2piAt (idx + 2) >>> (64 - shift)),
        Nat.lor ((inv2piAt (idx + 2) <<< shift) % 2^64) (inv2piAt (idx + 3) >>> (64 - shift)))
  let w1 := ((X * a1) % 2^64) <<< 64
  let w2 := X * a2
  let w3 := (X * a3) >>> 64
  let w := (w1 + w2 + w3) % 2^128
  let w := if F64.signbit x then (2^128 - w) % 2^128 else w
  let q : Int := ((((w >>> 125 : Nat) : Int) + 1) >>> 1)
  let fu : Nat := (w <<< 2) % 2^128
  let f : Int := if fu ≥ 2^127 then (fu : Int) - 2^128 else (fu : Int)
  let (zHi, zLo) := fromfraction f
  let pio2 := lit 0x3ff921fb54442d18
  let pio2Hi := lit 0x3ff921fb58000000
  let pio2Lo := lit 0xbe4dde973dcb3b3a
  let yHi := F64.mul (F64.add zHi zLo) pio2
  let yLo := F64.add (F64.add (F64.add (F64.sub (F64.mul zHi pio2Hi) yHi) (F64.mul zHi pio2Lo))
    (F64.mul zLo pio2Hi)) (F64.mul zLo pio2Lo)
  (q, yHi, yLo)

/-- `rem_pio2_kernel(x::Float64)`: `(n, hi, lo)` with `n*π/2 ≈ x - (hi + lo)`, choosing
two-constant Cody-Waite, extended Cody-Waite, or Payne-Hanek by the high word of `|x|`;
`base/special/rem_pio2.jl:222-282`. -/
def remPio2Kernel (x : F64) : Int × F64 × F64 :=
  let xhp := poshighword x
  let pos := F64.lt F64.zero x
  if xhp ≤ 0x400f6a7a then
    if xhp % 2^20 == 0x921fb then codyWaiteExtPio2 x xhp
    else if xhp ≤ 0x4002d97c then
      if pos then codyWaite2cPio2 x (F64.ofInt 1) 1 else codyWaite2cPio2 x (F64.ofInt (-1)) (-1)
    else
      if pos then codyWaite2cPio2 x (F64.ofInt 2) 2 else codyWaite2cPio2 x (F64.ofInt (-2)) (-2)
  else if xhp ≤ 0x401c463b then
    if xhp ≤ 0x4015fdbc then
      if xhp == 0x4012d97c then codyWaiteExtPio2 x xhp
      else if pos then codyWaite2cPio2 x (F64.ofInt 3) 3
      else codyWaite2cPio2 x (F64.ofInt (-3)) (-3)
    else
      if xhp == 0x401921fb then codyWaiteExtPio2 x xhp
      else if pos then codyWaite2cPio2 x (F64.ofInt 4) 4
      else codyWaite2cPio2 x (F64.ofInt (-4)) (-4)
  else if xhp < 0x413921fb then codyWaiteExtPio2 x xhp
  else paynehanek x

end JuliaLean.MathFuncs

/-!
# Model of `base/special/rem_pio2.jl`

Typed Float64 argument reduction. IEEE operations use `base/float.lean`; `DoubleFloat64` uses the
shared representation from `special/trig.lean`. -/

namespace JuliaLean.base.special.rem_pio2

open JuliaLean JuliaLean.Promotion

abbrev F64 := JuliaLean.base.float.FV .f64
abbrev DF64 := JuliaLean.base.special.trig.DF64

-- Reason: license and derivation notes do not define callable Julia methods.
-- UNTRANSLATED
-- Source: base/special/rem_pio2.jl:1-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. Except for the rem_pio2_kernel, and
-- # cody_waite_* methods (see below) license is MIT: https://julialang.org/license
-- 
-- # rem_pio2_kernel and cody_waite_* methods are heavily based on FDLIBM code:
-- # __ieee754_rem_pio2, that is made available under the following licence:
-- 
-- ## Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
-- ##
-- ## Developed at SunPro, a Sun Microsystems, Inc. business.
-- ## Permission to use, copy, modify, and distribute this
-- ## software is freely granted, provided that this notice
-- ## is preserved.
-- 
-- # Bits of 1/2π
-- #   1/2π == sum(x / 0x1p64^i for i,x = enumerate(INV_2PI))
-- # Can be obtained by:
-- #
-- #    setprecision(BigFloat, 4096)
-- #    I = 0.5/big(pi)
-- #    for i = 1:19
-- #        I *= 0x1p64
-- #        k = trunc(UInt64, I)
-- #        @printf "0x%016x,\n" k
-- #        I -= k
-- #    end
-- 
-- /Source

/--
Julia source: base/special/rem_pio2.jl:27-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const INV_2PI = (
    0x28be_60db_9391_054a,
    0x7f09_d5f4_7d4d_3770,
    0x36d8_a566_4f10_e410,
    0x7f94_58ea_f7ae_f158,
    0x6dc9_1b8e_9093_74b8,
    0x0192_4bba_8274_6487,
    0x3f87_7ac7_2c4a_69cf,
    0xba20_8d7d_4bae_d121,
    0x3a67_1c09_ad17_df90,
    0x4e64_758e_60d4_ce7d,
    0x2721_17e2_ef7e_4a0e,
    0xc7fe_25ff_f781_6603,
    0xfbcb_c462_d682_9b47,
    0xdb4d_9fb3_c9f2_c26d,
    0xd3d1_8fd9_a797_fa8b,
    0x5d49_eeb1_faf9_7c5e,
    0xcf41_ce7d_e294_a4ba,
    0x9afe_d7ec_47e3_5742,
    0x1580_cc11_bf1e_daea)

```
-/
def INV_2PI : List (JInt .u64) := [
  JInt.lit .u64 0x28be_60db_9391_054a,
  JInt.lit .u64 0x7f09_d5f4_7d4d_3770,
  JInt.lit .u64 0x36d8_a566_4f10_e410,
  JInt.lit .u64 0x7f94_58ea_f7ae_f158,
  JInt.lit .u64 0x6dc9_1b8e_9093_74b8,
  JInt.lit .u64 0x0192_4bba_8274_6487,
  JInt.lit .u64 0x3f87_7ac7_2c4a_69cf,
  JInt.lit .u64 0xba20_8d7d_4bae_d121,
  JInt.lit .u64 0x3a67_1c09_ad17_df90,
  JInt.lit .u64 0x4e64_758e_60d4_ce7d,
  JInt.lit .u64 0x2721_17e2_ef7e_4a0e,
  JInt.lit .u64 0xc7fe_25ff_f781_6603,
  JInt.lit .u64 0xfbcb_c462_d682_9b47,
  JInt.lit .u64 0xdb4d_9fb3_c9f2_c26d,
  JInt.lit .u64 0xd3d1_8fd9_a797_fa8b,
  JInt.lit .u64 0x5d49_eeb1_faf9_7c5e,
  JInt.lit .u64 0xcf41_ce7d_e294_a4ba,
  JInt.lit .u64 0x9afe_d7ec_47e3_5742,
  JInt.lit .u64 0x1580_cc11_bf1e_daea]

/--
Julia source: base/special/rem_pio2.jl:48-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function cody_waite_2c_pio2(x::Float64, fn, n)
    pio2_1 = 1.57079632673412561417e+00
    pio2_1t = 6.07710050650619224932e-11

    z = muladd(-fn, pio2_1, x) # x - fn*pio2_1
    y1 = muladd(-fn, pio2_1t, z) # z - fn*pio2_1t
    y2 = muladd(-fn, pio2_1t, (z - y1)) # (z - y1) - fn*pio2_1t
    n, DoubleFloat64(y1, y2)
end

```
-/
def codyWaite2cPio2 {Fn NegFn N : Type}
    (negFn : Fn → NegFn) (muladd : NegFn → F64 → F64 → F64)
    (x : F64) (fn : Fn) (n : N) : N × DF64 :=
  let pio2_1 := Fl.ofBits 0x3ff921fb54400000
  let pio2_1t := Fl.ofBits 0x3dd0b4611a626331
  let z := muladd (negFn fn) pio2_1 x
  let y1 := muladd (negFn fn) pio2_1t z
  let y2 := muladd (negFn fn) pio2_1t (JuliaLean.base.float.sub_float z y1)
  (n, ⟨y1, y2⟩)

/--
Julia source: base/special/rem_pio2.jl:58-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function cody_waite_ext_pio2(x::Float64, xhp)
    pio2_1 = 1.57079632673412561417e+00
    pio2_1t = 6.07710050650619224932e-11
    pio2_2 = 6.07710050630396597660e-11
    pio2_2t = 2.02226624879595063154e-21
    pio2_3 = 2.02226624871116645580e-21
    pio2_3t = 8.47842766036889956997e-32

    fn = round(x*(2/pi)) # round to integer
    # on older systems, the above could be faster with
    # rf = 1.5/eps(Float64)
    # fn = (x*(2/pi)+rf)-rf

    r  = muladd(-fn, pio2_1, x) # x - fn*pio2_1
    w  = fn*pio2_1t # 1st round good to 85 bit
    j  = xhp>>20
    y1 = r-w
    high = highword(y1)
    i = j-((high>>20)&0x7ff)
    if i>16  # 2nd iteration needed, good to 118
        t  = r
        w  = fn*pio2_2
        r  = t-w
        w  = muladd(fn, pio2_2t,-((t-r)-w))
        y1 = r-w
        high = highword(y1)
        i = j-((high>>20)&0x7ff)
        if i>49 # 3rd iteration needed, 151 bits acc
            t  = r # will cover all possible cases
            w  = fn*pio2_3
            r  = t-w
            w  = muladd(fn, pio2_3t, -((t-r)-w))
            y1 = r-w
        end
    end
    y2 = (r-y1)-w
    return unsafe_trunc(Int, fn), DoubleFloat64(y1, y2)
end


```
-/
def codyWaiteExtPio2 {H : Type} (shift20 : H → JInt .u32)
    (x : F64) (xhp : H) : JInt .i64 × DF64 :=
  let pio2_1 := Fl.ofBits 0x3ff921fb54400000
  let pio2_1t := Fl.ofBits 0x3dd0b4611a626331
  let pio2_2 := Fl.ofBits 0x3dd0b4611a600000
  let pio2_2t := Fl.ofBits 0x3ba3198a2e037073
  let pio2_3 := Fl.ofBits 0x3ba3198a2e000000
  let pio2_3t := Fl.ofBits 0x397b839a252049c1
  let fn := JuliaLean.base.float.round_Nearest_llvm
    (JuliaLean.base.float.mul_float x (Fl.ofBits 0x3fe45f306dc9c883))
  let r := JuliaLean.base.float.muladd_float (JuliaLean.base.float.neg_float fn) pio2_1 x
  let w := JuliaLean.base.float.mul_float fn pio2_1t
  let j := shift20 xhp
  let y1 := JuliaLean.base.float.sub_float r w
  let high := JuliaLean.base.math.highword64 y1
  let i := j - JuliaLean.base.int.band
    (JuliaLean.base.int.shr_Int high (JInt.lit .i64 20)) (JInt.lit .u32 0x7ff)
  let (r, w, y1) :=
    if i.val > 16 then
      let t := r
      let w := JuliaLean.base.float.mul_float fn pio2_2
      let r := JuliaLean.base.float.sub_float t w
      let w := JuliaLean.base.float.muladd_float fn pio2_2t
        (JuliaLean.base.float.neg_float
          (JuliaLean.base.float.sub_float
            (JuliaLean.base.float.sub_float t r) w))
      let y1 := JuliaLean.base.float.sub_float r w
      let high := JuliaLean.base.math.highword64 y1
      let i := j - JuliaLean.base.int.band
        (JuliaLean.base.int.shr_Int high (JInt.lit .i64 20)) (JInt.lit .u32 0x7ff)
      if i.val > 49 then
        let t := r
        let w := JuliaLean.base.float.mul_float fn pio2_3
        let r := JuliaLean.base.float.sub_float t w
        let w := JuliaLean.base.float.muladd_float fn pio2_3t
          (JuliaLean.base.float.neg_float
            (JuliaLean.base.float.sub_float
              (JuliaLean.base.float.sub_float t r) w))
        (r, w, JuliaLean.base.float.sub_float r w)
      else
        (r, w, y1)
    else
      (r, w, y1)
  let y2 := JuliaLean.base.float.sub_float (JuliaLean.base.float.sub_float r y1) w
  (JuliaLean.base.float.unsafe_trunc .i64 fn, ⟨y1, y2⟩)

/--
Julia source: base/special/rem_pio2.jl:98-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    fromfraction(f::Int128)

Compute a tuple of values `(z1,z2)` such that
    ``z1 + z2 == f / 2^128``
and the significand of `z1` has 27 trailing zeros.
"""
function fromfraction(f::Int128)
    if f == 0
        return (0.0,0.0)
    end

    # 1. get leading term truncated to 26 bits
    s = ((f < 0) % UInt64) << 63     # sign bit
    x = abs(f) % UInt128             # magnitude
    n1 = Base.top_set_bit(x)          # ndigits0z(x,2)
    m1 = ((x >> (n1-26)) % UInt64) << 27
    d1 = ((n1-128+1021) % UInt64) << 52
    z1 = reinterpret(Float64, s | (d1 + m1))

    # 2. compute remaining term
    x2 = (x - (UInt128(m1) << (n1-53)))
    if x2 == 0
        return (z1, 0.0)
    end
    n2 = Base.top_set_bit(x2)
    m2 = (x2 >> (n2-53)) % UInt64
    d2 = ((n2-128+1021) % UInt64) << 52
    z2 = reinterpret(Float64,  s | (d2 + m2))
    return (z1,z2)
end

```
-/
def fromfraction (f : JInt .i128) : F64 × F64 :=
  if f.val = 0 then (JuliaLean.base.float.zero_float .f64, JuliaLean.base.float.zero_float .f64)
  else
    let s : JInt .u64 := JuliaLean.base.int.shl_Int
      (JInt.lit .u64 (if f.val < 0 then 1 else 0)) (JInt.lit .i64 63)
    let x : JInt .u128 := JInt.wrap .u128 (Int.ofNat f.val.natAbs)
    let n1 := JuliaLean.base.int.top_set_bit x
    let m1 := JuliaLean.base.int.shl_Int
      (JuliaLean.base.int.remT .u64
        (JuliaLean.base.int.shr_Int x (n1 - JInt.lit .i64 26)))
      (JInt.lit .i64 27)
    let d1 := JuliaLean.base.int.shl_Int
      (JuliaLean.base.int.remT .u64
        (n1 - JInt.lit .i64 128 + JInt.lit .i64 1021))
      (JInt.lit .i64 52)
    let z1 := JuliaLean.base.float.bitcast_to_float .f64
      (JuliaLean.base.int.or_int s (JuliaLean.base.int.add_int d1 m1))
    let x2 := x - JuliaLean.base.int.shl_Int
      (JuliaLean.base.int.widenTo .u128 m1) (n1 - JInt.lit .i64 53)
    if x2.val = 0 then (z1, JuliaLean.base.float.zero_float .f64)
    else
      let n2 := JuliaLean.base.int.top_set_bit x2
      let m2 := JuliaLean.base.int.remT .u64
        (JuliaLean.base.int.shr_Int x2 (n2 - JInt.lit .i64 53))
      let d2 := JuliaLean.base.int.shl_Int
        (JuliaLean.base.int.remT .u64
          (n2 - JInt.lit .i64 128 + JInt.lit .i64 1021))
        (JInt.lit .i64 52)
      let z2 := JuliaLean.base.float.bitcast_to_float .f64
        (JuliaLean.base.int.or_int s (JuliaLean.base.int.add_int d2 m2))
      (z1, z2)

private def inv2piAt (i : JInt .i64) : JInt .u64 :=
  if i.val < 0 then JInt.lit .u64 0 else INV_2PI.getD i.val.toNat (JInt.lit .u64 0)

private def widemulUInt64 (x y : JInt .u64) : JInt .u128 :=
  (JuliaLean.base.int.widenTo .u128 x) * (JuliaLean.base.int.widenTo .u128 y)

private def flipsignUInt128Float64 (x : JInt .u128) (y : F64) : JInt .u128 :=
  if JuliaLean.base.float.signbit_float y then -x else x

/--
Julia source: base/special/rem_pio2.jl:130-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function paynehanek(x::Float64)
    # 1. Convert to form
    #
    #    x = X * 2^k,
    #
    # where 2^(n-1) <= X < 2^n  is an n-bit integer (n = 53, k = exponent(x)-52 )

    # Computations are integer based, so reinterpret x as UInt64
    u = reinterpret(UInt64, x)
    # Strip x of exponent bits and replace with ^1
    X = (u & significand_mask(Float64)) | (one(UInt64) << significand_bits(Float64))
    # Get k from formula above
    # k = exponent(x)-52
    raw_exponent = ((u & exponent_mask(Float64)) >> significand_bits(Float64)) % Int
    k = raw_exponent - exponent_bias(Float64) - significand_bits(Float64)

    # 2. Let α = 1/2π, then:
    #
    #    α*x mod 1 ≡ [(α*2^k mod 1)*X] mod 1
    #
    # so we can ignore the first k bits of α. Extract the next 3 64-bit parts of α.
    #
    # i.e. equivalent to
    #     setprecision(BigFloat,4096)
    #     α  = 1/(2*big(pi))
    #     A  = mod(ldexp(α,k), 1)
    #     z1 = ldexp(A,64)
    #     a1 = trunc(UInt64, z1)
    #     z2 = ldexp(z1-a1, 64)
    #     a2 = trunc(UInt64, z2)
    #     z3 = ldexp(z2-a2, 64)
    #     a3 = trunc(UInt64, z3)

    # This is equivalent to
    #     idx, shift = divrem(k, 64)
    # but divrem is slower.
    idx = k >> 6

    shift = k - (idx << 6)
    Base.@assume_effects :nothrow :noub @inbounds if shift == 0
        a1 = INV_2PI[idx+1]
        a2 = INV_2PI[idx+2]
        a3 = INV_2PI[idx+3]
    else
        # use shifts to extract the relevant 64 bit window
        a1 = (idx < 0 ? zero(UInt64) : INV_2PI[idx+1] << shift) | (INV_2PI[idx+2] >> (64 - shift))
        a2 = (INV_2PI[idx+2] << shift) | (INV_2PI[idx+3] >> (64 - shift))
        a3 = (INV_2PI[idx+3] << shift) | (INV_2PI[idx+4] >> (64 - shift))
    end

    # 3. Perform the multiplication:
    #
    #      X.  0  0  0
    #   ×  0. a1 a2 a3
    #   ==============
    #      _.  w  w  _
    #
    # (i.e. ignoring integer and lowest bit parts of result)

    w1 = UInt128(X *% a1) << 64 # overflow becomes integer
    w2 = widemul(X, a2)
    w3 = widemul(X, a3) >> 64
    w = w1 +% w2 +% w3      # quotient fraction after division by 2π

    # adjust for sign of x
    w = flipsign(w,x)

    # 4. convert to quadrant, quotient fraction after division by π/2:
    q = (((w>>125)%Int +1)>>1) # nearest quadrant
    f = (w<<2) % Int128 # fraction part of quotient after division by π/2, taking values on [-0.5,0.5)

    # 5. convert quotient fraction to split precision Float64
    z_hi,z_lo = fromfraction(f)

    # 6. multiply by π/2
    pio2 = 1.5707963267948966
    pio2_hi = 1.5707963407039642
    pio2_lo = -1.3909067614167116e-8
    y_hi = (z_hi+z_lo)*pio2
    y_lo = (((z_hi*pio2_hi - y_hi) + z_hi*pio2_lo) + z_lo*pio2_hi) + z_lo*pio2_lo
    return q, DoubleFloat64(y_hi, y_lo)
end

```
-/
def paynehanek (x : F64) : JInt .i64 × DF64 :=
  let u := JuliaLean.base.float.reinterpret_Unsigned_Float64 x
  let X := JuliaLean.base.int.bor
    (JuliaLean.base.int.band u (JuliaLean.base.float.significand_mask .f64))
    (JuliaLean.base.int.shl_Int (JInt.lit .u64 1) (JuliaLean.base.float.significand_bits .f64))
  let rawExponent := JuliaLean.base.int.remT .i64
    (JuliaLean.base.int.shr_Int
      (JuliaLean.base.int.band u (JuliaLean.base.float.exponent_mask .f64))
      (JuliaLean.base.float.significand_bits .f64))
  let k := rawExponent - JuliaLean.base.float.exponent_bias .f64 -
    JuliaLean.base.float.significand_bits .f64
  let idx := JuliaLean.base.int.shr_Int k (JInt.lit .i64 6)
  let shift := k - JuliaLean.base.int.shl_Int idx (JInt.lit .i64 6)
  let idx1 := idx + JInt.lit .i64 1
  let idx2 := idx + JInt.lit .i64 2
  let idx3 := idx + JInt.lit .i64 3
  let (a1, a2, a3) :=
    if shift.val = 0 then
      (inv2piAt idx, inv2piAt idx1, inv2piAt idx2)
    else
      let rightShift := JInt.lit .i64 64 - shift
      let leftA1 := if idx.val < 0 then JInt.lit .u64 0 else JuliaLean.base.int.shl_Int (inv2piAt idx) shift
      let leftA2 := JuliaLean.base.int.shl_Int (inv2piAt idx1) shift
      let leftA3 := JuliaLean.base.int.shl_Int (inv2piAt idx2) shift
      let a1 := JuliaLean.base.int.or_int leftA1 (JuliaLean.base.int.shr_Int (inv2piAt idx1) rightShift)
      let a2 := JuliaLean.base.int.or_int leftA2 (JuliaLean.base.int.shr_Int (inv2piAt idx2) rightShift)
      let a3 := JuliaLean.base.int.or_int leftA3 (JuliaLean.base.int.shr_Int (inv2piAt idx3) rightShift)
      (a1, a2, a3)
  let w1 := JuliaLean.base.int.shl_Int
    (JuliaLean.base.int.widenTo .u128 (X * a1)) (JInt.lit .i64 64)
  let w2 := widemulUInt64 X a2
  let w3 := JuliaLean.base.int.shr_Int (widemulUInt64 X a3) (JInt.lit .i64 64)
  let w := w1 + w2 + w3
  let w := flipsignUInt128Float64 w x
  let q := JuliaLean.base.int.shr_Int
    (JuliaLean.base.int.remT .i64 (JuliaLean.base.int.shr_Int w (JInt.lit .i64 125)) + JInt.lit .i64 1)
    (JInt.lit .i64 1)
  let f := JuliaLean.base.int.remT .i128 (JuliaLean.base.int.shl_Int w (JInt.lit .i64 2))
  let (zHi, zLo) := fromfraction f
  let pio2 := Fl.ofBits 0x3ff921fb54442d18
  let pio2Hi := Fl.ofBits 0x3ff921fb58000000
  let pio2Lo := Fl.ofBits 0xbe4dde973dcb3b3a
  let yHi := JuliaLean.base.float.mul_float (JuliaLean.base.float.add_float zHi zLo) pio2
  let yLo := JuliaLean.base.float.add_float
    (JuliaLean.base.float.add_float
      (JuliaLean.base.float.add_float
        (JuliaLean.base.float.sub_float (JuliaLean.base.float.mul_float zHi pio2Hi) yHi)
        (JuliaLean.base.float.mul_float zHi pio2Lo))
      (JuliaLean.base.float.mul_float zLo pio2Hi))
    (JuliaLean.base.float.mul_float zLo pio2Lo)
  (q, ⟨yHi, yLo⟩)

/--
Julia source: base/special/rem_pio2.jl:213-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    rem_pio2_kernel(x::Union{Float32, Float64})

Calculate `x` divided by `π/2` accurately for arbitrarily large `x`.
Returns a pair `(k, r)`, where `k` is the quadrant of the result
(multiple of π/2) and `r` is the remainder, such that ``k * π/2 = x - r``.
The remainder is given as a double-double pair.
`k` is positive if `x > 0` and is negative if `x ≤ 0`.
"""
@inline function rem_pio2_kernel(x::Float64) # accurate to 1e-22
    xhp = poshighword(x)
    #  xhp <= highword(5pi/4) implies |x| ~<= 5pi/4,
    if xhp <= 0x400f6a7a
        #  last five bits of xhp == last five bits of highword(pi/2) or
        #  highword(2pi/2) implies |x| ~= pi/2 or 2pi/2,
        if (xhp & 0xfffff) == 0x921fb # use precise Cody Waite scheme
            return cody_waite_ext_pio2(x, xhp)
        end
        # use Cody Waite with two constants
        #  xhp <= highword(3pi/4) implies |x| ~<= 3pi/4
        if xhp <= 0x4002d97c
            if x > 0.0
                return cody_waite_2c_pio2(x, 1.0, 1)
            else
                return cody_waite_2c_pio2(x, -1.0, -1)
            end
        # 3pi/4 < |x| <= 5pi/4
        else
            if x > 0.0
                return cody_waite_2c_pio2(x, 2.0, 2)
            else
                return cody_waite_2c_pio2(x, -2.0, -2)
            end
        end
    end
    #  xhp <= highword(9pi/4) implies |x| ~<= 9pi/4
    if xhp <= 0x401c463b
        #  xhp <= highword(7pi/4) implies |x| ~<= 7pi/4
        if xhp <= 0x4015fdbc
            #  xhp == highword(3pi/2) implies |x| ~= 3pi/2
            if xhp == 0x4012d97c # use precise Cody Waite scheme
                return cody_waite_ext_pio2(x, xhp)
            end
            # use Cody Waite with two constants
            if x > 0.0
                return cody_waite_2c_pio2(x, 3.0, 3)
            else
                return cody_waite_2c_pio2(x, -3.0, -3)
            end
        # 7pi/4 < |x| =< 9pi/4
        else
            #  xhp == highword(4pi/2) implies |x| ~= 4pi/2
            if xhp == 0x401921fb # use precise Cody Waite scheme
                return cody_waite_ext_pio2(x, xhp)
            end
            # use Cody Waite with two constants
            if x > 0.0
                return cody_waite_2c_pio2(x, 4.0, 4)
            else
                return cody_waite_2c_pio2(x, -4.0, -4)
            end
        end
    end
    #  xhp < highword(2.0^20*pi/2) implies |x| ~< 2^20*pi/2
    if xhp < 0x413921fb # use precise Cody Waite scheme
        return cody_waite_ext_pio2(x, xhp)
    end
    # if |x| >= 2^20*pi/2 switch to Payne Hanek
    return paynehanek(x)
end

```
-/
def remPio2Kernel (x : F64) : JInt .i64 × DF64 :=
  let xhp := JuliaLean.base.math.poshighword64 x
  if xhp.val ≤ 0x400f6a7a then
    if (JuliaLean.base.int.band xhp (JInt.lit .u32 0xfffff)).val == 0x921fb then
      codyWaiteExtPio2 (fun h => JuliaLean.base.int.shr_Int h (JInt.lit .i64 20)) x xhp
    else if xhp.val ≤ 0x4002d97c then
      if JuliaLean.base.float.lt_float (JuliaLean.base.float.zero_float .f64) x then
        codyWaite2cPio2 (fun v : F64 => JuliaLean.base.float.neg_float v)
          (fun (a b c : F64) => JuliaLean.base.float.muladd_float a b c)
          x (Fl.ofBits 0x3ff0000000000000) (JInt.lit .i64 1)
      else
        codyWaite2cPio2 (fun v : F64 => JuliaLean.base.float.neg_float v)
          (fun (a b c : F64) => JuliaLean.base.float.muladd_float a b c)
          x (Fl.ofBits 0xbff0000000000000) (JInt.lit .i64 (-1))
    else if JuliaLean.base.float.lt_float (JuliaLean.base.float.zero_float .f64) x then
      codyWaite2cPio2 (fun v : F64 => JuliaLean.base.float.neg_float v)
        (fun (a b c : F64) => JuliaLean.base.float.muladd_float a b c)
        x (Fl.ofBits 0x4000000000000000) (JInt.lit .i64 2)
    else
      codyWaite2cPio2 (fun v : F64 => JuliaLean.base.float.neg_float v)
        (fun (a b c : F64) => JuliaLean.base.float.muladd_float a b c)
        x (Fl.ofBits 0xc000000000000000) (JInt.lit .i64 (-2))
  else if xhp.val ≤ 0x401c463b then
    if xhp.val ≤ 0x4015fdbc then
      if xhp.val == 0x4012d97c then
        codyWaiteExtPio2 (fun h => JuliaLean.base.int.shr_Int h (JInt.lit .i64 20)) x xhp
      else if JuliaLean.base.float.lt_float (JuliaLean.base.float.zero_float .f64) x then
        codyWaite2cPio2 (fun v : F64 => JuliaLean.base.float.neg_float v)
          (fun (a b c : F64) => JuliaLean.base.float.muladd_float a b c)
          x (Fl.ofBits 0x4008000000000000) (JInt.lit .i64 3)
      else
        codyWaite2cPio2 (fun v : F64 => JuliaLean.base.float.neg_float v)
          (fun (a b c : F64) => JuliaLean.base.float.muladd_float a b c)
          x (Fl.ofBits 0xc008000000000000) (JInt.lit .i64 (-3))
    else if xhp.val == 0x401921fb then
      codyWaiteExtPio2 (fun h => JuliaLean.base.int.shr_Int h (JInt.lit .i64 20)) x xhp
    else if JuliaLean.base.float.lt_float (JuliaLean.base.float.zero_float .f64) x then
      codyWaite2cPio2 (fun v : F64 => JuliaLean.base.float.neg_float v)
        (fun (a b c : F64) => JuliaLean.base.float.muladd_float a b c)
        x (Fl.ofBits 0x4010000000000000) (JInt.lit .i64 4)
    else
      codyWaite2cPio2 (fun v : F64 => JuliaLean.base.float.neg_float v)
        (fun (a b c : F64) => JuliaLean.base.float.muladd_float a b c)
        x (Fl.ofBits 0xc010000000000000) (JInt.lit .i64 (-4))
  else if xhp.val < 0x413921fb then
    codyWaiteExtPio2 (fun h => JuliaLean.base.int.shr_Int h (JInt.lit .i64 20)) x xhp
  else
    paynehanek x

/- `DoubleFloat32` is the one-field Float64 result container declared by `trig.jl`. -/
structure DF32 where
  hi : F64

/--
Julia source: base/special/rem_pio2.jl:284-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function rem_pio2_kernel(x::Float32)
    xd = convert(Float64, x)
    # use Cody Waite reduction with two coefficients
    if abs(x) < Float32(pi*0x1p27) # x < 2^28 * pi/2
        fn = round(xd * (2/pi))
        r  = fma(fn, -pi/2, xd)
        y = fma(fn, -6.123233995736766e-17, r) # big(pi)/2 - pi/2 remainder
        return unsafe_trunc(Int, fn), DoubleFloat32(y)
    end
    n, y = @noinline paynehanek(xd)
    return n, DoubleFloat32(y.hi)
end
```
-/
def remPio2Kernel32 (x : JuliaLean.base.float.FV .f32) : JInt .i64 × DF32 :=
  let xd := JuliaLean.base.float.convertFloat .f64 x
  if JuliaLean.base.float.lt_float (JuliaLean.base.float.abs_float x) (Fl.ofBits 0x4dc90fdb) then
    let fn := JuliaLean.base.float.round_Nearest_llvm
      (JuliaLean.base.float.mul_float xd (Fl.ofBits 0x3fe45f306dc9c883))
    let r := JuliaLean.base.float.muladd_float fn (Fl.ofBits 0xbff921fb54442d18) xd
    let y := JuliaLean.base.float.muladd_float fn (Fl.ofBits 0xbc91a62633145c07) r
    (JuliaLean.base.float.unsafe_trunc .i64 fn, ⟨y⟩)
  else
    let (n, y) := paynehanek xd
    (n, ⟨y.hi⟩)

end JuliaLean.base.special.rem_pio2

namespace JuliaLean.MathCov.Special

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

/-- `rem_pio2_kernel(x::Float32)`: `(n, DoubleFloat32(y))`; `base/special/rem_pio2.jl:284-295`. -/
def remPio2Kernel32 (x : FV .f32) : Int × FV .f64 :=
  let xd : FV .f64 := conv x
  if lt (abs x) remPio2Bound32 then
    let fn := roundI (mul xd twoOverPi64)
    let r := fma fn negPiOver2 xd
    let y := fma fn pio2Tail r
    ((unsafeTrunc .i64 fn).val, y)
  else
    let (n, hi, _) := MathFuncs.paynehanek (Fl.toF64 xd)
    (n, Fl.ofF64 hi)

end JuliaLean.MathCov.Special

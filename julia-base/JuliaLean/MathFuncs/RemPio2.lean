import JuliaLean.MathFuncs.Prelude

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

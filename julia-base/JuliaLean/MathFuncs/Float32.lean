import JuliaLean.MathFuncs.Prelude

/-!
Binary32 storage and the two conversions `Float64(::Float32)` (exact `fpext`) and
`Float32(::Float64)` (`fptrunc`, nearest with ties to even, gradual underflow), from
`base/float.jl:343,346` at master `bbfa0ce4150`. Only these conversions are modelled;
Float32 arithmetic goes through Float64 in the methods that use them.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- Binary32 storage; `base/float.jl:112-116`. -/
abbrev F32 := BitVec 32

namespace F32

/-- The raw exponent field. -/
def exponentField (x : F32) : Nat := x.toNat / 2^23 % 256

/-- The stored fraction. -/
def fraction (x : F32) : Nat := x.toNat % 2^23

/-- Sign bit. -/
def signbit (x : F32) : Bool := decide (x.toNat ≥ 2^31)

/-- Finite classification. -/
def isfinite (x : F32) : Bool := exponentField x != 255

/-- Exact value `(numerator, denominator)` of a finite binary32 value. -/
def toRat (x : F32) : Int × Nat :=
  let e := exponentField x
  let m := fraction x + if e == 0 then 0 else 2^23
  let p : Int := if e == 0 then -149 else (e : Int) - 150
  let s : Int := if signbit x then -(m : Int) else (m : Int)
  if p ≥ 0 then (s * (2^p.toNat : Nat), 1) else (s, 2^(-p).toNat)

end F32

/-- Floor of log2(n/d) for positive n and d. -/
private def floorLog2Q (n d : Nat) : Int :=
  let e : Int := (n.log2 : Int) - (d.log2 : Int)
  let below := if e ≥ 0 then n < d * 2^e.toNat else n * 2^(-e).toNat < d
  if below then e - 1 else e

/-- Nearest integer to n/d, ties to even. -/
private def roundQ (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2*r > d || (2*r == d && q % 2 == 1) then q + 1 else q

/-- Round a nonzero rational of the given sign to binary32 bits, nearest with ties to even. -/
private def roundToF32 (negative : Bool) (a d : Nat) : F32 :=
  let signBits := if negative then 2^31 else 0
  let e := floorLog2Q a d
  if e ≥ 128 then BitVec.ofNat 32 (signBits + 0x7f800000)
  else if e < -150 then BitVec.ofNat 32 signBits
  else
    let k := max (e - 23) (-149)
    let scaled := if k ≥ 0 then (a, d * 2^k.toNat) else (a * 2^(-k).toNat, d)
    let q := roundQ scaled.1 scaled.2
    if q == 0 then BitVec.ofNat 32 signBits
    else
      let carry := q ≥ 2^24
      let m := if carry then q / 2 else q
      let p := if carry then k + 1 else k
      let ex := p + 150
      if ex ≥ 255 then BitVec.ofNat 32 (signBits + 0x7f800000)
      else
        let mag := if m < 2^23 then m else ex.toNat * 2^23 + (m - 2^23)
        BitVec.ofNat 32 (signBits + mag)

/-- `Float32(x::Float64)`, the `fptrunc` intrinsic; `base/float.jl:343`. NaNs keep the
sign and the top 22 payload bits and become quiet. -/
def toF32 (x : F64) : F32 :=
  let b := F64.toBits x
  let signBits := if F64.signbit x then 2^31 else 0
  if F64.isnan x then BitVec.ofNat 32 (signBits + 0x7fc00000 + (F64.fraction x / 2^29) % 2^22)
  else if F64.isinf x then BitVec.ofNat 32 (signBits + 0x7f800000)
  else if F64.iszero x then BitVec.ofNat 32 (b / 2^32)
  else
    let r := F64.toRat x
    roundToF32 (F64.signbit x) r.1.natAbs r.2

/-- `Float64(x::Float32)`, the exact `fpext` intrinsic; `base/float.jl:346`. NaN payloads
are shifted into the top fraction bits and quieted. -/
def ofF32 (x : F32) : F64 :=
  let signBits := if F32.signbit x then 2^63 else 0
  if F32.exponentField x == 255 then
    if F32.fraction x == 0 then F64.ofBits (signBits + 0x7ff0000000000000)
    else F64.ofBits (signBits + 0x7ff8000000000000 + (F32.fraction x % 2^22) * 2^29)
  else
    let r := F32.toRat x
    F64.roundRat r.1 r.2 (F32.signbit x)

end JuliaLean.MathFuncs

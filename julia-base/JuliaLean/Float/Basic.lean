import JuliaLean.Core

/-!
Kernel-computable binary64 semantics for Julia's IEEE intrinsics.

The representation follows `base/float.jl:98-111` at Julia `bbfa0ce4150`.
Finite arithmetic uses exact integers and rounds once, nearest with ties to even.
The model assumes the default rounding mode and gradual underflow.

LLVM does not prescribe the sign/payload of every NaN result. Arithmetic here
quiets the first NaN operand, retaining its sign and payload; an invalid operation
without a NaN operand returns the x86 indefinite quiet NaN. Claims about portable
Julia arithmetic should compare NaNs with `isequal`, rather than their payloads.
-/

namespace JuliaLean.Float

/-- Binary64 storage; `base/float.jl:98-111`. -/
abbrev F64 := BitVec 64

namespace F64

/-- Reinterpret a UInt64 bit pattern, reducing modulo 2^64; `base/float.jl:98-105`. -/
def ofBits (n : Nat) : F64 := BitVec.ofNat 64 n

/-- Reinterpret binary64 as UInt64; `base/float.jl:98-105`. -/
def toBits (x : F64) : Nat := x.toNat

/-- The raw exponent field; `base/float.jl:498-500`. -/
def exponentField (x : F64) : Nat := toBits x / 2^52 % 2048

/-- The stored fraction; `base/float.jl:111,125`. -/
def fraction (x : F64) : Nat := toBits x % 2^52

/-- Sign bit, including signed zeros and NaNs; `base/floatfuncs.jl:15`. -/
def signbit (x : F64) : Bool := decide (toBits x ≥ 2^63)

/-- Remove the sign bit; `base/float.jl:692`. -/
def abs (x : F64) : F64 := ofBits (toBits x % 2^63)

/-- Toggle the sign bit without changing a NaN payload; `base/float.jl:485`. -/
def neg (x : F64) : F64 :=
  if signbit x then ofBits (toBits x - 2^63) else ofBits (toBits x + 2^63)

/-- Signed zero; `base/float.jl:216-225`. -/
def zero (neg : Bool := false) : F64 := ofBits (if neg then 2^63 else 0)

/-- Signed infinity; `base/float.jl:38,203-208`. -/
def inf (neg : Bool := false) : F64 :=
  ofBits ((if neg then 2^63 else 0) + 0x7ff0000000000000)

/-- Julia's default NaN; `base/float.jl:39`. -/
def nan : F64 := ofBits 0x7ff8000000000000

/-- The binary64 representation of one; `base/float.jl:109`. -/
def one : F64 := ofBits 0x3ff0000000000000

/-- IEEE unordered classification underlying `x != x`; `base/float.jl:702`. -/
def isnan (x : F64) : Bool :=
  exponentField x == 2047 && fraction x != 0

/-- `abs(x) === Inf`; `base/float.jl:717`. -/
def isinf (x : F64) : Bool := toBits (abs x) == 0x7ff0000000000000

/-- Equivalent to `!isnan(x-x)`; `base/float.jl:705`. -/
def isfinite (x : F64) : Bool := exponentField x != 2047

/-- IEEE equality with zero, identifying both signs; `base/float.jl:615`. -/
def iszero (x : F64) : Bool := toBits (abs x) == 0

/-- Set the quiet bit while retaining the operand's NaN sign and payload. -/
private def quietNaN (x : F64) : F64 :=
  if fraction x < 2^51 then ofBits (toBits x + 2^51) else x

/-- The x86 indefinite NaN returned by an invalid arithmetic operation. -/
private def invalidNaN : F64 := ofBits 0xfff8000000000000

/--
Exact finite value from `base/float.jl:769-778`, with the power of two moved into
an integer numerator or positive denominator. Nonfinite values return `(0,0)`.
-/
def toRat (x : F64) : Int × Nat :=
  if !isfinite x then (0, 0)
  else
    let e := exponentField x
    let m := fraction x + if e == 0 then 0 else 2^52
    let p : Int := if e == 0 then -1074 else (e : Int) - 1075
    let s : Int := if signbit x then -(m : Int) else (m : Int)
    if p ≥ 0 then (s * (2^p.toNat : Nat), 1)
    else (s, 2^(-p).toNat)

/-- Floor of log2(n/d), for positive n and d, using exact comparisons. -/
private def floorLog2Rat (n d : Nat) : Int :=
  let e : Int := (n.log2 : Int) - (d.log2 : Int)
  let below := if e ≥ 0 then n < d * 2^e.toNat else n * 2^(-e).toNat < d
  if below then e - 1 else e

/-- Round a nonnegative rational to the nearest integer, ties to even. -/
private def roundQuotient (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2*r > d || (2*r == d && q % 2 == 1) then q + 1 else q

/-- Pack q*2^k after significand rounding; q has at most 54 bits. -/
private def packRounded (negative : Bool) (q : Nat) (k : Int) : F64 :=
  if q == 0 then zero negative
  else
    let carry := q ≥ 2^53
    let m := if carry then q / 2 else q
    let p := if carry then k + 1 else k
    let exponent := p + 1075
    if exponent ≥ 2047 then inf negative
    else
      let magnitude :=
        if m < 2^52 then m
        else exponent.toNat * 2^52 + (m - 2^52)
      ofBits ((if negative then 2^63 else 0) + magnitude)

/--
Round an exact rational to binary64, nearest with ties to even, including gradual
underflow and overflow. This supplies the IEEE primitive semantics used at
`base/float.jl:246,252,487-490`. The final argument supplies the sign only when
n is exactly zero. A zero denominator denotes an infinity, or NaN when n is zero.
-/
def roundRat (n : Int) (d : Nat) (zeroSign : Bool) : F64 :=
  if d == 0 then if n == 0 then nan else inf (decide (n < 0))
  else if n == 0 then zero zeroSign
  else
    let negative := decide (n < 0)
    let a := n.natAbs
    let e := floorLog2Rat a d
    if e ≥ 1024 then inf negative
    else if e < -1075 then zero negative
    else
      let k := max (e - 52) (-1074)
      let scaled :=
        if k ≥ 0 then (a, d * 2^k.toNat)
        else (a * 2^(-k).toNat, d)
      packRounded negative (roundQuotient scaled.1 scaled.2) k

/-- Correctly rounded `sitofp`/`uitofp`; `base/float.jl:243-256`. -/
def ofInt (n : Int) : F64 := roundRat n 1 false

/-- IEEE addition intrinsic; `base/float.jl:487`. -/
def add (x y : F64) : F64 :=
  if isnan x then quietNaN x
  else if isnan y then quietNaN y
  else if isinf x then
    if isinf y && signbit x != signbit y then invalidNaN else x
  else if isinf y then y
  else
    let a := toRat x
    let b := toRat y
    roundRat (a.1 * (b.2 : Int) + b.1 * (a.2 : Int)) (a.2 * b.2)
      (signbit x && signbit y)

/-- IEEE subtraction intrinsic; `base/float.jl:488`. -/
def sub (x y : F64) : F64 :=
  if isnan x then quietNaN x
  else if isnan y then quietNaN y
  else add x (neg y)

/-- IEEE multiplication intrinsic; `base/float.jl:489`. -/
def mul (x y : F64) : F64 :=
  let negative := signbit x != signbit y
  if isnan x then quietNaN x
  else if isnan y then quietNaN y
  else if (isinf x && iszero y) || (iszero x && isinf y) then invalidNaN
  else if isinf x || isinf y then inf negative
  else
    let a := toRat x
    let b := toRat y
    roundRat (a.1 * b.1) (a.2 * b.2) negative

/-- IEEE division intrinsic; `base/float.jl:490`. -/
def div (x y : F64) : F64 :=
  let negative := signbit x != signbit y
  if isnan x then quietNaN x
  else if isnan y then quietNaN y
  else if (isinf x && isinf y) || (iszero x && iszero y) then invalidNaN
  else if isinf x then inf negative
  else if isinf y then zero negative
  else if iszero y then inf negative
  else
    let a := toRat x
    let b := toRat y
    let numerator := a.1 * (b.2 : Int)
    roundRat (if b.1 < 0 then -numerator else numerator)
      (a.2 * b.1.natAbs) negative

/--
Fused multiply-add with one final rounding; `base/floatfuncs.jl:343-346,464-465`.
The exact finite product is retained even when a separately rounded product would
underflow or overflow.
-/
def fma (x y z : F64) : F64 :=
  let negative := signbit x != signbit y
  if isnan x then quietNaN x
  else if isnan y then quietNaN y
  else if isnan z then quietNaN z
  else if (isinf x && iszero y) || (iszero x && isinf y) then invalidNaN
  else if isinf x || isinf y then
    if isinf z && negative != signbit z then invalidNaN else inf negative
  else if isinf z then z
  else
    let a := toRat x
    let b := toRat y
    let c := toRat z
    roundRat (a.1 * b.1 * (c.2 : Int) + c.1 * ((a.2 * b.2 : Nat) : Int))
      (a.2 * b.2 * c.2) (negative && signbit z)

/--
`base/float.jl:492`: the fused x86-64 interpretation of `muladd_float`.
Julia permits contraction with surrounding expressions and compiler-dependent
results; this fixes the single-call fused interpretation for this model.
-/
def muladd (x y z : F64) : F64 := fma x y z

/-- IEEE ordered equality; `base/float.jl:615`. -/
def eq (x y : F64) : Bool :=
  !isnan x && !isnan y && (toBits x == toBits y || (iszero x && iszero y))

/-- IEEE ordered less-than; `base/float.jl:616`. -/
def lt (x y : F64) : Bool :=
  if isnan x || isnan y || (iszero x && iszero y) then false
  else if signbit x != signbit y then signbit x
  else if signbit x then toBits x > toBits y else toBits x < toBits y

/-- IEEE ordered less-or-equal; `base/float.jl:617`. -/
def le (x y : F64) : Bool := lt x y || eq x y

/-- NaNs compare equal, but signed zeros differ; `base/float.jl:619`. -/
def isequal (x y : F64) : Bool :=
  (isnan x && isnan y) || toBits x == toBits y

/-- Julia's total order, with -0 before +0 and NaNs last; `base/float.jl:621-634`. -/
def isless (x y : F64) : Bool :=
  if isnan x || isnan y then !isnan x
  else if signbit x != signbit y then signbit x
  else if signbit x then toBits x > toBits y else toBits x < toBits y

/-- Binary search for floor(sqrt(n/d)) with an exclusive upper endpoint. -/
private def sqrtFloor (n d : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if mid * mid * d ≤ n then sqrtFloor n d fuel mid hi
      else sqrtFloor n d fuel lo mid

/--
`base/math.jl:629-632`: reject x<0, then correctly rounded `sqrt_llvm`.
The scaled root has at most 53 significand bits. Integer square-root search and
an exact squared-midpoint comparison implement rounding without approximation.
-/
def sqrt (x : F64) : Jl F64 :=
  if lt x (zero false) then .error (.domainError "sqrt")
  else if isnan x then .ok (quietNaN x)
  else if isinf x || iszero x then .ok x
  else
    let a := toRat x
    let e := floorLog2Rat a.1.natAbs a.2
    let k := e / 2 - 52
    let twiceK := 2*k
    let scaled :=
      if twiceK ≥ 0 then (a.1.natAbs, a.2 * 2^twiceK.toNat)
      else (a.1.natAbs * 2^(-twiceK).toNat, a.2)
    let q := sqrtFloor scaled.1 scaled.2 54 0 (2^53 + 1)
    let midpointSquare := (2*q + 1) * (2*q + 1) * scaled.2
    let target := 4 * scaled.1
    let rounded :=
      if target > midpointSquare || (target == midpointSquare && q % 2 == 1)
      then q + 1 else q
    .ok (packRounded false rounded k)

end F64
end JuliaLean.Float

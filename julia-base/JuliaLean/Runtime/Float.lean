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
def floorLog2Rat (n d : Nat) : Int :=
  let e : Int := (n.log2 : Int) - (d.log2 : Int)
  let below := if e ≥ 0 then n < d * 2^e.toNat else n * 2^(-e).toNat < d
  if below then e - 1 else e

/-- Round a nonnegative rational to the nearest integer, ties to even. -/
def roundQuotient (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2*r > d || (2*r == d && q % 2 == 1) then q + 1 else q

/-- Pack q*2^k after significand rounding; q has at most 54 bits. -/
def packRounded (negative : Bool) (q : Nat) (k : Int) : F64 :=
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
`base/float.jl:492`: the fused x86 interpretation of `muladd_float`.
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
/-!
Generic IEEE binary interchange formats for Julia's `Float16`, `Float32` and
`Float64` at master `bbfa0ce4150`. A value is its bit pattern. Finite values decode
exactly to rationals; rounding is nearest with ties to even and gradual underflow,
the semantics of the `sitofp`/`uitofp`/`fptrunc`/`fpext` intrinsics used at
`base/float.jl:243-256,342-349`. `Float64` values convert losslessly to the
shared `JuliaLean.Float.F64` model by reinterpreting their bits.
-/

namespace JuliaLean.Promotion

open JuliaLean.Float

/-- Exponent and stored significand widths; `base/float.jl:107-137`. -/
structure Fmt where
  eb : Nat
  sb : Nat
  deriving DecidableEq, Repr

namespace Fmt
/-- Total bit width, `8*sizeof(T)`. -/
def width (f : Fmt) : Nat := 1 + f.eb + f.sb
/-- `exponent_bias(T)`; `base/float.jl:133`. -/
def bias (f : Fmt) : Nat := 2 ^ (f.eb - 1) - 1
/-- Raw exponent of infinities and NaNs, `exponent_raw_max(T)`; `base/float.jl:137`. -/
def emax (f : Fmt) : Nat := 2 ^ f.eb - 1
end Fmt

/-- `Float16`. -/
def half : Fmt := ⟨5, 10⟩
/-- `Float32`. -/
def single : Fmt := ⟨8, 23⟩
/-- `Float64`. -/
def double : Fmt := ⟨11, 52⟩

theorem width_pos (f : Fmt) : 0 < 2 ^ f.width := Nat.pow_pos (by decide)

/-- A value of the format, as its bit pattern (`reinterpret(Unsigned, x)`). -/
structure Fl (f : Fmt) where
  bits : Fin (2 ^ f.width)
  deriving DecidableEq, Repr

namespace Fl

variable {f : Fmt}

/-- `reinterpret(T, u)`, reducing modulo `2^width`. -/
def ofBits (n : Nat) : Fl f := ⟨⟨n % 2 ^ f.width, Nat.mod_lt _ (width_pos f)⟩⟩

def toBits (x : Fl f) : Nat := x.bits.val

/-- Raw exponent field; `base/float.jl:120,498-500`. -/
def expField (x : Fl f) : Nat := x.toBits / 2 ^ f.sb % 2 ^ f.eb

/-- Stored fraction; `base/float.jl:123`. -/
def frac (x : Fl f) : Nat := x.toBits % 2 ^ f.sb

/-- Sign bit; `base/floatfuncs.jl:15`. -/
def signbit (x : Fl f) : Bool := decide (x.toBits ≥ 2 ^ (f.eb + f.sb))

/-- Bits without the sign; `abs_float`, `base/float.jl:692`. -/
def magnitude (x : Fl f) : Nat := x.toBits % 2 ^ (f.eb + f.sb)

def isnan (x : Fl f) : Bool := x.expField == f.emax && x.frac != 0
def isinf (x : Fl f) : Bool := x.expField == f.emax && x.frac == 0
def isfinite (x : Fl f) : Bool := x.expField != f.emax
def iszero (x : Fl f) : Bool := x.magnitude == 0

/-- Signed zero and infinity, and the default NaN `0x7e00`/`0x7fc00000`. -/
def zero (neg : Bool := false) : Fl f := ofBits (if neg then 2 ^ (f.eb + f.sb) else 0)
def inf (neg : Bool := false) : Fl f :=
  ofBits ((if neg then 2 ^ (f.eb + f.sb) else 0) + f.emax * 2 ^ f.sb)
def nan : Fl f := ofBits (f.emax * 2 ^ f.sb + 2 ^ (f.sb - 1))

/-- `floatmax(T)`; `base/float.jl:1040-1046`. -/
def floatmax : Fl f := ofBits ((f.emax - 1) * 2 ^ f.sb + (2 ^ f.sb - 1))

/-- `-x`, toggling the sign bit; `base/float.jl:485`. -/
def neg (x : Fl f) : Fl f :=
  if x.signbit then ofBits (x.toBits - 2 ^ (f.eb + f.sb)) else ofBits (x.toBits + 2 ^ (f.eb + f.sb))

/-- Exact finite value `num / den` (`den > 0`), as in `decompose`, `base/float.jl:747-778`.
Nonfinite values return `(0,0)`. -/
def toRat (x : Fl f) : Int × Nat :=
  if !x.isfinite then (0, 0)
  else
    let e := x.expField
    let m := x.frac + if e == 0 then 0 else 2 ^ f.sb
    let p : Int := if e == 0 then 1 - (f.bias : Int) - f.sb else (e : Int) - f.bias - f.sb
    let s : Int := if x.signbit then -(m : Int) else (m : Int)
    if p ≥ 0 then (s * (2 ^ p.toNat : Nat), 1) else (s, 2 ^ (-p).toNat)

/-- Floor of log2(n/d) for positive n and d. -/
def floorLog2Rat (n d : Nat) : Int :=
  let e : Int := (n.log2 : Int) - (d.log2 : Int)
  let below := if e ≥ 0 then n < d * 2 ^ e.toNat else n * 2 ^ (-e).toNat < d
  if below then e - 1 else e

/-- Nearest integer to n/d, ties to even. -/
def roundQuotient (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q

/-- Pack `q*2^k` after significand rounding; `q` has at most `sb+2` bits. -/
def packRounded (negative : Bool) (q : Nat) (k : Int) : Fl f :=
  if q == 0 then zero negative
  else
    let carry := q ≥ 2 ^ (f.sb + 1)
    let m := if carry then q / 2 else q
    let p := if carry then k + 1 else k
    let exponent := p + f.bias + f.sb
    if exponent ≥ f.emax then inf negative
    else
      let mag := if m < 2 ^ f.sb then m else exponent.toNat * 2 ^ f.sb + (m - 2 ^ f.sb)
      ofBits ((if negative then 2 ^ (f.eb + f.sb) else 0) + mag)

/-- Round the exact rational `n/d` to the format, nearest with ties to even, with gradual
underflow and overflow to infinity. `zeroSign` gives the sign of an exact zero. A zero
denominator denotes an infinity, or NaN when `n` is zero. -/
def roundRat (n : Int) (d : Nat) (zeroSign : Bool) : Fl f :=
  if d == 0 then if n == 0 then nan else inf (decide (n < 0))
  else if n == 0 then zero zeroSign
  else
    let negative := decide (n < 0)
    let a := n.natAbs
    let e := floorLog2Rat a d
    if e ≥ (f.emax : Int) - f.bias then inf negative
    else if e < -((f.bias : Int) + f.sb) - 1 then zero negative
    else
      let k := max (e - f.sb) (1 - (f.bias : Int) - f.sb)
      let scaled := if k ≥ 0 then (a, d * 2 ^ k.toNat) else (a * 2 ^ (-k).toNat, d)
      packRounded negative (roundQuotient scaled.1 scaled.2) k

/-- `sitofp`/`uitofp` from a fixed-width integer; `base/float.jl:243-256`. -/
def ofInt (n : Int) : Fl f := roundRat n 1 false

/-- Conversion between formats (`fpext`/`fptrunc`, `base/float.jl:342-349`); the identity
for the same format (`base/boot.jl:1195`). NaNs keep their sign, are
quieted, and keep the leading payload bits. -/
def convert {g : Fmt} (x : Fl g) : Fl f :=
  if f == g then ofBits x.toBits
  else if x.isnan then
    let payload := if f.sb ≥ g.sb then x.frac * 2 ^ (f.sb - g.sb) else x.frac / 2 ^ (g.sb - f.sb)
    ofBits ((if x.signbit then 2 ^ (f.eb + f.sb) else 0) + f.emax * 2 ^ f.sb
      + Nat.lor payload (2 ^ (f.sb - 1)))
  else if x.isinf then inf x.signbit
  else
    let r := x.toRat
    roundRat r.1 r.2 x.signbit

/-- IEEE ordered equality; `base/float.jl:615`. -/
def eq (x y : Fl f) : Bool :=
  !x.isnan && !y.isnan && (x.toBits == y.toBits || (x.iszero && y.iszero))

/-- IEEE ordered less-than; `base/float.jl:616`. -/
def lt (x y : Fl f) : Bool :=
  if x.isnan || y.isnan || (x.iszero && y.iszero) then false
  else if x.signbit != y.signbit then x.signbit
  else if x.signbit then x.toBits > y.toBits else x.toBits < y.toBits

/-- IEEE ordered less-or-equal; `base/float.jl:617`. -/
def le (x y : Fl f) : Bool := lt x y || eq x y

/-- `fpiseq`; `base/float.jl:619`. -/
def isequal (x y : Fl f) : Bool := (x.isnan && y.isnan) || x.toBits == y.toBits

/-- Sign-magnitude total order with NaNs last; `base/float.jl:622-634`. -/
def isless (x y : Fl f) : Bool :=
  if x.isnan || y.isnan then !x.isnan
  else if x.signbit != y.signbit then x.signbit
  else if x.signbit then x.toBits > y.toBits else x.toBits < y.toBits

/-- Addition with one rounding of the exact sum; `base/float.jl:487`. `Float16` addition
computes in `Float32` and rounds again; for two `Float16` operands that double rounding
equals single rounding, since 24 ≥ 2*11+2. -/
def add (x y : Fl f) : Fl f :=
  if x.isnan then x else if y.isnan then y
  else if x.isinf then (if y.isinf && x.signbit != y.signbit then nan else x)
  else if y.isinf then y
  else
    let a := x.toRat
    let b := y.toRat
    roundRat (a.1 * (b.2 : Int) + b.1 * (a.2 : Int)) (a.2 * b.2) (x.signbit && y.signbit)

/-- `isinteger(x) = iszero(x - trunc(x))`; `base/floatfuncs.jl:51`. -/
def isinteger (x : Fl f) : Bool := x.isfinite && (x.toRat.1 % (x.toRat.2 : Int) == 0)

/-- Exact truncation toward zero of a finite value (`fptosi`/`fptoui` on in-range inputs,
`base/float.jl:408-450`); nonfinite inputs give 0. -/
def truncVal (x : Fl f) : Int := x.toRat.1.tdiv (x.toRat.2 : Int)

/-- `unsafe_trunc(Ti, x)`; the result wraps (callers use it only in range). -/
def unsafeTrunc (t : IntTy) (x : Fl f) : JInt t := JInt.wrap t x.truncVal

/-- Bridge to the shared binary64 model. -/
def toF64 (x : Fl double) : F64 := F64.ofBits x.toBits
def ofF64 (x : F64) : Fl double := ofBits (F64.toBits x)

end Fl

end JuliaLean.Promotion

namespace JuliaLean.Float

/-- `base/rounding.jl:48-102`: the five rounding modes modelled here. -/
inductive Rounding where
  | RoundNearest | RoundNearestTiesAway | RoundUp | RoundDown | RoundToZero
  deriving Repr, DecidableEq, Inhabited

end JuliaLean.Float

namespace JuliaLean.MathFuncs

open JuliaLean.Float

deriving instance DecidableEq for Except

/-- `reinterpret(UInt64, x)`. -/
def bitsOf (x : F64) : Nat := F64.toBits x

/-- `reinterpret(Float64, u)` for a UInt64 value, reducing modulo 2^64. -/
def ofBitsU (u : Nat) : F64 := F64.ofBits (u % 2^64)

/-- `reinterpret(Int64, x)`. -/
def toInt64 (x : F64) : Int :=
  let b := F64.toBits x
  if b ≥ 2^63 then (b : Int) - 2^64 else (b : Int)

/-- `reinterpret(Float64, i)` for an Int64 value, reducing modulo 2^64. -/
def ofInt64 (i : Int) : F64 := F64.ofBits (i % 2^64).toNat

/-- A Float64 literal given by its bit pattern. -/
def lit (u : Nat) : F64 := F64.ofBits u

end JuliaLean.MathFuncs
namespace JuliaLean.Float


namespace F64

private def extraSign : Nat := 0x8000000000000000
private def extraFrac : Nat := 0x000fffffffffffff
private def extraExp : Nat := 0x7ff0000000000000
private def extraU (n : Nat) : JInt .u64 := JInt.wrap .u64 (Int.ofNat n)
private def extraN (x : JInt .u64) : Nat := x.val.toNat
private def extraShl (x : JInt .u64) (n : Nat) : JInt .u64 :=
  if n ≥ 64 then extraU 0 else extraU (extraN x <<< n)
private def extraShr (x : JInt .u64) (n : Nat) : JInt .u64 := extraU (extraN x >>> n)
private def extraShift (x : JInt .u64) (n : Int) : JInt .u64 :=
  if n < 0 then extraShr x n.natAbs else extraShl x n.toNat
private def extraLz (x : JInt .u64) : Nat :=
  if extraN x == 0 then 64 else 63 - (extraN x).log2
private def extraCountTz : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, u => if u % 2 == 1 then 0 else 1 + extraCountTz n (u >>> 1)
private def extraTz (x : JInt .u64) : Nat := extraCountTz 64 (extraN x)

/-- `base/floatfuncs.jl:5`: sign-copy intrinsic. -/
private def extraCopySign (x y : F64) : F64 :=
  ofBits (Nat.lor (toBits (abs x)) (Nat.land (toBits y) extraSign))

/-- `base/floatfuncs.jl:10`: sign-flip intrinsic. -/
private def extraFlipSign (x y : F64) : F64 := if signbit y then neg x else x

/-- `base/float.jl:810-845`: stepping through sign-magnitude encodings. -/
protected def extraNext (x : F64) (dneg : Bool) (da : Nat) : F64 := Id.run do
  if isnan x then return x
  let mut fneg := signbit x
  let mut fu := extraU (toBits (abs x))
  let fumax := extraU extraExp
  if da > 2^64 - 1 then
    fneg := dneg
    fu := fumax
  else
    let du := extraU da
    if fneg != dneg then
      if du.val > fu.val then
        fu := if (du - fu).val < fumax.val then du - fu else fumax
        fneg := !fneg
      else
        fu := fu - du
    else
      if (fumax - fu).val < du.val then fu := fumax else fu := fu + du
  return ofBits (extraN fu + if fneg then extraSign else 0)


/-- `base/float.jl:974`: smallest positive normal Float64. -/
def floatmin : F64 := ofBits 0x0010000000000000
/-- `base/float.jl:977`: largest finite Float64. -/
def floatmax : F64 := ofBits 0x7fefffffffffffff


/-- `base/math.jl:854-897`: exponent manipulation, including wrapped Int64 exponent addition. -/
def ldexp (x : F64) (e : Int) : F64 := Id.run do
  let mut xu := toBits x
  let xs := toBits (abs x)
  if xs ≥ extraExp then return x
  let mut k := JInt.wrap .i64 (Int.ofNat (xs >>> 52))
  if k.val == 0 then
    if xs == 0 then return x
    let m := extraLz (extraU xs) - 11
    let ys := extraN (extraShl (extraU xs) m)
    xu := Nat.lor ys (Nat.land xu extraSign)
    k := JInt.wrap .i64 (1 - Int.ofNat m)
    if e < -50000 then return zero (signbit x)
  if e > IntTy.max .i64 then return inf (signbit x)
  if e < IntTy.min .i64 then return zero (signbit x)
  k := k + JInt.wrap .i64 e
  if k.val ≥ 2047 then return inf (signbit x)
  if k.val > 0 then
    return ofBits (Nat.lor (Nat.land xu (extraSign + extraFrac)) (k.val.toNat <<< 52))
  else
    if k.val ≤ -53 then
      if e > 50000 then return inf (signbit x)
      return zero (signbit x)
    k := k + JInt.wrap .i64 53
    let z := ofBits (970 <<< 52)
    let y := ofBits (Nat.lor (Nat.land xu (extraSign + extraFrac)) (k.val.toNat <<< 52))
    return mul z y

/-- `base/math.jl:936-950`: exponent errors precede subnormal normalization. -/
def exponent (x : F64) : Jl Int :=
  let xs := toBits (abs x)
  if xs ≥ extraExp then .error (.domainError "Cannot be NaN or Inf.")
  else
    let k := Int.ofNat (xs >>> 52)
    if k == 0 then
      if xs == 0 then .error (.domainError "Cannot be ±0.0.")
      else .ok (1 - Int.ofNat (extraLz (extraU xs) - 11) - 1023)
    else .ok (k - 1023)

/-- `base/math.jl:1026-1038`: normalize subnormals before replacing exponent bits. -/
def significand (x : F64) : F64 := Id.run do
  let mut xu := toBits x
  let xs := toBits (abs x)
  if xs ≥ extraExp then return x
  if xs ≤ extraFrac then
    if xs == 0 then return x
    let m := extraLz (extraU xs) - 11
    xu := Nat.lor (extraN (extraShl (extraU xs) m)) (Nat.land xu extraSign)
  return ofBits (Nat.lor (Nat.land xu (extraSign + extraFrac)) 0x3ff0000000000000)

/-- `base/math.jl:1060-1077`: preserve nonfinite values and signed zeros with exponent zero. -/
def frexp (x : F64) : F64 × Int := Id.run do
  let mut xu := toBits x
  let xs := toBits (abs x)
  if xs ≥ extraExp then return (x, 0)
  let mut k := Int.ofNat (xs >>> 52)
  if k == 0 then
    if xs == 0 then return (x, 0)
    let m := extraLz (extraU xs) - 11
    xu := Nat.lor (extraN (extraShl (extraU xs) m)) (Nat.land xu extraSign)
    k := 1 - Int.ofNat m
  return (ofBits (Nat.lor (Nat.land xu (extraSign + extraFrac)) 0x3fe0000000000000), k - 1022)

/-- `base/float.jl:502-506`: explicit mantissa of a finite nonzero value. -/
private def extraMantissa (x : F64) : JInt .u64 :=
  let u := toBits x
  extraU (Nat.land u extraFrac + if u >>> 52 == 0 then 0 else 2^52)

/-- `base/float.jl:508-522`: UInt64 mantissa/exponent reconstruction. -/
private def extraToFloat (number ep : JInt .u64) : F64 :=
  let epint := JInt.wrap .i64 ep.val
  let lz := JInt.wrap .i64 (Int.ofNat (extraLz number) - 11)
  let number := extraShift number lz.val
  let epint := epint - lz
  if epint.val ≥ 0 then
    ofBits (Nat.lor (Nat.land (extraN number) extraFrac)
      (Nat.land (extraN (extraShl (JInt.wrap .u64 (epint + JInt.wrap .i64 1).val) 52)) extraExp))
  else ofBits (Nat.land (extraN (extraShift number epint.val)) extraFrac)

/-- `base/float.jl:580-586`: the exact shift/remainder loop; the shift size is positive. -/
private def extraRemLoop (n sideMinusOne : Nat) (mx my : JInt .u64) : JInt .u64 :=
  let side := sideMinusOne + 1
  if _h : side < n then
    let mx := extraU (extraN (extraShl mx side) % extraN my)
    extraRemLoop (n - side) sideMinusOne mx my
  else extraU (extraN (extraShl mx n) % extraN my)
termination_by n
decreasing_by omega

/-- `base/float.jl:524-588`: all three mantissa-reduction branches of rem_internal. -/
private def extraRemInternal (x y : F64) : F64 := Id.run do
  let xuint := extraU (toBits x)
  let yuint := extraU (toBits y)
  if xuint.val ≤ yuint.val then
    if xuint.val < yuint.val then return x
    return zero
  let ex := extraU (toBits x >>> 52)
  let ey := extraU (toBits y >>> 52)
  if ey.val > 52 && (ex - ey).val ≤ 11 then
    let mx := extraMantissa x
    let my := extraMantissa y
    let d := extraU (extraN (extraShl mx (extraN (ex - ey))) % extraN my)
    if d.val == 0 then return zero
    return extraToFloat d (ey - extraU 1)
  if ex.val == 0 && ey.val == 0 then
    return ofBits (Nat.land (extraN xuint % extraN yuint) extraFrac)
  let mut mx := extraMantissa x
  let ex := ex - extraU 1
  let mut my := extraMantissa y
  let mut ey := ey
  let mut lzmy := 11
  if ey.val > 0 then ey := ey - extraU 1
  else
    my := extraU (Nat.land (toBits y) extraFrac)
    lzmy := extraLz my
  let tzmy := extraTz my
  let side := lzmy + tzmy
  let mut diff := ex - ey
  let right := min (extraN diff) tzmy
  my := extraShr my right
  diff := diff - extraU right
  ey := ey + extraU right
  let left := min (extraN diff) 11
  mx := extraShl mx left
  diff := diff - extraU left
  mx := extraU (extraN mx % extraN my)
  if mx.val == 0 then return zero
  if diff.val == 0 then return extraToFloat mx ey
  return extraToFloat (extraRemLoop (extraN diff) (side - 1) mx my) ey

/-- `base/float.jl:590-598`: exceptional cases and dividend-signed exact remainder. -/
def rem (x y : F64) : F64 :=
  if isfinite x && !iszero x && isfinite y && !iszero y then
    extraCopySign (extraRemInternal (abs x) (abs y)) x
  else if isinf x || isnan y || iszero y then nan
  else x

/-- `base/float.jl:600-612`: retain the rounded addition when remainder and divisor differ in sign. -/
def mod (x y : F64) : F64 :=
  if isinf y && isfinite x then x
  else
    let r := rem x y
    if eq r zero then extraCopySign r y
    else if lt zero r != lt zero y then add r y
    else r

/-
This remainder method follows Julia's adaptation of the msun remainder functions.
Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
Developed at SunSoft, a Sun Microsystems, Inc. business.
Permission to use, copy, modify, and distribute this software is freely granted,
provided that this notice is preserved.
-/
/-- `base/math.jl:1122-1145`: IEEE nearest-even remainder, including tiny-divisor branches. -/
protected def extraRemNearest (x p : F64) : F64 := Id.run do
  if iszero p || !isfinite x || isnan p then return nan
  if eq x p then return zero (signbit x)
  let oldx := x
  let two := ofInt 2
  let mut x := abs (rem x (mul two p))
  let p := abs p
  if lt p (mul two floatmin) then
    if lt p (mul two x) then
      x := sub x p
      if le p (mul two x) then x := sub x p
  else
    let phalf := div p two
    if lt phalf x then
      x := sub x p
      if le phalf x then x := sub x p
  return extraFlipSign x oldx


/-- LLVM integral rounding behind `base/float.jl:458-461`, with exact rational arithmetic. -/
private def extraRoundIntrinsic (x : F64) (mode : Rounding) : F64 :=
  if isnan x then ofBits (Nat.lor (toBits x) 0x0008000000000000)
  else if isinf x then x
  else
    let (num, den) := toRat x
    let q := num.natAbs / den
    let r := num.natAbs % den
    let increment := match mode with
      | .RoundToZero => false
      | .RoundDown => signbit x && r != 0
      | .RoundUp => !signbit x && r != 0
      | .RoundNearest => 2*r > den || (2*r == den && q % 2 == 1)
      | .RoundNearestTiesAway => decide (2*r ≥ den)
    let magnitude := q + if increment then 1 else 0
    if magnitude == 0 then zero (signbit x)
    else ofInt (if signbit x then -Int.ofNat magnitude else Int.ofNat magnitude)

/-- `base/float.jl:458-461`, `base/floatfuncs.jl:151-154`: ties-away retains rounded intermediates. -/
def round (x : F64) (mode : Rounding := .RoundNearest) : F64 :=
  match mode with
  | .RoundNearestTiesAway =>
    let y := extraRoundIntrinsic x .RoundToZero
    if eq x y then y else extraRoundIntrinsic (sub (mul (ofInt 2) x) y) .RoundToZero
  | _ => extraRoundIntrinsic x mode

/-- `base/rounding.jl:480`: truncation wrapper. -/
def trunc (x : F64) : F64 := round x .RoundToZero
/-- `base/rounding.jl:481`: floor wrapper. -/
def floor (x : F64) : F64 := round x .RoundDown
/-- `base/rounding.jl:482`: ceiling wrapper. -/
def ceil (x : F64) : F64 := round x .RoundUp


/-- `base/float.jl:265-305`: two Float64 mantissas and the large UInt128 sticky-bit packing. -/
private def extraOfUInt128 (x : JInt .u128) : F64 :=
  let n := x.val.toNat
  if n < 2^104 then
    let lowExp := ofBits (1075 <<< 52)
    let highExp := ofBits (1127 <<< 52)
    let lowBits := Nat.land (n % 2^64) extraFrac
    let lowValue := sub (ofBits (Nat.lor (toBits lowExp) lowBits)) lowExp
    let highBits := (n >>> 52) % 2^64
    let highValue := sub (ofBits (Nat.lor (toBits highExp) highBits)) highExp
    add lowValue highValue
  else
    let lowExp := ofBits (1099 <<< 52)
    let highExp := ofBits (1151 <<< 52)
    let lowBits := Nat.lor (((n >>> 12) % 2^64) >>> 12) (Nat.land (n % 2^64) 0xffffff)
    let lowValue := sub (ofBits (Nat.lor (toBits lowExp) lowBits)) lowExp
    let highBits := (n >>> 76) % 2^64
    let highValue := sub (ofBits (Nat.lor (toBits highExp) highBits)) highExp
    add lowValue highValue

/-- `base/float.jl:243-305`: fixed-width integer conversion, preserving the Int128 source branches. -/
def ofJInt {t : IntTy} (x : JInt t) : F64 :=
  match t with
  | .u128 => extraOfUInt128 (JInt.wrap .u128 x.val)
  | .i128 =>
    let magnitude := extraOfUInt128 (JInt.wrap .u128 (Int.ofNat x.val.natAbs))
    ofBits (Nat.lor (toBits magnitude) (if x.val < 0 then extraSign else 0))
  | _ => ofInt x.val

/-- `base/floatfuncs.jl:51`: infinity is excluded by the rounded subtraction. -/
def isinteger (x : F64) : Bool := iszero (sub x (trunc x))



end F64
end JuliaLean.Float

namespace JuliaLean.Promotion

open JuliaLean.Float

/-- Julia's three `IEEEFloat` types. -/
inductive FTy where
  | f16 | f32 | f64
  deriving DecidableEq, Repr

def FTy.fmt : FTy → Fmt
  | .f16 => half | .f32 => single | .f64 => double

/-- `sizeof(T)`. -/
def FTy.bytes : FTy → Nat
  | .f16 => 2 | .f32 => 4 | .f64 => 8

abbrev FV (T : FTy) := Fl T.fmt
def one (T : FTy) : FV T := Fl.ofInt 1

end JuliaLean.Promotion

/-!
Arithmetic on the three IEEE formats for the `base/math.jl`, `base/special/*.jl`,
`base/floatfuncs.jl` and `base/rounding.jl` coverage models (Julia master `bbfa0ce4150`).

Values are `Promotion.FV T` bit patterns. Every operation on a `Float32` or `Float16`
operand widens exactly to binary64, applies the shared `JuliaLean.Float.F64` intrinsic,
and rounds back once (`Fl.convert`). For `+`, `-`, `*`, `/` and `sqrt` this equals the
correctly rounded operation of the narrow format, because binary64 has more than
`2p+2` significand bits for `p = 24` and `p = 11` (Julia evaluates `Float16` arithmetic in
`Float32` and rounds again, which is equally exact since `24 ≥ 2*11+2`). `fma` of narrow
operands rounds the exact rational once. `muladd` is fused in the MathCov call sites except
for the compensated `cospi` product, where Julia's optimized code keeps separate operations.
-/

namespace JuliaLean.MathCov

open JuliaLean JuliaLean.Float JuliaLean.Promotion

namespace FP

variable {T : FTy}

/-- `Float64(x)`, the exact `fpext`; `base/float.jl:346`. -/
def toD (x : FV T) : F64 := Fl.toF64 (Fl.convert x : Fl double)

/-- `T(y::Float64)`, the `fptrunc` rounding; `base/float.jl:343`. -/
def ofD (y : F64) : FV T := Fl.convert (Fl.ofF64 y)

/-- The shared binary64 model's view of a `Float64` value, and back. -/
def of64 (y : F64) : FV .f64 := Fl.ofF64 y
def to64 (x : FV .f64) : F64 := Fl.toF64 x

/-- Conversion between formats, `S(x::T)`; `base/float.jl:342-349`. -/
def conv {S : FTy} (x : FV T) : FV S := Fl.convert x

/-- A literal of the format given by its bit pattern. -/
def lit (T : FTy) (u : Nat) : FV T := Fl.ofBits u

def add (x y : FV T) : FV T := ofD (F64.add (toD x) (toD y))
def sub (x y : FV T) : FV T := ofD (F64.sub (toD x) (toD y))
def mul (x y : FV T) : FV T := ofD (F64.mul (toD x) (toD y))
def div (x y : FV T) : FV T := ofD (F64.div (toD x) (toD y))

/-- `sqrt_llvm`: correctly rounded square root, NaN for negative arguments;
`base/math.jl:631`. -/
def sqrt64 (y : F64) : F64 := match F64.sqrt y with
  | .ok r => r
  | .error _ => F64.nan

def sqrtLlvm (x : FV T) : FV T := ofD (sqrt64 (toD x))

/-- `fma_float` (hardware fused multiply-add) with one rounding of the exact
`x*y+z`; `base/floatfuncs.jl:464-466`. Exact zeros and nonfinite operands follow the
binary64 rules, which are the IEEE rules of every format. -/
def fma (x y z : FV T) : FV T :=
  let wide : FV T := ofD (F64.fma (toD x) (toD y) (toD z))
  if T = .f64 then wide
  else if x.isfinite && y.isfinite && z.isfinite then
    let a := x.toRat
    let b := y.toRat
    let c := z.toRat
    let n := a.1 * b.1 * (c.2 : Int) + c.1 * ((a.2 * b.2 : Nat) : Int)
    if n == 0 then wide else Fl.roundRat n (a.2 * b.2 * c.2) false
  else wide

/-- `muladd_float`, fused at the ordinary MathCov call sites; `base/float.jl:492`. -/
def muladd (x y z : FV T) : FV T := fma x y z

def neg (x : FV T) : FV T := Fl.neg x
def abs (x : FV T) : FV T := Fl.ofBits x.magnitude
def signbit (x : FV T) : Bool := x.signbit
def isnan (x : FV T) : Bool := x.isnan
def isinf (x : FV T) : Bool := x.isinf
def isfinite (x : FV T) : Bool := x.isfinite
def iszero (x : FV T) : Bool := x.iszero
def lt (x y : FV T) : Bool := Fl.lt x y
def le (x y : FV T) : Bool := Fl.le x y
def eq (x y : FV T) : Bool := Fl.eq x y
def isequal (x y : FV T) : Bool := Fl.isequal x y

/-- `copysign_float`: magnitude of `x`, sign bit of `y`; `base/floatfuncs.jl:5-6`. -/
def copysign (x y : FV T) : FV T :=
  Fl.ofBits (x.magnitude + if y.signbit then 2 ^ (T.fmt.eb + T.fmt.sb) else 0)

/-- `flipsign`: xor with the sign bit of `y`; `base/floatfuncs.jl:10-11`. -/
def flipsign (x y : FV T) : FV T := if y.signbit then Fl.neg x else x

def zero (T : FTy) (neg : Bool := false) : FV T := Fl.zero neg
def inf (T : FTy) (neg : Bool := false) : FV T := Fl.inf neg
def nan (T : FTy) : FV T := Fl.nan
/-- `T(n)` for a small integer literal `n`. -/
def ofInt (T : FTy) (n : Int) : FV T := Fl.ofInt n

/-- Integer rounding of a float in its own type (`trunc_llvm`, `floor_llvm`, `ceil_llvm`,
`rint_llvm`); the binary64 rounding of the exact widening is exact. `base/float.jl:458-461`. -/
def roundI (x : FV T) (mode : Rounding := .RoundNearest) : FV T := ofD (F64.round (toD x) mode)
def trunc (x : FV T) : FV T := roundI x .RoundToZero
def floor (x : FV T) : FV T := roundI x .RoundDown
def ceil (x : FV T) : FV T := roundI x .RoundUp

/-- Exact value of a finite float as a rational `(num, den)`. -/
def val (x : FV T) : Int × Nat := x.toRat

/-- `unsafe_trunc(t, x)`. -/
def unsafeTrunc (t : IntTy) (x : FV T) : JInt t := x.unsafeTrunc t

/-- `reinterpret(Unsigned, x)` as a natural number. -/
def bits (x : FV T) : Nat := x.toBits

end FP

end JuliaLean.MathCov

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

/-!
Floating-point constants of the `base/special/*.jl` and `base/math.jl` models at Julia master
`bbfa0ce4150`, as exact bit patterns, obtained from the literals of the Julia source
(evaluated by Julia nightly), so each value is the one Base uses.
-/

namespace JuliaLean.MathCov.C

open JuliaLean.Promotion JuliaLean.MathCov.FP

def maxExp32Two : FV .f32 := lit .f32 0x43000000  -- 128.0f0
def minExp32Two : FV .f32 := lit .f32 0xc3160000  -- -150.0f0
def subnormExp32Two : FV .f32 := lit .f32 0x42fc0001  -- 126.00001f0
def logBInv32Two : FV .f32 := lit .f32 0x3f800000  -- 1.0f0
def logBU32Two : FV .f32 := lit .f32 0xbf800000  -- -1.0f0
def logBL32Two : FV .f32 := lit .f32 0x0  -- 0.0f0
def logB16Two : FV .f32 := lit .f32 0xbf800000  -- -1.0f0
def maxExp32E : FV .f32 := lit .f32 0x42b17218  -- 88.72284f0
def minExp32E : FV .f32 := lit .f32 0xc2cff1b4  -- -103.97208f0
def subnormExp32E : FV .f32 := lit .f32 0x42aeac50  -- 87.33655f0
def logBInv32E : FV .f32 := lit .f32 0x3fb8aa3b  -- 1.442695f0
def logBU32E : FV .f32 := lit .f32 0xbf317200  -- -0.69314575f0
def logBL32E : FV .f32 := lit .f32 0xb5bfbe8e  -- -1.4286068f-6
def logB16E : FV .f32 := lit .f32 0xbf317218  -- -0.6931472f0
def maxExp32Ten : FV .f32 := lit .f32 0x421a209b  -- 38.53184f0
def minExp32Ten : FV .f32 := lit .f32 0xc2349e35  -- -45.1545f0
def subnormExp32Ten : FV .f32 := lit .f32 0x4217b818  -- 37.92978f0
def logBInv32Ten : FV .f32 := lit .f32 0x40549a78  -- 3.321928f0
def logBU32Ten : FV .f32 := lit .f32 0xbe9a2000  -- -0.3010254f0
def logBL32Ten : FV .f32 := lit .f32 0xb69a84fc  -- -4.605039f-6
def logB16Ten : FV .f32 := lit .f32 0xbe9a209b  -- -0.30103f0
def magic32 : FV .f32 := lit .f32 0x4b200000  -- 1.048576f7
def expbKernel32Two : List (FV .f32) := [lit .f32 0x3f800000, lit .f32 0x3f317218, lit .f32 0x3e75fdf0, lit .f32 0x3d635847, lit .f32 0x3c1d94ec, lit .f32 0x3aaec38b, lit .f32 0x3922363f, lit .f32 0x37807bdb]
def expbKernel32E : List (FV .f32) := [lit .f32 0x3f800000, lit .f32 0x3f800000, lit .f32 0x3f000000, lit .f32 0x3e2aaaab, lit .f32 0x3d2aaa32, lit .f32 0x3c08882e, lit .f32 0x3ab6d3ab, lit .f32 0x3950eb8a]
def expbKernel32Ten : List (FV .f32) := [lit .f32 0x3f800000, lit .f32 0x40135d8e, lit .f32 0x4029a926, lit .f32 0x4002382d, lit .f32 0x3f95eb47, lit .f32 0x3f0a14a4, lit .f32 0x3e54dfee, lit .f32 0x3d8c0798]
def expm1Max32 : FV .f32 := lit .f32 0x42b17218  -- 88.72284f0
def expm1Min32 : FV .f32 := lit .f32 0xc18aa123  -- -17.32868f0
def expm1Max16 : FV .f16 := lit .f16 0x498c  -- Float16(11.09)
def expm1Min16 : FV .f16 := lit .f16 0xc829  -- Float16(-8.32)
def ln2Inv64 : FV .f64 := lit .f64 0x3ff71547652b82fe  -- 1.4426950408889634
def ln2Neg64 : FV .f64 := lit .f64 0xbfe62e42fefa39ef  -- -0.6931471805599453
def ln2Inv32 : FV .f32 := lit .f32 0x3fb8aa3b  -- 1.442695f0
def ln2Neg32 : FV .f32 := lit .f32 0xbf317218  -- -0.6931472f0
def expm1SmallP32 : List (FV .f32) := [lit .f32 0x3e2aaaaa, lit .f32 0x3d2aaaa0, lit .f32 0x3c0889ff, lit .f32 0x3ab64de5, lit .f32 0x394ab327]
def expm1Lo32 : FV .f32 := lit .f32 0xbe934b11  -- -0.2876821f0
def expm1Hi32 : FV .f32 := lit .f32 0x3e647fbe  -- 0.22314355f0
def expm1Poly64For32 : List (FV .f64) := [lit .f64 0x3ff0000000000000, lit .f64 0x3fe0000000000000, lit .f64 0x3fc55555683b0d0f, lit .f64 0x3fa555451ad5f015, lit .f64 0x3f8110e3fd4928ed, lit .f64 0x3f56e1f74853b4b7, lit .f64 0x3f2a446eb9d24154]
def expm1SmallPoly16 : List (FV .f32) := [lit .f32 0x3f800000, lit .f32 0x3f000000, lit .f32 0x3e2aaa91, lit .f32 0x3d2aabe8, lit .f32 0x3c08d631, lit .f32 0x3ab3400f]
def expm1Poly16 : List (FV .f32) := [lit .f32 0x3f800000, lit .f32 0x3f000000, lit .f32 0x3e2aaaab, lit .f32 0x3d2aa9d3, lit .f32 0x3c08879a, lit .f32 0x3ab74220, lit .f32 0x39518be2]
def tLogFloat32 : List (FV .f64) := [lit .f64 0x0, lit .f64 0x3f7fe02a6b106789, lit .f64 0x3f8fc0a8b0fc03e4, lit .f64 0x3f97b91b07d5b11b, lit .f64 0x3f9f829b0e783300, lit .f64 0x3fa39e87b9febd60, lit .f64 0x3fa77458f632dcfc, lit .f64 0x3fab42dd711971bf, lit .f64 0x3faf0a30c01162a6, lit .f64 0x3fb16536eea37ae1, lit .f64 0x3fb341d7961bd1d1, lit .f64 0x3fb51b073f06183f, lit .f64 0x3fb6f0d28ae56b4c, lit .f64 0x3fb8c345d6319b21, lit .f64 0x3fba926d3a4ad563, lit .f64 0x3fbc5e548f5bc743, lit .f64 0x3fbe27076e2af2e6, lit .f64 0x3fbfec9131dbeabb, lit .f64 0x3fc0d77e7cd08e59, lit .f64 0x3fc1b72ad52f67a0, lit .f64 0x3fc29552f81ff523, lit .f64 0x3fc371fc201e8f74, lit .f64 0x3fc44d2b6ccb7d1e, lit .f64 0x3fc526e5e3a1b438, lit .f64 0x3fc5ff3070a793d4, lit .f64 0x3fc6d60fe719d21d, lit .f64 0x3fc7ab890210d909, lit .f64 0x3fc87fa06520c911, lit .f64 0x3fc9525a9cf456b4, lit .f64 0x3fca23bc1fe2b563, lit .f64 0x3fcaf3c94e80bff3, lit .f64 0x3fcbc286742d8cd6, lit .f64 0x3fcc8ff7c79a9a22, lit .f64 0x3fcd5c216b4fbb91, lit .f64 0x3fce27076e2af2e6, lit .f64 0x3fcef0adcbdc5936, lit .f64 0x3fcfb9186d5e3e2b, lit .f64 0x3fd0402594b4d041, lit .f64 0x3fd0a324e27390e3, lit .f64 0x3fd1058bf9ae4ad5, lit .f64 0x3fd1675cababa60e, lit .f64 0x3fd1c898c16999fb, lit .f64 0x3fd22941fbcf7966, lit .f64 0x3fd2895a13de86a3, lit .f64 0x3fd2e8e2bae11d31, lit .f64 0x3fd347dd9a987d55, lit .f64 0x3fd3a64c556945ea, lit .f64 0x3fd404308686a7e4, lit .f64 0x3fd4618bc21c5ec2, lit .f64 0x3fd4be5f957778a1, lit .f64 0x3fd51aad872df82d, lit .f64 0x3fd5767717455a6c, lit .f64 0x3fd5d1bdbf5809ca, lit .f64 0x3fd62c82f2b9c795, lit .f64 0x3fd686c81e9b14af, lit .f64 0x3fd6e08eaa2ba1e4, lit .f64 0x3fd739d7f6bbd007, lit .f64 0x3fd792a55fdd47a2, lit .f64 0x3fd7eaf83b82afc3, lit .f64 0x3fd842d1da1e8b17, lit .f64 0x3fd89a3386c1425b, lit .f64 0x3fd8f11e873662c7, lit .f64 0x3fd947941c2116fb, lit .f64 0x3fd99d958117e08b, lit .f64 0x3fd9f323ecbf984c, lit .f64 0x3fda484090e5bb0a, lit .f64 0x3fda9cec9a9a084a, lit .f64 0x3fdaf1293247786b, lit .f64 0x3fdb44f77bcc8f63, lit .f64 0x3fdb9858969310fb, lit .f64 0x3fdbeb4d9da71b7c, lit .f64 0x3fdc3dd7a7cdad4d, lit .f64 0x3fdc8ff7c79a9a22, lit .f64 0x3fdce1af0b85f3eb, lit .f64 0x3fdd32fe7e00ebd5, lit .f64 0x3fdd83e7258a2f3e, lit .f64 0x3fddd46a04c1c4a1, lit .f64 0x3fde24881a7c6c26, lit .f64 0x3fde744261d68788, lit .f64 0x3fdec399d2468cc0, lit .f64 0x3fdf128f5faf06ed, lit .f64 0x3fdf6123fa7028ac, lit .f64 0x3fdfaf588f78f31f, lit .f64 0x3fdffd2e0857f498, lit .f64 0x3fe02552a5a5d0ff, lit .f64 0x3fe04bdf9da926d2, lit .f64 0x3fe0723e5c1cdf40, lit .f64 0x3fe0986f4f573521, lit .f64 0x3fe0be72e4252a83, lit .f64 0x3fe0e44985d1cc8c, lit .f64 0x3fe109f39e2d4c97, lit .f64 0x3fe12f719593efbc, lit .f64 0x3fe154c3d2f4d5ea, lit .f64 0x3fe179eabbd899a1, lit .f64 0x3fe19ee6b467c96f, lit .f64 0x3fe1c3b81f713c25, lit .f64 0x3fe1e85f5e7040d0, lit .f64 0x3fe20cdcd192ab6e, lit .f64 0x3fe23130d7bebf43, lit .f64 0x3fe2555bce98f7cb, lit .f64 0x3fe2795e1289b11b, lit .f64 0x3fe29d37fec2b08b, lit .f64 0x3fe2c0e9ed448e8c, lit .f64 0x3fe2e47436e40268, lit .f64 0x3fe307d7334f10be, lit .f64 0x3fe32b1339121d71, lit .f64 0x3fe34e289d9ce1d3, lit .f64 0x3fe37117b54747b6, lit .f64 0x3fe393e0d3562a1a, lit .f64 0x3fe3b68449fffc23, lit .f64 0x3fe3d9026a7156fb, lit .f64 0x3fe3fb5b84d16f42, lit .f64 0x3fe41d8fe84672ae, lit .f64 0x3fe43f9fe2f9ce67, lit .f64 0x3fe4618bc21c5ec2, lit .f64 0x3fe48353d1ea88df, lit .f64 0x3fe4a4f85db03ebb, lit .f64 0x3fe4c679afccee3a, lit .f64 0x3fe4e7d811b75bb1, lit .f64 0x3fe50913cc01686b, lit .f64 0x3fe52a2d265bc5ab, lit .f64 0x3fe54b2467999498, lit .f64 0x3fe56bf9d5b3f399, lit .f64 0x3fe58cadb5cd7989, lit .f64 0x3fe5ad404c359f2d, lit .f64 0x3fe5cdb1dc6c1765, lit .f64 0x3fe5ee02a9241675, lit .f64 0x3fe60e32f44788d9, lit .f64 0x3fe62e42fefa39ef]
def logb32Two : FV .f64 := lit .f64 0x3ff71547652b82fe  -- 1.4426950408889634
def logb32E : FV .f64 := lit .f64 0x3ff0000000000000  -- 1.0
def logb32Ten : FV .f64 := lit .f64 0x3fdbcb7b1526e50e  -- 0.4342944819032518
def ln2For32 : FV .f64 := lit .f64 0x3fe62e42fefa39ef  -- 0.6931471805599453
def logProc1Q32 : FV .f32 := lit .f32 0x3daaaac2  -- 0.08333351f0
def logProc2Q32 : List (FV .f32) := [lit .f32 0x3daaaaa9, lit .f32 0x3c4d0095]
def logLo32 : FV .f32 := lit .f32 0x3f707d5f  -- 0.939413f0
def logHi32 : FV .f32 := lit .f32 0x3f88415b  -- 1.0644945f0
def logShift32 : FV .f32 := lit .f32 0x47800000  -- 65536.0f0
def log2p25 : FV .f32 := lit .f32 0x4c000000  -- 3.3554432f7
def log1pTiny32 : FV .f32 := lit .f32 0x33800000  -- 5.9604645f-8
def log1pLo32 : FV .f32 := lit .f32 0xbd782a03  -- -0.06058694f0
def log1pHi32 : FV .f32 := lit .f32 0x3d8415ac  -- 0.06449446f0
def cbrtAdj64 : FV .f64 := lit .f64 0x40854fbc49cda07d  -- 681.96693764349
def cbrtAdj32 : FV .f64 := lit .f64 0x4055288cf917ae90  -- 84.63360431015667
def cbrtThird32 : FV .f32 := lit .f32 0x3eaaaaab  -- 0.33333334f0
def powMaxExp32 : FV .f32 := lit .f32 0x4ed00000  -- 1.7448305f9
def powMaxExp16 : FV .f16 := lit .f16 0x7a00  -- Float16(4.915e4)
def remPio2Bound32 : FV .f32 := lit .f32 0x4dc90fdb  -- 4.2165744f8
def twoOverPi64 : FV .f64 := lit .f64 0x3fe45f306dc9c883  -- 0.6366197723675814
def negPiOver2 : FV .f64 := lit .f64 0xbff921fb54442d18  -- -1.5707963267948966
def pio2Tail : FV .f64 := lit .f64 0xbc91a62633145c07  -- -6.123233995736766e-17
def piOver4_64 : FV .f64 := lit .f64 0x3fe921fb54442d18  -- 0.7853981633974483
def piOver4_32 : FV .f32 := lit .f32 0x3f490fdb  -- 0.7853982f0
def sqrtEps64 : FV .f64 := lit .f64 0x3e50000000000000  -- 1.4901161193847656e-8
def sqrtEps32 : FV .f32 := lit .f32 0x39b504f3  -- 0.00034526698f0
def sqrtHalfEps64 : FV .f64 := lit .f64 0x3e46a09e667f3bcd  -- 1.0536712127723509e-8
def sqrtHalfEps32 : FV .f32 := lit .f32 0x39800000  -- 0.00024414062f0
def halfSqrtEps64 : FV .f64 := lit .f64 0x3e40000000000000  -- 7.450580596923828e-9
def halfSqrtEps32 : FV .f32 := lit .f32 0x393504f3  -- 0.00017263349f0
def DS : List (FV .f64) := [lit .f64 0xbfc5555555555549, lit .f64 0x3f8111111110f8a6, lit .f64 0xbf2a01a019c161d5, lit .f64 0x3ec71de357b1fe7d, lit .f64 0xbe5ae5e68a2b9ceb, lit .f64 0x3de5d93a5acfd57c]
def DC : List (FV .f64) := [lit .f64 0x3fa555555555554c, lit .f64 0xbf56c16c16c15177, lit .f64 0x3efa01a019cb1590, lit .f64 0xbe927e4f809c52ad, lit .f64 0x3e21ee9ebdb4b1c4, lit .f64 0xbda8fae9be8838d4]
def sinK32 : List (FV .f64) := [lit .f64 0xbfc5555554cbac77, lit .f64 0x3f811110896efbb2, lit .f64 0xbf2a00f9e2cae774, lit .f64 0x3ec6cd878c3b46a7]
def cosK32 : List (FV .f64) := [lit .f64 0xbfdffffffd0c5e81, lit .f64 0x3fa55553e1053a42, lit .f64 0xbf56c087e80f1e27, lit .f64 0x3ef99342e0ee5069]
def tanT64 : List (FV .f64) := [lit .f64 0x3fc111111110fe7a, lit .f64 0x3f9664f48406d637, lit .f64 0x3f6d6d22c9560328, lit .f64 0x3f4344d8f2f26501, lit .f64 0x3f147e88a03792a6, lit .f64 0xbef375cbdb605373, lit .f64 0x3faba1ba1bb341fe, lit .f64 0x3f8226e3e96e8493, lit .f64 0x3f57dbc8fee08315, lit .f64 0x3f3026f71a8d1068, lit .f64 0x3f12b80f32f0a7e9, lit .f64 0x3efb2a7074bf7ad4]
def tanMisc64 : List (FV .f64) := [lit .f64 0x3fe594af4f0d844d, lit .f64 0x3fe921fb54442d18, lit .f64 0x3c81a62633145c07, lit .f64 0x3fd5555555555563]
def tanK32 : List (FV .f64) := [lit .f64 0x3f685dadfcecf44e, lit .f64 0x3f8362b9bf971bcd, lit .f64 0x3fab54c91d865afe, lit .f64 0x3f991df3908c33ce, lit .f64 0x3fd5554d3418c99f, lit .f64 0x3fc112fd38999f72]
def arcP64 : List (FV .f64) := [lit .f64 0x3fc5555555555555, lit .f64 0xbfd4d61203eb6f7d, lit .f64 0x3fc9c1550e884455, lit .f64 0xbfa48228b5688f3b, lit .f64 0x3f49efe07501b288, lit .f64 0x3f023de10dfdf709]
def arcQ64 : List (FV .f64) := [lit .f64 0x3ff0000000000000, lit .f64 0xc0033a271c8a2d4b, lit .f64 0x40002ae59c598ac8, lit .f64 0xbfe6066c1b8d0159, lit .f64 0x3fb3b8c5b12e9282]
def arcP32 : List (FV .f32) := [lit .f32 0x3e2aaa75, lit .f32 0xbd2f13ba, lit .f32 0xbc0dd36b]
def arcQ32 : List (FV .f32) := [lit .f32 0x3f800000, lit .f32 0xbf34e5ae]
def asinMisc64 : List (FV .f64) := [lit .f64 0x3c91a62633145c07, lit .f64 0x3fef333333333333, lit .f64 0x3ff921fb54442d18, lit .f64 0x3fe921fb54442d18]
def asinMin32 : FV .f32 := lit .f32 0x39800000  -- 0.00024414062f0
def asinMin64 : FV .f64 := lit .f64 0x3e50000000000000  -- 1.4901161193847656e-8
def atanHi32 : List (FV .f32) := [lit .f32 0x3eed6338, lit .f32 0x3f490fda, lit .f32 0x3f7b985e, lit .f32 0x3fc90fda]
def atanLo32 : List (FV .f32) := [lit .f32 0x31ac3769, lit .f32 0x33222168, lit .f32 0x33140fb4, lit .f32 0x33a22168]
def atanLarge32 : FV .f32 := lit .f32 0x4c800000  -- 6.7108864f7
def atanSmall32 : FV .f32 := lit .f32 0x39800000  -- 0.00024414062f0
def atanBreaks32 : List (FV .f32) := [lit .f32 0x3ee00000, lit .f32 0x3f300000, lit .f32 0x3f980000, lit .f32 0x401c0000, lit .f32 0x3fc00000, lit .f32 0x3fc90fdb]
def atan2PiLo32 : FV .f32 := lit .f32 0xb3bbbd2e  -- -8.742278f-8
def acosMin32 : FV .f32 := lit .f32 0x32800000  -- 1.4901161f-8
def pio2Hi32 : FV .f32 := lit .f32 0x3fc90fda  -- 1.5707963f0
def pio2Lo32 : FV .f32 := lit .f32 0x33a22168  -- 7.5497894f-8
def acosPi32 : FV .f32 := lit .f32 0x40490fda  -- 3.1415925f0
def piT32 : FV .f32 := lit .f32 0x40490fdb  -- 3.1415927f0
def piOver2T32 : FV .f32 := lit .f32 0x3fc90fdb  -- 1.5707964f0
def piOver4T32 : FV .f32 := lit .f32 0x3f490fdb  -- 0.7853982f0
def threePiOver4T32 : FV .f32 := lit .f32 0x4016cbe4  -- 2.3561945f0
def atanHi64 : List (FV .f64) := [lit .f64 0x3fddac670561bb4f, lit .f64 0x3fe921fb54442d18, lit .f64 0x3fef730bd281f69b, lit .f64 0x3ff921fb54442d18]
def atanLo64 : List (FV .f64) := [lit .f64 0x3c7a2b7f222f65e2, lit .f64 0x3c81a62633145c07, lit .f64 0x3c7007887af0cbbd, lit .f64 0x3c91a62633145c07]
def atanLarge64 : FV .f64 := lit .f64 0x4410000000000000  -- 7.378697629483821e19
def atanSmall64 : FV .f64 := lit .f64 0x3e40000000000000  -- 7.450580596923828e-9
def atanBreaks64 : List (FV .f64) := [lit .f64 0x3fdc000000000000, lit .f64 0x3fe6000000000000, lit .f64 0x3ff3000000000000, lit .f64 0x4003800000000000, lit .f64 0x3ff8000000000000, lit .f64 0x3ff921fb54442d18]
def atan2PiLo64 : FV .f64 := lit .f64 0x3ca1a62633145c07  -- 1.2246467991473532e-16
def acosMin64 : FV .f64 := lit .f64 0x3c60000000000000  -- 6.938893903907228e-18
def pio2Hi64 : FV .f64 := lit .f64 0x3ff921fb54442d18  -- 1.5707963267948966
def pio2Lo64 : FV .f64 := lit .f64 0x3c91a62633145c07  -- 6.123233995736766e-17
def acosPi64 : FV .f64 := lit .f64 0x400921fb54442d18  -- 3.141592653589793
def piT64 : FV .f64 := lit .f64 0x400921fb54442d18  -- 3.141592653589793
def piOver2T64 : FV .f64 := lit .f64 0x3ff921fb54442d18  -- 1.5707963267948966
def piOver4T64 : FV .f64 := lit .f64 0x3fe921fb54442d18  -- 0.7853981633974483
def threePiOver4T64 : FV .f64 := lit .f64 0x4002d97c7f3321d2  -- 2.356194490192345
def atanP64 : List (FV .f64) := [lit .f64 0x3fd555555555550d, lit .f64 0x3fc24924920083ff, lit .f64 0x3fb745cdc54c206e, lit .f64 0x3fb10d66a0d03d51, lit .f64 0x3fa97b4b24760deb, lit .f64 0x3f90ad3ae322da11]
def atanQ64 : List (FV .f64) := [lit .f64 0xbfc999999998ebc4, lit .f64 0xbfbc71c6fe231671, lit .f64 0xbfb3b0f2af749a6d, lit .f64 0xbfadde2d52defd9a, lit .f64 0xbfa2b4442c6a6c2f]
def atanP32 : List (FV .f32) := [lit .f32 0x3eaaaaa9, lit .f32 0x3e11f50d, lit .f32 0x3d7cac25]
def atanQ32 : List (FV .f32) := [lit .f32 0xbe4cca98, lit .f32 0xbdda1247]
def cospiPoly32 : List (FV .f32) := [lit .f32 0x3f800000, lit .f32 0xc09de9e6, lit .f32 0xb3f945b3, lit .f32 0x4081e0ef, lit .f32 0xbfaae306, lit .f32 0x3e6cf05a]
def sinpiPoly32 : List (FV .f32) := [lit .f32 0x40490fdb, lit .f32 0xb3bc367f, lit .f32 0xc0a55de7, lit .f32 0x402335c5, lit .f32 0xbf195c2c, lit .f32 0x3da3b622]
def cospiPoly64 : List (FV .f64) := [lit .f64 0x3ff0000000000000, lit .f64 0xc013bd3cc9be45de, lit .f64 0xbcb30f699892a25e, lit .f64 0x40103c1f081b5aae, lit .f64 0xbff55d3c7e3c9254, lit .f64 0x3fce1f5068363dd1, lit .f64 0xbf9a6d1ec7b4d288, lit .f64 0x3f5f9cc3eb9ab614, lit .f64 0xbf1b26337cdaa924]
def sinpiPoly64 : List (FV .f64) := [lit .f64 0x400921fb54442d18, lit .f64 0x3ca1adc7bbf1b141, lit .f64 0xc014abbce625be53, lit .f64 0x400466bc6775ab4d, lit .f64 0xbfe32d2cce634924, lit .f64 0x3fb50783492dcb22, lit .f64 0xbf7e3075d7cb71a7, lit .f64 0x3f3e8fb7e22504ca, lit .f64 0xbef6fdb69126ffe7]
def sinpiWide32 : List (FV .f64) := [lit .f64 0x400921fb5443b5c3, lit .f64 0xc014abbce56b2366, lit .f64 0x400466bbacb024a2, lit .f64 0xbfe32ca9e6bf80ea, lit .f64 0x3fb4bc899499446d]
def sinpiWide16 : List (FV .f32) := [lit .f32 0x40490fdb, lit .f32 0xc0a55de7, lit .f32 0x402335dd, lit .f32 0xbf19654f, lit .f32 0x3da5e44d]
def cospiWide32 : List (FV .f64) := [lit .f64 0x3ff0000000000000, lit .f64 0xc013bd3cc9be3639, lit .f64 0x40103c1f07ea6c8d, lit .f64 0xbff55d3c1c4d2f31, lit .f64 0x3fce1ec7267d1bf4, lit .f64 0xbf9a1e888f6fb6f8]
def cospiWide16 : List (FV .f32) := [lit .f32 0x3f800000, lit .f32 0xc09de9e6, lit .f32 0x4081e0f8, lit .f32 0xbfaae9e1, lit .f32 0x3e70f639, lit .f32 0xbcd0f444]
def deg2radExt : List (FV .f64) := [lit .f64 0x3f91df46a2529d39, lit .f64 0x3f91df46a0000000, lit .f64 0x3de294e9c8ae0ec6, lit .f64 0x41a0000002000000]
def sincThr64 : FV .f64 := lit .f64 0x3f50624dd2f1a9fc  -- 0.001
def sincThr32 : FV .f32 := lit .f32 0x3d4ccccd  -- 0.05f0
def cosc32 : List (FV .f32) := [lit .f32 0x3e8a4000, lit .f32 0xc0528d33, lit .f32 0x404fce4a, lit .f32 0xbf9278c9, lit .f32 0x3e5259b1, lit .f32 0x3ee66000, lit .f32 0xc0528d18, lit .f32 0x404fcae1, lit .f32 0xbf922d6d, lit .f32 0x3e494658]
def cosc64 : List (FV .f64) := [lit .f64 0x3fc5c40000000000, lit .f64 0xc00a51a6625307d3, lit .f64 0x4009f9cb402bc398, lit .f64 0xbff24feab5565c48, lit .f64 0x3fcac6805326b732, lit .f64 0xbf980608d10e2748, lit .f64 0x3f5d0a576dcb5d72, lit .f64 0x3fd1480000000000, lit .f64 0xc00a51a66252fcd9, lit .f64 0x4009f9cb40262ab7, lit .f64 0xbff24feab304480f, lit .f64 0x3fcac67e56f1391d, lit .f64 0xbf980524577ed4dc, lit .f64 0x3f5cb25eef2af5da, lit .f64 0x3fd5c40000000000, lit .f64 0xc00a51a66250e59b, lit .f64 0x4009f9cb3fa0530f, lit .f64 0xbff24fea97d508bc, lit .f64 0x3fcac67319ed0cf2, lit .f64 0xbf9802c5f947cb3c, lit .f64 0x3f5c4a01290c1fd2, lit .f64 0x3fd9980000000000, lit .f64 0xc00a51a6623da6e8, lit .f64 0x4009f9cb3c7bfdea, lit .f64 0xbff24fea2e06e2f3, lit .f64 0x3fcac6570d757151, lit .f64 0xbf97ff069b7db52e, lit .f64 0x3f5be29eb442a28e]
def rad2deg16 : FV .f16 := lit .f16 0x5329  -- Float16(57.28)
def rad2deg32 : FV .f32 := lit .f32 0x42652ee1  -- 57.29578f0
def deg2rad16 : FV .f16 := lit .f16 0x2478  -- Float16(0.01746)
def rad2deg64 : FV .f64 := lit .f64 0x404ca5dc1a63c1f8  -- 57.29577951308232
def deg2rad32 : FV .f32 := lit .f32 0x3c8efa35  -- 0.017453292f0
def deg2rad64 : FV .f64 := lit .f64 0x3f91df46a2529d39  -- 0.017453292519943295

end JuliaLean.MathCov.C

namespace JuliaLean.FloatFuncs

open JuliaLean.Float

/-- The seven rounding modes, `base/rounding.jl:48-110`. -/
inductive Mode where
  | Nearest | NearestTiesAway | NearestTiesUp | ToZero | FromZero | Up | Down
  deriving Repr, DecidableEq, Inhabited

/-- The four `F64.round` intrinsic modes. -/
def Mode.llvm : Mode → Option Rounding
  | .Nearest => some .RoundNearest
  | .NearestTiesAway => some .RoundNearestTiesAway
  | .ToZero => some .RoundToZero
  | .Up => some .RoundUp
  | .Down => some .RoundDown
  | _ => none

end JuliaLean.FloatFuncs

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `Float64(pi)`, the `π` constant of `base/mathconstants.jl:13` rounded to nearest. -/
def piF64 : F64 := lit 0x400921FB54442D18

end JuliaLean.MathFuncs

namespace JuliaLean.base.special.trig

open JuliaLean.Promotion

/--
Julia source: base/special/trig.jl:4-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct DoubleFloat64
    hi::Float64
    lo::Float64
end
```
-/
structure DF64 where
  hi : FV .f64
  lo : FV .f64

end JuliaLean.base.special.trig

namespace JuliaLean.NumMisc.Coverage

inductive FloatKind where | f16 | f32 | f64 deriving DecidableEq, Repr

end JuliaLean.NumMisc.Coverage

namespace JuliaLean.NumMisc

abbrev NF32 := JuliaLean.Promotion.Fl JuliaLean.Promotion.single

def nf32 (bits : Nat) : NF32 := JuliaLean.Promotion.Fl.ofBits bits

/-- One correctly rounded Float32 multiplication, as used by `x*x` and the final
`x*tanh_kernel(x*x)` in `base/special/hyperbolic.jl:174`. -/
def nf32Mul (x y : NF32) : NF32 :=
  if x.isfinite && y.isfinite then
    let a := x.toRat
    let b := y.toRat
    JuliaLean.Promotion.Fl.roundRat (a.1 * b.1) (a.2 * b.2) (x.signbit != y.signbit)
  else JuliaLean.Promotion.Fl.nan

/-- Float32 `muladd(x,y,z)` for the generated Horner form of `evalpoly`,
`base/math.jl:75-82`. -/
def nf32Fma (x y z : NF32) : NF32 :=
  if x.isfinite && y.isfinite && z.isfinite then
    let a := x.toRat
    let b := y.toRat
    let c := z.toRat
    let abDen := a.2 * b.2
    JuliaLean.Promotion.Fl.roundRat
      (a.1 * b.1 * (c.2 : Int) + c.1 * (abDen : Int))
      (abDen * c.2) false
  else JuliaLean.Promotion.Fl.nan

/-- The Float32 coefficients at `base/special/hyperbolic.jl:157-159`. -/
def tanhCoefficients32 : List NF32 :=
  [nf32 0x3f800000, nf32 0xbeaaaa63, nf32 0x3e087aa6,
   nf32 0xbd5b2657, nf32 0x3ca3a310, nf32 0xbba58fa2]

end JuliaLean.NumMisc

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `maxintfloat(::Type{Float64}) = 9007199254740992.`; `base/floatfuncs.jl:34`. -/
def maxintfloat : F64 := lit 0x4340000000000000

end JuliaLean.MathFuncs

namespace JuliaLean.MathCov.Trig

open JuliaLean JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

def h64 : FV .f64 := lit .f64 0x3fe0000000000000
def one64 : FV .f64 := one .f64
def two64 : FV .f64 := ofInt .f64 2

/-- `DoubleFloat64(hi, lo)`; `base/special/trig.jl:4-7`. -/
structure DF64 where
  hi : FV .f64
  lo : FV .f64

def piT : (T : FTy) → FV T | .f32 => piT32 | _ => conv piT64

end JuliaLean.MathCov.Trig

namespace JuliaLean.MathCov.TrigPi

open JuliaLean.Promotion

/-- A `Complex{T}` value. -/
structure Cx (T : FTy) where
  re : FV T
  im : FV T

end JuliaLean.MathCov.TrigPi

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `Float64(pi, RoundDown)`, the largest Float64 below π (its `nextfloat` lies above π);
`base/irrationals.jl:101-106`, `base/mathconstants.jl:13`. -/
def piRoundDown : F64 := lit 0x400921fb54442d18

end JuliaLean.MathFuncs

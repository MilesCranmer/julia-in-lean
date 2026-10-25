import JuliaLean.Float.Extras

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

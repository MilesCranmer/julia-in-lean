import JuliaLean.Promotion.RationalFloat

/-!
Numeric hashing at master `bbfa0ce4150` (`base/hashing.jl:75-246`,
`base/rational.jl:676-701`). The mixing primitives are deterministic functions of their
arguments, so a hash is modelled as the term of primitive calls it performs:
`hash_uint64(hash_mix_linear(v, h))` for a UInt64 `v` (`base/hashing.jl:75`),
`hash_integer(v, h)` for a mathematical integer `v` (`base/hashing.jl:147-160`, which
hashes the sign and the bytes of `abs(v)`), and `hx_NaN ⊻ h` (`base/hashing.jl:178`).
Equal terms give equal hashes.
-/

namespace JuliaLean.Promotion

open JuliaLean.Float
open JuliaLean.IntArith.Rational

inductive HTerm where
  | seed
  | u64 (v : Nat) (h : HTerm)
  | int (v : Int) (h : HTerm)
  | nanx (h : HTerm)
  deriving DecidableEq, Repr

/-- `hash(x::Int64, h) = hash(bitcast(UInt64, x), h)` and the narrower integer methods;
`base/hashing.jl:75-77`. -/
def hashI64 (v : Int) (h : HTerm) : HTerm := .u64 (wrapInt .u64 v).toNat h

/-- `hash(x::Float64, h)`; `base/hashing.jl:165-181`. The range tests are the exact mixed
comparisons of `base/float.jl:649-676`. -/
def hashF64 (x : Fl double) (h : HTerm) : HTerm :=
  let x' : FV .f64 := x
  if cmpIF .le (JInt.typemin .i64) x' && cmpFI .lt x' (JInt.typemax .i64) then
    let xi := x.unsafeTrunc .i64
    if isequalFI x' xi then hashI64 xi.val h else .u64 x.toBits h
  else if cmpIF .le (JInt.typemin .u64) x' && cmpFI .lt x' (JInt.typemax .u64) then
    let xu := x.unsafeTrunc .u64
    if isequalFI x' xu then .u64 xu.val.toNat h else .u64 x.toBits h
  else if x.isnan then .nanx h
  else .u64 x.toBits h

/-- `hash(x::Float32, h) = hash(Float64(x), h)`; `base/hashing.jl:183`. -/
def hashF32 (x : Fl single) (h : HTerm) : HTerm := hashF64 (Fl.convert x) h

/-- `hash(x::Float16, h)`; `base/hashing.jl:185-196`. -/
def hashF16 (x : Fl half) (h : HTerm) : HTerm :=
  let x' : FV .f16 := x
  if x.isfinite then
    let xi := x.unsafeTrunc .i64
    if isequalFI x' xi then hashI64 xi.val h else .u64 (Fl.convert (f := double) x).toBits h
  else if x.isnan then .nanx h
  else .u64 (Fl.convert (f := double) x).toBits h

/-- `trailing_zeros` of a nonzero integer. -/
def trailingZeros (n : Int) : Nat := go n.natAbs 200
where
  go (m : Nat) : Nat → Nat
    | 0 => 0
    | k + 1 => if m % 2 == 1 || m == 0 then 0 else 1 + go (m / 2) k

/-- `hash(ldexp(Float64(num), pow), h)` for a value exactly representable in Float64. -/
def hashExactF64 (num pow : Int) (h : HTerm) : HTerm :=
  hashF64 (if pow ≥ 0 then Fl.roundRat (num * 2 ^ pow.toNat) 1 false
    else Fl.roundRat num (2 ^ (-pow).toNat) false) h

/-- `hash(x::Real, h)` from `decompose(x) = (num, pow, den)`; `base/hashing.jl:200-246`.
`numTy` is the integer type of `num` (for the `num << (pow % 8)` shift). -/
def hashReal (numTy : IntTy) (d : Int × Int × Int) (h : HTerm) : HTerm :=
  let (num, pow, den) := d
  if num == 0 && den == 0 then hashF64 Fl.nan h
  else if num == 0 then hashF64 (Fl.zero (decide (den < 0))) h
  else if den == 0 then hashF64 (Fl.inf (decide (num < 0))) h
  else
    let (num, den) := if den < 0 then (-num, -den) else (num, den)
    let numZ := trailingZeros num
    let num := num / 2 ^ numZ
    let denZ := trailingZeros den
    let den := den / 2 ^ denZ
    let pow := pow + numZ - denZ
    let finish (h : HTerm) : HTerm :=
      let h := HTerm.int pow h
      HTerm.int (if pow > 0 then wrapInt numTy (num * 2 ^ (pow % 8).toNat) else num) h
    if den == 1 then
      let left := ndigits2 num + pow
      if -1074 ≤ pow then
        if 0 ≤ pow ∧ left ≤ 63 then hashI64 (num * 2 ^ pow.toNat) h
        else if 0 ≤ pow ∧ left ≤ 64 ∧ 0 ≤ num then .u64 (num * 2 ^ pow.toNat).toNat h
        else if left ≤ 1024 ∧ left - pow ≤ 53 then hashExactF64 num pow h
        else finish h
      else finish h
    else finish (HTerm.int den h)

/-- `hash(x::Rational{<:BitInteger64}, h)`; `base/rational.jl:679-701`. -/
def hashRat64 {t : IntTy} (x : Rat t) (h : HTerm) : HTerm :=
  let num := x.num.val
  let den := x.den.val
  if den == 1 then (if t == .u64 then .u64 num.toNat h else hashI64 num h)
  else if den == 0 then hashF64 (Fl.inf (decide (num ≤ 0))) h
  else
    let tail (pow num : Int) (h : HTerm) : HTerm :=
      let h := HTerm.int pow h
      HTerm.int (if pow > 0 then wrapInt t (num * 2 ^ (pow % 8).toNat) else num) h
    if den % 2 == 1 then
      let pow := trailingZeros num
      tail pow (num / 2 ^ pow) (HTerm.int den h)
    else
      let pz := trailingZeros den
      let den := den / 2 ^ pz
      let pow : Int := -(pz : Int)
      if den == 1 then
        if num.natAbs < 2 ^ 53 then hashExactF64 num pow h
        else tail pow num h
      else tail pow num (HTerm.int den h)

/-- Julia numbers of the modelled types. -/
inductive Num where
  | int (t : IntTy) (x : JInt t)
  | flt (T : FTy) (x : FV T)
  | rat (t : IntTy) (x : Rat t)

/-- `hash(x, h)` dispatch. -/
def hashNum : Num → HTerm → HTerm
  | .int t x, h =>
    match t with
    | .i128 | .u128 => hashReal t (x.val, 0, 1) h
    | .u64 => .u64 x.val.toNat h
    | _ => hashI64 x.val h
  | .flt .f64 x, h => hashF64 x h
  | .flt .f32 x, h => hashF32 x h
  | .flt .f16 x, h => hashF16 x h
  | .rat t x, h =>
    match t with
    | .i128 | .u128 => hashReal t (decomposeR x) h
    | _ => hashRat64 x h

end JuliaLean.Promotion

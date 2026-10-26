import JuliaLean.MathFuncs.Exp
import JuliaLean.MathFuncs.Log

/-!
Model of the Float64 methods of `base/special/pow.jl`, Julia master `bbfa0ce4150`:
`^(::Float64, ::Float64)`, `^(::Float64, ::Integer)` and both `pow_body` methods.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `use_power_by_squaring(n) = -2^12 <= n <= 3 * 2^13`; `base/special/pow.jl:1-3`. -/
def usePowerBySquaring (n : Int) : Bool := decide (-4096 ≤ n ∧ n ≤ 24576)

/-- `*(x::Bool, y::AbstractFloat) = ifelse(x, y, copysign(zero(y), y))`, also used for
`y * x`; `base/bool.jl:161-164`. -/
def boolMul (b : Bool) (y : F64) : F64 := if b then y else copysign F64.zero y

/-- `sign(x::Real)` for Float64; `base/number.jl:212`. -/
def signF (x : F64) : F64 :=
  if F64.lt x F64.zero then lit 0xbff0000000000000
  else if F64.lt F64.zero x then F64.one
  else x

/-- One iteration state `(x, xnlo, y, ynlo)` of the compensated power-by-squaring loop
`while n > 1 ... n >>>= 1 end`, with `fuel` bounding the iterations;
`base/special/pow.jl:130-140`. -/
def powBodyLoop : Nat → F64 → F64 → F64 → F64 → Int → F64 × F64 × F64 × F64
  | 0, x, xnlo, y, ynlo, _ => (x, xnlo, y, ynlo)
  | fuel + 1, x, xnlo, y, ynlo, n =>
    if n > 1 then
      let (y, ynlo) :=
        if n % 2 == 1 then
          let err := F64.muladd y xnlo (F64.mul x ynlo)
          let (y', ynlo') := twoMul x y
          (y', F64.add ynlo' err)
        else (y, ynlo)
      let err := F64.mul (F64.mul x (lit 0x4000000000000000)) xnlo
      let (x', xnlo') := twoMul x x
      powBodyLoop fuel x' (F64.add xnlo' err) y ynlo ((n % 2^64).toNat / 2 : Nat)
    else (x, xnlo, y, ynlo)

/-- Loop and final compensation of `pow_body(x::Float64, n::Integer)`;
`base/special/pow.jl:119-121,130-143`. The final `ifelse(..., muladd(x, y, err), x*y)` is
compiled with the product `x*y` shared by both branches, so that `muladd` is not fused:
on x86 Julia returns `x*y + err` with two roundings (e.g. `3.0^-3` gives
`0x3fa2f684bda12f69`, the fused value would be `0x3fa2f684bda12f68`). -/
def powBodyIFinish (x xnlo : F64) (n : Int) : F64 :=
  let (x, xnlo, y, ynlo) := powBodyLoop 64 x xnlo F64.one F64.zero n
  let err := F64.muladd y xnlo (F64.mul x ynlo)
  if F64.isfinite x && F64.isfinite err && !F64.iszero err then F64.add (F64.mul x y) err
  else F64.mul x y

/-- `pow_body(x::Float64, n::Integer)` for an Int64 value `n`, the compensated power by
squaring; `base/special/pow.jl:118-144`. -/
def powBodyI (x : F64) (n : Int) : F64 :=
  if n == 3 then F64.mul (F64.mul x x) x
  else if n < 0 then
    let rx := F64.div F64.one x
    if n == -2 then F64.mul rx rx
    else
      let xnlo := if F64.isfinite x then
          F64.mul (F64.neg (F64.fma x rx (lit 0xbff0000000000000))) rx
        else F64.zero true
      powBodyIFinish rx xnlo (JInt.wrap .i64 (-n)).val
  else powBodyIFinish x (F64.zero true) n

/-- `pow_body(x::Float64, y::Float64)`; `base/special/pow.jl:91-103`. -/
def powBodyF (x y : F64) : F64 :=
  let xu := if bitsOf x < 2^52 then
      (Nat.land (bitsOf (F64.mul x (lit 0x4330000000000000))) (2^63 - 1) + 2^64 - 52 * 2^52) % 2^64
    else bitsOf x
  let (logxhi, logxlo) := logExt xu
  let (xyhi, xylo) := twoMul logxhi y
  let xylo := F64.muladd logxlo y xylo
  let hi := F64.add xyhi xylo
  expImplLo hi (F64.sub xylo (F64.sub hi xyhi)) .e

/-- Body of `^(x::Float64, y::Float64)` after the clamp of `y` to `|y| <= 0x1.8p62`;
`base/special/pow.jl:16-29`. `unsafe_trunc(Int64, y)` is exact truncation and `y == yint`
is exact comparison. -/
def powFFClamped (x y : F64) : Jl F64 :=
  let (num, den) := F64.toRat y
  let yint := num.tdiv (den : Int)
  let yisint := num == yint * (den : Int)
  if yisint && yint == 0 then .ok F64.one
  else if yisint && usePowerBySquaring yint then .ok (powBodyI x yint)
  else if 2 * bitsOf x % 2^64 == 0 then
    .ok (boolMul (!F64.lt F64.zero y) (F64.mul (F64.abs y) F64.inf))
  else if F64.lt x F64.zero && !yisint then .error (.domainError "^")
  else
    let s : Int := if F64.lt x F64.zero then (if yint.tmod 2 != 0 then -1 else 1) else 1
    if !F64.isfinite x then
      .ok (boolMul (F64.lt F64.zero y || F64.isnan x) (copysign x (F64.ofInt s)))
    else .ok (copysign (powBodyF (F64.abs x) y) (F64.ofInt s))

/-- `^(x::Float64, y::Float64)`; `base/special/pow.jl:7-30`. -/
def powFF (x y : F64) : Jl F64 :=
  if bitsOf x == 0x3ff0000000000000 then .ok F64.one
  else if !F64.lt (F64.abs y) (lit 0x43d8000000000000) then
    if F64.isnan y then .ok y
    else powFFClamped x (F64.mul (signF y) (lit 0x43d8000000000000))
  else powFFClamped x y

/-- `^(x::Float64, n::Integer)` for the mathematical value `n` of any integer type;
`clamp(n, Int64)` saturates, `isodd(n)` uses the original `n`; `base/special/pow.jl:58-76`. -/
def powFI (x : F64) (n : Int) : F64 :=
  let n64 := if n > 2^63 - 1 then 2^63 - 1 else if n < -2^63 then -2^63 else n
  if n64 == 0 then F64.one
  else if usePowerBySquaring n64 then powBodyI x n64
  else if F64.isnan x then x
  else
    let s := if F64.signbit x && n.tmod 2 != 0 then lit 0xbff0000000000000 else F64.one
    let x := F64.abs x
    let y := F64.ofInt n64
    let (num, den) := F64.toRat y
    if num == n64 * (den : Int) then copysign (powBodyF x y) s
    else
      let n2 := n64.tmod 1024
      let y := F64.ofInt (n64 - n2)
      F64.mul (powBodyF x y) (copysign (powBodyI x n2) s)

end JuliaLean.MathFuncs

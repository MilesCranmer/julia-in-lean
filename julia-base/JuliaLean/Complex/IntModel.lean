import JuliaLean.Complex.Model

/-!
`power_by_squaring` (`base/intfuncs.jl:399-442`), `^` for complex numbers with
integer exponents (`base/complex.jl:886-894`), `Complex{T}` for fixed-width
integers `T`, and `Complex{Bool}` (`base/complex.jl:36,294-295,360-377`).
-/

namespace JuliaLean.Complex

open JuliaLean JuliaLean.Float

/-- Operations of `x_` used by `power_by_squaring`: `*`, `one`, `isone`, unary `-`. -/
structure MulOps (α : Type) where
  mul : α → α → α
  one : α
  isone : α → Bool
  neg : α → α

/-- `trailing_zeros(p)` for positive `p`; `fuel ≥ 64` covers every Int64. -/
def trailingZeros : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n != 0 && n % 2 == 0 then trailingZeros fuel (n / 2) + 1 else 0

/-- `while (t -= 1) >= 0; x = mul(x, x); end` run `k` times; `base/intfuncs.jl:436-438`. -/
def squareN {α : Type} (mul : α → α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => squareN mul k (mul x x)

/-- The outer loop `while p > 0`; `base/intfuncs.jl:433-440`. -/
def pbsLoop {α : Type} (mul : α → α → α) : Nat → α → α → Nat → α
  | 0, _, y, _ => y
  | fuel + 1, x, y, p =>
    if p = 0 then y
    else
      let t := trailingZeros 64 p + 1
      let x := squareN mul t x
      pbsLoop mul fuel x (mul y x) (p >>> t)

/-- `power_by_squaring(x_, p)` with `mul = *`; `base/intfuncs.jl:399-442`. -/
def powerBySquaring {α : Type} (ops : MulOps α) (x : α) (p : JInt .i64) : Jl α :=
  let xsq := ops.mul x x
  if p.val = 1 then .ok x
  else if p.val = 0 then .ok ops.one
  else if p.val = 2 then .ok xsq
  else if p.val < 0 then
    if ops.isone x then .ok x
    else if ops.isone (ops.neg x) then .ok (if p.val % 2 = 0 then ops.one else x)
    else .error (.domainError "Cannot raise an integer x to a negative power")
  else
    let n := p.val.toNat
    let t := trailingZeros 64 n + 1
    let x1 := if t - 1 > 0 then xsq else x
    let x2 := squareN ops.mul (t - 2) x1
    .ok (pbsLoop ops.mul 64 x2 x2 (n >>> t))

namespace CF64

/-- `Complex{Float64}` operations seen by `power_by_squaring`. -/
def ops : MulOps CF64 := ⟨mul, one, isone, neg⟩

/-- `^(z::Complex{<:AbstractFloat}, n::Integer)` for `n::Int`; `base/complex.jl:892-893`. -/
def powInt (z : CF64) (n : JInt .i64) : Jl CF64 :=
  if n.val ≥ 0 then powerBySquaring ops z n
  else do
    let w ← inv z
    powerBySquaring ops w (-n)

end CF64

/-- `Complex{T}` for a fixed-width integer type `T`; `base/complex.jl:13-16`. -/
structure CInt (t : IntTy) where
  re : JInt t
  im : JInt t
  deriving DecidableEq, Repr

namespace CInt

variable {t : IntTy}

/-- `one(Complex{T})`. -/
def one : CInt t := ⟨JInt.lit t 1, JInt.lit t 0⟩
/-- `isone(z::Complex)`; `base/complex.jl:155`. -/
def isone (z : CInt t) : Bool := z.re.val == 1 && z.im.val == 0
/-- `-(z::Complex)`; `base/complex.jl:291`. -/
def neg (z : CInt t) : CInt t := ⟨-z.re, -z.im⟩
/-- `conj(z::Complex)`; `base/complex.jl:280`. -/
def conj (z : CInt t) : CInt t := ⟨z.re, -z.im⟩
/-- `+(z::Complex, w::Complex)`; `base/complex.jl:292`. -/
def add (z w : CInt t) : CInt t := ⟨z.re + w.re, z.im + w.im⟩
/-- `*(z::Complex, w::Complex)`; `base/complex.jl:294-295`. -/
def mul (z w : CInt t) : CInt t :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
/-- `abs2(z::Complex)`; `base/complex.jl:282`. -/
def abs2 (z : CInt t) : JInt t := z.re * z.re + z.im * z.im

/-- `Complex{T}` operations seen by `power_by_squaring`. -/
def ops : MulOps (CInt t) := ⟨mul, one, isone, neg⟩

/-- `^(z::Complex{<:Integer}, n::Integer)` for `n::Int`; `base/complex.jl:894`. -/
def powInt (z : CInt t) (n : JInt .i64) : Jl (CInt t) := powerBySquaring ops z n

/-- `abs(x::Signed) = flipsign(x, x)` (`base/int.jl:234`); `abs(x::Unsigned) = x`. -/
def iabs (x : JInt t) : JInt t := if t.signed && x.val < 0 then -x else x

/-- `float(x)` of a fixed-width integer; `base/float.jl:243-305`. -/
def fl (x : JInt t) : F64 := F64.ofJInt x

/--
`/(a::Complex{T}, b::Complex{T}) where T<:Real` for a fixed-width integer `T`;
`base/complex.jl:360-377`. `isinf` of an integer is false (`base/float.jl:716`);
`Int / Int` is `float(x) / float(y)` (`base/int.jl:103`); mixed `Int`/`Float64`
arithmetic converts the integer first.
-/
def div (a b : CInt t) : CF64 :=
  let are := fl a.re
  let aim := fl a.im
  let bre := fl b.re
  let bim := fl b.im
  if (iabs b.re).val ≤ (iabs b.im).val then
    let r := F64.div bre bim
    let den := F64.add bim (F64.mul r bre)
    ⟨F64.div (F64.add (F64.mul are r) aim) den, F64.div (F64.sub (F64.mul aim r) are) den⟩
  else
    let r := F64.div bim bre
    let den := F64.add bre (F64.mul r bim)
    ⟨F64.div (F64.add are (F64.mul aim r)) den, F64.div (F64.sub aim (F64.mul are r)) den⟩

end CInt

/-- `Complex{Bool}`; `base/complex.jl:13-16,36`. -/
structure CBool where
  re : Bool
  im : Bool
  deriving DecidableEq, Repr

namespace CBool

/-- `im = Complex(false, true)`; `base/complex.jl:36`. -/
def imUnit : CBool := ⟨false, true⟩

/-- `Int(x::Bool)`. -/
def toInt (b : Bool) : JInt .i64 := JInt.lit .i64 (if b then 1 else 0)

/-- `Complex{Int}(z::Complex{Bool})`; `base/complex.jl:43`. -/
def toCInt (z : CBool) : CInt .i64 := ⟨toInt z.re, toInt z.im⟩

/--
`*(z::Complex, w::Complex)` (`base/complex.jl:294-295`) on two `Complex{Bool}`:
`Bool * Bool = x & y`, `Bool - Bool = Int(x) -% Int(y)`, `Bool + Bool = Int(x) +% Int(y)`
(`base/bool.jl:144-149`), so the result is a `Complex{Int}`.
-/
def mul (z w : CBool) : CInt .i64 :=
  ⟨toInt (z.re && w.re) - toInt (z.im && w.im), toInt (z.re && w.im) + toInt (z.im && w.re)⟩

end CBool

end JuliaLean.Complex

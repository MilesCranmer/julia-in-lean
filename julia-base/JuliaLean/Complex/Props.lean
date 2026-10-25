import JuliaLean.Complex.IntModel

/-!
Properties of `base/complex.jl` promised by docstrings, the manual, or obvious
invariants. Exact rational values use `F64.toRat`.
-/

namespace JuliaLean.Complex

open JuliaLean JuliaLean.Float

/-- Whether a `Jl` computation returned normally. -/
def jlOk {α : Type} : Jl α → Bool
  | .ok _ => true
  | .error _ => false

/-- Exact value of a finite binary64 number as a fraction with positive denominator. -/
def ratOf (x : F64) : Int × Int := ((F64.toRat x).1, ((F64.toRat x).2 : Int))

/-- Numerator and denominator of the exact real part `(ac + bd)/(c² + d²)` of `z/w`. -/
def exactDivRe (z w : CF64) : Int × Int :=
  let (na, da) := ratOf z.re
  let (nb, db) := ratOf z.im
  let (nc, dc) := ratOf w.re
  let (nd, dd) := ratOf w.im
  ((na * nc * db * dd + nb * nd * da * dc) * dc * dd,
   da * db * (nc * nc * dd * dd + nd * nd * dc * dc))

/-- Exact `x*y`: the binary64 product is finite and equal to the rational product. -/
def exactMul (x y : F64) : Bool :=
  let p := ratOf (F64.mul x y)
  let a := ratOf x
  let b := ratOf y
  F64.isfinite (F64.mul x y) && p.1 * (a.2 * b.2) == a.1 * b.1 * p.2

/-- Exact `x+y` or `x-y` (`sign = -1`): finite and equal to the rational sum. -/
def exactAdd (x y : F64) (sign : Int) : Bool :=
  let s := if sign < 0 then F64.sub x y else F64.add x y
  let p := ratOf s
  let a := ratOf x
  let b := ratOf y
  F64.isfinite s && p.1 * (a.2 * b.2) == (a.1 * b.2 + sign * b.1 * a.2) * p.2

/-! ### Division -/

/--
For finite `z` and finite nonzero real `x`, `z / complex(x, 0.0)` equals the
componentwise quotient `z / x`.
-/
def DivRealDivisor : Prop := ∀ z : CF64, ∀ x : F64,
  CF64.isfinite z = true → F64.isfinite x = true → F64.iszero x = false →
  CF64.isequal (CF64.div z ⟨x, Fl.pzero⟩) (CF64.divReal z x) = true

/--
For finite `z` and finite nonzero `w`, the real part of `z / w` is not NaN when
the exact real part of the quotient is at most `floatmax(Float64)` in magnitude.
-/
def DivNoSpuriousNaN : Prop := ∀ z w : CF64,
  CF64.isfinite z = true → CF64.isfinite w = true → CF64.iszero w = false →
  (exactDivRe z w).1.natAbs ≤ (F64.toRat F64.floatmax).1.natAbs * (exactDivRe z w).2.natAbs →
  F64.isnan (CF64.div z w).re = false

/--
For finite `z` and finite nonzero `w` whose exact real part `q` is a normal
binary64 magnitude, `real(z / w)` is finite with relative error at most `2^-20`.
-/
def DivComponentAccurate : Prop := ∀ z w : CF64,
  CF64.isfinite z = true → CF64.isfinite w = true → CF64.iszero w = false →
  let q := exactDivRe z w
  q.2.natAbs ≤ q.1.natAbs * 2^1022 →
  q.1.natAbs ≤ (F64.toRat F64.floatmax).1.natAbs * q.2.natAbs →
  let p := ratOf (CF64.div z w).re
  F64.isfinite (CF64.div z w).re = true ∧
    (p.1 * q.2 - q.1 * p.2).natAbs * 2^20 ≤ q.1.natAbs * p.2.natAbs

/--
`Complex{Int}` division of finite values by a nonzero divisor never returns a
NaN component (every component of the exact quotient is finite).
-/
def IntDivNoNaN : Prop := ∀ a b : CInt .i64,
  ¬ (b.re.val = 0 ∧ b.im.val = 0) → CF64.isnan (CInt.div a b) = false

/-! ### Powers -/

/-- `z^n` for `z::ComplexF64` and `n::Int` returns normally for every `n`. -/
def PowIntTotal : Prop := ∀ z : CF64, ∀ n : JInt .i64, jlOk (CF64.powInt z n) = true

/-- Exact Gaussian-integer product. -/
def gmul (a b : Int × Int) : Int × Int := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- Exact Gaussian-integer power by repeated multiplication. -/
def gpow (a : Int × Int) : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => gmul (gpow a n) a

/--
For `z::Complex{Int}` and `n ≥ 0`, `z^n` is the exact Gaussian-integer power with
each component reduced modulo 2^64 (Int wraps on overflow).
-/
def IntPowWraps : Prop := ∀ z : CInt .i64, ∀ n : JInt .i64, 0 ≤ n.val →
  CInt.powInt z n =
    .ok ⟨JInt.wrap .i64 (gpow (z.re.val, z.im.val) n.val.toNat).1,
         JInt.wrap .i64 (gpow (z.re.val, z.im.val) n.val.toNat).2⟩

/-! ### muladd -/

/--
When every product, difference and sum in `z*w + x` is exact, `muladd(z, w, x)`
equals `z*w + x`.
-/
def MuladdExact : Prop := ∀ z w x : CF64,
  exactMul z.re w.re = true → exactMul z.im w.im = true →
  exactMul z.re w.im = true → exactMul z.im w.re = true →
  exactAdd (F64.mul z.re w.re) (F64.mul z.im w.im) (-1) = true →
  exactAdd (F64.mul z.re w.im) (F64.mul z.im w.re) 1 = true →
  exactAdd (CF64.mul z w).re x.re 1 = true → exactAdd (CF64.mul z w).im x.im 1 = true →
  CF64.eq (CF64.muladd z w x) (CF64.add (CF64.mul z w) x) = true

/-! ### Structure, equality, hashing -/

/-- `conj(conj(z))` is bit-identical to `z`. -/
def ConjInvolution : Prop := ∀ z : CF64, CF64.conj (CF64.conj z) = z

/--
`isequal` implies equal `hash` for complex/complex and complex/real pairs, for
any real `hash` that respects `isequal` (the `hash` contract).
-/
def HashIsequal : Prop := ∀ H : F64 → UInt64 → UInt64,
  (∀ x y h, F64.isequal x y = true → H x h = H y h) →
  ∀ hImag h : UInt64,
    (∀ z w : CF64, CF64.isequal z w = true → CF64.hash H hImag z h = CF64.hash H hImag w h) ∧
    (∀ (z : CF64) (x : F64), CF64.isequalReal z x = true → CF64.hash H hImag z h = H x h)

/--
`isreal(z)` holds when `isequal(z, real(z))`, and for a non-NaN real part
`isreal(z)` is exactly `z == real(z)`.
-/
def IsrealDoc : Prop := ∀ z : CF64,
  (CF64.isequalReal z z.re = true → CF64.isreal z = true) ∧
  (F64.isnan z.re = false → CF64.isreal z = CF64.eqReal z z.re)

/--
`false * z` is a signed zero in both components for every `z::ComplexF64`,
including infinities and NaNs (`false` is a strong zero).
-/
def FalseStrongZero : Prop := ∀ z : CF64,
  CF64.iszero (CF64.boolMul false z) = true ∧ CF64.isnan (CF64.boolMul false z) = false

/--
`Complex{Bool} * Complex{Bool}` equals the product of the operands promoted to
`Complex{Int}`; in particular `im * im == -1 + 0im`.
-/
def BoolMulPromotes : Prop :=
  (∀ z w : CBool, CBool.mul z w = CInt.mul z.toCInt w.toCInt) ∧
  CBool.mul CBool.imUnit CBool.imUnit = ⟨JInt.lit .i64 (-1), JInt.lit .i64 0⟩

/--
Branch cut of `sqrt`: for `real(z) < 0` the imaginary part of `sqrt(z)` carries
the sign of `imag(z)`, so `-0.0im` lies below the negative real axis.
-/
def SqrtBranchCut : Prop := ∀ x y : F64, ∀ r : CF64,
  F64.lt x Fl.pzero = true → CF64.sqrt ⟨x, y⟩ = .ok r → F64.signbit r.im = F64.signbit y

/-- `abs(conj(z))` and `abs(-z)` are identical to `abs(z)`, including NaN and Inf parts. -/
def AbsConjNeg : Prop := ∀ z : CF64,
  CF64.abs (CF64.conj z) = CF64.abs z ∧ CF64.abs (CF64.neg z) = CF64.abs z

end JuliaLean.Complex

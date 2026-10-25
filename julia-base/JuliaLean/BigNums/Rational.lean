import JuliaLean.Promotion.IEEE
import JuliaLean.BigNums.Int

/-!
`Rational{BigInt}` comparison and float conversion at master `bbfa0ce4150`
(`base/gmp.jl:958-1120`, `base/mpfr.jl:565-571`).

`cmp(::Rational{BigInt}, ::Rational{BigInt})` returns GMP's `mpq_cmp` unchanged. The GMP
manual (§6 "Rational Number Functions") only fixes the sign of `mpq_cmp` and requires
canonical operands (positive denominators). The model mirrors GMP 6.3's `mpq/cmp.c`
(`mpq_cmp_numden`): its early exits return signed limb counts. For a zero denominator the
function reads `PTR(DEN)[den_size - 1]` at index `-1`; that call is undefined and the model
returns `none`.
-/

namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-- A `Rational{BigInt}` as Julia stores it: `den ≥ 0`, coprime components, and `±1//0` for the
infinities. -/
structure QBig where
  num : Int
  den : Nat
  deriving DecidableEq, Repr

/-- `count_leading_zeros` of a nonzero 64-bit limb. -/
def clz (w : Nat) : Nat := 64 - (w.log2 + 1)

/-- The most significant limb of `abs(x)` (`PTR(x)[size - 1]`), for `x ≠ 0`. -/
def topLimb (x : Int) : Nat := limb x (nlimbs x - 1)

/-- `mpq_cmp(op1, op2)` as implemented in GMP 6.3 `mpq/cmp.c` (`mpq_cmp_numden`). -/
def mpqCmp (a b : QBig) : Option Int :=
  let n1 := size a.num
  let n2 := size b.num
  let d1 := nlimbs a.den
  let d2 := nlimbs b.den
  if n1 = 0 then some (-n2)
  else if n2 = 0 then some n1
  else if decide (n1 < 0) != decide (n2 < 0) then some n1
  else if d1 = 0 ∨ d2 = 0 then none
  else
    let sign1 := n1
    let a1 := n1.natAbs
    let d1h := topLimb a.den
    let d2h := topLimb b.den
    let op2Int := d2 = 1 ∧ d2h = 1
    let op1Int := d1 = 1 ∧ d1h = 1
    if op2Int ∧ op1Int then
      if sign1 ≠ n2 then some (if sign1 > n2 then 1 else -1)
      else
        let c : Int := if a.num.natAbs < b.num.natAbs then -1
          else if a.num.natAbs = b.num.natAbs then 0 else 1
        some (if sign1 > 0 then c else -c)
    else
      let a2 := n2.natAbs
      let oi : Nat := if op2Int then 1 else 0
      let t1 := a1 + d2
      let t2 := a2 + d1
      if t1 > t2 + 1 then some sign1
      else if t2 + oi > t1 + 1 then some (-sign1)
      else
        let bits1 := t1 * 64 - clz (topLimb a.num) - clz d2h
        let bits2 := t2 * 64 - clz (topLimb b.num) - clz d1h
        if bits1 > bits2 + 1 then some sign1
        else if bits2 + oi > bits1 + 1 then some (-sign1)
        else
          -- step 3: exact cross products; `cc` is their limb-count difference or `mpn_cmp`
          let p1 := a.num.natAbs * b.den
          let p2 := b.num.natAbs * a.den
          let s1 : Int := nlimbs p1
          let s2 : Int := nlimbs p2
          let cc : Int := if s1 ≠ s2 then s1 - s2
            else if p1 < p2 then -1 else if p1 = p2 then 0 else 1
          some (if sign1 < 0 then -cc else cc)

/-- `cmp(x::Rational{BigInt}, y::Rational{BigInt})`, `base/gmp.jl:1116-1118`. -/
def cmpQ (a b : QBig) : Option Int := mpqCmp a b

/-- The order of `Rational` values, with `±1//0` the infinities (`base/rational.jl`). -/
def qOrder (a b : QBig) : Int :=
  let l := a.num * b.den
  let r := b.num * a.den
  if a.den = 0 ∧ b.den = 0 then (if a.num < b.num then -1 else if a.num = b.num then 0 else 1)
  else if l < r then -1 else if l = r then 0 else 1

/-- A normalized `Rational{BigInt}`: positive denominator and coprime parts, or `±1//0`. -/
def QBig.normalized (q : QBig) : Prop :=
  (0 < q.den ∧ Nat.gcd q.num.natAbs q.den = 1) ∨ (q.den = 0 ∧ (q.num = 1 ∨ q.num = -1))

/-- `cmp` on finite `Rational{BigInt}` values returns `-1`, `0` or `1` (the `cmp` docstring,
`base/operators.jl:508-511`). -/
def RationalCmpUnit : Prop :=
  ∀ a b : QBig, 0 < a.den → 0 < b.den → a.normalized → b.normalized →
    ∃ c, cmpQ a b = some c ∧ (c = -1 ∨ c = 0 ∨ c = 1)

theorem rationalCmpUnit_refuted : ¬ RationalCmpUnit := by
  intro h
  obtain ⟨c, hc, h1⟩ := h ⟨0, 1⟩ ⟨2 ^ 200, 1⟩ (by decide) (by decide)
    (Or.inl ⟨by decide, by decide⟩) (Or.inl ⟨by decide, by decide⟩)
  have : cmpQ ⟨0, 1⟩ ⟨2 ^ 200, 1⟩ = some (-4) := by decide +kernel
  rw [this] at hc
  cases hc
  omega

/-- `cmp` on `Rational{BigInt}` values, infinite ones included, is a defined call whose sign is
the order of the values (`isless`, `base/operators.jl:508-511`). -/
def RationalCmpIsless : Prop :=
  ∀ a b : QBig, a.normalized → b.normalized → ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b

theorem rationalCmpIsless_refuted : ¬ RationalCmpIsless := by
  intro h
  obtain ⟨c, hc, _⟩ := h ⟨1, 0⟩ ⟨1, 2⟩ (Or.inr ⟨rfl, Or.inl rfl⟩) (Or.inl ⟨by decide, by decide⟩)
  have : cmpQ ⟨1, 0⟩ ⟨1, 2⟩ = none := by decide +kernel
  rw [this] at hc
  cases hc

/-- `Rational{BigInt}(x::AbstractFloat)` for `x = Float64`, `base/mpfr.jl:565-571`. NaN builds
`zero(BigInt)//zero(BigInt)`, which `Rational{BigInt}(num, den)` rejects with
`ArgumentError` (`base/gmp.jl:1004-1006`). -/
def rationalBigOfF64 (x : Fl double) : Jl QBig :=
  if x.isnan then .error (.argumentError "invalid rational: zero(BigInt)//zero(BigInt)")
  else if x.isinf then .ok ⟨if x.signbit then -1 else 1, 0⟩
  else if x.iszero then .ok ⟨0, 1⟩
  else
    let (n, d) := x.toRat
    let g := Nat.gcd n.natAbs d
    .ok ⟨n / g, d / g⟩

/-- Converting NaN to `Rational{BigInt}` throws `InexactError`, as for every other `Rational{T}`
and every lossy conversion (`convert` docstring, `base/essentials.jl`). -/
def RationalOfNaNInexact : Prop :=
  ∀ x : Fl double, x.isnan = true → ∃ fn, rationalBigOfF64 x = .error (.inexactError fn)

theorem rationalOfNaNInexact_refuted : ¬ RationalOfNaNInexact := by
  intro h
  obtain ⟨fn, hfn⟩ := h Fl.nan (by decide)
  simp [rationalBigOfF64, (by decide : (Fl.nan : Fl double).isnan = true)] at hfn

end JuliaLean.BigNums

import JuliaLean.base.mpfr

/-!
Specification only: defines the real constant pi for primitive laws.
The rational enclosures and certificates are mathematical specifications, never
Julia model execution or a replacement implementation of mpfr_const_pi.
-/
namespace JuliaLean.Spec.Pi
open JuliaLean JuliaLean.base.mpfr

/-- Integer enclosure of atan(1/q), scaled by 2^bits. Each truncated term
contributes at most one unit of interval width; the alternating remainder is
at most the first omitted term. q≥2 is the domain used by Machin's identity. -/
def atanBounds (q bits terms : Nat) : Int × Int := Id.run do
  let scale := 2^bits
  let mut lower : Int := 0
  let mut upper : Int := 0
  for k in List.range terms do
    let denominator := (2*k+1)*q^(2*k+1)
    let term : Int := (scale / denominator : Nat)
    if k%2 = 0 then
      lower := lower + term
      upper := upper + term + 1
    else
      lower := lower - term - 1
      upper := upper - term
  let tail : Int := (scale / ((2*terms+1)*q^(2*terms+1)) : Nat) + 1
  if terms%2 = 0 then upper := upper + tail else lower := lower - tail
  return (lower,upper)

/-- π = 16 atan(1/5) - 4 atan(1/239) (Machin's identity).
The endpoints enclose the mathematical value, rather than an IEEE approximation.
https://en.wikipedia.org/wiki/Machin-like_formula -/
def piBounds (depth : Nat) : Int × Int × Nat :=
  let bits := 4*depth+32
  let a := atanBounds 5 bits (depth+1)
  let b := atanBounds 239 bits (depth+1)
  (16*a.1-4*b.2,16*a.2-4*b.1,2^bits)

/-- An exact Dedekind cut representation: q < π iff q lies below some lower
Machin enclosure. n/d has positive denominator; the other relation is π < n/d. -/
def rationalBelowPi (n : Int) (d : Nat) : Prop :=
  0 < d ∧ ∃ depth, n*(piBounds depth).2.2 < (piBounds depth).1*d

def piBelowRational (n : Int) (d : Nat) : Prop :=
  0 < d ∧ ∃ depth, (piBounds depth).2.1*d < n*(piBounds depth).2.2

/-- Equality of represented numbers, independent of a finite mantissa/scale
encoding. Special values retain their sign, including signed zero. -/
def sameValue (a b : FP) : Bool :=
  match a, b with
  | .finite _ _, .finite _ _ =>
    let (an, ad) := a.toRat
    let (bn, bd) := b.toRat
    decide (an * (bd : Int) = bn * (ad : Int))
  | _, _ => decide (a = b)

/-- A finite check of the MPFR π result. Both enclosure endpoints must round
to the same stored value and have the same nonzero ternary sign and flags.
This checks only rounding π, never a remainder or a double-double result. -/
def piCertificate (state : Context) (precision : Clong) (mode : Mode)
    (depth : Nat) (result : PrimitiveResult) : Bool :=
  if mode = .faithful then false else
  let (lower,upper,denominator) := piBounds depth
  let lo := roundRat state precision mode lower denominator
  let hi := roundRat state precision mode upper denominator
  decide (lo.value = hi.value ∧ lo.ternary = hi.ternary ∧ lo.ternary.val ≠ 0 ∧
    lo.flags = hi.flags ∧ sameValue result.value.value lo.value.value = true ∧
    result.value.prec = precision ∧ result.value.sign = lo.value.sign ∧
    JuliaLean.base.gmp.sgn result.ternary.val = JuliaLean.base.gmp.sgn lo.ternary.val ∧
    result.flags = lo.flags)

/-- MPFR manual §§4.4,4.6,5.7: in a documented supported rounding mode,
mpfr_const_pi sets its destination to correctly rounded π, returns the ternary
comparison with exact π, and raises the prescribed exception flags.
The finite witness expresses that contract through enclosing rational values.
The C call is generated at base/irrationals.jl:274-278; destination construction
uses base/mpfr.jl:124-172. No law about any Julia caller is assumed.
https://www.mpfr.org/mpfr-current/mpfr.html#Transcendental-Functions -/
def PiRounded (state : Context) (precision : Clong) (mode : Mode)
    (result : PrimitiveResult) : Prop :=
  ∃ depth, piCertificate state precision mode depth result = true

end JuliaLean.Spec.Pi

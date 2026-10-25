import JuliaLean.MathFuncs.Pow

/-!
Universally quantified properties of `exp`, `log`, `^`, `exponent`, `significand` and
`frexp` promised by docstrings in `base/math.jl` and `base/special/*.jl`.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `exp(0) == 1` and `expm1(±0) === ±0`, for both signed zeros: `exp` docstring
(`base/special/exp.jl:337`), `expm1` docstring (`base/special/exp.jl:495`). -/
def expZero : Prop := ∀ s : Bool,
  exp (F64.zero s) = F64.one ∧ exp2 (F64.zero s) = F64.one ∧ exp10 (F64.zero s) = F64.one ∧
    expm1 (F64.zero s) = F64.zero s

/-- `log(1) === 0.0` in every base (the `log.(exp.(-1:1))` example, `base/math.jl:538`)
and `log1p(±0) === ±0` (`base/math.jl:616`). -/
def logOne : Prop :=
  (∀ b : LogBase, logImpl F64.one b = .ok (F64.zero false)) ∧
  (∀ s : Bool, log1p (F64.zero s) = .ok (F64.zero s))

/-- `log` of either signed zero is `-Inf` in every base; `log1p(-1) == -Inf`. -/
def logZero : Prop :=
  (∀ b : LogBase, ∀ s : Bool, logImpl (F64.zero s) b = .ok (F64.inf true)) ∧
  log1p (F64.neg F64.one) = .ok (F64.inf true)

/-- `log`, `log2`, `log10` docstrings (`base/math.jl:511,550,583`): "Throw a DomainError
for negative Real arguments", for every negative Float64 including `-Inf`. -/
def logNegDomain : Prop := ∀ x : F64, ∀ b : LogBase, F64.lt x F64.zero = true →
  ∃ m, logImpl x b = .error (.domainError m)

/-- `log1p` docstring (`base/math.jl:608-609`): DomainError for arguments less than -1. -/
def log1pDomain : Prop := ∀ x : F64, F64.lt x (F64.neg F64.one) = true →
  ∃ m, log1p x = .error (.domainError m)

/-- `log2` is exact on powers of two, generalising the docstring example
`log2.(2.0 .^ (-1:1))` (`base/math.jl:570`) to every binary64 power of two `2^k`,
`-1074 ≤ k ≤ 1023`. -/
def log2Pow2Exact : Prop := ∀ k : Fin 2098,
  log2 (F64.ldexp F64.one ((k : Int) - 1074)) = .ok (F64.ofInt ((k : Int) - 1074))

/-- `exp2` is exact on integers, generalising `exp2(5) == 32.0`
(`base/special/exp.jl:360`) to every integer `k` with `2^k` a binary64 number. -/
def exp2IntegerExact : Prop := ∀ k : Fin 2098,
  exp2 (F64.ofInt ((k : Int) - 1074)) = F64.ldexp F64.one ((k : Int) - 1074)

/-- `exp10(2) == 100.0` and `log10(100) == 2.0` (`base/special/exp.jl:381`,
`base/math.jl:589`), generalised to every exactly representable power `10^k`, `0 ≤ k ≤ 22`. -/
def exp10Log10Exact : Prop := ∀ k : Fin 23,
  exp10 (F64.ofInt (k : Int)) = F64.ofInt (10^(k : Nat)) ∧
    log10 (F64.ofInt (10^(k : Nat))) = .ok (F64.ofInt (k : Int))

/-- `x^0 == 1` for every Float64 `x`, NaN included, with a Float64 (`±0.0`) or Integer
zero exponent (`base/special/pow.jl:17,60`; IEEE 754 `pow(x, ±0) = 1`). -/
def powZeroExponent : Prop := ∀ x : F64,
  powFF x (F64.zero false) = .ok F64.one ∧ powFF x (F64.zero true) = .ok F64.one ∧
    powFI x 0 = F64.one

/-- `1.0^y == 1` for every Float64 `y`, NaN and infinities included
(`base/special/pow.jl:9`; IEEE 754 `pow(+1, y) = 1`). -/
def powOneBase : Prop := ∀ y : F64, powFF F64.one y = .ok F64.one

/-- `significand` docstring, `base/math.jl:1005-1007`: for nonzero finite `x`, the result
has the sign of `x` and magnitude in `[1, 2)`, and `x == significand(x) * 2^exponent(x)`. -/
def significandRange : Prop := ∀ x : F64, F64.isfinite x = true → F64.iszero x = false →
  F64.signbit (F64.significand x) = F64.signbit x ∧
  F64.le F64.one (F64.abs (F64.significand x)) = true ∧
  F64.lt (F64.abs (F64.significand x)) (F64.ofInt 2) = true ∧
  ∃ e, F64.exponent x = .ok e ∧ F64.ldexp (F64.significand x) e = x

/-- `frexp` docstring, `base/math.jl:1043-1044`: `(f, e) = frexp(x)` has `|f|` in
`[1/2, 1)` (for nonzero finite `x`) and `x == f * 2^e`. -/
def frexpRange : Prop := ∀ x : F64, F64.isfinite x = true → F64.iszero x = false →
  F64.le (F64.ofBits 0x3fe0000000000000) (F64.abs (F64.frexp x).1) = true ∧
  F64.lt (F64.abs (F64.frexp x).1) F64.one = true ∧
  F64.ldexp (F64.frexp x).1 (F64.frexp x).2 = x

/-- `exponent` docstring, `base/math.jl:903`: for nonzero finite Float64 `x`, `exponent(x)`
is the largest `y` with `2^y ≤ |x|`. -/
def exponentFloatDefinition : Prop := ∀ x : F64, F64.isfinite x = true → F64.iszero x = false →
  ∃ e, F64.exponent x = .ok e ∧
    F64.le (F64.ldexp F64.one e) (F64.abs x) = true ∧
    F64.lt (F64.abs x) (F64.ldexp F64.one (e + 1)) = true

/-- IEEE 754 `pow(±0, -1) = ±Inf` (odd negative integer exponent), for both the Float64
and the Integer exponent methods (`base/special/pow.jl:7-31,58-75`). -/
def powZeroNegOne : Prop := ∀ s : Bool,
  powFF (F64.zero s) (F64.neg F64.one) = .ok (F64.inf s) ∧ powFI (F64.zero s) (-1) = F64.inf s

/-- `x^1 === x` for every non-NaN Float64, with a Float64 or an Integer exponent
(`base/special/pow.jl:20,62`). -/
def powOneExponent : Prop := ∀ x : F64, F64.isnan x = false →
  powFF x F64.one = .ok x ∧ powFI x 1 = x

end JuliaLean.MathFuncs

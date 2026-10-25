import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Complex.Model
import JuliaLean.Complex.IntModel
import JuliaLean.Complex.Props
import JuliaLean.Complex.Refutations
import JuliaLean.Complex.Proofs
import JuliaLean.Complex.PowProof
import JuliaLean.Complex.Validation

namespace JuliaLean.Complex

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- refuted
  { id := "complex-div-real-divisor", juliaFile := "base/complex.jl"
    juliaFns := ["/(::ComplexF64, ::ComplexF64)"]
    statement := "For finite z and finite nonzero real x, z / complex(x, 0.0) equals the componentwise quotient z / x."
    source := "invariant (real-valued complex divisor behaves like real division); issue #48457", status := .refuted
    prop := ``DivRealDivisor, thm := some ``divRealDivisor_refuted
    issue := "#48457 (closed, same 49.0 example)"
    notes := "complex(49.0,0.0)/complex(49.0,0.0) == 0.9999999999999999+0.0im because robust_cdiv2 multiplies by t = 1/c. The / docstring defines x/y as x*inv(y), so P3." },
  { id := "complex-div-spurious-nan", juliaFile := "base/complex.jl"
    juliaFns := ["/(::ComplexF64, ::ComplexF64)", "robust_cdiv2"]
    statement := "For finite z and finite nonzero w, real(z/w) is not NaN when the exact real part of z/w is at most floatmax in magnitude."
    source := "invariant; base/complex.jl:394-396 (scaled robust division); issue #5979", status := .refuted
    prop := ``DivNoSpuriousNaN, thm := some ``divNoSpuriousNaN_refuted
    issue := "related #5979 (closed), #22983 (closed); none found for this case"
    notes := "complex(1.0, 2.0^1000)/complex(2.0^-40, 0.0) == NaN + Inf*im: robust_cdiv2's r == 0 branch evaluates 0*(b/c) = 0*Inf. Also (Inf+0im)/(1+0im) == Inf + NaN*im." },
  { id := "complex-div-subnormal-ratio", juliaFile := "base/complex.jl"
    juliaFns := ["/(::ComplexF64, ::ComplexF64)", "robust_cdiv1"]
    statement := "For finite z and nonzero finite w whose exact real part is a normal binary64 magnitude, real(z/w) is finite with relative error at most 2^-20."
    source := "base/complex.jl:394-396 (robust division, arXiv:1210.4539)", status := .refuted
    prop := ``DivComponentAccurate, thm := some ``divComponentAccurate_refuted
    issue := "none found (queries: complex division accuracy, complex division underflow, complex division subnormal, robust complex division); related #5072"
    notes := "complex(2.0^1000, 0.0)/complex(3*nextfloat(0.0), 2.0) has real part 2^-74 instead of about 3*2^-76: r = c/d underflows gradually. Normwise accurate, so P3." },
  { id := "complex-int-div-typemin", juliaFile := "base/complex.jl"
    juliaFns := ["/(::Complex{T}, ::Complex{T}) where T<:Real"]
    statement := "Complex{Int} division by a nonzero divisor never returns a NaN component."
    source := "invariant; base/docs/basedocs.jl:3552 (floating-point results for integer arguments)", status := .refuted
    prop := ``IntDivNoNaN, thm := some ``intDivNoNaN_refuted
    issue := "none found (queries: complex typemin, Complex Int division, complex integer division NaN, complex division NaN)"
    notes := "Complex(1,0)/Complex(typemin(Int),0) == NaN + NaN*im: abs(typemin) wraps negative, so base/complex.jl:368 takes the branch dividing by the zero component." },
  { id := "complex-pow-typemin", juliaFile := "base/complex.jl"
    juliaFns := ["^(::Complex{<:AbstractFloat}, ::Integer)", "power_by_squaring"]
    statement := "z^n for z::ComplexF64 and n::Int returns normally for every z and n."
    source := "invariant; real analogue fixed in #57464", status := .refuted
    prop := ``PowIntTotal, thm := some ``powIntTotal_refuted
    issue := "none found (queries: complex power typemin, power_by_squaring typemin, complex typemin); related #57464 (closed, Float32/Float16)"
    notes := "complex(2.0,0.0)^typemin(Int) throws DomainError because -typemin(Int) wraps; 2.0^typemin(Int) == 0.0." },
  { id := "complex-muladd-exact", juliaFile := "base/complex.jl"
    juliaFns := ["muladd(::Complex, ::Complex, ::Complex)"]
    statement := "When every product, difference and sum in z*w + x is exact, muladd(z, w, x) == z*w + x."
    source := "base/math.jl:1248-1252 (muladd docstring)", status := .refuted
    prop := ``MuladdExact, thm := some ``muladdExact_refuted
    issue := "none found (queries: complex muladd, muladd complex, PR complex muladd); related #59684 (closed), PR #62005 (open)"
    notes := "z = w = 2^30 + 2^30im, x = 1: muladd gives 0 + 2^61im, z*w + x gives 1 + 2^61im. The complex muladd reassociates real(z)*real(w) - (imag(z)*imag(w) - real(x))." },
  -- proven
  { id := "complex-conj-involution", juliaFile := "base/complex.jl"
    juliaFns := ["conj(::Complex)"]
    statement := "conj(conj(z)) is bit-identical to z for every ComplexF64 z, including NaN payloads and signed zeros."
    source := "base/complex.jl:268-280 (conj docstring)", status := .proven
    prop := ``ConjInvolution, thm := some ``conjInvolution_proven },
  { id := "complex-isequal-hash", juliaFile := "base/complex.jl"
    juliaFns := ["hash(::Complex, ::UInt)", "isequal(::Complex, ::Complex)", "isequal(::Complex, ::Real)"]
    statement := "isequal(z, w) implies hash(z, h) == hash(w, h), and isequal(z, x) for real x implies hash(z, h) == hash(x, h), given a real hash that respects isequal."
    source := "hash docstring (isequal(x,y) implies hash(x)==hash(y)); base/complex.jl:250-263", status := .proven
    prop := ``HashIsequal, thm := some ``hashIsequal_proven
    notes := "Holds for -0.0 and NaN components: complex isequal is componentwise isequal." },
  { id := "complex-isreal-doc", juliaFile := "base/complex.jl"
    juliaFns := ["isreal(::Complex)", "==(::Complex, ::Real)"]
    statement := "isequal(z, real(z)) implies isreal(z); for non-NaN real part, isreal(z) == (z == real(z))."
    source := "base/complex.jl:126-131 (isreal docstring)", status := .proven
    prop := ``IsrealDoc, thm := some ``isrealDoc_proven },
  { id := "complex-false-strong-zero", juliaFile := "base/complex.jl"
    juliaFns := ["*(::Bool, ::Complex)"]
    statement := "false * z is a (signed) zero in both components for every ComplexF64 z, including Inf and NaN components."
    source := "Bool docstring (false is a strong zero); base/complex.jl:322, base/bool.jl:161-164", status := .proven
    prop := ``FalseStrongZero, thm := some ``falseStrongZero_proven },
  { id := "complex-bool-mul-promotes", juliaFile := "base/complex.jl"
    juliaFns := ["*(::Complex{Bool}, ::Complex{Bool})", "im"]
    statement := "Complex{Bool} * Complex{Bool} equals the product of both operands converted to Complex{Int}; im*im == -1 + 0im."
    source := "base/complex.jl:20-31 (im docstring: im * im == -1 + 0im)", status := .proven
    prop := ``BoolMulPromotes, thm := some ``boolMulPromotes_proven },
  { id := "complex-sqrt-branch-cut", juliaFile := "base/complex.jl"
    juliaFns := ["sqrt(::Complex)"]
    statement := "For real(z) < 0 (including -Inf), imag(sqrt(z)) has the sign of imag(z); -0.0im is below the branch cut."
    source := "base/math.jl:644-646 (sqrt branch-cut note)", status := .proven
    prop := ``SqrtBranchCut, thm := some ``sqrtBranchCut_proven },
  { id := "complex-int-pow-wraps", juliaFile := "base/complex.jl"
    juliaFns := ["^(::Complex{<:Integer}, ::Integer)", "power_by_squaring"]
    statement := "For z::Complex{Int} and n >= 0, z^n is the exact Gaussian-integer power with both components reduced modulo 2^64."
    source := "manual (integer arithmetic wraps on overflow); base/complex.jl:894", status := .proven
    prop := ``IntPowWraps, thm := some ``intPowWraps_proven
    notes := "No checked_pow exists for Complex; overflow wraps exactly like repeated Int multiplication." },
  { id := "complex-abs-conj-neg", juliaFile := "base/complex.jl"
    juliaFns := ["abs(::Complex)", "hypot(::Float64, ::Float64)"]
    statement := "abs(conj(z)) and abs(-z) are identical to abs(z) for every ComplexF64 z."
    source := "invariant |conj z| = |-z| = |z|; base/complex.jl:281, base/math.jl:732-786", status := .proven
    prop := ``AbsConjNeg, thm := some ``absConjNeg_proven }
]

end JuliaLean.Complex

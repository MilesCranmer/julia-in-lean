import JuliaLean.BigNumsCov.Common
import JuliaLean.BigNumsCov.Gmp
import JuliaLean.BigNumsCov.Mpfr
import JuliaLean.BigNumsCov.MpfrFaithful.Entries
import JuliaLean.BigNumsCov.Raw
import JuliaLean.Registry.Types

namespace JuliaLean.BigNumsCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "bignumscov-gmp-bootstrap", juliaFile := "base/gmp.jl"
    juliaFns := ["version", "major_version", "bits_per_limb", "BigInt(; nbits)", "__init__", "gmpz", "sizeinbase"]
    statement := "GMP setup reports version mismatches by limb compatibility, BigInt construction returns the initialized allocation, and primitive observations return their primitive value."
    source := "base/gmp.jl:39-169"
    status := .proven, prop := ``Gmp.GmpBootstrapCorrect, thm := some ``Gmp.gmpBootstrapCorrect },
  { id := "bignumscov-gmp-mpz-mutation", juliaFile := "base/gmp.jl"
    juliaFns := ["init!", "init2!", "realloc2!", "generated MPZ unary/binary mutators", "fac_ui!", "powm!"]
    statement := "Every generated MPZ allocating and aliasing wrapper calls its selected primitive with the source argument order and returns the destination object."
    source := "base/gmp.jl:161-253"
    status := .proven, prop := ``WrapperAllocationCorrect, thm := some ``wrapperAllocationCorrect },
  { id := "bignumscov-gmp-mpz-observers", juliaFile := "base/gmp.jl"
    juliaFns := ["popcount", "mpn_popcount", "tdiv_qr!", "gcdext!", "cmp", "get_str!", "set_str!", "export!", "limbs_write!", "tstbit"]
    statement := "MPZ observers preserve primitive results and output order; export rejects non-unit stride, grows to the digit count, and accepts only a returned count within the resized vector."
    source := "base/gmp.jl:205-290"
    status := .proven, prop := ``Gmp.GmpMpzObserversCorrect, thm := some ``Gmp.gmpMpzObserversCorrect },
  { id := "bignumscov-gmp-conversion-routing", juliaFile := "base/gmp.jl"
    juliaFns := ["widen", "signed", "BigInt", "Signed", "unsafe_trunc", "Float16", "Float32", "Float64", "promote_rule", "big"]
    statement := "Identity, machine-setter, float-integrality, IEEE overflow, promotion, and big-type branches route every input to the source-specified result or error."
    source := "base/gmp.jl:298-492"
    status := .proven, prop := ``Gmp.GmpConversionRoutingCorrect, thm := some ``Gmp.gmpConversionRoutingCorrect },
  { id := "bignumscov-gmp-arithmetic-routing", juliaFile := "base/gmp.jl"
    juliaFns := ["generated binary BigInt operators", "mixed C-long arithmetic", "unary - and ~", "<<", ">>", ">>>"]
    statement := "Generated exact arithmetic delegates to its MPZ operation, signed machine operands take the matching add/subtract branch, and zero shifts return the original object."
    source := "base/gmp.jl:494-574"
    status := .proven, prop := ``Gmp.GmpArithmeticRoutingCorrect, thm := some ``Gmp.gmpArithmeticRoutingCorrect },
  { id := "bignumscov-gmp-bit-query", juliaFile := "base/gmp.jl"
    juliaFns := ["trailing_zeros", "trailing_ones", "count_ones", "count_zeros", "count_ones_abs", "_bit_magnitude", "exponent", "top_set_bit", "cmp"]
    statement := "Bit scans reject GMP's -1 sentinel as documented, zero has zero absolute population count, exponent rejects zero, top_set_bit rejects negative inputs, and cmp normalization returns only -1, 0, or 1."
    source := "base/gmp.jl:576-635"
    status := .proven, prop := ``Gmp.GmpBitQueryCorrect, thm := some ``Gmp.gmpBitQueryCorrect },
  { id := "bignumscov-gmp-number-theory-routing", juliaFile := "base/gmp.jl"
    juliaFns := ["divrem", "^ aliases", "gcdx", "+ varargs", "sum", "prod", "_prod", "binomial(::BigInt,::Culong)"]
    statement := "Power aliases, gcdx's compatibility swap, sums, and both product branches preserve their mathematical results for every input."
    source := "base/gmp.jl:625-728"
    status := .proven, prop := ``Gmp.GmpNumberTheoryRoutingCorrect, thm := some ``Gmp.gmpNumberTheoryRoutingCorrect },
  { id := "bignumscov-gmp-comparison-sign", juliaFile := "base/gmp.jl"
    juliaFns := ["==", "<=", "<", "iszero", "isone", "isnegative", "ispositive", "signbit", "flipsign!", "flipsign", "sign", "show"]
    statement := "BigInt predicates use the sign of cmp or the limb count exactly, flipsign changes sign only for a negative second operand, and sign returns -1, 0, or 1."
    source := "base/gmp.jl:730-763"
    status := .proven, prop := ``Gmp.GmpComparisonAndSignCorrect, thm := some ``Gmp.gmpComparisonAndSignCorrect },
  { id := "bignumscov-gmp-checked-alias", juliaFile := "base/gmp.jl"
    juliaFns := ["ndigits0zpb", "_prevpow2", "_nextpow2", "checked_*", "*_with_overflow", "deepcopy_internal", "_hash_shl!"]
    statement := "Digit-count routing follows invalid/zero/power-of-two/logarithmic branches; exact checked aliases delegate unchanged and overflow tuples always report false."
    source := "base/gmp.jl:812-864"
    status := .proven, prop := ``Gmp.GmpCheckedAliasCorrect, thm := some ``Gmp.gmpCheckedAliasCorrect },
  { id := "bignumscov-gmp-limb-view", juliaFile := "base/gmp.jl"
    juliaFns := ["size(::UnsafeLimbView)", "getindex(::UnsafeLimbView)", "iterate(::UnsafeLimbView)", "length(::UnsafeLimbView)", "hash_integer"]
    statement := "UnsafeLimbView reports num_bytes, rejects indices outside 1:num_bytes, and terminates iteration immediately after that range."
    source := "base/gmp.jl:873-916"
    status := .proven, prop := ``Gmp.GmpLimbViewCorrect, thm := some ``Gmp.gmpLimbViewCorrect },
  { id := "bignumscov-gmp-rational-special", juliaFile := "base/gmp.jl"
    juliaFns := ["_MPQ", "sync_rational!", "Rational{BigInt}", "set!", "set_z!", "set_ui", "set_si", "add!", "sub!", "mul!", "div!", "generated Rational operators"]
    statement := "Rational{BigInt} construction and arithmetic follow every zero-denominator, zero-numerator, sign, finite-primitive, and DivideError branch."
    source := "base/gmp.jl:958-1115"
    status := .proven, prop := ``Gmp.GmpRationalSpecialValuesCorrect, thm := some ``Gmp.gmpRationalSpecialValuesCorrect },

  { id := "bignumscov-mpfr-setup-rounding", juliaFile := "base/mpfr.jl"
    juliaFns := ["version", "patches", "__init__", "convert rounding modes", "rounds_to_nearest", "rounds_away_from_zero", "tie_breaker_is_to_even"]
    statement := "MPFR setup calls both exponent setters, mode conversions accept exactly the five MPFR modes, and direction predicates follow sign and mode."
    source := "base/mpfr.jl:44-110"
    status := .proven, prop := ``Mpfr.MpfrSetupAndRoundingCorrect, thm := some ``Mpfr.mpfrSetupAndRoundingCorrect },
  { id := "bignumscov-mpfr-storage", juliaFile := "base/mpfr.jl"
    juliaFns := ["_BigFloat", "BigFloat(; precision)", "getproperty", "setproperty!", "unsafe_convert", "cconvert", "BigFloatData indexing", "rounding_raw", "setrounding"]
    statement := "BigFloat property access, permitted mutation, checked data indexing, pointer-routing wrappers, and scoped rounding selection follow the source branches for all inputs."
    source := "base/mpfr.jl:149-255"
    status := .proven, prop := ``Mpfr.MpfrStorageCorrect, thm := some ``Mpfr.mpfrStorageCorrect },
  { id := "bignumscov-mpfr-constructors", juliaFile := "base/mpfr.jl"
    juliaFns := ["widen", "BigFloat constructors", "_duplicate", "_opposite_round", "Rational", "AbstractFloat", "float", "unchecked casts", "round", "unsafe_trunc", "Bool", "BigInt"]
    statement := "BigFloat construction, copy precision, directed rational conversion, integer casts, range checks, Bool conversion, and constructor routing return the source-selected value or error."
    source := "base/mpfr.jl:299-493"
    status := .proven, prop := ``Mpfr.MpfrConstructorRoutingCorrect, thm := some ``Mpfr.mpfrConstructorRoutingCorrect },
  { id := "bignumscov-mpfr-ieee-routing", juliaFile := "base/mpfr.jl"
    juliaFns := ["to_ieee754", "Float16", "Float32", "Float64", "promote_rule", "big", "Rational{BigInt}"]
    statement := "BigFloat conversion to fixed IEEE formats selects finite, zero, infinity, omega, or NaN according to special-value, exponent, and rounding-direction branches."
    source := "base/mpfr.jl:494-571"
    status := .proven, prop := ``Mpfr.MpfrIeeeRoutingCorrect, thm := some ``Mpfr.mpfrIeeeRoutingCorrect },
  { id := "bignumscov-mpfr-arithmetic", juliaFile := "base/mpfr.jl"
    juliaFns := ["generated + - * /", "inv", "fma", "muladd", "div", "generated 3-5 argument operations", "unary -"]
    statement := "Allocating MPFR unary, binary, ternary, mixed-operand, and generated left-fold wrappers preserve primitive selection, argument order, and return value."
    source := "base/mpfr.jl:573-779"
    status := .proven, prop := ``Mpfr.MpfrArithmeticRoutingCorrect, thm := some ``Mpfr.mpfrArithmeticRoutingCorrect },
  { id := "bignumscov-mpfr-transcendentals", juliaFile := "base/mpfr.jl"
    juliaFns := ["sqrt", "^", "generated unary functions", "sincos", "ldexp", "factorial", "hypot", "log1p", "minmax", "_extrema_rf", "modf", "rem", "rem2pi", "sum", "trigonometric and degree functions"]
    statement := "MPFR mathematical wrappers preserve primitive arguments, return input NaNs, reject newly produced NaNs, take log1p's real-domain branch, and preserve minmax and sum ordering."
    source := "base/mpfr.jl:781-985"
    status := .proven, prop := ``Mpfr.MpfrTranscendentalRoutingCorrect, thm := some ``Mpfr.mpfrTranscendentalRoutingCorrect },
  { id := "bignumscov-mpfr-comparisons", juliaFile := "base/mpfr.jl"
    juliaFns := ["==", "<", "<=", "cmp", "signbit", "sign"]
    statement := "BigFloat comparisons follow the explicit NaN ordering and unordered numeric predicates, and sign preserves zeros and NaNs while returning unit sign otherwise."
    source := "base/mpfr.jl:990-1039"
    status := .proven, prop := ``Mpfr.MpfrComparisonCorrect, thm := some ``Mpfr.mpfrComparisonCorrect },
  { id := "bignumscov-mpfr-precision-classification", juliaFile := "base/mpfr.jl"
    juliaFns := ["precision", "_precision_with_base_2", "_convert_precision_from_base", "setprecision", "maxintfloat", "copysign", "exponent", "frexp", "significand", "isinteger", "round", "isinf", "isnan", "issubnormal", "isfinite", "iszero", "isone", "ispositive", "isnegative", "typemax", "typemin"]
    statement := "Precision validation rejects invalid bases and precisions, exponent rejects zero and nonfinite values, and BigFloat classification follows the three special exponent codes."
    source := "base/mpfr.jl:1041-1149"
    status := .proven, prop := ``Mpfr.MpfrPrecisionAndClassificationCorrect, thm := some ``Mpfr.mpfrPrecisionAndClassificationCorrect },
  { id := "bignumscov-nextfloat-typemin", juliaFile := "base/mpfr.jl"
    juliaFns := ["nextfloat!", "prevfloat!", "nextfloat", "prevfloat"]
    statement := "Every negative Int step count becomes nonnegative before nextfloat! or prevfloat! starts the opposite-direction loop."
    source := "nextfloat/prevfloat docstrings base/float.jl:848-869; base/mpfr.jl:1151-1168"
    status := .refuted, prop := ``Mpfr.BigFloatStepTerminates, thm := some ``Mpfr.bigFloatStepTerminates_refuted
    issue := "none found (queries: nextfloat typemin BigFloat; prevfloat typemin BigFloat; nextfloat! hang; PR nextfloat typemin BigFloat; PR prevfloat typemin BigFloat)"
    notes := "Both Julia 1.13.2 and master hang: abs(typemin(Int)) wraps, so nextfloat! and prevfloat! call each other forever." },
  { id := "bignumscov-mpfr-neighbor-derived", juliaFile := "base/mpfr.jl"
    juliaFns := ["nextfloat", "prevfloat", "eps", "floatmin", "floatmax"]
    statement := "For nonnegative counts, zero-step neighbor calls preserve identity, nonzero calls duplicate before mutation, and the three constants delegate to their documented one-step neighbor operation."
    source := "base/mpfr.jl:1167-1173"
    status := .proven, prop := ``Mpfr.MpfrNeighborDerivedCorrect, thm := some ``Mpfr.mpfrNeighborDerivedCorrect },
  { id := "bignumscov-scoped-setprecision-validation", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(::Function,::Type{BigFloat},::Integer; base)", "setprecision(::Function,::Integer; base)"]
    statement := "Callback-scoped BigFloat setprecision rejects invalid bases and precisions before running the callback, as its documented equivalent global-setter sequence does."
    source := "setprecision callback docstring base/mpfr.jl:1175-1183; validation base/mpfr.jl:1069-1073; scoped implementation base/mpfr.jl:1214-1219"
    status := .refuted, prop := ``Mpfr.ScopedPrecisionValidates, thm := some ``Mpfr.scopedPrecisionValidates_refuted
    issue := "none found (queries: setprecision BigFloat scoped validation; setprecision BigFloat DomainError; PR setprecision BigFloat scoped validation; PR setprecision BigFloat DomainError)"
    notes := "Both Julia 1.13.2 and master accept precision 0 and base 1 when the callback returns without allocating BigFloat." },
  { id := "bignumscov-mpfr-state-formatting", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision callback forms", "string_mpfr", "_prettify_bigfloat", "_string", "string", "print", "show", "get/set exponent range", "deepcopy_internal", "decompose", "lerpi", "flag functions"]
    statement := "Scoped precision restores the prior value, formatting selects fixed notation only for exponents -4 through 5, exponent setters check their status, decomposition follows special classes, and flag wrappers test nonzero."
    source := "base/mpfr.jl:1200-1332"
    status := .proven, prop := ``Mpfr.MpfrStateAndFormattingCorrect, thm := some ``Mpfr.mpfrStateAndFormattingCorrect },

  { id := "bignumscov-raw-count-index", juliaFile := "base/rawbigfloats.jl"
    juliaFns := ["elem_count", "word_length", "reversed_index", "split_bit_index", "get_elem words", "get_elem bits"]
    statement := "Raw BigFloat word and bit counts, zero-based ascending access, descending reversal, and out-of-range bit behavior follow the source formulas."
    source := "base/rawbigfloats.jl:5-24,66-81"
    status := .proven, prop := ``Raw.RawCountingAndIndexingCorrect, thm := some ``Raw.rawCountingAndIndexingCorrect },
  { id := "bignumscov-raw-tail", juliaFile := "base/rawbigfloats.jl"
    juliaFns := ["word_is_nonzero", "tail_is_nonzero words", "tail_is_nonzero word", "tail_is_nonzero bits"]
    statement := "Raw BigFloat tail predicates scan exactly the requested least-significant words and the quotient/remainder bit tail, returning false for a zero bit length."
    source := "base/rawbigfloats.jl:26-60"
    status := .proven, prop := ``Raw.RawTailCorrect, thm := some ``Raw.rawTailCorrect },
  { id := "bignumscov-raw-trunc-round", juliaFile := "base/rawbigfloats.jl"
    juliaFns := ["truncated", "BigFloatDataRoundingIncrementHelper", "FinalBit", "RoundBit", "StickyBit"]
    statement := "Truncation consumes descending significant bits with zero extension, and the rounding helper caches the final and round bits while computing sticky bits from the remaining tail."
    source := "base/rawbigfloats.jl:89-142"
    status := .proven, prop := ``Raw.RawTruncationAndRoundingCorrect, thm := some ``Raw.rawTruncationAndRoundingCorrect }
] ++ JuliaLean.BigNumsCov.MpfrFaithful.entries

end JuliaLean.BigNumsCov

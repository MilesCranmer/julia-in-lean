import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.BigNums.Int
import JuliaLean.BigNums.Float
import JuliaLean.BigNums.Rational
import JuliaLean.BigNums.Parse
import JuliaLean.BigNums.Proofs.Division
import JuliaLean.BigNums.Proofs.Modular
import JuliaLean.BigNums.Proofs.Convert
import JuliaLean.BigNums.Proofs.Hash
import JuliaLean.BigNums.Proofs.Roundtrip

/-!
`BigInt` and `BigFloat` (`base/gmp.jl`, `base/mpfr.jl`) at master `bbfa0ce4150`.
GMP and MPFR calls are exact primitives defined by their manuals; Julia's wrapper code is
mirrored line by line. See the module docstrings of `BigNums/Int.lean`, `BigNums/Float.lean`,
`BigNums/Rational.lean` and `BigNums/Parse.lean`.

Differential check against Julia master:
6,820 rows over BigInt `div`/`rem`/`mod`/`fld`/`cld`, `isqrt`, conversion to and `rem` into all
ten `BitInteger` types, `powermod`, `invmod`, `^`, `digits`, `parse`, `string(base, pad)`,
`BigFloat(::Rational, mode; precision)`, `cmp(::BigFloat, ::Float64)`, `round(Int64, ::BigFloat,
mode)` and `cmp(::Rational{BigInt}, ::Rational{BigInt})` all match, except one `mpq_cmp` call
on a zero denominator (`cmp(-3//1, -1//0)`), where GMP's behaviour is undefined and the model
leaves the result unspecified.
-/

namespace JuliaLean.BigNums

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "bignums-division-matches-int", juliaFile := "base/gmp.jl",
    juliaFns := ["div(::BigInt,::BigInt)", "rem(::BigInt,::BigInt)", "mod(::BigInt,::BigInt)", "fld(::BigInt,::BigInt)", "cld(::BigInt,::BigInt)"],
    statement := "div, rem, fld, cld and mod on BigInt agree with the same functions on every BitInteger type wherever the machine call does not overflow, including DivideError for a zero divisor.",
    source := "invariant: BigInt arithmetic is exact integer arithmetic; base/gmp.jl:495-514, base/div.jl, base/int.jl:331-351",
    status := .proven, prop := ``DivisionMatchesInt, thm := some ``divisionMatchesInt_proven },
  { id := "bignums-powermod-floored-mod", juliaFile := "base/gmp.jl",
    juliaFns := ["powermod(::BigInt,::BigInt,::BigInt)"],
    statement := "For p >= 0 and m != 0, powermod(x, p, m) == mod(x^p, m), with the sign of m.",
    source := "powermod docstring, base/intfuncs.jl:501-523; base/gmp.jl:669-672 comment",
    status := .proven, prop := ``PowermodFlooredMod, thm := some ``powermodFlooredMod_proven },
  { id := "bignums-invmod-postcondition", juliaFile := "base/gmp.jl",
    juliaFns := ["invmod(::BigInt,::BigInt)"],
    statement := "When invmod(x, y) returns z, mod(z*x, y) == mod(1, y) and div(z, y) == 0.",
    source := "invmod docstring, base/intfuncs.jl:289-294; postcondition comment base/gmp.jl:533",
    status := .proven, prop := ``InvmodPostcondition, thm := some ``invmodPostcondition_proven },
  { id := "bignums-to-int-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["(::Type{T})(::BigInt) where T<:BitInteger", "rem(::BigInt, ::Type{T})"],
    statement := "T(x::BigInt) returns x when it is representable in T and throws InexactError otherwise, for all ten BitInteger types.",
    source := "convert docstring, base/essentials.jl; base/gmp.jl:367-407",
    status := .proven, prop := ``ToIntExact, thm := some ``toIntExact_proven },
  { id := "bignums-hash-small", juliaFile := "base/gmp.jl",
    juliaFns := ["hash(::BigInt, ::UInt)", "hash(::Int64, ::UInt)", "hash(::UInt64, ::UInt)"],
    statement := "hash(big(x), h) == hash(x, h) for every Int64 and UInt64 x.",
    source := "isequal docstring, base/operators.jl:160-161: isequal(x,y) must imply hash(x) == hash(y); base/gmp.jl:917-955",
    status := .proven, prop := ``HashBigMatchesSmall, thm := some ``hashBigMatchesSmall_proven },
  { id := "bignums-hash-128", juliaFile := "base/gmp.jl",
    juliaFns := ["hash(::BigInt, ::UInt)", "hash(::Int128, ::UInt)", "hash(::UInt128, ::UInt)"],
    statement := "hash(big(x), h) == hash(x, h) for every Int128 and UInt128 x, through all branches of the BigInt hash (single limb, float-representable, byte hash).",
    source := "isequal docstring, base/operators.jl:160-161; base/gmp.jl:917-955, base/hashing.jl:200-246",
    status := .proven, prop := ``HashBigMatches128, thm := some ``hashBigMatches128_proven },
  { id := "bignums-pow-negative-exponent", juliaFile := "base/gmp.jl",
    juliaFns := ["^(::BigInt, ::Integer)", "bigint_pow"],
    statement := "For negative exponents, big(x)^p agrees with x^p on Int64: 1 for x == 1, +-1 for x == -1, DomainError otherwise.",
    source := "invariant: consistency with power_by_squaring, base/intfuncs.jl; base/gmp.jl:641-661",
    status := .proven, prop := ``PowNegativeMatchesInt, thm := some ``powNegativeMatchesInt_proven },
  { id := "bignums-string-parse-roundtrip", juliaFile := "base/gmp.jl",
    juliaFns := ["string(::BigInt; base, pad)", "parse(::Type{BigInt}, ::AbstractString; base)"],
    statement := "parse(BigInt, string(n; base, pad); base) == n for every BigInt n, base 2..62 and pad >= 1.",
    source := "invariant: string/parse round trip; base/gmp.jl:307-331,765-782",
    status := .proven, prop := ``StringParseRoundtrip, thm := some ``stringParseRoundtrip_proven },
  { id := "bignums-isqrt-negative", juliaFile := "base/gmp.jl",
    juliaFns := ["isqrt(::BigInt)"],
    statement := "isqrt(n) is the floor square root for n >= 0 and throws DomainError for n < 0, as for machine integers.",
    source := "isqrt docstring, base/intfuncs.jl:1283-1293",
    status := .refuted, prop := ``IsqrtSpec, thm := some ``isqrtSpec_refuted,
    issue := "none found (queries: isqrt BigInt; isqrt negative; isqrt; mpz_sqrt; isqrt DivideError); related #4884",
    notes := "isqrt(big(-4)) throws DivideError (GMP SQRT_OF_NEGATIVE via SIGFPE); isqrt(-4) throws DomainError. Same on 1.13.2 and master." },
  { id := "bignums-powermod-noninvertible", juliaFile := "base/gmp.jl",
    juliaFns := ["powermod(::BigInt,::BigInt,::BigInt)", "powermod(::Integer,::Integer,::BigInt)"],
    statement := "powermod on BigInt agrees with powermod on Int64 for all Int64 arguments: the same value or the same exception type.",
    source := "invariant: consistency between integer types; invmod docstring base/intfuncs.jl:289-294",
    status := .refuted, prop := ``PowermodMatchesInt, thm := some ``powermodMatchesInt_refuted,
    issue := "none found (queries: powermod; powermod BigInt; powermod DivideError; powermod BigInt negative; invmod BigInt); related #15350",
    notes := "powermod(big(2), -1, big(4)) throws DivideError from mpz_powm; powermod(2, -1, 4) throws DomainError from invmod. Same on 1.13.2 and master." },
  { id := "bignums-digits-unsigned-negative", juliaFile := "base/gmp.jl",
    juliaFns := ["digits!(::AbstractVector{T}, ::BigInt)", "digits(::Type{T}, ::BigInt)"],
    statement := "digits(T, n; base) on BigInt agrees with digits(T, n; base) on Int64 for every element type and base 2..62: the same digits or the same exception type.",
    source := "digits docstring, base/intfuncs.jl:1170-1211",
    status := .refuted, prop := ``DigitsMatchesInt, thm := some ``digitsMatchesInt_refuted,
    issue := "none found (queries: digits BigInt; digits! BigInt; digits BigInt unsigned; digits!; mpz_export digits)",
    notes := "digits(UInt8, big(-7)) == UInt8[0xf9] while digits(UInt8, -7) throws InexactError. Same on 1.13.2 and master." },
  { id := "bignums-digits-view-pow2-base", juliaFile := "base/gmp.jl",
    juliaFns := ["digits!(::AbstractVector{T}, ::BigInt)", "Base.GMP.MPZ.export!"],
    statement := "digits!(a, n; base) with a power-of-two base above 62 fills a with its length(a) least significant digits for every output vector, resizable or not.",
    source := "digits! docstring, base/intfuncs.jl:1223-1228",
    status := .refuted, prop := ``DigitsBangFillsLow, thm := some ``digitsBangFillsLow_refuted,
    issue := "none found (queries: digits! BigInt; digits!; digits! resize; mpz_export digits; digits BigInt)",
    notes := "digits!(view(zeros(Int, 10), 1:3), big(2)^62 + 5; base=128) throws MethodError (resize! on a SubArray). Same on 1.13.2 and master." },
  { id := "bignums-tryparse-nul", juliaFile := "base/mpfr.jl",
    juliaFns := ["tryparse(::Type{BigFloat}, ::AbstractString)"],
    statement := "tryparse(BigFloat, s) returns a value or nothing and never throws.",
    source := "tryparse docstring, base/parse.jl:241-246",
    status := .refuted, prop := ``TryparseBigFloatNoThrow, thm := some ``tryparseBigFloatNoThrow_refuted,
    issue := "none found (queries: tryparse BigFloat; BigFloat embedded NUL; parse BigFloat; BigFloat parse); related #16499",
    notes := "tryparse(BigFloat, \"1\\0\") throws ArgumentError from the Cstring conversion; tryparse(Float64, \"1\\0\") === nothing. Same on 1.13.2 and master." },
  { id := "bignums-cmp-signed-zero", juliaFile := "base/mpfr.jl",
    juliaFns := ["cmp(::BigFloat, ::CdoubleMax)", "cmp(::BigFloat, ::Integer)"],
    statement := "cmp(x::BigFloat, y::Float64) follows the total order implemented by isless.",
    source := "cmp docstring, base/operators.jl:508-511",
    status := .refuted, prop := ``CmpBigFloatIsless, thm := some ``cmpBigFloatIsless_refuted,
    issue := "none found (queries: BigFloat cmp; BigFloat -0.0; BigFloat signed zero; cmp signed zero); related promotion-cmp-rational-signed-zero",
    notes := "cmp(big(-0.0), 0.0) == 0 and cmp(big(-0.0), 0) == 0 while isless(big(-0.0), 0.0) is true and cmp(-0.0, 0.0) == -1. Same on 1.13.2 and master." },
  { id := "bignums-bigfloat-rational-rounding", juliaFile := "base/mpfr.jl",
    juliaFns := ["BigFloat(::Rational, ::RoundingMode)"],
    statement := "BigFloat(q, r; precision = p) is q correctly rounded to p bits in direction r.",
    source := "BigFloat docstring, base/mpfr.jl:258-263",
    status := .refuted, prop := ``BigFloatOfRationalRounded, thm := some ``bigFloatOfRationalRounded_refuted,
    issue := "related #49749 (open PR, correctly rounded floats from rationals); no issue found (queries: BigFloat Rational rounding; BigFloat rational precision; BigFloat Rational)",
    notes := "BigFloat(1//5; precision=2) == 0.25 (nearest 0.1875); BigFloat(1//5, RoundToZero; precision=2) == 0.25 > 1//5. Same on 1.13.2 and master." },
  { id := "bignums-round-ties-away", juliaFile := "base/mpfr.jl",
    juliaFns := ["round(::Type{T}, ::BigFloat, ::RoundingMode)"],
    statement := "round(Int64, x::BigFloat, r) rounds x in direction r for every RoundingMode, throwing InexactError only when the result does not fit.",
    source := "round docstring, base/rounding.jl:331-350",
    status := .refuted, prop := ``RoundBigFloatAllModes, thm := some ``roundBigFloatAllModes_refuted,
    issue := "none found (queries: round BigFloat RoundNearestTiesAway; RoundNearestTiesAway BigFloat; round BigFloat; round BigFloat Int MethodError)",
    notes := "round(Int, big(2.5), RoundNearestTiesAway) throws MethodError (no convert to MPFRRoundingMode); round(Int, 2.5, RoundNearestTiesAway) == 3. Same on 1.13.2 and master." },
  { id := "bignums-rational-cmp-range", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp(::Rational{BigInt}, ::Rational{BigInt})"],
    statement := "cmp on finite Rational{BigInt} values returns -1, 0 or 1.",
    source := "cmp docstring, base/operators.jl:508-511",
    status := .refuted, prop := ``RationalCmpUnit, thm := some ``rationalCmpUnit_refuted,
    issue := "none found (queries: mpq_cmp; cmp Rational BigInt; Rational{BigInt} cmp; cmp returns; MPQ)",
    notes := "cmp(big(0)//1, big(2)^200//1) == -4 (GMP's mpq_cmp returns -num2_size). Same on 1.13.2 and master." },
  { id := "bignums-rational-cmp-infinite", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp(::Rational{BigInt}, ::Rational{BigInt})"],
    statement := "cmp on Rational{BigInt} values, infinite ones included, is a defined computation whose sign is the order of the values.",
    source := "cmp docstring, base/operators.jl:508-511; GMP manual: mpq functions require canonical operands",
    status := .refuted, prop := ``RationalCmpIsless, thm := some ``rationalCmpIsless_refuted,
    issue := "none found (queries: mpq_cmp; cmp Rational BigInt; Rational{BigInt} cmp; Rational BigInt infinity; MPQ)",
    notes := "cmp(big(1)//0, big(1)//2) == -1 on both versions; mpq_cmp reads the zero-size denominator at index -1. Same on 1.13.2 and master." },
  { id := "bignums-parse-bigint-sign", juliaFile := "base/gmp.jl",
    juliaFns := ["tryparse_internal(::Type{BigInt}, ...)", "parse(::Type{BigInt}, ::AbstractString)"],
    statement := "parse(BigInt, s) accepts at most one sign, as Julia's integer grammar does (checked on strings without whitespace).",
    source := "parse docstring, base/parse.jl:6-30; parseint_preamble base/parse.jl:96-121",
    status := .refuted, prop := ``ParseBigIntMatchesInt, thm := some ``parseBigIntMatchesInt_refuted,
    issue := "none found (queries: parse BigInt; BigInt parse minus sign; parse BigInt double minus; BigInt parse sign); related #44570",
    notes := "parse(BigInt, \"--5\") == 5, parse(BigInt, \"+-5\") == -5, parse(BigInt, \"-0x-5\") == 5; parse(Int, ·) throws. Same on 1.13.2 and master." },
  { id := "bignums-parse-bigint-whitespace", juliaFile := "base/gmp.jl",
    juliaFns := ["tryparse_internal(::Type{BigInt}, ...)", "parse(::Type{BigInt}, ::AbstractString)"],
    statement := "parse(BigInt, s) rejects whitespace between digits, as parse(Int, s) does (checked on strings without signs).",
    source := "parse docstring, base/parse.jl:6-30; base/parse.jl:126-160",
    status := .refuted, prop := ``ParseBigIntNoInteriorSpace, thm := some ``parseBigIntNoInteriorSpace_refuted,
    issue := "#44570",
    notes := "parse(BigInt, \"100 10\") == 10010. Duplicate of open issue #44570. Same on 1.13.2 and master." },
  { id := "bignums-rational-nan", juliaFile := "base/mpfr.jl",
    juliaFns := ["Rational{BigInt}(::AbstractFloat)"],
    statement := "Rational{BigInt}(NaN) throws InexactError, as Rational{T}(NaN) does for machine T.",
    source := "convert docstring, base/essentials.jl; consistency with base/rational.jl",
    status := .refuted, prop := ``RationalOfNaNInexact, thm := some ``rationalOfNaNInexact_refuted,
    issue := "none found (queries: Rational NaN InexactError; Rational(NaN); Rational BigInt infinity; BigFloat Rational)",
    notes := "Rational{BigInt}(NaN) throws ArgumentError \"invalid rational: zero(BigInt)//zero(BigInt)\". Same on 1.13.2 and master." },
  { id := "bignums-string-base-error", juliaFile := "base/gmp.jl",
    juliaFns := ["string(::BigInt; base, pad)"],
    statement := "string(n; base, pad) on BigInt agrees with string(n; base, pad) on Int64: the same text or the same exception type.",
    source := "invariant: consistency between integer types; base/intfuncs.jl:1047-1119",
    status := .refuted, prop := ``StringBigIntMatchesInt, thm := some ``stringBigIntMatchesInt_refuted,
    issue := "none found (queries: BigInt string base; string BigInt base error; digits BigInt)",
    notes := "string(big(7); base=63) throws ArgumentError; string(7; base=63) throws DomainError. Same on 1.13.2 and master." }
]

end JuliaLean.BigNums

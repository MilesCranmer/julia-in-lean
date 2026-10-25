import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Promotion.Props
import JuliaLean.Promotion.PromoteType
import JuliaLean.Promotion.Float16
import JuliaLean.Promotion.CompareProofs

/-!
Mixed-type numeric comparison, conversion, promotion and hashing at master `bbfa0ce4150`.

The model was differential-checked against Julia over a corpus of 690 float bit patterns
(Float16/Float32/Float64 boundaries near 2^k for k up to 128, subnormals, signed zeros,
NaNs), 617 integers of all ten types and 706 rationals of all ten component types:
20,671 result rows (every mixed `==`/`<`/`<=`/`isequal`/`isless`/`cmp` between floats and
integers and between floats and rationals, float/integer conversions, `trunc`, `Ti(x)`,
`Float64(::Rational)`, `Rational{T}(::Float64)`, and hash-equality classes) plus 6,170
integer-pair rows. All rows match master; release 1.13.2 differs only in six
`Rational{T}(±2^(bits-1))`/`Rational{T}(2^bits)` rows, where master's `rationalize`
returns `typemax(T)//1` (PR #61297).
-/

namespace JuliaLean.Promotion

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "promotion-int-compare-exact", juliaFile := "base/int.jl",
    juliaFns := ["==(::BitInteger,::BitInteger)", "<(::BitSigned,::BitUnsigned)", "<=(::BitUnsigned,::BitSigned)"],
    statement := "==, < and <= between any two BitInteger types, including mixed signedness and Int128/UInt128, compare the mathematical values.",
    source := "invariant; base/int.jl:577-589 and base/promotion.jl:516-518",
    status := .proven, prop := ``IntCompareExact, thm := some ``intCompareExact_proven },
  { id := "promotion-mixed-compare-small", juliaFile := "base/float.jl",
    juliaFns := ["==(::IEEEFloat,::BitInteger)", "<(::IEEEFloat,::BitInteger)", "<=(::BitInteger,::IEEEFloat)"],
    statement := "==, < and <= between Float16/Float32/Float64 and every integer type of at most 32 bits, in both argument orders, compare the mathematical values; NaN compares false.",
    source := "invariant of exact mixed comparison; base/float.jl:678-690, base/promotion.jl:516-518",
    status := .proven, prop := ``MixedCompareSmall, thm := some ``mixedCompareSmall_proven,
    notes := "64- and 128-bit integer types (the exact methods at base/float.jl:649-676 and the Float16 methods through Float64) are differential-checked only." },
  { id := "promotion-mixed-isless-total-small", juliaFile := "base/operators.jl",
    juliaFns := ["isless(::AbstractFloat,::Real)", "isless(::Real,::AbstractFloat)", "isequal(::AbstractFloat,::Real)"],
    statement := "For every IEEE float x and integer y of at most 32 bits, exactly one of isless(x,y), isless(y,x), isequal(x,y) holds, including NaN and signed zeros.",
    source := "isless docstring, base/operators.jl:206-214",
    status := .proven, prop := ``MixedIslessTotalSmall, thm := some ``mixedIslessTotalSmall_proven },
  { id := "promotion-promote-type-table", juliaFile := "base/promotion.jl",
    juliaFns := ["promote_type", "promote_rule"],
    statement := "promote_type over Bool, the ten BitInteger types and the three IEEE float types gives the documented promotion: wider integer with unsigned winning ties, the float for float/integer pairs, the wider float.",
    source := "manual: Conversion and Promotion; base/int.jl:809-822, base/float.jl:243-263,477-479, base/bool.jl:6",
    status := .proven, prop := ``PromoteTypeTable, thm := some ``promoteTypeTable_proven },
  { id := "promotion-float16-to-int-exact", juliaFile := "base/float.jl",
    juliaFns := ["(::Type{<:BitInteger})(::Float16)"],
    statement := "For every Float16 x and every BitInteger type Ti, Ti(x) returns the exact value when x is an integer representable in Ti and throws InexactError otherwise.",
    source := "convert docstring, base/essentials.jl:428-430; base/float.jl:881-931",
    status := .proven, prop := ``F16.Float16ToIntExact, thm := some ``F16.float16ToIntExact_proven },
  { id := "promotion-float16-trunc-exact", juliaFile := "base/float.jl",
    juliaFns := ["trunc(::Type{<:BitInteger}, ::Float16)"],
    statement := "For every Float16 x and every BitInteger type Ti, trunc(Ti, x) returns the truncated value when it is representable and throws InexactError otherwise.",
    source := "trunc docstring, base/rounding.jl:423-424; base/float.jl:881-931",
    status := .proven, prop := ``F16.Float16TruncExact, thm := some ``F16.float16TruncExact_proven },
  { id := "promotion-float16-hash-consistent", juliaFile := "base/hashing.jl",
    juliaFns := ["hash(::Float16)", "hash(::Float64)", "hash(::Int64)"],
    statement := "For every Float16 x, hash(x) == hash(Float64(x)), and hash(x) == hash(Int64(x)) whenever isequal(x, Int64(x)).",
    source := "isequal docstring, base/operators.jl:160-161: isequal(x,y) must imply hash(x) == hash(y)",
    status := .proven, prop := ``F16.Float16HashConsistent, thm := some ``F16.float16HashConsistent_proven },
  { id := "promotion-cmp-rational-signed-zero", juliaFile := "base/rational.jl",
    juliaFns := ["cmp(::AbstractFloat,::Rational)", "cmp(::Rational,::AbstractFloat)"],
    statement := "cmp between a float and a normalized Rational follows the isless total order.",
    source := "cmp docstring, base/operators.jl:508-511: uses the total order implemented by isless",
    status := .refuted, prop := ``CmpRationalFloatIsless, thm := some ``cmpRationalFloatIsless_refuted,
    issue := "none found (queries: cmp rational float; cmp -0.0; cmp signed zero; cmp isless inconsistent; cmp Rational; cmp zero; cmp NaN Rational; cmp float; Rational -0.0; isless rational float)",
    notes := "cmp(-0.0, 0//1) == 0 and cmp(0//1, -0.0) == 0 while isless(-0.0, 0//1) is true; cmp(-0.0, 0) == -1. Same on 1.13.2 and master." },
  { id := "promotion-rational-from-float-exact", juliaFile := "base/rational.jl",
    juliaFns := ["Rational{T}(::AbstractFloat)"],
    statement := "Rational{T}(x) for finite float x returns only a rational exactly equal to x.",
    source := "invariant of exact conversion; convert docstring base/essentials.jl:428-430",
    status := .refuted, prop := ``RationalOfFloatExact, thm := some ``rationalOfFloatExact_refuted,
    issue := "related #63403 (open PR, master typemax regression only), #61297",
    notes := "Rational{Int8}(0.1) == 1//10 on both versions. SEMANTICS CANDIDATE: the check x == Float64(r) deliberately accepts approximations that round back to x. Master additionally returns typemax(T)//1 for Rational{Int32}(2f0^31), which 1.13.2 rejects." },
  { id := "promotion-rational-from-float-representable", juliaFile := "base/rational.jl",
    juliaFns := ["Rational{T}(::AbstractFloat)", "rationalize(::Type{T}, ::AbstractFloat)"],
    statement := "Rational{T}(x) succeeds with the exact value whenever finite x equals a normalized Rational{T}.",
    source := "invariant; Rational docstring base/rational.jl:3-7",
    status := .refuted, prop := ``RationalOfFloatRepresentable, thm := some ``rationalOfFloatRepresentable_refuted,
    issue := "related #49848, #49803, #63121 (subnormal Float16 part); none found for typemin (queries: rationalize; Rational InexactError; rationalize typemin; typemin Rational conversion)",
    notes := "Rational{Int8}(-128.0) throws InexactError on both versions; Rational{Int32}(nextfloat(Float16(0.0))) also throws." },
  { id := "promotion-float-from-rational-nearest", juliaFile := "base/rational.jl",
    juliaFns := ["Float64(::Rational)", "Float32(::Rational)", "Float16(::Rational)"],
    statement := "Float64(q) for a normalized finite Rational q is the nearest binary64 value, ties to even.",
    source := "convert docstring, base/essentials.jl:443-445: returns the closest value representable by T",
    status := .refuted, prop := ``RationalToFloatNearest, thm := some ``rationalToFloatNearest_refuted,
    issue := "#49749 (open PR, correctly rounded conversion); related #45213",
    notes := "Float64(9007199254740995//3) is one ulp above the nearest. SEMANTICS CANDIDATE: the manual documents isequal(float(a//b), a/b), i.e. the current double rounding." },
  { id := "promotion-trunc-rational-infinite-error", juliaFile := "base/rational.jl",
    juliaFns := ["trunc(::Type{<:Integer}, ::Rational)", "round(::Type{<:Integer}, ::Rational)"],
    statement := "trunc(T, x) throws InexactError for the infinite rationals ±1//0, whose truncation is not representable.",
    source := "trunc docstring, base/rounding.jl:423-424",
    status := .refuted, prop := ``TruncInfiniteInexact, thm := some ``truncInfiniteInexact_refuted,
    issue := "none found (queries: trunc Rational infinite; round Rational DivideError; DivideError rational; rational infinity round; rational infinite integer conversion; round Rational; trunc Rational)",
    notes := "trunc(Int, 1//0) throws DivideError; trunc(Int, Inf) throws InexactError. SEMANTICS CANDIDATE: IntArith's intarith-rational-infinite-rounding records DivideError as the modelled behaviour." }
]

end JuliaLean.Promotion

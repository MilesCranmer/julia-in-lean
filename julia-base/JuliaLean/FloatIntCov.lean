import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.FloatIntCov.Checked
import JuliaLean.FloatIntCov.Int
import JuliaLean.FloatIntCov.Div
import JuliaLean.FloatIntCov.Float
import JuliaLean.FloatIntCov.CheckedRows
import JuliaLean.FloatIntCov.IntRows
import JuliaLean.FloatIntCov.DivRows
import JuliaLean.FloatIntCov.FloatRows

namespace JuliaLean.FloatIntCov

open JuliaLean.Registry
open JuliaLean.FloatIntCov.Checked
open JuliaLean.FloatIntCov.Int
open JuliaLean.FloatIntCov.Div
open JuliaLean.FloatIntCov.Float

/-- Registry entries of this area. -/
def umbrellaEntries : List Entry := [
  { id := "floatintcov-checked-promoted-calls", juliaFile := "base/checked.jl"
    juliaFns := ["checked_add(::Integer,::Integer)", "checked_sub(::Integer,::Integer)",
      "checked_mul(::Integer,::Integer)", "checked_div(::Integer,::Integer)",
      "checked_rem(::Integer,::Integer)", "checked_fld(::Integer,::Integer)",
      "checked_mod(::Integer,::Integer)", "checked_cld(::Integer,::Integer)"]
    statement := "Every mixed-type checked operation promotes both operands in source order and then invokes its same-type checked operation."
    source := "base/checked.jl:25-33", status := .proven
    prop := ``PromotedCallsSourceOrder, thm := some ``promotedCallsSourceOrder },
  { id := "floatintcov-checked-abs-fallback", juliaFile := "base/checked.jl"
    juliaFns := ["checked_abs(::Integer fallback)"]
    statement := "Every integer type without a checked_abs implementation reaches the explicit no-operation error."
    source := "base/checked.jl:35-37", status := .proven
    prop := ``CheckedAbsFallbackErrors, thm := some ``checkedAbsFallbackErrors },
  { id := "floatintcov-checked-overflow-helpers", juliaFile := "base/checked.jl"
    juliaFns := ["throw_overflowerr_negation", "throw_overflowerr_binaryop"]
    statement := "Both overflow-reporting helpers throw OverflowError for every input."
    source := "base/checked.jl:92-93,156-157", status := .proven
    prop := ``OverflowHelpersThrow, thm := some ``overflowHelpersThrow },
  { id := "floatintcov-checked-bool", juliaFile := "base/checked.jl"
    juliaFns := ["checked_abs(::Bool)", "checked_add(::Bool)",
      "add_with_overflow(::Bool,::Bool)", "sub_with_overflow(::Bool,::Bool)",
      "mul_with_overflow(::Bool,::Bool)"]
    statement := "The Boolean special cases return their exact promoted integer results and never report overflow."
    source := "base/checked.jl:128,138,179,202,241", status := .proven
    prop := ``BoolSpecialCasesExact, thm := some ``boolSpecialCasesExact
    notes := "Master spells Bool add and multiply with explicit wrapping operators; release has the same promoted numerical results." },
  { id := "floatintcov-checked-overflow-methods", juliaFile := "base/checked.jl"
    juliaFns := ["add_with_overflow", "sub_with_overflow", "mul_with_overflow"]
    statement := "Every active overflow-reporting method delegates to the source-faithful intrinsic or 128-bit fallback model."
    source := "base/checked.jl:136-137,200-201,239-240,259-280", status := .proven
    prop := ``WithOverflowMethodsDelegate, thm := some ``withOverflowMethodsDelegate
    notes := "Master uses explicit wrapping operators in fallback bodies; active release and master results agree." },
  { id := "floatintcov-checked-fixed-arity", juliaFile := "base/checked.jl"
    juliaFns := ["checked_add(::Any)", "checked_add(3 to 8 arguments)",
      "checked_mul(::Any)", "checked_mul(3 to 8 arguments)"]
    statement := "Unary checked folds are identities; every 3-to-8 argument checked add or multiply evaluates left to right and stops at the first error."
    source := "base/checked.jl:177-192,297-310", status := .proven
    prop := ``FixedAritySourceOrder, thm := some ``fixedAritySourceOrder },
  { id := "floatintcov-checked-bool-power", juliaFile := "base/checked.jl"
    juliaFns := ["checked_power_by_squaring(::Bool,::Integer)"]
    statement := "Boolean checked power agrees with ordinary Boolean power for every exponent."
    source := "base/checked.jl:366-368", status := .proven
    prop := ``CheckedPowerBoolContract, thm := some ``checkedPowerBoolContract },
  { id := "floatintcov-checked-length", juliaFile := "base/checked.jl"
    juliaFns := ["checked_length"]
    statement := "The generic checked_length fallback returns exactly the underlying length call, including any error."
    source := "base/checked.jl:370-376", status := .proven
    prop := ``CheckedLengthDelegates, thm := some ``checkedLengthDelegates },
  { id := "floatintcov-int-signed-types", juliaFile := "base/int.jl"
    juliaFns := ["signed(::Type)"]
    statement := "signed maps each fixed-width integer type to the signed type of the same width and maps Bool to Int."
    source := "base/int.jl:61-80", status := .proven
    prop := ``SignedTypeSameWidth, thm := some ``signedTypeSameWidth },
  { id := "floatintcov-int-union-errors", juliaFile := "base/int.jl"
    juliaFns := ["signed(::Type{Union{}})", "rem/mod/unsafe_trunc(::Type{Union{}})", "typemin/typemax(::Type{Union{}})"]
    statement := "Every explicit Union{} target method throws its source MethodError."
    source := "base/int.jl:80,700-705,907-908", status := .proven
    prop := ``UnionTypeMethodsError, thm := some ``unionTypeMethodsError
    notes := "All six explicit Union{} methods are new in master." },
  { id := "floatintcov-int-primitives", juliaFile := "base/int.jl"
    juliaFns := ["<", "unary -", "-", "+", "*", "-%", "+%", "*%"]
    statement := "Primitive fixed-width comparison is mathematical and every arithmetic primitive wraps in its operand type."
    source := "base/int.jl:82-94", status := .proven
    prop := ``PrimitiveArithmeticBehavior, thm := some ``primitiveArithmeticBehavior
    notes := "The -%, +%, and *% aliases are new in master; the underlying primitive behavior matches the ordinary wrapping operators in release." },
  { id := "floatintcov-int-negate", juliaFile := "base/int.jl"
    juliaFns := ["negate", "negate(::Unsigned)"]
    statement := "negate applies wrapping unary minus; the unsigned method first performs the checked same-width signed conversion."
    source := "base/int.jl:96-97", status := .proven
    prop := ``NegateBehavior, thm := some ``negateBehavior },
  { id := "floatintcov-int-float-division", juliaFile := "base/int.jl"
    juliaFns := ["inv(::Integer)", "/(::Integer,::Integer)", "/(::BitInteger,::BitInteger)"]
    statement := "Fixed-width integer reciprocal and division convert operands to binary64 before floating-point division."
    source := "base/int.jl:100-103", status := .proven
    prop := ``IntegerFloatDivisionBehavior, thm := some ``integerFloatDivisionBehavior },
  { id := "floatintcov-int-mul-hi", juliaFile := "base/int.jl"
    juliaFns := ["mul_hi"]
    statement := "mul_hi returns the upper half of the exact fixed-width product for every operand pair."
    source := "base/int.jl:106-141", status := .proven
    prop := ``MulHiExact, thm := some ``mulHiExact
    notes := "Master makes Int128 intermediate subtraction explicitly wrapping; release has the same result." },
  { id := "floatintcov-int-parity-dispatch", juliaFile := "base/int.jl"
    juliaFns := ["isodd(::Number)", "isodd(::Real)", "iseven(::Number)", "iseven(::Real)"]
    statement := "Generic parity first requires a real integral value and then tests its remainder modulo two."
    source := "base/int.jl:143-181", status := .proven
    prop := ``ParityDispatchBehavior, thm := some ``parityDispatchBehavior },
  { id := "floatintcov-int-sign-predicates", juliaFile := "base/int.jl"
    juliaFns := ["signbit(::Integer)", "signbit(::Unsigned)", "isnegative(::Unsigned)"]
    statement := "Integer signbit tests negativity, and every unsigned value has false signbit and isnegative."
    source := "base/int.jl:183-186", status := .proven
    prop := ``SignPredicates, thm := some ``signPredicates },
  { id := "floatintcov-int-sign-operations", juliaFile := "base/int.jl"
    juliaFns := ["flipsign", "copysign", "abs"]
    statement := "Integer flipsign, copysign, and abs follow the source's fixed-width sign-bit operations."
    source := "base/int.jl:188-234", status := .proven
    prop := ``SignOperationBehavior, thm := some ``signOperationBehavior },
  { id := "floatintcov-int-division-methods", juliaFile := "base/int.jl"
    juliaFns := ["div", "rem", "divrem", "mod"]
    statement := "Mixed-signedness and same-type fixed-width division, remainder, divrem, and modulo follow the source magnitude and sign-restoration paths."
    source := "base/int.jl:275-358", status := .proven
    prop := ``IntegerDivisionMethodBehavior, thm := some ``integerDivisionMethodBehavior
    notes := "Master adds an explicit wrapping BitSigned mod method and wrapping mixed addition; release follows the same modular result path." },
  { id := "floatintcov-int-bitwise", juliaFile := "base/int.jl"
    juliaFns := ["~", "&", "|", "xor"]
    statement := "Bitwise not, and, or, and xor act pointwise on every bit in the fixed-width representation."
    source := "base/int.jl:236,360-433", status := .proven
    prop := ``BitwiseBehavior, thm := some ``bitwiseBehavior },
  { id := "floatintcov-int-bit-reversal", juliaFile := "base/int.jl"
    juliaFns := ["bswap", "bitreverse"]
    statement := "bswap reverses bytes and bitreverse reverses every bit of a fixed-width integer."
    source := "base/int.jl:435-459,1106-1134", status := .proven
    prop := ``ByteAndBitReverseBehavior, thm := some ``byteAndBitReverseBehavior },
  { id := "floatintcov-int-bit-counts", juliaFile := "base/int.jl"
    juliaFns := ["count_ones", "leading_zeros", "trailing_zeros", "count_zeros", "leading_ones", "trailing_ones", "top_set_bit"]
    statement := "Every bit-count operation counts the complete fixed-width representation, and top_set_bit is width minus leading zeros."
    source := "base/int.jl:461-569", status := .proven
    prop := ``BitCountBehavior, thm := some ``bitCountBehavior },
  { id := "floatintcov-int-extrema", juliaFile := "base/int.jl"
    juliaFns := ["max", "min", "minmax"]
    statement := "Mixed fixed-width min, max, and minmax choose by mathematical order and return the promoted result type."
    source := "base/int.jl:591-599", status := .proven
    prop := ``IntegerExtremaBehavior, thm := some ``integerExtremaBehavior
    notes := "These mixed BitInteger specializations are new in master." },
  { id := "floatintcov-int-shifts", juliaFile := "base/int.jl"
    juliaFns := [">>", "<<", ">>>"]
    statement := "Unsigned shift counts retain their direction; negative Int counts reverse it, with fixed-width saturation and wrapping."
    source := "base/int.jl:601-616", status := .proven
    prop := ``ShiftBehavior, thm := some ``shiftBehavior },
  { id := "floatintcov-int-bitrotate", juliaFile := "base/int.jl"
    juliaFns := ["bitrotate"]
    statement := "bitrotate rotates left by the count modulo the fixed bit width, including negative counts."
    source := "base/int.jl:636-665", status := .proven
    prop := ``BitrotateBehavior, thm := some ``bitrotateBehavior },
  { id := "floatintcov-int-type-remainder", juliaFile := "base/int.jl"
    juliaFns := ["rem(::Integer,::Type)", "mod(::Integer,::Type)", "unsafe_trunc(::Type,::Integer)"]
    statement := "Integer remainder-to-type, modulo-to-type, and unsafe_trunc reduce the source bit pattern to the target width; Bool keeps the low bit."
    source := "base/int.jl:618-705", status := .proven
    prop := ``TypeRemainderBehavior, thm := some ``typeRemainderBehavior
    notes := "Master adds explicit Union{} error methods; ordinary target types behave as in release." },
  { id := "floatintcov-int-string-macros", juliaFile := "base/int.jl"
    juliaFns := ["@int128_str", "@uint128_str", "@big_str"]
    statement := "Integer string macros parse at expansion time; big string parsing normalizes underscores and tries BigInt before BigFloat."
    source := "base/int.jl:707-804", status := .proven
    prop := ``StringMacroBehavior, thm := some ``stringMacroBehavior },
  { id := "floatintcov-int-promotion-rules", juliaFile := "base/int.jl"
    juliaFns := ["promote_rule"]
    statement := "Integer promotion chooses the wider width and uses unsigned when widths tie."
    source := "base/int.jl:806-822", status := .proven
    prop := ``PromotionRuleBehavior, thm := some ``promotionRuleBehavior },
  { id := "floatintcov-int-bounds", juliaFile := "base/int.jl"
    juliaFns := ["typemin", "typemax"]
    statement := "typemin and typemax return the exact lower and upper value of every fixed-width integer type."
    source := "base/int.jl:826-908", status := .proven
    prop := ``IntegerBoundsBehavior, thm := some ``integerBoundsBehavior
    notes := "Master adds explicit Union{} error methods; fixed-width bounds are unchanged." },
  { id := "floatintcov-int-widen", juliaFile := "base/int.jl"
    juliaFns := ["widen"]
    statement := "widen doubles each integer width through 128 bits and preserves signedness."
    source := "base/int.jl:911-918", status := .proven
    prop := ``WidenTypeBehavior, thm := some ``widenTypeBehavior },
  { id := "floatintcov-int-widemul", juliaFile := "base/int.jl"
    juliaFns := ["widemul"]
    statement := "Widening multiplication computes the exact product in the promoted widened fixed-width type."
    source := "base/int.jl:920-928", status := .proven
    prop := ``WidemulBehavior, thm := some ``widemulBehavior },
  { id := "floatintcov-int-128-primitives", juliaFile := "base/int.jl"
    juliaFns := ["*(::Int128,::Int128)", "div(::Int128,::Int128)", "rem(::Int128,::Int128)"]
    statement := "On the supported 64-bit build, Int128 and UInt128 multiplication wraps and division and remainder use the checked integer primitives."
    source := "base/int.jl:1082-1089", status := .proven
    prop := ``Int128PrimitiveBehavior, thm := some ``int128PrimitiveBehavior },
  { id := "floatintcov-int-promoted-binary", juliaFile := "base/int.jl"
    juliaFns := ["generic Integer +, -, *, &, |, xor, +%, -%, *%"]
    statement := "Generic unchecked integer binary operations reduce both operands to the promoted type before applying the same operation."
    source := "base/int.jl:1092-1099", status := .proven
    prop := ``PromotedBinaryBehavior, thm := some ``promotedBinaryBehavior
    notes := "Master extends the loop with +%, -%, and *%; the original six operators match release." },
  { id := "floatintcov-div-integer-dispatch", juliaFile := "base/div.jl"
    juliaFns := ["div", "rem", "fld", "cld", "fld1", "fldmod"]
    statement := "Integer quotient and remainder wrappers select the requested rounding mode; fld1 is cld and fldmod is rounded-down divrem."
    source := "base/div.jl:77,127-138,196,243,252,387,391-475", status := .proven
    prop := ``IntegerModeDispatch, thm := some ``integerModeDispatch
    notes := "fld1 and nearest ties-away/ties-up integer rem methods are new in master; common directed modes otherwise agree with release." },
  { id := "floatintcov-divrem-roundup-typemin", juliaFile := "base/div.jl"
    juliaFns := ["rem(::Integer,::Integer,RoundUp)", "divrem(::Integer,::Integer,RoundUp)"]
    statement := "divrem(x, y, RoundUp) equals (div(x, y, RoundUp), rem(x, y, RoundUp)) for every fixed-width integer pair where division succeeds."
    source := "base/div.jl:80-87,255-262 (divrem equivalence); base/div.jl:129,290-325"
    status := .refuted, prop := ``DivremProjectionConsistency
    thm := some ``divremProjectionConsistency_refuted
    issue := "duplicate PR #62283 (open); superseded by PR #62319 (open)"
    notes := "For Int8(-127), typemin(Int8), RoundUp: rem negates typemin and gets the wrapped divisor -128, returning -127; divrem reconstructs the exact remainder 1. Both 1.13.2 and master fail." },
  { id := "floatintcov-div-directed-divrem", juliaFile := "base/div.jl"
    juliaFns := ["divrem(::Integer,::Integer,RoundToZero/Down/Up)", "divrem(::Any,::Any,RoundFromZero)"]
    statement := "Directed integer divrem computes the quotient first and reconstructs the remainder in source order; RoundFromZero chooses by operand signs."
    source := "base/div.jl:273-325,375-377", status := .proven
    prop := ``IntegerDivremSourceOrder, thm := some ``integerDivremSourceOrder
    notes := "Master adds a same-type BitSigned method with explicit wrapping; its numerical results match the generic release path." },
  { id := "floatintcov-div-nearest-divrem", juliaFile := "base/div.jl"
    juliaFns := ["divrem(::Integer,::Integer,RoundNearest)", "divrem(::Integer,::Integer,RoundNearestTiesAway)", "divrem(::Integer,::Integer,RoundNearestTiesUp)"]
    statement := "Each nearest integer divrem mode uses its source branch for ties-to-even, ties-away, or ties-up."
    source := "base/div.jl:326-373", status := .proven
    prop := ``NearestDivremDispatch, thm := some ``nearestDivremDispatch },
  { id := "floatintcov-div-bool", juliaFile := "base/div.jl"
    juliaFns := ["div(::Bool,::Bool,::RoundingMode)"]
    statement := "Boolean division ignores the rounding mode and delegates to ordinary Boolean division."
    source := "base/div.jl:421-431", status := .proven
    prop := ``BoolDivisionIgnoresMode, thm := some ``boolDivisionIgnoresMode },
  { id := "floatintcov-div-float-modes", juliaFile := "base/div.jl"
    juliaFns := ["rem(::AbstractFloat,::AbstractFloat,::RoundingMode)", "div(::AbstractFloat,::AbstractFloat,::RoundingMode)"]
    statement := "Binary64 remainder dispatch follows every rounding branch, and rounded division subtracts rem/y from x/y before integral rounding."
    source := "base/div.jl:127-149,480", status := .proven
    prop := ``FloatModeDispatch, thm := some ``floatModeDispatch
    notes := "Release lacks the AbstractFloat ties-away and ties-up remainder method and uses (x-rem)/y, with Float16/32 widening specializations; master uses x/y-rem/y." },
  { id := "floatintcov-div-generic-routes", juliaFile := "base/div.jl"
    juliaFns := ["divrem(::Any,::Any,::RoundingMode)", "div(::Real,::Real,::RoundingMode)", "fld(::Real,::Real)", "cld(::Real,::Real)"]
    statement := "Generic divrem preserves the compatibility routes for ToZero and Down, while mixed Real division promotes before redispatch."
    source := "base/div.jl:276-286,432-456", status := .proven
    prop := ``GenericRoutesSourceOrder, thm := some ``genericRoutesSourceOrder },
  { id := "floatintcov-float-bit-traits", juliaFile := "base/float.jl"
    juliaFns := ["reinterpret", "sign_mask", "exponent_mask", "exponent_one", "exponent_half", "significand_mask", "mantissa", "significand_bits", "exponent_bits", "exponent_bias", "exponent_max", "exponent_raw_max", "exponent_min"]
    statement := "Every IEEE format trait and signed or unsigned reinterpretation agrees with its complete bit layout."
    source := "base/float.jl:99-169", status := .proven
    prop := ``FloatBitTraitBehavior, thm := some ``floatBitTraitBehavior
    notes := "Master consolidates the three exponent_min methods into one union method; values match release." },
  { id := "floatintcov-float-ieee-constructors", juliaFile := "base/float.jl"
    juliaFns := ["ieee754_representation"]
    statement := "Every IEEE representation helper packs sign, exponent, and significand fields at the format-defined offsets."
    source := "base/float.jl:171-223", status := .proven
    prop := ``IEEEConstructorBehavior, thm := some ``ieeeConstructorBehavior
    notes := "Master adds an explicit return to the general constructor; behavior matches release." },
  { id := "floatintcov-float-uabs", juliaFile := "base/float.jl"
    juliaFns := ["uabs(::Integer)", "uabs(::BitSigned)"]
    statement := "uabs returns ordinary absolute value when safe and the same-width unsigned magnitude for fixed signed integers."
    source := "base/float.jl:225-236", status := .proven
    prop := ``IntegerUabsBehavior, thm := some ``integerUabsBehavior },
  { id := "floatintcov-float-conversions", juliaFile := "base/float.jl"
    juliaFns := ["Float16", "Float32", "Float64", "AbstractFloat", "Bool(::Float16)", "promote_rule", "widen"]
    statement := "Fixed-width integer and IEEE-format conversions round to the target format; promotions retain the float type and widening advances to the next format."
    source := "base/float.jl:241-350,477-482", status := .proven
    prop := ``FloatConversionBehavior, thm := some ``floatConversionBehavior
    notes := "Master consolidates ten AbstractFloat integer methods into one union method; numerical behavior matches release." },
  { id := "floatintcov-float-dispatch", juliaFile := "base/float.jl"
    juliaFns := ["float(::Any)", "float(::Type{Number})", "float(::Type{AbstractFloat})"]
    statement := "Scalar float delegates to AbstractFloat conversion; type float converts zero; an AbstractFloat type is already its own float type."
    source := "base/float.jl:354-387", status := .proven
    prop := ``FloatDispatchBehavior, thm := some ``floatDispatchBehavior
    notes := "Master makes float(Union{}) return Union{} only at arity one and throws MethodError for extra arguments; release returned Union{} for every arity." },
  { id := "floatintcov-float-unsafe-trunc", juliaFile := "base/float.jl"
    juliaFns := ["unsafe_trunc"]
    statement := "For every IEEE input, unsafe_trunc returns the target-width reduction of truncation; the documented out-of-range result remains arbitrary."
    source := "base/float.jl:389-450", status := .proven
    prop := ``UnsafeTruncBehavior, thm := some ``unsafeTruncBehavior
    notes := "Master uses remainder conversion instead of checked Int conversion for the Float64 exponent field; representable results match release." },
  { id := "floatintcov-float-checked-integer", juliaFile := "base/float.jl"
    juliaFns := ["round(::Type{Integer},::IEEEFloat,RoundToZero)", "(::Type{<:Integer})(::IEEEFloat)"]
    statement := "Generated float-to-integer methods enforce their source bounds, integral-value check, and InexactError result."
    source := "base/float.jl:454-456,881-931", status := .proven
    prop := ``CheckedFloatIntegerDispatch, thm := some ``checkedFloatIntegerDispatch
    notes := "Master changes only how the target type name is obtained for InexactError; numerical behavior matches release." },
  { id := "floatintcov-float-round-direction", juliaFile := "base/float.jl"
    juliaFns := ["rounds_up", "_round_convert"]
    statement := "Directed conversion steps to the adjacent target float exactly when the first conversion rounded in the wrong direction."
    source := "base/float.jl:463-474", status := .proven
    prop := ``RoundDirectionBehavior, thm := some ``roundDirectionBehavior },
  { id := "floatintcov-float-primitives", juliaFile := "base/float.jl"
    juliaFns := ["-", "+", "*", "/", "muladd", "round(::IEEEFloat,::RoundingMode)"]
    statement := "IEEE arithmetic and integral rounding methods dispatch directly to their corresponding compiler primitives."
    source := "base/float.jl:458-492", status := .proven
    prop := ``FloatPrimitiveDispatch, thm := some ``floatPrimitiveDispatch },
  { id := "floatintcov-float-fields", juliaFile := "base/float.jl"
    juliaFns := ["unbiased_exponent", "explicit_mantissa_noinfnan"]
    statement := "Exponent and mantissa extraction read their IEEE bit fields."
    source := "base/float.jl:498-506", status := .proven
    prop := ``FloatFieldExtraction, thm := some ``floatFieldExtraction
    notes := "Master removes an overwritten zero initialization in _to_float; behavior matches release." },
  { id := "floatintcov-float-to-float-fields", juliaFile := "base/float.jl"
    juliaFns := ["_to_float"]
    statement := "_to_float shifts the mantissa by its leading-zero count, adjusts the exponent, and packs normal or subnormal fields."
    source := "base/float.jl:508-522", status := .proven
    prop := ``ToFloatFieldsBehavior, thm := some ``toFloatFieldsBehavior },
  { id := "floatintcov-float-remainder", juliaFile := "base/float.jl"
    juliaFns := ["rem_internal", "rem", "mod"]
    statement := "Finite nonzero IEEE remainder equals the exact truncating remainder; public rem and mod apply the documented exceptional and sign branches."
    source := "base/float.jl:524-612", status := .proven
    prop := ``FloatRemainderBehavior, thm := some ``floatRemainderBehavior },
  { id := "floatintcov-float-comparisons", juliaFile := "base/float.jl"
    juliaFns := ["==", "<", "<=", "isequal", "_fpint", "isless"]
    statement := "IEEE comparisons and total ordering follow ordered comparison, bit identity classes, and the sign-magnitude integer key."
    source := "base/float.jl:615-634", status := .proven
    prop := ``FloatComparisonBehavior, thm := some ``floatComparisonBehavior },
  { id := "floatintcov-float-mixed-comparisons", juliaFile := "base/float.jl"
    juliaFns := ["mixed IEEEFloat/BitInteger ==, <, <="]
    statement := "Every generated mixed float and fixed-width integer comparison follows its exact, Float64, Float32, or promotion route."
    source := "base/float.jl:636-687", status := .proven
    prop := ``MixedComparisonDispatch, thm := some ``mixedComparisonDispatch },
  { id := "floatintcov-float-classification", juliaFile := "base/float.jl"
    juliaFns := ["abs", "isnan", "isfinite", "isinf"]
    statement := "IEEE absolute value clears the sign bit, and NaN, finite, and infinity classification follows exponent and significand fields."
    source := "base/float.jl:692-717", status := .proven
    prop := ``FloatClassificationBehavior, thm := some ``floatClassificationBehavior },
  { id := "floatintcov-float-generic-classification", juliaFile := "base/float.jl"
    juliaFns := ["isnan(::Number)", "isfinite(::Real)", "isfinite(::Integer)", "isinf(::Real)"]
    statement := "Generic numeric classification uses false for NaN, the decompose denominator for finiteness, and the conjunction of non-NaN and nonfinite for infinity."
    source := "base/float.jl:702-716", status := .proven
    prop := ``GenericClassificationBehavior, thm := some ``genericClassificationBehavior },
  { id := "floatintcov-float-decompose", juliaFile := "base/float.jl"
    juliaFns := ["decompose(::Integer)", "decompose(::Float16)", "decompose(::Float32)", "decompose(::Float64)"]
    statement := "decompose returns an exact signed power-of-two representation and the documented special-value tuples."
    source := "base/float.jl:719-778", status := .proven
    prop := ``DecomposeBehavior, thm := some ``decomposeBehavior },
  { id := "floatintcov-float-precision", juliaFile := "base/float.jl"
    juliaFns := ["_precision_with_base_2", "_precision", "precision"]
    statement := "Binary precision is stored-significand width plus one; other bases use the source quotient and bases below two throw DomainError."
    source := "base/float.jl:781-807", status := .proven
    prop := ``PrecisionBehavior, thm := some ``precisionBehavior
    notes := "The explicit precision(Union{}) MethodError method is new in master." },
  { id := "floatintcov-float-next-prev", juliaFile := "base/float.jl"
    juliaFns := ["_nextfloat", "nextfloat", "prevfloat"]
    statement := "nextfloat and prevfloat step through sign-magnitude encodings, reverse direction for negative counts, preserve NaNs, and saturate at infinities."
    source := "base/float.jl:810-879", status := .proven
    prop := ``NextPrevFloatBehavior, thm := some ``nextPrevFloatBehavior },
  { id := "floatintcov-float-integer-predicates", juliaFile := "base/float.jl"
    juliaFns := ["issubnormal", "ispow2", "iseven", "isodd"]
    statement := "Subnormal, power-of-two, even, and odd predicates follow the IEEE fields and exact integral value."
    source := "base/float.jl:933-960", status := .proven
    prop := ``FloatIntegerPredicateBehavior, thm := some ``floatIntegerPredicateBehavior },
  { id := "floatintcov-float-limits", juliaFile := "base/float.jl"
    juliaFns := ["typemin", "typemax", "floatmin", "floatmax", "eps"]
    statement := "IEEE limits and machine epsilon have their format-defined bit patterns; value eps toggles the low bit and takes the rounded absolute difference."
    source := "base/float.jl:962-1050", status := .proven
    prop := ``FloatLimitBehavior, thm := some ``floatLimitBehavior
    notes := "Master adds Union{} error methods for eps, floatmin, and floatmax; ordinary IEEE values match release." },
  { id := "floatintcov-float-storage-traits", juliaFile := "base/float.jl"
    juliaFns := ["bswap", "uinttype", "inttype", "floattype"]
    statement := "Float byte swap reverses storage bytes and the float/integer trait functions preserve storage width."
    source := "base/float.jl:1132-1148", status := .proven
    prop := ``FloatStorageTraitBehavior, thm := some ``floatStorageTraitBehavior },
  { id := "floatintcov-float-collections", juliaFile := "base/float.jl"
    juliaFns := ["float(::AbstractArray)", "float(::StepRange)", "float(::UnitRange)", "float(::StepRangeLen)", "float(::LinRange)"]
    statement := "Floating arrays are returned unchanged, other concrete arrays convert elementwise, and range conversion preserves endpoints, step, length, and offset."
    source := "base/float.jl:1151-1181", status := .proven
    prop := ``FloatCollectionBehavior, thm := some ``floatCollectionBehavior }
]

def entries : List Entry := umbrellaEntries ++ CheckedRows.entries ++ IntRows.entries ++ DivRows.entries ++ FloatRows.entries

end JuliaLean.FloatIntCov

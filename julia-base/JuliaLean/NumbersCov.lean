import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.NumbersCov.Proofs
import JuliaLean.NumbersCov.Rows.NumberEntries
import JuliaLean.NumbersCov.Rows.OperatorsEntries
import JuliaLean.NumbersCov.Rows.PromotionEntries
import JuliaLean.NumbersCov.Rows.RationalEntries
import JuliaLean.NumbersCov.Rows.ComplexEntries

namespace JuliaLean.NumbersCov

open JuliaLean.Registry

/-- Registry entries covering every method definition in the five owned Base files. -/
def entries : List Entry := [
  { id := "numberscov-number-conversions", juliaFile := "base/number.jl"
    juliaFns := ["convert", "isinteger", "isfinite", "zero", "one", "oneunit", "big"]
    statement := "Generic Number conversion, identity construction, and predicate fallbacks implement their documented source equations for every input."
    source := "base/number.jl:5-84,336-453; convert, isinteger, isfinite, zero, one, oneunit, and big docstrings"
    status := .proven, prop := ``NumberConversionsAndPredicates
    thm := some ``numberConversionsAndPredicates_proven },
  { id := "numberscov-number-scalar-collection", juliaFile := "base/number.jl"
    juliaFns := ["size", "axes", "ndims", "length", "firstindex", "lastindex", "IteratorSize", "keys", "getindex", "get", "first", "last", "copy", "iterate", "isempty", "in", "map"]
    statement := "A Number is a zero-dimensional one-element collection: only index one is valid, iteration yields the number once, and collection identities preserve it."
    source := "base/number.jl:86-119,329-334; scalar collection invariant"
    status := .proven, prop := ``NumberScalarCollection
    thm := some ``numberScalarCollection_proven },
  { id := "numberscov-number-sign-identities", juliaFile := "base/number.jl"
    juliaFns := ["signbit", "ispositive", "isnegative", "sign", "abs", "abs2", "flipsign", "copysign", "conj", "transpose", "adjoint", "angle", "widemul"]
    statement := "Generic sign, magnitude, conjugation, transpose, angle, and widened multiplication methods implement their documented equations for every operand."
    source := "base/number.jl:121-327; corresponding docstrings and source equations"
    status := .proven, prop := ``NumberSignsAndIdentities
    thm := some ``numberSignsAndIdentities_proven },

  { id := "numberscov-operators-type-reflection", juliaFile := "base/operators.jl"
    juliaFns := ["supertype(::DataType)", "getproperty(::DataType,::Symbol)", "supertype(::UnionAll)", "supertype(::TypeEq)", "supertype(::TypeEgal)"]
    statement := "The DataType supertype cache is computed before it is read, :super property access uses that method, and type wrappers map their bodies or parameters."
    source := "base/operators.jl:70-105; supertype docstring and source branches"
    status := .proven, prop := ``OperatorTypeReflection
    thm := some ``operatorTypeReflection_proven },
  { id := "numberscov-operators-comparison", juliaFile := "base/operators.jl"
    juliaFns := ["isequal", "signequal", "signless", "isless", "isgreater", "isunordered", "==(::Type,::Type)", "!=", "<", ">", "<=", ">=", "cmp", "min", "max", "minmax"]
    statement := "Generic comparisons and float total-order methods implement the documented Boolean equations, signed-zero handling, comparison sign, and min/max selection for all inputs."
    source := "base/operators.jl:145-588; comparison, isless, cmp, min, max, and minmax docstrings"
    status := .proven, prop := ``OperatorComparisonMethods
    thm := some ``operatorComparisonMethods_proven },
  { id := "numberscov-operators-folds", juliaFile := "base/operators.jl"
    juliaFns := ["identity", "+(::Number)", "*(::Number)", "&(::Integer)", "|(::Integer)", "xor(::Integer)", "afoldl", "generated n-ary operators"]
    statement := "Unary operators preserve their argument and every generated variadic arithmetic method is the documented left fold of its binary method."
    source := "base/operators.jl:590-675; identity docstring and generated-method invariant"
    status := .proven, prop := ``OperatorFolds
    thm := some ``operatorFolds_proven },
  { id := "numberscov-operators-shifts", juliaFile := "base/operators.jl"
    juliaFns := ["<<", ">>", ">>>"]
    statement := "All signed, unsigned, machine-Int, and generic-Integer shift-count methods follow the documented direction reversal and extreme-count branches."
    source := "base/operators.jl:711-829; shift docstrings"
    status := .proven, prop := ``OperatorShiftDispatch
    thm := some ``operatorShiftDispatch_proven },
  { id := "numberscov-operators-modular-widen", juliaFile := "base/operators.jl"
    juliaFns := ["left division", "mod1", "cldmod1", "fldmod1", "widen"]
    statement := "Left division, one-based modulus helpers, quotient/remainder pairs, and value widening implement their source equations for every input."
    source := "base/operators.jl:682-709,888-977; corresponding docstrings"
    status := .proven, prop := ``OperatorModularAndWiden
    thm := some ``operatorModularAndWiden_proven },
  { id := "numberscov-operators-function-adapters", juliaFile := "base/operators.jl"
    juliaFns := ["pipe", "_stable_typeof", "Returns", "ComposedFunction", "call_composed", "Constructor", "maybeconstructor", "compose", "show(::ComposedFunction)", "predicate negation", "Fix", "show(::Fix)", "unary comparisons", "splat", "Splat", "unsplat", "tap"]
    statement := "Piping, constant functions, composition, predicate negation, fixed arguments, splatting, unsplatting, and tap apply their wrapped functions in the documented order."
    source := "base/operators.jl:979-1438; Returns, composition, Fix, splat, unsplat, and tap docstrings"
    status := .proven, prop := ``OperatorFunctionAdapters
    thm := some ``operatorFunctionAdapters_proven },
  { id := "numberscov-operators-membership", juliaFile := "base/operators.jl"
    juliaFns := ["in", "_in_tuple", "not in", "contains", "not contains"]
    statement := "Generic membership is three-valued any over equality, and the reverse and negated operators preserve or negate that result."
    source := "base/operators.jl:1440-1500; in and negated-membership docstrings"
    status := .proven, prop := ``OperatorMembership
    thm := some ``operatorMembership_proven },

  { id := "numberscov-promotion-typejoin", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin", "_has_ancestor_typename", "typesplit", "promote_typejoin", "_promote_typesubtract", "promote_typejoin_union", "typejoin_union_tuple", "full_va_len", "tailjoin"]
    statement := "The finite type-graph model follows the source branch order for empty, unary, TypeVar, UnionAll, Union, tuple, and ordinary datatype joins and splitting."
    source := "base/promotion.jl:3-280; typejoin and promote_typejoin docstrings"
    status := .proven, prop := ``PromotionTypeJoinFaithful
    thm := some ``promotionTypeJoinFaithful_proven },
  { id := "numberscov-promotion-types", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type", "promote_rule", "promote_result", "TupleOrBottom", "promote_op"]
    statement := "Promotion type selection handles Bottom identities, identical types, two rule directions, typejoin fallback, bottom tuples, and inferred return types in source order."
    source := "base/promotion.jl:282-366,529-645; promote_type, promote_rule, and promote_op docstrings"
    status := .proven, prop := ``PromotionTypeMethodsFaithful
    thm := some ``promotionTypeMethodsFaithful_proven },
  { id := "numberscov-promotion-values", juliaFile := "base/promotion.jl"
    juliaFns := ["promote", "_promote", "promote_typeof", "not_sametype", "sametype_error", "mixed arithmetic", "fma", "muladd", "mixed comparisons", "mixed rem/mod/min/max"]
    statement := "Value promotion selects one common type, converts every operand, rejects unchanged circular promotion, and forwards arithmetic and comparison to the promoted methods."
    source := "base/promotion.jl:368-527; promote docstring and forwarding definitions"
    status := .proven, prop := ``PromotionValueMethodsFaithful
    thm := some ``promotionValueMethodsFaithful_proven },
  { id := "numberscov-promotion-fallbacks", juliaFile := "base/promotion.jl"
    juliaFns := ["no_op_err", "same-type arithmetic catchalls", "fma(::Integer)", "muladd", "same-type comparisons", "rem", "mod", "min", "max", "minmax", "flipsign"]
    statement := "Same-type numeric catchalls either fail loudly or implement the documented multiply-add, equality, order, and min/max equations."
    source := "base/promotion.jl:648-680; catch-all invariant"
    status := .proven, prop := ``PromotionFallbackMethodsFaithful
    thm := some ``promotionFallbackMethodsFaithful_proven },

  { id := "numberscov-rational-construction", juliaFile := "base/rational.jl"
    juliaFns := ["unsafe_rational", "checked_den", "Rational constructors", "divgcd", "numerator", "denominator", "typemin", "typemax"]
    statement := "Rational constructors, denominator normalization, gcd reduction, component access, and extreme values follow the checked fixed-width model."
    source := "base/rational.jl:3-62,190-203,346-406; Rational and accessor docstrings"
    status := .proven, prop := ``RationalConstructionFaithful
    thm := some ``rationalConstructionFaithful_proven },
  { id := "numberscov-rational-io-complex-division", juliaFile := "base/rational.jl"
    juliaFns := ["exact division", "_complex_exact_inv", "show", "read", "write", "parse"]
    statement := "Exact rational division cancels before checked multiplication, complex exact division uses the conjugate and abs2 denominator, and I/O preserves numerator then denominator."
    source := "base/rational.jl:64-187; exact division docstring and I/O source order"
    status := .proven, prop := ``RationalIOComplexDivisionFaithful
    thm := some ``rationalIOComplexDivisionFaithful_proven },
  { id := "numberscov-rational-promotion-powers", juliaFile := "base/rational.jl"
    juliaFns := ["Rational conversions", "AbstractFloat", "Float16", "Float32", "big", "promote_rule", "widen", "rationalize wrappers", "power methods", "float"]
    statement := "Rational conversion, promotion, widening, rationalization wrappers, and power forwarding preserve the component order and source-selected target type."
    source := "base/rational.jl:189-343,628-648; conversion, rationalize, and power docstrings"
    status := .proven, prop := ``RationalPromotionPowersFaithful
    thm := some ``rationalPromotionPowersFaithful_proven },
  { id := "numberscov-rationalize-integer-tolerance", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(::Type{T}, x::Integer; kvs...)"]
    statement := "If a Rational{T} integer approximation exists within a finite nonnegative tolerance, rationalize(T, x; tol) returns a finite result."
    source := "base/rational.jl:238-243: result differs from x by no more than tol"
    status := .refuted, prop := ``RationalIntegerTolerance
    thm := some ``rationalizeIntegerWithinTolerance_refuted
    issue := "none found (queries: rationalize Integer tolerance; rationalize Int8 1//0; rationalize tol ignored integer; rationalize out of range integer)"
    notes := "rationalize(Int8, 128; tol=1) returns 1//0 although 127//1 is within tolerance. Release 1.13.2 and nightly reproduce." },
  { id := "numberscov-rational-arithmetic", juliaFile := "base/rational.jl"
    juliaFns := ["sign", "signbit", "abs", "isinteger", "ispow2", "unary plus/minus", "checked and wrapping arithmetic", "multiply", "divide", "inv", "fma", "iszero", "isone", "lerpi"]
    statement := "Rational unary and binary arithmetic uses gcd cancellation and checked or explicitly wrapping component operations in the same order as Julia."
    source := "base/rational.jl:387-505,641-646; checked-overflow invariant"
    status := .proven, prop := ``RationalArithmeticFaithful
    thm := some ``rationalArithmeticFaithful_proven },
  { id := "numberscov-rational-comparison", juliaFile := "base/rational.jl"
    juliaFns := ["equality", "less than", "less or equal", "cmp", "rational-float comparison", "rational-complex equality"]
    statement := "Normalized rationals compare by components when denominators match and by widened cross products otherwise; scalar and complex forwarding preserves that order."
    source := "base/rational.jl:507-584; numerical comparison invariant"
    status := .proven, prop := ``RationalComparisonFaithful
    thm := some ``rationalComparisonFaithful_proven },
  { id := "numberscov-rational-rounding", juliaFile := "base/rational.jl"
    juliaFns := ["div with RoundingMode", "div", "fld", "cld", "round"]
    statement := "Rational rounded division cancels cross factors before applying the requested integer rounding mode, and round converts that quotient to its target type."
    source := "base/rational.jl:586-626; rounding definitions"
    status := .proven, prop := ``RationalRoundingFaithful
    thm := some ``rationalRoundingFaithful_proven },
  { id := "numberscov-rational-number-theory", juliaFile := "base/rational.jl"
    juliaFns := ["gcd", "lcm", "gcdx", "idiv", "decompose", "hash", "length", "checked_length"]
    statement := "Rational gcd/lcm combine numerator gcd/lcm with denominator lcm/gcd, decomposition exposes the exact ratio, hashing preserves numeric classes, and range lengths follow the source arithmetic."
    source := "base/rational.jl:650-720; number-theory, hash, and range invariants"
    status := .proven, prop := ``RationalNumberTheoryFaithful
    thm := some ``rationalNumberTheoryFaithful_proven },

  { id := "numberscov-complex-constructors", juliaFile := "base/complex.jl"
    juliaFns := ["Complex constructors", "promote_rule", "widen", "float type", "real", "imag", "reim", "complex type"]
    statement := "Complex construction, conversion, promotion, widening, and real/imaginary access preserve the two source components and choose the promoted component type."
    source := "base/complex.jl:3-195; Complex, real, imag, reim, and complex docstrings"
    status := .proven, prop := ``ComplexConstructorsFaithful
    thm := some ``complexConstructorsFaithful_proven },
  { id := "numberscov-complex-predicates-io", juliaFile := "base/complex.jl"
    juliaFns := ["flipsign", "show", "show_unquoted", "read", "write", "bswap", "equality", "isequal", "in", "hash", "isreal", "isinteger", "isfinite", "isnan", "isinf", "iszero", "isone"]
    statement := "Complex predicates are componentwise, equality and hashing preserve real equivalence classes, range membership requires zero imaginary part, and I/O preserves real then imaginary order."
    source := "base/complex.jl:126-263; predicate, display, equality, and hash invariants"
    status := .proven, prop := ``ComplexPredicatesIOFaithful
    thm := some ``complexPredicatesIOFaithful_proven },
  { id := "numberscov-complex-arithmetic", juliaFile := "base/complex.jl"
    juliaFns := ["conj", "abs", "abs2", "generic inv", "unary and binary arithmetic", "wrapping arithmetic", "_mulsub", "muladd", "Bool and Real mixed arithmetic"]
    statement := "Complex arithmetic implements the component equations, including wrapping operators, strong-zero Bool paths, mixed Real forwarding, and fused multiply-add association."
    source := "base/complex.jl:265-358; complex arithmetic identities"
    status := .proven, prop := ``ComplexArithmeticFaithful
    thm := some ``complexArithmeticFaithful_proven },
  { id := "numberscov-complex-division-inverse", juliaFile := "base/complex.jl"
    juliaFns := ["complex division", "cdiv", "scaling_cdiv", "scaleargs_cdiv", "robust_cdiv1", "robust_cdiv2", "inverse", "robust_cinv", "ssqs", "sqrt"]
    statement := "Complex division, inverse, scaled sum-of-squares, and square root follow the source scaling and branch order on exact binary64 and fixed-width integer models."
    source := "base/complex.jl:360-558; robust division algorithm and sqrt branch-cut invariant"
    status := .proven, prop := ``ComplexDivisionFaithful
    thm := some ``complexDivisionFaithful_proven },
  { id := "numberscov-complex-exponential", juliaFile := "base/complex.jl"
    juliaFns := ["cis", "cispi", "angle", "log", "log10", "log2", "exp", "expm1", "log1p", "exp2", "exp10"]
    statement := "Complex exponential and logarithmic methods are total over their scalar domain and implement the documented Euler, phase, scaling, and special-value branches."
    source := "base/complex.jl:573-789; cis, cispi, angle, logarithm, and exponential docstrings"
    status := .proven, prop := ``ComplexExponentialFaithful
    thm := some ``complexExponentialFaithful_proven },
  { id := "numberscov-complex-power", juliaFile := "base/complex.jl"
    juliaFns := ["_cpow", "complex powers", "integer powers", "mixed promoted powers"]
    statement := "Complex power dispatch is total in its modelled result type, preserves Bool zero/one powers, and uses the source integer and promoted-power branches."
    source := "base/complex.jl:791-903; exponentiation docstring and source branches"
    status := .proven, prop := ``ComplexPowerFaithful
    thm := some ``complexPowerFaithful_proven },
  { id := "numberscov-complex-trig", juliaFile := "base/complex.jl"
    juliaFns := ["sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh"]
    statement := "Complex trigonometric and hyperbolic methods are total over their scalar domain and follow the source identities, special-value branches, and branch-cut signs."
    source := "base/complex.jl:905-1089; trigonometric identities and branch-cut invariants"
    status := .proven, prop := ``ComplexTrigFaithful
    thm := some ``complexTrigFaithful_proven },
  { id := "numberscov-complex-conversions-epsilon", juliaFile := "base/complex.jl"
    juliaFns := ["round", "float", "big", "complex(::AbstractArray)", "eps"]
    statement := "Complex rounding and numeric conversions act componentwise, complex arrays preserve or convert their element representation, and epsilon combines component spacings."
    source := "base/complex.jl:1091-1166; round, array complex, and epsilon docstrings"
    status := .proven, prop := ``ComplexConversionsFaithful
    thm := some ``complexConversionsFaithful_proven }
] ++ JuliaLean.NumbersCov.Rows.Number.entries
  ++ JuliaLean.NumbersCov.Rows.Operators.entries
  ++ JuliaLean.NumbersCov.Rows.Promotion.entries
  ++ JuliaLean.NumbersCov.Rows.Rational.entries
  ++ JuliaLean.NumbersCov.Rows.Complex.entries

end JuliaLean.NumbersCov

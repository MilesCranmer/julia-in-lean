import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.NumMisc.Model
import JuliaLean.NumMisc.Proofs
import JuliaLean.NumMisc.Coverage

namespace JuliaLean.NumMisc

open JuliaLean.Registry
open JuliaLean.NumMisc.Coverage

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "nummisc-float-nan-invalid-payload"
    juliaFile := "base/parsers/floats.jl"
    juliaFns := ["tryparse(::Type{Float64}, ::AbstractString)", "Base.Parsers.nanpayload"]
    statement := "Float parsing accepts nan(payload) exactly when payload is a complete unsigned decimal, hexadecimal, or octal integer."
    source := "base/parsers/Parsers.jl:66-71 (documented float grammar)"
    status := .refuted
    prop := ``FloatGrammarExact
    thm := some ``floatGrammarExact_refuted
    issue := "none found (queries: nan payload parse Float64; nan(foo); parsefloat nan payload; nanpayload invalid)"
    notes := "nan(foo), nan(_), and nan(0x) return NaN with payload zero on 1.13.2 and master." },
  { id := "nummisc-float-exact-integer-rounding"
    juliaFile := "base/parsers/floats.jl"
    juliaFns := ["Base.Parsers.fromdecimal"]
    statement := "Every nonnegative integer through 2^53 takes the exact Float64 decimal fast path and is returned unchanged."
    source := "base/parsers/floats.jl:143-151 (both factors exact, so one rounding gives the nearest float)"
    status := .proven
    prop := ``FloatExactIntegerRounding
    thm := some ``floatExactIntegerRounding_proven },
  { id := "nummisc-irrational-directed-rounding"
    juliaFile := "base/irrationals.jl"
    juliaFns := ["Float32(::AbstractIrrational, ::RoundingMode)", "Float64(::AbstractIrrational, ::RoundingMode)", "_irrational_to_float"]
    statement := "Rounding-mode conversion of every AbstractIrrational returns the requested rounding of its exact value."
    source := "base/irrationals.jl:8-12,101-106"
    status := .refuted
    prop := ``IrrationalRoundingCorrect
    thm := some ``irrationalRoundingCorrect_refuted
    issue := "none found (queries: AbstractIrrational rounding; Irrational RoundUp; _irrational_to_float; irrational correctly rounded)"
    notes := "A conforming irrational 1 + sqrt(2)*2^-1000 becomes 1 at the fixed 256-bit intermediate, so Float64(x, RoundUp) returns 1 instead of nextfloat(1). Same on 1.13.2 and master." },
  { id := "nummisc-irrational-separated-rounding"
    juliaFile := "base/irrationals.jl"
    juliaFns := ["_irrational_to_float"]
    statement := "The fixed 256-bit intermediate preserves directed rounding for near-one values whose side of 1 remains distinguishable at that precision."
    source := "base/irrationals.jl:101-104"
    status := .proven
    prop := ``IrrationalSeparatedRoundingCorrect
    thm := some ``irrationalSeparatedRoundingCorrect_proven },
  { id := "nummisc-fastmath-hypot-varargs"
    juliaFile := "base/fastmath.jl"
    juliaFns := ["@fastmath", "Base.FastMath.hypot_fast", "hypot(x...)"]
    statement := "The @fastmath rewrite of hypot preserves every public arity supported by hypot."
    source := "base/fastmath.jl:75,327,371-395; base/math.jl:688-731"
    status := .refuted
    prop := ``FastMathCoverage
    thm := some ``fastMathCoverage_refuted
    issue := "none found (queries: fastmath hypot; hypot_fast; @fastmath MethodError hypot)"
    notes := "@fastmath hypot(3.0, 4.0, 12.0) throws MethodError while hypot returns 13.0. Same on 1.13.2 and master." },
  { id := "nummisc-hyperbolic-symmetry"
    juliaFile := "base/special/hyperbolic.jl"
    juliaFns := ["sinh", "cosh", "tanh", "asinh"]
    statement := "sinh, tanh, and asinh are odd and cosh is even for every finite, zero, infinite, and NaN value class, preserving signed zero."
    source := "base/special/hyperbolic.jl:58-80,103-125,161-177,183-219"
    status := .proven
    prop := ``HyperbolicSymmetry
    thm := some ``hyperbolicSymmetry_proven },
  { id := "nummisc-tanh-float32-nonmonotone"
    juliaFile := "base/special/hyperbolic.jl"
    juliaFns := ["tanh(::Float32)", "tanh_kernel(::Float32)"]
    statement := "The Float32 small-polynomial branch of tanh is nondecreasing on ordered nonnegative inputs."
    source := "invariant; base/special/hyperbolic.jl:157-175"
    status := .refuted
    prop := ``TanhMonotone
    thm := some ``tanhMonotone_refuted
    issue := "none found (queries: tanh Float32 monotonic; tanh nonmonotonic; hyperbolic monotonic; tanh_kernel)"
    notes := "For adjacent inputs 0x3efbfa81 < 0x3efbfa82, tanh returns 0x3ee96e0c > 0x3ee96e0b. Same on 1.13.2 and master." },
  { id := "nummisc-hyperbolic-special-values"
    juliaFile := "base/special/hyperbolic.jl"
    juliaFns := ["acosh", "atanh"]
    statement := "atanh has odd signed-zero, unit, infinity, and NaN behavior; acosh maps one to +0, +Inf to +Inf, and NaN to NaN."
    source := "base/special/hyperbolic.jl:221-286"
    status := .proven
    prop := ``HyperbolicSpecialValues
    thm := some ``hyperbolicSpecialValues_proven },
  { id := "nummisc-views-documented-rewrite"
    juliaFile := "base/views.jl"
    juliaFns := ["@views", "Base._views", "Base.maybeview"]
    statement := "@views changes read-position bracket references to maybeview, leaves explicit getindex calls explicit, preserves assignment targets, and leaves non-expression atoms unchanged."
    source := "base/views.jl:233-303 (@views implementation and docstring)"
    status := .proven
    prop := ``ViewsDocumentedRewrite
    thm := some ``viewsDocumentedRewrite_proven },
  { id := "nummisc-pointer-ref-semantics"
    juliaFile := "base/refpointer.jl"
    juliaFns := ["Ref(::Ptr, i)", "Ref(::AbstractArray, i)", "cconvert(::Type{Ref{T}}, ::NTuple{N,T})"]
    statement := "Ref(ptr,i) uses (i-1)*sizeof(T), RefArray checks on dereference, and tuple conversion roots the complete tuple."
    source := "base/refpointer.jl:116-150,182-193"
    status := .proven
    prop := ``PointerRefSemantics
    thm := some ``pointerRefSemantics_proven },
  { id := "nummisc-coverage-parser-init"
    juliaFile := "base/parsers/floats.jl"
    juliaFns := ["mulsmall!", "div5!", "top128", "limb", "pow5table", "pow10range", "halfwayrange", "mul64", "packbits", "eisellemire", "exactpow10s", "frombits", "fromdecimal", "mulpow!"]
    statement := "Float-parser limb arithmetic, table ranges, packing, Eisel-Lemire route selection, exact-power handling, and power chunking preserve the source formulas and branch order."
    source := "base/parsers/floats.jl:15-165"
    status := .proven, prop := ``ParserInitBehavior, thm := some ``parserInitBehavior },
  { id := "nummisc-coverage-parser-scan"
    juliaFile := "base/parsers/floats.jl"
    juliaFns := ["cmpmidpoint", "scandigits", "scanexponent", "hexbits", "scanhex", "parsehex", "matchword", "isnanchar", "nanpayload", "parsespecial", "parsefloat", "parsevalue"]
    statement := "Decimal and hexadecimal scanning, exponent saturation, special-word matching, NaN payload acceptance, top-level float route selection, and parsevalue delegation follow the source checks in order."
    source := "base/parsers/floats.jl:171-425"
    status := .proven, prop := ``ParserScanBehavior, thm := some ``parserScanBehavior },
  { id := "nummisc-coverage-ryu-exp"
    juliaFile := "base/ryu/exp.jl"
    juliaFns := ["writeexp"]
    statement := "writeexp validates precision, emits signs and special values, rounds the exact binary value to the requested scientific precision with ties to even, trims zeros as requested, and emits the signed exponent."
    source := "base/ryu/exp.jl:1-241"
    status := .proven, prop := ``RyuExpBehavior, thm := some ``ryuExpBehavior },
  { id := "nummisc-coverage-ryu-fixed"
    juliaFile := "base/ryu/fixed.jl"
    juliaFns := ["writefixed"]
    statement := "writefixed validates precision, emits signs and special values, rounds the exact binary value to the requested fixed precision with ties to even, and applies decimal-point and trimming flags in source order."
    source := "base/ryu/fixed.jl:1-185"
    status := .proven, prop := ``RyuFixedBehavior, thm := some ``ryuFixedBehavior },
  { id := "nummisc-coverage-irrational-core"
    juliaFile := "base/irrationals.jl"
    juliaFns := ["typemin", "typemax", "promote_rule", "AbstractFloat", "Float16", "Complex", "irrational-to-rational helpers", "Rational", "_irrational_to_float", "float", "comparison methods", "rationalize", "cmp", "numeric predicates", "hash", "widen", "zero", "one", "sign", "arithmetic", "round"]
    statement := "Irrational promotion, conversion precision loops, Float conversion, exact identity and false fallbacks, comparisons, rationalization, predicates, and arithmetic forwarding preserve the source branches."
    source := "base/irrationals.jl:31-223"
    status := .proven, prop := ``IrrationalCoreBehavior, thm := some ``irrationalCoreBehavior },
  { id := "nummisc-coverage-irrational-macro"
    juliaFile := "base/irrationals.jl"
    juliaFns := ["show", "@irrational", "irrational", "generated BigFloat/Float methods", "big", "alignment", "inv"]
    statement := "Irrational display, macro-generated declarations and checks, BigFloat and Float method installation, alignment, big forwarding, and inv forwarding occur in source order."
    source := "base/irrationals.jl:34-42,264-311"
    status := .proven, prop := ``IrrationalMacroBehavior, thm := some ``irrationalMacroBehavior },
  { id := "nummisc-coverage-fastmath-rewrite"
    juliaFile := "base/fastmath.jl"
    juliaFns := ["make_fastmath", "@fastmath"]
    statement := "Fast-math rewriting preserves quoted expressions, recursively rewrites calls and operands, handles literal powers and simple assignments, and maps only registered operation names."
    source := "base/fastmath.jl:102-158"
    status := .proven, prop := ``FastRewriteBehavior, thm := some ``fastRewriteBehavior },
  { id := "nummisc-coverage-fastmath-scalar"
    juliaFile := "base/fastmath.jl"
    juliaFns := ["scalar fast arithmetic and comparisons", "fallback and promotion loops", "exp fast methods", "pow_fast", "sqrt_fast", "sincos_fast", "rem_fast", "hypot_fast"]
    statement := "Scalar fast operations, comparisons, false or true classification assumptions, promotion and fallback dispatch, n-ary folds, power selection, sincos conversion, remainder, and binary hypot follow their source definitions."
    source := "base/fastmath.jl:165-327"
    status := .proven, prop := ``ScalarCoverageBehavior, thm := some ``scalarCoverageBehavior },
  { id := "nummisc-coverage-fastmath-complex"
    juliaFile := "base/fastmath.jl"
    juliaFns := ["complex fast arithmetic", "complex transcendental fast methods", "unary and binary fallbacks", "maximum_fast", "minimum_fast", "maximum!_fast", "minimum!_fast"]
    statement := "Complex component formulas, transcendental forwarding, generic fallbacks, promotion, and reduction folds preserve the source formulas and argument order."
    source := "base/fastmath.jl:192-290,331-418"
    status := .proven, prop := ``ComplexCoverageBehavior, thm := some ``complexCoverageBehavior },
  { id := "nummisc-coverage-hyperbolic-forward"
    juliaFile := "base/special/hyperbolic.jl"
    juliaFns := ["threshold methods", "sinh_kernel", "sinh16_kernel", "sinh", "cosh_kernel", "cosh", "sech", "csch", "tanh_kernel", "tanh"]
    statement := "Forward hyperbolic kernels and Float16 forwarding select polynomial, direct exponential, split exponential, reciprocal, and saturation branches using the source thresholds and symmetries."
    source := "base/special/hyperbolic.jl:20-177"
    status := .proven, prop := ``HyperbolicForwardBehavior, thm := some ``hyperbolicForwardBehavior },
  { id := "nummisc-coverage-hyperbolic-inverse"
    juliaFile := "base/special/hyperbolic.jl"
    juliaFns := ["AH_LN2", "asinh", "acosh_domain_error", "acosh", "atanh_domain_error", "atanh"]
    statement := "Inverse hyperbolic methods handle NaN and domain checks first, then select tiny, below-half or below-two, medium, and large formulas in source order."
    source := "base/special/hyperbolic.jl:180-286"
    status := .proven, prop := ``HyperbolicInverseBehavior, thm := some ``hyperbolicInverseBehavior },
  { id := "nummisc-coverage-arraymath-arithmetic-reverse"
    juliaFile := "base/arraymath.jl"
    juliaFns := ["_broadcast_preserving_zero_d", "array arithmetic methods", "reverse", "_reverse", "reverse!", "_reverse!"]
    statement := "Array arithmetic selects same-rank map, reshaped map, or scalar-map routes after shape checks, and reverse normalizes dimensions, rejects invalid dimensions, swaps the computed half, and recurses on odd middle slices."
    source := "base/arraymath.jl:5-133"
    status := .proven, prop := ``ArrayArithmeticReverseBehavior, thm := some ``arrayArithmeticReverseBehavior },
  { id := "nummisc-coverage-arraymath-rotation"
    juliaFile := "base/arraymath.jl"
    juliaFns := ["rotl90", "rotr90", "rot180"]
    statement := "Matrix rotations allocate swapped or equal axes, map source indices to the source-defined reflected coordinates, and reduce integer rotation counts modulo four or two."
    source := "base/arraymath.jl:154-317"
    status := .proven, prop := ``ArrayRotationBehavior, thm := some ``arrayRotationBehavior },
  { id := "nummisc-coverage-views-boundaries"
    juliaFile := "base/views.jl"
    juliaFns := ["replace_ref_begin_end!", "replace_ref_begin_end_!", "escapes", "handle_refexpr!", "@view"]
    statement := "begin and end replacement uses firstindex and lastindex in the active reference context, preserves escape depth and quote context, and @view accepts only a reference result with optional binding setup."
    source := "base/views.jl:17-228"
    status := .proven, prop := ``ViewBoundaryBehavior, thm := some ``viewBoundaryBehavior },
  { id := "nummisc-coverage-views-macro"
    juliaFile := "base/views.jl"
    juliaFns := ["maybeview", "_views", "@views"]
    statement := "maybeview chooses getindex for scalars and nonarrays, _views recursively rewrites reads while preserving assignment targets, and @views applies boundary replacement before escaping the result."
    source := "base/views.jl:235-334"
    status := .proven, prop := ``ViewsMacroBehavior, thm := some ``viewsMacroBehavior },
  { id := "nummisc-coverage-genericmemory-core"
    juliaFile := "base/genericmemory.jl"
    juliaFns := ["IndexStyle", "parent", "memoryindex", "pointer", "unsetindex methods", "elsize", "sizeof", "isassigned", "unsafe_copyto!", "copy", "copyto!", "similar", "fill!", "convert", "promote_rule", "Memory constructor"]
    statement := "GenericMemory projections, unset wrappers, checked assignment queries, typed and fallback copy routes, constructors, fill, conversion, and promotion preserve source checks, alias direction, and return values."
    source := "base/genericmemory.jl:64-301"
    status := .proven, prop := ``GenericMemoryCoreBehavior, thm := some ``genericMemoryCoreBehavior },
  { id := "nummisc-coverage-genericmemory-index"
    juliaFile := "base/genericmemory.jl"
    juliaFns := ["getindex", "_setindex!", "setindex!", "cmp", "==", "findall", "indcopy", "atomic index operations"]
    statement := "GenericMemory range and colon indexing, scalar and bulk assignment, comparison, sorted-find choice, subregion copying, and atomic wrappers preserve source bounds, conversion, ordering, and forwarding."
    source := "base/genericmemory.jl:308-490"
    status := .proven, prop := ``GenericMemoryIndexBehavior, thm := some ``genericMemoryIndexBehavior },
  { id := "nummisc-coverage-pointer-conversion"
    juliaFile := "base/pointer.jl"
    juliaFns := ["convert", "cconvert", "unsafe_convert methods", "unsafe_wrap", "unsafe_load", "unsafe_store!", "unsafe_modify!", "unsafe_replace!", "unsafe_swap!", "unsafe_pointer_to_objref", "pointer_from_objref"]
    statement := "Pointer conversion, array and memory rooting, memory-reference offsets, unsafe wrapping and access forwarding, atomic operations, and object-pointer conversion follow source casts, branches, and mutability checks."
    source := "base/pointer.jl:23-303"
    status := .proven, prop := ``PointerConversionBehavior, thm := some ``pointerConversionBehavior },
  { id := "nummisc-coverage-pointer-arithmetic"
    juliaFile := "base/pointer.jl"
    juliaFns := ["isequal", "isless", "==", "<", "pointer subtraction", "pointer addition and subtraction by Integer", "unsigned", "signed"]
    statement := "Pointer equality and ordering compare UInt addresses, differences and integer offsets wrap in the UInt address space, and signed or unsigned conversion projects the same bits."
    source := "base/pointer.jl:307-320"
    status := .proven, prop := ``PointerArithmeticBehavior, thm := some ``pointerArithmeticBehavior },
  { id := "nummisc-coverage-ref-core"
    juliaFile := "base/refpointer.jl"
    juliaFns := ["Ref metadata and iteration", "Ref conversion", "RefArray constructors", "RefArray unsafe_convert", "Ref", "Ref{T}"]
    statement := "Ref metadata, iteration, value conversion, RefArray construction, pointer route selection, single-Ref index checking, and pointer indexing preserve source values, roots, and deferred checks."
    source := "base/refpointer.jl:97-150"
    status := .proven, prop := ``RefCoreBehavior, thm := some ``refCoreBehavior },
  { id := "nummisc-coverage-ref-array-tuple"
    juliaFile := "base/refpointer.jl"
    juliaFns := ["Ref{P}(::Array)", "Ref(::AbstractArray,i)", "pointer-array cconvert", "tuple cconvert and unsafe_convert", "getindex(::RefArray)", "setindex!(::RefArray)"]
    statement := "Pointer-array refs retain conversion roots and append a null terminator, tuple refs expose their first element through a rooted tuple, and RefArray reads and writes use the stored index."
    source := "base/refpointer.jl:154-194"
    status := .proven, prop := ``RefArrayTupleBehavior, thm := some ``refArrayTupleBehavior },
  { id := "nummisc-coverage-bool-methods"
    juliaFile := "base/bool.jl"
    juliaFns := ["promotion", "typemin", "typemax", "bitwise logic", "xor", "nand", "nor", "shifts", "numeric predicates", "ordering", "unary and binary arithmetic", "powers", "float arithmetic", "div", "rem", "mod", "Bool(::Real)"]
    statement := "Every Bool method follows its two-value truth table, Int promotion, shift forwarding, strong-zero float formulas, checked division or remainder branch, and exact real conversion."
    source := "base/bool.jl:6-170"
    status := .proven, prop := ``BoolMethodBehavior, thm := some ``boolMethodBehavior },
  { id := "nummisc-coverage-summarysize"
    juliaFile := "base/summarysize.jl"
    juliaFns := ["nth_pointer_isdefined", "get_nth_pointer", "summarysize", "_summarysize", "SummarySize call overloads"]
    statement := "Summary-size traversal deduplicates identities, honors exclude and chargeall, charges bytes or object count, enumerates kind-specific pointer fields, and processes the frontier in source order."
    source := "base/summarysize.jl:12-263"
    status := .proven, prop := ``SummarySizeBehavior, thm := some ``summarySizeBehavior }
]

end JuliaLean.NumMisc

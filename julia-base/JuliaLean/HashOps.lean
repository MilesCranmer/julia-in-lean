import JuliaLean.Registry.Types
import JuliaLean.HashOps.Validation

namespace JuliaLean.HashOps

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "hashops-small-integer-hash"
    juliaFile := "base/hashing.jl"
    juliaFns := ["hash(::UInt64, ::UInt)", "hash(::Int64, ::UInt)", "hash(::Union{Bool,Int8,UInt8,Int16,UInt16,Int32,UInt32}, ::UInt)"]
    statement := "For every seed, isequal machine integers of any widths through 64 bits have equal hashes."
    source := "hash docstring base/hashing.jl:12-20; integer methods base/hashing.jl:75-77"
    status := .proven
    prop := ``SmallIntegerHashConsistency
    thm := some ``smallIntegerHashConsistency_proven
    notes := "Uses Promotion.Hash's source-level primitive-call terms. Int128, UInt128, BigInt and BigFloat use the generic decomposition entry." },
  { id := "hashops-decomposed-real-hash"
    juliaFile := "base/hashing.jl"
    juliaFns := ["hash(::Real, ::UInt)", "hash_integer", "decompose"]
    statement := "The generic Real hash gives equal results for every seed when isequal values have the same normalized decompose triple and intermediate integer storage type."
    source := "hash docstring base/hashing.jl:12-20; generic Real method base/hashing.jl:198-245"
    status := .proven
    prop := ``DecomposedHashConsistency
    thm := some ``decomposedHashConsistency_proven
    notes := "This is the shared source obligation for Int128, UInt128, BigInt, BigFloat and generic Rational/Real paths. Cross-type dispatch was also differential-checked against Julia." },
  { id := "hashops-string-hash"
    juliaFile := "base/hashing.jl"
    juliaFns := ["hash(::AbstractString, ::UInt)", "hash(::String, ::UInt)", "utf8units", "codeunits"]
    statement := "Valid byte-backed and character-iterated strings with the same character sequence hash equally for every seed."
    source := "hash docstring base/hashing.jl:12-20; UTF8Units and string methods base/hashing.jl:101-145,649-654"
    status := .proven
    prop := ``StringHashConsistency
    thm := some ``stringHashConsistency_proven
    notes := "Covers String, SubString, LazyString, StringView and annotation-free AnnotatedString values on their valid UTF-8 path." },
  { id := "hashops-annotated-isless"
    juliaFile := "base/strings/annotated.jl"
    juliaFns := ["isequal(::AnnotatedString, ::AnnotatedString)", "cmp(::AnnotatedString, ::AnnotatedString)", "isless(::AbstractString, ::AbstractString)"]
    statement := "For any two AnnotatedStrings, exactly one of isless(a,b), isless(b,a), and isequal(a,b) is true."
    source := "isless docstring base/operators.jl:208-214; cmp docstring base/operators.jl:508-511"
    status := .refuted
    prop := ``AnnotatedStringOrder
    thm := some ``annotatedStringOrder_refuted
    issue := "none found (queries: AnnotatedString cmp; AnnotatedString isless; AnnotatedString equality ordering; annotations cmp isless)"
    notes := "Same text with :red versus :blue annotations: isequal and both isless calls are false, while cmp is 0, on both versions." },
  { id := "hashops-annotated-non8-hash"
    juliaFile := "base/hashing.jl"
    juliaFns := ["hash(::AbstractString, ::UInt)", "iterate(::UTF8Units)", "hash(::AnnotatedString, ::UInt)"]
    statement := "An annotation-free AnnotatedString over a non-UInt8 AbstractString hashes successfully and equals the hash of its isequal underlying string."
    source := "hash docstring base/hashing.jl:12-20; AnnotatedString equality base/strings/annotated.jl:232-233"
    status := .refuted
    prop := ``AnnotatedStringHash
    thm := some ``annotatedStringHash_refuted
    issue := "none found (queries: AnnotatedString hash; UTF8Units AnnotatedChar; hash AbstractString reinterpret; non UInt8 AbstractString hash)"
    notes := "UTF8Units reinterprets the non-isbits AnnotatedChar and throws ArgumentError on both versions; the underlying UTF32String hashes normally." },
  { id := "hashops-array-hash"
    juliaFile := "base/multidimensional.jl"
    juliaFns := ["hash(::AbstractArray, ::UInt)", "hash_shaped", "_hash_fib"]
    statement := "Arrays with equal axes and equal canonical element isequal classes hash equally for every seed in the short, eight-stream and Fibonacci branches."
    source := "hash docstring base/hashing.jl:12-20; array equality base/abstractarray.jl:3106-3116; hashing base/multidimensional.jl:1995-2123"
    status := .proven
    prop := ``ArrayHashConsistency
    thm := some ``arrayHashConsistency_proven
    notes := "The model retains the thresholds 8 and 32768, eight accumulator streams, Fibonacci skips, index hashing and previous-distinct search. Boundary lengths were differential-checked against ranges, vectors and views." },
  { id := "hashops-tuple-hash"
    juliaFile := "base/tuple.jl"
    juliaFns := ["hash(::Tuple, ::UInt)", "hash(::Any32, ::UInt)", "hash(::NamedTuple, ::UInt)"]
    statement := "If element hash respects element isequal, isequal Tuples and NamedTuples hash equally for every seed."
    source := "hash docstring base/hashing.jl:12-20; tuple methods base/tuple.jl:601-610"
    status := .proven
    prop := ``TupleHashConsistency
    thm := some ``tupleHashConsistency_proven
    notes := "Reuses the complete recursive and Any32 Tuple proof from JuliaLean.Tuples." },
  { id := "hashops-unordered-hash"
    juliaFile := "base/abstractdict.jl"
    juliaFns := ["hash(::AbstractDict, ::UInt)", "hash(::AbstractSet, ::UInt)"]
    statement := "Permuting the pairs of a lawful AbstractDict or the elements of a lawful AbstractSet does not change its hash for any seed."
    source := "hash docstring base/hashing.jl:12-20; base/abstractdict.jl:538-545; base/set.jl:697-704"
    status := .proven
    prop := ``UnorderedHashConsistency
    thm := some ``unorderedHashConsistency_proven
    notes := "The source xor fold is proved permutation-invariant. ImmutableDict duplicate-key equality violates the lawful unique-key premise and is already catalogued by Dicts." },
  { id := "hashops-comparison-fallbacks"
    juliaFile := "base/operators.jl"
    juliaFns := ["isless(::Real, ::Real)", "cmp", "cmp(::Integer, ::Integer)"]
    statement := "The generic Real isless inherits any strict weak order implemented by <, and cmp agrees exactly with its two isless calls."
    source := "isless docstring base/operators.jl:205-225; cmp docstring and methods base/operators.jl:507-537"
    status := .proven
    prop := ``ComparisonFallbacks
    thm := some ``comparisonFallbacks_proven
    notes := "Specialized signed-zero cmp failures for Rational and BigFloat are already catalogued by Promotion and BigNums." },
  { id := "hashops-operator-fallbacks"
    juliaFile := "base/operators.jl"
    juliaFns := ["isequal", "!=", "<=", ">="]
    statement := "The generic isequal, !=, <= and >= methods implement their documented equations in terms of == and <."
    source := "base/operators.jl:196,338,467,499"
    status := .proven
    prop := ``OperatorFallbacks
    thm := some ``operatorFallbacks_proven },
  { id := "hashops-number-fallbacks"
    juliaFile := "base/number.jl"
    juliaFns := ["zero", "one", "oneunit", "iszero", "isone", "signbit", "abs", "sign", "fma", "muladd", "inv", "literal_pow"]
    statement := "The generic number fallbacks implement the documented constructor, predicate, sign, multiply-add, inverse and small literal-power equations."
    source := "base/number.jl:25-66,121-214,278-305,336-432; base/promotion.jl:657-659; base/intfuncs.jl:470-489"
    status := .proven
    prop := ``NumberFallbacks
    thm := some ``numberFallbacks_proven },
  { id := "hashops-widen-unsigned-sub"
    juliaFile := "base/operators.jl"
    juliaFns := ["widen", "widen(::Type{UInt8})", "-(::UInt16, ::UInt16)"]
    statement := "After widening any two fixed-width integers of one type, their sum and difference equal the mathematical results without overflow or precision loss."
    source := "widen docstring base/operators.jl:955-964"
    status := .refuted
    prop := ``WidenNoLoss
    thm := some ``widenNoLoss_refuted
    issue := "none found (queries: widen UInt; widen unsigned; widen subtraction; guaranteed not to overflow widen)"
    notes := "widen(UInt8(0)) - widen(typemax(UInt8)) is UInt16(65281), not -255, on both versions. The implementation may be intended; then the docstring overpromises." },
  { id := "hashops-widen-addition"
    juliaFile := "base/int.jl"
    juliaFns := ["widen(::Type{<:BitInteger})", "+(::BitInteger, ::BitInteger)"]
    statement := "After widening any two fixed-width integers of one type, their sum equals the mathematical sum without overflow."
    source := "widen docstring base/operators.jl:955-964; type table base/int.jl:911-918"
    status := .proven
    prop := ``WidenAdditionNoLoss
    thm := some ``widenAdditionNoLoss_proven }
]

end JuliaLean.HashOps

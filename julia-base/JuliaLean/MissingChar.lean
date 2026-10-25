import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.MissingChar.Basic
import JuliaLean.MissingChar.Logic
import JuliaLean.MissingChar.Some
import JuliaLean.MissingChar.Skip
import JuliaLean.MissingChar.SkipProofs
import JuliaLean.MissingChar.Char
import JuliaLean.MissingChar.CharProofs

namespace JuliaLean.MissingChar

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- three-valued logic and comparisons
  { id := "missingchar-three-valued-logic", juliaFile := "base/missing.jl"
    juliaFns := ["&(::Missing, ::Bool)", "|(::Missing, ::Bool)", "xor(::Missing, ::Bool)", "!(::Missing)", "nand", "nor"]
    statement := "&, |, xor, !, nand and nor on Union{Bool, Missing} follow Kleene's three-valued logic: missing exactly when the result depends on a missing operand."
    source := "doc/src/manual/missing.md:105-201", status := .proven
    prop := ``ThreeValuedLogic, thm := some ``threeValuedLogic_proven },
  { id := "missingchar-logic-algebra", juliaFile := "base/missing.jl"
    juliaFns := ["&(::Missing, ::Bool)", "|(::Missing, ::Bool)", "!(::Missing)"]
    statement := "& and | on Union{Bool, Missing} are commutative and associative, distribute, and satisfy De Morgan's laws with !."
    source := "invariant (consequence of three-valued logic, doc/src/manual/missing.md:105-201)", status := .proven
    prop := ``LogicAlgebra, thm := some ``logicAlgebra_proven },
  { id := "missingchar-comparison-propagates", juliaFile := "base/missing.jl"
    juliaFns := ["==(::Missing, ::Any)", "<(::Missing, ::Any)", "!=", "<=", ">", ">="]
    statement := "==, !=, <, <=, > and >= return missing whenever an operand is missing, and agree with the ordinary methods otherwise."
    source := "doc/src/manual/missing.md:49-50", status := .proven
    prop := ``ComparisonPropagates, thm := some ``comparisonPropagates_proven },
  { id := "missingchar-isless-strict-weak", juliaFile := "base/missing.jl"
    juliaFns := ["isless(::Missing, ::Any)", "isless(::Any, ::Missing)"]
    statement := "isless on values that may be missing is a strict weak order whenever isless on the other values is one."
    source := "base/operators.jl:206-217 (isless contract); base/missing.jl:86-88", status := .proven
    prop := ``IslessStrictWeak, thm := some ``islessStrictWeak_proven },
  { id := "missingchar-isless-missing-last", juliaFile := "base/missing.jl"
    juliaFns := ["isless(::Missing, ::Any)", "isless(::Any, ::Missing)"]
    statement := "isless(missing, x) is false for every x and isless(x, missing) is true for every non-missing x."
    source := "doc/src/manual/missing.md:90-92", status := .proven
    prop := ``MissingLast, thm := some ``missingLast_proven },
  { id := "missingchar-isless-trichotomy", juliaFile := "base/missing.jl"
    juliaFns := ["isless(::Missing, ::Any)", "isequal(::Missing, ::Any)"]
    statement := "Exactly one of isless(x, y), isless(y, x) and isequal(x, y) is true when x or y is missing, given this holds for non-missing values."
    source := "base/operators.jl:206-213 (isless docstring)", status := .proven
    prop := ``IslessTrichotomy, thm := some ``islessTrichotomy_proven },
  { id := "missingchar-isequal-missing", juliaFile := "base/missing.jl"
    juliaFns := ["isequal(::Missing, ::Missing)", "isequal(::Missing, ::Any)"]
    statement := "isequal(missing, x) is true exactly for x === missing, and isequal stays an equivalence relation with missing added."
    source := "doc/src/manual/missing.md:71-74", status := .proven
    prop := ``IsequalMissing, thm := some ``isequalMissing_proven },
  { id := "missingchar-minmax-missing", juliaFile := "base/missing.jl"
    juliaFns := ["min(::Missing, ::Any)", "max(::Missing, ::Any)", "minmax(::Missing, ::Any)"]
    statement := "min and max return missing when an argument is missing, and minmax(x, y) == (min(x, y), max(x, y)) for values that may be missing."
    source := "base/operators.jl:540-587 (max, min, minmax docstrings)", status := .proven
    prop := ``MinMaxMissing, thm := some ``minMaxMissing_proven
    notes := "Master defines minmax(::Missing, ::Any) = (missing, missing); on 1.13.2 minmax(missing, 1) == (1, missing) and max(missing) has no method." },
  { id := "missingchar-isgreater-missing", juliaFile := "base/operators.jl"
    juliaFns := ["Base.isgreater", "isunordered(::Missing)"]
    statement := "Base.isgreater orders missing below every other value, NaN included."
    source := "base/operators.jl:255-262 (isgreater docstring)", status := .proven
    prop := ``IsgreaterMissingSmallest, thm := some ``isgreaterMissingSmallest_proven },
  -- coalesce, something, Some
  { id := "missingchar-coalesce-first", juliaFile := "base/missing.jl"
    juliaFns := ["coalesce", "@coalesce"]
    statement := "coalesce(xs...) and @coalesce(xs...) return the first argument that is not missing, or missing."
    source := "base/missing.jl:398-399 (coalesce docstring)", status := .proven
    prop := ``CoalesceFirst, thm := some ``coalesceFirst_proven },
  { id := "missingchar-something-first", juliaFile := "base/some.jl"
    juliaFns := ["something", "@something"]
    statement := "something(xs...) and @something(xs...) return the first argument that is not nothing, unwrapping one Some, and throw ArgumentError if there is none."
    source := "base/some.jl:73-75 (something docstring)", status := .proven
    prop := ``SomethingFirst, thm := some ``somethingFirst_proven },
  { id := "missingchar-notnothing", juliaFile := "base/some.jl"
    juliaFns := ["notnothing"]
    statement := "notnothing(x) throws when x === nothing and returns x otherwise."
    source := "base/some.jl:50-52", status := .proven
    prop := ``NotnothingSpec, thm := some ``notnothingSpec_proven },
  { id := "missingchar-some-hash-isequal", juliaFile := "base/some.jl"
    juliaFns := ["isequal(::Some, ::Some)", "hash(::Some, ::UInt)"]
    statement := "isequal(Some(a), Some(b)) implies hash(Some(a), h) == hash(Some(b), h) whenever the hash contract holds for the wrapped values."
    source := "invariant (hash docstring: isequal(x,y) implies hash(x)==hash(y))", status := .proven
    prop := ``SomeHashIsequal, thm := some ``someHashIsequal_proven },
  { id := "missingchar-some-show-typeinfo", juliaFile := "base/some.jl"
    juliaFns := ["show(::IO, ::Some)"]
    statement := "Evaluating repr(v) for v::Vector{Some{Int64}} gives v back."
    source := "base/show.jl (show docstring: parseable Julia code when possible)", status := .refuted
    prop := ``SomeShowEval, thm := some ``someShowEval_refuted
    issue := "none found (queries: Some show typeinfo, Some typeinfo, show Some array convert, repr Some)"
    notes := "repr([Some(1), Some(2)]) == \"Some{Int64}[1, 2]\", which throws MethodError (no convert(Some{Int64}, ::Int64)). show(io, x::Some) prints the bare value when :typeinfo == typeof(x)." },
  { id := "missingchar-sincospi-missing", juliaFile := "base/math.jl"
    juliaFns := ["sincospi(::Missing)", "sincos(::Missing)", "sincosd(::Missing)"]
    statement := "sincos, sincosd and sincospi of missing return the tuple (missing, missing)."
    source := "base/special/trig.jl:993-996 (sincospi returns a tuple); doc/src/manual/missing.md:14-18", status := .refuted
    prop := ``SincosFamilyMissing, thm := some ``sincosFamilyMissing_refuted
    issue := "none found (queries: sincospi missing, sincos missing, sincospi, sincosd missing)"
    notes := "sincospi(missing) === missing because :sincospi is in the f(::Missing) = missing loop at base/math.jl:1322-1332 (PR #50850); sincosd(missing) === (missing, missing)." },
  -- skipmissing
  { id := "missingchar-skipmissing-iterate", juliaFile := "base/missing.jl"
    juliaFns := ["iterate(::SkipMissing)", "collect(::SkipMissing)"]
    statement := "Iterating skipmissing(x) for a vector x yields exactly the non-missing elements of x in order."
    source := "base/missing.jl:185, 190-193 (skipmissing docstring)", status := .proven
    prop := ``SkipMissingIterate, thm := some ``skipMissingIterate_proven },
  { id := "missingchar-skipmissing-keys", juliaFile := "base/missing.jl"
    juliaFns := ["keys(::SkipMissing)", "eachindex(::SkipMissing)", "getindex(::SkipMissing, ::Int)"]
    statement := "keys(skipmissing(x)) are the indices of the non-missing elements; s[i] at those keys gives the iterated values, at other in-bounds indices it throws MissingException."
    source := "base/missing.jl:186-188 (skipmissing docstring)", status := .proven
    prop := ``SkipMissingKeys, thm := some ``skipMissingKeys_proven },
  { id := "missingchar-skipmissing-getindex-nonscalar", juliaFile := "base/missing.jl"
    juliaFns := ["getindex(::SkipMissing, I...)"]
    statement := "Indexing skipmissing(x) with a vector of indices never returns a missing value."
    source := "base/missing.jl:186-188 (skipmissing docstring: indices of missing values are not valid)", status := .refuted
    prop := ``SkipMissingGetindexNoMissing, thm := some ``skipMissingGetindexNoMissing_refuted
    issue := "none found (queries: skipmissing getindex range, skipmissing indexing vector, SkipMissing getindex, skipmissing index range missing); related #30606 (open)"
    notes := "skipmissing([1, missing, 3])[1:2] == [1, missing] and skipmissing(x)[[2]] == [missing]; getindex only checks ismissing on the whole result." },
  { id := "missingchar-skipmissing-filter", juliaFile := "base/missing.jl"
    juliaFns := ["filter(::Any, ::SkipMissing{<:AbstractArray})"]
    statement := "filter(f, skipmissing(x)) equals filter(f, collect(skipmissing(x)))."
    source := "base/missing.jl:367-368 (filter docstring)", status := .proven
    prop := ``SkipMissingFilter, thm := some ``skipMissingFilter_proven },
  { id := "missingchar-skipmissing-findfirst", juliaFile := "base/missing.jl"
    juliaFns := ["findfirst(::Function, ::SkipMissing)"]
    statement := "findfirst(f, skipmissing(x)) is the first index of x holding a non-missing value satisfying f."
    source := "doc/src/manual/missing.md:356-360", status := .proven
    prop := ``SkipMissingFindFirst, thm := some ``skipMissingFindFirst_proven },
  { id := "missingchar-skipmissing-findlast", juliaFile := "base/missing.jl"
    juliaFns := ["findlast(::Function, ::SkipMissing)", "findnext(::Function, ::SkipMissing, ::Int)", "findprev(::Function, ::SkipMissing, ::Int)"]
    statement := "findlast(f, skipmissing(x)) is the last index of x holding a non-missing value satisfying f."
    source := "doc/src/manual/missing.md:356-360", status := .refuted
    prop := ``SkipMissingFindLast, thm := some ``skipMissingFindLast_refuted
    issue := "none found (queries: skipmissing findlast, findnext skipmissing, findprev skipmissing, skipmissing nextind, Cannot reverse zipped iterators); related #37014 (open)"
    notes := "findlast throws ArgumentError (reverse of a zip with the SizeUnknown keys Filter); findnext/findprev throw MethodError (no nextind/prevind) or MissingException; findfirst and findall work. Only findlast is modelled." },
  { id := "missingchar-skipmissing-mapreduce", juliaFile := "base/missing.jl"
    juliaFns := ["mapreduce(::Any, ::Any, ::SkipMissing{<:AbstractArray})", "_mapreduce_impl_skipmissing"]
    statement := "For associative op, mapreduce(f, op, skipmissing(x)) is the left fold of op over f of the non-missing values (mapreduce_empty if none), for every pairwise block size."
    source := "doc/src/manual/missing.md:318-326; base/missing.jl:269-362", status := .proven
    prop := ``SkipMissingMapreduce, thm := some ``skipMissingMapreduce_proven
    notes := "The @simd loop is modelled as a left fold; the pairwise association structure matches Julia exactly in a differential test with a non-associative bracketing op on vectors up to 3000 elements." },
  -- Char
  { id := "missingchar-isvalid-char-negative", juliaFile := "base/strings/unicode.jl"
    juliaFns := ["isvalid(::Type{<:AbstractChar}, ::Integer)"]
    statement := "isvalid(Char, x) returns a Bool for every Int x: true exactly for valid codepoints."
    source := "base/strings/unicode.jl:34-36 (isvalid(T, value) docstring)", status := .refuted
    prop := ``IsvalidCharInteger, thm := some ``isvalidCharInteger_refuted
    issue := "none found (queries: isvalid Char negative, isvalid InexactError, isvalid(Char, -1))"
    notes := "isvalid(Char, -1) throws InexactError from Unsigned(-1) at base/strings/unicode.jl:60." },
  { id := "missingchar-codepoint-malformed", juliaFile := "base/char.jl"
    juliaFns := ["codepoint(::Char)", "UInt32(::Char)"]
    statement := "codepoint(c) throws for every malformed Char c."
    source := "base/char.jl:83-85 (codepoint docstring), :141-142 (ismalformed docstring)", status := .refuted
    prop := ``CodepointThrowsMalformed, thm := some ``codepointThrowsMalformed_refuted
    issue := "none found (queries: codepoint malformed, ismalformed codepoint, UInt32 Char malformed, InvalidCharError reinterpret)"
    notes := "reinterpret(Char, 0x61620000) is malformed but codepoint returns 0x61: UInt32(c::Char) returns u >> 24 for u < 0x80000000 before checking the low bytes." },
  { id := "missingchar-codepoint-wellformed", juliaFile := "base/char.jl"
    juliaFns := ["codepoint(::Char)", "ismalformed(::Char)"]
    statement := "codepoint(c) succeeds for every Char c with ismalformed(c) false, including overlong encodings."
    source := "base/char.jl:89-92 (codepoint docstring)", status := .proven
    prop := ``CodepointWellFormed, thm := some ``codepointWellFormed_proven },
  { id := "missingchar-char-codepoint-roundtrip", juliaFile := "base/char.jl"
    juliaFns := ["Char(::UInt32)", "codepoint(::Char)", "ismalformed(::Char)", "isoverlong(::Char)"]
    statement := "Char(u) throws CodePointError exactly for u >= 0x200000; otherwise it is well-formed, not overlong, and codepoint(Char(u)) == u."
    source := "base/char.jl:39-51 (Char docstring), :135-140 (ismalformed docstring)", status := .proven
    prop := ``CharCodepointRoundTrip, thm := some ``charCodepointRoundTrip_proven },
  { id := "missingchar-char-order-codepoint", juliaFile := "base/char.jl"
    juliaFns := ["isless(::Char, ::Char)", "==(::Char, ::Char)"]
    statement := "For Chars built from codepoints, < and == agree with < and == on the codepoints."
    source := "base/char.jl:10-12 (AbstractChar docstring)", status := .proven
    prop := ``CharOrderCodepoint, thm := some ``charOrderCodepoint_proven },
  { id := "missingchar-isvalid-char-codepoint", juliaFile := "base/strings/unicode.jl"
    juliaFns := ["isvalid(::Char)", "isvalid(::Type{Char}, ::Unsigned)"]
    statement := "isvalid(Char(u)) == isvalid(Char, u) for every codepoint u that Char accepts."
    source := "base/strings/unicode.jl:58-59; invariant", status := .proven
    prop := ``IsvalidCharCodepoint, thm := some ``isvalidCharCodepoint_proven },
  { id := "missingchar-char-add-codepoint", juliaFile := "base/char.jl"
    juliaFns := ["+(::Char, ::Integer)", "+%(::Char, ::Integer)"]
    statement := "Char(u) + n == Char(u + n) for every Int n with 0 <= u + n < 0x200000."
    source := "invariant (Char arithmetic on codepoints, base/char.jl:274-300)", status := .proven
    prop := ``CharAddCodepoint, thm := some ``charAddCodepoint_proven },
  { id := "missingchar-isvalid-overlength", juliaFile := "base/char.jl"
    juliaFns := ["ismalformed(::Char)", "isvalid(::Char)", "codepoint(::Char)"]
    statement := "Every Char c with isvalid(c) is the UTF-8 encoding of its codepoint: codepoint(c) <= 0x10ffff and Char(codepoint(c)) == c."
    source := "base/char.jl:46-50 (Char docstring: isvalid tells whether c represents a valid Unicode character)", status := .refuted
    prop := ``IsvalidCanonical, thm := some ``isvalidCanonical_refuted
    issue := "none found (queries: ismalformed, isvalid Char reinterpret, isvalid char codepoint 0x10ffff, ismalformed continuation bytes)"
    notes := "reinterpret(Char, 0xe9a9a5bf) (3-byte lead, 3 continuation bytes) is valid with codepoint 0x26997f; reinterpret(Char, 0x00800000) is valid with codepoint 0 but != '\\0'. ismalformed never checks that the byte count matches the lead byte." },
  { id := "missingchar-ncodeunits-write", juliaFile := "base/char.jl"
    juliaFns := ["ncodeunits(::Char)", "write(::IO, ::Char)"]
    statement := "ncodeunits(c) is the number of bytes write(io, c) emits, for every Char bit pattern c."
    source := "base/char.jl:63-65 (ncodeunits docstring)", status := .proven
    prop := ``NcodeunitsWrite, thm := some ``ncodeunitsWrite_proven },
  { id := "missingchar-show-char-roundtrip", juliaFile := "base/char.jl"
    juliaFns := ["show(::IO, ::AbstractChar)"]
    statement := "For every well-formed, non-overlong Char c, the literal repr(c) parses back to c."
    source := "base/show.jl (show docstring: parseable Julia code when possible)", status := .refuted
    prop := ``ShowCharParses, thm := some ``showCharParses_refuted
    issue := "#54396 (open, duplicate); related #1988 (closed)"
    notes := "repr(Char(0x110000)) == \"'\\\\U110000'\"; JuliaSyntax rejects \\U escapes above 0x10ffff. The same Char parses as '\\xf4\\x90\\x80\\x80'. Over-length Chars (see missingchar-isvalid-overlength) also fail: reinterpret(Char, 0x00800000) prints as '\\x00', which parses to '\\0'." }
]

end JuliaLean.MissingChar

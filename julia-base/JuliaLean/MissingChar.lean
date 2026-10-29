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
  -- coalesce, something, Some
  { id := "missingchar-coalesce-first", juliaFile := "base/missing.jl"
    juliaFns := ["coalesce", "@coalesce"]
    statement := "coalesce(xs...) and @coalesce(xs...) return the first argument that is not missing, or missing."
    source := "base/missing.jl:398-399 (coalesce docstring)", status := .proven
    prop := ``CoalesceFirst, thm := some ``coalesceFirst_proven },
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
    notes := "The @simd loop is modelled as a left fold; the pairwise association structure matches Julia exactly in a differential test with a non-associative bracketing op on vectors up to 3000 elements." }
  -- Char
]

end JuliaLean.MissingChar

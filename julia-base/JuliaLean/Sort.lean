import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Sort.Ordering
import JuliaLean.Sort.Search
import JuliaLean.Sort.RangeSearch
import JuliaLean.Sort.RangeSearchProof
import JuliaLean.Sort.Algorithms
import JuliaLean.Sort.Partial
import JuliaLean.Sort.AlgorithmsProof

namespace JuliaLean.Sort

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "sort-order-reverse-cancellation", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering", "reverse(::Ordering)"]
    statement := "Reversing an ordering twice restores it, including the By and Perm specializations."
    source := "base/ordering.jl:33-48,110-111 (ReverseOrdering docstring)", status := .proven
    prop := ``ReverseCancellation, thm := some ``reverseCancellation
    notes := "Orderings are modelled in constructor-normal form; the key function of By has the element type as codomain." },
  { id := "sort-order-combinations", juliaFile := "base/ordering.jl"
    juliaFns := ["ord", "_ord", "_by", "lt"]
    statement := "ord(lt, by, rev, order) compares by-keys with lt (or isless), reversed exactly when one of rev=true and order=Reverse holds, for every combination of lt, by, rev in {nothing,false,true} and order in {Forward, Reverse}; in particular rev=true cancels order=Reverse."
    source := "base/ordering.jl:140-153 (ord docstring: all options independent, usable in all combinations)", status := .proven
    prop := ``OrdCombinations, thm := some ``ordCombinations },
  { id := "sort-order-perm-stability", juliaFile := "base/ordering.jl"
    juliaFns := ["Perm", "lt(::Perm, a, b)"]
    statement := "Under Perm, indices of equivalent data values compare by numeric value."
    source := "base/ordering.jl:98-103 (Perm docstring)", status := .proven
    prop := ``PermStability, thm := some ``permStability },
  { id := "sort-issorted-adjacent", juliaFile := "base/sort.jl"
    juliaFns := ["issorted(itr, order)"]
    statement := "issorted(itr, o) is true exactly when no element is ordered before its predecessor."
    source := "base/sort.jl:62-66 (issorted docstring)", status := .proven
    prop := ``IssortedAdjacent, thm := some ``issortedAdjacent },
  { id := "sort-vector-search-correct", juliaFile := "base/sort.jl"
    juliaFns := ["searchsortedfirst(v, x; kws...)", "searchsortedlast(v, x; kws...)"]
    statement := "For every vector sorted under a strict weak order, searchsortedfirst returns the first index whose value is not ordered before x (length+1 if none) and searchsortedlast the last index whose value is not ordered after x (0 if none)."
    source := "base/sort.jl:353-357, 392-396 (docstrings)", status := .proven
    prop := ``VectorSearchCorrect, thm := some ``vectorSearchCorrect
    notes := "The binary-search interpreter tracks the Julia type of each local (promotion of m+1 to Int, T-typed sentinels); the theorem covers the keyword methods, which search the Int window 1:length(v) (length < 2^62)." },
  { id := "sort-vector-u8-search-sentinel", juliaFile := "base/sort.jl"
    juliaFns := ["searchsortedlast(v, x, lo::T, hi::T, o)", "searchsorted(v, x, lo::T, hi::T, o)"]
    statement := "For a valid window 1 <= lo <= hi <= length(v) of any integer type, searchsortedlast(v, x, lo, hi, o) never reads outside the vector."
    source := "invariant: the positional methods accept any lo::T, hi::T <: Integer (base/sort.jl:203, 221) and read v[m] under @inbounds", status := .refuted
    prop := ``WindowSearchInBounds, thm := some ``windowSearchInBounds_refuted
    issue := "none found (related: #31618 generalized lo/hi to T<:Integer; #30388 these methods are undocumented; queries: searchsortedlast UInt8, searchsorted lo hi, searchsorted overflow)"
    notes := "lo=0x01, hi=0xff: hi + 0x01 wraps to 0x00, so lo-u == hi+u == 0x00 and midpoint(0x00,0x00) = 0 is read with @inbounds. searchsortedfirst is unaffected because m+1 promotes to Int. Same on 1.13.2." },
  { id := "sort-range-search-no-overflow", juliaFile := "base/sort.jl"
    juliaFns := ["searchsortedfirst(::AbstractRange{<:Integer}, x, o)", "searchsortedlast(::AbstractRange{<:Integer}, x, o)"]
    statement := "On every nonempty sorted integer range (UnitRange{T}, StepRange{T,T}) and every x::T for which x - first(r) neither overflows T nor equals typemin(T), the range methods agree with the docstring answer on collect(r), for Forward, Reverse, Lt(<) and ReverseOrdering(Lt(<))."
    source := "base/sort.jl:353-357, 392-396 (docstrings); the range methods are documented as optimized implementations of the same functions", status := .proven
    prop := ``RangeSearchNoOverflowCorrect, thm := some ``rangeSearchNoOverflowCorrect },
  { id := "sort-range-search-overflow", juliaFile := "base/sort.jl"
    juliaFns := ["searchsortedfirst(::AbstractRange{<:Integer}, x, o)", "searchsortedlast(::AbstractRange{<:Integer}, x, o)", "searchsorted(::AbstractRange{<:Real}, x, o)"]
    statement := "On every nonempty sorted integer range and every x of its element type, the range methods agree with the docstring answer on collect(r)."
    source := "base/sort.jl:353-357, 392-396 (docstrings)", status := .refuted
    prop := ``RangeSearchNonemptyCorrect, thm := some ``rangeSearchNonemptyCorrect_refuted
    issue := "#63399 (open PR, same overflow; queries: searchsorted overflow, searchsortedfirst range, searchsorted range wrong, searchsortedlast Int8)"
    notes := "x - first(r) is computed in T (sort.jl:278, 280, 294, 296) and wraps once the range spans more than typemax(T): searchsortedfirst(Int8(-100):Int8(100), Int8(50)) == -105. With x::Int it hits Int64 ranges spanning more than typemax(Int), e.g. typemin(Int):2:2^62 (theorem rangeSearchInt64Overflow). When x - first(r) == typemin(T) and step == -1, fld throws DivideError instead. Same on 1.13.2." },
  { id := "sort-range-search-empty", juliaFile := "base/sort.jl"
    juliaFns := ["searchsortedfirst(::AbstractRange{<:Integer}, x, o)", "searchsortedlast(::AbstractRange{<:Integer}, x, o)", "searchsorted(::AbstractRange{<:Real}, x, o)"]
    statement := "On every empty integer range, searchsortedfirst returns 1 and searchsortedlast returns 0 (searchsorted returns 1:0), for every x and ordering."
    source := "base/sort.jl:353-354, 392-393 (docstrings: lastindex(v)+1 and firstindex(v)-1); an empty range is sorted under every order", status := .refuted
    prop := ``RangeSearchEmptyCorrect, thm := some ``rangeSearchEmptyCorrect_refuted
    issue := "none found (related: #35272, #18653 reversed-range inconsistencies; queries: searchsorted empty range, searchsortedfirst empty range, searchsorted rev range, searchsorted empty)"
    notes := "An empty range whose stored step points against the order (1:0 with rev=true, or 1:-1:2 with Forward) passes both guards because last(r) is first(r)-1 (or +1), and the fld/cld formula returns 0 or 1: searchsortedfirst(1:0, 0; rev=true) == 0, searchsorted(5:4, 5; rev=true) == 1:1, searchsorted(1:-1:2, 2) == 0:0. Same on 1.13.2." },
  { id := "sort-partialsort-reversed-range", juliaFile := "base/sort.jl"
    juliaFns := ["partialsort!(v, k::OrdinalRange)", "partialsort(v, k::OrdinalRange)", "ScratchQuickSort(r::OrdinalRange)"]
    statement := "partialsort(v, k) returns sort(v)[k] for every range k of valid indices."
    source := "base/sort.jl:116-120 (partialsort! docstring: k may be any range in Union{Integer,OrdinalRange}; values at those indices as if fully sorted)", status := .refuted
    prop := ``PartialsortRangeCorrect, thm := some ``partialsortRangeCorrect_refuted
    issue := "none found (queries: partialsort range, partialsort reversed range, partialsortperm)"
    notes := "ScratchQuickSort(r) keeps (first(r), last(r)) (sort.jl:1082), so for 5:-1:3 it sorts only around index 5 and skips the lower part when the pivot lands at 4 or 5 (sort.jl:1140-1144). Also wrong for strided descending ranges (9:-2:3) and in partialsortperm. The model uses Julia's pivot rule mod(hash(lo), lo:hi), checked against Julia (pivot 15 for 1:22). Same on 1.13.2." },
  { id := "sort-partialsort-empty-range", juliaFile := "base/sort.jl"
    juliaFns := ["partialsort!(v, k::OrdinalRange)", "BracketedSort"]
    statement := "partialsort(v, k) with an empty range k returns an empty vector for every v."
    source := "base/sort.jl:116-120 (docstring); invariant: behaviour does not depend on length(v); it returns Int[] for length(v) < 260", status := .refuted
    prop := ``PartialsortEmptyRange, thm := some ``partialsortEmptyRange_refuted
    issue := "none found (queries: partialsort empty, partialsort non-empty, partialsort range)"
    notes := "For length(v) >= 260 BracketedSort evaluates minimum(target) (sort.jl:1286), which throws ArgumentError(\"range must be non-empty\"). partialsortperm does not use BracketedSort and returns an empty view. Same on 1.13.2." },
  { id := "sort-partialsortperm-index-type", juliaFile := "base/sort.jl"
    juliaFns := ["partialsortperm(v, k)"]
    statement := "partialsortperm(v, k) returns sortperm(v)[k] for every valid index k, whatever its integer type."
    source := "base/sort.jl:1825-1831 (docstring: equivalent to sortperm(...)[k])", status := .refuted
    prop := ``PartialsortpermIndexType, thm := some ``partialsortpermIndexType_refuted
    issue := "none found (queries: partialsortperm, partialsortperm Int8, partialsortperm InexactError, partialsortperm eltype)"
    notes := "The index vector is allocated as Vector{eltype(k)} (sort.jl:1854), so partialsortperm(zeros(128), Int8(3)) throws InexactError storing index 128; for shorter vectors it returns indices of type eltype(k). Same on 1.13.2." },
  { id := "sort-insertionsort-stable", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(v, ::InsertionSortAlg, o, kw)"]
    statement := "InsertionSort returns exactly the stable sort of its input for every strict weak order."
    source := "base/sort.jl:807-821 (InsertionSort docstring: stable)", status := .proven
    prop := ``InsertionSortCorrect, thm := some ``insertionSortCorrect },
  { id := "sort-scratchquicksort-stable", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(v, ::ScratchQuickSort, o, kw)", "partition!"]
    statement := "ScratchQuickSort without targets returns exactly the stable sort of its input, for every strict weak order and every pivot rule choosing an index in lo:hi (hence for Julia's mod(hash(lo), lo:hi))."
    source := "base/sort.jl:1051-1073 (ScratchQuickSort docstring: stable)", status := .proven
    prop := ``ScratchQuickSortCorrect, thm := some ``scratchQuickSortCorrect },
  { id := "sort-default-stable", juliaFile := "base/sort.jl"
    juliaFns := ["sort!(v; lt, by, rev, order)", "sort(v; ...)", "StableCheckSorted"]
    statement := "The default sort! for orderings that are not UIntMappable (any by/lt, or Perm as used by sortperm) returns exactly the stable sort, for every strict weak order and pivot rule."
    source := "base/sort.jl:1548-1561 (DEFAULT_STABLE: guaranteed stable); manual: the default sort is stable since Julia 1.9", status := .proven
    prop := ``SortGenericStable, thm := some ``sortGenericStable
    notes := "Covers the IsUIntMappable no-branch (StableCheckSorted(ScratchQuickSort())) after InitialOptimizations' Small{10}. The UIntMappable branch for BitInteger vectors under Forward/Reverse (CountingSort, RadixSort) is not modelled; there equivalent elements are identical, so stability is unobservable." }
]

end JuliaLean.Sort

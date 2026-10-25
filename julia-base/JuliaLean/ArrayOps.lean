import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.ArrayOps.Vec
import JuliaLean.ArrayOps.Pure
import JuliaLean.ArrayOps.VecProps
import JuliaLean.ArrayOps.PureProps
import JuliaLean.ArrayOps.VecProofs
import JuliaLean.ArrayOps.PureProofs
import JuliaLean.ArrayOps.PureProofs2
import JuliaLean.ArrayOps.Unique
import JuliaLean.ArrayOps.UniqueProofs

namespace JuliaLean.ArrayOps

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "arrayops-dequeue", juliaFile := "base/array.jl"
    juliaFns := ["push!(::Vector, x)", "pushfirst!(::Vector, x)", "pop!(::Vector)", "popfirst!(::Vector)"]
    statement := "push!/pushfirst! add at the ends; pop!/popfirst! remove and return the last/first element, and throw ArgumentError on an empty vector."
    source := "base/array.jl:1330-1355, 1659-1699, 1758-1776, 1804-1835 (docstrings)", status := .proven
    prop := ``DequeueSpec, thm := some ``dequeueSpec },
  { id := "arrayops-insert", juliaFile := "base/array.jl"
    juliaFns := ["insert!(::Vector, i::Integer, x)", "_growat!"]
    statement := "insert!(a, i, x) for an index of any integer type puts x at index i for 1 <= i <= length(a)+1, and otherwise throws BoundsError (InexactError when Int(i) fails) leaving a unchanged."
    source := "base/array.jl:1845-1865 (docstring: index is the index of item in the resulting a)", status := .proven
    prop := ``InsertSpec, thm := some ``insertSpec },
  { id := "arrayops-deleteat-index", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, i::Integer)", "_deleteat!(a, i, delta)"]
    statement := "deleteat!(a, i) for an index of any integer type removes a[i] when 1 <= i <= length(a), and otherwise throws BoundsError (InexactError when Int(i) fails) leaving a unchanged."
    source := "base/array.jl:1880-1898 (docstring)", status := .proven
    prop := ``DeleteatIndexSpec, thm := some ``deleteatIndexSpec },
  { id := "arrayops-deleteat-range-inbounds", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, r::AbstractUnitRange{<:Integer})", "_deleteat!(a, i, delta)"]
    statement := "deleteat!(a, lo:hi) does nothing for an empty range and removes exactly a[lo:hi] for 1 <= lo <= hi <= length(a), for unit ranges of every integer type."
    source := "base/array.jl:1916-1944 (docstring)", status := .proven
    prop := ``DeleteatRangeInBounds, thm := some ``deleteatRangeInBounds },
  { id := "arrayops-deleteat-range-overflow", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, r::AbstractUnitRange{<:Integer})", "_deleteat!(a, i, delta)"]
    statement := "deleteat!(a, lo:hi) for a unit range of any integer type with Int-representable endpoints either removes a[lo:hi] (in bounds), does nothing (empty), or throws BoundsError leaving a unchanged."
    source := "base/array.jl:1916-1944 (docstring); invariant: index arithmetic does not wrap, out-of-bounds deletion is a BoundsError (base/array.jl:1316-1317)", status := .refuted
    prop := ``DeleteatRangeSpec, thm := some ``deleteatRangeSpec_refuted
    issue := "none found (related: #22055 closed, deleteat! should always throw BoundsError; queries: deleteat overflow, deleteat typemax, deleteat! BoundsError, deleteat)"
    notes := "_deleteat!(a, i, delta) checks i + delta <= len + 1 (array.jl:1317) in wrapping Int arithmetic: for 1:typemax(Int), 1 + typemax(Int) wraps negative, the check passes, and _deletebeg! throws ArgumentError(\"_deletebeg! requires delta in 0:length(a)\"). For k:typemax(Int) with k >= 2 the error is a BoundsError on a MemoryRef at an index near typemax; UInt ranges ending at typemax(UInt) give InexactError. a is left unchanged. Same on 1.13.2." },
  { id := "arrayops-deleteat-sorted", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, inds::AbstractVector)", "_deleteat!(a, inds)"]
    statement := "deleteat!(a, inds) for sorted, unique, in-bounds inds::Vector{Int} removes exactly the elements at those positions."
    source := "base/array.jl:1916-1944 (docstring: inds is a collection of sorted and unique integer indices)", status := .proven
    prop := ``DeleteatSortedSpec, thm := some ``deleteatSortedSpec },
  { id := "arrayops-deleteat-error-partial", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, inds)", "_deleteat!(a, inds)", "keepat!(::Vector, inds)", "splice!(::Vector, inds)"]
    statement := "When deleteat!(a, inds) throws because inds is unsorted, repeated or out of bounds, a is unchanged."
    source := "invariant: argument validation errors leave the argument untouched; the docstring example base/array.jl:1939-1942 shows the ArgumentError as a plain rejection", status := .refuted
    prop := ``DeleteatErrorUnchanged, thm := some ``deleteatErrorUnchanged_refuted
    issue := "none found (related: #7642 closed, same philosophy for convert errors; #54401 bounds checks in keepat!/deleteat!; queries: deleteat unsorted, deleteat error state, deleteat partially modified, keepat error, deleteat)"
    notes := "_deleteat!(a, inds) (array.jl:1970-2002) compacts a while it walks inds and validates each index only when it reaches it, so deleteat!([10,20,30,40], [1,3,5]) throws BoundsError after a[1] = a[2], leaving [20,20,30,40]; [2,4,1] leaves [10,30,30,40]. keepat! (abstractarray.jl:3699-3715) and splice!(a, inds) behave the same way (keepat!([10,20,30,40], [2,4,3]) leaves [20,40,30,40]). Same on 1.13.2." },
  { id := "arrayops-deleteat-mask", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, inds::AbstractVector{Bool})"]
    statement := "deleteat!(a, mask) with a Bool vector of length(a) removes the entries marked true; another length throws BoundsError leaving a unchanged."
    source := "base/array.jl:1916-1944 (docstring: a boolean vector of the same length as a)", status := .proven
    prop := ``DeleteatMaskSpec, thm := some ``deleteatMaskSpec },
  { id := "arrayops-keepat-sorted", juliaFile := "base/abstractarray.jl"
    juliaFns := ["keepat!(::Vector, inds)", "_keepat!(a, inds)"]
    statement := "keepat!(a, inds) for sorted, unique, in-bounds inds::Vector{Int} leaves exactly a[inds]."
    source := "base/array.jl:3109-3133 (docstring)", status := .proven
    prop := ``KeepatSortedSpec, thm := some ``keepatSortedSpec },
  { id := "arrayops-filter-bang", juliaFile := "base/array.jl"
    juliaFns := ["filter!(f, a::AbstractVector)"]
    statement := "filter!(f, a) keeps exactly the elements for which f is true, in order."
    source := "base/array.jl:3049-3065 (docstring)", status := .proven
    prop := ``FilterBangSpec, thm := some ``filterBangSpec },
  { id := "arrayops-splice-range", juliaFile := "base/array.jl"
    juliaFns := ["splice!(::Vector, r::AbstractUnitRange{<:Integer}, ins)"]
    statement := "splice!(a, f:l, ins) for 1 <= f <= l+1 <= length(a)+1 (including the empty range f:f-1) returns a[f:l] and replaces it by ins."
    source := "base/array.jl:2088-2124 (docstring: splice!(collection, n:n-1, replacement) inserts before n)", status := .proven
    prop := ``SpliceRangeSpec, thm := some ``spliceRangeSpec },
  { id := "arrayops-resize", juliaFile := "base/array.jl"
    juliaFns := ["resize!(::Vector, n::Integer; first)"]
    statement := "resize!(a, n; first) for n of any integer type throws ArgumentError for n < 0 and otherwise yields length n, keeping the first (first=false) or last (first=true) min(n, length(a)) elements, with new slots unassigned."
    source := "base/array.jl:1527-1563 (docstring)", status := .proven
    prop := ``ResizeSpec, thm := some ``resizeSpec
    notes := "The first keyword is new in 1.14 (absent in 1.13.2)." },
  { id := "arrayops-append-self", juliaFile := "base/array.jl"
    juliaFns := ["append!(::Vector, items::AbstractVector)", "prepend!(::Vector, items::AbstractVector)"]
    statement := "append!(a, a) and prepend!(a, a) with a single collection give vcat(a, a)."
    source := "base/array.jl:1389-1424, 1454-1482 (docstrings); prepend! special-cases items === a (array.jl:1488-1496)", status := .proven
    prop := ``AppendSelfSpec, thm := some ``appendSelfSpec },
  { id := "arrayops-append-many-self", juliaFile := "base/array.jl"
    juliaFns := ["append!(a::AbstractVector, iter...)", "prepend!(a::AbstractVector, iter...)"]
    statement := "append!(a, cs...) and prepend!(a, cs...) return vcat(a, cs...) and vcat(cs..., a) of the values before the call, also when some collection is a itself."
    source := "base/array.jl:1389-1424 (append! docstring: add the elements of each collection; the result of the example equals push!(a, items...)), 1454-1482 (prepend!)", status := .refuted
    prop := ``AppendManySpec, thm := some ``appendManySpec_refuted
    issue := "none found (queries: append aliasing, append itself, append! aliasing, append! multiple, prepend aliasing, prepend!)"
    notes := "append!(a, iter...) = foreach(v -> append!(a, v), iter) (array.jl:1437) re-reads a after each step, so a = [1,2,3]; append!(a, a, a) has 12 elements, not 9 (push!(a, a..., a...) has 9). prepend!(a, a, a) also gives 12. append!(a, a) and prepend!(a, a) alone are correct. Same on 1.13.2." },
  { id := "arrayops-reverse-window", juliaFile := "base/array.jl"
    juliaFns := ["reverse!(v::AbstractVector, start::Integer, stop::Integer)"]
    statement := "reverse!(v, start, stop) for indices of any integer type reverses exactly v[start:stop] when 1 <= start <= stop <= length(v), and leaves v unchanged when stop <= start."
    source := "base/array.jl:2291-2316 (docstring), 2212-2252 (reverse(v, start, stop) docstring)", status := .proven
    prop := ``ReverseBangSpec, thm := some ``reverseBangSpec },
  { id := "arrayops-reverse-window-inconsistent", juliaFile := "base/array.jl"
    juliaFns := ["reverse(v::AbstractVector, start::Integer, stop::Integer)", "reverse!(v::AbstractVector, start::Integer, stop::Integer)"]
    statement := "reverse(v, start, stop) returns what reverse!(copy(v), start, stop) leaves, or throws the same exception, for all indices."
    source := "base/array.jl:2291-2293 (reverse! docstring: in-place version of reverse)", status := .refuted
    prop := ``ReverseCopyAgrees, thm := some ``reverseCopyAgrees_refuted
    issue := "none found (queries: reverse start stop, reverse! bounds, reverse!)"
    notes := "reverse! only checks bounds when stop > start (array.jl:2319), so reverse!([1,2,3], 5, 5) returns the vector; reverse copies v[firstindex:start-1] and v[stop+1:end] element by element (array.jl:2256-2264) and throws BoundsError at index 4. Also reverse(Int[], 5, 5) throws while reverse!(Int[], 5, 5) returns. Same on 1.13.2." },
  { id := "arrayops-circshift", juliaFile := "base/abstractarray.jl"
    juliaFns := ["circshift!(a::AbstractVector, shift::Integer)", "circshift(a::AbstractArray, shift::Real)", "circshift!(dest, src, shifts)"]
    statement := "circshift!(v, k) and circshift(v, k) rotate right by mod(k, length(v)) for shifts of every integer type, including typemin and typemax."
    source := "base/abstractarray.jl:3731-3755, base/abstractarraymath.jl:339-410 (docstrings)", status := .proven
    prop := ``CircshiftSpec, thm := some ``circshiftSpec },
  { id := "arrayops-repeat", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["repeat(A::AbstractArray; inner, outer)", "repeat_inner", "repeat_outer"]
    statement := "repeat(v; inner, outer) with nonnegative Int counts repeats entries inner times and the whole outer times, and throws OverflowError exactly when the result length exceeds typemax(Int)."
    source := "base/abstractarraymath.jl:449-481 (docstring)", status := .proven
    prop := ``RepeatSpec, thm := some ``repeatSpec
    notes := "repeat(Int[], typemax(Int)) passes the overflow check (length 0) and then loops typemax(Int) times (about 1 ns per iteration), which is a hang in practice; not filed. 1.13.2 multiplies the counts without overflow checks (base/abstractarraymath.jl:571, 596 on v1.13.2), so repeat([1,2,3]; inner=typemax(Int)) throws ArgumentError there; master uses checked_mul." },
  { id := "arrayops-copyto-alias", juliaFile := "base/array.jl"
    juliaFns := ["copyto!(dest::Array, doffs, src::Array, soffs, n)", "_copyto_impl!"]
    statement := "copyto!(a, doffs, a, soffs, n) on one array equals copying from an unaliased copy, for overlapping blocks in both directions and offsets/counts of any integer type; n == 0 is a no-op and n < 0 an ArgumentError."
    source := "base/array.jl:282-286 (copyto! docstring)", status := .proven
    prop := ``CopytoAliasSpec, thm := some ``copytoAliasSpec },
  { id := "arrayops-find-inrange", juliaFile := "base/array.jl"
    juliaFns := ["findnext(testf::Function, A, start)", "findprev(testf::Function, A, start)"]
    statement := "findnext(f, v, i) for i >= 1 and findprev(f, v, i) for i <= length(v), of any integer type, return the next (previous) matching index after (before) or including i, or nothing."
    source := "base/array.jl:2446-2474, 2634-2670 (docstrings)", status := .proven
    prop := ``FindInRange, thm := some ``findInRange },
  { id := "arrayops-findnext-start-below", juliaFile := "base/array.jl"
    juliaFns := ["findnext(testf::Function, A, start)", "findprev(testf::Function, A, start)"]
    statement := "findnext(f, v, i) and findprev(f, v, i) return the next/previous matching index after/before or including i for every Int start i."
    source := "base/array.jl:2446-2474 (findnext docstring: the next index after or including i), 2634-2670 (findprev)", status := .refuted
    prop := ``FindAllStarts, thm := some ``findAllStarts_refuted
    issue := "#40120 (open PR: fix inconsistencies of findnext and findprev); related: #54584 (open, strings), #33100 (closed); queries: findnext BoundsError, findprev, findnext out of bounds, findnext start index"
    notes := "findnext returns nothing for any start past the end but reads A[i] for a start below firstindex, so findnext(iseven, [1,2], 0) throws BoundsError; findprev mirrors it (findprev(iseven, [1,2], 3) throws, findprev(iseven, [1,2], 0) returns nothing). maybe_intended: starts outside the indices are errors; then the other side should throw too. Same on 1.13.2." },
  { id := "arrayops-find-extrema", juliaFile := "base/reduce.jl"
    juliaFns := ["findmax(itr)", "findmin(itr)", "argmax(itr)", "argmin(itr)"]
    statement := "For Float64 vectors findmax returns the first element that no element is isless-greater than (NaN is greatest, -0.0 < 0.0) with its index, findmin the first minimal one with NaN least; both throw ArgumentError on empty input."
    source := "base/reduce.jl:855-879, 921-945 (docstrings)", status := .proven
    prop := ``FindExtremaSpec, thm := some ``findExtremaSpec },
  { id := "arrayops-sum-prod", juliaFile := "base/reduce.jl"
    juliaFns := ["sum(::AbstractArray)", "prod(::AbstractArray)", "mapreduce_impl", "reduce_empty(add_sum, T)"]
    statement := "sum(v) and prod(v) for a vector of any BitInteger type equal the exact sum/product wrapped into Int/UInt (narrower types) or T, for every length including 0 (zero and one of that type)."
    source := "base/reduce.jl:545-600, 601-640 (sum/prod docstrings: integers narrower than the system word are promoted); invariant: the pairwise order does not change the result", status := .proven
    prop := ``SumProdSpec, thm := some ``sumProdSpec },
  { id := "arrayops-accumulate", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate(op, A; init)", "cumsum(::AbstractVector)"]
    statement := "accumulate(op, v; init) is [op(init, v1), op(op(init, v1), v2), ...] and cumsum of a BitInteger vector is the running sum wrapped into the widened type."
    source := "base/accumulate.jl:69-115, 234-280 (cumsum and accumulate docstrings; accumulate(+, [1,2,3]; init=100) == [101, 103, 106]; cumsum widens narrow integers)", status := .proven
    prop := ``AccumulateSpec, thm := some ``accumulateSpec },
  { id := "arrayops-diff", juliaFile := "base/multidimensional.jl"
    juliaFns := ["diff(::AbstractVector)"]
    statement := "diff(v) has length(v)-1 entries (0 for empty v) equal to v[i+1] - v[i] in the element type."
    source := "base/multidimensional.jl:1084-1112 (docstring)", status := .proven
    prop := ``DiffSpec, thm := some ``diffSpec },
  { id := "arrayops-vcat-ranges", juliaFile := "base/range.jl"
    juliaFns := ["vcat(rs::AbstractRange{T}...)"]
    statement := "vcat of Int unit ranges whose lengths fit in Int is the concatenation of their elements, or OverflowError when the total length exceeds typemax(Int)."
    source := "invariant: vcat of vectors concatenates (base/abstractarray.jl vcat docstring)", status := .proven
    prop := ``VcatRangesSpec, thm := some ``vcatRangesSpec
    notes := "For a range with 2^64 elements length wraps to 0 and vcat stores every element with @inbounds into an empty vector: vcat(typemin(Int):typemax(Int)) dies with signal 11 on 1.13.2 and master. Same root cause as ranges-collect-full-width-crash; not filed separately." },
  { id := "arrayops-getindex-checkbounds", juliaFile := "base/indices.jl"
    juliaFns := ["getindex(::Array, i::Integer)", "to_index(::Array, i::UInt)", "checkbounds(Bool, A, i)"]
    statement := "v[i] for an index of any BitInteger type that to_index accepts (every UInt, and values representable as Int) returns v[i] when checkbounds(Bool, v, i) and throws BoundsError otherwise."
    source := "base/abstractarray.jl:655-680 (checkbounds docstring), base/indices.jl:231-258 (to_index)", status := .proven
    prop := ``GetindexCheckbounds, thm := some ``getindexCheckbounds },
  { id := "arrayops-index-type-exception", juliaFile := "base/indices.jl"
    juliaFns := ["to_index(::Array, i::UInt)", "to_index(i::Integer)", "getindex(::LinearIndices, i)", "getindex(::CartesianIndices, i)", "getindex(::Array, i::Integer)"]
    statement := "Indexing a vector, LinearIndices(v) or CartesianIndices(v) with an out-of-range integer of any BitInteger type throws BoundsError."
    source := "invariant: checkbounds(Bool, v, i) is false for these indices, and v[UInt(2)^63] throws BoundsError", status := .refuted
    prop := ``OutOfRangeBoundsError, thm := some ``outOfRangeBoundsError_refuted
    issue := "none found (related: #35038 closed, to_index returning UInt; queries: to_index, to_index Int128, InexactError index, BoundsError reinterpret UInt, checkbounds)"
    notes := "to_index(A::Array, i::UInt) reinterprets (indices.jl:247) so v[UInt(2)^63] throws BoundsError (reporting index -9223372036854775808), but LinearIndices(v)[UInt(2)^63] and CartesianIndices(v)[UInt(2)^63] go through convert(Int, i) (indices.jl:258) and throw InexactError; v[Int128(2)^64] also throws InexactError. maybe_intended: to_index is documented to convert to Int. Same on 1.13.2." },
  { id := "arrayops-unique", juliaFile := "base/set.jl"
    juliaFns := ["unique(itr)", "allunique(A::StridedArray)", "_indexed_allunique", "_hashed_allunique", "allequal(itr)"]
    statement := "For Vector{Int}: unique(v) keeps the first occurrence of each value in order; allunique(v) is true exactly when no value repeats, including through the sorted fast path for 32 or more elements; allequal(v) is true exactly when all values are equal."
    source := "base/set.jl:200-223 (unique docstring), 480-514 (allunique), 609-647 (allequal)", status := .proven
    prop := ``UniqueSpec, thm := some ``uniqueSpec },
  { id := "arrayops-linear-cartesian-1d", juliaFile := "base/indices.jl"
    juliaFns := ["getindex(::LinearIndices{1}, i)", "getindex(::CartesianIndices{1}, i)", "LinearIndices(v)[CartesianIndex(i)]"]
    statement := "For a vector of length n and i::Int, LinearIndices(v)[CartesianIndices(v)[i]] == i for i in 1:n, and both conversions throw BoundsError outside 1:n."
    source := "base/indices.jl:429-475 (LinearIndices docstring), base/multidimensional.jl (CartesianIndices docstring)", status := .proven
    prop := ``LinearCartesianRoundTrip, thm := some ``linearCartesianRoundTrip }
]

end JuliaLean.ArrayOps

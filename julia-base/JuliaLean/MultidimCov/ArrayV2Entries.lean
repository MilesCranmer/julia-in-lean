import JuliaLean.MultidimCov.ArrayV2VectorProps
import JuliaLean.MultidimCov.ArrayV2Find
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ArrayV2

open JuliaLean.Registry

private def entry (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (notes : String := "") : Entry :=
  { id := s!"multidimcov-array-v2-{id}", juliaFile := "base/array.jl", juliaFns := fns,
    statement, source, status := .proven, prop, thm := some thm, notes }

private def refuted (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (issue notes : String) : Entry :=
  { id, juliaFile := "base/array.jl", juliaFns := fns, statement, source, status := .refuted,
    prop, thm := some thm, issue, notes }

def entries : List Entry := [
  entry "unsafe-copyto" ["unsafe_copyto!(::Array, doffs, ::Array, soffs, n)"]
    "For in-bounds windows unsafe_copyto! sets dest[doffs+k-1] to the old src[soffs+k-1] for k in 1:n (memmove semantics when src === dest) and leaves every other slot, the size and the offset unchanged."
    "docstring base/array.jl:266" ``P276 ``p276,
  entry "overallocation" ["overallocation(::Int)"]
    "For 0 <= n <= typemax(Int), overallocation(n) is at least n, at most typemax(Int), strictly larger than n when n < typemax(Int), and adds at most n/8 + 3*2^56."
    "invariant; comment at base/array.jl:1103-1108" ``P1102 ``p1102,
  entry "growbeg-internal" ["_growbeg_internal!(::Vector, ::Int, ::Int)"]
    "On a valid vector the new ref's window holds n + delta slots whose last n are the old elements; an inconsistent ref/size pair throws ConcurrencyViolationError."
    "invariant; error message at base/array.jl:1124" ``P1116 ``p1116,
  entry "growbeg" ["_growbeg!(::Vector, ::Integer)"]
    "_growbeg!(a, delta) throws ArgumentError for delta < 0 and otherwise yields a valid vector of length n + delta whose last n elements are the old ones."
    "invariant; error message at base/array.jl:1155" ``P1151 ``p1151,
  entry "growend-internal" ["_growend_internal!(::Vector, ::Int, ::Int)"]
    "On a valid vector the new ref's window holds n + delta slots whose first n are the old elements; an inconsistent ref/size pair throws ConcurrencyViolationError."
    "invariant; error message at base/array.jl:1179" ``P1171 ``p1171,
  entry "growend" ["_growend!(::Vector, ::Integer)"]
    "_growend!(a, delta) throws ArgumentError for delta < 0 and otherwise yields a valid vector of length n + delta whose first n elements are the old ones."
    "invariant; error message at base/array.jl:1215" ``P1212 ``p1212,
  entry "growat" ["_growat!(::Vector, ::Integer, ::Integer)"]
    "_growat!(a, i, delta) throws ArgumentError for delta < 0 and BoundsError for i outside 1:n+1; otherwise it opens delta slots before position i, keeping a[1:i-1] and a[i:n] (now at i+delta:n+delta)."
    "invariant; error messages at base/array.jl:1237-1238" ``P1230 ``p1230,
  entry "deletebeg" ["_deletebeg!(::Vector, ::Integer)"]
    "_deletebeg!(a, delta) throws ArgumentError unless 0 <= delta <= length(a), and otherwise leaves exactly a[delta+1:end]."
    "error message at base/array.jl:1283" ``P1278 ``p1278,
  entry "deleteend" ["_deleteend!(::Vector, ::Integer)"]
    "_deleteend!(a, delta) throws ArgumentError unless 0 <= delta <= length(a), and otherwise leaves exactly a[1:end-delta]."
    "error message at base/array.jl:1303" ``P1296 ``p1296,
  entry "deleteat-window" ["_deleteat!(::Vector, ::Integer, ::Integer)"]
    "_deleteat!(a, i, delta) throws ArgumentError for delta < 0 and BoundsError for i outside 1:n; for a window inside the vector it removes exactly a[i:i+delta-1]."
    "error messages at base/array.jl:1315-1317" ``P1312 ``p1312,
  entry "cartesian-access" ["getindex(::Array, ::Int, ::Int, ::Int...)", "setindex!(::Array{T}, x, ::Int, ::Int, ::Int...)",
      "_setindex!(::Array{T}, ::T, ::Int, ::Int, ::Int...)", "isassigned(::Array, ::Int...)"]
    "With two or more indices, any number of them: an index outside 1:d of its dimension, an extra index other than 1, or an omitted index for a dimension of size other than 1 throws BoundsError; otherwise A[I...] is the element at the column-major position of I, A[I...] = x writes exactly that slot (after conversion), and isassigned(A, I...) holds exactly when A[I...] returns."
    "manual (column-major storage; omitted and extra indices); isassigned docstring base/essentials.jl:1112" ``PCartesian ``pCartesian,
  entry "reverse-window" ["reverse(::AbstractVector, start, stop)"]
    "For 1 <= start <= stop+1 <= length(v)+1 (elements assigned), reverse(v, start, stop) is a new vector equal to v with v[start:stop] reversed."
    "docstring base/array.jl:2235" ``P2253 ``p2253,
  entry "reverse-dims" ["reverse(::AbstractVector; dims)", "reverse!(::AbstractVector; dims)", "_reverse(A, ::Colon)",
      "_reverse(A, ::Tuple{Integer})", "_reverse(A, ::Integer)", "_reverse!(A, ::Colon)", "_reverse!(A, ::Tuple{Integer})",
      "_reverse!(A, ::Integer)"]
    "reverse(v; dims) and reverse!(v; dims) with dims = :, 1 or (1,) reverse the whole vector; every other dimension throws ArgumentError."
    "docstrings base/array.jl:2214, 2292" ``P2271 ``p2271,
  entry "reverseind" ["reverseind(::AbstractVector, ::Integer)"]
    "For i in 1:n, reverseind(v, i) = n + 1 - i is in 1:n, is an involution, and v[reverseind(v, i)] == reverse(v)[i]."
    "docstring base/array.jl:2276" ``P2281 ``p2281,
  entry "reverse-bang" ["reverse!(::AbstractVector, start, stop)"]
    "reverse!(v, start, stop) leaves v unchanged when stop <= start, throws BoundsError when a non-trivial window leaves 1:length(v), and otherwise reverses v[start:stop] in place."
    "docstring base/array.jl:2292" ``P2317 ``p2317,
  entry "push" ["push!(::Vector{T}, item)", "_push!(::Vector{T}, ::T)", "push!(::Vector{Any}, x)",
      "push!(::Vector{Any}, x...)", "_pushfirst!(::Vector{T}, ::T)", "pushfirst!(::Vector{Any}, x)",
      "pushfirst!(::Vector{Any}, x...)"]
    "push! appends the converted items after every old element and pushfirst! puts them before, old elements keeping their order; a failing conversion propagates."
    "docstrings base/array.jl:1330, 1757" ``PPush ``pPush,
  entry "append" ["append!(::Vector{T}, ::Union{AbstractVector{<:T},Tuple})", "push!(::AbstractVector, iter...)"]
    "append!(a, items) is a's old elements followed by items (converted for a Tuple), self-append doubling a; a failing tuple conversion propagates before a grows."
    "docstring base/array.jl:1383" ``P1427 ``p1427,
  entry "prepend" ["prepend!(::Vector{T}, ::Union{AbstractVector{<:T},Tuple})", "pushfirst!(::AbstractVector, iter...)"]
    "prepend!(a, items) is items (converted for a Tuple) followed by a's old elements, self-prepend doubling a."
    "docstring base/array.jl:1455" ``P1485 ``p1485,
  entry "resize" ["resize!(::Vector, ::Integer; first)"]
    "resize! rejects negative lengths with ArgumentError, keeps the first (with first=true the last) n elements when shrinking, and keeps every old element after (first=true) or before the new slots when growing."
    "docstring base/array.jl:1527" ``P1564 ``p1564 (notes := "The first keyword is master-only (1.14); 1.13.2 has no such method."),
  { id := "multidimcov-sizehint-first-empty", juliaFile := "base/array.jl",
    juliaFns := ["sizehint!(::Vector, ::Integer; first, shrink)"],
    statement := "sizehint!(a, sz; first, shrink) returns a with unchanged contents for every 0 <= sz that memory can hold.",
    source := "docstring base/array.jl:1581", status := .proven, prop := ``P1617, thm := some ``p1617,
    notes := "The target's len != 0 guard fixes the historical empty-vector BoundsError." },
  entry "kwcall-sizehint" ["Core.kwcall(::NamedTuple, ::typeof(sizehint!), a, sz)"]
    "The generic keyword sizehint! accepts first/shrink only as Bool (TypeError otherwise), rejects other keywords with MethodError, and otherwise is exactly sizehint!(a, sz)."
    "invariant (base/array.jl:1652)" ``P1652 ``p1652,
  entry "pop" ["pop!(::Vector)", "popfirst!(::Vector)"]
    "pop!/popfirst! throw ArgumentError on an empty vector and otherwise return and remove the last/first element, keeping the others in order."
    "docstrings base/array.jl:1660, 1802" ``P1700 ``p1700,
  entry "popat" ["popat!(::Vector, ::Integer)", "popat!(::Vector, ::Integer, default)"]
    "popat!(a, i) throws BoundsError (popat!(a, i, default) returns default, a unchanged) outside 1:length(a); otherwise a[i] is returned and removed."
    "docstring base/array.jl:1716" ``P1741 ``p1741,
  entry "insert" ["insert!(::Vector{T}, ::Integer, item)", "_insert!(::Vector{T}, ::Integer, ::T)"]
    "insert! converts first (errors propagate), throws BoundsError outside 1:length(a)+1, and otherwise puts the item at index i with the old elements around it in order."
    "docstring base/array.jl:1847" ``P1866 ``p1866,
  entry "deleteat-index-range" ["deleteat!(::Vector, ::Integer)", "deleteat!(::Vector, ::AbstractUnitRange{<:Integer})", "empty!(::Vector)"]
    "deleteat!(a, i) and deleteat!(a, lo:hi) inside 1:length(a) remove exactly those elements; an empty range changes nothing; an out-of-range index is a BoundsError; empty! removes everything."
    "docstrings base/array.jl:1884, 2141" ``PDeleteat ``pDeleteat,
  entry "find-pure" ["findnext(testf::Function, A, start)", "findfirst(testf::Function, A)",
      "findfirst(testf::Function, A::Union{AbstractArray, AbstractString})", "findprev(testf::Function, A, start)",
      "findlast(testf::Function, A)", "findlast(testf::Function, A::Union{AbstractArray, AbstractString})",
      "findall(testf::Function, A)", "findall(testf::F, A::AbstractArray)"]
    "On a vector, findfirst/findlast(q, v) are the first/last i of pairs(v) with q(v[i]), findnext(q, v, s)/findprev(q, v, s) the first i >= s / last i <= s for every index s of v, and findall(q, v) all such i in increasing order."
    "docstrings base/array.jl:2447, 2489, 2635, 2685, 2739" ``PFindPure ``pFindPure
    (notes := "Starts outside the indices of v are the refuted entry arrayops-findnext-start-below."),
  entry "find-call-order" ["findfirst(testf::Function, A)", "findfirst(testf::Function, A::Union{AbstractArray, AbstractString})",
      "findlast(testf::Function, A)", "findlast(testf::Function, A::Union{AbstractArray, AbstractString})",
      "findall(testf::Function, A)", "findall(testf::F, A::AbstractArray)"]
    "A throwing predicate: findfirst throws the error of the first element after only false results, findlast that of the last element after only false results from the end, findall that of the first throwing element."
    "invariant (iteration order of pairs(A), docstrings base/array.jl:2489, 2685, 2739)" ``PFindErr ``pFindErr,
  entry "find-bool" ["findnext(A, start)", "findfirst(A)", "findfirst(A::AbstractArray)", "findprev(A, start)",
      "findlast(A)", "findlast(A::AbstractArray)", "findall(A)", "findall(A::AbstractArray{Bool})"]
    "For a Bool vector, findfirst/findlast/findnext/findprev/findall locate the true entries of pairs(A): first, last, first at or after s, last at or before s (s an index), and all in order."
    "docstrings base/array.jl:2407, 2558, 2594, 2799" ``PFindBool ``pFindBool
    (notes := "Starts outside the indices are the refuted entry arrayops-findnext-start-below.")
]

end JuliaLean.MultidimCov.ArrayV2

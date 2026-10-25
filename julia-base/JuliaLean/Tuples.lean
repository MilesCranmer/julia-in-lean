import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Tuples.Model
import JuliaLean.Tuples.NamedTuple
import JuliaLean.Tuples.Props
import JuliaLean.Tuples.Lemmas
import JuliaLean.Tuples.Refutations
import JuliaLean.Tuples.ProofsBasic
import JuliaLean.Tuples.ProofsCompare
import JuliaLean.Tuples.ProofsNT
import JuliaLean.Tuples.Validation
import JuliaLean.Tuples.Circshift

namespace JuliaLean.Tuples

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "tuples-split-rest-state", juliaFile := "base/tuple.jl"
    juliaFns := ["split_rest(t::Tuple, n, i)", "_split_tuple", "split_rest(t::NamedTuple, n, st...)", "a, b..., c = t"]
    statement := "For every valid iteration state 1 <= i <= length(t)+1 and n >= 0, Base.split_rest(t, n, i) on a tuple or named tuple agrees with split_rest on the corresponding Vector: the same values, or the same exception type."
    source := "base/tuple.jl:215-246 (split_rest docstring: the tail of the collection starting from itr_state, split into all but the last n and the last n); manual, destructuring assignment"
    status := .refuted, prop := ``SplitRestAgrees, thm := some ``splitRestAgrees_refuted
    issue := "none found (related: #47326, #59611; queries: split_rest, split_rest NamedTuple, slurping tuple, destructuring slurp middle)"
    notes := "_split_tuple(t, length(t)-n, i) computes the split point from length(t) instead of length(t)-i+1 (tuple.jl:265-267), so it never checks that the rest holds n elements and returns already consumed elements: split_rest((1,), 1, 2) == ((), (1,)), hence `a, b..., c = (1,)` binds a = 1, b = (), c = 1 (theorem destructureMid_duplicates); for a tuple literal on the right-hand side lowering throws BoundsError instead. The NamedTuple method (namedtuple.jl:585-589) checks length(t) < n on the whole named tuple and then calls the tuple method on the names (theorem splitRestNT_refuted). Vectors and strings throw ArgumentError. Same on 1.13.2." },
  { id := "tuples-namedtuple-haskey-integer", juliaFile := "base/namedtuple.jl"
    juliaFns := ["haskey(nt::NamedTuple, key::Union{Integer,Symbol})", "get(nt::NamedTuple, key::Union{Integer,Symbol}, default)", "get(f, nt::NamedTuple, key)"]
    statement := "haskey(nt, k) and get(nt, k, d) accept every Integer key, as their signatures declare: haskey is 1 <= k <= length(nt), and get returns the field or the default."
    source := "base/namedtuple.jl:384-386 (signatures key::Union{Integer, Symbol})"
    status := .refuted, prop := ``HaskeyInteger, thm := some ``haskeyInteger_refuted
    issue := "none found (queries: haskey NamedTuple, NamedTuple get Integer, isdefined Int32)"
    notes := "Both methods call isdefined(nt, key), which accepts only Int and Symbol: haskey((a=1,), Int32(1)), haskey((a=1,), 0x01), haskey((a=1,), big(1)), haskey((a=1,), true) and get with those keys throw TypeError. By contrast getindex(nt, i) is declared for i::Int only (namedtuple.jl:165), so (a=1,)[0x01] is a MethodError, while tuples accept any Integer position. Same on 1.13.2." },
  { id := "tuples-findall-in-isequal", juliaFile := "base/array.jl"
    juliaFns := ["findall(pred::Fix2{typeof(in)}, x::Tuple)", "findall(pred::Fix2{typeof(in)}, x::AbstractArray)", "_findin"]
    statement := "findall(in(b), t) returns the indices i with t[i] in b, i.e. it equals findall(x -> x in b, t), for tuples of Float64 and Vector b."
    source := "base/array.jl (findall docstring: indices for which f returns true); in(x) is the curried form of in, which compares with =="
    status := .refuted, prop := ``FindallInAgrees, thm := some ``findallInAgrees_refuted
    issue := "none found (related: #29124, #52639; queries: _findin, findall in isequal, findall in NaN, findall in -0.0)"
    notes := "The specialised methods (array.jl:2964-2967) call _findin(x, pred.x), which converts b to a Set (array.jl:2910) and so matches with isequal instead of ==: findall(in([0.0]), (-0.0,)) == Int[] although -0.0 in [0.0], and findall(in([NaN]), (NaN,)) == [1] although NaN in [NaN] is false; findall(in([missing]), (missing,)) == [1] where the predicate is missing. The sorted Array{<:Real} path _sortedfindin uses isless and behaves the same way. Same on 1.13.2." },
  { id := "tuples-getindex-bool", juliaFile := "base/tuple.jl"
    juliaFns := ["getindex(t::Tuple, i::Integer)", "setindex(t::Tuple, v, i::Integer)", "get(t::Tuple, i::Integer, default)", "isassigned(v::Tuple, i::Integer)"]
    statement := "Indexing a tuple with a Bool scalar (getindex, Base.setindex, get, isassigned) throws ArgumentError, as the same operations on a Vector or range do."
    source := "base/indices.jl:259 (to_index(i::Bool) throws \"invalid index: true of type Bool\"); base/range.jl:946-949 (isassigned(r, ::Bool) throws)"
    status := .refuted, prop := ``BoolIndexAgrees, thm := some ``boolIndexAgrees_refuted
    issue := "none found (queries: tuple index Bool, getindex tuple Bool, invalid index Bool tuple)"
    notes := "The tuple methods take i::Integer and convert(Int, i), so (10, 20)[true] == 10, get((1, 2), true, 0) == 1, Base.setindex((1, 2), 0, true) == (0, 2) and isassigned((1, 2), true) == true, while [10, 20][true], get([1, 2], true, 0) and isassigned([1, 2], true) throw ArgumentError. isassigned(::Tuple) is new in 1.13. Same on 1.13.2." },
  { id := "tuples-getindex-bool-range", juliaFile := "base/range.jl"
    juliaFns := ["getindex(t::Tuple, r::AbstractUnitRange)", "getindex(t::Tuple, b::AbstractArray{Bool,1})"]
    statement := "Indexing a tuple with a UnitRange{Bool} agrees with indexing it by the same Bool values collected into a Vector{Bool} (logical indexing)."
    source := "base/tuple.jl:37 (logical indexing for AbstractArray{Bool,1}); base/array.jl:993 (Vector: getindex(a::Array, r::AbstractUnitRange{Bool}) = getindex(a, to_index(r)))"
    status := .refuted, prop := ``BoolRangeLogical, thm := some ``boolRangeLogical_refuted
    issue := "none found (queries: tuple index Bool, getindex tuple UnitRange Bool)"
    notes := "A UnitRange{Bool} dispatches to getindex(t::Tuple, r::AbstractUnitRange) (range.jl:451-466), which treats it as an integer range: (10, 20)[false:true] reads t[0] and throws BoundsError, and (1, 2, 3)[true:true] == (1,), while (10, 20)[[false, true]] == (20,), [10, 20][false:true] == [20] and [1, 2, 3][true:true] throws BoundsError. Same on 1.13.2." },
  { id := "tuples-getindex-inexact", juliaFile := "base/tuple.jl"
    juliaFns := ["getindex(t::Tuple, i::Integer)"]
    statement := "t[i] throws BoundsError for every integer index i outside 1:length(t), as Base.setindex(t, v, i) does."
    source := "base/tuple.jl:43-54 (setindex docstring: throws a BoundsError when out of bounds); manual: indexing out of bounds throws BoundsError"
    status := .refuted, prop := ``GetindexBoundsError, thm := some ``getindexBoundsError_refuted
    issue := "none found (queries: tuple getindex InexactError, tuple index UInt64)"
    notes := "getindex(t, i::Integer) converts i to Int before the bounds check (tuple.jl:34): (1, 2)[typemax(UInt)] throws InexactError, while Base.setindex((1, 2), 0, typemax(UInt)), get and isassigned compare exactly, and [1, 2][typemax(UInt)] throws BoundsError. Int128/UInt128 indices outside Int throw InexactError for Vectors too. Same on 1.13.2." },
  { id := "tuples-prod-empty", juliaFile := "base/tuple.jl"
    juliaFns := ["prod(x::Tuple{})", "prod(f, t::Tuple)", "sum(::Tuple{})"]
    statement := "prod(t) agrees with prod(identity, t) for every tuple t of Int."
    source := "base/reduce.jl (prod docstring: prod(f, itr) and prod(itr) are the same reduction; an empty collection needs init unless the element type determines the identity)"
    status := .refuted, prop := ``ProdAgrees, thm := some ``prodAgrees_refuted
    issue := "none found (queries: prod empty tuple, sum empty tuple)"
    notes := "prod(x::Tuple{}) = 1 (tuple.jl:688) special-cases the empty tuple, while prod(identity, ()), reduce(*, ()), prod(Union{}[]) and sum(()) throw ArgumentError (reducing over an empty collection). Same on 1.13.2." },
  { id := "tuples-ntuple", juliaFile := "base/ntuple.jl"
    juliaFns := ["ntuple(f, n::Int)", "ntuple(f, n::Integer)", "ntuple(f, ::Val{N})", "_ntuple"]
    statement := "ntuple(f, n) for n of any BitInteger type returns (f(1), ..., f(n)), throws ArgumentError for negative n and InexactError when n is not representable as Int; ntuple(f, Val(N)) likewise."
    source := "base/ntuple.jl:5-16, 48-64 (docstrings); base/ntuple.jl:38, 66 (length should be >= 0)"
    status := .proven, prop := ``NtupleCorrect, thm := some ``ntupleCorrect },
  { id := "tuples-fill-to-length", juliaFile := "base/ntuple.jl"
    juliaFns := ["fill_to_length(t, val, ::Val{N})"]
    statement := "Base.fill_to_length(t, v, Val(N)) pads t with v to length N (all specialised methods agree) and throws ArgumentError when length(t) > N."
    source := "invariant: base/tuple.jl:441-445 (type-stable padding) and base/ntuple.jl:74-85"
    status := .proven, prop := ``FillToLengthCorrect, thm := some ``fillToLengthCorrect },
  { id := "tuples-reverse", juliaFile := "base/tuple.jl"
    juliaFns := ["reverse(t::Tuple)", "revargs", "reverse(t::NTuple)"]
    statement := "Both reverse methods (revargs and the NTuple method) reverse the tuple."
    source := "invariant: reverse; base/tuple.jl:668-671, base/ntuple.jl:89-93"
    status := .proven, prop := ``ReverseCorrect, thm := some ``reverseCorrect },
  { id := "tuples-front-tail", juliaFile := "base/tuple.jl"
    juliaFns := ["front(t)", "front(t::NTuple{32})", "front(t::Any32)", "tail(t)", "first(t::Tuple)", "last(t::Tuple)"]
    statement := "Base.front, Base.tail, first and last return all but the last element, all but the first, the first and the last element of a tuple of any length; on () front, tail and first throw ArgumentError and last throws BoundsError."
    source := "base/tuple.jl:328-343 (front docstring), base/essentials.jl:525-540 (tail docstring)"
    status := .proven, prop := ``FrontTailCorrect, thm := some ``frontTailCorrect },
  { id := "tuples-integer-index", juliaFile := "base/tuple.jl"
    juliaFns := ["getindex(t::Tuple, i::Int)", "getindex(t::Tuple, i::Integer)", "setindex(t::Tuple, v, i::Integer)", "get(t::Tuple, i::Integer, default)", "isassigned(v::Tuple, i::Integer)"]
    statement := "For scalar indices of every BitInteger type, t[i] is the element for 1 <= i <= length(t), else BoundsError (InexactError when i is not an Int); Base.setindex replaces the element or throws BoundsError; get returns the element or the default; isassigned tests 1 <= i <= length(t)."
    source := "base/tuple.jl:43-54 (setindex docstring), base/tuple.jl:673-680 (isassigned docstring)"
    status := .proven, prop := ``IntegerIndexCorrect, thm := some ``integerIndexCorrect },
  { id := "tuples-unitrange-index", juliaFile := "base/range.jl"
    juliaFns := ["getindex(t::Tuple, r::AbstractUnitRange)"]
    statement := "t[a:b] for Int endpoints, including the front/tail shortcuts for ranges longer than 10, agrees with Vector indexing: the slice when a:b is empty or inside 1:length(t), else BoundsError."
    source := "invariant: base/range.jl:450-466 (constant-foldable tuple indexing, same values as the generic method base/tuple.jl:36)"
    status := .proven, prop := ``UnitRangeIndexCorrect, thm := some ``unitRangeIndexCorrect },
  { id := "tuples-map", juliaFile := "base/tuple.jl"
    juliaFns := ["map(f, t::Tuple)", "map(f, t::Any32)", "map(f, t::Tuple, s::Tuple)", "map(f, t::Any32, s::Any32)", "map(f, t1, t2, ts...)"]
    statement := "map over one, two or three tuples of any lengths applies f elementwise and stops at the shortest tuple, as map over Vectors does."
    source := "map docstring (base/abstractarray.jl): iteration stops when any collection is exhausted"
    status := .proven, prop := ``MapCorrect, thm := some ``mapCorrect },
  { id := "tuples-find-filter", juliaFile := "base/tuple.jl"
    juliaFns := ["findfirst(f::Function, t::Tuple)", "findlast(f::Function, t::Tuple)", "filter(f, t::Tuple)"]
    statement := "findfirst(f, t) and findlast(f, t) return the first and last index whose element satisfies f, or nothing, and filter(f, t) keeps exactly those elements in order, for short and long (>= 32) tuples."
    source := "findfirst/findlast/filter docstrings (base/array.jl)"
    status := .proven, prop := ``FindFilterCorrect, thm := some ``findFilterCorrect },
  { id := "tuples-in", juliaFile := "base/operators.jl"
    juliaFns := ["in(x, itr::Tuple)", "_in_tuple", "in(x, itr::Any32)"]
    statement := "x in t for a tuple agrees with the generic in(x, itr) = any(==(x), itr) used for Vectors, including three-valued missing results."
    source := "in docstring (base/operators.jl): == comparison, missing when no match and some comparison is missing"
    status := .proven, prop := ``InCorrect, thm := some ``inCorrect },
  { id := "tuples-equality", juliaFile := "base/tuple.jl"
    juliaFns := ["isequal(t1::Tuple, t2::Tuple)", "_isequal", "==(t1::Tuple, t2::Tuple)", "_eq", "_eq_missing"]
    statement := "isequal(t, s) holds iff equal lengths and elementwise isequal; t == s is false for different lengths and otherwise the three-valued conjunction of elementwise ==, for short and long tuples."
    source := "== and isequal docstrings (base/operators.jl): collections compare elementwise, == propagates missing"
    status := .proven, prop := ``EqualityCorrect, thm := some ``equalityCorrect },
  { id := "tuples-lt-lexicographic", juliaFile := "base/tuple.jl"
    juliaFns := ["<(t1::Tuple, t2::Tuple)", "<(t1::Any32, t2::Any32)"]
    statement := "t < s on tuples is decided at the first position where == is not true (missing gives missing, false gives t[i] < s[i]), else the shorter tuple is smaller; the Any32 loop agrees with the recursive method."
    source := "invariant: lexicographic order (base/tuple.jl:612-637)"
    status := .proven, prop := ``LtLexicographic, thm := some ``ltLexicographic },
  { id := "tuples-isless-order", juliaFile := "base/tuple.jl"
    juliaFns := ["isless(t1::Tuple, t2::Tuple)", "isless(t1::Any32, t2::Any32)", "isless(a::Tuple{BitInteger,BitInteger}, b::Tuple{BitInteger,BitInteger})", "cmp"]
    statement := "If element isless is a strict weak order with isequal as incomparability, then isless on tuples of any lengths (every method) is a strict weak order whose incomparability is tuple isequal, and cmp(t, s) == 0 iff isequal(t, s)."
    source := "base/tuple.jl:643-647 (isless docstring: lexicographic order); isless docstring (base/operators.jl: total order consistent with isequal)"
    status := .proven, prop := ``IslessStrictWeakOrder, thm := some ``islessStrictWeakOrder },
  { id := "tuples-hash-isequal", juliaFile := "base/tuple.jl"
    juliaFns := ["hash(t::Tuple, h::UInt)", "hash(t::Any32, h::UInt)", "hash(x::NamedTuple, h::UInt)", "isequal(a::NamedTuple, b::NamedTuple)"]
    statement := "If element hash is consistent with element isequal, then isequal(t, s) implies hash(t, h) == hash(s, h) for tuples (both methods) and named tuples."
    source := "hash docstring (base/hashing.jl): isequal(x,y) implies hash(x)==hash(y)"
    status := .proven, prop := ``HashIsequal, thm := some ``hashIsequal },
  { id := "tuples-namedtuple-merge", juliaFile := "base/namedtuple.jl"
    juliaFns := ["merge(a::NamedTuple, b::NamedTuple)", "merge_names", "merge_fallback", "structdiff", "diff_names", "setindex(nt::NamedTuple, v, idx::Symbol)", "getindex(t::NamedTuple, idxs::Tuple{Vararg{Symbol}})"]
    statement := "merge(a, b) lists a's names then b-only names and takes each value from b when present there; structdiff(a, b) keeps the fields of a not named in b; Base.setindex(nt, v, k) sets field k; nt[names] returns the requested fields in order."
    source := "base/namedtuple.jl:306-330 (merge docstring), 442-447 (structdiff docstring), 463-482 (setindex docstring)"
    status := .proven, prop := ``NamedTupleCorrect, thm := some ``namedTupleCorrect },
  { id := "tuples-circshift", juliaFile := "base/tuple.jl"
    juliaFns := ["circshift(t::Tuple, shift::Integer)", "circshift(a::AbstractArray, shiftamt::Real)", "_circshift!", "mod1"]
    statement := "circshift on a tuple returns the same values as circshift on the Vector of its elements, for every shift of every BitInteger type including typemin and typemax; both rotate right by mod(shift, length)."
    source := "invariant: tuple methods agree with the corresponding Vector methods (base/tuple.jl:717-724, base/abstractarraymath.jl:335, base/multidimensional.jl:1257-1290)"
    status := .proven, prop := ``CircshiftAgrees, thm := some ``circshiftAgrees
    notes := "Bool shifts are excluded. Tuples shorter than 2^62 (larger ones cannot exist). Differential check: 715 cases, identical on 1.13.2 and nightly." }
]

end JuliaLean.Tuples

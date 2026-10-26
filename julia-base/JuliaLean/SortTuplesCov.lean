import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.SortTuplesCov.Ordering
import JuliaLean.SortTuplesCov.Pair
import JuliaLean.SortTuplesCov.TupleProofs
import JuliaLean.SortTuplesCov.NamedTupleProofs
import JuliaLean.SortTuplesCov.SortBugs
import JuliaLean.SortTuplesCov.TupleCoverage
import JuliaLean.SortTuplesCov.NtupleCoverage
import JuliaLean.SortTuplesCov.NamedTupleCoverage
import JuliaLean.SortTuplesCov.SortLegacy
import JuliaLean.SortTuplesCov.SortRemaining
import JuliaLean.SortTuplesCov.OrderingCoverage
import JuliaLean.SortTuplesCov.PairCoverage

namespace JuliaLean.SortTuplesCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "sorttuplescov-reverse-ordering", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering(rev::ReverseOrdering)", "ReverseOrdering(fwd::Fwd)", "ReverseOrdering()", "ReverseOrdering(by::By)", "By(by)"]
    statement := "For orderings without Perm, ReverseOrdering(o) swaps the arguments of lt, reversing twice restores every constructor-built ordering, Reverse compares by isless with swapped arguments, and By(f) compares f values by isless."
    source := "base/ordering.jl:33-48,86,110 (ReverseOrdering and By docstrings)", status := .proven
    prop := ``ReverseOrderingCorrect, thm := some ``reverseOrderingCorrect },
  { id := "sorttuplescov-reverseordering-perm-lt", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering(perm::Perm)", "lt(p::Perm, a::Integer, b::Integer)"]
    statement := "For every ordering o and all a, b: lt(ReverseOrdering(o), a, b) == lt(o, b, a)."
    source := "base/ordering.jl:33-41 (ReverseOrdering docstring)", status := .refuted
    prop := ``ReverseOrderingLtSwap, thm := some ``reverseOrderingLtSwap_refuted
    issue := "none found (related: #46732; queries: ReverseOrdering Perm, ReverseOrdering docstring lt, Order.Perm reverse)"
    notes := "ReverseOrdering(Perm(order, data)) keeps the ascending index tie-break: with p = Perm(Forward, [0, 0]), lt(ReverseOrdering(p), 1, 2) is true and lt(p, 2, 1) is false. Same on 1.13.2." },
  { id := "sorttuplescov-perm-lt", juliaFile := "base/ordering.jl"
    juliaFns := ["lt(p::Perm, a::Integer, b::Integer)"]
    statement := "lt(Perm(o, data), i, j) compares data[i] and data[j] under o and breaks ties by i < j, throws BoundsError outside the data, and is a total strict weak order on valid indices when o is."
    source := "base/ordering.jl:98-103 (Perm docstring)", status := .proven
    prop := ``PermLtCorrect, thm := some ``permLtCorrect },
  { id := "sorttuplescov-lt-methods", juliaFile := "base/ordering.jl"
    juliaFns := ["lt(o::ForwardOrdering, a, b)", "lt(o::ReverseOrdering, a, b)", "lt(o::By, a, b)", "lt(o::Lt, a, b)"]
    statement := "Forward compares by isless, ReverseOrdering swaps the arguments, By compares the by values, and Lt calls its function."
    source := "base/ordering.jl:74-96,118-121 (Ordering docstrings)", status := .proven
    prop := ``LtMethodsCorrect, thm := some ``ltMethodsCorrect },
  { id := "sorttuplescov-ord", juliaFile := "base/ordering.jl"
    juliaFns := ["_ord", "_by", "ord(lt, by, rev::Nothing, order)", "ord(lt, by, rev::Bool, order)"]
    statement := "ord(lt, by, rev, order) accepts every order with lt = isless and Forward/Reverse with another lt, and the result compares by-keys with lt or the order, reversed when rev = true."
    source := "base/ordering.jl:139-160 (ord docstring)", status := .proven
    prop := ``OrdCorrect, thm := some ``ordCorrect },
  { id := "sorttuplescov-ord-rejects", juliaFile := "base/ordering.jl"
    juliaFns := ["_ord(lt, by, order::Ordering)", "ord"]
    statement := "ord with a custom lt and an order other than Forward and Reverse throws ErrorException."
    source := "base/ordering.jl:135,150-151", status := .proven
    prop := ``OrdRejects, thm := some ``ordRejects },
  { id := "sorttuplescov-ordtype", juliaFile := "base/ordering.jl"
    juliaFns := ["ordtype(o::ReverseOrdering, vs)", "ordtype(o::Perm, vs)", "ordtype(o::By, vs)", "ordtype(o::Ordering, vs)"]
    statement := "ordtype is the element type for direct orders, the type of by(vs[1]) for By (Any for empty vs), that of the wrapped order for ReverseOrdering and of data for Perm; reversing never changes it."
    source := "base/ordering.jl:163-174", status := .proven
    prop := ``OrdtypeCorrect, thm := some ``ordtypeCorrect },
  { id := "sorttuplescov-pair-iter-index", juliaFile := "base/pair.jl"
    juliaFns := ["iterate(p::Pair, i)", "indexed_iterate(p::Pair, i, state)", "getindex(p::Pair, i::Int)", "getindex(p::Pair, i::Real)", "firstindex(p::Pair)", "lastindex(p::Pair)", "length(p::Pair)", "first(p::Pair)", "last(p::Pair)"]
    statement := "A Pair iterates first then second, indexes 1 and 2 for every integral index type (InexactError for non-integers, BoundsError otherwise), has length 2 and index range 1:2."
    source := "base/pair.jl:5-11 (Pair docstring: treated like a 2-tuple), 41-62", status := .proven
    prop := ``PairIterIndexCorrect, thm := some ``pairIterIndexCorrect },
  { id := "sorttuplescov-pair-compare", juliaFile := "base/pair.jl"
    juliaFns := ["==(p::Pair, q::Pair)", "isequal(p::Pair, q::Pair)", "isless(p::Pair, q::Pair)", "hash(p::Pair, h::UInt)"]
    statement := "Pair == is the three-valued conjunction, isequal the conjunction, isequal pairs hash equally, and isless is a lexicographic strict weak order with isequal as equivalence for lawful elements."
    source := "invariant: isequal/hash and isless contracts (base/hashing.jl, base/operators.jl isless docstring)", status := .proven
    prop := ``PairCompareCorrect, thm := some ``pairCompareCorrect },
  { id := "sorttuplescov-pair-types", juliaFile := "base/pair.jl"
    juliaFns := ["reverse(p::Pair)", "eltype(::Type{Pair{A,B}})", "convert(::Type{Pair{A,B}}, x::Pair{A,B})", "convert(::Type{Pair{A,B}}, x::Pair)", "promote_rule(::Type{Pair{A1,B1}}, ::Type{Pair{A2,B2}})"]
    statement := "reverse swaps the fields and is an involution, eltype bounds both field types, convert returns a Pair{A,B} unchanged and otherwise converts the fields first to second, and promote_rule is symmetric when promote_type is."
    source := "base/pair.jl:40,56,64-74", status := .proven
    prop := ``PairTypesCorrect, thm := some ``pairTypesCorrect },
  { id := "sorttuplescov-tuple-basics", juliaFile := "base/tuple.jl"
    juliaFns := ["length(t::Tuple)", "firstindex(t::Tuple)", "lastindex(t::Tuple)", "size(t::Tuple, d::Integer)", "axes(t::Tuple)", "keys(t::Tuple)", "__safe_getindex", "iterate(t::Tuple, i)", "prevind", "nextind", "isempty", "empty", "safe_tail"]
    statement := "Tuple length, index range, size(t, 1), axes, keys, unchecked indexing, iteration, prevind/nextind (Int(i) -+ 1 with InexactError outside Int), isempty, empty and safe_tail behave as for the 1-d collection of the elements."
    source := "base/tuple.jl:28-75,143-146,323-324,665-666,712", status := .proven
    prop := ``TupleBasicsCorrect, thm := some ``tupleBasicsCorrect },
  { id := "sorttuplescov-tuple-index-vec", juliaFile := "base/tuple.jl"
    juliaFns := ["getindex(t::Tuple, r::AbstractArray{<:Any,1})", "getindex(t::Tuple, b::AbstractArray{Bool,1})", "getindex(t::Tuple, c::Colon)", "get(f::Callable, t::Tuple, i::Integer)"]
    statement := "t[r] for an index vector is the tuple of t[r[k]] (BoundsError when any index is outside), t[b] for a Bool mask keeps the selected elements (BoundsError on a length mismatch), t[:] is t, and get(f, t, i) is t[i] for valid i and f() otherwise."
    source := "base/tuple.jl:36-41 (getindex/get semantics of collections)", status := .proven
    prop := ``TupleIndexVecCorrect, thm := some ``tupleIndexVecCorrect },
  { id := "sorttuplescov-tuple-iter-protocol", juliaFile := "base/tuple.jl"
    juliaFns := ["keys(t::Tuple, t2::Tuple...)", "indexed_iterate(t::Tuple, i, state)", "indexed_iterate(a::Union{Array,Memory}, i, state)", "indexed_iterate(I, i)", "indexed_iterate(I, i, state)"]
    statement := "keys of several tuples is OneTo(length) when all lengths agree, and indexed_iterate returns the i-th element of tuples and arrays and the next iterate of a generic iterator, throwing BoundsError when it is exhausted."
    source := "base/tuple.jl:148-172 (destructuring protocol)", status := .proven
    prop := ``TupleIterProtocolCorrect, thm := some ``tupleIterProtocolCorrect },
  { id := "sorttuplescov-rest", juliaFile := "base/tuple.jl"
    juliaFns := ["rest(t::Tuple)", "rest(t::Tuple, i)", "rest(a::Union{Array,Memory,Core.SimpleVector}, i)", "rest(itr, state...)"]
    statement := "Base.rest returns the elements from position i on (the whole collection for rest(t)), for tuples, arrays and generic iterators."
    source := "base/tuple.jl:174-213 (Base.rest docstring)", status := .proven
    prop := ``RestCorrect, thm := some ``restCorrect },
  { id := "sorttuplescov-split-rest", juliaFile := "base/tuple.jl"
    juliaFns := ["split_rest(itr, n::Int, state...)", "_split_rest(itr, n::Int)", "_check_length_split_rest(len, n)", "_split_rest(a::Union{AbstractArray, Core.SimpleVector}, n::Int)"]
    statement := "split_rest of an array or finite iterator with 0 <= n <= its length splits it into the front part and the last n elements; larger n, and infinite iterators, throw ArgumentError."
    source := "base/tuple.jl:215-263 (Base.split_rest docstring)", status := .proven
    prop := ``SplitRestCorrect, thm := some ``splitRestCorrect },
  { id := "sorttuplescov-map-n-foreach", juliaFile := "base/tuple.jl"
    juliaFns := ["heads(ts::Tuple...)", "tails(ts::Tuple...)", "anyempty", "map(f, ::Tuple{}, ::Tuple{}...)", "map(f, t1::Tuple, t2::Tuple, ts::Tuple...)", "map(f, t1::Any32, t2::Any32, ts::Any32...)", "foreach(f, itr::Tuple)", "foreach(f, itr::Tuple, itrs::Tuple...)"]
    statement := "map over three or more tuples applies f to the k-th elements up to the shortest tuple (short and Any32 methods), and foreach applies f to the elements or zipped elements in order."
    source := "base/tuple.jl:420-439,714-715 (map/foreach docstrings)", status := .proven
    prop := ``MapNForeachCorrect, thm := some ``mapNForeachCorrect },
  { id := "sorttuplescov-sym-in", juliaFile := "base/tuple.jl"
    juliaFns := ["sym_in(x::Symbol, itr::Tuple{Vararg{Symbol}})", "in(x::Symbol, itr::Tuple{Vararg{Symbol}})"]
    statement := "sym_in(x, itr) and x in itr are membership of x in the tuple of symbols."
    source := "base/tuple.jl:696-704 (in docstring)", status := .proven
    prop := ``SymInCorrect, thm := some ``symInCorrect },
  { id := "sorttuplescov-fill-to-length", juliaFile := "base/tuple.jl"
    juliaFns := ["fill_to_length(t::NTuple{N,Any}, val, ::Val{N})", "fill_to_length(t::Tuple{}, val, ::Val{1})", "fill_to_length(t::Tuple{Any}, val, ::Val{2})", "fill_to_length(t::Tuple{}, val, ::Val{2})"]
    statement := "The specialised fill_to_length methods pad the tuple with val up to the requested length."
    source := "base/tuple.jl:442-445, base/ntuple.jl:74-85", status := .proven
    prop := ``FillToLengthSpecialized, thm := some ``fillToLengthSpecialized },
  { id := "sorttuplescov-nt-construct", juliaFile := "base/namedtuple.jl"
    juliaFns := ["NamedTuple{names,T}(args::Tuple)", "NamedTuple{names,T}(nt::NamedTuple)", "NamedTuple{names,T}(itr)", "NamedTuple{names}(itr)", "_new_NamedTuple", "convert(::Type{NT}, nt::NT)", "Tuple(nt::NamedTuple)", "(::Type{T})(nt::NamedTuple)"]
    statement := "NamedTuple constructors pair names with converted values (ArgumentError for a length mismatch, FieldError for a missing field, ErrorException for repeated names), and conversions to tuples convert each value."
    source := "base/namedtuple.jl:6-112 (NamedTuple docstring), 115-196", status := .proven
    prop := ``NTConstructCorrect, thm := some ``ntConstructCorrect },
  { id := "sorttuplescov-nt-access", juliaFile := "base/namedtuple.jl"
    juliaFns := ["length(t::NamedTuple)", "iterate(t::NamedTuple, iter)", "rest(t::NamedTuple)", "firstindex", "lastindex", "getindex(t::NamedTuple, i::Int)", "getindex(t::NamedTuple, i::Symbol)", "getindex(t::NamedTuple, ::Colon)", "indexed_iterate(t::NamedTuple, i, state)", "isempty", "empty", "keys", "values", "tail", "front", "reverse(nt::NamedTuple)"]
    statement := "Named tuples iterate, index and slice their values like the tuple of values, keys and values are the names and values, and tail/front/reverse drop or reverse fields."
    source := "base/namedtuple.jl:159-176,382-389", status := .proven
    prop := ``NTAccessCorrect, thm := some ``ntAccessCorrect },
  { id := "sorttuplescov-nt-compare", juliaFile := "base/namedtuple.jl"
    juliaFns := ["==(a::NamedTuple{n}, b::NamedTuple{n})", "==(a::NamedTuple, b::NamedTuple)", "isequal", "_nt_names", "<(a::NamedTuple{n}, b::NamedTuple{n})", "isless(a::NamedTuple{n}, b::NamedTuple{n})", "same_names"]
    statement := "==, isequal, < and isless on named tuples compare the values when the names agree; == and isequal are false otherwise and < / isless have no method."
    source := "base/namedtuple.jl:241-256", status := .proven
    prop := ``NTCompareCorrect, thm := some ``ntCompareCorrect },
  { id := "sorttuplescov-nt-map-filter", juliaFile := "base/namedtuple.jl"
    juliaFns := ["map(f, nt::NamedTuple{names}, nts::NamedTuple...)", "filter(f, xs::NamedTuple)"]
    statement := "map on named tuples throws ArgumentError unless all names agree and otherwise maps the values fieldwise; filter keeps the fields whose value satisfies f."
    source := "base/namedtuple.jl:258-266 (map/filter docstrings)", status := .proven
    prop := ``NTMapFilterCorrect, thm := some ``ntMapFilterCorrect },
  { id := "sorttuplescov-nt-merge-itr", juliaFile := "base/namedtuple.jl"
    juliaFns := ["merge(a::NamedTuple, itr)", "merge(a::NamedTuple, b::Iterators.Pairs)", "merge(a, b, cs...)", "merge(a::NamedTuple)", "delete(a::NamedTuple, field::Symbol)"]
    statement := "merge(a, itr) merges the pairs of itr, each key once at its first position with its last value (TypeError for a non-Symbol key); merge of pairs(nt), of several and of one argument; delete drops a field."
    source := "base/namedtuple.jl:307-357 (merge docstring), 437-440", status := .proven
    prop := ``NTMergeItrCorrect, thm := some ``ntMergeItrCorrect },
  { id := "sorttuplescov-merge-zip", juliaFile := "base/namedtuple.jl"
    juliaFns := ["merge(a::NamedTuple, b::Iterators.Zip{<:Tuple{Any,Any}})"]
    statement := "merge(a, zip(ks, vs)) agrees with the generic merge(a, itr) on the iterated pairs."
    source := "base/namedtuple.jl:354-357 (merge docstring: iterator of key-value pairs)", status := .refuted
    prop := ``MergeZipAgrees, thm := some ``mergeZipAgrees_refuted
    issue := "none found (queries: merge NamedTuple zip, merge zip duplicate, NamedTuple merge iterator)"
    notes := "With a repeated key, merge((;), zip((:a, :a), (1, 2))) throws ErrorException while the generic iterator method returns (a = 2,). Same on 1.13.2." },
  { id := "sorttuplescov-float-range-search-overflow", juliaFile := "base/sort.jl"
    juliaFns := ["searchsortedlast(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)", "searchsortedfirst(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)", "searchsorted(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)"]
    statement := "Finite float-range searches return an index rather than throwing."
    source := "base/sort.jl:243-267 and searchsortedfirst/last docstrings", status := .refuted
    prop := ``FloatRangeSearchNoThrow, thm := some ``floatRangeSearchNoThrow_refuted
    issue := "related #34408; none found (queries: searchsorted float range InexactError, searchsortedlast range Inf, searchsorted range overflow float)"
    notes := "For range(-1e308, 1e308, length=3), searchsortedlast(r, 9e307) computes x-first(r) as Inf and throws InexactError. Same on 1.13.2." },
  { id := "sorttuplescov-insorted-range-equivalence", juliaFile := "base/sort.jl"
    juliaFns := ["insorted(x, v::AbstractVector; kw...)", "insorted(x, r::AbstractRange)"]
    statement := "The optimized range method agrees with vector insorted under the sort-order equivalence and returns Bool."
    source := "base/sort.jl:426-466 (insorted docstring and methods)", status := .refuted
    prop := ``InsortedRangeAgrees, thm := some ``insortedRangeAgrees_refuted
    issue := "related #48388 and #44102; none found (queries: insorted range, insorted missing, insorted -0.0)"
    notes := "The range method calls in and therefore uses ==: signed zero compares differently and missing propagates. Same on 1.13.2." },
  { id := "sorttuplescov-legacy-sort-scratch", juliaFile := "base/sort.jl"
    juliaFns := ["sort!(v, lo, hi, a::Algorithm, o, scratch::Vector)", "_sort!(v, a::Algorithm, o, kw)"]
    statement := "A caller-provided scratch vector does not make a supported legacy five-argument sort throw on a valid window."
    source := "base/sort.jl:2570-2595 (supported legacy entry points)", status := .refuted
    prop := ``LegacySortScratch, thm := some ``legacySortScratch_refuted
    issue := "none found (queries: sort! QuickSort scratch, _sort! is not defined, legacy sort! QuickSort)"
    notes := "The scratch method sets legacy_dispatch_entry=a and reaches the generic _sort! guard for QuickSort and PartialQuickSort. Same on 1.13.2." },
  { id := "sorttuplescov-partialquicksort-reversed-range", juliaFile := "base/sort.jl"
    juliaFns := ["_partialquicksort!(v, lo, hi, a::PartialQuickSort, o)", "sort!(v, lo, hi, a::PartialQuickSort, o)"]
    statement := "A partial quicksort partition does not discard a side containing a requested target index."
    source := "base/sort.jl:2321-2356 (PartialQuickSort docstring),2533-2566", status := .refuted
    prop := ``PartialQuickSortCorrect, thm := some ``partialQuickSortCorrect_refuted
    issue := "related #63228; none found (queries: PartialQuickSort range, PartialQuickSort reverse)"
    notes := "For a descending target 5:-1:3 and pivot 4, the test pivot <= first(k) discards the lower side containing target 3. Same on 1.13.2." },
  { id := "sorttuplescov-sort-ntuple-alg", juliaFile := "base/sort.jl"
    juliaFns := ["sort(x::NTuple; alg, lt, by, rev, order, scratch)", "_sort(x::NTuple, a::Union{DefaultStable,DefaultUnstable}, o, kw)"]
    statement := "Every built-in Algorithm accepted by sort(::NTuple)'s signature has a working dispatch."
    source := "base/sort.jl:1743-1747,1785-1808", status := .refuted
    prop := ``SortNTupleAlgs, thm := some ``sortNTupleAlgs_refuted
    issue := "related #54494; none found (queries: sort tuple alg, sort NTuple QuickSort, sort NTuple MethodError)"
    notes := "Only DefaultStable and DefaultUnstable have _sort(::NTuple, ...) methods; QuickSort throws MethodError. Same on 1.13.2." },
  { id := "sorttuplescov-sort-dims-exception", juliaFile := "base/sort.jl"
    juliaFns := ["sort!(A::AbstractArray; dims, alg, lt, by, rev, order, scratch)"]
    statement := "Every out-of-range dimension reaches the method's explicit ArgumentError check."
    source := "base/sort.jl:2187-2223", status := .refuted
    prop := ``SortDimsChecked, thm := some ``sortDimsChecked_refuted
    issue := "none found (queries: sort! dims BoundsError, sort dims out of range)"
    notes := "The default scratch expression evaluates size(A,dims) before the body; dims=0 throws BoundsError first. Same on 1.13.2." },
  { id := "sorttuplescov-sort-missing-scratch", juliaFile := "base/sort.jl"
    juliaFns := ["sort!(v::AbstractVector{T}; scratch::Union{Vector{T},Nothing})", "make_scratch(scratch::Vector, T, len)", "_sort!(v, a::MissingOptimization, o, kw)"]
    statement := "A scratch vector whose element type equals the input vector's accepted element type remains usable after MissingOptimization."
    source := "base/sort.jl:494-516,651-686,1017-1047,1732-1741", status := .refuted
    prop := ``SortScratchAccepted, thm := some ``sortScratchAccepted_refuted
    issue := "none found (queries: sort scratch missing reinterpret, cannot reinterpret scratch sort, make_scratch)"
    notes := "MissingOptimization changes the working view to Int32 but keeps the Union{Missing,Int32} scratch; make_scratch then tries an invalid reinterpret. Same on 1.13.2." },
  { id := "sorttuplescov-tuple-type-methods", juliaFile := "base/tuple.jl"
    juliaFns := ["_counttuple", "_eltype_ntuple", "eltype(::Type{<:Tuple})", "_compute_eltype", "keytype(::Tuple)", "keytype(::Type{<:Tuple})", "valtype(::Tuple)", "valtype(::Type{<:Tuple})", "tuple_type_tail"]
    statement := "Tuple length extraction, element-type joins, key and value types, and tuple type tails follow the source branches."
    source := "base/tuple.jl:21-24,273-320,451-468", status := .proven
    prop := ``TupleTypeMethodsCorrect, thm := some ``tupleTypeMethodsCorrect },
  { id := "sorttuplescov-tuple-construction", juliaFile := "base/tuple.jl"
    juliaFns := ["(::Type{T})(x::Tuple)", "Tuple(x::Ref)", "Tuple(x::Array{T,0})", "(::Type{T})(itr)", "_totuple", "_totuple_err"]
    statement := "Tuple constructors consume and convert iterator values in field order, reject too few elements, and use the source fast paths."
    source := "base/tuple.jl:470-518", status := .proven
    prop := ``TupleConstructionCorrect, thm := some ``tupleConstructionCorrect },
  { id := "sorttuplescov-ntuple-any", juliaFile := "base/ntuple.jl"
    juliaFns := ["ntupleany(f, n)"]
    statement := "ntupleany calls f on 1:n and rejects a negative length."
    source := "base/ntuple.jl:42-46", status := .proven
    prop := ``NtupleAnyCorrect, thm := some ``ntupleAnyCorrect },
  { id := "sorttuplescov-namedtuple-show", juliaFile := "base/namedtuple.jl"
    juliaFns := ["show(io::IO, t::NamedTuple)"]
    statement := "NamedTuple show selects the full-type, empty, singleton, or ordinary field form after its concrete-field scan."
    source := "base/namedtuple.jl:198-229", status := .proven
    prop := ``NamedTupleShowCorrect, thm := some ``namedTupleShowCorrect },
  { id := "sorttuplescov-namedtuple-type-methods", juliaFile := "base/namedtuple.jl"
    juliaFns := ["eltype(::Type{T})", "nteltype", "keytype(::NamedTuple)", "keytype(::Type{<:NamedTuple})", "valtype(::NamedTuple)", "valtype(::Type{<:NamedTuple})", "_nt_names(::Type)"]
    statement := "NamedTuple element, key, value, and name type methods return the types described by their source bodies."
    source := "base/namedtuple.jl:231-248", status := .proven
    prop := ``NamedTupleTypeMethodsCorrect, thm := some ``namedTupleTypeMethodsCorrect },
  { id := "sorttuplescov-namedtuple-type-helpers", juliaFile := "base/namedtuple.jl"
    juliaFns := ["merge_types", "diff_types", "diff_fallback"]
    statement := "Merge types prefer the right field and diff helpers retain the left fields whose names are absent from the right."
    source := "base/namedtuple.jl:280-285,403-422", status := .proven
    prop := ``NamedTupleTypeHelpersCorrect, thm := some ``namedTupleTypeHelpersCorrect },
  { id := "sorttuplescov-namedtuple-macros", juliaFile := "base/namedtuple.jl"
    juliaFns := ["@NamedTuple", "@Kwargs"]
    statement := "The macros validate declaration syntax, default omitted types to Any, and construct the corresponding NamedTuple and Pairs type forms."
    source := "base/namedtuple.jl:487-523,525-583", status := .proven
    prop := ``NamedTupleMacrosCorrect, thm := some ``namedTupleMacrosCorrect },
  { id := "sorttuplescov-sort-keyword-wrappers", juliaFile := "base/sort.jl"
    juliaFns := ["issorted(itr; ...)", "partialsort!(v,k; ...)", "searchsortedfirst(v,x,o)", "searchsortedlast(v,x,o)", "searchsorted(v,x,o)", "searchsortedfirst(v,x; ...)", "searchsortedlast(v,x; ...)", "searchsorted(v,x; ...)"]
    statement := "Sorting and searching keyword wrappers construct the documented ordering and forward the same values and index window."
    source := "base/sort.jl:86-95,166-168,304-310", status := .proven
    prop := ``SortKeywordWrappersCorrect, thm := some ``sortKeywordWrappersCorrect },
  { id := "sorttuplescov-generated-keywords", juliaFile := "base/sort.jl"
    juliaFns := ["@getkw", "_lo", "_hi", "_mn", "_mx", "_scratch", "_legacy_dispatch_entry"]
    statement := "Generated keyword getters return an existing value or append and return the source default."
    source := "base/sort.jl:470-489", status := .proven
    prop := ``GeneratedKeywordCorrect, thm := some ``generatedKeywordCorrect },
  { id := "sorttuplescov-make-scratch", juliaFile := "base/sort.jl"
    juliaFns := ["make_scratch(::Nothing,T,len)", "make_scratch(::Vector{T},T,len)", "make_scratch(::Vector,T,len)"]
    statement := "make_scratch allocates, resizes, or reinterprets the backing vector according to the dispatched source method."
    source := "base/sort.jl:494-516", status := .proven
    prop := ``MakeScratchCorrect, thm := some ``makeScratchCorrect },
  { id := "sorttuplescov-subarray-optimization", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(v,a::SubArrayOptimization,o,kw)", "_sort!(v::UnwrappableSubArray,a::SubArrayOptimization,o,kw)"]
    statement := "SubArrayOptimization forwards ordinary views and unwraps only the parent cases selected by the source condition."
    source := "base/sort.jl:559-574", status := .proven
    prop := ``SubarrayOptimizationCorrect, thm := some ``subarrayOptimizationCorrect },
  { id := "sorttuplescov-without-missing", juliaFile := "base/sort.jl"
    juliaFns := ["WithoutMissingVector", "getindex(::WithoutMissingVector)", "setindex!(::WithoutMissingVector)", "size(::WithoutMissingVector)", "axes(::WithoutMissingVector)"]
    statement := "WithoutMissingVector validates safe construction and delegates indexing, mutation, size, and axes to its data."
    source := "base/sort.jl:589-608", status := .proven
    prop := ``WithoutMissingVectorCorrect, thm := some ``withoutMissingVectorCorrect },
  { id := "sorttuplescov-send-to-end", juliaFile := "base/sort.jl"
    juliaFns := ["send_to_end!(f,v;lo,hi)", "send_to_end!(f,v,::ForwardOrdering,...)", "send_to_end!(f,v,::ReverseOrdering,...)"]
    statement := "send_to_end! follows the two source scans and the direct-order wrappers choose the correct direction, complement, and stability route."
    source := "base/sort.jl:610-648", status := .proven
    prop := ``SendToEndCorrect, thm := some ``sendToEndCorrect },
  { id := "sorttuplescov-missing-optimization", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(v,a::MissingOptimization,o,kw)"]
    statement := "MissingOptimization selects its direct, permutation, or pass-through branch under the exact source conditions."
    source := "base/sort.jl:651-686", status := .proven
    prop := ``MissingOptimizationCorrect, thm := some ``missingOptimizationCorrect },
  { id := "sorttuplescov-ieee-optimization", juliaFile := "base/sort.jl"
    juliaFns := ["after_zero", "is_concrete_IEEEFloat", "_sort!(v,a::IEEEFloatOptimization,o,kw)"]
    statement := "IEEEFloatOptimization partitions direct float values or permutation data and otherwise passes through."
    source := "base/sort.jl:703-731", status := .proven
    prop := ``IEEEOptimizationCorrect, thm := some ``ieeeOptimizationCorrect },
  { id := "sorttuplescov-bool-optimization", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(v,a::BoolOptimization,o,kw)", "_sort!(v::AbstractVector{Bool},::BoolOptimization,o,kw)"]
    statement := "BoolOptimization passes non-Bool vectors through and fills the Bool window according to the ordering and counted first value."
    source := "base/sort.jl:745-758", status := .proven
    prop := ``BoolOptimizationCorrect, thm := some ``boolOptimizationCorrect },
  { id := "sorttuplescov-algorithm-dispatch", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(v,a::IsUIntMappable,o,kw)", "Small constructors", "_sort!(v,a::Small,o,kw)", "_sort!(v,a::CheckSorted,o,kw)", "_sort!(v,a::ComputeExtrema,o,kw)", "ConsiderCountingSort", "_sort!(v,a::ConsiderCountingSort,o,kw)", "maybe_reverse", "ConsiderRadixSort", "_sort!(v,a::ConsiderRadixSort,o,kw)", "_sort!(v,a::StableCheckSorted,o,kw)"]
    statement := "Algorithm components select the same branch, threshold, extrema state, and direction as their source methods."
    source := "base/sort.jl:770-802,855-992,1355-1379", status := .proven
    prop := ``SortDispatchCorrect, thm := some ``sortDispatchCorrect },
  { id := "sorttuplescov-initial-pipeline", juliaFile := "base/sort.jl"
    juliaFns := ["InitialOptimizations", "_sort!(v,::Union{DefaultStable,DefaultUnstable},o,kw)", "defalg"]
    statement := "InitialOptimizations and the default vector pipeline compose the documented stages, and defalg selects stable or unstable defaults by value class."
    source := "base/sort.jl:1456-1593,1620-1624", status := .proven
    prop := ``InitialPipelineCorrect, thm := some ``initialPipelineCorrect },
  { id := "sorttuplescov-algorithm-show", juliaFile := "base/sort.jl"
    juliaFns := ["show(io,alg::Algorithm)", "print_tree", "show_type"]
    statement := "Algorithm display prints the recursive field tree and the specialized Small type name."
    source := "base/sort.jl:1597-1618", status := .proven
    prop := ``AlgorithmShowCorrect, thm := some ``algorithmShowCorrect },
  { id := "sorttuplescov-counting-sort", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(v,::CountingSort,o,kw)"]
    statement := "CountingSort counts every mapped value and repopulates buckets in forward or reverse order."
    source := "base/sort.jl:936-969", status := .proven
    prop := ``CountingSortCorrect, thm := some ``countingSortCorrect },
  { id := "sorttuplescov-radix-sort", juliaFile := "base/sort.jl"
    juliaFns := ["radix_sort!", "radix_sort_pass!", "radix_chunk_size_heuristic", "maybe_unsigned"]
    statement := "Radix passes stably group mapped words by each bit chunk, alternate buffers, and use the source chunk-size and unsigned helpers."
    source := "base/sort.jl:1382-1451", status := .proven
    prop := ``RadixSortCorrect, thm := some ``radixSortCorrect },
  { id := "sorttuplescov-top-level-sort", juliaFile := "base/sort.jl"
    juliaFns := ["sort!(v::AbstractVector;...)", "sort(v::AbstractVector;...)", "sort(::KeySet/ValueIterator)", "_sort(x::NTuple,::DefaultStable/DefaultUnstable,...)", "_mergesort(::NTuple)", "merge(::NTuple,::NTuple,o)"]
    statement := "Public vector sort wrappers copy or mutate as documented and the default tuple path uses vector sort above length nine and merge sort otherwise."
    source := "base/sort.jl:1732-1818", status := .proven
    prop := ``TopLevelSortCorrect, thm := some ``topLevelSortCorrect },
  { id := "sorttuplescov-sortperm-wrappers", juliaFile := "base/sort.jl"
    juliaFns := ["partialsortperm!", "sortperm", "_sortperm", "sortperm!"]
    statement := "Permutation wrappers validate axes, initialize linear indices, choose reverse ordering, and take the integer-range fast path under its exact guard."
    source := "base/sort.jl:1896-2055", status := .proven
    prop := ``SortpermWrappersCorrect, thm := some ``sortpermWrappersCorrect },
  { id := "sorttuplescov-multidimensional-sort", juliaFile := "base/sort.jl"
    juliaFns := ["sort(A;dims,...)", "sort_chunks!", "sort!(A;dims,...)", "get_view", "get_value"]
    statement := "Multidimensional sorting chooses the first or permuted dimension route, propagates scratch across chunks, and forms the source views."
    source := "base/sort.jl:2112-2224", status := .proven
    prop := ``MultidimensionalSortCorrect, thm := some ``multidimensionalSortCorrect },
  { id := "sorttuplescov-uint-mapping", juliaFile := "base/sort.jl"
    juliaFns := ["UIntMappable", "uint_map", "uint_unmap"]
    statement := "Unsigned, signed, Char, and reverse mappings follow the source bit transformations and advertise only supported types."
    source := "base/sort.jl:2227-2289", status := .proven
    prop := ``UIntMappingCorrect, thm := some ``uintMappingCorrect },
  { id := "sorttuplescov-uint-mapping-loops", juliaFile := "base/sort.jl"
    juliaFns := ["uint_map!", "uint_unmap!"]
    statement := "The vector mapping methods update each requested position in source order with the documented offset."
    source := "base/sort.jl:2292-2310", status := .proven
    prop := ``UIntMappingLoopsCorrect, thm := some ``uintMappingLoopsCorrect },
  { id := "sorttuplescov-initial-optimization-wrapper", juliaFile := "base/sort.jl"
    juliaFns := ["maybe_apply_initial_optimizations"]
    statement := "QuickSort, MergeSort, and InsertionSort receive InitialOptimizations; other algorithms pass through."
    source := "base/sort.jl:2396-2399", status := .proven
    prop := ``MaybeApplyInitialOptimizationsCorrect, thm := some ``maybeApplyInitialOptimizationsCorrect },
  { id := "sorttuplescov-legacy-sort-kernels", juliaFile := "base/sort.jl"
    juliaFns := ["selectpivot!", "partition!", "_quicksort!", "_mergesort!", "_partialquicksort!"]
    statement := "Legacy quick, merge, and partial quick kernels follow the pivot, partition, small-window, and recursive source branches."
    source := "base/sort.jl:2401-2566", status := .proven
    prop := ``LegacySortKernelsCorrect, thm := some ``legacySortKernelsCorrect },
  { id := "sorttuplescov-bracketed-sort", juliaFile := "base/sort.jl"
    juliaFns := ["bracket_kernel!", "move!", "_sort!(v,a::BracketedSort,o,kw)"]
    statement := "BracketedSort computes its signpost predicates and counters, moves by pair swaps or range reversals, and selects the documented fallback or trial route."
    source := "base/sort.jl:1226-1353", status := .proven
    prop := ``BracketedSortCorrect, thm := some ``bracketedSortCorrect },
  { id := "sorttuplescov-radix-wrapper", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(v,a::RadixSort,o,kw)"]
    statement := "The RadixSort wrapper maps values, subtracts the minimum, obtains scratch, runs radix passes, and unmaps the selected buffer."
    source := "base/sort.jl:1017-1047", status := .proven
    prop := ``RadixSortWrapperCorrect, thm := some ``radixSortWrapperCorrect },
  { id := "sorttuplescov-sortperm-int-range", juliaFile := "base/sort.jl"
    juliaFns := ["sortperm_int_range"]
    statement := "The integer-range fast path returns indices grouped stably by the source integer labels."
    source := "base/sort.jl:2058-2081", status := .proven
    prop := ``SortpermIntRangeCorrect, thm := some ``sortpermIntRangeCorrect },
  { id := "sorttuplescov-legacy-entries", juliaFile := "base/sort.jl"
    juliaFns := ["sort!(v,lo,hi,::QuickSortAlg,o)", "sort!(v,lo,hi,::MergeSortAlg,o,scratch)", "sort!(v,lo,hi,::PartialQuickSort,o)", "sort!(v,a,o)", "sort!(v,lo,hi,a,o)", "sort!(v,lo,hi,a,o,_)"]
    statement := "Legacy entries check bounds, invoke their kernel, and forward three-, five-, and ignored-scratch arguments as the source specifies."
    source := "base/sort.jl:2454-2582", status := .proven
    prop := ``LegacyEntriesCorrect, thm := some ``legacyEntriesCorrect },
  { id := "sorttuplescov-namedtuple-hash", juliaFile := "base/namedtuple.jl"
    juliaFns := ["hash(x::NamedTuple,h::UInt)"]
    statement := "Named tuple hashing combines the names' identity hash with tuple value hashing and respects isequal."
    source := "base/namedtuple.jl:250; hash contract", status := .proven
    prop := ``NamedTupleHashCorrect, thm := some ``namedTupleHashCorrect },
  { id := "sorttuplescov-namedtuple-split-rest", juliaFile := "base/namedtuple.jl"
    juliaFns := ["split_rest(t::NamedTuple,n,st...)"]
    statement := "NamedTuple split_rest performs the length check, delegates name splitting to the tuple method, and selects both resulting field groups."
    source := "base/namedtuple.jl:585-589", status := .proven
    prop := ``NamedTupleSplitRestDelegates, thm := some ``namedTupleSplitRestDelegates },
  { id := "sorttuplescov-ntuple-reverse", juliaFile := "base/ntuple.jl"
    juliaFns := ["reverse(t::NTuple{N})"]
    statement := "NTuple reverse constructs element i from source index end+1-i."
    source := "base/ntuple.jl:89-93", status := .proven
    prop := ``NtupleReverseCorrect, thm := some ``ntupleReverseCorrect },
  { id := "sorttuplescov-generic-reverse-ordering", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering(::ReverseOrdering)", "ReverseOrdering(fwd)", "reverse(::Ordering)", "ReverseOrdering(::By)", "ReverseOrdering(::Perm)"]
    statement := "ReverseOrdering unwraps an existing reverse, wraps every arbitrary ordering subtype, preserves By's key and Perm's data, and reverse delegates to the constructor."
    source := "base/ordering.jl:46-47,56,110-111", status := .proven
    prop := ``GenericReverseConstructorsCorrect, thm := some ``genericReverseConstructorsCorrect },
  { id := "sorttuplescov-perm-lt-evaluation", juliaFile := "base/ordering.jl"
    juliaFns := ["lt(p::Perm,a::Integer,b::Integer)"]
    statement := "Perm lt reads both data values, eagerly evaluates and Bool-asserts both comparisons, then applies the stable index tie-break."
    source := "base/ordering.jl:123-127", status := .proven
    prop := ``PermLtEvaluationCorrect, thm := some ``permLtEvaluationCorrect },
  { id := "sorttuplescov-generic-ord", juliaFile := "base/ordering.jl"
    juliaFns := ["_ord", "_by", "ord"]
    statement := "_ord retains arbitrary existing orderings for isless, handles Forward and Reverse for custom lt, emits the exact ambiguity error, and ord conditionally reverses the result."
    source := "base/ordering.jl:130-160", status := .proven
    prop := ``GenericOrdCorrect, thm := some ``genericOrdCorrect },
  { id := "sorttuplescov-generic-ordtype", juliaFile := "base/ordering.jl"
    juliaFns := ["ordtype(::ReverseOrdering)", "ordtype(::Perm)", "ordtype(::By)"]
    statement := "ordtype delegates through arbitrary wrapped orders and Perm data, while By returns Any after any indexing or key-function exception."
    source := "base/ordering.jl:170-174", status := .proven
    prop := ``GenericOrdtypeCorrect, thm := some ``genericOrdtypeCorrect },
  { id := "sorttuplescov-pair-generic-iteration", juliaFile := "base/pair.jl"
    juliaFns := ["iterate(p::Pair,i)", "indexed_iterate(p::Pair,i,state)"]
    statement := "Pair iteration accepts every state supported by Julia's operations, and indexed_iterate accepts and ignores its state argument."
    source := "base/pair.jl:41-42", status := .proven
    prop := ``PairIterationGenericCorrect, thm := some ``pairIterationGenericCorrect },
  { id := "sorttuplescov-pair-fixed-hash", juliaFile := "base/pair.jl"
    juliaFns := ["hash(p::Pair,h::UInt)"]
    statement := "Pair hash uses the architecture-specific UInt seed and wraps every intermediate to the platform UInt width."
    source := "base/pair.jl:44-46", status := .proven
    prop := ``PairHashFixedCorrect, thm := some ``pairHashFixedCorrect },
  { id := "sorttuplescov-pair-eager-compare", juliaFile := "base/pair.jl"
    juliaFns := ["isequal(p::Pair,q::Pair)", "isless(p::Pair,q::Pair)"]
    statement := "Pair isequal evaluates both fields for &, and pair isless eagerly evaluates the condition and both ifelse branches."
    source := "base/pair.jl:50-53", status := .proven
    prop := ``PairEagerCompareCorrect, thm := some ``pairEagerCompareCorrect },
  { id := "sorttuplescov-pair-generic-index", juliaFile := "base/pair.jl"
    juliaFns := ["getindex(p::Pair,i::Int)", "getindex(p::Pair,i::Real)"]
    statement := "Pair indexing returns the two fields at 1 and 2, and the Real overload applies Julia's convert(Int,i) for every Real input before indexing."
    source := "base/pair.jl:54-55", status := .proven
    prop := ``PairGetindexCorrect, thm := some ``pairGetindexCorrect },
  { id := "sorttuplescov-pair-typed-reverse", juliaFile := "base/pair.jl"
    juliaFns := ["reverse(p::Pair{A,B})"]
    statement := "Pair reverse constructs Pair{B,A} and is an involution."
    source := "base/pair.jl:56", status := .proven
    prop := ``PairTypedReverseCorrect, thm := some ``pairTypedReverseCorrect },
  { id := "sorttuplescov-pair-typed-convert", juliaFile := "base/pair.jl"
    juliaFns := ["convert(::Type{Pair{A,B}},x::Pair)"]
    statement := "Pair conversion checks and converts first then second and returns a result carrying exactly target types A and B."
    source := "base/pair.jl:65-71", status := .proven
    prop := ``PairTypedConvertCorrect, thm := some ``pairTypedConvertCorrect }
]

end JuliaLean.SortTuplesCov

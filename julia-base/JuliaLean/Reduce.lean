import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Reduce.Model
import JuliaLean.Reduce.Val
import JuliaLean.Reduce.Vec
import JuliaLean.Reduce.Dims
import JuliaLean.Reduce.Props
import JuliaLean.Reduce.Refutations
import JuliaLean.Reduce.ProofsGeneric
import JuliaLean.Reduce.ProofsVal
import JuliaLean.Reduce.ProofsFindmax
import JuliaLean.Reduce.ProofsSumDims
import JuliaLean.Reduce.ProofsDims
import JuliaLean.Reduce.Validation

namespace JuliaLean.Reduce

open JuliaLean.Registry

def entries : List Entry := [
  -- proven
  { id := "reduce-pairwise-foldl", juliaFile := "base/reduce.jl"
    juliaFns := ["reduce(op, A)", "mapreduce(f, op, A)", "mapreduce_impl", "_mapreduce"]
    statement := "For an associative op, the pairwise reduction mapreduce(f, op, A) equals the left fold of op over map(f, A), for every block size."
    source := "base/reduce.jl:480-483 (reduce docstring: associativity is implementation dependent)"
    status := .proven, prop := ``PairwiseFoldl, thm := some ``pairwiseFoldl_proven },
  { id := "reduce-extrema-agree", juliaFile := "base/reduce.jl"
    juliaFns := ["extrema(itr)", "maximum(itr)", "minimum(itr)"]
    statement := "extrema(v) == (minimum(v), maximum(v)) for every vector of integers, floats (NaN, -0.0), Bools and missing, and both throw for empty v."
    source := "base/reduce.jl:750-775 (extrema docstring)"
    status := .proven, prop := ``ExtremaAgree, thm := some ``extremaAgree_proven },
  { id := "reduce-findmax-agree", juliaFile := "base/reduce.jl"
    juliaFns := ["findmax(itr)", "findmin(itr)", "argmax(itr)", "argmin(itr)", "maximum(itr)", "minimum(itr)"]
    statement := "For a nonempty Vector{Float64}, findmax(v) == (v[i], i) with v[i] isequal to maximum(v), and findmin likewise with minimum."
    source := "base/reduce.jl:855-878, 921-944 (findmax/findmin docstrings)"
    status := .proven, prop := ``FindmaxAgree, thm := some ``findmaxAgree_proven },
  { id := "reduce-fold-init", juliaFile := "base/reduce.jl"
    juliaFns := ["foldl(op, itr; init)", "foldr(op, itr; init)", "mapfoldl", "mapfoldr"]
    statement := "foldl and foldr with init are the left and right folds starting from init, which is used exactly once."
    source := "base/reduce.jl:166-241 (mapfoldl/foldl/mapfoldr/foldr docstrings)"
    status := .proven, prop := ``FoldInit, thm := some ``foldInit_proven },
  { id := "reduce-anyall-3vl", juliaFile := "base/anyall.jl"
    juliaFns := ["any(f, itr)", "all(f, itr)"]
    statement := "any(f, v) and all(f, v) follow three-valued logic for Bool/missing values of f and short-circuit once the result is decided."
    source := "base/anyall.jl:3-10, 32-39, 63-69 (any/all docstrings)"
    status := .proven, prop := ``AnyAllThreeValued, thm := some ``anyAllThreeValued_proven },
  { id := "reduce-sum-init-widened", juliaFile := "base/reduce.jl"
    juliaFns := ["sum(v; init)", "add_sum"]
    statement := "sum(v; init=zero(S)) of a nonempty small-integer vector is the sum in Int or UInt, for every small S."
    source := "base/reduce.jl:546-557 (sum docstring: Int/UInt for small integers)"
    status := .proven, prop := ``SumInitWidened, thm := some ``sumInitWidened_proven },
  { id := "reduce-flatten-foldl", juliaFile := "base/reduce.jl"
    juliaFns := ["foldl(op, ::Iterators.Flatten)", "FlatteningRF"]
    statement := "foldl over Iterators.flatten(vs) (with init, or without when nonempty) is the left fold over the concatenation."
    source := "base/reduce.jl:112-125 (FlatteningRF docstring), 175-182 (foldl)"
    status := .proven, prop := ``FlattenFoldl, thm := some ``flattenFoldl_proven },
  { id := "reduce-cat", juliaFile := "base/abstractarray.jl"
    juliaFns := ["reduce(vcat, A)", "reduce(hcat, A)"]
    statement := "reduce(vcat, vs) concatenates a nonempty vector of vectors; reduce(hcat, vs) puts equal-length vectors side by side and throws DimensionMismatch otherwise."
    source := "base/reduce.jl:477-478 (efficient reduce(vcat/hcat) methods)"
    status := .proven, prop := ``ReduceCatSpec, thm := some ``reduceCatSpec_proven },
  { id := "reduce-empty", juliaFile := "base/reduce.jl"
    juliaFns := ["maximum", "minimum", "extrema", "findmax", "findmin", "sum", "prod"]
    statement := "Empty collections: maximum/minimum/extrema/findmax/findmin throw ArgumentError, reductions with init return init, sum/prod of an empty integer vector are zero/one of the widened type."
    source := "base/reduce.jl:317-356, 686-747 (reduce_empty and maximum/minimum docstrings)"
    status := .proven, prop := ``EmptyReductions, thm := some ``emptyReductions_proven },
  { id := "reduce-sumdims-exact", juliaFile := "base/reducedim.jl"
    juliaFns := ["sum(A; dims)", "_mapreducedim!", "reducedim_init"]
    statement := "sum(A; dims=1 or 2) of a BitInteger matrix has the reduced shape and holds the exact slice sums in the widened type (Int/UInt for small types), on every code path including the pairwise one."
    source := "base/reducedim.jl:464-485 (sum(A; dims) docstring), base/reduce.jl:511-513"
    status := .proven, prop := ``SumDimsExact, thm := some ``sumDimsExact_proven },
  { id := "reduce-maxdims-int", juliaFile := "base/reducedim.jl"
    juliaFns := ["maximum(A; dims)", "minimum(A; dims)", "reducedim_init"]
    statement := "maximum/minimum(A; dims=1 or 2) of a nonempty Matrix{Int} has the reduced shape and holds maximum/minimum of each slice."
    source := "base/reducedim.jl:613-743 (maximum/minimum(A; dims) docstrings)"
    status := .proven, prop := ``MaxDimsInt, thm := some ``maxDimsInt_proven },
  { id := "reduce-finddims-slices", juliaFile := "base/reducedim.jl"
    juliaFns := ["findmax(A; dims)", "findmin(A; dims)", "findminmax!"]
    statement := "findmax/findmin(A; dims=1 or 2) of a nonempty Matrix{Float64} hold findmax/findmin of each slice, with indices mapped to CartesianIndex."
    source := "base/reducedim.jl:1096-1212 (findmin/findmax(A; dims) docstrings)"
    status := .proven, prop := ``FindDimsSlices, thm := some ``findDimsSlices_proven },
  { id := "reduce-accumulate-dims-scan", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate(op, A; dims, init)", "_accumulate!", "_accumulaten!"]
    statement := "accumulate(op, A; dims=1) scans each column and dims=2 each row like accumulate(op, slice; init); accumulate(op, v; dims=1) is accumulate(op, v)."
    source := "base/accumulate.jl:235-293 (accumulate docstring)"
    status := .proven, prop := ``AccumulateDimsScan, thm := some ``accumulateDimsScan_proven },
  { id := "reduce-cumprod-widened", juliaFile := "base/accumulate.jl"
    juliaFns := ["cumprod(v)", "mul_prod"]
    statement := "cumprod(v) of a small-integer vector holds the prefix products in Int/UInt, wrapping only there."
    source := "base/accumulate.jl:175-198 (cumprod docstring), base/reduce.jl:582-584"
    status := .proven, prop := ``CumprodWidened, thm := some ``cumprodWidened_proven },
  -- refuted
  { id := "reduce-foldr-reduce-first", juliaFile := "base/reduce.jl"
    juliaFns := ["foldr(op, itr)", "mapfoldr(f, op, itr)", "reduce_first"]
    statement := "foldr(op, [x]) returns reduce_first(op, x), as foldl and reduce do; e.g. foldr(+, [true]) == 1."
    source := "base/reduce.jl:397-403 (reduce_first docstring: the value returned by reduce, foldl or foldr over a single element)"
    status := .refuted, prop := ``FoldrReduceFirst, thm := some ``foldrReduceFirst_refuted
    issue := "none found (queries: foldr reduce_first, foldr single element, foldr hcat, FlipArgs, foldr Char String)"
    notes := "mapfoldr wraps op in FlipArgs and reduce_first(::FlipArgs, x) falls to the generic x: foldr(*, ['a']) === 'a', foldr(hcat, [v]) is a Vector, foldr(vcat, [v]) === v (aliased)." },
  { id := "reduce-any-dims-missing", juliaFile := "base/reducedim.jl"
    juliaFns := ["any(A; dims)", "all(A; dims)", "or_any", "and_all"]
    statement := "any(A; dims) holds any(slice) for every slice of a matrix of Bool and missing, three-valued like any(A)."
    source := "base/anyall.jl:8-10 (any docstring: missing if no true and some missing)"
    status := .refuted, prop := ``AnyDimsSlices, thm := some ``anyDimsSlices_refuted
    issue := "none found (queries: any dims missing, any dims missing TypeError, or_any missing, all dims missing; related merged PR #58185 introduced or_any/and_all)"
    notes := "or_any(x, y) = (x || y)::Bool throws TypeError on missing: any([missing false]; dims=2) throws, any([missing, false]) is missing. The Bool result array could not hold missing either." },
  { id := "reduce-count-init-float", juliaFile := "base/reduce.jl"
    juliaFns := ["count(A::Array{Bool}; init)", "_simple_count"]
    statement := "count(A; init) for an integer or Float64 init gives the same value for an Array{Bool} as for a tuple of the same Bools."
    source := "base/reduce.jl:1067-1072 (count docstring: init specifies the starting value and the output type)"
    status := .refuted, prop := ``CountInitAgrees, thm := some ``countInitAgrees_refuted
    issue := "none found (queries: count init Float64, count init rem, count Array{Bool} init, _simple_count)"
    notes := "_simple_count for Array{Bool} reduces with (n + c) % T, undefined for T = Float64: count([true]; init=0.0) throws MethodError, count((true,); init=0.0) == 1.0." },
  { id := "reduce-prod-init-mixed-sign", juliaFile := "base/reduce.jl"
    juliaFns := ["prod(A; init)", "mul_prod"]
    statement := "prod(v; init=one(S)) of a nonempty small-integer vector is the product in Int or UInt for all small S, as sum(v; init=zero(S)) is."
    source := "base/reduce.jl:578-584 (prod docstring: Int for small signed, UInt for small unsigned)"
    status := .refuted, prop := ``ProdInitWidened, thm := some ``prodInitWidened_refuted
    issue := "none found (queries: mul_prod, prod init mixed, prod small integer init, prod init UInt8; related merged PR #58374 widened add_sum for mixed small types)"
    notes := "mul_prod widens only two signed or two unsigned small integers; mul_prod(0x01, Int8(-1)) is UInt8 * Int8 = 0xff, so prod(Int8[-1]; init=0x01) === 0xff and prod(Int8[16,16]; init=0x01) === 0x00." },
  { id := "reduce-flatten-sum-empty", juliaFile := "base/reduce.jl"
    juliaFns := ["sum(::Iterators.Flatten)", "FlatteningRF", "reduce_empty"]
    statement := "sum(Iterators.flatten(vs)) equals sum(collect(Iterators.flatten(vs))) for vectors of Vector{Int}."
    source := "base/reduce.jl:470-472 (reduce docstring: init not needed when Julia can determine the neutral element of +)"
    status := .refuted, prop := ``FlattenSumAgrees, thm := some ``flattenSumAgrees_refuted
    issue := "none found (queries: flatten sum empty, Iterators.flatten reduce empty, flatten reduce_empty, reduce flatten empty)"
    notes := "No reduce_empty method for FlatteningRF: sum(Iterators.flatten([Int[], Int[]])) throws ArgumentError although eltype is Int; sum over an all-filtered Iterators.filter returns 0." },
  { id := "reduce-maxdims-union-eltype", juliaFile := "base/reducedim.jl"
    juliaFns := ["maximum(A; dims)", "minimum(A; dims)", "extrema(A; dims)", "findmax(A; dims)", "reducedim_init"]
    statement := "maximum(A; dims) succeeds for a nonempty matrix with element type Int, Float64 or Union{Int, Float64} and holds the maximum of each slice."
    source := "base/reducedim.jl:613-639 (maximum(A; dims) docstring: maximum value over the given dimensions)"
    status := .refuted, prop := ``MaxDimsUnion, thm := some ``maxDimsUnion_refuted
    issue := "none found (queries: maximum dims Union, maximum dims InexactError, reducedim InexactError, findmax dims InexactError, sum dims type unstable; related #32366, #55213, closed PR #55318, open PR #58418)"
    notes := "The result eltype is typeof(v0) when v0 isa promote_union(eltype) fails: maximum(Union{Int,Float64}[1, 2.5]; dims=1) throws InexactError; same for minimum, extrema, findmax and for type-unstable f." },
  { id := "reduce-maxdims-all-missing", juliaFile := "base/reducedim.jl"
    juliaFns := ["maximum(A; dims)", "minimum(A; dims)", "extrema(A; dims)", "reducedim_init"]
    statement := "maximum(A; dims) and minimum(A; dims) of a nonempty matrix of missing values hold missing for every slice."
    source := "base/missing.jl:129-137 (max/min with missing return missing); maximum([missing, missing]) === missing"
    status := .refuted, prop := ``MaxDimsMissing, thm := some ``maxDimsMissing_refuted
    issue := "none found (queries: maximum missing dims typemin, all missing dims maximum, nonmissingtype Union{} typemin; related closed #35308, merged PR #43604)"
    notes := "nonmissingtype(Missing) is Union{}, which passes Tnm <: Union{BitInteger, IEEEFloat, BigFloat}: typemin(Union{}) throws (MethodError on master, ArgumentError on 1.13.2)." },
  { id := "reduce-maxabs-dims-typemin", juliaFile := "base/reducedim.jl"
    juliaFns := ["maximum(abs, A; dims)", "maximum(abs2, A; dims)", "reducedim_init"]
    statement := "maximum(abs, A; dims) of a nonempty Matrix{Int} holds maximum(abs, slice) for every slice."
    source := "base/reducedim.jl:641-664 (maximum(f, A; dims) docstring)"
    status := .refuted, prop := ``MaxAbsDims, thm := some ``maxAbsDims_refuted
    issue := "#54920 (open, related: same reducedim_init method, Complex{Int} InexactError)"
    notes := "reducedim_init(::typeof(abs), ::typeof(max), ...) starts from 0 assuming abs(x) >= 0: maximum(abs, [typemin(Int);;]; dims=1) == [0;;] while maximum(abs, [typemin(Int)]) == typemin(Int); abs2 wraps negative too." },
  { id := "reduce-sumdims-init-narrow", juliaFile := "base/reducedim.jl"
    juliaFns := ["sum(A; dims, init)", "count(A; dims, init)", "mapreduce(f, op, A; dims, init)", "reducedim_initarray"]
    statement := "sum(A; dims, init=zero(S)) of a small-integer matrix holds sum(slice; init=zero(S)) for every slice."
    source := "base/reduce.jl:546-557 (sum docstring: Int for small signed integers); the dims-free sum(v; init) widens"
    status := .refuted, prop := ``SumDimsInit, thm := some ``sumDimsInit_refuted
    issue := "none found (queries: sum dims init Int8, count dims init, sum dims init InexactError, reduce dims init type; related merged PR #58374, open PR #58241)"
    notes := "The result array has eltype typeof(init): sum(Int8[100; 100;;]; dims=1, init=Int8(0)) throws InexactError while sum(Int8[100, 100]; init=Int8(0)) == 200; also sum([1.5 2.5]; dims=2, init=0) throws." },
  { id := "reduce-finddims-empty-shape", juliaFile := "base/reducedim.jl"
    juliaFns := ["findmax(A; dims)", "findmin(A; dims)", "argmax(A; dims)", "argmin(A; dims)"]
    statement := "findmax(A; dims) returns arrays of the reduced shape (size 1 along dims), the shape sum(A; dims) has."
    source := "invariant (findmax(A; dims) reduces over dims like maximum(A; dims) and sum(A; dims))"
    status := .refuted, prop := ``FindDimsShape, thm := some ``findDimsShape_refuted
    issue := "none found (queries: findmax dims empty, findmax empty dims shape, findmax zeros(0, reduced_indices0; related open PR #55628)"
    notes := "_findmax uses reduced_indices0, which keeps an empty reduced dimension at 0: findmax(zeros(0,0); dims=1) returns 0x0 arrays, sum gives 1x0 and maximum throws." },
  { id := "reduce-accumulate-dims-init", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate(op, A; dims, init)", "accumulate!(op, B, A; dims, init)"]
    statement := "accumulate(op, v; dims=d, init) with d beyond ndims(v) returns op(init, x) for every element x."
    source := "base/accumulate.jl:306-310 (accumulate! docstring: init is used to instantiate the accumulation)"
    status := .refuted, prop := ``AccumulateDimsInit, thm := some ``accumulateDimsInit_refuted
    issue := "none found (queries: accumulate dims init, accumulate init ignored, accumulate dims larger than ndims)"
    notes := "_accumulate! returns copyto!(B, A) when dims > ndims(A), ignoring init: accumulate(+, [1, 2]; dims=2, init=10) == [1, 2], while sum([1 2; 3 4]; dims=3, init=10) adds init." },
  { id := "reduce-cumsum-dims-nonpositive", juliaFile := "base/accumulate.jl"
    juliaFns := ["cumsum(v::AbstractVector; dims)", "cumsum!(out, v::AbstractVector; dims)", "_cumsum!"]
    statement := "cumsum(v; dims) equals accumulate(+, v; dims) for every dims, so dims <= 0 throws ArgumentError."
    source := "base/accumulate.jl:70-119 (cumsum docstring), 374-375 (dims must be a positive integer)"
    status := .refuted, prop := ``CumsumAccumulate, thm := some ``cumsumAccumulate_refuted
    issue := "none found (queries: cumsum dims=0, cumsum dims positive, cumsum dims negative, cumsum dims vector, _cumsum! dims)"
    notes := "_cumsum! does dim == 1 ? accumulate : copyto! without checking dims: cumsum([1,2,3]; dims=0) == [1,2,3] while accumulate, cumprod and cumsum of a matrix throw ArgumentError." }
]

end JuliaLean.Reduce

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
import JuliaLean.Reduce.ProofsFlatten
import JuliaLean.Reduce.ProofsDims
import JuliaLean.Reduce.Validation

namespace JuliaLean.Reduce

open JuliaLean.Registry

def entries : List Entry := [
  -- proven
  { id := "reduce-cat", juliaFile := "base/abstractarray.jl"
    juliaFns := ["reduce(vcat, A)", "reduce(hcat, A)"]
    statement := "reduce(vcat, vs) concatenates a nonempty vector of vectors; reduce(hcat, vs) puts equal-length vectors side by side and throws DimensionMismatch otherwise."
    source := "base/reduce.jl:477-478 (efficient reduce(vcat/hcat) methods)"
    status := .proven, prop := ``ReduceCatSpec, thm := some ``reduceCatSpec_proven },
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
  { id := "reduce-accumulate-dims-init", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate(op, A; dims, init)", "accumulate!(op, B, A; dims, init)"]
    statement := "accumulate(op, v; dims=d, init) with d beyond ndims(v) returns op(init, x) for every element x."
    source := "base/accumulate.jl:306-310 (accumulate! docstring: init is used to instantiate the accumulation)"
    status := .proven, prop := ``AccumulateDimsInit, thm := some ``accumulateDimsInit_proven
    issue := "none found (queries: accumulate dims init, accumulate init ignored, accumulate dims larger than ndims)"
    notes := "The target source applies init to each element when dims exceeds ndims(A); earlier versions copied A and ignored init." },
  { id := "reduce-cumsum-dims-nonpositive", juliaFile := "base/accumulate.jl"
    juliaFns := ["cumsum(v::AbstractVector; dims)", "cumsum!(out, v::AbstractVector; dims)", "_cumsum!"]
    statement := "cumsum(v; dims) equals accumulate(+, v; dims) for every dims, so dims <= 0 throws ArgumentError."
    source := "base/accumulate.jl:70-119 (cumsum docstring), 374-375 (dims must be a positive integer)"
    status := .refuted, prop := ``CumsumAccumulate, thm := some ``cumsumAccumulate_refuted
    issue := "none found (queries: cumsum dims=0, cumsum dims positive, cumsum dims negative, cumsum dims vector, _cumsum! dims)"
    notes := "_cumsum! does dim == 1 ? accumulate : copyto! without checking dims: cumsum([1,2,3]; dims=0) == [1,2,3] while accumulate, cumprod and cumsum of a matrix throw ArgumentError." }
]

end JuliaLean.Reduce

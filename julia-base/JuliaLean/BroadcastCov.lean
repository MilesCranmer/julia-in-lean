import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.BroadcastCov.ArrayMath
import JuliaLean.BroadcastCov.PermutedDims
import JuliaLean.BroadcastCov.Accumulate
import JuliaLean.BroadcastCov.BroadcastCore
import JuliaLean.BroadcastCov.BroadcastRanges
import JuliaLean.BroadcastCov.BitsSyntax
import JuliaLean.BroadcastCov.Refutations
import JuliaLean.BroadcastCov.StyleExact
import JuliaLean.BroadcastCov.LazyExact
import JuliaLean.BroadcastCov.AxisMetaExact
import JuliaLean.BroadcastCov.ShapeExact
import JuliaLean.BroadcastCov.IndexExact
import JuliaLean.BroadcastCov.MaterialExact
import JuliaLean.BroadcastCov.BitsExact
import JuliaLean.BroadcastCov.RangeExact
import JuliaLean.BroadcastCov.SyntaxExact

namespace JuliaLean.BroadcastCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "broadcastcov-array-basic", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["isreal", "iszero", "vec", "_sub", "conj!", "conj", "real", "imag",
      "-(::AbstractArray)", "+(::AbstractArray)", "*(::AbstractArray)"]
    statement := "Array predicates, vectorization, tuple-tail removal, conjugation, real and imaginary projections, and unary array operations return the elementwise values and shapes stated by their source equations."
    source := "base/abstractarraymath.jl:5-46,194-296; vec, conj, real and imag docstrings"
    status := .proven, prop := ``ArrayMath.BasicArrayMethods
    thm := some ``ArrayMath.basicArrayMethods },
  { id := "broadcastcov-array-dimensions", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["dropdims", "_dropdims", "insertdims", "_insertdims"]
    statement := "dropdims removes exactly the unique requested singleton dimensions and insertdims adds exactly the unique requested singleton dimensions, with the documented ArgumentError checks."
    source := "base/abstractarraymath.jl:48-166 (dropdims and insertdims docstrings and implementations)"
    status := .proven, prop := ``ArrayMath.DimensionMethods
    thm := some ``ArrayMath.dimensionMethods },
  { id := "broadcastcov-array-wrappers", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["circshift", "to_tuple", "pad", "repeat_inner_outer"]
    statement := "The circshift overloads convert their shifts and call the common multidimensional implementation; repeat tuple and dispatch helpers preserve their source-level arguments."
    source := "base/abstractarraymath.jl:335-413,488-505,554-557"
    status := .proven, prop := ``ArrayMath.WrapperMethods
    thm := some ``ArrayMath.wrapperMethods },

  { id := "broadcastcov-permuted-construct-index", juliaFile := "base/permuteddimsarray.jl"
    juliaFns := ["PermutedDimsArray", "genperm", "getindex", "setindex!", "isassigned"]
    statement := "Both constructors enforce tuple, permutation and inverse checks; reads, writes and assignment tests map a checked view index through the inverse permutation."
    source := "base/permuteddimsarray.jl:12-46,70-88; PermutedDimsArray docstring"
    status := .proven, prop := ``PermutedDims.ConstructorAndIndexMethods
    thm := some ``PermutedDims.constructorAndIndexMethods },
  { id := "broadcastcov-permuted-projections", juliaFile := "base/permuteddimsarray.jl"
    juliaFns := ["parent", "size", "axes", "has_offset_axes", "similar", "dataids",
      "unaliascopy", "cconvert", "pointer", "strides", "elsize"]
    statement := "Every PermutedDimsArray projection either forwards to the parent, permutes the parent tuple, or throws the deliberate pointer-offset ArgumentError."
    source := "base/permuteddimsarray.jl:48-68"
    status := .proven, prop := ``PermutedDims.ProjectionMethods
    thm := some ``PermutedDims.projectionMethods },
  { id := "broadcastcov-permuted-copy-reduce", juliaFile := "base/permuteddimsarray.jl"
    juliaFns := ["permutedims", "permutedims!", "copyto!", "_copy!", "_mapreduce_dim",
      "mapreducedim!", "showarg"]
    statement := "Permutation copies choose direct or tiled copying from the first moved dimension, reductions forward through the inverse view, and convenience overloads return the documented shape."
    source := "base/permuteddimsarray.jl:90-317,349-375; permutedims and permutedims! docstrings"
    status := .proven, prop := ``PermutedDims.CopyAndReductionMethods
    thm := some ``PermutedDims.copyAndReductionMethods },

  { id := "broadcastcov-accumulate-wrappers", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate_pairwise", "cumsum!", "_cumsum!", "cumsum", "cumprod!",
      "cumprod", "accumulate(::Tuple)"]
    statement := "The public cumulative wrappers dispatch to the pairwise or ordinary prefix scan selected in the source and return the corresponding prefix values."
    source := "base/accumulate.jl:38-303; cumsum, cumprod and accumulate docstrings"
    status := .proven, prop := ``Accumulate.WrapperMethods
    thm := some ``Accumulate.wrapperMethods },
  { id := "broadcastcov-accumulate-dispatch-promote", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate", "accumulate!", "_accumulate1!", "_accumulate_promote_op", "f", "g", "h"]
    statement := "Accumulation validates keywords in source order, the one-dimensional loop scans or copies according to dims, and the three inference-only mock functions perform their written passes."
    source := "base/accumulate.jl:281-303,347-356,436-491"
    status := .proven, prop := ``Accumulate.DispatchAndPromotionMethods
    thm := some ``Accumulate.dispatchAndPromotionMethods },

  { id := "broadcastcov-linrange-shift-elementwise", juliaFile := "base/broadcast.jl"
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(+), ::LinRange, ::Number)",
      "broadcasted(::DefaultArrayStyle{1}, ::typeof(-), ::LinRange, ::Number)"]
    statement := "Broadcasting + or - between a Float64 LinRange and a scalar has the same Float64 elements as applying the operation to each original element."
    source := "base/broadcast.jl:785-792 (broadcast applies the function over container elements)"
    status := .refuted, prop := ``Refutations.LinRangeShiftElementwise
    thm := some ``Refutations.linRangeShiftElementwise_refuted
    issue := "none found (queries: LinRange broadcast scalar rounding; range broadcast not elementwise)"
    notes := "LinRange(0.0, 1.0, 7) .+ 2.0 and .- 2.0 differ by one ulp from the materialized elementwise operations on release and nightly." },
  { id := "broadcastcov-steprangelen-div-elementwise", juliaFile := "base/broadcast.jl"
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(/), ::StepRangeLen, ::Number)"]
    statement := "Broadcast division of a Float64 StepRangeLen by a scalar has the same Float64 elements as dividing each original element."
    source := "base/broadcast.jl:785-792 (broadcast applies the function over container elements)"
    status := .refuted, prop := ``Refutations.StepRangeLenDivElementwise
    thm := some ``Refutations.stepRangeLenDivElementwise_refuted
    issue := "none found (queries: broadcast range division rounding; StepRangeLen broadcast division)"
    notes := "range(0.0; step=0.25, length=6) ./ 3.0 differs by one ulp at the last element from collect(r) ./ 3.0 on release and nightly." }
] ++ StyleExact.entries
  ++ LazyExact.entries
  ++ AxisMetaExact.entries
  ++ ShapeExact.entries
  ++ IndexExact.entries
  ++ MaterialExact.entries
  ++ BitsExact.entries
  ++ RangeExact.entries
  ++ SyntaxExact.entries

end JuliaLean.BroadcastCov

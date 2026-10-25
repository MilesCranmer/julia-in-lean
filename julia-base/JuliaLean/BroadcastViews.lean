import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.BroadcastViews.Shape
import JuliaLean.BroadcastViews.ShapeProofs
import JuliaLean.BroadcastViews.Alias
import JuliaLean.BroadcastViews.AliasProofs
import JuliaLean.BroadcastViews.NestedView
import JuliaLean.BroadcastViews.NestedViewProofs
import JuliaLean.BroadcastViews.Ranges
import JuliaLean.BroadcastViews.RangeProofs
import JuliaLean.BroadcastViews.FastLinear
import JuliaLean.BroadcastViews.FastLinearProofs
import JuliaLean.BroadcastViews.Validation
import JuliaLean.BroadcastViews.Stride

namespace JuliaLean.BroadcastViews

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- proven
  { id := "broadcastviews-shape-combination", juliaFile := "base/broadcast.jl"
    juliaFns := ["Base.Broadcast.broadcast_shape", "_bcs", "_bcs1(::Integer, ::Integer)"]
    statement := "broadcast_shape on Int size tuples returns as many dimensions as the longest tuple; in each dimension every input extent is 1 or the result extent, which is one of the inputs. It throws only DimensionMismatch, and only when two extents of one dimension differ and neither is 1."
    source := "base/broadcast.jl:506-518 (broadcast_shape docstring); manual doc/src/manual/arrays.md:1133-1135 (broadcast expands singleton dimensions)", status := .proven
    prop := ``ShapeCombination, thm := some ``shapeCombination
    notes := "Differential check: 20000 random size-tuple lists (up to 3 tuples of up to 3 dims, extents 0..3) against the spec and against broadcast over zeros(...) arrays, 0 mismatches. Same code in 1.13.2." },
  { id := "broadcastviews-nested-view-compose", juliaFile := "base/subarray.jl"
    juliaFns := ["view(::SubArray, I...)", "_maybe_reindex", "reindex", "getindex(::SubArray, ::Vararg{Int})"]
    statement := "For views whose indices are Ints, Colons (one-based Slices) or one-based integer vectors (ranges, Vector{Int}, logical masks, CartesianIndex{1} arrays), view(view(A, I...), J...)[K...] reads the parent element that view(A, I...) reads at J[K]: reindex(reindex(I, J), K) == reindex(I, reindex(J, K)) for every in-bounds K."
    source := "base/subarray.jl:175-183 (view docstring), 282-288 (reindex: A[i, j][x, y] is A[i[x], j[y]])", status := .proven
    prop := ``NestedViewCompose, thm := some ``nestedViewCompose
    notes := "IdentityUnitRange indices are excluded (known bug #62906, reported as reinterpretarrays-nested-slice-offset). Differential check: 8899 random nested views of a 3x4x5 array over Int, Colon, UnitRange, StepRange, Vector{Int}, Bool masks, CartesianIndex{1} arrays, CartesianIndices, OneTo and zero-step StepRangeLen indices; element values, axes and linear versus Cartesian indexing all agreed with A[I...][J...] (the reported mismatches were test-harness artifacts: repeated parent indices in the write check and 0-dimensional results)." },
  { id := "broadcastviews-fast-linear-view", juliaFile := "base/subarray.jl"
    juliaFns := ["viewindexing", "compute_stride1", "compute_offset1", "compute_linindex", "getindex(::FastSubArray, ::Int)"]
    statement := "For every view of an Array that SubArray marks IndexLinear (leading Int indices, then Colons optionally followed by one unit range, or one Int range, then Int indices), V[i] with i = LinearIndices(V)[js...] reads the parent element that Cartesian indexing V[js...] reads (offset1 + stride1*i with wrapping Int arithmetic), for every in-bounds view of a parent whose length is an Int."
    source := "base/subarray.jl:10 (SubArray docstring: L is true for types that support fast linear indexing), 175-183 (view docstring)", status := .proven
    prop := ``FastLinearView, thm := some ``fastLinearView
    notes := "Covers the Slice-prefix and leading-scalar layouts not covered by reinterpretarrays-view-linear-index (range followed by scalars). Model checked against Julia's own V.offset1/V.stride1 on 40 random linear views and viewindexing on 15 Cartesian ones (Validation.lean); a random differential of linear versus Cartesian indexing over 8899 nested views found no mismatch." },
  { id := "broadcastviews-overlap-conservative", juliaFile := "base/multidimensional.jl"
    juliaFns := ["Base.mightalias(::SubArray, ::SubArray)", "_indicesmightoverlap"]
    statement := "For two views of the same parent whose indices are Ints, unit ranges, step ranges or Int vectors (no arrays of CartesianIndex) and have the same count, _indicesmightoverlap returns true whenever the views select a common parent element."
    source := "Base.mightalias docstring (base/abstractarray.jl:1596-1601: a conservative test)", status := .proven
    prop := ``OverlapConservativeNoCarts, thm := some ``overlapConservativeNoCarts
    notes := "Pins broadcastviews-cartesian-alias to CartesianIndex arrays: without them the per-dimension test is sound. The Idx model was checked against Base._indicesmightoverlap on 60 random view pairs (Validation.lean)." },
  -- refuted
  { id := "broadcastviews-cartesian-alias", juliaFile := "base/multidimensional.jl"
    juliaFns := ["Base.mightalias(::SubArray, ::SubArray)", "_indicesmightoverlap", "Base.Broadcast.broadcast_unalias", "materialize!"]
    statement := "dest .= src for two views of one parent with the same number of elements equals dest .= copy(src) whenever dest selects no parent element twice."
    source := "Base.mightalias docstring (base/abstractarray.jl:1596-1601: a conservative test); base/broadcast.jl:1004-1008 (preprocess unaliases arguments from dest)", status := .refuted
    prop := ``AliasAssignFresh, thm := some ``aliasAssignFresh_refuted
    issue := "none found (queries: mightalias CartesianIndex, _indicesmightoverlap, indicesmightoverlap, aliasing view CartesianIndex, unalias CartesianIndex, mightalias SubArray, mightalias, view alias findall broadcast); related #50820 (open), #31392 (open)"
    notes := "M = [1 2 3; 4 5 6; 7 8 9]; @views M[1, :] .= M[[CartesianIndex(3,3), CartesianIndex(2,2), CartesianIndex(1,1)]] gives row [9, 5, 9] instead of [9, 5, 1]: _indicesmightoverlap compares the scalar row index 1 with CartesianIndex elements using in, which is false. Same in 1.13.2. Random differential (30252 aliasing view pairs) found only this cause plus repeated-index destinations." },
  { id := "broadcastviews-repeated-index-alias", juliaFile := "base/broadcast.jl"
    juliaFns := ["Base.Broadcast.broadcast_unalias", "Base.Broadcast.preprocess", "copyto!(::AbstractArray, ::Broadcasted{Nothing})"]
    statement := "dest .= dest .+ c for a view dest equals computing dest .+ c into a fresh array first, as P[I...] .+= c does."
    source := "base/broadcast.jl:995-1001 (comment: the indices on the LHS and RHS will always match); base/views.jl:297-303 (@views docstring)", status := .refuted
    prop := ``SelfAssignFresh, thm := some ``selfAssignFresh_refuted
    issue := "#31392 (open, duplicate), PR #31407 (open)"
    notes := "x = [10, 20, 30]; @views x[[1, 1, 2]] .+= 1 gives [12, 21, 30], x[[1, 1, 2]] .+= 1 gives [11, 21, 30]. Same in 1.13.2." },
  { id := "broadcastviews-range-singleton", juliaFile := "base/broadcast.jl"
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(+), ::AbstractRange, ::AbstractRange)", "+(::OrdinalRange, ::OrdinalRange)"]
    statement := "r1 .+ r2 for two UnitRange{Int}s equals collect(r1) .+ collect(r2): a length-1 range is expanded and only unequal non-singleton lengths throw DimensionMismatch."
    source := "manual doc/src/manual/arrays.md:1133-1135 (broadcast expands singleton dimensions); base/broadcast.jl:531", status := .refuted
    prop := ``RangeBroadcastPair, thm := some ``rangeBroadcastPair_refuted
    issue := "none found (queries: range broadcast DimensionMismatch length 1, broadcast two ranges singleton, argument dimensions must match broadcast range, broadcast ranges length one, range plus range broadcast, ranges broadcasting singleton dimension, range broadcast, broadcast_shape)"
    notes := "(1:3) .+ (5:5) throws DimensionMismatch; also .-, OneTo, StepRange, LinRange and Float64 ranges, singleton on either side. Same in 1.13.2." },
  { id := "broadcastviews-range-ldiv", juliaFile := "base/broadcast.jl"
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(\\), ::Number, ::StepRangeLen)"]
    statement := "x .\\ r returns a range for every floating-point colon range r = a:s:b."
    source := "invariant (x .\\ r computes x \\ r[i]); base/operators.jl:683-685 (\\ docstring)", status := .refuted
    prop := ``RangeLdivTotal, thm := some ``rangeLdivTotal_refuted
    issue := "none found (queries: TwicePrecision adjoint, range ldiv broadcast, ldiv StepRangeLen, TwicePrecision MethodError broadcast, range broadcast)"
    notes := "2.0 .\\ (0.0:0.5:2.0) throws MethodError: no method matching adjoint(::Base.TwicePrecision{Float64}). Float32 ranges work. Same in 1.13.2." },
  { id := "broadcastviews-range-unsigned-float", juliaFile := "base/broadcast.jl"
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(-), ::AbstractRange, ::Number)", "Base.floatrange", "unsafe_getindex(::StepRangeLen, ::Integer)"]
    statement := "r .- x for an unsigned StepRange{UInt64,UInt64} r and an integral x::Float64 has the elements r[i] - x of collect(r) .- x (small values, exact Float64 arithmetic)."
    source := "invariant (range broadcast methods, base/broadcast.jl:1174-1242, are optimizations of elementwise broadcast)", status := .refuted
    prop := ``RangeUnsignedFloat, thm := some ``rangeUnsignedFloat_refuted
    issue := "none found (queries: unsigned range float broadcast, range length UInt float, UInt range float, StepRangeLen unsigned offset, floatrange UInt, unsigned range negative broadcast, range broadcast)"
    notes := "(UInt(1):UInt(2):UInt(5)) .- 2.0 == [3.6893488147419103e19, 1.0, 3.0]; -2.0 .* (UInt(1):UInt(3)) throws InexactError. length(r)::UInt64 makes floatrange compute in UInt64. Same in 1.13.2." },
  { id := "broadcastviews-range-negate-unsigned", juliaFile := "base/broadcast.jl"
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(-), ::OrdinalRange)"]
    statement := ".-r for r::UnitRange{UInt8} has the elements of .-collect(r)."
    source := "invariant (range broadcast methods, base/broadcast.jl:1174-1242, are optimizations of elementwise broadcast)", status := .refuted
    prop := ``RangeNegUnsigned, thm := some ``rangeNegUnsigned_refuted
    issue := "none found (queries: negate unsigned range, unsigned range negative broadcast, range broadcast); related #54364 (open)"
    notes := ".-(0x00:0x02) is the empty 0x00:-1:0x01 instead of [0x00, 0xff, 0xfe]; .-(0x01:0x00) has 256 elements. Unary -r is correct. Same in 1.13.2." },
  { id := "broadcastviews-shape-mixed-singleton", juliaFile := "base/broadcast.jl"
    juliaFns := ["Base.Broadcast.broadcast_shape", "_bcs1(::Integer, ::Any)"]
    statement := "_bcs1 on an Int size and a one-based axis (either order) throws exactly when both lengths differ from 1 and from each other, and otherwise returns an entry of the non-singleton length."
    source := "base/broadcast.jl:506-518 (broadcast_shape docstring), 531 and 536 (singletons broadcast)", status := .refuted
    prop := ``ShapeMixedSingleton, thm := some ``shapeMixedSingleton_refuted
    issue := "none found (queries: broadcast_shape OneTo, broadcast_shape integer axes, broadcast_shape); related #45921 (closed)"
    notes := "Broadcast.broadcast_shape((3,), (Base.OneTo(1),)) throws DimensionMismatch while (3,) with (1,) gives (3,). Internal function; P3. Same in 1.13.2." },
  { id := "broadcastviews-stride-zero-dim", juliaFile := "base/subarray.jl"
    juliaFns := ["stride(::SubArray, ::Integer)", "strides(::SubArray)", "substrides"]
    statement := "stride(V, k) returns a value for every view V of an Array with Int, Colon and Int-range indices and every k >= 1."
    source := "base/abstractarray.jl:580-582 (stride docstring), 597-607 (zero-dimensional arrays give 1); base/reinterpretarray.jl:205-206 (Arrays give length(A) past the last dimension)", status := .refuted
    prop := ``StrideTotal, thm := some ``strideTotal_refuted
    issue := "none found (queries: stride zero-dimensional view, stride SubArray BoundsError, stride 0-dimensional)"
    notes := "stride(view(zeros(3, 4), 1, 2), 1) throws BoundsError (strides(V) == () and base/subarray.jl:446 takes strides(V)[end]); stride(fill(0.0), 1) == 1. Probed: views with zero-step StepRangeLen, negative steps and k past ndims return values. Same in 1.13.2." }
]

end JuliaLean.BroadcastViews

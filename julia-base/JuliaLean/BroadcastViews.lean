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
  { id := "broadcastviews-fast-linear-view", juliaFile := "base/subarray.jl"
    juliaFns := ["viewindexing", "compute_stride1", "compute_offset1", "compute_linindex", "getindex(::FastSubArray, ::Int)"]
    statement := "For every view of an Array that SubArray marks IndexLinear (leading Int indices, then Colons optionally followed by one unit range, or one Int range, then Int indices), V[i] with i = LinearIndices(V)[js...] reads the parent element that Cartesian indexing V[js...] reads (offset1 + stride1*i with wrapping Int arithmetic), for every in-bounds view of a parent whose length is an Int."
    source := "base/subarray.jl:10 (SubArray docstring: L is true for types that support fast linear indexing), 175-183 (view docstring)", status := .proven
    prop := ``FastLinearView, thm := some ``fastLinearView
    notes := "Covers the Slice-prefix and leading-scalar layouts not covered by reinterpretarrays-view-linear-index (range followed by scalars). Model checked against Julia's own V.offset1/V.stride1 on 40 random linear views and viewindexing on 15 Cartesian ones (Validation.lean); a random differential of linear versus Cartesian indexing over 8899 nested views found no mismatch." }
  -- refuted
]

end JuliaLean.BroadcastViews

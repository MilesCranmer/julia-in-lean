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
    thm := some ``Accumulate.dispatchAndPromotionMethods }

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

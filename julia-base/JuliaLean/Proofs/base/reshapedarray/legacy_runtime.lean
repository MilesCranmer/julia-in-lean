import JuliaLean.Proofs.base.reshapedarray
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.reshapedarray.LegacyRuntime
open JuliaLean.Registry

def entries : List Entry := [
  { id := "multidimcov-reshape-bang-field", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["reshape!(a::Array{T,N}, dims::NTuple{N,Int}) where {T,N}"]
    statement := "reshape!(a, dims) with the same rank and element count returns the identical array after updating its dimensions."
    source := "base/reshapedarray.jl:55-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .todo, prop := ``JuliaLean.Proofs.base.reshapedarray.ReshapeBangUpdatesDimensions
    notes := "The native model delegates setfield!(a, :dims, dims) to an unbound setter and ReshapedError has no FieldError constructor. Array's real :ref/:size field descriptor and the missing-:dims-field error must be bound before the historical refutation can be re-proved." }
]

end JuliaLean.Proofs.base.reshapedarray.LegacyRuntime

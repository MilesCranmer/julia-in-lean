import JuliaLean.base.operators
import JuliaLean.base.number
import JuliaLean.base.tuple
import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.bitarray
import JuliaLean.base.checked
import JuliaLean.base.abstractarray
import JuliaLean.base.range
import JuliaLean.Proofs.base.range
import JuliaLean.base.indices
import JuliaLean.Proofs.base.array
import JuliaLean.Proofs.base.bitarray.common.reshape



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesBitreshape1 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bitreshape-fresh-allocation", juliaFile := "base/bitarray.jl",
    juliaFns := ["_bitreshape(B::BitArray, dims::NTuple{N,Int}) where N"],
    statement := "The internal reshape helper applies native dimension validation before checking the mathematical element count; failures preserve the complete state. Compatible dimensions always create a fresh header sharing the source chunks, including equal-shape direct calls, and retain the temporary zero-shaped chunk allocation while preserving all old object headers and data.",
    source := "base/bitarray.jl:476-485; base/boot.jl:782-818; base/reshapedarray.jl:67-79", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.BitreshapeFreshAllocationAndErrors, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15BitreshapeFreshAllocation_proven,
    notes := "Independent internal identity/allocation invariant. No correctness callback, callee law, successful-result premise or physical source-chunk restriction appears in the property." }
]
end JuliaLean.Proofs.base.bitarray


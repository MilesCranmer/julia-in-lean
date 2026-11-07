import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- An `IO` input to `countlines`, represented by the chunks returned by
`readbytes!(io, a)`. The public `readbytes!` contract says each call returns at
most its `nb = length(a) = 8192` argument (`base/io.jl:1295-1300`). -/
structure CountlinesIO where
  chunks : List (List UInt8)
  chunkLength : ∀ chunk ∈ chunks, chunk.length ≤ 8192

/-- The array indices computed by the nested `while` and `for i=1:nb` loops of
`countlines`, `base/io.jl:1700-1714`. -/
def countlinesAccesses (io : CountlinesIO) : List Nat :=
  io.chunks.flatMap (fun chunk => oneBasedLoop chunk.length)

/-- The byte offsets read by the endianness probe from its one-element
`Vector{UInt32}`, `base/io.jl:817-834`. -/
def endianBomAccesses : List Nat := [0]

/-- The endianness probe reads one byte from four allocated bytes, and every
`countlines` scan index is computed from a documented-size read chunk. -/
def IOSafe : Prop :=
  (∀ offset ∈ endianBomAccesses, offset < 4) ∧
  (∀ (io : CountlinesIO) i, i ∈ countlinesAccesses io → inOneBased 8192 i)

theorem ioSafe_proven : IOSafe := by
  constructor
  · intro offset ho
    simp [endianBomAccesses] at ho
    omega
  · intro io i hi
    simp only [countlinesAccesses, List.mem_flatMap, oneBasedLoop,
      List.mem_map, List.mem_range] at hi
    obtain ⟨chunk, hc, k, hk, rfl⟩ := hi
    have hlen := io.chunkLength chunk hc
    unfold inOneBased
    omega

end JuliaLean.MemSafety.G3

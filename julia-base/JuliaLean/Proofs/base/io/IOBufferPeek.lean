import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.iobuffer
import JuliaLean.Proofs.base.iobuffer.Ops
import JuliaLean.Proofs.base.iobuffer.Props
import JuliaLean.Proofs.base.iobuffer.Refuted
import JuliaLean.Proofs.base.iobuffer.Inv
import JuliaLean.Proofs.base.iobuffer.Proven

namespace JuliaLean.IOBuffers

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- proven
  -- refuted
  { id := "iobuffers-peek-clears-mark", juliaFile := "base/io.jl"
    juliaFns := ["peek(::IO, ::Type{T})"]
    statement := "peek(io, T) leaves the stream's mark unchanged."
    source := "base/essentials.jl:1539 (peek docstring: without advancing the current position)", status := .refuted
    prop := ``PeekKeepsMark, thm := some ``peekKeepsMark_refuted
    issue := "none found (queries: peek mark reset, peek clobbers mark, peek Char mark, peek resets mark, peek unmark, peek mark IOBuffer)"
    notes := "Generic peek = mark; read; reset. IOBuffer(\"abc\"); mark; read UInt8; peek(io, Char) or peek(io, Int8) unmarks io." }
]

end JuliaLean.IOBuffers

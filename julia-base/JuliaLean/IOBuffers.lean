import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.IOBuffers.Model
import JuliaLean.IOBuffers.Ops
import JuliaLean.IOBuffers.Props
import JuliaLean.IOBuffers.Refuted
import JuliaLean.IOBuffers.Inv
import JuliaLean.IOBuffers.Proven

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

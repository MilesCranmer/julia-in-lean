import JuliaLean.IOCov.Common

/-!
`show(io, b::GenericIOBuffer)` of `base/iobuffer.jl` at master `bbfa0ce4150`, on the
fields it prints.
-/

namespace JuliaLean.IOCov.IOBuf

/-- The `GenericIOBuffer` fields used by `show` and `position`. -/
structure Buf where
  size : Int
  ptr : Int
  offsetOrCompacted : Int
  deriving DecidableEq, Repr

/-- `get_offset(io) = max(0, io.offset_or_compacted)`, line 163. -/
def getOffset (b : Buf) : Int := max 0 b.offsetOrCompacted
/-- `get_compacted(io) = max(0, -io.offset_or_compacted)`, line 164. -/
def getCompacted (b : Buf) : Int := max 0 (-b.offsetOrCompacted)
/-- `position(io) = io.ptr - io.offset_or_compacted - 1`, lines 470-473. -/
def position (b : Buf) : Int := b.ptr - b.offsetOrCompacted - 1
/-- The `size=` and `ptr=` values printed by `show(io, b)`, lines 334-342. -/
def showSize (b : Buf) : Int := b.size - getOffset b
def showPtr (b : Buf) : Int := b.ptr - getOffset b

/-- The printed `ptr` is the read position plus one, as in the docstring examples
(`base/io.jl:1628-1632`), for every buffer. -/
def ShowPtrPosition : Prop := ∀ b : Buf, showPtr b = position b + 1

/-- A `PipeBuffer` that has discarded 90 read bytes (`offset_or_compacted = -90`, `ptr = 1`)
prints `ptr=1` at position 90. -/
theorem showPtrPosition_refuted : ¬ ShowPtrPosition := by
  intro h
  have := h ⟨2010, 1, -90⟩
  simp [showPtr, position, getOffset] at this
  omega

/-- For a buffer that was not compacted (`offset_or_compacted ≥ 0`), `ptr` is the position
plus one and `size` the size relative to the offset. -/
def ShowUncompacted : Prop :=
  ∀ b : Buf, 0 ≤ b.offsetOrCompacted → showPtr b = position b + 1 ∧ showSize b = b.size - b.offsetOrCompacted
theorem showUncompacted : ShowUncompacted := by
  intro b h
  have : max 0 b.offsetOrCompacted = b.offsetOrCompacted := by omega
  simp [showPtr, showSize, position, getOffset, this]

end JuliaLean.IOCov.IOBuf

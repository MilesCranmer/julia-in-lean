import JuliaLean.base.iobuffer

/-!
`show(io, b::GenericIOBuffer)` of `base/iobuffer.jl` at master `bbfa0ce4150`, on the
fields it prints.
-/

namespace JuliaLean.IOCov.IOBuf


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

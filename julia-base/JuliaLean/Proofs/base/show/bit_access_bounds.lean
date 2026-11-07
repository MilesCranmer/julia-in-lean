import JuliaLean.Core

namespace JuliaLean.MemSafety.G5

/-- Inputs affecting the branch in show.jl:530-557. Structured values take the
field loop; only the raw-bits branch reaches the pointer conversion and load. -/
structure ShowBitsInput where
  bitSize : Nat
  rawBitsBranch : Bool

/-- Raw byte offsets computed from `bitsizeof(t)`, `cld`, pointer conversion,
and the descending `(nbytes-1):-1:0` loop. -/
def showBitsAccesses (input : ShowBitsInput) : List Nat :=
  if input.rawBitsBranch then (List.range ((input.bitSize + 7) / 8)).reverse else []

/-- Every raw display load is within the `cld(bitsizeof(t), 8)` bytes occupied
by the bits object. -/
def ShowBitsAccessesInBounds : Prop :=
  ∀ input offset, offset ∈ showBitsAccesses input → offset < (input.bitSize + 7) / 8

theorem showBitsAccessesInBounds : ShowBitsAccessesInBounds := by
  intro input offset h
  unfold showBitsAccesses at h
  split at h
  · simpa only [List.mem_reverse, List.mem_range] using h
  · contradiction


end JuliaLean.MemSafety.G5

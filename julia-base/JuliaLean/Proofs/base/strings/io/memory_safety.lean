import JuliaLean.Proofs.base.strings.substring.memory_safety

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- String-backed IOBuffer constructors, `base/strings/io.jl:288-307`: a String
wraps all its bytes, while a SubString view starts at its stored parent offset
and has exactly its stored byte length. -/
def stringIOAccesses (s : SubView) : List Access :=
  [span0 s.parentLength s.offset s.length]

def StringIOInBounds : Prop := ∀ s, s.valid → accessesSafe (stringIOAccesses s)

theorem stringIOInBounds_proven : StringIOInBounds := by
  intro s hs
  unfold SubView.valid at hs
  simpa [stringIOAccesses, accessesSafe, Access.safe, span0] using hs

end JuliaLean.MemSafety.G1

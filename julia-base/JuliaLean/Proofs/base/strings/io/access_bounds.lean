import JuliaLean.Proofs.base.strings.substring.access_bounds

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- String-backed IOBuffer construction combines the SubString view invariant with the
checked remaining-span rule used by `wrap`; `base/strings/io.jl:288-307`. -/
def StringIOBounds : Prop := SubstringBounds ∧ WrapBounds

theorem stringIOBounds_proven : StringIOBounds := ⟨substringBounds_proven, wrapBounds_proven⟩

end JuliaLean.MemSafety.G1

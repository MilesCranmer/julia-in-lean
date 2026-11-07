import JuliaLean.Proofs.base.array.cartesian_contracts

namespace JuliaLean.Multidim

/-- `findfirst(zeros(Bool, 0, 3))` reads `A[1, 1]` and throws `BoundsError`:
`CartesianIndex(1, 1) > CartesianIndex(0, 3)` is false. -/
theorem findfirst_empty_0x3 : findfirst inc ciLess [0, 3] (fun _ => false) = .error .boundsError := by
  decide

theorem findfirstCartesian_refuted : ¬ FindfirstCartesian := by
  intro h
  have := h [0, 3] (fun _ => false) (by decide)
  rw [findfirst_empty_0x3] at this
  exact absurd this (by decide)

end JuliaLean.Multidim

import JuliaLean.base.reducedim
import JuliaLean.Core

namespace JuliaLean.ReduceCov.Dims

/-- Every integer dimension at least one is valid, including trailing dimensions
larger than `typemax(Int)`. -/
def ValidRegionUnsigned : Prop := ∀ d : Int, 1 ≤ d → checkValidRegion d = .ok ()

theorem validRegionUnsigned_refuted : ¬ ValidRegionUnsigned := by
  intro h
  have counterexample := h (2 ^ 63) (by omega)
  revert counterexample
  decide

/-- `init=false` should combine the input with the value already stored in
`rval`, as the other in-place reductions do. -/
def FindInplaceInit : Prop :=
  (∀ old xs, findMaxInplace false old xs = xs.foldl max old) ∧
  (∀ old xs, findMinInplace false old xs = xs.foldl min old)

theorem findInplaceInit_refuted : ¬ FindInplaceInit := by
  intro h
  have counterexample := h.1 100 [1, 2]
  revert counterexample
  decide

/-- In-place min, max and extrema use the same empty-reduction `ArgumentError`
as their allocating forms. -/
def InplaceEmptyError : Prop :=
  ∀ _ : Unit,
    initExtremaInplace true [] = .error (argErr "reducing over an empty collection is not allowed") ∧
    mapfirstForInit [] = .error (argErr "reducing over an empty collection is not allowed") ∧
    inplaceExtrema true [] = .error (argErr "reducing over an empty collection is not allowed")

theorem inplaceEmptyError_refuted : ¬ InplaceEmptyError := by
  intro h
  have counterexample := h ()
  simp [initExtremaInplace, mapfirstForInit, inplaceExtrema, boundsErr, argErr] at counterexample

end JuliaLean.ReduceCov.Dims

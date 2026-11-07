import JuliaLean.base.iterators
import JuliaLean.Proofs.base.iterators.coverage_zip

/-!
# `intersect(::ProductIterator, ::ProductIterator)`

The model uses lists for product factors and product elements. Julia's method
at `base/iterators.jl:1257` broadcasts `intersect` over the two factor tuples,
then wraps those factors in `ProductIterator`. Tuple broadcasting repeats a
one-element tuple against a longer tuple.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Products of different arity have no common tuple, so their intersection
must be empty. This is the `intersect` docstring's set invariant. -/
def ProductIntersect : Prop :=
  ∀ as bs, as.length ≠ bs.length → productIntersect as bs = .ok []

theorem productIntersect_refuted : ¬ ProductIntersect := by
  intro h
  have hactual : productIntersect [[1, 2, 3]] [[1, 2], [1, 2]] =
      .ok [[1, 1], [2, 1], [1, 2], [2, 2]] := by rfl
  have hempty := h [[1, 2, 3]] [[1, 2], [1, 2]] (by decide)
  rw [hactual] at hempty
  cases hempty

end JuliaLean.IteratorsCov

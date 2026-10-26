import JuliaLean.IteratorsCov.Zip

/-!
# `intersect(::ProductIterator, ::ProductIterator)`

The model uses lists for product factors and product elements. Julia's method
at `base/iterators.jl:1257` broadcasts `intersect` over the two factor tuples,
then wraps those factors in `ProductIterator`. Tuple broadcasting repeats a
one-element tuple against a longer tuple.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Set-like intersection of two integer factors, preserving the first
factor's order. -/
def factorIntersect (a b : List Int) : List Int := a.filter b.contains

/-- Julia tuple broadcasting for the binary call `intersect.(as, bs)` used by
`intersect(::ProductIterator, ::ProductIterator)` (`base/iterators.jl:1257`). -/
def broadcastFactorIntersect (as bs : List (List Int)) : R (List (List Int)) :=
  if as.length = bs.length then .ok (List.zipWith factorIntersect as bs)
  else match as, bs with
  | [a], _ => .ok (bs.map (factorIntersect a))
  | _, [b] => .ok (as.map (fun a => factorIntersect a b))
  | _, _ => .error .dimensionMismatch

/-- Elements of a product of factors. The first factor changes fastest in
Julia; reversing the construction order gives that observable ordering. -/
def productElements : List (List Int) → List (List Int)
  | [] => [[]]
  | a :: as => (productElements as).flatMap fun tail => a.map fun x => x :: tail

/-- The body of Julia's method: broadcast the factor intersections and build
the resulting product. -/
def productIntersect (as bs : List (List Int)) : R (List (List Int)) := do
  pure (productElements (← broadcastFactorIntersect as bs))

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

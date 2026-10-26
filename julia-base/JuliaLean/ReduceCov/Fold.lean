import JuliaLean.Reduce.Val

namespace JuliaLean.ReduceCov.Fold

open JuliaLean.Reduce

/-- `reduce(op, a::Number) = a`, `base/reduce.jl:500`. -/
def reduceNumber (a : Val) : Val := a

/-- A single-element reduction with `+` applies `reduce_first(+, a)`, as the
`reduce_first` docstring promises for every single-element iterator. -/
def ReduceNumberFirst : Prop := ∀ a : Val, reduceNumber a = Val.firstPlus a

theorem reduceNumberFirst_refuted : ¬ ReduceNumberFirst := by
  intro h
  have counterexample := h (.bool true)
  revert counterexample
  decide

end JuliaLean.ReduceCov.Fold

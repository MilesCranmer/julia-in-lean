import JuliaLean.base.stacktraces


namespace JuliaLean.ErrorShow


def StackLookupAndRemoval : Prop :=
  (∀ frames : List Frame, lookupFrames (.raw frames) = frames) ∧
  (∀ frames : List Frame, lookupFrames (.debugTraversal frames) = frames.reverse) ∧
  (∀ stack : List Frame, ∀ names : List String,
    removeFrames stack names =
      (stack.reverse.takeWhile fun frame => !names.contains frame.functionName).reverse)

theorem stackLookupAndRemoval_proven : StackLookupAndRemoval := by
  constructor
  · intro frames
    rfl
  constructor
  · intro frames
    rfl
  · intro stack names
    rfl

end JuliaLean.ErrorShow

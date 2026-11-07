import JuliaLean.base.views

namespace JuliaLean.NumMisc.Coverage

open JuliaLean
def ViewBoundaryBehavior : Prop :=
  (∀ first last token, replaceBoundary first last token = match token with
    | .first => first | .last => last | .value n => n) ∧
  (∀ isReference block, viewMacroRoute isReference block =
    if !isReference then .invalid else if block then .withBindings else .direct)

theorem viewBoundaryBehavior : ViewBoundaryBehavior := by
  constructor
  · intros first last token; cases token <;> rfl
  · intros; rfl
def ViewsMacroBehavior : Prop :=
  (∀ array scalar, maybeViewRoute array scalar = if array && !scalar then .view else .getindex) ∧
  (∀ id, rewriteViews (.atom id) = .atom id) ∧
  (∀ array indices, rewriteViews (.ref array indices) =
    .call .maybeview (rewriteViews array :: indices.map rewriteViews)) ∧
  (∀ fn args, rewriteViews (.call fn args) = .call fn (args.map rewriteViews)) ∧
  (∀ array indices rhs, rewriteViews (.assign (.ref array indices) rhs) =
    .assign (.ref (rewriteViews array) (indices.map rewriteViews)) (rewriteViews rhs)) ∧
  (∀ items, rewriteViews (.block items) = .block (items.map rewriteViews))

theorem viewsMacroBehavior : ViewsMacroBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; simp only [rewriteViews]
  · intros; simp only [rewriteViews]
  · intros; simp only [rewriteViews]
  · intros; simp only [rewriteViews]
  · intros; simp only [rewriteViews]

end JuliaLean.NumMisc.Coverage

namespace JuliaLean.NumMisc

def ViewsDocumentedRewrite : Prop :=
  (∀ a is, rewriteViews (.ref a is) =
      .call .maybeview (rewriteViews a :: is.map rewriteViews)) ∧
  (∀ args, ∃ args', rewriteViews (.call .getindex args) = .call .getindex args') ∧
  (∀ a is rhs, rewriteViews (.assign (.ref a is) rhs) =
      .assign (.ref (rewriteViews a) (is.map rewriteViews)) (rewriteViews rhs)) ∧
  (∀ id, rewriteViews (.atom id) = .atom id)
theorem viewsDocumentedRewrite_proven : ViewsDocumentedRewrite := by
  constructor
  · intro a is
    simp only [rewriteViews]
  constructor
  · intro args
    exact ⟨args.map rewriteViews, by simp only [rewriteViews]⟩
  constructor
  · intro a is rhs
    simp only [rewriteViews]
  · intro id
    simp only [rewriteViews]

end JuliaLean.NumMisc

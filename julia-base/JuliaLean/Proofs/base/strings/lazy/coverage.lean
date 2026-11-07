import JuliaLean.base.strings.lazy
import JuliaLean.Core

/-!
Models for `base/strings/lazy.jl` at Julia `bbfa0ce4150`.  Printed parts are
represented by their resulting byte strings; this keeps the model focused on
the lazy cache and the `AbstractString` forwarding methods.
-/

namespace JuliaLean.StringsCovA.Lazy

def ConstructionContract : Prop :=
  (∀ parts str, privateCtor parts str = ⟨parts, false, str⟩) ∧
  (∀ parts compact, ctor parts compact = ⟨parts, compact, none⟩) ∧
  (∀ parts compact, lazyMacro parts compact = ctor parts compact)

theorem constructionContract : ConstructionContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def MaterializationContract : Prop :=
  (∀ parts compact, materialize (ctor parts compact) = render parts) ∧
  (∀ parts compact cached, materialize ⟨parts, compact, some cached⟩ = cached)

theorem materializationContract : MaterializationContract := by
  constructor <;> intros <;> rfl

def ForwardingContract : Prop :=
  (∀ H s h, hash H s h = H (materialize s) h) ∧
  (∀ stringLastindex s, lastindex stringLastindex s = stringLastindex (materialize s)) ∧
  (∀ (α : Type) (stringIterate : List UInt8 → Option α) s,
    iterate0 stringIterate s = stringIterate (materialize s)) ∧
  (∀ (α : Type) (stringIterate : List UInt8 → Int → Option α) s i,
    iterateAt stringIterate s i = stringIterate (materialize s) i) ∧
  (∀ a b, isequal a b = (materialize a == materialize b)) ∧
  (∀ a b, eq a b = (materialize a == materialize b)) ∧
  (∀ s, ncodeunits s = (materialize s).length) ∧
  (∀ s, codeunitType s = 8) ∧
  (∀ s i, codeunitAt s i =
    if 1 ≤ i ∧ i ≤ (materialize s).length then
      .ok ((materialize s).getD (i.toNat - 1) 0)
    else .error .boundsError) ∧
  (∀ s, codeunits s = materialize s) ∧
  (∀ stringIsvalid s i, isvalid stringIsvalid s i = stringIsvalid (materialize s) i)

theorem forwardingContract : ForwardingContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.Lazy

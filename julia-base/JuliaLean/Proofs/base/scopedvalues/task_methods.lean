import JuliaLean.base.scopedvalues
import JuliaLean.Proofs.base.asyncmap.task_properties
import JuliaLean.Proofs.base.linked_list.wellformed
import JuliaLean.Proofs.base.scopedvalues.task_properties
import JuliaLean.Proofs.base.atomics.task_properties

namespace JuliaLean.Tasks



def ScopedAccessBodies : Prop := ∀ (scope : Scope) (cell : ScopedCell) (key : Nat),
  scopedAssigned scope cell key = (cell.hasDefault || (scope key).isSome) ∧
  (cell.hasDefault → scopedDefault cell = some cell.defaultValue)

theorem scopedAccessBodies_proven : ScopedAccessBodies := by
  intro scope cell key
  constructor
  · rfl
  · intro hasDefault
    simp [scopedDefault, hasDefault]

def ScopedDynamicBodies : Prop := ∀ (parent : Scope) (bindings : Bindings)
    (body : Scope → Except Nat Nat) (result : Nat),
  (withScope parent bindings body).2 = parent ∧
  (scopedThunkCall ⟨enterScope parent bindings, result⟩).2 = enterScope parent bindings

theorem scopedDynamicBodies_proven : ScopedDynamicBodies := by
  unfold ScopedDynamicBodies
  intros
  exact ⟨rfl, rfl⟩

end JuliaLean.Tasks

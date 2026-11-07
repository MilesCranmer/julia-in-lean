import JuliaLean.base.scopedvalues
import JuliaLean.Proofs.base.task.interleavings

namespace JuliaLean.Tasks





def ScopedValuesRestore : Prop :=
  ∀ (parent : Scope) (bindings : Bindings) (body : Scope → Except Nat Nat),
    (withScope parent bindings body).2 = parent

theorem scopedValuesRestore_proven : ScopedValuesRestore := by
  intro parent bindings body
  rfl

/-- Children see the scope active when `Task` was created, even if they run
after the parent's `with` expression has restored its outer scope
(`base/scopedvalues.jl:47-55`; `base/task.jl:5-8`). -/
def ScopedValuesChildInheritance : Prop :=
  ∀ (parent : Scope) (bindings : Bindings) (key : Nat),
    createTaskScope (enterScope parent bindings) key = enterScope parent bindings key

theorem scopedValuesChildInheritance_proven : ScopedValuesChildInheritance := by
  intro parent bindings key
  rfl

end JuliaLean.Tasks

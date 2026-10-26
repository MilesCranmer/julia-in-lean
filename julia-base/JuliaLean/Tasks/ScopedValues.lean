import JuliaLean.Tasks.TaskModel

namespace JuliaLean.Tasks

abbrev Scope := Nat → Option Int
abbrev Bindings := List (Nat × Int)

/-- One `Scope(parent, bindings...)`, `base/scopedvalues.jl:231-243`.
The first binding for a key wins, matching the constructed scope storage. -/
def enterScope (parent : Scope) (bindings : Bindings) : Scope := fun key =>
  match bindings.find? (fun binding => binding.1 == key) with
  | some binding => some binding.2
  | none => parent key

/-- `@with` installs the child scope only while evaluating the body. The
runtime's `tryfinally` scope operand restores `parent` for both outcomes. -/
def withScope (parent : Scope) (bindings : Bindings)
    (body : Scope → Except Nat Nat) :
    Except Nat Nat × Scope :=
  (body (enterScope parent bindings), parent)

/-- A new task captures `Core.current_scope()` at construction. -/
def createTaskScope (current : Scope) : Scope := current

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

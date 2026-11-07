import JuliaLean.base.atomics
import JuliaLean.Proofs.base.asyncmap.task_properties
import JuliaLean.Proofs.base.linked_list.wellformed
import JuliaLean.Proofs.base.scopedvalues.task_properties
import JuliaLean.Proofs.base.atomics.task_properties

namespace JuliaLean.Tasks



def AtomicStorageBodies : Prop := ∀ (cell : CoverageAtomic) (value expected desired : AtomicInt),
  atomicDefault.value = 0 ∧
  atomicLoad cell = cell.value ∧
  (atomicSwap cell value).1 = cell.value ∧
  (atomicReplace cell expected desired).1 = cell.value ∧
  (atomicStep (.exchange value) cell.value).1 = cell.value

theorem atomicStorageBodies_proven : AtomicStorageBodies := by
  unfold AtomicStorageBodies
  intros
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  simp [atomicReplace]
  split <;> rfl

def AtomicFenceBodies : Prop := ∀ kind : FenceKind, !(fenceBody kind).isEmpty

theorem atomicFenceBodies_proven : AtomicFenceBodies := by intro kind; cases kind <;> decide

end JuliaLean.Tasks

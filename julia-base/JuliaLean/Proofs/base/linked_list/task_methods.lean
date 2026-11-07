import JuliaLean.base.linked_list
import JuliaLean.Proofs.base.asyncmap.task_properties
import JuliaLean.Proofs.base.linked_list.wellformed
import JuliaLean.Proofs.base.scopedvalues.task_properties
import JuliaLean.Proofs.base.atomics.task_properties

namespace JuliaLean.Tasks



def LinkedGenericBodies : Prop := ∀ (nodes : List Nat) (node : Nat),
  (node ∉ nodes → linkedPushFirst nodes node = .ok (node :: nodes)) ∧
  (linkedPopFirst (node :: nodes) = .ok (node, nodes)) ∧
  (linkedListStep (.delete node) nodes = nodes.erase node) ∧
  (linkedAppend nodes [] = .ok (nodes, []))

theorem linkedGenericBodies_proven : LinkedGenericBodies := by
  intro nodes node
  constructor
  · intro fresh; simp [linkedPushFirst, fresh]
  exact ⟨rfl, rfl, by simp [linkedAppend]⟩

def LinkedBoxedBodies : Prop := ∀ (nodes : List BoxedNode) (freshId value : Nat),
  boxedValues (boxedPush nodes freshId value) = boxedValues nodes ++ [value] ∧
  (boxedDeleteValue nodes value).length ≤ nodes.length

theorem linkedBoxedBodies_proven : LinkedBoxedBodies := by
  intro nodes freshId value
  constructor
  · simp [boxedPush, boxedValues]
  · simp only [boxedDeleteValue]
    split <;> simp [List.length_erase_le]

def LinkedWaitEntryBodies : Prop := ∀ (queue : List MultiListEntry) (owner : Nat)
    (entry : MultiListEntry) (armed : List (Nat × Bool)),
  (owner ∉ entry.owners →
    match multiListPush queue owner entry with
    | .ok result => result.length = queue.length + 1
    | .error _ => False) ∧
  waitQueueHasArmed armed = armed.any (·.2) ∧
  (multiListDelete queue owner entry.id).length ≤ queue.length

theorem linkedWaitEntryBodies_proven : LinkedWaitEntryBodies := by
  intro queue owner entry armed
  constructor
  · intro fresh
    simp [multiListPush, fresh]
  constructor
  · rfl
  · unfold multiListDelete
    exact List.length_filterMap_le _ _

end JuliaLean.Tasks

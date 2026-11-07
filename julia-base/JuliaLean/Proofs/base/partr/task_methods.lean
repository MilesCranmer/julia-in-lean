import JuliaLean.base.partr
import JuliaLean.Proofs.base.task.interleavings
import JuliaLean.Proofs.base.condition.task_properties

namespace JuliaLean.Tasks



def PartrRngBodies : Prop := ∀ (maximum seed draw : Nat),
  partrCong 0 draw = 0 ∧
  (0 < maximum → 1 ≤ partrCong maximum draw ∧ partrCong maximum draw ≤ maximum) ∧
  (partrRandom 1 seed = (0, seed))

theorem partrRngBodies_proven : PartrRngBodies := by
  intro maximum seed draw
  constructor
  · rfl
  constructor
  · intro positive
    simp [partrCong, Nat.ne_of_gt positive]
    exact Nat.mod_lt draw positive
  · rfl

def PartrHeapBodies : Prop := ∀ (heap : CoverageTaskHeap) (task priority index child parent : Nat),
  (heapInsert heap task priority).tasks.length = heap.tasks.length + 1 ∧
  (heapInsert heap task priority).advertised = min heap.advertised priority ∧
  siftUpDecision index child parent =
    (if 1 < index && child < parent then (true, (index - 2) / 8 + 1) else (false, index))

theorem partrHeapBodies_proven : PartrHeapBodies := by
  unfold PartrHeapBodies
  intros
  exact ⟨by simp [heapInsert], rfl, rfl⟩

end JuliaLean.Tasks

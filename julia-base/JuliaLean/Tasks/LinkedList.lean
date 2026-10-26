import JuliaLean.Tasks.TaskModel

namespace JuliaLean.Tasks

inductive ListAction where
  | push (node : Nat)
  | pop
  | delete (node : Nat)
  deriving Repr, DecidableEq

def removeLast : List Nat → List Nat
  | [] => []
  | [_] => []
  | node :: next :: nodes => node :: removeLast (next :: nodes)

private theorem mem_removeLast {node : Nat} : ∀ nodes,
    node ∈ removeLast nodes → node ∈ nodes
  | [], found => by simp [removeLast] at found
  | [_], found => by simp [removeLast] at found
  | first :: next :: nodes, found => by
      simp only [removeLast, List.mem_cons] at found ⊢
      rcases found with same | rest
      · exact Or.inl same
      · exact Or.inr (by simpa using mem_removeLast (next :: nodes) rest)

private theorem removeLast_nodup : ∀ nodes : List Nat,
    nodes.Nodup → (removeLast nodes).Nodup
  | [], _ => by simp [removeLast]
  | [_], _ => by simp [removeLast]
  | first :: next :: nodes, wellFormed => by
      have parts := List.nodup_cons.mp wellFormed
      rw [removeLast, List.nodup_cons]
      exact ⟨fun found => parts.1 (mem_removeLast (next :: nodes) found),
        removeLast_nodup (next :: nodes) parts.2⟩

/-- Abstract identity order of `IntrusiveLinkedList`. The source mutations
at `base/linked_list.jl:64-142` implement these three list transformations;
the source `queue` field enforces the no-duplicate precondition on push. -/
def linkedListStep (action : ListAction) (nodes : List Nat) : List Nat :=
  match action with
  | .push node => if node ∈ nodes then nodes else nodes ++ [node]
  | .pop => removeLast nodes
  | .delete node => nodes.erase node

def linkedListRun : List ListAction → List Nat → List Nat
  | [], nodes => nodes
  | action :: actions, nodes => linkedListRun actions (linkedListStep action nodes)

private theorem linkedListStep_nodup (action : ListAction) (nodes : List Nat)
    (wellFormed : nodes.Nodup) : (linkedListStep action nodes).Nodup := by
  cases action with
  | push node =>
      simp only [linkedListStep]
      split
      · exact wellFormed
      · simp only [List.nodup_append, wellFormed, true_and, List.nodup_cons,
          List.not_mem_nil, List.mem_singleton]
        constructor
        · simp
        · intro a inNodes b equal
          subst b
          intro same
          subst a
          contradiction
  | pop =>
      exact removeLast_nodup nodes wellFormed
  | delete node =>
      simpa [linkedListStep] using wellFormed.erase node

/-- Push, tail-pop, and identity-delete preserve unique membership, so the
derived head, tail, next chain, and queue ownership remain well formed. -/
def LinkedListWellFormed : Prop :=
  ∀ (nodes : List Nat) (actions : List ListAction), nodes.Nodup →
    (linkedListRun actions nodes).Nodup

theorem linkedListWellFormed_proven : LinkedListWellFormed := by
  intro nodes actions wellFormed
  induction actions generalizing nodes with
  | nil => exact wellFormed
  | cons action actions ih =>
      exact ih (linkedListStep action nodes) (linkedListStep_nodup action nodes wellFormed)

end JuliaLean.Tasks

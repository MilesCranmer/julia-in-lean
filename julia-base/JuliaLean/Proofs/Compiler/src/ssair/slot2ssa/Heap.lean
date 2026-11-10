import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Spec

/-!
The binary heap of `Compiler/src/ssair/heap.jl` under the ordering `By(x -> -x[2])` that
`iterated_dominance_frontier` uses (the element with the highest level is the lowest ordered):
the docstrings of `heapify!`, `heappop!` and `heappush!` checked on every vector of up to five
elements with levels 1 to 3.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

/-- The heap property for the ordering: no element is lower ordered than its parent, that is
`!lt(o, xs[i], xs[div(i, 2)])` for `i ≥ 2`, which for `By(x -> -x[2])` is
`xs[div(i, 2)][2] ≥ xs[i][2]`. -/
def isHeap (xs : Array (Int × Int)) : Bool :=
  (List.range xs.size).all fun (i : Nat) => i == 0 ||
    (xs.getD ((i + 1) / 2 - 1) (0, 0)).2 ≥ (xs.getD i (0, 0)).2

def pairLt (a b : Int × Int) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- Insertion sort of pairs, to compare vectors as multisets. -/
def isortPair : List (Int × Int) → List (Int × Int)
  | [] => []
  | x :: xs => let r := isortPair xs; r.filter (pairLt · x) ++ [x] ++ r.filter (!pairLt · x)

def samePerm (a b : List (Int × Int)) : Bool := isortPair a == isortPair b

/-- Every vector of `k` elements `(i, level)` with distinct tags `i = 1..k` and levels 1 to 3. -/
def heapInputs : Nat → List (List Int)
  | 0 => [[]]
  | k + 1 => [1, 2, 3].flatMap fun l => (heapInputs k).map (l :: ·)

def tagged (ls : List Int) : Array (Int × Int) :=
  ((List.range ls.length).map fun (i : Nat) => ((i : Int) + 1, ls.getD i 0)).toArray

/-- For one vector `xs`: `heapify!` returns a heap that is a permutation of `xs`; on that heap,
`heappop!` returns an element of the highest level and leaves a heap of the other elements; and
`heappush!` of an element of any level 1 to 3 gives a heap of all the elements. -/
def heapOK (ls : List Int) : Bool :=
  let xs := tagged ls
  jmIs (heapify xs) fun h =>
    isHeap h && samePerm h.toList xs.toList &&
    (h.isEmpty || jmIs (heappop h) fun (x, h') =>
      isHeap h' && samePerm (h'.toList ++ [x]) h.toList && h.all (fun y => y.2 ≤ x.2)) &&
    [1, 2, 3].all fun l => jmIs (heappush h (9, l)) fun h2 =>
      isHeap h2 && samePerm h2.toList (h.toList ++ [(9, l)])

/-- `heapify!`, `heappop!` and `heappush!` (with `percolate_down!` and `percolate_up!`) under
`By(x -> -x[2])` satisfy their docstrings on every vector of 0 to 5 elements with levels 1 to
3: Compiler/src/ssair/heap.jl:33-71 ("Turn an arbitrary vector into a binary min-heap",
"remove and return the lowest ordered element", "push a new element `x`, preserving the heap
property"). -/
def HeapSmall : Prop := ∀ k ≤ 5, ∀ ls ∈ heapInputs k, heapOK ls = true

theorem heap_upto5 : ((List.range 6).all fun k => (heapInputs k).all heapOK) = true := by
  decide +kernel

theorem heapSmall_proven : HeapSmall := by
  intro k hk ls hls
  have h := List.all_eq_true.mp heap_upto5 k (List.mem_range.mpr (by omega))
  exact List.all_eq_true.mp h ls hls

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

import JuliaLean.Proofs.Compiler.src.ssair.domtree.Props

/-! General properties of the small functions of `Compiler/src/ssair/domtree.jl`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

theorem resize_size {α : Type} (a : Array α) (n : Nat) (u : α) :
    (JuliaLean.Compiler.ssair.resize a n u).size = n := by
  unfold JuliaLean.Compiler.ssair.resize
  split <;> simp <;> omega

theorem resize_getElem? {α : Type} (a : Array α) (n : Nat) (u : α) (i : Nat) (hi : i < n)
    (ha : i < a.size) : (JuliaLean.Compiler.ssair.resize a n u)[i]? = a[i]? := by
  unfold JuliaLean.Compiler.ssair.resize
  split
  · simp [Array.getElem?_extract]; omega
  · simp [Array.getElem?_append_left ha]

/-- `DFSTree(n)` (Compiler/src/ssair/domtree.jl:89-96): five vectors of length `n`; `to_pre`,
`to_post` and `to_parent_pre` are zero, the undefined `from_pre` and `from_post` are 0 in the
model, and `_worklist` is empty (which `DFS!` relies on: "always starts empty", line 126). -/
def DFSTreeCtorSpec : Prop :=
  ∀ n : Nat, (DFSTree.new n).toPre = .replicate n 0 ∧ (DFSTree.new n).toPost = .replicate n 0 ∧
    (DFSTree.new n).toParentPre = .replicate n 0 ∧ (DFSTree.new n).fromPre.size = n ∧
    (DFSTree.new n).fromPost.size = n ∧ (DFSTree.new n).worklist = #[]

theorem dfsTreeCtorSpec_proven : DFSTreeCtorSpec := by
  intro n; simp [DFSTree.new]

/-- `copy(D)` (Compiler/src/ssair/domtree.jl:98-103) gives back every field of `D` in its own
place, `_worklist` included; `copy!(dst, src)` (lines 105-112) gives the five vectors of `src`
and keeps `dst._worklist`, whatever `dst` held. The model of `copy` is the positional
constructor in the order of the Julia call, so a call that passed two vectors in the wrong
order would break the first part. -/
def DFSTreeCopySpec : Prop :=
  (∀ D : DFSTree, D.copy = D) ∧
  ∀ dst src : DFSTree, dst.copyInto src = { src with worklist := dst.worklist }

theorem dfsTreeCopySpec_proven : DFSTreeCopySpec :=
  ⟨fun D => by cases D; rfl, fun _ _ => rfl⟩

/-- `resize!(D, n)` (Compiler/src/ssair/domtree.jl:113-119) makes all five vectors length `n`,
keeps their first entries and `_worklist`, and returns the value of its last call, the resized
`to_parent_pre` vector; `length(D)` (line 121) is the length of `from_pre`. -/
def DFSTreeResizeSpec : Prop :=
  (∀ D : DFSTree, D.length = D.fromPre.size) ∧
  ∀ (D : DFSTree) (n : Nat),
    let E := (D.resize n).1
    (D.resize n).2 = E.toParentPre ∧ E.worklist = D.worklist ∧
    E.toPre.size = n ∧ E.fromPre.size = n ∧ E.toPost.size = n ∧ E.fromPost.size = n ∧
    E.toParentPre.size = n ∧
    (∀ i, i < n → i < D.toPre.size → E.toPre[i]? = D.toPre[i]?) ∧
    (∀ i, i < n → i < D.fromPre.size → E.fromPre[i]? = D.fromPre[i]?) ∧
    (∀ i, i < n → i < D.toPost.size → E.toPost[i]? = D.toPost[i]?) ∧
    (∀ i, i < n → i < D.fromPost.size → E.fromPost[i]? = D.fromPost[i]?) ∧
    (∀ i, i < n → i < D.toParentPre.size → E.toParentPre[i]? = D.toParentPre[i]?)

theorem dfsTreeResizeSpec_proven : DFSTreeResizeSpec := by
  refine ⟨fun _ => rfl, fun D n => ?_⟩
  simp only [DFSTree.resize, resize_size, true_and]
  exact ⟨fun i hi ha => resize_getElem? _ _ _ i hi ha, fun i hi ha => resize_getElem? _ _ _ i hi ha,
    fun i hi ha => resize_getElem? _ _ _ i hi ha, fun i hi ha => resize_getElem? _ _ _ i hi ha,
    fun i hi ha => resize_getElem? _ _ _ i hi ha⟩

/-- `DomTreeNode()` is level 1 with no children, and `DomTree()`/`PostDomTree()`
(Compiler/src/ssair/domtree.jl:220, 237-239) are empty. -/
def DomTreeCtorSpec : Prop :=
  DomTreeNode.new = ⟨1, #[]⟩ ∧
  ∀ isPost : Bool, GenericDomTree.new isPost = ⟨isPost, DFSTree.new 0, #[], #[], #[]⟩ ∧
    (DFSTree.new 0).length = 0

theorem domTreeCtorSpec_proven : DomTreeCtorSpec :=
  ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- `DomTreeCache()` (Compiler/src/ssair/domtree.jl:257) has three empty buffers. -/
def DomTreeCacheSpec : Prop :=
  DomTreeCache.new = ⟨#[], #[], #[]⟩ ∧ DomTreeCache.new.ancestors.size = 0 ∧
    DomTreeCache.new.idomsPre.size = 0 ∧ DomTreeCache.new.worklist.size = 0

theorem domTreeCacheSpec_proven : DomTreeCacheSpec := ⟨rfl, rfl, rfl, rfl⟩

/-- `dom_edges` (Compiler/src/ssair/domtree.jl:331-334) is the predecessors of block `idx` in a
`DomTree` and its successors in a `PostDomTree`, and a `BoundsError` outside the blocks. -/
def DomEdgesSpec : Prop :=
  ∀ (isPost : Bool) (blocks : Blocks) (idx : Int),
    domEdges isPost blocks idx =
      if h : 1 ≤ idx ∧ (idx - 1).toNat < blocks.size then
        .ok (if isPost then blocks[(idx - 1).toNat].succs else blocks[(idx - 1).toNat].preds)
      else .error "julia:BoundsError"

theorem domEdgesSpec_proven : DomEdgesSpec := by
  intro isPost blocks idx
  unfold domEdges aget
  split <;> rfl

end JuliaLean.Proofs.Compiler.src.ssair.domtree

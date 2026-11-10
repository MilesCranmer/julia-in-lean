import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Ssa
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Heap
import JuliaLean.Proofs.Compiler.src.ssair.domtree.Props

/-!
The general (unbounded) forms of the bounded properties of `Compiler/src/ssair/slot2ssa.jl` and
`Compiler/src/ssair/heap.jl`, which stay open, and the small general property of
`renumber_ssa`.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

/-- `IdfSmall` for every CFG of `compute_basic_blocks` form. -/
def IdfAll : Prop := ∀ succs zp, ValidCFG succs zp → idfOK (mkBlocks succs zp) = true

/-- `PrunedPhisSmall` for every CFG of `compute_basic_blocks` form. -/
def PrunedPhisAll : Prop := ∀ succs zp, ValidCFG succs zp → prunedOK (mkBlocks succs zp) = true

/-! ## `renumber_ssa` -/

/-- `renumber_ssa(SSAValue(id), ssanums)` (Compiler/src/ssair/slot2ssa.jl:48-56) gives back
`SSAValue(id)` for an id past the end of `ssanums`, `ssanums[id]` for an id inside it whose
entry is positive, an `AssertionError` (`@assert val.id > 0`) for a non-positive entry, and a
`BoundsError` for an id below 1. -/
def RenumberSsaSpec : Prop := ∀ (id : Int) (ssanums : Array Int),
  renumberSsa id ssanums =
    if id > ssanums.size then .ok (.ssa id)
    else if 1 ≤ id then
      (if ssanums[(id - 1).toNat]! > 0 then .ok (.ssa ssanums[(id - 1).toNat]!)
       else .error "julia:AssertionError")
    else .error "julia:BoundsError"

theorem renumberSsaSpec_proven : RenumberSsaSpec := by
  intro id ssanums
  by_cases h1 : id > (ssanums.size : Int)
  · simp only [renumberSsa, h1, ite_true]
    rfl
  · by_cases h2 : 1 ≤ id
    · have hlt : (id - 1).toNat < ssanums.size := by omega
      have hg : ssanums[(id - 1).toNat]! = ssanums[(id - 1).toNat] := getElem!_pos ssanums _ hlt
      have ha : aget ssanums id = .ok ssanums[(id - 1).toNat] := by
        simp only [aget, h2, hlt, and_self, dite_true]
        rfl
      simp only [renumberSsa, h1, ite_false, h2, ite_true, hg, ha]
      by_cases h3 : ssanums[(id - 1).toNat] > 0
      · show Except.bind (Except.ok _) _ = _
        simp only [Except.bind, h3, ite_true]
        rfl
      · show Except.bind (Except.ok _) _ = _
        simp only [Except.bind, h3, ite_false]
        rfl
    · have ha : aget ssanums id = .error "julia:BoundsError" := by
        simp only [aget, h2, false_and, dite_false]
        rfl
      simp only [renumberSsa, h1, ite_false, h2, ha]
      rfl

/-- `SsaSmall` for every number of blocks. -/
def SsaAll : Prop := ∀ n, 1 ≤ n → ∀ succs ∈ juliaCFGs n, ssaOK succs = true

/-- `HeapSmall` for every vector of levels. -/
def HeapAll : Prop := ∀ ls, heapOK ls = true

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

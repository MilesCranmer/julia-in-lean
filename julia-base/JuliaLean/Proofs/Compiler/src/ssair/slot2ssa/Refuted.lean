import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Props

/-! Refutations of properties of `Compiler/src/ssair/slot2ssa.jl`, by kernel evaluation of the
model on the inputs of `Inputs.lean`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair

theorem h3Inputs_ok : phiInputsOK h3Inputs h3IR = true := by decide +kernel

/-- On `h3` the phi nodes for `c` and `x` in the catch block (new nodes 2 and 4) are not used:
on the first visit of the block the renaming sets the slot's value to the new phi and then
overwrites it with the block's `PhiC` node, so the loop body reads the `PhiC`. -/
theorem h3_phis_unused : okThen (slot2regSsa h3Inputs h3IR) phisUsed = false := by decide +kernel

theorem phisUsed_refuted : ¬ PhisUsed := fun h => by
  have := h h3Inputs h3IR h3Inputs_ok
  rw [h3_phis_unused] at this
  exact Bool.false_ne_true this

/-- On `g2` (a `@goto` into a `for` loop), `construct_ssa!` throws the `AssertionError` of
`renumber_ssa` (`val.id > 0`), as on the pinned Julia: `domsort_ssa!` does not schedule the
unreachable block 2 that defines `%5`, which block 6 still uses. Not a registry entry: the input
breaks lowering's invariant that SSA values dominate their uses (JuliaLang/julia#61132). -/
theorem g2_asserts :
    (match slot2regSsa g2Inputs g2IR with
     | .error e => e == "julia:AssertionError"
     | .ok _ => false) = true := by decide +kernel

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

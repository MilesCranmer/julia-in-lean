import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Ssa

/-! Splitting a list check into chunks of two, for the kernel checks of `ssaOK`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

/-- A check holds on `l.drop i` once it holds on the next two elements and on `l.drop (i + 2)`. -/
theorem all_drop_of_chunk {α : Type} (P : α → Bool) (l : List α) (i : Nat)
    (h1 : ((l.drop i).take 2).all P = true) (h2 : (l.drop (i + 2)).all P = true) :
    (l.drop i).all P = true := by
  rw [← List.take_append_drop 2 (l.drop i), List.all_append, h1, List.drop_drop]
  rw [Bool.true_and]
  exact h2

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

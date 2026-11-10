import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Props

/-! The finer slices of the 3-block CFGs of `smallCFGs` for the kernel checks of
`PrunedPhisSmall`: the CFGs whose blocks 1 and 2 have the successors `c` and `d`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

def slice3b (c d : List Int) : List (List (List Int) × List Int) :=
  (subsetsOf (irange 1 3)).map fun e => ([c, d, e], [1])

theorem slice3_eq (c : List Int) : slice3 c = (subsetsOf (irange 1 3)).flatMap (slice3b c) := rfl

/-- A check holds on `slice3 c` once it holds on each of its eight finer slices. -/
theorem slice3_of_sub (P : List (List Int) × List Int → Bool) (c : List Int)
    (h0 : (slice3b c []).all P = true) (h1 : (slice3b c [3]).all P = true)
    (h2 : (slice3b c [2]).all P = true) (h3 : (slice3b c [2, 3]).all P = true)
    (h4 : (slice3b c [1]).all P = true) (h5 : (slice3b c [1, 3]).all P = true)
    (h6 : (slice3b c [1, 2]).all P = true) (h7 : (slice3b c [1, 2, 3]).all P = true) :
    (slice3 c).all P = true := by
  have hs : subsetsOf (irange 1 3) = [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]] := by
    decide
  rw [slice3_eq, hs]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.all_append, h0, h1, h2,
    h3, h4, h5, h6, h7, Bool.and_self]

/-- A check holds on `l.drop i` once it holds on the next `c` elements and on `l.drop (i + c)`. -/
theorem all_drop_of_take {α : Type} (P : α → Bool) (l : List α) (i c : Nat)
    (h1 : ((l.drop i).take c).all P = true) (h2 : (l.drop (i + c)).all P = true) :
    (l.drop i).all P = true := by
  rw [← List.take_append_drop c (l.drop i), List.all_append, h1, List.drop_drop, Bool.true_and]
  exact h2

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

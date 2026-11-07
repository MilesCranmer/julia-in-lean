import JuliaLean.Proofs.base.multidimensional.cartesian_contracts

namespace JuliaLean.Multidim

/-- `circcopy!(dest, zeros(Int, 2, 0))` with `axes(dest) == (2:3, 1:0)` throws
`DivideError` (`mod(0, 0)` for the empty second dimension). -/
theorem circcopy_empty :
    errKind (circcopy [(2, 3), (1, 0)] (fun _ => (none : Option Int)) [(1, 2), (1, 0)]
      (fun _ => (0 : Int))) = some .divideError := by
  decide

theorem circcopyCorrect_refuted : ¬ CirccopyCorrect := by
  intro h
  obtain ⟨out, hout⟩ := h [(2, 3), (1, 0)] [(1, 2), (1, 0)] (fun _ => none) (fun _ => 0)
    (by decide) (by decide) (by decide)
  have := circcopy_empty
  rw [hout] at this
  simp [errKind] at this

/-- `copyto!(dest, CartesianIndices((1:0,)), src, CartesianIndices((1:3,)))` returns `dest`. -/
theorem copyto_empty_dest :
    errKind (copytoCI [(1, 2)] (fun _ => (none : Option Int)) [⟨i64 1, i64 1, 0⟩] [(1, 3)]
      (fun _ => (0 : Int)) [⟨i64 1, i64 1, 3⟩]) = none := by
  decide

theorem copytoSizeChecked_refuted : ¬ CopytoSizeChecked := by
  intro h
  have := h [(1, 2)] [(1, 3)] (fun _ => none) (fun _ => 0) [⟨i64 1, i64 1, 0⟩] [⟨i64 1, i64 1, 3⟩]
    (by decide) (by decide)
  rw [copyto_empty_dest] at this
  exact absurd this (by decide)

/-- `CartesianIndices((1:0, 1:2)) == CartesianIndices((1:0, 3:4))` is `false` although both
are empty 0×2 arrays. -/
theorem cartesianEq_empty :
    ciEq [unitRng 1 0, unitRng 1 2] [unitRng 1 0, unitRng 3 4] = false ∧
      ([unitRng 1 0, unitRng 1 2].map (·.len) == [unitRng 1 0, unitRng 3 4].map (·.len) &&
        elems [unitRng 1 0, unitRng 1 2] == elems [unitRng 1 0, unitRng 3 4]) = true := by
  decide

theorem cartesianEqArrays_refuted : ¬ CartesianEqArrays := by
  intro h
  have := h [unitRng 1 0, unitRng 1 2] [unitRng 1 0, unitRng 3 4] (by decide) (by decide) (by decide)
  rw [cartesianEq_empty.1, cartesianEq_empty.2] at this
  exact absurd this (by decide)

end JuliaLean.Multidim

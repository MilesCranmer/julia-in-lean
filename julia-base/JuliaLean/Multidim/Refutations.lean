import JuliaLean.Multidim.Props

/-! Counterexamples for the refuted multidimensional-array properties, evaluated by
`decide`. Each matches `repro/multidim-*.jl`. -/

namespace JuliaLean.Multidim

/-- `findfirst(zeros(Bool, 0, 3))` reads `A[1, 1]` and throws `BoundsError`:
`CartesianIndex(1, 1) > CartesianIndex(0, 3)` is false. -/
theorem findfirst_empty_0x3 : findfirst [0, 3] (fun _ => false) = .error .boundsError := by
  decide

theorem findfirstCartesian_refuted : ¬ FindfirstCartesian := by
  intro h
  have := h [0, 3] (fun _ => false) (by decide)
  rw [findfirst_empty_0x3] at this
  exact absurd this (by decide)

/-- `selectdim([1 2; 3 4], 1, CartesianIndex(2, 2))` is the view
`view(B, CartesianIndex(2, 2), Slice(OneTo(2)))`, whose second element is `B[2, 2, 2]`. -/
theorem selectdim_cart_idxs :
    selectdim [2, 2] 1 (.cart [2, 2]) = .ok [.cart [2, 2], .slice 2] := by
  decide

theorem selectdimInBounds_refuted : ¬ SelectdimInBounds := by
  intro h
  have := h [2, 2] 1 (.cart [2, 2]) (by decide) (by intro n; simp)
  rw [selectdim_cart_idxs] at this
  exact absurd this (by decide)

/-- `selectdim([1 2 3; 4 5 6], 3, 1:1)` throws `BoundsError`; `view(A, :, :, 1:1)` is 2×3×1. -/
theorem selectdim_trailing_range :
    (selectdim [2, 3] ((3 : Nat) : Int) (.urange 1 1) >>= view [2, 3]) = .error .boundsError ∧
      view [2, 3] [.colon, .colon, .urange 1 1] = .ok [2, 3, 1] := by
  decide

theorem selectdimViewAgrees_refuted : ¬ SelectdimViewAgrees := by
  intro h
  have := h [2, 3] 3 (.urange 1 1) (by decide) (by decide) (by intro n; simp)
  rw [selectdim_trailing_range.1] at this
  exact absurd this (by decide)

/-- `vcat(1, [2 3])`: the shape is `(2, 2)` and the scalar is broadcast into the first row. -/
theorem cat_scalar_row : cat [1] [.scalar, .array [1, 2]] = .ok [2, 2] := by
  decide

theorem catShapeChecked_refuted : ¬ CatShapeChecked := by
  intro h
  have := h [1] [.scalar, .array [1, 2]]
  rw [cat_scalar_row] at this
  have := this .scalar (by simp) 1 (by decide) (by decide)
  exact absurd this (by decide)

/-- `hvcat((2, 1), 1, 2, 3)`: `ArgumentError` for one number type, `DimensionMismatch`
for mixed types. -/
theorem hvcat_rows_2_1 :
    hvcatSame [2, 1] 3 = .error .argumentError ∧ hvcatTyped [2, 1] 3 = .error .dimensionMismatch := by
  decide

theorem hvcatNumbersAgree_refuted : ¬ HvcatNumbersAgree := by
  intro h
  have := h [2, 1] 3
  rw [hvcat_rows_2_1.1, hvcat_rows_2_1.2] at this
  exact absurd this (by decide)

/-- `hvcat(0, 1)` throws `DivideError` from `mod(1, 0)`. -/
theorem hvcat_zero_cols : hvcatCols (i64 0) 1 = .error .divideError := by
  decide

theorem hvcatColumnsError_refuted : ¬ HvcatColumnsError := by
  intro h
  have := h (i64 0) 1 (by decide) (by decide) (by decide)
  rw [hvcat_zero_cols] at this
  exact absurd this (by decide)

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

/-- `CartesianIndices((2^32, 2^32))` has `length` 0 (`2^64` wraps) and so `isempty` is true. -/
theorem cartesian_length_wraps :
    ciIsEmpty [unitRng 1 (2 ^ 32), unitRng 1 (2 ^ 32)] = true ∧
      (ciLength [unitRng 1 (2 ^ 63 - 1), unitRng 1 2]).val = -2 := by
  decide

/-- `1:hi` is a well-formed range for `0 ≤ hi < 2^62`. -/
theorem unitRng_one_wf (hi : Int) (h0 : 0 ≤ hi) (hn : hi < 2 ^ 62) : (unitRng 1 hi).WF := by
  have h1 : (i64 1).val = 1 := by decide
  have hmin : IntTy.min .i64 = -(2 ^ 63) := by decide
  have hmax : IntTy.max .i64 = 2 ^ 63 - 1 := by decide
  refine ⟨show (i64 1).val ≠ 0 by rw [h1]; decide, ?_⟩
  intro j hj
  change j < (hi - 1 + 1).toNat at hj
  have hlen : (((hi - 1 + 1).toNat : Nat) : Int) = hi - 1 + 1 := Int.toNat_of_nonneg (by omega)
  have hj' : ((j : Nat) : Int) < (((hi - 1 + 1).toNat : Nat) : Int) := by exact_mod_cast hj
  show IntTy.min .i64 ≤ (i64 1).val + (j : Int) * (i64 1).val ∧
    (i64 1).val + (j : Int) * (i64 1).val ≤ IntTy.max .i64
  rw [h1, hmin, hmax]
  constructor <;> omega

theorem cartesianIsEmpty_refuted : ¬ CartesianIsEmpty := by
  intro h
  have hwf : ∀ r ∈ [unitRng 1 (2 ^ 32), unitRng 1 (2 ^ 32)], r.WF := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    subst hr
    exact unitRng_one_wf _ (by decide) (by decide)
  have := (h [unitRng 1 (2 ^ 32), unitRng 1 (2 ^ 32)] hwf).1 cartesian_length_wraps.1
  revert this
  decide

end JuliaLean.Multidim

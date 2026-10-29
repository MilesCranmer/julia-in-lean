import JuliaLean.AbstractArraySpecs.CatRowsProps

/-!
Refutations of the `cat` front-end and shape-helper contracts, each through its own
row's method. The front ends write an argument whose axis along a concatenated
dimension starts at `f > 1` at `offset + f` instead of `offset + 1`
(`__cat_offset1!`, base/abstractarray.jl:1932, bug `abstractarrayspecs-cat-offset-axes`);
the shape helpers skip the size check of a dimension that only one of the running shape
and the new argument has (`_cshp`, lines 1873 and 1877, bug
`multidim-cat-scalar-shape`).
-/

namespace JuliaLean.AbstractArraySpecs

/-- An offset vector with axis `3:3`. -/
def ovec : Arr Int := ⟨[⟨.unit, i64 3, i64 3⟩], .cartesian, [20]⟩
/-- A 1×1 matrix with axes `(2:2, 4:4)`. -/
def omat : Arr Int := ⟨[⟨.unit, i64 2, i64 2⟩, ⟨.unit, i64 4, i64 4⟩], .cartesian, [40]⟩
/-- 1×1×1 arrays offset along dimension 1 (axis `10:10`) and along dimension 2. -/
def oa3v : Arr Int := ⟨[⟨.unit, i64 10, i64 10⟩, ⟨.unit, i64 1, i64 1⟩, ⟨.unit, i64 1, i64 1⟩], .cartesian, [1]⟩
def oa3h : Arr Int := ⟨[⟨.unit, i64 1, i64 1⟩, ⟨.unit, i64 10, i64 10⟩, ⟨.unit, i64 1, i64 1⟩], .cartesian, [1]⟩
/-- A 1-based 1×1×1 `Array`. -/
def a3 : Arr Int := ⟨[oneTo (i64 1), oneTo (i64 1), oneTo (i64 1)], .linear, [2]⟩

theorem catPre_of {α : Type} (catdims : List Bool) (X : List (Item α)) (hne : X ≠ [])
    (hwf : ∀ a, Item.arr a ∈ X → a.WF) (s0 : List Int) (hs : refShape catdims X = some s0)
    (hb : (∀ n ∈ s0, n ≤ tmax) ∧ s0.foldl (· * ·) 1 ≤ tmax) : CatPre catdims X := by
  refine ⟨hne, hwf, fun s h => ?_⟩
  rw [hs] at h
  cases h
  exact hb

theorem conv_id {α : Type} (X : List (Item α)) : ConvOK (fun x => (.ok x : R α)) id X :=
  fun _ _ _ _ => rfl

/-- Discharges the well-formedness of a concrete argument list. -/
macro "wf_items" : tactic => `(tactic| (
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, List.map_cons, List.map_nil,
    Item.arr.injEq, reduceCtorEq, or_false, false_or, forall_eq_or_imp, forall_eq]
  decide))

macro "cat_pre" : tactic => `(tactic|
  exact catPre_of _ _ (by simp) (by wf_items) _ (by rfl) (by decide))

theorem vcatAnySpec_refuted : ¬ VcatAnySpec := by
  intro h
  have := h (0 : Int) [.val 0, .arr ovec] (by cat_pre)
  revert this; decide

theorem hcatAnySpec_refuted : ¬ HcatAnySpec := by
  intro h
  have := h (0 : Int) [.val 0, .arr omat] (by cat_pre)
  revert this; decide

theorem typedVcatAnySpec_refuted : ¬ TypedVcatAnySpec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id 0 [.arr ovec, .val 1] (by cat_pre) (conv_id _)
  revert this; decide

theorem typedHcatAnySpec_refuted : ¬ TypedHcatAnySpec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id 0 [.arr omat, .val 1] (by cat_pre) (conv_id _)
  revert this; decide

theorem vcat1Spec_refuted : ¬ Vcat1Spec := by
  intro h
  have := h (0 : Int) oa3v (by cat_pre)
  revert this; decide

theorem vcat2Spec_refuted : ¬ Vcat2Spec := by
  intro h
  have := h (0 : Int) oa3v a3 (by cat_pre)
  revert this; decide

theorem vcatArrsSpec_refuted : ¬ VcatArrsSpec := by
  intro h
  have := h (0 : Int) [oa3v, a3, a3] (by cat_pre)
  revert this; decide

theorem vcatMixedSpec_refuted : ¬ VcatMixedSpec := by
  intro h
  have := h (0 : Int) [.arr oa3v, .val 1] (by cat_pre)
  revert this; decide

theorem hcat1Spec_refuted : ¬ Hcat1Spec := by
  intro h
  have := h (0 : Int) oa3h (by cat_pre)
  revert this; decide

theorem hcat2Spec_refuted : ¬ Hcat2Spec := by
  intro h
  have := h (0 : Int) oa3h a3 (by cat_pre)
  revert this; decide

theorem hcatArrsSpec_refuted : ¬ HcatArrsSpec := by
  intro h
  have := h (0 : Int) [oa3h, a3, a3] (by cat_pre)
  revert this; decide

theorem hcatMixedSpec_refuted : ¬ HcatMixedSpec := by
  intro h
  have := h (0 : Int) [.arr oa3h, .val 1] (by cat_pre)
  revert this; decide

theorem typedVcat1Spec_refuted : ¬ TypedVcat1Spec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id 0 oa3v (by cat_pre) (conv_id _)
  revert this; decide

theorem typedVcat2Spec_refuted : ¬ TypedVcat2Spec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id 0 oa3v a3 (by cat_pre) (conv_id _)
  revert this; decide

theorem typedVcatArrsSpec_refuted : ¬ TypedVcatArrsSpec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id 0 [oa3v, a3, a3] (by cat_pre) (conv_id _)
  revert this; decide

theorem typedHcat1Spec_refuted : ¬ TypedHcat1Spec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id 0 oa3h (by cat_pre) (conv_id _)
  revert this; decide

theorem typedHcat2Spec_refuted : ¬ TypedHcat2Spec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id 0 oa3h a3 (by cat_pre) (conv_id _)
  revert this; decide

theorem typedHcatArrsSpec_refuted : ¬ TypedHcatArrsSpec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id 0 [oa3h, a3, a3] (by cat_pre) (conv_id _)
  revert this; decide

theorem catPromoteSpec_refuted : ¬ CatPromoteSpec := by
  intro h
  have := h (0 : Int) [1] [.arr ovec, .val 1] ⟨by simp, by decide⟩ (by cat_pre)
  revert this; decide

theorem catTKwSpec_refuted : ¬ CatTKwSpec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id 0 [.arr ovec] [1] ⟨by simp, by decide⟩ (by cat_pre) (conv_id _)
  revert this; decide

theorem catInnerSpec_refuted : ¬ CatInnerSpec := by
  intro h
  have := h (fun x => (.ok x : R Int)) id ⟨[i64 1], [some 0]⟩ [true] [.arr ovec] [1] (by cat_pre) (conv_id _)
    (by rfl) (by decide) (by decide)
  revert this; decide

/-- `cat_shape((true,), ((1,), (1, 2)))` returns `(2, 2)`: the first shape has no
second dimension, so its size 1 there is never compared with 2. -/
theorem catShapeSpec_refuted : ¬ CatShapeSpec := by
  intro h
  have := h [true] [[i64 1], [i64 1, i64 2]] (by simp) (by decide)
  revert this; decide

theorem catSizeShapeFromSpec_refuted : ¬ CatSizeShapeFromSpec := by
  intro h
  have := h (α := Int) [true] [i64 1] [.arr ⟨[oneTo (i64 1), oneTo (i64 2)], .linear, [1, 2]⟩] (by simp)
    (by wf_items) (by decide) (by decide)
  revert this; decide

end JuliaLean.AbstractArraySpecs

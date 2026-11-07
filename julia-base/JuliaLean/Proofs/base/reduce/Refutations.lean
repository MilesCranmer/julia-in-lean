import JuliaLean.Proofs.base.reduce.Contracts

/-! Counterexamples for the refuted reduction properties. -/

namespace JuliaLean.Reduce

open JuliaLean.Float

/-- A singleton right fold delegates to the underlying operator's `reduce_first`. -/
theorem foldrReduceFirst_proven : FoldrReduceFirst := by
  intro x ty
  simp [Vec.foldr, mapfoldrNoInit, mapfoldlNoInit]

/-- `count([true]; init = 0.0)` throws `MethodError` (`rem(::Float64, ::Type{Float64})`),
while `count((true,); init = 0.0) == 1.0`. -/
theorem countInitAgrees_refuted : ¬ CountInitAgrees := by
  intro h
  have := h (.f64 F64.zero) [true] (.inr ⟨_, rfl⟩)
  revert this
  decide

/-- `prod(Int8[-1]; init = 0x01) === 0xff`: `mul_prod(::UInt8, ::Int8)` falls back to `*`,
which stays in `UInt8`. -/
theorem prodInitWidened_refuted : ¬ ProdInitWidened := by
  intro h
  obtain ⟨w, hw, heq⟩ := h .i8 .u8 [JInt.lit .i8 (-1)] rfl rfl (by simp) (by decide)
  have hv : Vec.prodInit (.int .u8 (JInt.lit .u8 1)) (ints .i8 [JInt.lit .i8 (-1)]) =
      .int .u8 (JInt.lit .u8 255) := by decide
  rw [hv] at heq
  rcases hw with rfl | rfl <;> simp at heq

/-- `sum(Iterators.flatten([Int[]]))` throws, `sum(Int[]) == 0`. -/
def HistoricalFlattenSumAgrees : Prop :=
  ∀ vs : List (List Val), (∀ v ∈ vs, ∀ x ∈ v, ∃ y, x = .int .i64 y) →
    Vec.foldlFlatten Val.addSum Val.firstAddSum (fun _ => .error .argumentError) (.vector (.int .i64)) vs =
      Vec.sum (.int .i64) vs.flatten

theorem flattenSumAgrees_refuted : ¬ HistoricalFlattenSumAgrees := by
  intro h
  have := h [[]] (by simp)
  revert this
  decide

end JuliaLean.Reduce

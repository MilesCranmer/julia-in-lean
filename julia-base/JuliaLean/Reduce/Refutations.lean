import JuliaLean.Reduce.Props

/-! Counterexamples for the refuted reduction properties. -/

namespace JuliaLean.Reduce

open JuliaLean.Float

/-- `2.5`. -/
def f2p5 : F64 := F64.ofBits 0x4004000000000000

/-- `foldr(+, [true])` returns `true`, not `reduce_first(+, true) == 1`. -/
theorem foldrReduceFirst_refuted : ¬ FoldrReduceFirst := by
  intro h
  have := h (.bool true) .bool
  revert this
  decide

/-- `any([missing false]; dims = 2)` throws `TypeError` from `or_any(false, missing)`. -/
theorem anyDimsSlices_refuted : ¬ AnyDimsSlices := by
  intro h
  obtain ⟨Rr, hR, -⟩ := h ⟨1, 2, [.missing, .bool false]⟩ 2 rfl (.inr rfl) (by decide)
    (by decide) (by decide)
  have he : anyDims id ⟨1, 2, [.missing, .bool false]⟩ 2 = .error .typeError := by decide
  rw [he] at hR
  cases hR

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
theorem flattenSumAgrees_refuted : ¬ FlattenSumAgrees := by
  intro h
  have := h [[]] (by simp)
  revert this
  decide

/-- `maximum(Union{Int,Float64}[1; 2.5;;]; dims = 1)` throws `InexactError`: the result
array gets element type `Int` from the first slice. -/
theorem maxDimsUnion_refuted : ¬ MaxDimsUnion := by
  intro h
  obtain ⟨Rr, hR, -⟩ := h ⟨2, 1, [Val.i64 1, .f64 f2p5]⟩ 1 (.union (.int .i64) .f64) rfl
    (.inl rfl) (by decide) (by decide) (.inr (.inr rfl)) (by decide)
  have he : maxminDims (fun x => .ok x) true (.union (.int .i64) .f64)
      ⟨2, 1, [Val.i64 1, .f64 f2p5]⟩ 1 = .error .inexactError := by decide
  rw [he] at hR
  cases hR

/-- `maximum([missing;;]; dims = 1)` throws (`typemin(Union{})`). -/
theorem maxDimsMissing_refuted : ¬ MaxDimsMissing := by
  intro h
  obtain ⟨Rr, hR, -⟩ := h ⟨1, 1, [.missing]⟩ 1 true rfl (.inl rfl) (by decide) (by decide)
    (by simp)
  have he : maxminDims (fun x => .ok x) true .missing ⟨1, 1, [.missing]⟩ 1 =
      .error .methodError := by decide
  rw [he] at hR
  cases hR

/-- `maximum(abs, [typemin(Int);;]; dims = 1) == [0;;]`, `maximum(abs, [typemin(Int)])` is
`typemin(Int)`. -/
theorem maxAbsDims_refuted : ¬ MaxAbsDims := by
  intro h
  obtain ⟨Rr, hR, hk⟩ := h ⟨1, 1, [.int .i64 (JInt.typemin .i64)]⟩ 1 rfl (.inl rfl)
    (by decide) (by decide) (fun x hx => by simp at hx; exact ⟨_, hx⟩)
  have hR' : maxAbsDims (.int .i64) ⟨1, 1, [.int .i64 (JInt.typemin .i64)]⟩ 1 =
      .ok { ty := .int .i64, m := 1, n := 1, data := [Val.i64 0] } := by decide
  rw [hR'] at hR
  cases hR
  have := hk 0 (by decide)
  revert this
  decide

/-- `sum(Int8[100; 100;;]; dims = 1, init = Int8(0))` throws `InexactError`. -/
theorem sumDimsInit_refuted : ¬ SumDimsInit := by
  intro h
  obtain ⟨Rr, hR, -⟩ := h .i8 .i8 ⟨2, 1, [.int .i8 (JInt.lit .i8 100), .int .i8 (JInt.lit .i8 100)]⟩
    1 rfl rfl rfl (.inl rfl) (fun x hx => by
      simp at hx; first | exact ⟨_, hx⟩ | (rcases hx with hx | hx <;> exact ⟨_, hx⟩))
  have he : mapreduceDimsInit (fun x => .ok x) (fun x y => .ok (Val.addSum x y)) 1024
      (.int .i8 (JInt.lit .i8 0))
      ⟨2, 1, [.int .i8 (JInt.lit .i8 100), .int .i8 (JInt.lit .i8 100)]⟩ 1 =
      .error .inexactError := by decide
  rw [he] at hR
  cases hR

/-- `findmax(zeros(0, 0); dims = 1)` returns `0×0` arrays; the reduced shape is `1×0`. -/
theorem findDimsShape_refuted : ¬ FindDimsShape := by
  intro h
  have := h ⟨0, 0, []⟩ 1 .f64 ⟨{ ty := .f64, m := 0, n := 0, data := [] }, []⟩ rfl (.inl rfl)
    (by decide)
  revert this
  decide

/-- `accumulate(+, [1]; dims = 2, init = 10) == [1]`, not `[11]`. -/
theorem accumulateDimsInit_refuted : ¬ AccumulateDimsInit := by
  intro h
  have := h [JInt.lit .i64 1] (JInt.lit .i64 10) 2 (by decide)
  revert this
  decide

/-- `cumsum([1]; dims = 0) == [1]`, `accumulate(+, [1]; dims = 0)` throws. -/
theorem cumsumAccumulate_refuted : ¬ CumsumAccumulate := by
  intro h
  have := h [JInt.lit .i64 1] 0
  revert this
  decide

end JuliaLean.Reduce

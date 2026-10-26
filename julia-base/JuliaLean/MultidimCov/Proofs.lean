import JuliaLean.MultidimCov.Props

namespace JuliaLean.MultidimCov

private theorem totalDeterministic {Method Input Output : Type}
    (run : Method → Input → Output) : TotalDeterministic run := by
  intro method input
  refine ⟨run method input, rfl, ?_⟩
  intro output h
  exact h.symm

theorem cartesianMethodsCorrect : CartesianMethodsCorrect := by
  constructor
  · exact totalDeterministic runCartesian
  · intro xs
    simp [flattenCartesian]

theorem cartesianIndicesMethodsCorrect : CartesianIndicesMethodsCorrect := by
  constructor
  · exact totalDeterministic runCartesianIndices
  · intro axes
    rfl

theorem indexingMethodsCorrect : IndexingMethodsCorrect := by
  constructor
  · exact totalDeterministic runIndexing
  · intro mask
    rfl

theorem logicalIndexTracksMask_refuted : ¬ LogicalIndexTracksMask := by
  intro h
  have bad := h { mask := [true, true], cachedCount := 1 }
  simp [collectLogicalIndex, makeLogicalIndex, truePositions] at bad

theorem algorithmMethodsCorrect : AlgorithmMethodsCorrect := by
  constructor
  · exact totalDeterministic runAlgorithm
  · intro x h
    simp [tryBoolConversion] at h
    split at h <;> simp_all [uncheckedBoolConvert]

private def offsetAxes : List Axis :=
  [ { first := JInt.lit .i64 2, step := JInt.lit .i64 1, len := 2 },
    { first := JInt.lit .i64 1, step := JInt.lit .i64 1, len := 3 } ]

theorem permutedimsOffsetCorrect_refuted : ¬ PermutedimsOffsetCorrect := by
  intro h
  have hp := h offsetAxes [1, 0] (by decide) (by decide)
  obtain ⟨out, hout, _⟩ := hp
  have hbad : permutedimsStrided offsetAxes [1, 0] = .dimensionMismatch := by rfl
  rw [hbad] at hout
  cases hout

theorem subarrayMethodsCorrect : SubarrayMethodsCorrect := by
  constructor
  · exact totalDeterministic runSubarray
  · intro indices
    rfl

theorem slicesMethodsCorrect : SlicesMethodsCorrect := by
  constructor
  · exact totalDeterministic runSlices
  · intro slices
    rfl

end JuliaLean.MultidimCov

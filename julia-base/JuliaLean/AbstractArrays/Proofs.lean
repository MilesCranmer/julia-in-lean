import JuliaLean.AbstractArrays.Props
import JuliaLean.ArrayOps.PureProofs
import JuliaLean.ReinterpretArrays.ProofSmi

namespace JuliaLean.AbstractArrays

open JuliaLean

theorem sizeAxesDim_proven : SizeAxesDim := by
  intro sizes d
  constructor
  · intro h
    simp [sizeDim, axesDim, h]
  constructor
  · intro h1 h2
    simp [sizeDim, axesDim, show ¬d.val < 1 by omega, h2]
  · intro h
    simp [sizeDim, axesDim, show ¬d.val < 1 by omega, show ¬d.val ≤ sizes.length by omega]

theorem checkIndexForms_proven : CheckIndexForms := by
  constructor
  · intro a i
    rfl
  constructor
  · intro a r
    rfl
  · intro a
    rfl

theorem checkboundsCartesian_proven : CheckboundsCartesian := by
  intro axes is
  induction axes, is using checkCoords.induct <;>
    simp_all [checkCoords, CoordsValid, checkScalar, List.all_eq_true]

theorem checkboundsLogical_proven : CheckboundsLogical := by
  intro axes maskAxes
  simp [checkMask]

theorem checkboundsLinear_proven : CheckboundsLinear := by
  constructor
  · intro a i
    rfl
  · intro axes i h
    cases axes with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b rest => rfl

theorem toIndicesCartesian_proven : ToIndicesCartesian := by
  constructor
  · intro axes is
    rfl
  · intro axes i
    cases axes <;> simp [toIndices, ScalarIndex.toIndex]

theorem copytoGeneric_proven : CopytoGeneric := by
  intro α dest src
  constructor
  · intro h
    simp [GVec.copyAll, h]
  · intro h
    simp [GVec.copyAll, show ¬src.slots.length ≤ dest.slots.length by omega]

theorem copytoOverlap_proven : CopytoOverlap := by
  exact JuliaLean.ArrayOps.copytoAliasSpec

theorem similarFallback_proven : SimilarFallback := by
  intro α n
  simp [GVec.similar]

theorem indexIteration_proven : IndexIteration := by
  intro α v
  simp [GVec.eachIndex, GVec.firstIndex, GVec.lastIndex]

theorem isassignedSpec_proven : IsassignedSpec := by
  intro α v i
  unfold GVec.isAssigned
  simp only [ScalarIndex.toIndex, bind, Except.bind, pure, Except.pure]
  split <;> simp_all

theorem concatVectors_proven : ConcatVectors := by
  constructor
  · intro α β γ f g xs ys
    rfl
  · intro α β γ f g xs ys
    constructor
    · intro h
      simp [hcatPromote, h]
    · intro h
      refine ⟨"number of rows must match", ?_⟩
      simp [hcatPromote, h]

theorem basicArrayOps_proven : BasicArrayOps := by
  intro α v x
  simp [GVec.reverse, GVec.fill, GVec.axis, GVec.isEmpty]

theorem requireOneBased_proven : RequireOneBased := by
  intro axes
  constructor
  · intro hall
    have hnone : hasOffsetAxes axes = false := by
      simp only [hasOffsetAxes, List.any_eq_false]
      intro a ha
      have hbase : Axis.isOneBased a = true := by
        rw [List.all_eq_true] at hall
        exact hall a ha
      simp [hbase]
    simp [requireOneBased, hnone]
  · intro hany
    refine ⟨"offset arrays are not supported", ?_⟩
    simp [requireOneBased, hasOffsetAxes] at hany ⊢
    exact hany

theorem linearCartesianRoundTrip_proven : LinearCartesianRoundTrip := by
  exact JuliaLean.ReinterpretArrays.ind2subCorrect

end JuliaLean.AbstractArrays

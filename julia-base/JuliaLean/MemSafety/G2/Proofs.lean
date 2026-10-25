import JuliaLean.MemSafety.G2.Model

namespace JuliaLean.MemSafety.G2

theorem reverseInBounds : ReverseInBounds := by
  intro n k hk
  simp only [reverseOrdinals]
  omega

theorem constGetindexInBounds : ConstGetindexInBounds :=
  JuliaLean.AbstractArrays.linearCartesianRoundTrip_proven

theorem enumeratedInBounds : EnumeratedInBounds := by
  intro n k hk
  exact List.mem_range.mp hk

theorem exprCopyInBounds : ExprCopyInBounds := enumeratedInBounds

theorem gmpLimbAccessesInBounds : GmpLimbAccessesInBounds := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro allocated used i hused hi1 hi
    exact Nat.le_trans hi (Nat.le_trans hused (Nat.le_max_right 1 allocated))
  · intro allocated
    exact Nat.le_max_left 1 allocated
  · intro used pow hused hpow
    have hdiv : pow / 64 < used := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 64)]
      omega
    omega
  · intro used start count offset hwindow hoffset
    unfold byteLimb
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 8)]
    omega

theorem gmpStringSignInBounds : GmpStringSignInBounds := by
  intro nd hnd
  omega

theorem hashArrayInBounds : HashArrayInBounds := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h8 h16
    omega
  · intro n h4 h8
    omega
  · intro n hn h4
    omega
  · intro n pos hpos
    omega
  · intro n pos i hn hi hi48
    omega
  · intro n h16
    omega

theorem linearIndicesRangeInBounds : LinearIndicesRangeInBounds :=
  JuliaLean.AbstractArrays.checkIndexForms_proven

theorem loadingHeaderInBounds : LoadingHeaderInBounds := by
  intro basenameLength
  omega

theorem missingMapreduceInBounds : MissingMapreduceInBounds := by
  intro n first last i hfirst hi hlast
  omega

theorem cartesianGetindexInBounds : CartesianGetindexInBounds :=
  JuliaLean.AbstractArrays.checkboundsCartesian_proven

theorem cartesianIterationInBounds : CartesianIterationInBounds :=
  ⟨enumeratedInBounds, JuliaLean.ReinterpretArrays.ind2subCorrect⟩

theorem logicalIndexInBounds : LogicalIndexInBounds := by
  constructor
  · intro chunks sum hsum hchunks
    omega
  · intro chunks current hcurrent
    omega

theorem matchedIterationInBounds : MatchedIterationInBounds := by
  intro sourceCount destCount k hcount hk
  omega

theorem diffAndBlockCopyInBounds : DiffAndBlockCopyInBounds := by
  constructor
  · intro n i hi
    omega
  · intro sourceCount destCount k hcount hk
    omega

theorem bitCopyInBounds : BitCopyInBounds := by
  intro destBits sourceCount destStart sourceStart count k hdest hsource hk
  omega

theorem isassignedInBounds : IsassignedInBounds :=
  JuliaLean.AbstractArrays.isassignedSpec_proven

theorem reshapedIndexingInBounds : ReshapedIndexingInBounds :=
  JuliaLean.ReinterpretArrays.ind2subCorrect

theorem ryuExponentTableInBounds : RyuExponentTableInBounds := by
  intro exp hexp
  constructor
  · intro h100
    have hdiv : exp / 10 ≤ 32 := by omega
    omega
  · omega

theorem payneHanekTableInBounds_refuted : ¬ PayneHanekTableInBounds := by
  intro h
  have hm : (-15 : Int) ∈ payneHanekTableIndices 0 := by decide
  have hb := h 0 (by omega) (-15) hm
  omega

theorem stringViewInBounds : StringViewInBounds := by
  constructor
  · intro n i j next hi hij hj hnext
    omega
  · intro n removed hremoved
    omega

theorem summarySizeInBounds : SummarySizeInBounds := by
  constructor
  · intro n np i hnp hi
    rw [Nat.div_lt_iff_lt_mul hnp]
    omega
  · intro n i hi
    exact hi

end JuliaLean.MemSafety.G2

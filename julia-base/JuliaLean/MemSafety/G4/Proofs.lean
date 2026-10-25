import JuliaLean.MemSafety.G4.Model

namespace JuliaLean.MemSafety.G4

theorem checkedIntervalInBounds : CheckedIntervalInBounds := by
  intro len lo hi i hlo hlohi hhi hli hih
  exact ⟨by omega, by omega⟩

theorem bitArrayChunkInBounds : BitArrayChunkInBounds := by
  intro len i hi hil
  omega

theorem bitArrayCopyInBounds : BitArrayCopyInBounds := by
  intro destLen srcLen doffs soffs n i hd hs hn hdest hsrc hi hin
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

theorem bitCacheInBounds : BitCacheInBounds := by
  intro i h1 h2
  exact ⟨h1, h2⟩

theorem bootArrayRefInBounds : BootArrayRefInBounds := by
  intro len i h0 h1
  exact ⟨by omega, by omega⟩

theorem broadcastEachindexInBounds : BroadcastEachindexInBounds := by
  intro destLen bcLen i hlen hi
  subst destLen
  exact ⟨hi, hi⟩

theorem hamtSlotInBounds : HamtSlotInBounds := by
  intro before after
  dsimp
  omega

theorem processStatsReadsInBounds : ProcessStatsReadsInBounds := by
  intro bufLen off hlen hoff
  subst bufLen
  simp at hoff
  rcases hoff with rfl | rfl | rfl <;> omega

theorem rationalSplitInBounds : RationalSplitInBounds := by
  intro parts hp hn
  rcases hp with rfl | rfl
  · exact absurd rfl hn
  · omega

theorem reinterpretMapreduceInBounds : ReinterpretMapreduceInBounds := by
  intro K n firstJ lastJ i j hK hfirst horder hlast hsite
  rcases hsite with ⟨⟨rfl | rfl⟩, rfl⟩ | ⟨hi, hle, rfl⟩ | ⟨hi, hle, hj, hjl⟩ <;>
    omega

theorem reinterpretTupleInBounds : ReinterpretTupleInBounds := by
  intro N len h
  omega

theorem runtimeFieldInBounds : RuntimeFieldInBounds := by
  intro n i h1 h2
  exact ⟨h1, h2⟩

theorem runtimeBitfieldInBounds : RuntimeBitfieldInBounds := by
  intro n s h1 h2
  omega

theorem runtimeMetadataInBounds : RuntimeMetadataInBounds := by
  intro objectBytes readBytes _ h
  omega

theorem ryuAppendDigitsInBounds : RyuAppendDigitsInBounds := by
  intro bufLen pos digits hpos hdigits hcap
  omega

theorem ryuLookupInBounds_refuted : ¬ RyuLookupInBounds := by
  intro h
  have hz := h 1 (-1) (by omega)
  unfold InBounds at hz
  omega

theorem simdIndexInBounds : SimdIndexInBounds := by
  intro len i h
  omega

theorem sendToEndInBounds_refuted : ¬ SendToEndInBounds := by
  intro h
  have hz := h 1 0 1 0 (by omega) (by omega) (by omega)
  unfold InBounds at hz
  omega

theorem sortCountBucketInBounds : SortCountBucketInBounds := by
  intro range bucket h
  omega

theorem sortRadixBucketInBounds : SortRadixBucketInBounds := by
  intro mask bucket h
  omega

theorem stringSearchInBounds : StringSearchInBounds := by
  intro n i h1 h2
  exact ⟨h1, h2⟩

theorem cpuInfoInBounds : CpuInfoInBounds := by
  intro count i _ h
  exact h

end JuliaLean.MemSafety.G4

import JuliaLean.MemSafety.G4.Model

namespace JuliaLean.MemSafety.G4

theorem checkedIntervalInBounds : CheckedIntervalInBounds := by
  intro len lo hi k i h
  unfold checkedIntervalIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem bitArrayChunkInBounds : BitArrayChunkInBounds := by
  intro len i chunk h
  unfold bitArrayChunkIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst chunk
    unfold InBounds
    omega
  · contradiction

theorem bitFindKeyInBounds : BitFindKeyInBounds := by
  intro bits wanted len i h
  unfold bitFindKeyAccess at h
  split at h
  · contradiction
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    unfold bitFindKeyIndex InBounds
    cases hfind : bits.findIdx? (· == wanted) with
    | none =>
        have hlen : 0 < bits.length := by
          cases bits with
          | nil => contradiction
          | cons => simp
        simp only [hfind]
        omega
    | some k =>
        have hk : k < bits.length := (List.findIdx?_eq_some_iff_getElem.mp hfind).1
        simp only [hfind]
        omega

theorem bitFindAllInBounds : BitFindAllInBounds := by
  intro bits selection i h
  unfold bitFindAllOutputIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem bitArrayCopyInBounds : BitArrayCopyInBounds := by
  intro destLen srcLen doffs soffs n k di si h
  unfold bitArrayCopyIndex at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    unfold InBounds
    omega
  · contradiction

theorem bitArrayCopyChunksInBounds : BitArrayCopyChunksInBounds := by
  intro destLen srcLen doffs soffs n k dlen slen di si h
  unfold bitArrayCopyChunkIndex at h
  cases hc : bitArrayCopyIndex destLen srcLen doffs soffs n k with
  | none => simp [hc] at h
  | some p =>
      rcases p with ⟨dei, sei⟩
      simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      have hb := bitArrayCopyInBounds destLen srcLen doffs soffs n k dei sei hc
      constructor
      · apply bitArrayChunkInBounds destLen.toNat dei
        have hd := hb.1
        unfold InBounds at hd
        unfold bitArrayChunkIndex
        rw [if_pos hd]
      · apply bitArrayChunkInBounds srcLen.toNat sei
        have hs := hb.2
        unfold InBounds at hs
        unfold bitArrayChunkIndex
        rw [if_pos hs]

theorem bitCacheInBounds : BitCacheInBounds := by
  intro iteration tail i h
  dsimp [bitCacheIndex] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    have hm := Nat.mod_lt iteration (by decide : 0 < 4096)
    omega
  · contradiction

theorem bitMaskChunksInBounds : BitMaskChunksInBounds := by
  intro destChunks maskChunks k di mi h
  unfold bitMaskChunkIndex at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    unfold InBounds
    omega
  · contradiction

theorem bitMaskSourceInBounds : BitMaskSourceInBounds := by
  intro mask sourceLen selection i h
  unfold bitMaskSourceIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem bitVectorLoopInBounds : BitVectorLoopInBounds := by
  intro chunks k fromEnd i h
  unfold bitVectorLoopIndex at h
  split at h
  · split at h <;> simp only [Option.some.injEq] at h <;> subst i <;>
      unfold InBounds <;> omega
  · contradiction

theorem bootArrayRefInBounds : BootArrayRefInBounds := by
  intro len i j h
  unfold bootArrayIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst j
    unfold InBounds
    omega
  · contradiction

theorem broadcastEachindexInBounds : BroadcastEachindexInBounds := by
  intro α axes k i h
  have hk : k < axes.length := List.getElem?_eq_some_iff.mp h |>.1
  have hi : axes[k] = i := by simpa [broadcastEachindex, List.getElem?_eq_getElem hk] using h
  rw [← hi]
  exact List.getElem_mem hk

theorem broadcastChunkInBounds : BroadcastChunkInBounds := by
  intro logicalLen k i h
  dsimp [broadcastChunkIndex] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem hamtSlotInBounds : HamtSlotInBounds := by
  intro s len i h
  unfold hamtDataAccess at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    unfold HamtSplit.dataLen HamtSplit.entryIndex InBounds at *
    simp_all
    omega
  · contradiction

theorem processStatsReadsInBounds : ProcessStatsReadsInBounds := by
  intro site
  cases site <;> simp [processStatsRead, ByteSpan.safe]

theorem rationalSplitInBounds : RationalSplitInBounds := by
  intro s which n i h
  unfold rationalAccess at h
  split at h
  · cases which <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      rcases h with ⟨rfl, rfl⟩ <;> exact ⟨by omega, by omega⟩
  · contradiction

theorem reinterpretMapreduceInBounds : ReinterpretMapreduceInBounds := by
  have safe : ∀ fuel K firstJ lastJ block n, 2 ≤ K → 1 ≤ firstJ → firstJ ≤ lastJ →
      lastJ ≤ n → 0 < block → ∀ a ∈ reinterpretMapreduceAccesses K firstJ lastJ block fuel,
        1 ≤ a.1 ∧ a.1 ≤ K ∧ 1 ≤ a.2 ∧ a.2 ≤ n := by
    intro fuel
    induction fuel with
    | zero => simp [reinterpretMapreduceAccesses]
    | succ fuel ih =>
        intro K firstJ lastJ block n hK hf hfl hln hb a ha
        simp only [reinterpretMapreduceAccesses, hK, hf, hfl, true_and, ↓reduceIte] at ha
        by_cases hs : lastJ - firstJ < block
        · simp only [hs, ↓reduceIte, List.mem_flatMap, List.mem_range, scartColumn,
            List.mem_map] at ha
          rcases ha with ⟨dj, hdj, i, hi, rfl⟩
          omega
        · simp only [hs, ↓reduceIte, List.mem_append] at ha
          let mid := firstJ + (lastJ - firstJ) / 2
          have hm0 : firstJ ≤ mid := by dsimp [mid]; omega
          have hml : mid < lastJ := by
            dsimp [mid]
            have hd : 0 < lastJ - firstJ := by omega
            have hh : (lastJ - firstJ) / 2 < lastJ - firstJ := by omega
            omega
          rcases ha with ha | ha
          · exact ih K firstJ mid block n hK hf hm0 (by omega) hb a ha
          · exact ih K (mid + 1) lastJ block n hK (by omega) (by omega) hln hb a ha
  intro K n block a ha
  unfold reinterpretMapreduceProgram at ha
  split at ha
  · rename_i h
    exact safe (n + 1) K 1 n block n h.1 (by omega) (by omega) (by omega) h.2.2 a ha
  · contradiction

theorem reinterpretTupleInBounds : ReinterpretTupleInBounds := by
  intro N itrLen len i h
  unfold reinterpretTupleIndex at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨by decide, by decide⟩
  · contradiction

theorem runtimeFieldInBounds : RuntimeFieldInBounds := by
  intro n i j h
  unfold runtimeFieldIndex at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Option.some.injEq] at h
  subst j
  unfold InBounds
  omega

theorem runtimeBitfieldInBounds : RuntimeBitfieldInBounds := by
  intro n s i h
  unfold runtimeBitfieldIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem runtimeMetadataInBounds : RuntimeMetadataInBounds := by
  intro objects i j h
  unfold runtimeMetadataIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst j
    exact ‹1 ≤ i ∧ i ≤ ↑objects›
  · contradiction

theorem runtimeMetadataAccessesInBounds : RuntimeMetadataAccessesInBounds := by
  intro site
  cases site <;> simp [runtimeMetadataAccess, ByteSpan.safe]

theorem ryuLookupInBounds_refuted : ¬ RyuLookupInBounds := by
  intro h
  have hz := h 1 (-1) (by omega)
  unfold ryuLookupIndex InBounds at hz
  omega

theorem simdIndexInBounds : SimdIndexInBounds := by
  intro indices i j h
  have hi : i < indices.length := List.getElem?_eq_some_iff.mp h |>.1
  have hj : indices[i] = j := by simpa [simdIndex, List.getElem?_eq_getElem hi] using h
  rw [← hj]
  exact List.getElem_mem hi

theorem sendToEndInBounds_refuted : ¬ SendToEndInBounds := by
  intro h
  have hz := h 1 0 1 0 (by simp [sendToEndFirstIndex])
  unfold InBounds at hz
  omega

private theorem listMinMax_bounds : ∀ (values : List Nat) (lo hi : Nat),
    listMinMax values = some (lo, hi) → ∀ value ∈ values, lo ≤ value ∧ value ≤ hi
  | [], _, _, h => by simp [listMinMax] at h
  | x :: xs, lo, hi, h => by
      simp only [listMinMax] at h
      cases hm : listMinMax xs with
      | none =>
          simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          intro value hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · omega
          · cases xs with
            | nil => simp at hv
            | cons y ys =>
                have hsome : listMinMax (y :: ys) ≠ none := by
                  simp only [listMinMax]
                  cases listMinMax ys <;> simp
                exact False.elim (hsome hm)
      | some p =>
          rcases p with ⟨a, b⟩
          simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          intro value hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact ⟨Nat.min_le_left _ _, Nat.le_max_left _ _⟩
          · have hb := listMinMax_bounds xs a b hm value hv
            exact ⟨Nat.le_trans (Nat.min_le_right _ _) hb.1,
              Nat.le_trans hb.2 (Nat.le_max_right _ _)⟩

theorem sortCountBucketInBounds : SortCountBucketInBounds := by
  intro values k countLen i h
  unfold sortCountIndex at h
  cases hv : values[k]? with
  | none => simp [hv] at h
  | some value =>
      cases hm : listMinMax values with
      | none => simp [hv, hm] at h
      | some p =>
          rcases p with ⟨minimum, maximum⟩
          simp only [hv, hm, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hk : k < values.length := (List.getElem?_eq_some_iff.mp hv).1
          have hmem : value ∈ values := by
            have he : values[k] = value := by simpa [List.getElem?_eq_getElem hk] using hv
            rw [← he]
            exact List.getElem_mem hk
          have hb := listMinMax_bounds values minimum maximum hm value hmem
          unfold InBounds
          omega

theorem sortPartitionInBounds : SortPartitionInBounds := by
  intro len lo hi k toEnd memory objectLen i h
  unfold sortPartitionIndex at h
  split at h
  · cases memory <;> split at h <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      rcases h with ⟨rfl, rfl⟩ <;> unfold InBounds <;> omega
  · contradiction

theorem sortPermDataInBounds : SortPermDataInBounds := by
  intro dataAxes indices k i h
  unfold sortPermDataIndex at h
  split at h
  · rename_i heq
    have hk : k < indices.length := List.getElem?_eq_some_iff.mp h |>.1
    have hi : indices[k] = i := by simpa [List.getElem?_eq_getElem hk] using h
    rw [← heq, ← hi]
    exact List.getElem_mem hk
  · contradiction

theorem boolSortInBounds : BoolSortInBounds := by
  intro xs first phase k i h
  have hc : xs.count first ≤ xs.length := List.count_le_length
  cases phase with
  | scan =>
      by_cases hk : k < xs.length
      · simp [boolSortIndex, hk] at h
        subst i
        unfold InBounds
        omega
      · simp [boolSortIndex, hk] at h
  | first =>
      by_cases hk : k < xs.count first
      · simp [boolSortIndex, hk] at h
        subst i
        unfold InBounds
        omega
      · simp [boolSortIndex, hk] at h
  | second =>
      by_cases hk : k < xs.length - xs.count first
      · simp [boolSortIndex, hk] at h
        subst i
        unfold InBounds
        omega
      · simp [boolSortIndex, hk] at h

theorem sortRadixBucketInBounds : SortRadixBucketInBounds := by
  intro chunk x
  dsimp [sortRadixIndices]
  have hp : 0 < 2 ^ chunk := Nat.two_pow_pos chunk
  have hm := Nat.mod_lt x hp
  omega

theorem stringSearchInBounds : StringSearchInBounds := by
  intro positions start forward k i h
  have hk' : k < (stringSearchPositions positions start forward).length :=
    List.getElem?_eq_some_iff.mp h |>.1
  have hi : (stringSearchPositions positions start forward)[k] = i := by
    simpa [stringSearchIndex, List.getElem?_eq_getElem hk'] using h
  have hm : i ∈ stringSearchPositions positions start forward := by
    rw [← hi]
    exact List.getElem_mem hk'
  unfold stringSearchPositions at hm
  split at hm <;> simp_all

theorem cpuInfoInBounds : CpuInfoInBounds := by
  intro count i j h
  unfold cpuInfoIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst j
    unfold InBounds
    omega
  · contradiction

theorem vectorSearchFirstInBounds : VectorSearchFirstInBounds := by
  intro α lt v x horder hsorted hlen i
  obtain ⟨r, hr, -⟩ := (JuliaLean.Sort.vectorSearchCorrect α lt v x horder hsorted hlen).1
  rw [hr]
  intro h
  cases h

end JuliaLean.MemSafety.G4

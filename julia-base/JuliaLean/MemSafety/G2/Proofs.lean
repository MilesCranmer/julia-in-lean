import JuliaLean.MemSafety.G2.RyuProofs

namespace JuliaLean.MemSafety.G2

open JuliaLean

private theorem oneBased_mem {n : Nat} {i : Int} (h : i ∈ oneBased n) :
    1 ≤ i ∧ i ≤ n := by
  simp [oneBased] at h
  omega

private theorem mappedOneBased (n : Nat) :
    AllInBounds ((oneBased n).map fun i => Access.mk n i) := by
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact oneBased_mem hi

private theorem reverseAxisPass_safe (a : JuliaLean.AbstractArrays.Axis) (r l : Bool) :
    AllInBounds (reverseAxisPass a r l) := by
  intro access ha
  simp only [reverseAxisPass, List.mem_flatMap, List.mem_range] at ha
  split at ha
  all_goals
    obtain ⟨k, hk, hmem⟩ := ha
    simp at hmem
    rcases hmem with rfl | rfl
    · simp only [Access.inBounds]
      omega
    · simp only [Access.inBounds]
      split <;> omega

private theorem reverseFuel_safe : ∀ fuel axes dims,
    AllInBounds (reverseAccessesFuel fuel axes dims)
  | 0, axes, dims => by simp [reverseAccessesFuel, AllInBounds]
  | fuel + 1, axes, dims => by
      intro access ha
      simp only [reverseAccessesFuel] at ha
      split at ha
      · split at ha
        · rw [List.mem_append] at ha
          rcases ha with ha | ha
          · simp only [List.mem_flatMap] at ha
            obtain ⟨pair, hpair, ha⟩ := ha
            exact reverseAxisPass_safe pair.1 (dims.contains (pair.2 + 1))
              (pair.2 + 1 == dims.headD 0) access ha
          · exact reverseFuel_safe fuel (middleViewAxes axes (dims.headD 0)) dims.tail access ha
        · simp only [List.mem_flatMap] at ha
          obtain ⟨pair, hpair, ha⟩ := ha
          exact reverseAxisPass_safe pair.1 (dims.contains (pair.2 + 1))
            (pair.2 + 1 == dims.headD 0) access ha
      · simp at ha

theorem reverseInBounds : ReverseInBounds := by
  intro axes dims
  exact reverseFuel_safe dims.length axes dims

private theorem sub2ind_bounds : ∀ dims coords,
    dims.length = coords.length →
    (∀ p ∈ dims.zip coords, 1 ≤ p.2 ∧ p.2 ≤ p.1) →
    1 ≤ sub2ind dims coords ∧ sub2ind dims coords ≤ product dims
  | [], [], _, _ => by simp [sub2ind, product]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | [d], [i], _, h => by
      have hi := h (d, i) (by simp)
      simpa [sub2ind, product] using hi
  | d :: d2 :: ds, i :: i2 :: is, hlen, h => by
      have hd := h (d, i) (by simp)
      have htail : ∀ p ∈ (d2 :: ds).zip (i2 :: is), 1 ≤ p.2 ∧ p.2 ≤ p.1 := by
        intro p hp
        exact h p (by exact List.mem_cons_of_mem _ hp)
      have hlen' : (d2 :: ds).length = (i2 :: is).length := by simpa using hlen
      have ih := sub2ind_bounds (d2 :: ds) (i2 :: is) hlen' htail
      change 1 ≤ i + (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ∧
        i + (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ≤
          (d : Int) * product (d2 :: ds)
      have hm0 : 0 ≤ (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) :=
        Int.mul_nonneg (by omega) (by omega)
      have hm1 : (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ≤
          (d : Int) * ((product (d2 :: ds) : Int) - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have hid : (d : Int) * ((product (d2 :: ds) : Int) - 1) =
          (d : Int) * product (d2 :: ds) - d := by
        rw [Int.mul_sub, Int.mul_one]
      rw [hid] at hm1
      omega

private theorem normalized_lengths (dims : List Nat) (coords : List Int) :
    (normalizeDims dims (max dims.length coords.length)).length =
      (normalizeCoords coords (max dims.length coords.length)).length := by
  simp [normalizeDims, normalizeCoords]
  omega

theorem constGetindexInBounds : ConstGetindexInBounds := by
  constructor
  · intro dims i access ha
    simp only [constLinearAccess] at ha
    split at ha
    · simp only [List.mem_singleton] at ha
      subst access
      simp only [Access.inBounds]
      simp_all
    · simp at ha
  · intro dims coords access ha
    simp only [constCartesianAccess] at ha
    split at ha
    · simp only [List.mem_singleton] at ha
      subst access
      simp only [Access.inBounds]
      apply sub2ind_bounds
      · exact normalized_lengths dims coords
      · intro p hp
        simp only [coordsCheck] at *
        have hall := of_decide_eq_true (List.all_eq_true.mp ‹_› p hp)
        exact hall
    · simp at ha

private theorem constCartesianAccessAxes_safe (axes : List JuliaLean.AbstractArrays.Axis)
    (coords : List Int) : AllInBounds (constCartesianAccessAxes axes coords) := by
  simpa only [constCartesianAccessAxes] using
    constGetindexInBounds.2 (axes.map (fun axis => axis.len)) (relativeCoords axes coords)

theorem exprCopyInBounds : ExprCopyInBounds := by
  intro values
  constructor
  · intro access ha
    simp only [exprCopyAccesses, List.mem_flatMap] at ha
    obtain ⟨i, hi, ha⟩ := ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact oneBased_mem hi
    · split at ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> exact oneBased_mem hi
      · simp at ha
  · simpa [exprArgsAccesses] using mappedOneBased values.length

theorem gmpBoolRemInBounds_refuted : ¬ GmpBoolRemInBounds := by
  intro h
  have bad := h BigStorage.globalZero
  simp [gmpBoolRemAccess, BigStorage.capacity, AllInBounds, Access.inBounds] at bad

private theorem scanNonzeroLimbs_safe (x : Int) : ∀ n i,
    i ∈ scanNonzeroLimbs x n → 1 ≤ i ∧ i ≤ n
  | 0, i, h => by simp [scanNonzeroLimbs] at h
  | n + 1, i, h => by
      simp only [scanNonzeroLimbs, List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · split at h
        · have ih := scanNonzeroLimbs_safe x n i h
          omega
        · simp at h

theorem gmpLimbAccessesInBounds : GmpLimbAccessesInBounds := by
  refine ⟨?_, ?_, ?_⟩
  · intro x access ha
    simp only [gmpConstructorAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact oneBased_mem hi
  · intro x words access ha
    simp only [gmpRemainderAccesses, List.mem_append] at ha
    rcases ha with ha | ha
    · split at ha
      · simp at ha
      · simp only [List.mem_singleton] at ha
        subst access
        simp only [Access.inBounds]
        have hp : 0 < JuliaLean.BigNums.nlimbs x := by
          unfold JuliaLean.BigNums.nlimbs
          simp [*]
        omega
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      have hb := oneBased_mem hi
      simp only [Access.inBounds]
      omega
  · intro x access ha
    simp only [gmpFloatAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp only [Access.inBounds]
        omega
      · split at hi
        · have hs := scanNonzeroLimbs_safe x _ i hi
          simp only [Access.inBounds]
          omega
        · simp at hi

theorem gmpBitMagnitudeInBounds : GmpBitMagnitudeInBounds := by
  intro x access ha
  simp only [gmpBitMagnitudeAccess] at ha
  split at ha
  · simp at ha
  · simp only [List.mem_singleton] at ha
    subst access
    simp only [Access.inBounds]
    have hp : 0 < JuliaLean.BigNums.nlimbs x := by
      unfold JuliaLean.BigNums.nlimbs
      simp [*]
    omega

theorem gmpStringSignInBounds : GmpStringSignInBounds := by
  intro n base pad access ha
  simp only [gmpStringSignAccess] at ha
  split at ha
  · simp at ha
  · split at ha
    · simp only [List.mem_singleton] at ha
      subst access
      simp only [Access.inBounds]
      omega
    · simp at ha

private theorem window_mem {start width k : Nat} (h : k ∈ window start width) :
    start ≤ k ∧ k < start + width := by
  simp [window] at h
  omega

private theorem hashLoop_mem : ∀ i pos k,
    k ∈ hashLoop i pos → pos ≤ k ∧ k < pos + i
  := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      intro pos k hk
      rw [hashLoop] at hk
      split at hk
      · rw [List.mem_append] at hk
        rcases hk with hk | hk
        · have hw := window_mem hk
          omega
        · have hr := ih (i - 48) (by omega) (pos + 48) k hk
          omega
      · rw [List.mem_append] at hk
        rcases hk with hk | hk
        · split at hk
          · have hw := window_mem hk
            omega
          · simp at hk
        · split at hk
          · have hw := window_mem hk
            omega
          · simp at hk

private theorem hashByteOffsets_mem {n k : Nat} (h : k ∈ hashByteOffsets n) : k < n := by
  simp only [hashByteOffsets] at h
  split at h
  · split at h
    · rcases List.mem_append.mp h with h | h <;> have hw := window_mem h <;> omega
    · split at h
      · rcases List.mem_append.mp h with h | h <;> have hw := window_mem h <;> omega
      · split at h
        · simp at h
          rcases h with rfl | rfl | rfl <;> omega
        · simp at h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · have hh := hashLoop_mem n 0 k h
        omega
      · have hw := window_mem h
        omega
    · have hw := window_mem h
      omega

theorem hashArrayInBounds : HashArrayInBounds := by
  intro a access ha
  simp only [hashArrayAccesses, List.mem_map] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  have hb := hashByteOffsets_mem hk
  simp only [Access.inBounds]
  omega

private theorem firstNonzeroBit_le (limbs : List Nat) :
    firstNonzeroBit limbs ≤ 64 * limbs.length := by
  unfold firstNonzeroBit
  cases h : (List.range (64 * limbs.length)).findIdx? (limbBit limbs) with
  | none => simp [h]
  | some k =>
      have hk : k < (List.range (64 * limbs.length)).length :=
        (List.findIdx?_eq_some_iff_getElem.mp h).1
      simp only [List.length_range] at hk
      simp [h]
      omega

private theorem viewLimbAccesses_safe (limbs : List Nat) (start count : Nat)
    (hstart : 1 ≤ start) (hspan : start - 1 + count ≤ 8 * limbs.length) :
    AllInBounds (viewLimbAccesses limbs start count) := by
  intro access ha
  simp only [viewLimbAccesses, List.mem_map] at ha
  obtain ⟨byte, hbyte, rfl⟩ := ha
  have hb := hashByteOffsets_mem hbyte
  simp only [Access.inBounds]
  constructor
  · exact_mod_cast Nat.succ_pos ((start + byte - 1) / 8)
  · have hlt : (start + byte - 1) / 8 < limbs.length := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 8)]
      omega
    exact_mod_cast Nat.succ_le_of_lt hlt

set_option maxHeartbeats 200000 in
theorem gmpHashInBounds : GmpHashInBounds := by
  constructor
  · intro limbs access ha
    simp only [gmpHashIntegerAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp only [Access.inBounds]
        have hne : limbs ≠ [] := by
          intro hnil
          subst limbs
          simp_all
        have : 0 < limbs.length := List.length_pos_iff.mpr hne
        omega
      · exact viewLimbAccesses_safe limbs 1 (8 * limbs.length - leadingZeroBytes limbs)
          (by omega) (by omega) access ha
  · intro limbs access ha
    simp only [gmpHashAccesses] at ha
    split at ha
    · simp at ha
    · split at ha
      · simp at ha
        subst access
        simp only [Access.inBounds]
        simp_all
      · split at ha
        · simp at ha
        · rw [List.mem_append] at ha
          rcases ha with hdirectTop | hview
          · rw [List.mem_append] at hdirectTop
            rcases hdirectTop with hdirect | htop
            · have hp := firstNonzeroBit_le limbs
              have hd : firstNonzeroBit limbs / 64 < limbs.length := by
                rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 64)]
                omega
              split at hdirect
              · simp only [List.mem_singleton] at hdirect
                subst access
                simp only [Access.inBounds]
                exact ⟨by omega, by exact_mod_cast Nat.succ_le_of_lt hd⟩
              · rw [List.mem_append] at hdirect
                rcases hdirect with hdirect | hnext
                · simp only [List.mem_singleton] at hdirect
                  subst access
                  simp only [Access.inBounds]
                  exact ⟨by omega, by exact_mod_cast Nat.succ_le_of_lt hd⟩
                · split at hnext
                  · simp only [List.mem_singleton] at hnext
                    subst access
                    simp only [Access.inBounds]
                    omega
                  · simp at hnext
            · simp only [List.mem_singleton] at htop
              subst access
              simp only [Access.inBounds]
              have hne : limbs ≠ [] := by
                intro hnil
                subst limbs
                simp_all
              have : 0 < limbs.length := List.length_pos_iff.mpr hne
              omega
          · exact viewLimbAccesses_safe limbs (firstNonzeroBit limbs / 8 + 1)
              (8 * limbs.length - (leadingZeroBytes limbs + firstNonzeroBit limbs / 8))
              (by omega) (by have hp := firstNonzeroBit_le limbs; omega) access hview

theorem loadingHeaderInBounds : LoadingHeaderInBounds := by
  have headerSafe : ∀ n, 12 ≤ n → AllInBounds (headerAccess n) := by
    intro n hn access ha
    simp [headerAccess] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp [Access.inBounds] <;> omega
  intro basename returned access ha
  simp only [loadingHeaderAccess, List.mem_append] at ha
  rcases ha with ha | ha
  · exact headerSafe _ (by omega) access ha
  · split at ha
    · exact headerSafe _ (by omega) access ha
    · simp at ha

theorem skipMissingEachindexInBounds : SkipMissingEachindexInBounds := by
  intro first missing access ha
  simp only [skipMissingEachindexAccesses, List.mem_map] at ha
  obtain ⟨i, hi, heq⟩ := ha
  subst access
  simp [axisValues] at hi
  simp only [Access.inBounds]
  omega

theorem skipMissingKeysInBounds : SkipMissingKeysInBounds := by
  intro axes access ha
  simp only [skipMissingKeysAccesses, List.mem_flatMap] at ha
  obtain ⟨coords, hcoords, ha⟩ := ha
  exact constCartesianAccessAxes_safe axes coords access ha

private theorem scanMissing_safe (missing : List Bool) (start count : Nat) :
    (∀ k ∈ (scanMissing missing start count).visited,
      start ≤ k ∧ k < start + count ∧ k < missing.length) ∧
    (∀ k, (scanMissing missing start count).found = some k →
      start ≤ k ∧ k < start + count ∧ k < missing.length) := by
  simp only [scanMissing]
  split
  · rename_i off hfind
    have hoff : off < (List.range (min count (missing.length - start))).length :=
      (List.findIdx?_eq_some_iff_getElem.mp hfind).1
    simp only [List.length_range] at hoff
    constructor
    · intro k hk
      simp only [List.mem_map, List.mem_range] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      omega
    · intro k hk
      simp only [Option.some.injEq] at hk
      subst k
      omega
  · constructor
    · intro k hk
      simp only [List.mem_map, List.mem_range] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      omega
    · intro k hk
      simp at hk

private theorem sequentialMapreduceTrace_safe (first : JuliaLean.AbstractArrays.I64)
    (missing : List Bool) :
    ∀ start count k, start + count ≤ missing.length →
      k ∈ sequentialMapreduceTrace first missing start count → k < missing.length := by
  intro start count k hspan hk
  simp only [sequentialMapreduceTrace] at hk
  cases hfound : (scanMissing missing start count).found with
  | none =>
      rw [hfound] at hk
      exact ((scanMissing_safe missing start count).1 k hk).2.2
  | some p =>
    rw [hfound] at hk
    simp_all only [Option.some.injEq]
    split at hk
    · exact ((scanMissing_safe missing start count).1 k hk).2.2
    · cases hfound2 : (scanMissing missing (p + 1) (start + count - (p + 1))).found with
      | none =>
        rw [hfound2] at hk
        rcases List.mem_append.mp hk with hk | hk
        · exact ((scanMissing_safe missing start count).1 k hk).2.2
        · exact ((scanMissing_safe missing (p + 1) (start + count - (p + 1))).1 k hk).2.2
      | some q =>
        rw [hfound2] at hk
        simp_all only [Option.some.injEq]
        split at hk
        · rcases List.mem_append.mp hk with hk | hk
          · exact ((scanMissing_safe missing start count).1 k hk).2.2
          · exact ((scanMissing_safe missing (p + 1) (start + count - (p + 1))).1 k hk).2.2
        · rcases List.mem_append.mp hk with hk | hk
          · rcases List.mem_append.mp hk with hk | hk
            · exact ((scanMissing_safe missing start count).1 k hk).2.2
            · exact ((scanMissing_safe missing (p + 1) (start + count - (p + 1))).1 k hk).2.2
          · simp only [List.mem_map, List.mem_range] at hk
            obtain ⟨j, hj, rfl⟩ := hk
            have hq := (scanMissing_safe missing (p + 1)
              (start + count - (p + 1))).2 q hfound2
            omega

private theorem mapreduceImplTrace_safe (first : JuliaLean.AbstractArrays.I64)
    (missing : List Bool) :
    ∀ fuel start count blockSize k, start + count ≤ missing.length →
      k ∈ mapreduceImplTrace fuel first missing start count blockSize → k < missing.length
  | 0, start, count, blockSize, k, hspan, hk => by simp [mapreduceImplTrace] at hk
  | fuel + 1, start, count, blockSize, k, hspan, hk => by
      simp only [mapreduceImplTrace] at hk
      split at hk
      · simp at hk
      · split at hk
        · simp only [List.mem_singleton] at hk
          subst k
          omega
        · split at hk
          · exact sequentialMapreduceTrace_safe first missing start count k hspan hk
          · rw [List.mem_append] at hk
            rcases hk with hk | hk
            · exact mapreduceImplTrace_safe first missing fuel start ((count - 1) / 2 + 1)
                blockSize k (by omega) hk
            · exact mapreduceImplTrace_safe first missing fuel (start + ((count - 1) / 2 + 1))
                (count - ((count - 1) / 2 + 1)) blockSize k (by omega) hk

theorem missingMapreduceInBounds : MissingMapreduceInBounds := by
  intro first missing blockSize access ha
  simp only [mapreduceBlockAccesses, List.mem_map] at ha
  obtain ⟨k, hk, heq⟩ := ha
  subst access
  simp only [Access.inBounds]
  have hbound : k < missing.length := by
    simp only [mapreduceOrdinals] at hk
    cases hfound : (scanMissing missing 0 missing.length).found with
    | none =>
      rw [hfound] at hk
      exact ((scanMissing_safe missing 0 missing.length).1 k hk).2.2
    | some p =>
      rw [hfound] at hk
      simp_all only [Option.some.injEq]
      split at hk
      · exact ((scanMissing_safe missing 0 missing.length).1 k hk).2.2
      · cases hfound2 : (scanMissing missing (p + 1) (missing.length - (p + 1))).found with
        | none =>
          rw [hfound2] at hk
          rcases List.mem_append.mp hk with hk | hk
          · exact ((scanMissing_safe missing 0 missing.length).1 k hk).2.2
          · exact ((scanMissing_safe missing (p + 1) (missing.length - (p + 1))).1 k hk).2.2
        | some q =>
          rw [hfound2] at hk
          simp_all only [Option.some.injEq]
          rcases List.mem_append.mp hk with hk | hk
          · rcases List.mem_append.mp hk with hk | hk
            · exact ((scanMissing_safe missing 0 missing.length).1 k hk).2.2
            · exact ((scanMissing_safe missing (p + 1) (missing.length - (p + 1))).1 k hk).2.2
          · exact mapreduceImplTrace_safe first missing missing.length 0 missing.length
              blockSize k (by omega) hk
  exact ⟨by omega, by omega⟩

theorem cartesianCollectInBounds : CartesianCollectInBounds := by
  intro axes
  simpa [cartesianCollectAccesses] using mappedOneBased (product (axes.map (·.len)))

private theorem logicalChunkScan_safe (bits : List Bool) : ∀ fuel chunk access,
    access ∈ logicalChunkScan bits fuel chunk → access.inBounds
  | 0, chunk, access, h => by simp [logicalChunkScan] at h
  | fuel + 1, chunk, access, h => by
      simp only [logicalChunkScan] at h
      split at h
      · split at h
        · simp only [List.mem_singleton] at h
          subst access
          simp only [Access.inBounds]
          omega
        · simp only [List.mem_cons] at h
          rcases h with rfl | h
          · simp only [Access.inBounds]
            omega
          · exact logicalChunkScan_safe bits fuel (chunk + 1) access h
      · simp at h

theorem logicalIndexInBounds : LogicalIndexInBounds := by
  intro bits access ha
  simp only [logicalIndexAccesses] at ha
  split at ha
  · exact logicalChunkScan_safe bits _ 0 access ha
  · simp at ha

theorem genericIndexingInBounds : GenericIndexingInBounds := by
  constructor
  · intro axes indices access ha
    simp only [genericGetindexAccesses] at ha
    split at ha
    · rw [List.mem_append] at ha
      rcases ha with ha | ha
      · simp only [List.mem_flatMap] at ha
        obtain ⟨coords, hcoords, ha⟩ := ha
        exact constCartesianAccessAxes_safe axes coords access ha
      · exact mappedOneBased (cartesianValues indices).length access ha
    · simp at ha
  · intro axes indices sourceLength access ha
    simp only [genericSetindexAccesses] at ha
    split at ha
    · rw [List.mem_append] at ha
      rcases ha with ha | ha
      · simp only [List.mem_flatMap] at ha
        obtain ⟨coords, hcoords, ha⟩ := ha
        exact constCartesianAccessAxes_safe axes coords access ha
      · exact mappedOneBased sourceLength access ha
    · simp at ha

theorem cartesianCopyInBounds : CartesianCopyInBounds := by
  intro dest src access ha
  simp only [cartesianCopyAccesses] at ha
  split at ha
  · rw [List.mem_append] at ha
    rcases ha with ha | ha
    · simp only [List.mem_flatMap] at ha
      obtain ⟨coords, hcoords, ha⟩ := ha
      exact constCartesianAccessAxes_safe src.parentAxes coords access ha
    · simp only [List.mem_flatMap] at ha
      obtain ⟨coords, hcoords, ha⟩ := ha
      exact constCartesianAccessAxes_safe dest.parentAxes coords access ha
  · simp at ha

theorem bitSourceScanInBounds : BitSourceScanInBounds := by
  intro sourceLength sourceStart count access ha
  simp only [bitSourceScanAccesses] at ha
  split at ha
  · simp only [List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    simp only [List.mem_range] at hk
    simp only [Access.inBounds]
    simp_all
    omega
  · simp at ha

theorem isassignedInBounds : IsassignedInBounds := by
  intro axes coords indexLinear access ha
  simp only [isassignedAccess] at ha
  split at ha
  · exact constCartesianAccessAxes_safe axes coords access ha
  · simp at ha

private theorem reshapedLinearInBounds : ∀ parent reshapeLength i,
    AllInBounds (reshapedLinearAccess parent reshapeLength i) := by
  intro parent reshapeLength i access ha
  simp only [reshapedLinearAccess] at ha
  split at ha
  · simp only [List.mem_singleton] at ha
    subst access
    simp only [Access.inBounds]
    simp_all
    omega
  · simp at ha

theorem reshapedIndexingInBounds : ReshapedIndexingInBounds := by
  refine ⟨reshapedLinearInBounds, ?_⟩
  intro parentLength parentIndex access ha
  simp only [reshapedIndexAccess] at ha
  split at ha
  · simp only [List.mem_singleton] at ha
    subst access
    simp_all [Access.inBounds]
  · simp at ha

private theorem payne_indices_safe (raw : Nat) (hlo : 1043 ≤ raw) (hhi : raw ≤ 2046) :
    ∀ i ∈ payneHanekIndices raw, 1 ≤ i ∧ i ≤ 19 := by
  intro i hi
  simp only [payneHanekIndices] at hi
  split at hi
  · simp at hi
    rcases hi with rfl | rfl | rfl <;> omega
  · rw [List.mem_append] at hi
    rcases hi with hi | hi
    · split at hi
      · simp at hi
      · simp at hi
        omega
    · simp at hi
      rcases hi with rfl | rfl | rfl <;> omega

theorem payneHanekCallerInBounds : PayneHanekCallerInBounds := by
  constructor
  · intro x access ha
    simp only [f64PayneAccesses] at ha
    split at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      apply payne_indices_safe _ _ _ i hi
      · simp_all
        omega
      · simp_all
        omega
    · simp at ha
  · intro x access ha
    simp only [f32PayneAccesses] at ha
    split at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      apply payne_indices_safe _ _ _ i hi
      · simp_all
        omega
      · simp_all
        omega
    · simp at ha

private theorem chompLength_le (bytes : List UInt8) : chompLength bytes ≤ bytes.length := by
  rw [chompLength]
  split
  · omega
  · dsimp only
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem stringViewInBounds : StringViewInBounds := by
  intro bytes first last
  constructor
  · intro access ha
    simp only [stringRangeAccesses] at ha
    split at ha
    · simp_all only [Bool.and_eq_true, decide_eq_true_eq]
      simp at ha
      rcases ha with rfl | rfl
      · simp only [Access.inBounds]
        omega
      · simp only [Access.inBounds]
        omega
    · simp at ha
  · intro access ha
    simp only [chompAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      have hb := oneBased_mem hi
      have hl := chompLength_le bytes
      simp only [Access.inBounds]
      omega

theorem summarySizeInBounds : SummarySizeInBounds := by
  constructor
  · intro length np access ha
    simp only [summaryInlineAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      simp only [frontierIndices, List.mem_map] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      simp only [List.mem_range] at hk
      rename_i hnonzero
      have hp : 0 < np := by
        simp at hnonzero
        omega
      have hk' : k < length * np := hk
      have hd : k / np < length := by
        exact (Nat.div_lt_iff_lt_mul hp).2 hk'
      simp only [Access.inBounds]
      simp
      constructor
      · exact_mod_cast Nat.succ_pos (k / np)
      · exact_mod_cast Nat.succ_le_of_lt hd
  · intro length access ha
    simp only [summaryOutlineAccesses, List.mem_map] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    simp only [frontierIndices, List.mem_map] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [List.mem_range] at hk
    simp only [Access.inBounds]
    omega

end JuliaLean.MemSafety.G2

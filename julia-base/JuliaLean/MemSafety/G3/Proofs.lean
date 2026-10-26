import JuliaLean.MemSafety.G3.Model

namespace JuliaLean.MemSafety.G3

open JuliaLean

private theorem linearOffset_lt_product :
    ∀ dims coords, coordsValid dims coords → linearOffset dims coords < dims.prod
  | [], [], _ => by simp [linearOffset]
  | d :: ds, c :: cs, h => by
      have hc : c < d := h.1
      have ih := linearOffset_lt_product ds cs h.2
      have hs : linearOffset ds cs + 1 ≤ ds.prod := Nat.succ_le_iff.mpr ih
      calc
        linearOffset (d :: ds) (c :: cs) = c + d * linearOffset ds cs := rfl
        _ < d + d * linearOffset ds cs := Nat.add_lt_add_right hc _
        _ = d * (linearOffset ds cs + 1) := by simp [Nat.mul_add, Nat.add_comm]
        _ ≤ d * ds.prod := Nat.mul_le_mul_left d hs
        _ = (d :: ds).prod := by simp
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

private theorem linearArrayIndices_safe_early (a : LinearArray α) :
    ∀ i ∈ linearArrayIndices a, inAxis a.first a.values.length i := by
  intro i hi
  simp only [linearArrayIndices, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  unfold inAxis
  omega

private theorem coordsValidB_true : ∀ dims coords,
    coordsValidB dims coords = true → coordsValid dims coords
  | [], [], _ => trivial
  | d :: ds, c :: cs, h => by
      simp only [coordsValidB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, coordsValidB_true ds cs h.2⟩
  | [], _ :: _, h => by simp [coordsValidB] at h
  | _ :: _, [], h => by simp [coordsValidB] at h

theorem abstractArrayCopySafe_proven : AbstractArrayCopySafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro α a start count i hi
    unfold checkedSpanAccesses at hi
    split at hi
    · rename_i hspan
      simp only [List.mem_map, List.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      unfold inAxis
      omega
    · simp at hi
  · intro α β dest src access hi
    unfold unaliasedCopyAccesses at hi
    split at hi
    · simp only [List.mem_append, List.mem_map] at hi
      rcases hi with ⟨index, hindex, rfl⟩ | ⟨index, hindex, rfl⟩
      · exact linearArrayIndices_safe_early dest index (List.mem_of_mem_take hindex)
      · exact linearArrayIndices_safe_early src index hindex
    · simp at hi
  · intro dims coords index hi
    unfold canonicalIndexAccess at hi
    split at hi
    · rename_i hcoords
      cases hi
      have hb := linearOffset_lt_product dims coords (coordsValidB_true dims coords hcoords)
      unfold inOneBased
      omega
    · contradiction

theorem abstractArrayConcatSafe_proven : AbstractArrayConcatSafe := by
  constructor
  · intro dims index hi
    simp only [concatAccesses, List.mem_map] at hi
    obtain ⟨coords, hcoords, rfl⟩ := hi
    have valid : coordsValid dims coords := by
      induction dims generalizing coords with
      | nil =>
          simp [shapeCoordinates] at hcoords
          subst coords
          trivial
      | cons dim dims ih =>
          simp only [shapeCoordinates, List.mem_flatMap, List.mem_map, List.mem_range] at hcoords
          obtain ⟨coordinate, hc, rest, hr, rfl⟩ := hcoords
          exact ⟨hc, ih rest hr⟩
    have hb := linearOffset_lt_product dims coords valid
    unfold inOneBased
    omega
  · intro dims i hi
    simp only [oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega

theorem abstractArrayIterationSafe_proven : AbstractArrayIterationSafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro α slices i hi
    simp only [stackAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega
  · intro α a i hi
    exact linearArrayIndices_safe_early a i hi
  · intro α a requested i hi
    exact linearArrayIndices_safe_early a i (List.mem_of_mem_take hi)

theorem deepcopyMemorySafe_proven : DeepcopyMemorySafe := by
  intro α x i hi
  simp only [deepcopyMemoryAccesses, oneBasedLoop, List.mem_map,
    List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  simp only [List.length_replicate]
  constructor <;> unfold inOneBased <;> omega

theorem dictProbeSafe_proven : DictProbeSafe := by
  intro K V o t hash index hinv hi
  unfold dictAccesses at hi
  simp only [List.mem_append] at hi
  rcases hi with (hprobe | hscan) | hfloor
  · unfold dictProbeAccesses at hprobe
    by_cases hzero : t.size = 0
    · simp [hzero] at hprobe
    · simp only [hzero, ↓reduceIte, List.mem_map, List.mem_range] at hprobe
      obtain ⟨distance, hd, rfl⟩ := hprobe
      have hp : Dicts.IsPow t.size := by
        rcases hinv.size with h | h
        · exact absurd h hzero
        · exact h
      have hh := Dicts.hashindex_range hp hash
      exact Dicts.pr_range hp hh.1 hh.2 hd
  · simp only [dictScanAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hscan
    obtain ⟨k, hk, rfl⟩ := hscan
    unfold inOneBased
    omega
  · simp only [dictFloorAccesses, List.mem_map, List.mem_range] at hfloor
    obtain ⟨k, hk, rfl⟩ := hfloor
    unfold inOneBased
    have hf := hinv.idxfloor
    omega

private theorem bitCountPrefix_mono (bitmap : Nat) :
    ∀ {a b : Nat}, a ≤ b → bitCountPrefix bitmap a ≤ bitCountPrefix bitmap b
  | _, 0, h => by simp at h; subst h; exact Nat.le_refl _
  | a, b + 1, h => by
      by_cases hab : a = b + 1
      · subst hab; exact Nat.le_refl _
      · have ha : a ≤ b := by omega
        have ih := bitCountPrefix_mono bitmap ha
        simp only [bitCountPrefix]
        split <;> omega

theorem persistentDictPathSafe_proven : PersistentDictPathSafe := by
  intro bitmap dataLength bi hbi hset hlen
  have hstep : bitCountPrefix bitmap (bi + 1) = bitCountPrefix bitmap bi + 1 := by
    simp [bitCountPrefix, hset]
  have hmono := bitCountPrefix_mono bitmap (show bi + 1 ≤ 32 by omega)
  unfold inOneBased
  rw [hlen]
  omega

private theorem windowsEnvStarts_safe :
    ∀ entryLengths offset i, i ∈ windowsEnvStarts offset entryLengths →
      i < offset + windowsEnvStorageLength entryLengths
  | [], offset, i, hi => by
      have h : i = offset := by simpa [windowsEnvStarts] using hi
      subst i
      simp [windowsEnvStorageLength]
  | len :: rest, offset, i, hi => by
      simp only [windowsEnvStarts, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp [windowsEnvStorageLength]
        omega
      · have h := windowsEnvStarts_safe rest (offset + len + 1) i hi
        simp only [windowsEnvStorageLength]
        omega

private theorem windowsEnvCopies_safe :
    ∀ entryLengths offset span, span ∈ windowsEnvCopies offset entryLengths →
      span.1 + span.2 ≤ offset + windowsEnvStorageLength entryLengths
  | [], _, span, hi => by simp [windowsEnvCopies] at hi
  | len :: rest, offset, span, hi => by
      simp only [windowsEnvCopies, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp only [windowsEnvStorageLength]
        simpa only [Nat.add_assoc] using
          Nat.add_le_add_left (Nat.le_add_right len (1 + windowsEnvStorageLength rest)) offset
      · have h := windowsEnvCopies_safe rest (offset + len + 1) span hi
        simp only [windowsEnvStorageLength]
        omega

theorem environmentBufferSafe_proven : EnvironmentBufferSafe := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro entryLengths offset hi
    simpa using windowsEnvStarts_safe entryLengths 0 offset hi
  · intro entryLengths span hi
    simpa using windowsEnvCopies_safe entryLengths 0 span hi
  · intro entries i hi
    simp only [unixEnvLoads, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega

theorem integerFormattingSafe_proven : IntegerFormattingSafe := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t bty n base pad result hr i hi
    unfold integerStringAccesses at hr
    cases hs : ParsePrint.IntPrint.string n base pad with
    | error e =>
      rw [hs] at hr
      simp only [Except.map] at hr
      cases hr
    | ok buf =>
      rw [hs] at hr
      simp only [Except.map, Except.ok.injEq] at hr
      subst result
      simp only [oneBasedLoop, List.mem_map, List.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      unfold inOneBased
      omega
  · intro t x i hi
    simp only [bitstringAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [bitstringAccesses]
    unfold inOneBased
    omega
  · intro remainder
    unfold decimalPairIndex inOneBased
    have hm := Nat.mod_lt remainder (by decide : 0 < 100)
    omega
  · intro base x index length hi
    unfold genericBaseDigitAccess at hi
    dsimp only at hi
    split at hi
    · rename_i hb
      split at hi <;> cases hi
      all_goals unfold inOneBased
      all_goals have hm := Int.emod_nonneg x (by omega : (base.natAbs : Int) ≠ 0)
      all_goals have hl := Int.emod_lt_of_pos x (by omega : 0 < (base.natAbs : Int))
      all_goals omega
    · contradiction
  · intro α a i hi
    simp only [linearArrayIndices, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inAxis
    omega

theorem ioSafe_proven : IOSafe := by
  constructor
  · intro offset ho
    simp [endianBomAccesses] at ho
    omega
  · intro io i hi
    simp only [countlinesAccesses, List.mem_flatMap, oneBasedLoop,
      List.mem_map, List.mem_range] at hi
    obtain ⟨chunk, hc, k, hk, rfl⟩ := hi
    have hlen := io.chunkLength chunk hc
    unfold inOneBased
    omega

theorem moduleSymbolSafe_proven : ModuleSymbolSafe := by
  intro storageLength h
  exact ⟨by omega, h⟩

private theorem skipspaceLoop_result_lower (s : ParsePrint.IntParse.Bytes) (j : Int) :
    ∀ (fuel : Nat) (i : Int), 1 ≤ i →
      1 ≤ ParsePrint.IntParse.skipspaceLoop s j fuel i
  | 0, _, h1 => h1
  | fuel + 1, i, h1 => by
      simp only [ParsePrint.IntParse.skipspaceLoop]
      split
      · split
        · exact skipspaceLoop_result_lower s j fuel (i + 1) (by omega)
        · split
          · rename_i hnext
            exact skipspaceLoop_result_lower s j fuel
              (ParsePrint.IntParse.skipspacechar s i) (by omega)
          · exact h1
      · exact h1

private theorem skipspace_result_lower (s : ParsePrint.IntParse.Bytes) (i j : Int)
    (h1 : 1 ≤ i) : 1 ≤ ParsePrint.IntParse.skipspace s i j := by
  exact skipspaceLoop_result_lower s j (s.length + 1) i h1

private theorem skipspaceAccessesLoop_safe (s : ParsePrint.IntParse.Bytes) (j : Int)
    (hj : j ≤ s.length) : ∀ (fuel : Nat) (i q : Int), 1 ≤ i →
      q ∈ skipspaceAccessesLoop s j fuel i → inAxis 1 s.length q
  | 0, _, q, _, hq => by simp [skipspaceAccessesLoop] at hq
  | fuel + 1, i, q, h1, hq => by
      simp only [skipspaceAccessesLoop] at hq
      split at hq
      · rename_i hij
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · unfold inAxis
          omega
        · split at hq
          · exact skipspaceAccessesLoop_safe s j hj fuel (i + 1) q
              (by omega) hq
          · split at hq
            · rename_i hnext
              exact skipspaceAccessesLoop_safe s j hj fuel
                (ParsePrint.IntParse.skipspacechar s i) q (by omega) hq
            · simp at hq
      · simp at hq

private theorem skipspaceAccesses_safe (s : ParsePrint.IntParse.Bytes) (i j q : Int)
    (h1 : 1 ≤ i) (hj : j ≤ s.length)
    (hq : q ∈ skipspaceAccesses s i j) : inAxis 1 s.length q :=
  skipspaceAccessesLoop_safe s j hj (s.length + 1) i q h1 hq

private theorem skipspacecharBack_lower (s : ParsePrint.IntParse.Bytes) (lo j : Int)
    (h : lo ≤ j) :
    lo - 1 ≤ ParsePrint.IntParse.skipspacecharBack s lo j := by
  unfold ParsePrint.IntParse.skipspacecharBack
  dsimp only
  split <;> omega

private theorem skipspaceBackAccessesLoop_safe (s : ParsePrint.IntParse.Bytes) (lo : Int)
    (hlo : 1 ≤ lo) : ∀ (fuel : Nat) (j q : Int), j ≤ s.length →
      q ∈ skipspaceBackAccessesLoop s lo fuel j → inAxis 1 s.length q
  | 0, _, q, _, hq => by simp [skipspaceBackAccessesLoop] at hq
  | fuel + 1, j, q, hj, hq => by
      simp only [skipspaceBackAccessesLoop] at hq
      split at hq
      · rename_i hji
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · unfold inAxis
          omega
        · split at hq
          · exact skipspaceBackAccessesLoop_safe s lo hlo fuel (j - 1) q (by omega) hq
          · split at hq
            · have hb := skipspacecharBack_lower s lo j hji
              exact skipspaceBackAccessesLoop_safe s lo hlo fuel
                (ParsePrint.IntParse.skipspacecharBack s lo j) q (by omega) hq
            · simp at hq
      · simp at hq

private theorem skipspaceBackAccesses_safe (s : ParsePrint.IntParse.Bytes) (lo j q : Int)
    (hlo : 1 ≤ lo) (hj : j ≤ s.length) (hq : q ∈ skipspaceBackAccesses s lo j) :
    inAxis 1 s.length q :=
  skipspaceBackAccessesLoop_safe s lo hlo (s.length + 1) j q hj hq

private theorem preambleAccesses_safe (signed : Bool) (base : Int)
    (s : ParsePrint.IntParse.Bytes) (q : Int)
    (hq : q ∈ preambleAccesses signed base s 1 s.length) : inAxis 1 s.length q := by
  have hi1 := skipspace_result_lower s 1 s.length (by omega)
  have hi2 := skipspace_result_lower s
    (ParsePrint.IntParse.skipspace s 1 s.length + 1) s.length (by omega)
  unfold preambleAccesses at hq
  dsimp only at hq
  simp only [List.mem_append] at hq
  rcases hq with (((hfirst | hsign) | hsecond) | hprefix1) | hprefix2
  · exact skipspaceAccesses_safe s 1 s.length q (by omega) (by omega) hfirst
  · split at hsign
    · simp only [List.mem_singleton] at hsign
      subst q
      unfold inAxis
      omega
    · simp at hsign
  · exact skipspaceAccesses_safe s _ s.length q (by omega) (by omega) hsecond
  · split at hprefix1
    · simp only [List.mem_cons] at hprefix1
      rcases hprefix1 with rfl | hprefix1
      · unfold inAxis
        omega
      · rcases hprefix1 with rfl | hnil
        · unfold inAxis
          omega
        · cases hnil
    · simp at hprefix1
  · split at hprefix2
    · simp only [List.mem_cons] at hprefix2
      rcases hprefix2 with rfl | hprefix2
      · unfold inAxis
        omega
      · rcases hprefix2 with rfl | hnil
        · unfold inAxis
          omega
        · cases hnil
    · simp at hprefix2

theorem integerParseSafe_proven : IntegerParseSafe := by
  intro t s base q hq
  unfold integerParseAccesses at hq
  dsimp only at hq
  simp only [List.mem_append] at hq
  rcases hq with (((((hfast | hpreamble) | hback1) | hback2) | hback3) | hback4)
  · by_cases hlen : 1 ≤ (s.length : Int)
    · by_cases htwo : 2 ≤ (s.length : Int)
      · simp [hlen, htwo] at hfast
        rcases hfast with rfl | rfl | rfl <;> unfold inAxis <;> omega
      · simp [hlen, htwo] at hfast
        rcases hfast with rfl | rfl <;> unfold inAxis <;> omega
    · simp [hlen] at hfast
  · exact preambleAccesses_safe t.signed base s q hpreamble
  all_goals
    unfold guardedParseBackReads at *
    split at *
    · rename_i hguard
      exact skipspaceBackAccesses_safe s _ s.length q hguard.1 (by omega) ‹_›
    · simp_all

theorem floatParseSafe_proven : FloatParseSafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro kind q index hi
    cases kind with
    | f64 =>
        by_cases h : q < -342 ∨ 308 < q
        · simp [pow5Access, pow10Range, h] at hi
        · simp [pow5Access, pow10Range, h] at hi
          cases hi
          unfold inOneBased
          omega
    | f32 =>
        by_cases h : q < -64 ∨ 38 < q
        · simp [pow5Access, pow10Range, h] at hi
        · simp [pow5Access, pow10Range, h] at hi
          cases hi
          unfold inOneBased
          omega
    | f16 =>
        by_cases h : q < -26 ∨ 4 < q
        · simp [pow5Access, pow10Range, h] at hi
        · simp [pow5Access, pow10Range, h] at hi
          cases hi
          unfold inOneBased
          omega
  · intro q tableLength index hi
    unfold exactPow10Access at hi
    split at hi
    · cases hi
      unfold exactPow10Index inOneBased
      split
      · constructor <;> omega
      · have hq0 : 0 ≤ q := by omega
        have ha : (q.natAbs : Int) = q := Int.natAbs_of_nonneg hq0
        have ht : (q.toNat : Int) = q := Int.toNat_of_nonneg hq0
        have heq : q.natAbs = q.toNat := by omega
        constructor <;> omega
    · contradiction
  · intro buf index hi
    simp only [floatParseByteAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega

theorem pathBufferSafe_proven : PathBufferSafe := by
  constructor
  · intro sid
    simp [sidWrapLength, sidStorageLength]
  · intro width offset hi
    cases width <;>
      simp [passwdUidOffsets, pointerBytes] at hi <;>
      omega

theorem pcreNameTableSafe_proven : PcreNameTableSafe := by
  constructor
  · intro runtime contexts
    have ht := runtime.threadId.isLt
    by_cases h : contexts.length < runtime.threadId.val + 1 <;>
      simp [matchContextLength, juliaThreadId, inOneBased, h] <;>
      omega
  · intro table i hi
    simp only [pcreNameByteIndices, List.mem_flatMap, oneBasedLoop,
      List.mem_map, List.mem_range] at hi
    obtain ⟨entry, ⟨k, hk, rfl⟩, hi⟩ := hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · unfold pcreNameStorageLength inOneBased
      simp only [Nat.succ_sub_one]
      have hs := table.headerFits
      have hnext : k + 1 ≤ table.count := by omega
      have hmul := Nat.mul_le_mul_right table.entrySize hnext
      rw [Nat.add_mul] at hmul
      omega
    · rcases hi with rfl | hi
      · unfold pcreNameStorageLength inOneBased
        simp only [Nat.succ_sub_one]
        have hs := table.headerFits
        have hnext : k + 1 ≤ table.count := by omega
        have hmul := Nat.mul_le_mul_right table.entrySize hnext
        rw [Nat.add_mul] at hmul
        omega
      · contradiction

private theorem linearArrayIndices_safe (a : LinearArray α) :
    ∀ i ∈ linearArrayIndices a, inAxis a.first a.values.length i := by
  intro i hi
  simp only [linearArrayIndices, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  unfold inAxis
  omega

private theorem linearMapreduceAccesses_subset (a : LinearArray α) :
    ∀ i ∈ linearMapreduceAccesses a, i ∈ linearArrayIndices a := by
  intro i hi
  unfold linearMapreduceAccesses at hi
  cases hinds : linearArrayIndices a with
  | nil => simp [hinds] at hi
  | cons first rest =>
      cases rest with
      | nil => simpa [hinds] using hi
      | cons second tail =>
          by_cases hshort : tail.length + 2 < 16
          · simpa [hinds, hshort] using hi
          · simp [hinds, hshort] at hi

theorem reduceSafe_proven : ReduceSafe := by
  constructor
  · intro α a i hi
    exact linearArrayIndices_safe a i (linearMapreduceAccesses_subset a i hi)
  · intro width length i hi
    simp only [boolWordAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨word, hword, rfl⟩ := hi
    have hdiv := Nat.mul_div_le length (pointerBytes width)
    have hmul := Nat.mul_le_mul_right (pointerBytes width) (Nat.succ_le_iff.mpr hword)
    calc
      (word + 1) * pointerBytes width ≤ (length / pointerBytes width) * pointerBytes width := hmul
      _ = pointerBytes width * (length / pointerBytes width) := Nat.mul_comm _ _
      _ ≤ length := hdiv

private theorem iterTrace_indices_safe (s : Strings.JStr) :
    ∀ {start trace}, Strings.IterTrace s start trace → StringUtil.Strip.VE s start →
      ∀ pair ∈ trace, inAxis 1 s.bytes.length pair.2.val
  | _, [], _, _, pair, hp => by simp at hp
  | start, pair :: rest, htrace, hv, p, hp => by
      obtain ⟨hindex, next, hstep, hrest⟩ := StringUtil.Strip.trace_cons_inv htrace
      obtain ⟨hvalid, _, hvnext⟩ := StringUtil.Strip.iter_step hv hstep
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · rw [hindex]
        unfold inAxis
        exact ⟨hvalid.1, by omega⟩
      · exact iterTrace_indices_safe s hrest hvnext p hp

theorem stringPositionSafe_proven : StringPositionSafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i hi
    simp only [stringCharacterAccesses, List.mem_map] at hi
    obtain ⟨pair, hp, rfl⟩ := hi
    exact iterTrace_indices_safe s (StringUtil.Strip.collect_trace s)
      (StringUtil.Strip.ve_one s) pair hp
  · intro s i hi
    unfold chompCodeunitAccesses at hi
    dsimp only at hi
    split at hi
    · simp at hi
    · rename_i hn
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with rfl | hi
      · unfold inOneBased
        omega
      · split at hi
        · simp only [List.mem_singleton] at hi
          subst i
          unfold inOneBased
          omega
        · simp at hi
  · intro s i hi
    simp only [stringSubstringBoundaries, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    omega

private theorem hexDigitIndices_safe : ∀ x : UInt8,
    inOneBased StringUtil.hexChars.length (x.toNat / 16 + 1) ∧
    inOneBased StringUtil.hexChars.length (x.toNat % 16 + 1) := by
  intro x
  have hx := UInt8.toNat_lt x
  simp only [StringUtil.hexChars, List.length_cons, List.length_nil, Nat.reduceAdd]
  constructor <;> unfold inOneBased <;> omega

theorem stringHexSafe_proven : StringHexSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro dest i hi
    simp only [hex2bytesDestIndices, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega
  · intro bytes i hi
    simp only [bytes2hexOutputIndices, List.mem_flatMap, oneBasedLoop,
      List.mem_map, List.mem_range, List.mem_cons] at hi
    obtain ⟨entry, ⟨k, hk, rfl⟩, hi⟩ := hi
    rcases hi with rfl | hi
    · unfold inOneBased
      omega
    · rcases hi with rfl | hi
      · unfold inOneBased
        omega
      · contradiction
  · intro bytes i hi
    simp only [bytes2hexDigitIndices, List.mem_flatMap, List.mem_cons] at hi
    obtain ⟨x, _, hi⟩ := hi
    rcases hi with rfl | hi
    · exact (hexDigitIndices_safe x).1
    · rcases hi with rfl | hi
      · exact (hexDigitIndices_safe x).2
      · contradiction
  · intro s i hi
    simp only [asciiCodeunitIndices, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega

private theorem asciiCategoryBound :
    ∀ k : Fin 128, Show.asciiCats.getD k.val 0 ≤ 30 := by
  decide +kernel

theorem unicodeCategorySafe_proven : UnicodeCategorySafe := by
  intro d c
  unfold categoryStringIndex inOneBased Show.categoryCode
  split
  · omega
  · split
    · rename_i u hcp
      split
      · unfold Show.utf8procCategory
        split
        · rename_i hu
          have hk : u.toNat < 128 := by
            simpa using UInt32.lt_iff_toNat_lt.mp hu
          have hb : Show.asciiCats.getD u.toNat 0 ≤ 30 := by
            simpa using asciiCategoryBound ⟨u.toNat, hk⟩
          omega
        · constructor
          · omega
          · simp [CategoryData.toUData]
      · omega
    · omega

theorem timingGlobalsSafe_proven : TimingGlobalsSafe := by
  constructor
  · decide
  constructor
  · decide
  · intro i hi
    simp only [oneBasedLoop, fullSweepReasonNames, List.length_cons,
      List.length_nil, Nat.reduceAdd, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp [inOneBased, fullSweepReasonStorage]
    omega

end JuliaLean.MemSafety.G3

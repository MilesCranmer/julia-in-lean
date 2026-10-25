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

theorem abstractArrayCopySafe_proven : AbstractArrayCopySafe := by
  intro destFirst srcFirst destLen srcLen start count k hd hs hk
  constructor <;> unfold inAxis <;> omega

theorem abstractArrayConcatSafe_proven : AbstractArrayConcatSafe := by
  intro dims coords h
  have hb := linearOffset_lt_product dims coords h
  unfold inOneBased
  omega

theorem abstractArrayIterationSafe_proven : AbstractArrayIterationSafe := by
  intro first len sourceOffset destOffset hs hd
  constructor <;> unfold inAxis <;> omega

theorem deepcopyMemorySafe_proven : DeepcopyMemorySafe := by
  intro len i h1 h2
  exact ⟨h1, h2⟩

theorem dictProbeSafe_proven : DictProbeSafe := by
  intro size index hash hp hs h1 h2
  have hh := Dicts.hashindex_range hp hash
  have hn := Dicts.nextIdx_range hp h1 h2
  have hv := (Dicts.nextIdx_prevIdx hp (by omega) h1 h2).2
  exact ⟨hh, hn, hv⟩

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

theorem environmentBufferSafe_proven : EnvironmentBufferSafe := by
  intro storageLength position payloadLength hp hl
  omega

theorem integerFormattingSafe_proven : IntegerFormattingSafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro bufferLength i hi
    constructor
    · intro h4
      repeat' apply And.intro
      all_goals omega
    · intro h1
      exact ⟨h1, hi⟩
  · intro c hc
    exact ⟨by omega, by omega⟩
  · intro d hd
    exact ⟨by omega, by omega⟩

theorem ioSafe_proven : IOSafe := by
  intro bufferLength bytesRead i hb h1 h2
  exact ⟨h1, by omega⟩

theorem moduleSymbolSafe_proven : ModuleSymbolSafe := by
  intro storageLength h
  exact ⟨by omega, h⟩

theorem integerParseSafe_proven : IntegerParseSafe := by
  intro length i j h1 hij hj
  refine ⟨⟨h1, by omega⟩, ⟨by omega, hj⟩, ?_⟩
  intro hlt
  exact ⟨by omega, by omega⟩

theorem floatParseSafe_proven : FloatParseSafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro length i j h1 hij hj
    refine ⟨⟨h1, by omega⟩, ⟨by omega, hj⟩, ?_⟩
    intro h7
    omega
  · intro q h1 h2
    omega
  · intro q tableLength hq
    unfold exactPow10Index inOneBased
    split
    · constructor <;> omega
    · have hq0 : 0 ≤ q := by omega
      have ha : (q.natAbs : Int) = q := Int.natAbs_of_nonneg hq0
      have ht : (q.toNat : Int) = q := Int.toNat_of_nonneg hq0
      have heq : q.natAbs = q.toNat := by omega
      constructor <;> omega

theorem pathBufferSafe_proven : PathBufferSafe := by
  intro storageLength offset width h
  omega

theorem pcreNameTableSafe_proven : PcreNameTableSafe := by
  intro count entrySize entry currentLength threadId maxThreadId hs he ht hp
  dsimp
  have hnext : entry + 1 ≤ count := by omega
  have hmul := Nat.mul_le_mul_right entrySize hnext
  have hpos : 0 < entrySize := by omega
  refine ⟨?_, ?_, ?_⟩
  · have : entry * entrySize < (entry + 1) * entrySize :=
      Nat.mul_lt_mul_of_pos_right (by omega) hpos
    omega
  · have htwo : entry * entrySize + 2 ≤ (entry + 1) * entrySize := by
      rw [Nat.add_mul]
      simp only [Nat.one_mul]
      omega
    omega
  · split <;> omega

theorem reduceSafe_proven : ReduceSafe := by
  intro length wordSize word index hw hword hi1 hi2
  have hdiv := Nat.mul_div_le length wordSize
  have hmul := Nat.mul_le_mul_right wordSize (Nat.succ_le_iff.mpr hword)
  constructor
  · calc
      (word + 1) * wordSize ≤ (length / wordSize) * wordSize := hmul
      _ = wordSize * (length / wordSize) := Nat.mul_comm _ _
      _ ≤ length := hdiv
  · exact ⟨hi1, hi2⟩

theorem stringPositionSafe_proven : StringPositionSafe := by
  intro codeunits position h
  exact ⟨by omega, by omega⟩

theorem stringHexSafe_proven : StringHexSafe := by
  intro length i h1 h2
  refine ⟨?_, ?_, ⟨h1, h2⟩⟩ <;> unfold inOneBased <;> omega

theorem unicodeCategorySafe_proven : UnicodeCategorySafe := by
  intro code h
  exact ⟨by omega, by omega⟩

theorem timingGlobalsSafe_proven : TimingGlobalsSafe := by
  intro globalLength exposedLength i he h1 h2
  exact ⟨h1, by omega⟩

end JuliaLean.MemSafety.G3

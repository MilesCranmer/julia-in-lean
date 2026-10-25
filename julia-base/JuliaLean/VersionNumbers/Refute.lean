import JuliaLean.VersionNumbers.Props

/-!
# Refuted `VersionNumber` properties
-/

namespace JuliaLean.VersionNumbers

open JuliaLean

/-- `"4294967296"`. -/
def bigMajor : List Char := ['4', '2', '9', '4', '9', '6', '7', '2', '9', '6']

theorem tryparse_bigMajor : tryparse bigMajor = .error (.overflowError "overflow parsing") := by decide +kernel

/-- `"١"` (U+0661, ARABIC-INDIC DIGIT ONE). -/
theorem tryparse_arabicDigit :
    tryparse [Char.ofNat 0x661] = .error (.argumentError "invalid base 10 digit") := by decide +kernel

theorem tryparseNothrow_refuted : ¬ TryparseNothrow := by
  intro h
  obtain ⟨r, hr⟩ := h bigMajor
  rw [tryparse_bigMajor] at hr
  cases hr

/-- `VersionNumber(1, 0, 0, ("a\n",))`. -/
def newlineVersion : VersionNumber := ⟨u32 1, u32 0, u32 0, [.str ['a', '\n']], []⟩

theorem newlineVersion_constructible : Constructible newlineVersion := by
  unfold Constructible; decide +kernel

theorem newlineVersion_print : vprint newlineVersion = ['1', '.', '0', '.', '0', '-', 'a', '\n'] := by decide +kernel

theorem newlineVersion_reparse :
    parse (vprint newlineVersion) = .ok ⟨u32 1, u32 0, u32 0, [.str ['a']], []⟩ := by decide +kernel

theorem printParseRoundtrip_refuted : ¬ PrintParseRoundtrip := by
  intro h
  obtain ⟨w, hw, heq⟩ := h newlineVersion newlineVersion_constructible
  rw [newlineVersion_reparse] at hw
  cases hw
  revert heq
  decide

/-- `"1-ſ"` (U+017F, LATIN SMALL LETTER LONG S). -/
def longSVersion : List Char := ['1', '-', Char.ofNat 0x17F]

theorem tryparse_longS :
    tryparse longSVersion = .ok (some ⟨u32 1, u32 0, u32 0, [.str [Char.ofNat 0x17F]], []⟩) := by decide +kernel

theorem parseIdentCharset_refuted : ¬ ParseIdentCharset := by
  intro h
  have := h _ _ tryparse_longS
  revert this
  decide

/-- `-1 :: Int`. -/
def minusOne : JInt .i64 := JInt.wrap .i64 (-1)

theorem versionNumber_minusOne :
    versionNumber minusOne (JInt.wrap .i64 0) (JInt.wrap .i64 0) [] [] = .error (.inexactError "UInt32") := by
  decide +kernel

theorem negativeArgumentError_refuted : ¬ NegativeArgumentError := by
  intro h
  obtain ⟨msg, hm⟩ := h minusOne (JInt.wrap .i64 0) (JInt.wrap .i64 0) [] [] (Or.inl (by decide))
  rw [versionNumber_minusOne] at hm
  cases hm

end JuliaLean.VersionNumbers

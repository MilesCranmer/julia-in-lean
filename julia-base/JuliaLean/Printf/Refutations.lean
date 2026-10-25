import JuliaLean.Printf.Props

/-!
Counterexamples to the refuted Printf properties. Each instance is the one the
reproducer `repro/<id>.jl` runs (or, for `BigFloat`, a value with the same output
length), evaluated by `decide` on the model.
-/

namespace JuliaLean.Printf

open JuliaLean JuliaLean.Float

/-- `你`: three UTF-8 code units, `textwidth` 2. -/
def glyphNi : Glyph := ⟨[0xE4, 0xBD, 0xA0], 2⟩

/-- `Format("%1")` throws `BoundsError`. -/
theorem formatErrorsAreInvalidFormat_refuted : ¬ FormatErrorsAreInvalidFormat := by
  intro h
  exact absurd (h [37, 49] (.julia .boundsError) (by decide +kernel)) (by decide +kernel)

/-- `Format("%D")` succeeds, and `plength` has no method for `Spec{Val{'D'}}`. -/
theorem acceptedHaveMethods_refuted : ¬ AcceptedHaveMethods := by
  intro h
  have hp : parseBytes [37, 68] = .ok ⟨[[], []], [{conv := 68}], 1⟩ := by decide +kernel
  exact h _ _ hp {conv := 68} (by simp) (iarg 1) (by decide +kernel)

/-- `@sprintf("%.0d", UInt32(0)) == "0"`. -/
theorem integerZeroPrecision_refuted : ¬ IntegerZeroPrecision := by
  intro h
  exact absurd (h cd .u32 (JInt.lit .u32 0) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- `@sprintf("%05.0d", Int32(3)) == "00003"`, `@sprintf("%5.0d", Int32(3)) == "    3"`. -/
theorem zeroFlagPrecision_refuted : ¬ ZeroFlagPrecision := by
  intro h
  exact absurd (h 5 0 .i32 (JInt.lit .i32 3)) (by decide +kernel)

/-- `@sprintf("%#.5o", UInt32(1)) == "000001"`; C99 gives `"00001"`. -/
theorem octalHashPrecision_refuted : ¬ OctalHashPrecision := by
  intro h
  exact absurd (h 5 .u32 (JInt.lit .u32 1) (by decide +kernel)) (by decide +kernel)

/-- `@sprintf("%#x", UInt32(0)) == "0x0"`. -/
theorem hexZeroPrefix_refuted : ¬ HexZeroPrefix := by
  intro h
  exact absurd (h cx .u32 (JInt.lit .u32 0) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- `@sprintf("%+x", 42) == "+2a"`. -/
theorem plusUnsigned_refuted : ¬ PlusUnsigned := by
  intro h
  exact absurd (h cx plusC .i64 (ix 42) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- `@sprintf("%*d", -5, 42) == "42"`, `@sprintf("%-5d", 42) == "42   "`. -/
theorem negativeWidth_refuted : ¬ NegativeWidth := by
  intro h
  exact absurd (h 5 .i64 (ix 42) (by decide +kernel)) (by decide +kernel)

/-- `@sprintf("%.*s", -2, "hello")` throws `BoundsError`. -/
theorem negativePrecision_refuted : ¬ NegativePrecision := by
  intro h
  exact absurd (h (-2) [104, 101, 108, 108, 111] (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- `@sprintf("%.*d", -6, 42)` stores the digits past the end of a one-byte buffer. -/
theorem intDigitsInBounds_refuted : ¬ IntDigitsInBounds := by
  intro h
  exact h cd (-6) .i64 (ix 42) (by decide +kernel) (by decide +kernel)

/-- `@sprintf("%5.1s", "你")` is four spaces: neither five spaces nor `"   你"`. -/
theorem stringFieldWidth_refuted : ¬ StringFieldWidth := by
  intro h
  obtain ⟨k, hk⟩ := h 5 1 [glyphNi]
  cases k with
  | zero => exact absurd hk (by decide +kernel)
  | succ k =>
    simp only [List.take_succ_cons, List.take_nil] at hk
    exact absurd hk (by decide +kernel)

/-- `@sprintf("%.3g", 999.5) == "1000"`; C99 gives `"1e+03"`. -/
theorem generalStyle_refuted : ¬ GeneralStyle := by
  intro h
  exact absurd (h 3 (F64.ofBits 0x408f3c0000000000) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- `@sprintf("%#a", 0.0) == "0x0p+0"`, without a decimal point. -/
theorem hexZeroHash_refuted : ¬ HexZeroHash := by
  intro h
  exact absurd (h (F64.ofBits 0) (by decide +kernel)) (by decide +kernel)

/-- `@sprintf("%.0f", 0.5) == "0"`; away from zero gives `"1"`. -/
theorem tiesAway_refuted : ¬ TiesAway := by
  intro h
  exact absurd (h 0 (F64.ofBits 0x3fe0000000000000) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- 100 bytes of text, then `%f` of a `BigFloat` with 401 integer digits:
`mpfr_snprintf` writes 409 bytes from position 101 into a 409-byte buffer. -/
theorem bigFloatInBounds_refuted : ¬ BigFloatInBounds := by
  intro h
  exact h (List.replicate 100 97) false (10 ^ 400) 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `@sprintf("%320f", big"2.0")` ends in NUL. -/
theorem bigFloatWidth_refuted : ¬ BigFloatWidth := by
  intro h
  exact absurd (h 320 false 2 1 (by decide +kernel)) (by decide +kernel)

end JuliaLean.Printf

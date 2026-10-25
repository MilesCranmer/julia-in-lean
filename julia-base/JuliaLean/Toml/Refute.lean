import JuliaLean.Toml.Props

/-!
# Refuted TOML properties

Each refutation evaluates the parser model on the reproducer's document
(`repro/toml-*.jl`) by kernel reduction.
-/

namespace JuliaLean.Toml

theorem tryparseNoTypeError_refuted : ¬ TryparseNoTypeError := by
  intro h
  exact h (bytes% "a = 1\n[[a.b]]") (by decide +kernel)

theorem tryparseNoArgumentError_refuted : ¬ TryparseNoArgumentError := by
  intro h
  exact h (bytes% "a = 0o8") "invalid base digit" (by decide +kernel)

theorem baseParserNoThrow_refuted : ¬ BaseParserNoThrow := by
  intro h
  obtain ⟨t, ht⟩ := h (bytes% "a = [1979-05-27, 1979-05-28]") (.errorException "unexpected type")
    (by decide +kernel)
  cases ht

theorem inlineTableClosed_refuted : ¬ InlineTableClosed := by
  intro h
  have := h (bytes% "a") (bytes% "b") (by decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

theorem noHexFloat_refuted : ¬ NoHexFloat := by
  intro h
  have := h (bytes% "5") (by decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

theorem dateTimeUnsigned_refuted : ¬ DateTimeUnsigned := by
  intro h
  have := h.1 45 50 48 48 (Or.inr rfl) rfl rfl rfl
  revert this
  decide +kernel

theorem noTableOverwrite_refuted : ¬ NoTableOverwrite := by
  intro h
  have := h (bytes% "a") (bytes% "b") (bytes% "c") (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 49 rfl
  revert this
  decide +kernel

theorem singleLineNoContinuation_refuted : ¬ SingleLineNoContinuation := by
  intro h
  have := h (bytes% "x") (bytes% "y") (by decide +kernel)
  revert this
  decide +kernel

theorem controlCharsRejected_refuted : ¬ ControlCharsRejected := by
  intro h
  have := h 1 (Or.inl (by decide))
  revert this
  decide +kernel

theorem invalidUtf8Rejected_refuted : ¬ InvalidUtf8Rejected := by
  intro h
  have := h 0xFF (by decide) (by decide)
  revert this
  decide +kernel

theorem hexEscapeCodepoint_refuted : ¬ HexEscapeCodepoint := by
  intro h
  have := h 69 57 rfl rfl
  revert this
  decide +kernel

theorem multilineQuotesBeforeDelimiter_refuted : ¬ MultilineQuotesBeforeDelimiter := by
  intro h
  have := h (bytes% "q") (by decide +kernel)
  revert this
  decide +kernel

theorem continuationTrailingWhitespace_refuted : ¬ ContinuationTrailingWhitespace := by
  intro h
  have := h 2 (by decide)
  revert this
  decide +kernel

theorem floatUnderscoreExponent_refuted : ¬ FloatUnderscoreExponent := by
  intro h
  have := h 49 48 50 ⟨by decide, by decide⟩ rfl rfl
  revert this
  decide +kernel

/-- `0o2000000000000000000000` (`2^64`) and `0o20000000000000000000000` (`2^67`). -/
theorem octalAcceptanceMonotone_refuted : ¬ OctalAcceptanceMonotone := by
  intro h
  have := h (50 :: List.replicate 21 48) (50 :: List.replicate 22 48) (by simp) (by simp)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

theorem offsetDateTimeAccepted_refuted : ¬ OffsetDateTimeAccepted := by
  intro h
  have := h 45 48 55 48 48 (Or.inr rfl) ⟨by decide, by decide⟩ rfl ⟨by decide, by decide⟩ rfl
  revert this
  decide +kernel

theorem decimalInt64Typed_refuted : ¬ DecimalInt64Typed := by
  intro h
  have := h 1700000000000000000 (by decide)
  revert this
  decide +kernel

theorem bomSkipped_refuted : ¬ BomSkipped := by
  intro h
  have := h (bytes% "a = 1")
  revert this
  decide +kernel

end JuliaLean.Toml

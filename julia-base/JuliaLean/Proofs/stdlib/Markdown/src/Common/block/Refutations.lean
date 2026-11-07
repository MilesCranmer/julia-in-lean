import JuliaLean.Proofs.stdlib.Markdown.src.Common.block.Claims

namespace JuliaLean.Markdown

private def noWord : Nat → Bool := fun _ => false

theorem hashheaderTotal_refuted : ¬ HashheaderTotal := by
  intro h
  have := h Unit (fun _ => ()) (bytes% "#\r")
  revert this
  decide +kernel

/-- `Markdown.parse("a\r", flavor = :github)`. -/

theorem listNoOverflow_refuted : ¬ ListNoOverflow := by
  intro h
  have := h (fun _ => ()) (bytes% "12345678901234567890. item")
  revert this
  decide +kernel

/-- `Markdown.parse("۱. item")` (Persian digit one, a Unicode `\d`). -/
theorem listNoArgumentError_refuted : ¬ ListNoArgumentError := by
  intro h
  have := h (fun _ => ()) (bytes% "۱. item")
  revert this
  decide +kernel

/-- `Markdown.parse("- a\n- b\n\nText")` gives a loose list. -/
theorem listTrailingBlankTight_refuted : ¬ ListTrailingBlankTight := by
  intro h
  have := h [bytes% "a", bytes% "b"] (bytes% "Text") (by decide) (by decide) (by decide)
  revert this
  decide +kernel

/- `plain` of the loose list of `"- a\n\n- b"` prints no blank line between the items. -/

end JuliaLean.Markdown

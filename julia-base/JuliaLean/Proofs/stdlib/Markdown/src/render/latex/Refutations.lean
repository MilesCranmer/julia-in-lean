import JuliaLean.Proofs.stdlib.Markdown.src.render.latex.Claims

namespace JuliaLean.Markdown

private def noWord : Nat → Bool := fun _ => false

theorem latexTotal_refuted : ¬ LatexTotal := by
  intro h
  have := h id [.para [.text (bytes% "The answer is "), .value (bytes% "42"), .text (bytes% ".")]]
  revert this
  decide +kernel

/-- `Markdown.parse("![alt text](image.png)")`. -/

theorem latexHeaderCommands_refuted : ¬ LatexHeaderCommands := by
  intro h
  have := h id 6 [.text (bytes% "Title")] (by decide) (by decide)
  revert this
  decide +kernel

/-- `!!! note "50% of x_1"`: the title is printed without `latexesc`. -/
theorem latexTextEscaped_refuted : ¬ LatexTextEscaped := by
  intro h
  have := h id (bytes% "note") (bytes% "50% of x_1")
  revert this
  decide +kernel

end JuliaLean.Markdown

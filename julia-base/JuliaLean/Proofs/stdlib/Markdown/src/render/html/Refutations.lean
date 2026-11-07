import JuliaLean.Proofs.stdlib.Markdown.src.render.html.Claims

namespace JuliaLean.Markdown

private def noWord : Nat → Bool := fun _ => false

theorem htmlTextEscaped_refuted : ¬ HtmlTextEscaped := by
  intro h
  have := h id [.admonition (bytes% "warning") (bytes% "x < y & <script>alert(1)</script>")
    [.para [.text (bytes% "Body.")]]] (by decide +kernel)
  revert this
  decide +kernel

/-- `Markdown.parse("0. zero\n1. one")` renders as a bare `<ol>`. -/
theorem htmlOrderedStart_refuted : ¬ HtmlOrderedStart := by
  intro h
  have := h id [[.para [.text (bytes% "zero")]], [.para [.text (bytes% "one")]]] 0 false (by decide)
  revert this
  decide +kernel

/- The text `*not emphasis*` (from `\*not emphasis\*`) is printed as italic markup. -/

end JuliaLean.Markdown

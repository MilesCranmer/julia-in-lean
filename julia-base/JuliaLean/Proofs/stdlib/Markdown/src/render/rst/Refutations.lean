import JuliaLean.Proofs.stdlib.Markdown.src.render.rst.Claims

namespace JuliaLean.Markdown

private def noWord : Nat → Bool := fun _ => false

theorem rstTotal_refuted : ¬ RstTotal := by
  intro h
  have := h id [.para [.image (bytes% "image.png") (bytes% "alt text")]]
  revert this
  decide +kernel

/- `Markdown.parse("###### Title")` becomes `\subsubparagraph{Title}`. -/

end JuliaLean.Markdown

import JuliaLean.Proofs.stdlib.Markdown.src.render.plain.Claims

namespace JuliaLean.Markdown

private def noWord : Nat → Bool := fun _ => false

theorem plainLooseList_refuted : ¬ PlainLooseList := by
  intro h
  have := h [bytes% "a", bytes% "b"] (by decide) (by decide)
  revert this
  decide +kernel

/-- An admonition titled `x < y & <script>alert(1)</script>`. -/

theorem plainTextRoundtrip_refuted : ¬ PlainTextRoundtrip := by
  intro h
  have := h noWord (bytes% "*not emphasis*")
  revert this
  decide +kernel

/-- The display equation `x^2` is printed as `$$\nx^2\n$$`, which neither `blocktex` nor
`fencedcode` accepts. -/
theorem plainDisplayMath_refuted : ¬ PlainDisplayMath := by
  intro h
  have := h noWord (bytes% "x^2") (by decide)
  revert this
  decide +kernel

/-- `Markdown.parse("$x$ is positive")`: `blocktex` takes `$x$` and leaves ` is positive`. -/

theorem plainCodeSpan_refuted : ¬ PlainCodeSpan := by
  intro h
  have := h [] (by decide) (by decide)
  revert this
  decide +kernel

/- `md"The answer is $x."` with `x = 42`. -/

end JuliaLean.Markdown

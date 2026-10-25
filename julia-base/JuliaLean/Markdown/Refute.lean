import JuliaLean.Markdown.Props

/-!
# Markdown: refuted properties

Each refutation evaluates the model on the input of the reproducer
`repro/markdown-*.jl` by kernel reduction.
-/

namespace JuliaLean.Markdown

/-- `isword` is not consulted by the `*` and `$` readers; any function works. -/
private def noWord : Nat → Bool := fun _ => false

/-- `Markdown.parse("#\r")`: `peek` past the end after the carriage return. -/
theorem hashheaderTotal_refuted : ¬ HashheaderTotal := by
  intro h
  have := h Unit (fun _ => ()) (bytes% "#\r")
  revert this
  decide +kernel

/-- `Markdown.parse("a\r", flavor = :github)`. -/
theorem githubParagraphTotal_refuted : ¬ GithubParagraphTotal := by
  intro h
  have := h (pure false) (fun _ => ()) (fun st => ⟨(false, st), rfl⟩) (bytes% "a\r")
  revert this
  decide +kernel

/-- `Markdown.parse("12345678901234567890. item")`. -/
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

/-- `plain` of the loose list of `"- a\n\n- b"` prints no blank line between the items. -/
theorem plainLooseList_refuted : ¬ PlainLooseList := by
  intro h
  have := h [bytes% "a", bytes% "b"] (by decide) (by decide)
  revert this
  decide +kernel

/-- An admonition titled `x < y & <script>alert(1)</script>`. -/
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

/-- The text `*not emphasis*` (from `\*not emphasis\*`) is printed as italic markup. -/
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
theorem blocktexInlineDollar_refuted : ¬ BlocktexInlineDollar := by
  intro h
  have := h noWord (bytes% "$x$ is positive")
  revert this
  decide +kernel

/-- The empty code span of ``"a ` ` b"`` is printed as two backticks. -/
theorem plainCodeSpan_refuted : ¬ PlainCodeSpan := by
  intro h
  have := h [] (by decide) (by decide)
  revert this
  decide +kernel

/-- `md"The answer is $x."` with `x = 42`. -/
theorem latexTotal_refuted : ¬ LatexTotal := by
  intro h
  have := h id [.para [.text (bytes% "The answer is "), .value (bytes% "42"), .text (bytes% ".")]]
  revert this
  decide +kernel

/-- `Markdown.parse("![alt text](image.png)")`. -/
theorem rstTotal_refuted : ¬ RstTotal := by
  intro h
  have := h id [.para [.image (bytes% "image.png") (bytes% "alt text")]]
  revert this
  decide +kernel

/-- `Markdown.parse("###### Title")` becomes `\subsubparagraph{Title}`. -/
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

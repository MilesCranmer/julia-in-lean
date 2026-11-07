import JuliaLean.Proofs.stdlib.Markdown.src.IPython.IPython.Claims

namespace JuliaLean.Markdown

private def noWord : Nat → Bool := fun _ => false

theorem blocktexInlineDollar_refuted : ¬ BlocktexInlineDollar := by
  intro h
  have := h noWord (bytes% "$x$ is positive")
  revert this
  decide +kernel

/- The empty code span of ``"a ` ` b"`` is printed as two backticks. -/

end JuliaLean.Markdown

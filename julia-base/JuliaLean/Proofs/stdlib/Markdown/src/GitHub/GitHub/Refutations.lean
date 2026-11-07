import JuliaLean.Proofs.stdlib.Markdown.src.GitHub.GitHub.Claims

namespace JuliaLean.Markdown

private def noWord : Nat → Bool := fun _ => false

theorem githubParagraphTotal_refuted : ¬ GithubParagraphTotal := by
  intro h
  have := h (pure false) (fun _ => ()) (fun st => ⟨(false, st), rfl⟩) (bytes% "a\r")
  revert this
  decide +kernel

/- `Markdown.parse("12345678901234567890. item")`. -/

end JuliaLean.Markdown

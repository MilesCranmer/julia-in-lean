import JuliaLean.Proofs.stdlib.Markdown.src.Support

namespace JuliaLean.Markdown

def GithubParagraphTotal : Prop :=
  ∀ (brk : M Bool) (inl : Bytes → Unit),
    (∀ st, ∃ r, brk.run st = .ok r) →
    ∀ s, throwsJl (runOn (githubParagraph brk (fun b => .ok (inl b))) s) = false

/- `list` throws no `OverflowError` on any input, given a nested parser that does not throw. -/

end JuliaLean.Markdown

import JuliaLean.Proofs.stdlib.Markdown.src.Support

namespace JuliaLean.Markdown

def RstTotal : Prop :=
  ∀ (styled : Bytes → Bytes) (md : List Block), isMethodError (rst styled md) = false

/- Standard LaTeX sectioning commands. -/

end JuliaLean.Markdown

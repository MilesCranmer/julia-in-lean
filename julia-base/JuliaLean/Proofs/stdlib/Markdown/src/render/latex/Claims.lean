import JuliaLean.Proofs.stdlib.Markdown.src.Support

namespace JuliaLean.Markdown

def LatexTotal : Prop :=
  ∀ (styled : Bytes → Bytes) (md : List Block), isMethodError (latex styled md) = false

/-- `rst` has a method for every node the parser produces. -/

def LatexHeaderCommands : Prop :=
  ∀ (styled : Bytes → Bytes) (l : Nat) (xs : List Inline), 1 ≤ l → l ≤ 6 →
    (match latex styled [.header l xs] with
     | .ok out => latexSections.any fun c => ([92] ++ c ++ [123]).isPrefixOf out
     | .error _ => true) = true

/-- `latex` escapes the text of admonition titles like other text (`latexesc`). -/
def LatexTextEscaped : Prop :=
  ∀ (styled : Bytes → Bytes) (cat title : Bytes),
    (match latex styled [.admonition cat title []] with
     | .ok out => occursIn (latexesc title) out
     | .error _ => true) = true

end JuliaLean.Markdown

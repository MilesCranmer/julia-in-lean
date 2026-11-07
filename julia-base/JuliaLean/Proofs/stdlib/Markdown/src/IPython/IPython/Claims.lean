import JuliaLean.Proofs.stdlib.Markdown.src.Support

namespace JuliaLean.Markdown

def BlocktexInlineDollar : Prop :=
  ∀ (isword : Nat → Bool) (s : Bytes),
    (match runOn (blocktex isword) s with
     | .ok (some _, st) => ((st.data.drop st.pos).takeWhile (· != 10)).all isWhitespace
     | _ => true) = true

/- `inline_code` reads `plain` of an inline code node back as the same code, for every code
text the parser can produce (stripped, without newlines). -/

end JuliaLean.Markdown

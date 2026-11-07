import JuliaLean.Proofs.stdlib.Markdown.src.Support

namespace JuliaLean.Markdown

def PlainLooseList : Prop :=
  ∀ (xs : List Bytes), 2 ≤ xs.length → (∀ x ∈ xs, isLetters x = true) →
    listLoose (plain [.list (xs.map fun x => [.para [.text x]]) (-1) true]) = true

/-! ## HTML escaping -/

/-- Tag names printed by the HTML model. -/

def PlainTextRoundtrip : Prop :=
  ∀ (isword : Nat → Bool) (t : Bytes),
    (match runOn (asteriskItalic isword) (plain [.para [.text t]]) with
     | .ok (none, _) => true
     | _ => false) = true

/-- The block readers that produce a display equation (`blocktex` and `fencedcode`) read
`plain` of a display equation back as the same formula. -/
def PlainDisplayMath : Prop :=
  ∀ (isword : Nat → Bool) (f : Bytes), ¬ 10 ∈ f →
    let p := plain [.latex f]
    ((match runOn (blocktex isword) p with | .ok (some g, _) => g == f | _ => false) ||
     (match runOn fencedcode p with | .ok (some (.latex g), _) => g == f | _ => false)) = true

/-- When `blocktex` accepts, the formula is the whole rest of the line; otherwise the
paragraph that started with inline math is cut in two. -/

def PlainCodeSpan : Prop :=
  ∀ (c : Bytes), strip c = c → ¬ 10 ∈ c →
    (match runOn inlineCode (plainInline (.code [] c)) with
     | .ok (some (.code l c'), _) => l.isEmpty && c' == c
     | _ => false) = true

/-! ## LaTeX and reStructuredText printers -/

/- `latex` has a method for every node the parser produces. -/

end JuliaLean.Markdown

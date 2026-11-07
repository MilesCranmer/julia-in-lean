import JuliaLean.Proofs.stdlib.Markdown.src.Support

namespace JuliaLean.Markdown

def HtmlTextEscaped : Prop :=
  ∀ (styled : Bytes → Bytes) (md : List Block), blocksOk false md = true →
    tagSafe (html styled md) = true

/-- The admonition title is the only unescaped document text of `html`: when admonition titles
contain no `<` either, every `<` of the output starts one of the printer's own tags. -/
def HtmlTagSafeTitles : Prop :=
  ∀ (styled : Bytes → Bytes) (md : List Block), blocksOk true md = true →
    tagSafe (html styled md) = true

/-- Decoding of the four entities that `htmlesc` writes (`&lt;`, `&gt;`, `&quot;`, `&amp;`). -/

def HtmlescSound : Prop :=
  ∀ s : Bytes, 60 ∉ htmlesc s ∧ 62 ∉ htmlesc s ∧ 34 ∉ htmlesc s ∧ htmlUnescape (htmlesc s) = s

/-- `html` of an ordered list shows its start number: `<ol start="k">`, or `<ol>` when `k = 1`. -/
def HtmlOrderedStart : Prop :=
  ∀ (styled : Bytes → Bytes) (items : List (List Block)) (k : Int) (loose : Bool), 0 ≤ k →
    let out := html styled [.list items k loose]
    (bytes% "<ol start=\"" ++ intString k ++ bytes% "\">").isPrefixOf out ||
      (k == 1 && (bytes% "<ol>").isPrefixOf out)

/-! ## `plain` output reparses -/

/- The `*` reader that `parseinline` tries at the start of a paragraph (`asterisk_italic`)
declines on `plain` of a paragraph whose only element is a text node. -/

end JuliaLean.Markdown

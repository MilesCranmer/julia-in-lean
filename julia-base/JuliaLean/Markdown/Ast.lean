import JuliaLean.Markdown.Stream

/-!
# Markdown: document tree

The element types of `stdlib/Markdown/src` (master `bbfa0ce4150`) that the
parser produces, as one inductive per level. `MD.content` is a `List Block`;
inline content (`Paragraph.content`, `Header.text`, ...) is a `List Inline`.
Strings are byte lists (`Bytes`).

`value` stands for an interpolated Julia object (`md"$x"`, `Julia/interp.jl`);
`repr` is its `show(io, MIME"text/plain"(), x)` output, which the HTML printer
uses through `tohtml` (`render/rich.jl:7-9`) when the object has no richer
`show` method. `Table` is not modelled.
-/

namespace JuliaLean.Markdown

inductive Inline where
  /-- A `String` element. -/
  | text (s : Bytes)
  /-- `Code(language, code)` in inline position. -/
  | code (lang code : Bytes)
  /-- `LaTeX(formula)` in inline position. -/
  | latex (f : Bytes)
  | bold (xs : List Inline)
  | italic (xs : List Inline)
  | strike (xs : List Inline)
  | link (xs : List Inline) (url : Bytes)
  | image (url alt : Bytes)
  /-- `Footnote(id, nothing)`: a footnote reference. -/
  | footnoteRef (id : Bytes)
  | lineBreak
  | htmlInline (s : Bytes)
  | value (repr : Bytes)
  deriving Repr, Inhabited

inductive Block where
  | para (xs : List Inline)
  /-- `Header{level}(text)`. -/
  | header (level : Nat) (xs : List Inline)
  | code (lang code : Bytes)
  /-- A block-level `LaTeX(formula)` (display equation). -/
  | latex (f : Bytes)
  | quote (bs : List Block)
  /-- `List(items, ordered, loose)`: `ordered = -1` is unordered, `≥ 0` the start number. -/
  | list (items : List (List Block)) (ordered : Int) (loose : Bool)
  | hr
  | admonition (category title : Bytes) (bs : List Block)
  /-- `Footnote(id, text)`: a footnote definition. -/
  | footnote (id : Bytes) (bs : List Block)
  /-- `HTMLBlock(content)`: raw HTML lines, `first` then `rest`. The parser always reads at
  least one line (`Common/block.jl:479-524`). -/
  | htmlBlock (first : Bytes) (rest : List Bytes)
  | value (repr : Bytes)
  deriving Repr, Inhabited

end JuliaLean.Markdown

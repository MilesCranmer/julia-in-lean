import JuliaLean.stdlib.Markdown.src.Common.block
import JuliaLean.stdlib.Markdown.src.GitHub.GitHub
import JuliaLean.stdlib.Markdown.src.IPython.IPython
import JuliaLean.stdlib.Markdown.src.render.html
import JuliaLean.stdlib.Markdown.src.render.latex
import JuliaLean.stdlib.Markdown.src.render.plain
import JuliaLean.stdlib.Markdown.src.render.rst

/-!
# Markdown: properties

Each property states a promise of the parser or a printer. Round-trip properties
(`parse(plain(md)) == md`, where `==` on `MD` compares `html` output,
`parse/parse.jl:41`) are stated through the block or inline reader that would have
to accept the printed text: if that reader declines or returns something else, the
re-parsed document differs.
-/

namespace JuliaLean.Markdown

def throwsJl {α} : Except Err α → Bool
  | .error e => e != .outOfFuel
  | .ok _ => false

/-- The run ended with the exception `e`. -/
def errIs {α} (e : Err) : Except Err α → Bool
  | .error e' => e' == e
  | .ok _ => false

/-- The run ended with a `MethodError`. -/
def isMethodError {α} : Except Err α → Bool
  | .error (.methodError _) => true
  | _ => false

/-- ASCII letters only, at least one. -/
def isLetters (s : Bytes) : Bool :=
  !s.isEmpty && s.all fun b => (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)

/-! ## The parser never throws -/

/-- `hashheader` throws no exception on any input, given an inline parser that does not throw. -/
def listLoose (s : Bytes) : Bool :=
  match runOn (listP (fun _ => .ok ())) s with
  | .ok (some (_, _, loose), _) => loose
  | _ => false

/-- A list of one-word items `- x` followed by a blank line and a paragraph is tight. -/
def htmlTagNames : List Bytes :=
  [bytes% "p", bytes% "em", bytes% "strong", bytes% "s", bytes% "code", bytes% "pre", bytes% "a",
   bytes% "img", bytes% "br", bytes% "hr", bytes% "h1", bytes% "h2", bytes% "h3", bytes% "h4",
   bytes% "h5", bytes% "h6", bytes% "ul", bytes% "ol", bytes% "li", bytes% "blockquote", bytes% "div"]

/-- `t` begins with the rest of one of the printer's tags, after its `<`. -/
def opensTag (t : Bytes) : Bool :=
  htmlTagNames.any fun n =>
    (n ++ [62]).isPrefixOf t || (n ++ [32]).isPrefixOf t || ([47] ++ n ++ [62]).isPrefixOf t

/-- Every `<` in `s` starts one of the printer's own tags. -/
def tagSafe : Bytes → Bool
  | [] => true
  | b :: t => (b != 60 || opensTag t) && tagSafe t

mutual
/-- The inline tree contains no raw HTML and its footnote ids contain no `<` (the parser's ids
match `\w+`, `Common/inline.jl:147`). -/
def inlineOk : Inline → Bool
  | .htmlInline _ => false
  | .footnoteRef id => !id.contains 60
  | .bold xs => inlinesOk xs
  | .italic xs => inlinesOk xs
  | .strike xs => inlinesOk xs
  | .link xs _ => inlinesOk xs
  | _ => true
def inlinesOk : List Inline → Bool
  | [] => true
  | x :: xs => inlineOk x && inlinesOk xs
end

mutual
/-- The document contains no raw HTML, header levels are 1-6 and footnote ids contain no `<`
(as every parser output); with `titles`, admonition titles contain no `<` either. -/
def blockOk (titles : Bool) : Block → Bool
  | .htmlBlock _ _ => false
  | .para xs => inlinesOk xs
  | .header l xs => 1 ≤ l && l ≤ 6 && inlinesOk xs
  | .quote bs => blocksOk titles bs
  | .list items _ _ => itemsOk titles items
  | .admonition _ t bs => (!titles || !t.contains 60) && blocksOk titles bs
  | .footnote id bs => !id.contains 60 && blocksOk titles bs
  | _ => true
def blocksOk (titles : Bool) : List Block → Bool
  | [] => true
  | b :: bs => blockOk titles b && blocksOk titles bs
def itemsOk (titles : Bool) : List (List Block) → Bool
  | [] => true
  | it :: its => blocksOk titles it && itemsOk titles its
end

/-- `html` escapes all document text: in a document without raw HTML, every `<` of the output
starts one of the printer's own tags. -/
def htmlUnescape : Bytes → Bytes
  | [] => []
  | 38 :: 108 :: 116 :: 59 :: r => 60 :: htmlUnescape r
  | 38 :: 103 :: 116 :: 59 :: r => 62 :: htmlUnescape r
  | 38 :: 113 :: 117 :: 111 :: 116 :: 59 :: r => 34 :: htmlUnescape r
  | 38 :: 97 :: 109 :: 112 :: 59 :: r => 38 :: htmlUnescape r
  | b :: r => b :: htmlUnescape r

/-- `htmlesc` removes every `<`, `>` and `"` and loses no text: decoding its four entities gives
the input back. -/
def latexSections : List Bytes :=
  [bytes% "section", bytes% "subsection", bytes% "subsubsection", bytes% "paragraph",
   bytes% "subparagraph"]

/- `latex` renders every header level 1-6 with a standard sectioning command. -/

end JuliaLean.Markdown

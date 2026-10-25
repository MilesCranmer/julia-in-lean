import JuliaLean.Markdown.Block
import JuliaLean.Markdown.Render

/-!
# Markdown: properties

Each property states a promise of the parser or a printer. Round-trip properties
(`parse(plain(md)) == md`, where `==` on `MD` compares `html` output,
`parse/parse.jl:41`) are stated through the block or inline reader that would have
to accept the printed text: if that reader declines or returns something else, the
re-parsed document differs.
-/

namespace JuliaLean.Markdown

/-- The run ended with a Julia exception (not the model's fuel artefact). -/
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
def HashheaderTotal : Prop :=
  ∀ (α : Type) (inl : Bytes → α) (s : Bytes),
    throwsJl (runOn (hashheader (fun b => .ok (inl b))) s) = false

/-- `github_paragraph` throws no exception on any input, given a breaking-block parser and an
inline parser that do not throw. -/
def GithubParagraphTotal : Prop :=
  ∀ (brk : M Bool) (inl : Bytes → Unit),
    (∀ st, ∃ r, brk.run st = .ok r) →
    ∀ s, throwsJl (runOn (githubParagraph brk (fun b => .ok (inl b))) s) = false

/-- `list` throws no `OverflowError` on any input, given a nested parser that does not throw. -/
def ListNoOverflow : Prop :=
  ∀ (doc : Bytes → Unit) (s : Bytes),
    errIs .overflowError (runOn (listP (fun b => .ok (doc b))) s) = false

/-- `list` throws no `ArgumentError` on any input, given a nested parser that does not throw. -/
def ListNoArgumentError : Prop :=
  ∀ (doc : Bytes → Unit) (s : Bytes),
    errIs .argumentError (runOn (listP (fun b => .ok (doc b))) s) = false

/-! ## Tight and loose lists -/

/-- The `loose` flag of a list that `list` parses from `s` (`false` if it declines or throws). -/
def listLoose (s : Bytes) : Bool :=
  match runOn (listP (fun _ => .ok ())) s with
  | .ok (some (_, _, loose), _) => loose
  | _ => false

/-- A list of one-word items `- x` followed by a blank line and a paragraph is tight. -/
def ListTrailingBlankTight : Prop :=
  ∀ (xs : List Bytes) (t : Bytes), xs ≠ [] → (∀ x ∈ xs, isLetters x = true) → isLetters t = true →
    listLoose (xs.flatMap (fun x => bytes% "- " ++ x ++ [10]) ++ [10] ++ t) = false

/-- `plain` prints a loose list of one-word paragraphs so that `list` reads it back loose. -/
def PlainLooseList : Prop :=
  ∀ (xs : List Bytes), 2 ≤ xs.length → (∀ x ∈ xs, isLetters x = true) →
    listLoose (plain [.list (xs.map fun x => [.para [.text x]]) (-1) true]) = true

/-! ## HTML escaping -/

/-- Tag names printed by the HTML model. -/
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
def HtmlTextEscaped : Prop :=
  ∀ (styled : Bytes → Bytes) (md : List Block), blocksOk false md = true →
    tagSafe (html styled md) = true

/-- The admonition title is the only unescaped document text of `html`: when admonition titles
contain no `<` either, every `<` of the output starts one of the printer's own tags. -/
def HtmlTagSafeTitles : Prop :=
  ∀ (styled : Bytes → Bytes) (md : List Block), blocksOk true md = true →
    tagSafe (html styled md) = true

/-- Decoding of the four entities that `htmlesc` writes (`&lt;`, `&gt;`, `&quot;`, `&amp;`). -/
def htmlUnescape : Bytes → Bytes
  | [] => []
  | 38 :: 108 :: 116 :: 59 :: r => 60 :: htmlUnescape r
  | 38 :: 103 :: 116 :: 59 :: r => 62 :: htmlUnescape r
  | 38 :: 113 :: 117 :: 111 :: 116 :: 59 :: r => 34 :: htmlUnescape r
  | 38 :: 97 :: 109 :: 112 :: 59 :: r => 38 :: htmlUnescape r
  | b :: r => b :: htmlUnescape r

/-- `htmlesc` removes every `<`, `>` and `"` and loses no text: decoding its four entities gives
the input back. -/
def HtmlescSound : Prop :=
  ∀ s : Bytes, 60 ∉ htmlesc s ∧ 62 ∉ htmlesc s ∧ 34 ∉ htmlesc s ∧ htmlUnescape (htmlesc s) = s

/-- `html` of an ordered list shows its start number: `<ol start="k">`, or `<ol>` when `k = 1`. -/
def HtmlOrderedStart : Prop :=
  ∀ (styled : Bytes → Bytes) (items : List (List Block)) (k : Int) (loose : Bool), 0 ≤ k →
    let out := html styled [.list items k loose]
    (bytes% "<ol start=\"" ++ intString k ++ bytes% "\">").isPrefixOf out ||
      (k == 1 && (bytes% "<ol>").isPrefixOf out)

/-! ## `plain` output reparses -/

/-- The `*` reader that `parseinline` tries at the start of a paragraph (`asterisk_italic`)
declines on `plain` of a paragraph whose only element is a text node. -/
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
def BlocktexInlineDollar : Prop :=
  ∀ (isword : Nat → Bool) (s : Bytes),
    (match runOn (blocktex isword) s with
     | .ok (some _, st) => ((st.data.drop st.pos).takeWhile (· != 10)).all isWhitespace
     | _ => true) = true

/-- `inline_code` reads `plain` of an inline code node back as the same code, for every code
text the parser can produce (stripped, without newlines). -/
def PlainCodeSpan : Prop :=
  ∀ (c : Bytes), strip c = c → ¬ 10 ∈ c →
    (match runOn inlineCode (plainInline (.code [] c)) with
     | .ok (some (.code l c'), _) => l.isEmpty && c' == c
     | _ => false) = true

/-! ## LaTeX and reStructuredText printers -/

/-- `latex` has a method for every node the parser produces. -/
def LatexTotal : Prop :=
  ∀ (styled : Bytes → Bytes) (md : List Block), isMethodError (latex styled md) = false

/-- `rst` has a method for every node the parser produces. -/
def RstTotal : Prop :=
  ∀ (styled : Bytes → Bytes) (md : List Block), isMethodError (rst styled md) = false

/-- Standard LaTeX sectioning commands. -/
def latexSections : List Bytes :=
  [bytes% "section", bytes% "subsection", bytes% "subsubsection", bytes% "paragraph",
   bytes% "subparagraph"]

/-- `latex` renders every header level 1-6 with a standard sectioning command. -/
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

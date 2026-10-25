import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Markdown.Stream
import JuliaLean.Markdown.Ast
import JuliaLean.Markdown.Inline
import JuliaLean.Markdown.Block
import JuliaLean.Markdown.Render
import JuliaLean.Markdown.Props
import JuliaLean.Markdown.Refute
import JuliaLean.Markdown.Proven

namespace JuliaLean.Markdown

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- refuted: the parser throws
  { id := "markdown-hashheader-cr-eof", juliaFile := "stdlib/Markdown/src/Common/block.jl"
    juliaFns := ["Markdown.hashheader"]
    statement := "hashheader throws no exception on any input (given an inline parser that does not throw)."
    source := "invariant (Markdown.parse accepts every string); stdlib/Markdown/src/Markdown.jl:63-70", status := .refuted
    prop := ``HashheaderTotal, thm := some ``hashheaderTotal_refuted
    issue := "none found (queries: Markdown EOFError, Markdown carriage return, Markdown CRLF, hashheader)"
    notes := "Markdown.parse(\"#\\r\") throws EOFError on master: Common/block.jl:63-64 peeks after '\\r' without an eof check. Regression from #60708; 1.13.2 returns a paragraph." },
  { id := "markdown-github-paragraph-cr-eof", juliaFile := "stdlib/Markdown/src/GitHub/GitHub.jl"
    juliaFns := ["Markdown.github_paragraph"]
    statement := "github_paragraph throws no exception on any input (given breaking and inline parsers that do not throw)."
    source := "invariant (Markdown.parse accepts every string); stdlib/Markdown/src/Markdown.jl:63-70", status := .refuted
    prop := ``GithubParagraphTotal, thm := some ``githubParagraphTotal_refuted
    issue := "none found (queries: Markdown EOFError, github_paragraph, Markdown carriage return, Markdown CRLF)"
    notes := "Markdown.parse(\"a\\r\", flavor = :github) throws EOFError on master (GitHub/GitHub.jl:12-13). 1.13.2 returns a paragraph." },
  { id := "markdown-list-number-overflow", juliaFile := "stdlib/Markdown/src/Common/block.jl"
    juliaFns := ["Markdown.list"]
    statement := "list throws no OverflowError on any input."
    source := "invariant (Markdown.parse accepts every string); CommonMark 0.31 5.2 (at most 9 digits)", status := .refuted
    prop := ``ListNoOverflow, thm := some ``listNoOverflow_refuted
    issue := "none found (queries: Markdown list overflow, Markdown OverflowError, Markdown ordered list number, NUM_OR_BULLETS)"
    notes := "Markdown.parse(\"12345678901234567890. item\") throws OverflowError: Base.parse(Int, ...) on an unbounded \\d+ run (Common/block.jl:316, 331). Both versions." },
  { id := "markdown-list-unicode-digit", juliaFile := "stdlib/Markdown/src/Common/block.jl"
    juliaFns := ["Markdown.list"]
    statement := "list throws no ArgumentError on any input."
    source := "invariant (Markdown.parse accepts every string); CommonMark 0.31 5.2 (ASCII digits)", status := .refuted
    prop := ``ListNoArgumentError, thm := some ``listNoArgumentError_refuted
    issue := "none found (queries: Markdown list, Markdown ordered list, Markdown ArgumentError, invalid base 10 digit, Markdown unicode, Markdown Persian, Markdown digit)"
    notes := "Markdown.parse(\"۱. item\") and (\"１. item\") throw ArgumentError: PCRE \\d under UCP matches every Nd digit (ndRanges, read off PCRE on master), Base.parse(Int) accepts only ASCII. Both versions." },
  -- refuted: list structure
  { id := "markdown-list-trailing-blank-loose", juliaFile := "stdlib/Markdown/src/Common/block.jl"
    juliaFns := ["Markdown.list"]
    statement := "A list of one-word items followed by a blank line and a paragraph is parsed as a tight list."
    source := "CommonMark 0.31 5.3 (tight and loose lists), implemented by #60676", status := .refuted
    prop := ``ListTrailingBlankTight, thm := some ``listTrailingBlankTight_refuted
    issue := "related #60676 (merged), #22076 (closed); none found for this case (queries: loose list, tight list, Markdown loose, Markdown tight)"
    notes := "\"- a\\n- b\\n\\nText\" gives loose = true on master: the blank line that ends the list sets list.loose (Common/block.jl:350-352). 1.13.2 sets loose = false here." },
  { id := "markdown-plain-loose-list", juliaFile := "stdlib/Markdown/src/render/plain.jl"
    juliaFns := ["Markdown.plain(::IO, ::Markdown.List)"]
    statement := "plain prints a loose list so that list reads it back as loose."
    source := "show(io, MIME\"text/markdown\", md) = plain(io, md), render/plain.jl:170", status := .refuted
    prop := ``PlainLooseList, thm := some ``plainLooseList_refuted
    issue := "related #60676 (merged), #35917 (open); none found for this case (queries: loose list, Markdown plain, Markdown roundtripability, Markdown loose)"
    notes := "plain prints \"  * a\\n  * b\\n\" for the loose list of \"- a\\n\\n- b\". On 1.13.2 html ignores loose, so the round trip only fails on master." },
  -- refuted: HTML
  { id := "markdown-html-admonition-title", juliaFile := "stdlib/Markdown/src/render/html.jl"
    juliaFns := ["Markdown.html(::IO, ::Markdown.Admonition)"]
    statement := "In a document without raw HTML, every '<' in html output starts one of the printer's own tags."
    source := "manual (admonition titles are plain strings), stdlib/Markdown/docs/src/index.md:418; htmlinline(::String) escapes, render/html.jl:184-189", status := .refuted
    prop := ``HtmlTextEscaped, thm := some ``htmlTextEscaped_refuted
    issue := "related #62122 (open PR, switches the title to htmlinline), #62106 (closed); none found for the escaping (queries: Markdown admonition, admonition title escape, admonition-title, Markdown html escape, Markdown escape)"
    notes := "render/html.jl:124 print(io, md.title): a title \"<script>alert(1)</script>\" is emitted as a live element. Both versions. HtmlTagSafeTitles proves this is the only leak." },
  { id := "markdown-html-ordered-start-zero", juliaFile := "stdlib/Markdown/src/render/html.jl"
    juliaFns := ["Markdown.html(::IO, ::Markdown.List)"]
    statement := "html of an ordered list with start k ≥ 0 begins with <ol start=\"k\">, or <ol> when k = 1."
    source := "List.ordered (`>= 0` is ordered and indicates the start index), Common/block.jl:305", status := .refuted
    prop := ``HtmlOrderedStart, thm := some ``htmlOrderedStart_refuted
    issue := "none found (queries: Markdown ordered list, Markdown ordered list start 0, ol start, Markdown list start)"
    notes := "render/html.jl:131 tests ordered > 1, so a list starting at 0 renders as <ol> (numbered from 1). Both versions; manual describes start numbers as positive, so P3." },
  -- refuted: plain output does not reparse
  { id := "markdown-plain-text-unescaped", juliaFile := "stdlib/Markdown/src/render/plain.jl"
    juliaFns := ["Markdown.plaininline(::IO, ::AbstractString)"]
    statement := "asterisk_italic declines on plain of a paragraph whose only element is a text node (so the text node reparses as text)."
    source := "show(io, MIME\"text/markdown\", md) = plain(io, md), render/plain.jl:170; issue #35917", status := .refuted
    prop := ``PlainTextRoundtrip, thm := some ``plainTextRoundtrip_refuted
    issue := "#35917 (open, same report)"
    notes := "The text *not emphasis* (from \\*not emphasis\\*) is printed verbatim and reparses as Italic. Both versions." },
  { id := "markdown-plain-display-math", juliaFile := "stdlib/Markdown/src/render/plain.jl"
    juliaFns := ["Markdown.plain(::IO, ::Markdown.LaTeX)"]
    statement := "blocktex or fencedcode reads plain of a display equation (formula without newline) back as the same formula."
    source := "show(io, MIME\"text/markdown\", md) = plain(io, md), render/plain.jl:170", status := .refuted
    prop := ``PlainDisplayMath, thm := some ``plainDisplayMath_refuted
    issue := "related #37334 (open, $$ must be on one line), #35917 (open)"
    notes := "plain prints $$\\nx^2\\n$$; blocktex rejects a $ run followed by whitespace (parse/util.jl:232), fencedcode needs ``` or ~~~. Both versions." },
  { id := "markdown-blocktex-inline-dollar", juliaFile := "stdlib/Markdown/src/IPython/IPython.jl"
    juliaFns := ["Markdown.blocktex"]
    statement := "When blocktex accepts, only whitespace follows the formula on its line."
    source := "manual: inline LaTeX with single $, stdlib/Markdown/docs/src/index.md:85", status := .refuted
    prop := ``BlocktexInlineDollar, thm := some ``blocktexInlineDollar_refuted
    issue := "related #37334 (open); none found (queries: Markdown dollar, inline math dollar, blocktex, Markdown math, Markdown $$)"
    notes := "\"$x$ is positive\" parses to [LaTeX(x), Paragraph(is positive)]. plain prints inline ``x`` math as $x$, so it is also hit by round trips. Both versions." },
  { id := "markdown-plain-empty-code-span", juliaFile := "stdlib/Markdown/src/render/plain.jl"
    juliaFns := ["Markdown.plaininline(::IO, ::Markdown.Code)"]
    statement := "inline_code reads plain of an inline code node back as the same code, for every stripped code text without newlines."
    source := "show(io, MIME\"text/markdown\", md) = plain(io, md), render/plain.jl:170", status := .refuted
    prop := ``PlainCodeSpan, thm := some ``plainCodeSpan_refuted
    issue := "related #35917 (open); none found for this case (queries: Markdown code span empty, Markdown plain, Markdown roundtripability)"
    notes := "Code(\"\", \"\") from \"a ` ` b\" is printed as ``, an unclosed two-tick opener. Both versions." },
  -- refuted: LaTeX and rst printers
  { id := "markdown-latex-printer-throws", juliaFile := "stdlib/Markdown/src/render/latex.jl"
    juliaFns := ["Markdown.latex(::IO, ::Vector)", "Markdown.latexinline(::IO, ::Vector)"]
    statement := "latex has a method for every node the parser produces (never throws MethodError)."
    source := "manual: interpolated values are rendered with show, stdlib/Markdown/docs/src/index.md:434-436; latex docstring, render/latex.jl:185-199", status := .refuted
    prop := ``LatexTotal, thm := some ``latexTotal_refuted
    issue := "related #13760 (closed PR, missing latex fallback); none found (queries: Markdown latex, Markdown.latex, latexinline MethodError, Markdown interpolation latex)"
    notes := "latex(md\"The answer is $x.\") with x = 42 throws MethodError (both versions); on master raw HTML nodes also throw." },
  { id := "markdown-rst-printer-throws", juliaFile := "stdlib/Markdown/src/render/rst.jl"
    juliaFns := ["Markdown.rst(::IO, ::Any)", "Markdown.rstinline(::IO, ::Any)"]
    statement := "rst has a method for every node the parser produces (never throws MethodError)."
    source := "invariant (html and plain handle every node); show(io, MIME\"text/rst\", md), render/rst.jl:151", status := .refuted
    prop := ``RstTotal, thm := some ``rstTotal_refuted
    issue := "none found (queries: Markdown rst, Markdown.rst, rst Image, text/rst, rstinline)"
    notes := "rst of an Image throws (both versions); Strikethrough and raw HTML throw on master. The model follows the source for the \"\\\\ \" separator after code; nightly drops it because of compiler-isa-flag-loop." },
  { id := "markdown-latex-h6-invalid", juliaFile := "stdlib/Markdown/src/render/latex.jl"
    juliaFns := ["Markdown.latex(::IO, ::Markdown.Header)"]
    statement := "latex renders every header level 1-6 with a standard sectioning command."
    source := "manual lists six header levels, stdlib/Markdown/docs/src/index.md:160-169", status := .refuted
    prop := ``LatexHeaderCommands, thm := some ``latexHeaderCommands_refuted
    issue := "none found (queries: subparagraph, Markdown latex header, Markdown latex, Markdown.latex)"
    notes := "Level 6 becomes \\subsubparagraph (render/latex.jl:28), which LaTeX does not define. Both versions." },
  { id := "markdown-latex-admonition-title", juliaFile := "stdlib/Markdown/src/render/latex.jl"
    juliaFns := ["Markdown.latex(::IO, ::Markdown.Admonition)"]
    statement := "latex output of an admonition contains latexesc of its title."
    source := "manual: admonition titles are plain strings, stdlib/Markdown/docs/src/index.md:418", status := .refuted
    prop := ``LatexTextEscaped, thm := some ``latexTextEscaped_refuted
    issue := "related #62122 (open); none found (queries: Markdown latex escape admonition, Markdown admonition, Markdown latex, admonition title escape)"
    notes := "!!! note \"50% of x_1\" prints 50% of x_1 raw (render/latex.jl:78). Both versions." },
  -- proven
  { id := "markdown-htmlesc-sound", juliaFile := "stdlib/Markdown/src/render/html.jl"
    juliaFns := ["Markdown.htmlesc"]
    statement := "htmlesc output contains no <, > or \", and decoding &lt; &gt; &quot; &amp; recovers the input."
    source := "render/html.jl:46-48 (htmlesc), used for all text and attribute values", status := .proven
    prop := ``HtmlescSound, thm := some ``htmlescSound_proven },
  { id := "markdown-html-tag-safe-titles", juliaFile := "stdlib/Markdown/src/render/html.jl"
    juliaFns := ["Markdown.html", "Markdown.htmlinline", "Markdown.withtag"]
    statement := "In a document without raw HTML whose admonition titles contain no <, every < of html output starts one of the printer's own tags."
    source := "manual (admonition titles and text are plain strings), stdlib/Markdown/docs/src/index.md:418; render/html.jl:30-48, 184-189", status := .proven
    prop := ``HtmlTagSafeTitles, thm := some ``htmlTagSafeTitles_proven
    notes := "With markdown-html-admonition-title this shows the admonition title is the only unescaped document text. Footnote ids are printed raw but the parser only produces \\w+ ids (precondition)." }
]

end JuliaLean.Markdown

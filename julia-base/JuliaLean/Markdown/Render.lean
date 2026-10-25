import JuliaLean.Markdown.Inline

/-!
# Markdown: printers

Models of `Markdown.html` (`stdlib/Markdown/src/render/html.jl`, `rich.jl`),
`Markdown.latex` (`render/latex.jl`, `IPython/IPython.jl`), `Markdown.rst`
(`render/rst.jl`) and `Markdown.plain` (`render/plain.jl`) at master
`bbfa0ce4150`, over the tree of `JuliaLean.Markdown.Ast`. Output is a byte list;
`latex` and `rst` return `Except Err` because some nodes have no method.

* `styled` is `String(styled(code))` (StyledStrings markup, applied to code whose
  language is `"styled"`); the printers take it as an argument.
* `uppercasefirst` is modelled for ASCII first characters; the parser only
  produces admonition categories matching `[a-z]+` (`Common/block.jl:263-264`).
* An interpolated value is shown through `text/plain` (`tohtml`, `render/rich.jl:7-9`);
  `value repr` carries that output.
-/

namespace JuliaLean.Markdown

/-- `htmlesc(io, s)`, `render/html.jl:46-48`: `replace(io, s, '<'=>"&lt;", '>'=>"&gt;",
'"'=>"&quot;", '&'=>"&amp;")`. The four characters are ASCII, so the replacement acts on bytes. -/
def htmlesc (s : Bytes) : Bytes :=
  s.flatMap fun b =>
    if b == 60 then bytes% "&lt;" else if b == 62 then bytes% "&gt;"
    else if b == 34 then bytes% "&quot;" else if b == 38 then bytes% "&amp;" else [b]

/-- The attributes printed by `withtag`, `render/html.jl:30-41`. -/
def attrBytes (attrs : List (Bytes × Bytes)) : Bytes :=
  attrs.flatMap fun (a, v) => [32] ++ a ++ bytes% "=\"" ++ htmlesc v ++ [34]

/-- `withtag(f, io, tag, attrs...)`, `render/html.jl:30-41`, with a body. -/
def withtag (tag : Bytes) (attrs : List (Bytes × Bytes)) (body : Bytes) : Bytes :=
  [60] ++ tag ++ attrBytes attrs ++ [62] ++ body ++ bytes% "</" ++ tag ++ [62]

/-- `tag(io, tag, attrs...)`, i.e. `withtag(nothing, ...)`. -/
def tagOnly (tag : Bytes) (attrs : List (Bytes × Bytes)) : Bytes :=
  [60] ++ tag ++ attrBytes attrs ++ bytes% " />"

/-- A UTF-8 segment that decodes to a valid character. -/
def validSeg : Bytes → Bool
  | [a] => a < 0x80
  | [a, b] => 0xC2 ≤ a && a ≤ 0xDF && b / 64 == 2
  | [a, b, c] => 0xE0 ≤ a && a ≤ 0xEF && b / 64 == 2 && c / 64 == 2 &&
      (a != 0xE0 || b ≥ 0xA0) && (a != 0xED || b < 0xA0)
  | [a, b, c, d] => 0xF0 ≤ a && a ≤ 0xF4 && b / 64 == 2 && c / 64 == 2 && d / 64 == 2 &&
      (a != 0xF0 || b ≥ 0x90) && (a != 0xF4 || b < 0x90)
  | _ => false

/-- Characters kept by `encode_uri_component`: `[A-Za-z0-9\-_.~/:?#@!$&'()*+,;=]`. -/
def uriKeep (b : Nat) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) ||
  (bytes% "-_.~/:?#@!$&'()*+,;=").contains b

/-- Upper-case hex digit. -/
def hexDigit (d : Nat) : Nat := if d < 10 then 48 + d else 55 + d

/-- `encode_uri_component(s)`, `render/html.jl:24-27`: every byte of a valid character outside
the kept set becomes `%` and `uppercase(string(b, base=16))` (one digit below 16). Invalid
UTF-8 is never matched by the regex (`MATCH_INVALID_UTF`) and is kept. -/
def encodeUri (s : Bytes) : Bytes :=
  (segments s).flatMap fun (_, bs) =>
    if validSeg bs && !(bs.length == 1 && uriKeep (bs.headD 0)) then
      bs.flatMap fun b => [37] ++ (if b < 16 then [hexDigit b] else [hexDigit (b / 16), hexDigit (b % 16)])
    else bs

/-- Is the byte a space or a tab? -/
def isSpTab (c : Nat) : Bool := c == 32 || c == 9

/-- `replace(s, r"[ \t]+\n" => "\n")`. -/
def dropWsBeforeNl (s : Bytes) : Bytes := go s.length s
where
  go : Nat → Bytes → Bytes
  | 0, s => s
  | _, [] => []
  | k + 1, b :: bs =>
    if isSpTab b then
      let rest := bs.dropWhile isSpTab
      match rest with
      | 10 :: _ => go k rest
      | _ => b :: go k bs
    else b :: go k bs

/-- `replace(s, r"\n[ \t]+" => "\n")`. The fuel `s.length` covers every step. -/
def dropWsAfterNl (s : Bytes) : Bytes := go s.length s
where
  go : Nat → Bytes → Bytes
  | 0, s => s
  | _, [] => []
  | k + 1, b :: bs => if b == 10 then 10 :: go k (bs.dropWhile isSpTab) else b :: go k bs

/-- `htmlinline(io, s::String)`, `render/html.jl:184-189`. -/
def htmlText (s : Bytes) : Bytes := htmlesc (dropWsAfterNl (dropWsBeforeNl s))

/-- `show(io, ::LaTeX)`: `$formula$` (`IPython/IPython.jl:25-26`). -/
def latexShow (f : Bytes) : Bytes := [36] ++ f ++ [36]

/-- The decimal digits of a natural number. -/
def natDigits (n : Nat) : Bytes := (Nat.toDigits 10 n).map Char.toNat

/-- `string(x)` for an `Int`. -/
def intString (x : Int) : Bytes := if x < 0 then 45 :: natDigits x.natAbs else natDigits x.natAbs

/-- `x % Int64`: two's-complement wrap-around of Julia `Int` arithmetic. -/
def wrap64 (x : Int) : Int := (x + 2 ^ 63) % 2 ^ 64 - 2 ^ 63

/-! ## HTML -/

mutual
/-- `htmlinline(io, x)`, `render/html.jl:159-231`. -/
def htmlInline (styled : Bytes → Bytes) : Inline → Bytes
  | .text s => htmlText s
  | .code lang c =>
    let c := if lang == bytes% "styled" then styled c else c
    withtag (bytes% "code") [] (htmlesc c)
  | .latex f => htmlesc (latexShow f)
  | .bold xs => withtag (bytes% "strong") [] (htmlInlines styled xs)
  | .italic xs => withtag (bytes% "em") [] (htmlInlines styled xs)
  | .strike xs => withtag (bytes% "s") [] (htmlInlines styled xs)
  | .link xs url => withtag (bytes% "a") [(bytes% "href", encodeUri url)] (htmlInlines styled xs)
  | .image url alt => tagOnly (bytes% "img") [(bytes% "src", encodeUri url), (bytes% "alt", alt)]
  | .footnoteRef id =>
    withtag (bytes% "a") [(bytes% "href", bytes% "#footnote-" ++ id), (bytes% "class", bytes% "footnote")]
      ([91] ++ id ++ [93])
  | .lineBreak => tagOnly (bytes% "br") [] ++ [10]
  | .htmlInline s => s
  | .value r => htmlesc r
/-- `htmlinline(io, content::Vector)`. -/
def htmlInlines (styled : Bytes → Bytes) : List Inline → Bytes
  | [] => []
  | x :: xs => htmlInline styled x ++ htmlInlines styled xs
end

mutual
/-- `html(io, x)` for a block, `render/html.jl:73-155`. -/
def htmlBlock (styled : Bytes → Bytes) : Block → Bytes
  | .para xs => withtag (bytes% "p") [] (htmlInlines styled xs)
  | .header l xs => withtag ([104] ++ natDigits l) [] (htmlInlines styled xs)
  | .code lang c =>
    let (lang, c) := if lang == bytes% "styled" then ([], styled c) else (lang, c)
    withtag (bytes% "pre") []
      (withtag (bytes% "code") (if lang.isEmpty then [] else [(bytes% "class", bytes% "language-" ++ lang)])
        (htmlesc c ++ (if c.isEmpty then [] else [10])))
  | .latex f => htmlesc (latexShow f)
  | .quote bs => withtag (bytes% "blockquote") [] ([10] ++ htmlBlocks styled bs)
  | .list items k loose =>
    withtag (if k ≥ 0 then bytes% "ol" else bytes% "ul")
      (if k > 1 then [(bytes% "start", intString k)] else [])
      (htmlItems styled loose items ++ [10])
  | .hr => tagOnly (bytes% "hr") []
  | .admonition cat title bs =>
    withtag (bytes% "div") [(bytes% "class", bytes% "admonition " ++ cat)]
      (withtag (bytes% "p") [(bytes% "class", bytes% "admonition-title")] title ++ htmlBlocks styled bs)
  | .footnote id bs =>
    withtag (bytes% "div") [(bytes% "class", bytes% "footnote"), (bytes% "id", bytes% "footnote-" ++ id)]
      (withtag (bytes% "p") [(bytes% "class", bytes% "footnote-title")] id ++ htmlBlocks styled bs)
  | .htmlBlock first rest =>
    match (first :: rest).reverse with
    | last :: init => init.reverse.flatMap (· ++ [10]) ++ last
    | [] => []
  | .value r => htmlesc r
/-- `html(io, content::Vector)`: every element followed by a newline. -/
def htmlBlocks (styled : Bytes → Bytes) : List Block → Bytes
  | [] => []
  | b :: bs => htmlBlock styled b ++ [10] ++ htmlBlocks styled bs
/-- `htmltight(io, content::Vector)`, `render/html.jl:147-152`. -/
def htmlTight (styled : Bytes → Bytes) : List Block → Bytes
  | [] => []
  | .para xs :: bs => htmlInlines styled xs ++ htmlTight styled bs
  | b :: bs => htmlBlock styled b ++ htmlTight styled bs
/-- The item loop of `html(io, md::List)`, `render/html.jl:130-145`. -/
def htmlItems (styled : Bytes → Bytes) (loose : Bool) : List (List Block) → Bytes
  | [] => []
  | it :: its =>
    [10] ++ withtag (bytes% "li") [] (if loose then [10] ++ htmlBlocks styled it else htmlTight styled it)
      ++ htmlItems styled loose its
end

/-- `html(md)` for `md.content`. -/
def html (styled : Bytes → Bytes) (md : List Block) : Bytes := htmlBlocks styled md

/-! ## LaTeX -/

/-- `latexesc(io, s)`, `render/latex.jl:171-181`. -/
def latexesc (s : Bytes) : Bytes :=
  s.flatMap fun b =>
    if b == 126 then bytes% "{\\textasciitilde}" else if b == 94 then bytes% "\\^{}"
    else if b == 92 then bytes% "{\\textbackslash}"
    else if (bytes% "&%$#_{}").contains b then [92, b] else [b]

/-- `"sub"^k`. -/
def subs (k : Nat) : Bytes := (List.replicate k (bytes% "sub")).flatten

/-- `occursin(t, s)` on bytes. -/
def occursIn (t s : Bytes) : Bool := (List.range (s.length + 1)).any fun i => (s.drop i).take t.length == t

/-- `ndigits(x)`. -/
def ndigits (x : Int) : Nat := (natDigits x.natAbs).length

/-- `rpad(s, n)` for ASCII `s`. -/
def rpad (s : Bytes) (n : Nat) : Bytes := s ++ List.replicate (n - s.length) 32

mutual
/-- `latexinline(io, x)`, `render/latex.jl:47-169`. -/
def latexInline : Inline → Except Err Bytes
  | .text s => .ok (latexesc s)
  | .code _ c => .ok (bytes% "\\texttt{" ++ latexesc c ++ [125])
  | .latex f => .ok ([36] ++ f ++ [36])
  | .bold xs => do return bytes% "\\textbf{" ++ (← latexInlines xs) ++ [125]
  | .italic xs => do return bytes% "\\emph{" ++ (← latexInlines xs) ++ [125]
  | .strike xs => do return bytes% "\\sout{" ++ (← latexInlines xs) ++ [125]
  | .link xs url => do return bytes% "\\href{" ++ url ++ bytes% "}{" ++ (← latexInlines xs) ++ [125]
  | .image url alt => .ok (bytes% "\\begin{figure}\n\\centering\n\\includegraphics{" ++ url ++
      bytes% "}\n\\caption{" ++ latexesc alt ++ bytes% "}\n\\end{figure}\n")
  | .footnoteRef id => .ok (bytes% "\\footnotemark[" ++ id ++ [93])
  | .lineBreak => .ok (bytes% "\\\\\n")
  | .htmlInline _ => .error (.methodError "latexinline")
  | .value _ => .error (.methodError "latexinline")
def latexInlines : List Inline → Except Err Bytes
  | [] => .ok []
  | x :: xs => do return (← latexInline x) ++ (← latexInlines xs)
end

mutual
/-- `latex(io, x)` for a block, `render/latex.jl:19-110`, `IPython/IPython.jl:28-29`. -/
def latexBlock (styled : Bytes → Bytes) : Block → Except Err Bytes
  | .para xs => do return (← latexInlines xs) ++ [10, 10]
  | .header l xs => do
    let tag := if l < 4 then subs (l - 1) ++ bytes% "section" else subs (l - 4) ++ bytes% "paragraph"
    return [92] ++ tag ++ [123] ++ (← latexInlines xs) ++ [125, 10]
  | .code lang c => do
    let c := if lang == bytes% "styled" then styled c else c
    if occursIn (bytes% "\\end{verbatim}") c then throw .errorException
    return bytes% "\\begin{verbatim}\n" ++ c ++ [10] ++ bytes% "\\end{verbatim}\n"
  | .latex f => .ok (bytes% "$$" ++ f ++ bytes% "$$\n")
  | .quote bs => do return bytes% "\\begin{quote}\n" ++ (← latexBlocks styled bs) ++ bytes% "\\end{quote}\n"
  | .list items k _ => do
    let pad := ndigits (wrap64 (k + items.length)) + 2
    let body ← latexItems styled k pad items.length 1 items
    return bytes% "\\begin{itemize}\n" ++ body ++ bytes% "\\end{itemize}\n"
  | .hr => .ok (bytes% "\\rule{\\textwidth}{1pt}\n")
  | .admonition cat title bs => do
    return bytes% "\\begin{quote}\n\\textbf{" ++ cat ++ bytes% "}\n\n" ++ title ++ [10, 10] ++
      (← latexBlocks styled bs) ++ bytes% "\\end{quote}\n"
  | .footnote id bs => do
    return bytes% "\\footnotetext[" ++ id ++ bytes% "]{" ++ (← latexBlocks styled bs) ++ [125, 10]
  | .htmlBlock _ _ => .error (.methodError "latex")
  | .value _ => .error (.methodError "latex")
/-- `latex(io, content::Vector)`. -/
def latexBlocks (styled : Bytes → Bytes) : List Block → Except Err Bytes
  | [] => .ok []
  | b :: bs => do return (← latexBlock styled b) ++ (← latexBlocks styled bs)
/-- The item loop of `latex(io, md::List)`, `render/latex.jl:96-104`. -/
def latexItems (styled : Bytes → Bytes) (k : Int) (pad len : Nat) : Nat → List (List Block) → Except Err Bytes
  | _, [] => .ok []
  | n, it :: its => do
    let fmt := if k ≥ 0 then [91] ++ rpad (intString (wrap64 (n + k - 1)) ++ [46]) pad ++ [93] else []
    let body ← latexBlocks styled it
    let rest ← latexItems styled k pad len (n + 1) its
    return bytes% "\\item" ++ fmt ++ [32] ++ body ++ (if n < len then [10] else []) ++ rest
end

/-- `latex(md)` for `md.content`. -/
def latex (styled : Bytes → Bytes) (md : List Block) : Except Err Bytes := latexBlocks styled md

/-! ## Shared helpers of `plain` and `rst` -/

/-- `split(s, "\n")`: always at least one piece. -/
def splitNl (s : Bytes) : List Bytes :=
  s.foldr (fun b acc => if b == 10 then [] :: acc else match acc with
    | p :: ps => (b :: p) :: ps
    | [] => [[b]]) [[]]

/-- `rstrip(s)`: drop trailing characters satisfying `isspace`. -/
def rstrip (s : Bytes) : Bytes :=
  ((segments s).reverse.dropWhile (isspace ·.1)).reverse.flatMap (·.2)

/-- `length(s)` in characters. -/
def nchars (s : Bytes) : Nat := (segments s).length

/-- `uppercasefirst(s)` for an ASCII first character. -/
def uppercasefirst : Bytes → Bytes
  | b :: bs => (if 97 ≤ b && b ≤ 122 then b - 32 else b) :: bs
  | [] => []

/-- Indent every nonempty line after the first by `k` spaces and end with a newline: the line
loop of `plain(io, ::List)` and `rst(io, ::List)`. -/
def itemLines (k : Nat) (lines : List Bytes) : Bytes :=
  (lines.zipIdx.map fun (line, i) =>
      (if i == 0 || line.isEmpty then [] else List.replicate k 32) ++ line ++
      (if i + 1 < lines.length then [10] else [])).flatten ++ [10]

/-- `for line in split(rstrip(s), "\n"); println(io, isempty(line) ? e : p, line); end`. -/
def prefixLines (e p : Bytes) (s : Bytes) : Bytes :=
  (splitNl (rstrip s)).flatMap fun line => (if line.isEmpty then e else p) ++ line ++ [10]

/-! ## reStructuredText -/

/-- `rstescape(s)`: `replace(s, "\\" => "\\\\")`. -/
def rstescape (s : Bytes) : Bytes := s.flatMap fun b => if b == 92 then [92, 92] else [b]

/-- `occursin(r":(func|obj|ref|exc|class|const|data):`\.*", url)`. -/
def isRstRole (url : Bytes) : Bool :=
  [bytes% ":func:`", bytes% ":obj:`", bytes% ":ref:`", bytes% ":exc:`", bytes% ":class:`",
   bytes% ":const:`", bytes% ":data:`"].any (occursIn · url)

mutual
/-- `rstinline(io, x)`, `render/rst.jl:110-147`. The varargs calls for `Bold`, `Italic` and
`Link` pass literal strings and the text vector; none of them follows code, LaTeX or a link,
so the `"\\ "` separator of `rstinline(io, md...)` never applies inside them. -/
def rstInline : Inline → Except Err Bytes
  | .text s => .ok (rstescape s)
  | .code _ c => .ok (bytes% "``" ++ c ++ bytes% "``")
  | .latex f => .ok (bytes% ":math:`" ++ f ++ [96])
  | .bold xs => do return bytes% "**" ++ (← rstSeqList false xs) ++ bytes% "**"
  | .italic xs => do return [42] ++ (← rstSeqList false xs) ++ [42]
  | .link xs url =>
    if isRstRole url then .ok (rstescape url)
    else do return [96] ++ (← rstSeqList false xs) ++ bytes% " <" ++ rstescape url ++ bytes% ">`_"
  | .footnoteRef id => .ok ([91] ++ id ++ bytes% "]_")
  | .lineBreak => .ok [10]
  | .image _ _ => .error (.methodError "show")
  | .strike _ => .error (.methodError "show")
  | .htmlInline _ => .error (.methodError "show")
  | .value _ => .error (.methodError "show")
/-- `rstinline(io, md...)`, `render/rst.jl:110-117`, over the elements of a vector (the call
`rstinline(io, md::Vector) = !isempty(md) && rstinline(io, md...)` with `wasCode = false`): a
string right after code, LaTeX or a link gets `"\\ "` unless it starts with a space. -/
def rstSeqList (wasCode : Bool) : List Inline → Except Err Bytes
  | [] => .ok []
  | .text s :: xs => do
    let pre := if wasCode && s.headD 0 != 32 then bytes% "\\ " else []
    return pre ++ rstescape s ++ (← rstSeqList false xs)
  | x :: xs => do
    let isCode := match x with | .code .. | .latex _ | .link .. => true | _ => false
    return (← rstInline x) ++ (← rstSeqList isCode xs)
end

/-- `rstinline(io, md::Vector)`. -/
def rstInlines (xs : List Inline) : Except Err Bytes := rstSeqList false xs

/-- The underline characters `"*=-~:.^"` of `rst(io, ::Header)`. -/
def rstUnder (l : Nat) : Nat := (bytes% "*=-~:.^").getD (l - 1) 0

mutual
/-- `rst(io, x)` for a block, `render/rst.jl:15-104`. -/
def rstBlock (styled : Bytes → Bytes) : Block → Except Err Bytes
  | .para xs => do return (← rstInlines xs) ++ [10]
  | .header l xs => do
    let s ← rstInlines xs
    return s ++ [10] ++ List.replicate (nchars s) (rstUnder l) ++ [10, 10]
  | .code lang c => do
    let (hdr, c) :=
      if lang == bytes% "jldoctest" then (bytes% ".. doctest::\n\n", c)
      else if lang.isEmpty || lang == bytes% "julia" || lang == bytes% "julia-repl" then
        (bytes% ".. code-block:: julia\n\n", c)
      else if lang == bytes% "rst" then ([], c)
      else if lang == bytes% "styled" then (bytes% "::\n\n", styled c)
      else (bytes% "::\n\n", c)
    return hdr ++ (splitNl c).flatMap (fun l => bytes% "    " ++ l ++ [10])
  | .latex f => .ok (bytes% ".. math::\n\n" ++ (splitNl f).flatMap (fun l => bytes% "    " ++ l ++ [10]))
  | .quote bs => do return prefixLines (bytes% "    ") (bytes% "    ") (← rstBlocks styled bs) ++ [10]
  | .list items k _ => rstItems styled k 1 items
  | .hr => .ok ((List.replicate 5 (bytes% "–")).flatten ++ [10])
  | .admonition cat title bs => do
    let s ← rstBlocks styled bs
    let t := if title == uppercasefirst cat then [] else title
    return bytes% ".. " ++ cat ++ bytes% "::" ++ (if t.isEmpty then [] else [32] ++ t) ++ [10] ++
      prefixLines [] (bytes% "   ") s ++ [10]
  | .footnote id bs => do
    let s ← rstBlocks styled bs
    let lines := splitNl (rstrip s)
    let head := bytes% ".. [" ++ id ++ [93]
    if lines.length == 1 then return head ++ [32] ++ lines.headD [] ++ [10]
    return head ++ [10] ++ lines.flatMap (fun line =>
      (if line.isEmpty then [] else bytes% "   ") ++ rstrip line ++ [10]) ++ [10]
  | .htmlBlock _ _ => .error (.methodError "show")
  | .value _ => .error (.methodError "show")
/-- `rst(io, content::Vector)`: elements separated by newlines. -/
def rstBlocks (styled : Bytes → Bytes) : List Block → Except Err Bytes
  | [] => .ok []
  | [b] => rstBlock styled b
  | b :: bs => do return (← rstBlock styled b) ++ [10] ++ (← rstBlocks styled bs)
/-- The item loop of `rst(io, ::List)`, `render/rst.jl:41-52`. -/
def rstItems (styled : Bytes → Bytes) (k : Int) : Nat → List (List Block) → Except Err Bytes
  | _, [] => .ok []
  | i, it :: its => do
    let marker := if k ≥ 0 then intString (wrap64 (i + k - 1)) ++ bytes% ". " else bytes% "* "
    let s ← rstBlocks styled it
    return marker ++ itemLines marker.length (splitNl (rstrip s)) ++ (← rstItems styled k (i + 1) its)
end

/-- `rst(md)` for `md.content`. -/
def rst (styled : Bytes → Bytes) (md : List Block) : Except Err Bytes := rstBlocks styled md

/-! ## Plain Markdown -/

/-- Length of the longest run of backticks in `s`. -/
def maxTickRun (s : Bytes) : Nat := (go s 0 0).2
where
  go : Bytes → Nat → Nat → Nat × Nat
  | [], cur, best => (cur, max cur best)
  | b :: bs, cur, best => if b == 96 then go bs (cur + 1) (max (cur + 1) best) else go bs 0 best

/-- Longest backtick run at the start of a line (`eachmatch(r"^`+"m, code)`). -/
def maxLineStartTicks (s : Bytes) : Nat := ((splitNl s).map tickRun).foldl max 0

mutual
/-- `plaininline(io, x)`, `render/plain.jl:116-165`. -/
def plainInline : Inline → Bytes
  | .text s => s
  | .code _ c =>
    if c.contains 96 then
      let n := maxTickRun c
      let t := List.replicate ((if n % 2 == 0 then 1 else 2) + n) 96
      t ++ (if c.headD 0 == 96 then [32] else []) ++ c ++ (if c.getLastD 0 == 96 then [32] else []) ++ t
    else [96] ++ c ++ [96]
  | .latex f => latexShow f
  | .bold xs => bytes% "**" ++ plainInlines xs ++ bytes% "**"
  | .italic xs => [42] ++ plainInlines xs ++ [42]
  | .strike xs => bytes% "~~" ++ plainInlines xs ++ bytes% "~~"
  | .link xs url => [91] ++ plainInlines xs ++ bytes% "](" ++ url ++ [41]
  | .image url alt => bytes% "![" ++ alt ++ bytes% "](" ++ url ++ [41]
  | .footnoteRef id => bytes% "[^" ++ id ++ [93]
  | .lineBreak => [92, 10]
  | .htmlInline s => s
  | .value r => r
def plainInlines : List Inline → Bytes
  | [] => []
  | x :: xs => plainInline x ++ plainInlines xs
end

mutual
/-- `plain(io, x)` for a block, `render/plain.jl:3-112`. -/
def plainBlock : Block → Bytes
  | .para xs => plainInlines xs ++ [10]
  | .header l xs => List.replicate l 35 ++ [32] ++ plainInlines xs ++ [10]
  | .code lang c =>
    let t := List.replicate (max 2 (maxLineStartTicks c) + 1) 96
    t ++ lang ++ [10] ++ c ++ [10] ++ t ++ [10]
  | .latex f => bytes% "$$\n" ++ f ++ bytes% "\n$$\n"
  | .quote bs => prefixLines [62] (bytes% "> ") (plainBlocks bs) ++ [10]
  | .list items k loose => plainItems k loose 1 items
  | .hr => bytes% "---\n"
  | .admonition cat title bs =>
    let t := if title == uppercasefirst cat then [] else bytes% " \"" ++ title ++ [34]
    bytes% "!!! " ++ cat ++ t ++ [10] ++ prefixLines [] (bytes% "    ") (plainBlocks bs) ++ [10]
  | .footnote id bs =>
    let lines := splitNl (rstrip (plainBlocks bs))
    let head := bytes% "[^" ++ id ++ bytes% "]:"
    if lines.length == 1 then head ++ [32] ++ lines.headD [] ++ [10]
    else head ++ [10] ++ lines.flatMap (fun line =>
      (if line.isEmpty then [] else bytes% "    ") ++ line ++ [10]) ++ [10]
  | .htmlBlock first rest => (first :: rest).flatMap (· ++ [10])
  | .value r => r ++ [10]
/-- `plain(io, content::Vector)`: elements separated by newlines. -/
def plainBlocks : List Block → Bytes
  | [] => []
  | [b] => plainBlock b
  | b :: bs => plainBlock b ++ [10] ++ plainBlocks bs
/-- `plaintight(io, content::Vector)`, `render/plain.jl:58-65`: `plaintight(io, md)` prints a
paragraph without its trailing newline and any other block with `plain`. -/
def plainTight : List Block → Bytes
  | [] => []
  | [.para xs] => plainInlines xs
  | [b] => plainBlock b
  | .para xs :: bs => plainInlines xs ++ [10] ++ plainTight bs
  | b :: bs => plainBlock b ++ [10] ++ plainTight bs
/-- The item loop of `plain(io, ::List)`, `render/plain.jl:42-56`. -/
def plainItems (k : Int) (loose : Bool) : Nat → List (List Block) → Bytes
  | _, [] => []
  | i, it :: its =>
    let marker := if k ≥ 0 then intString (wrap64 (i + k - 1)) ++ bytes% ". " else bytes% "  * "
    let content := if loose then plainBlocks it else plainTight it
    marker ++ itemLines marker.length (splitNl (rstrip content)) ++ plainItems k loose (i + 1) its
end

/-- `plain(md)` for `md.content`. -/
def plain (md : List Block) : Bytes := plainBlocks md

end JuliaLean.Markdown

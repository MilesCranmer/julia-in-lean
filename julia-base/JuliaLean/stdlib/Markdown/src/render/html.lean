import JuliaLean.stdlib.Markdown.src.Common.block
import JuliaLean.stdlib.Markdown.src.IPython.IPython

/-!
# Markdown: printers

Models of `Markdown.html` (`stdlib/Markdown/src/render/html.jl`, `rich.jl`),
`Markdown.latex` (`render/latex.jl`, `IPython/IPython.jl`), `Markdown.rst`
(`render/rst.jl`) and `Markdown.plain` (`render/plain.jl`) at master
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`, over the tree of `JuliaLean.Markdown.Ast`. Output is a byte list;
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

end JuliaLean.Markdown

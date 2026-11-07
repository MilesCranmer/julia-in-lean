import JuliaLean.stdlib.Markdown.src.render.html

namespace JuliaLean.Markdown

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

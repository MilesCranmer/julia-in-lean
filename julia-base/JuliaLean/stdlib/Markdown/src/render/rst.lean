import JuliaLean.stdlib.Markdown.src.render.plain
import JuliaLean.stdlib.Markdown.src.render.latex

namespace JuliaLean.Markdown

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

end JuliaLean.Markdown

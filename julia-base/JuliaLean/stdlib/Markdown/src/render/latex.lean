import JuliaLean.stdlib.Markdown.src.render.html

namespace JuliaLean.Markdown

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

end JuliaLean.Markdown

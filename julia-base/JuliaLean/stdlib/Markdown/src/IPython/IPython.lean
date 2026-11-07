import JuliaLean.stdlib.Markdown.src.Common.inline

namespace JuliaLean.Markdown

/-- `tex(stream, md)`, `IPython/IPython.jl:7-11`: the formula of a `$`-delimited `LaTeX`. -/
def tex (isword : Nat → Bool) : M (Option Bytes) := parseInlineWrapper isword (C '$') 1 (rep := true)

/-- `blocktex(stream, md)`, `IPython/IPython.jl:13-23`. Pushes `LaTeX(formula)`. -/
def blocktex (isword : Nat → Bool) : M (Option Bytes) := withstreamOpt (tex isword)
/-- `show(io, ::LaTeX)`: `$formula$` (`IPython/IPython.jl:25-26`). -/
def latexShow (f : Bytes) : Bytes := [36] ++ f ++ [36]

end JuliaLean.Markdown

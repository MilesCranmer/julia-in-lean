import JuliaLean.base.expr


section

/-!
# `base/docs/core.jl`, `base/docs/utils.jl`, `base/docs/bindings.jl`, `base/docs/basedocs.jl`

Models of the bootstrap docsystem (`Core.CoreDocs`), the `HTML`/`Text` wrappers,
`Docs.Binding` and the `kw"..."` keyword literal, master `bbfa0ce4150`.
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-! ## `base/docs/basedocs.jl` -/

/-- `kw"text"`, `base/docs/basedocs.jl:11-13`: `Keyword(Symbol(text))`. -/
def kwStr (text : String) : JV := .keyword text

end JuliaLean.DocsSyntaxCov

end


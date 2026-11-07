import JuliaLean.Proofs.base.docs.Docs
import JuliaLean.Proofs.base.expr
import JuliaLean.Registry.Types
import JuliaLean.base.docs.basedocs
import JuliaLean.base.docs.bindings
import JuliaLean.base.docs.core
import JuliaLean.base.docs.utils


section

/-!
# Properties of `base/docs/core.jl`, `utils.jl`, `bindings.jl` and `basedocs.jl`
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-- `kw"text"` is the keyword `Keyword(Symbol(text))`. -/
def KwStrKeyword : Prop := ∀ t : String, kwStr t = .keyword t

theorem kwStrKeyword : KwStrKeyword := fun _ => rfl

end JuliaLean.DocsSyntaxCov

end

namespace JuliaLean.Proofs.base.docs.basedocs

open JuliaLean.Registry

open JuliaLean.DocsSyntaxCov in
open JuliaLean.Registry in
def entries : List Entry := [
  proven "docssyntaxcov-basedocs-keyword" "base/docs/basedocs.jl" ["kw_str"]
    "kw_str constructs the named documentation keyword."
    "base/docs/basedocs.jl:11-13" ``KwStrKeyword ``kwStrKeyword,
]

end JuliaLean.Proofs.base.docs.basedocs

import JuliaLean.Core
import JuliaLean.base.expr


section

/-!
# Julia values and `Expr` trees for the docsystem and `Base.Syntax` models

Model of the values that `base/docs/*.jl` and `base/syntax.jl` (master
`bbfa0ce4150`) take apart and build. A Julia `Expr` is `expr head args`, with
the head symbol's name as a `String`; `QuoteNode`, `GlobalRef`,
`LineNumberNode`, `Base.BaseDocs.Keyword` and the other atoms that these files
test with `isa` have their own constructors. Every other runtime value (a
module, a function, a type object) is `val name`, identified by a name.

Julia mutates `Expr` arguments in place in a few of these functions
(`x.args[i] = ...`); the models return the updated tree instead, which is
what the caller of each such function observes.
-/

namespace JuliaLean.DocsSyntaxCov

namespace JV

end JV

@[simp] theorem exc_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
@[simp] theorem exc_map_ok {ε α β : Type} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl
@[simp] theorem exc_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl
@[simp] theorem exc_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl

end JuliaLean.DocsSyntaxCov

end


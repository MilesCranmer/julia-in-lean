import JuliaLean.base.meta

namespace JuliaLean.ExprReflect

open JuliaLean

def QuotContract : Prop := ∀ ex, quot ex = .expr "quote" [ex]

def ShowSexprContract : Prop := ∀ head args,
  toSExpr (.expr head args) = .form head (args.map toSExpr)

end JuliaLean.ExprReflect

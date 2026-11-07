import JuliaLean.base.expr

namespace JuliaLean.ExprReflect

open JuliaLean

def CopyEqual : Prop := ∀ value fresh,
  eraseCopyIds (copyExprs fresh value) = eraseCopyIds value

def CopyIndependent : Prop := ∀ value fresh,
  allIdsBelow value fresh = true →
  idsDisjoint (copyIds value) (copyIds (copyExprs fresh value)) = true

def IsExprContract : Prop := ∀ head args heads arity,
  isExpr (.expr head args) heads arity =
    (heads.contains head && arity.all (args.length == ·))


def InlineContract : Prop := ∀ ex,
  annotateInline false ex = .expr "block" [
    .expr "inline" [.atom "true"],
    .expr "local" [.expr "=" [.atom "val", .expr "escape" [ex]]],
    .expr "inline" [.atom "false"],
    .atom "val"]

def GeneratedContract : Prop := ∀ signature body,
  annotateGenerated true signature body =
    .ok (.expr "escape" [.expr "function" [signature,
      .expr "if" [.expr "generated" [], body,
        .expr "block" [.expr "meta" [.atom "generated_only"],
          .expr "return" [.atom "nothing"]]]]])

end JuliaLean.ExprReflect

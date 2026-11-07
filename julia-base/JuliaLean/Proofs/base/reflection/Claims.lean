import JuliaLean.base.reflection

namespace JuliaLean.ExprReflect

open JuliaLean

def WhichHasMethod : Prop := ∀ table modules method,
  whichMethod table modules = some method → hasMethod table modules = true

def NameofContract : Prop := ∀ functionName, nameOf functionName = functionName

end JuliaLean.ExprReflect

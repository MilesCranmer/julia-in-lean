import JuliaLean.Runtime.Strings

namespace JuliaLean.base.io

open JuliaLean

inductive Error where
  | jl (error : JlError)
  | eofError
  | errorException (message : String)
  | foreignError (kind message : String)
  | showError (error : JuliaLean.Strings.ShowErrorKind)
  deriving DecidableEq

/-- Mutable IO computations retain mutations made before an exception. -/
abbrev M (World : Type) (A : Type) :=
  World → Option (Except (Error × World) (A × World))

instance {World : Type} : Monad (M World) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world => do
    match ← action world with
    | .error error => pure (.error error)
    | .ok (value, world) => next value world

instance {World : Type} : MonadExceptOf Error (M World) where
  throw error := fun world => some (.error (error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (error, world)) => handler error world

def getWorld {World : Type} : M World World := fun world => some (.ok (world, world))
def setWorld {World : Type} (world : World) : M World Unit := fun _ => some (.ok ((), world))
def liftJl {World A : Type} (value : Jl A) : M World A :=
  match value with
  | .ok result => pure result
  | .error error => throw (.jl error)

/-- Fuel-free source while-loop; `none` means an infinite execution. -/
def whileLoop {World S A : Type} (step : S → M World (Sum A S))
    (state : S) : M World A := fun world =>
  match step state world with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok (.inl result, world)) => some (.ok (result, world))
  | some (.ok (.inr next, world)) => whileLoop step next world
partial_fixpoint

end JuliaLean.base.io

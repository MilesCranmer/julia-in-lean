import JuliaLean.Core

/-!
An abstract execution environment for method-specific Base models. `Value`
represents every Julia value and type without restricting its concrete domain.
Calls are stateful and may throw, so a method model preserves the order of
dispatch, checks, mutation, and errors written in the Julia body.
-/

namespace JuliaLean.BroadcastCov.Exact

abbrev Value := Nat
abbrev World := Nat

inductive Error where
  | argumentError
  | boundsError
  | dimensionMismatch
  | methodError
  | errorException
  | other
  deriving Repr, DecidableEq

abbrev M := StateT World (Except Error)

structure Runtime where
  call : String → List Value → M Value
  truth : Value → Bool
  forEach : Value → (Value → M Unit) → M Unit
  whileDo : M Bool → M Unit → M Unit
  iterateUntil : Value → Value → (Value → Value → M Value) → M Value

def raise (error : Error) : M Value := fun _ => .error error

def call0 (rt : Runtime) (name : String) : M Value := rt.call name []
def call1 (rt : Runtime) (name : String) (a : Value) : M Value := rt.call name [a]
def call2 (rt : Runtime) (name : String) (a b : Value) : M Value := rt.call name [a, b]
def call3 (rt : Runtime) (name : String) (a b c : Value) : M Value := rt.call name [a, b, c]
def call4 (rt : Runtime) (name : String) (a b c d : Value) : M Value := rt.call name [a, b, c, d]

def decideCall (rt : Runtime) (name : String) (args : List Value) : M Bool := do
  return rt.truth (← rt.call name args)

end JuliaLean.BroadcastCov.Exact

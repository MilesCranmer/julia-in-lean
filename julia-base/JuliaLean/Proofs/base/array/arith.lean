import JuliaLean.base.array
import JuliaLean.src.genericmemory_c
import JuliaLean.Proofs.base.dict
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.base.cmem
import JuliaLean.Proofs.base.cmem
import JuliaLean.base.pointer
import JuliaLean.base.set
import JuliaLean.Proofs.base.set
import JuliaLean.base.multidimensional
import JuliaLean.base.indices
import JuliaLean.base.essentials
import JuliaLean.Proofs.base.array.common.convert
import JuliaLean.Proofs.base.array.common.copy

attribute [local instance] JuliaLean.Proofs.base.array.layoutAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection

open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion
open JuliaLean JuliaLean.base.array
open JuliaLean.Registry

/-- Colon reversal discovers firstindex then lastindex, passing the original
array and those exact endpoints to the selected reversing method. -/
def ReverseColonArguments : Prop :=
  ∀ (A : Type) (a : A) (first last : I)
    (initial : List Nat × List (A × I × I)),
    (reverseColon (m := StateM (List Nat × List (A × I × I)))
      (fun _ => do modify (fun s => (s.1 ++ [0], s.2)); pure first)
      (fun _ => do modify (fun s => (s.1 ++ [1], s.2)); pure last)
      (fun a s n => do modify (fun w => (w.1 ++ [2], w.2 ++ [(a, s, n)])); pure a)
      a).run initial =
        (a, (initial.1 ++ [0, 1, 2], initial.2 ++ [(a, first, last)]))

/-- A singleton dimension tuple preserves its integer unchanged. -/
def ReverseTupleArguments : Prop :=
  ∀ (A Z : Type) (a : A) (dim : Z) (initial : List (A × Z)),
    (reverseTupleDim (m := StateM (List (A × Z)))
      (fun a n => do modify (· ++ [(a, n)]); pure a) a (dim, ())).run initial =
        (a, initial ++ [(a, dim)])
end JuliaLean.Proofs.base.array.Completion


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
def entriesArith1 : List JuliaLean.Registry.Entry := [
{ id := "array-reverse-colon-arguments", juliaFile := "base/array.jl",
  juliaFns := ["$_f(A::AbstractVector, ::Colon)"],
  statement := "Colon reversal discovers firstindex then lastindex, passing the original array and those exact endpoints to the selected reversing method.",
  source := "base/array.jl:2267-2267", status := .todo,
  prop := ``JuliaLean.Proofs.base.array.Completion.ReverseColonArguments, thm := none,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-reverse-tuple-arguments", juliaFile := "base/array.jl",
  juliaFns := ["$_f(A::AbstractVector, dim::Tuple{Integer})"],
  statement := "A singleton dimension tuple preserves its integer unchanged.",
  source := "base/array.jl:2268-2268", status := .todo,
  prop := ``JuliaLean.Proofs.base.array.Completion.ReverseTupleArguments, thm := none,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." }
]
end JuliaLean.Proofs.base.array


import Lean

/-!
Property registry types.

Every property of Julia Base is a closed `Prop` constant (`prop`). A `proven`
entry names a theorem whose type is exactly `prop`; a `refuted` entry names a
theorem whose type is exactly `¬ prop` and a Julia reproducer
`repro/<id>.jl`. `Audit.lean` checks these types and the axioms each theorem
depends on.
-/

namespace JuliaLean.Registry

inductive Status where
  /-- Not yet settled. The audit fails while any entry is open. -/
  | todo
  | proven
  | refuted
  deriving Repr, BEq, DecidableEq

structure Entry where
  /-- Unique identifier, also used to name the reproducer `repro/<id>.jl`. -/
  id : String
  /-- Julia source file the property is about, e.g. `base/range.jl`. -/
  juliaFile : String
  /-- Julia functions and methods the property covers, e.g. `length(::StepRange)`. -/
  juliaFns : List String
  /-- Informal statement of the property. -/
  statement : String
  /-- Where Julia promises the property: a docstring, the manual, or "invariant". -/
  source : String
  status : Status
  /-- Closed `Prop` constant stating the property. -/
  prop : Lean.Name
  /-- Theorem proving `prop` (proven) or `¬ prop` (refuted). -/
  thm : Option Lean.Name := none
  /-- Refuted entries: existing JuliaLang/julia issue or PR numbers, or "none found". -/
  issue : String := ""
  /-- Notes, e.g. the counterexample or a difference between 1.13.2 and master. -/
  notes : String := ""

end JuliaLean.Registry

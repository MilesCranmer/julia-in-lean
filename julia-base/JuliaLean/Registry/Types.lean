import Lean

/-!
Property registry types.

Every property of Julia Base is a closed `Prop` constant (`prop`). A `proven`
entry names a theorem whose type is exactly `prop`; a `refuted` entry names a
theorem whose type is exactly `¬ prop`. Base refutations use a Julia reproducer
`repro/<id>.jl`; C-runtime refutations may instead record a formal model
counterexample. The audits check theorem types, evidence classes and axioms.
-/

namespace JuliaLean.Registry

inductive Status where
  /-- Not yet settled. `Audit.lean` lists open entries without failing; `CRuntimeAudit.lean`
  rejects them. -/
  | todo
  | proven
  | refuted
  deriving Repr, BEq, DecidableEq

inductive RefutationEvidence where
  | runtime
  | modelCounterexample
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
  /-- Evidence supporting a refutation. -/
  refutationEvidence : RefutationEvidence := .runtime
  /-- Closed `Prop` constant stating the property. -/
  prop : Lean.Name
  /-- Theorem proving `prop` (proven) or `¬ prop` (refuted). -/
  thm : Option Lean.Name := none
  /-- Refuted entries: existing JuliaLang/julia issue or PR numbers, or "none found". -/
  issue : String := ""
  /-- Notes, e.g. the counterexample or a difference between 1.13.2 and master. -/
  notes : String := ""

end JuliaLean.Registry

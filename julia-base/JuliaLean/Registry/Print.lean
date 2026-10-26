import JuliaLean.Registry.Types
import JuliaLean.Registry.Generality

namespace JuliaLean.Registry

open Lean Meta

/-- Print entries as tab-separated rows: id, status, number of universally
quantified data variables, Julia file, issue, statement. -/
def printRows (es : List Entry) : MetaM Unit := do
  for e in es do
    let status := match e.status with
      | .todo => "todo" | .proven => "proven" | .refuted => "refuted"
    let clean (s : String) := (s.replace "\t" " ").replace "\n" " "
    let n ← countForallData 6 (mkConst e.prop)
    IO.println s!"{e.id}\t{status}\t{n}\t{e.juliaFile}\t{clean e.issue}\t{clean e.statement}"

end JuliaLean.Registry

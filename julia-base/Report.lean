import JuliaLean

/-! Print the registry as tab-separated rows: id, status, number of universally
quantified data variables, Julia file, issue, statement. Run with
`lake env lean Report.lean > registry.tsv`. -/

open Lean Meta JuliaLean.Registry

#eval show MetaM Unit from do
  for e in JuliaLean.Registry.all do
    let status := match e.status with
      | .todo => "todo" | .proven => "proven" | .refuted => "refuted"
    let clean (s : String) := (s.replace "\t" " ").replace "\n" " "
    let n ← countForallData 6 (mkConst e.prop)
    IO.println s!"{e.id}\t{status}\t{n}\t{e.juliaFile}\t{clean e.issue}\t{clean e.statement}"

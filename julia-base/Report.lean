import JuliaLean
import JuliaLean.Registry.Print

/-! Print the registry as tab-separated rows with columns id, status,
quantified data variable count, Julia source file, issue, and statement (see
`JuliaLean.Registry.printRows`). Run with `lake env lean Report.lean > registry.tsv`. -/

#eval JuliaLean.Registry.printRows JuliaLean.Registry.all

import JuliaLean.Float.Validation

/-- Run with `lake env lean --run JuliaLean/Float/Check.lean release|nightly [start] [count]`.
Compare output with `julia repro/float-differential.jl`.
Optional indices divide the deterministic corpus into shorter commands. -/
def main (args : List String) : IO Unit :=
  JuliaLean.Float.Validation.differential
    (args[0]? == some "release")
    ((args[1]?.bind String.toNat?).getD 0)
    ((args[2]?.bind String.toNat?).getD 2194)

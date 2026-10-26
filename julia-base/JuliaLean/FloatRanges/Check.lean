import JuliaLean.FloatRanges.Validation

/-- Run with `lake env lean --run JuliaLean/FloatRanges/Check.lean [start] [count]` after
`lake build JuliaLean.FloatRanges.Validation`; compare with
`julia repro/floatranges-differential.jl`. -/
def main (args : List String) : IO Unit :=
  JuliaLean.FloatRanges.Validation.differential
    ((args[0]?.bind String.toNat?).getD 0)
    ((args[1]?.bind String.toNat?).getD 100000)

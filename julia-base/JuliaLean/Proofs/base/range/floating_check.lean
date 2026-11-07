import JuliaLean.Proofs.base.range.floating_validation

/-- Run with `lake env lean --run JuliaLean/Proofs/base/range/floating_check.lean [start] [count]` after
`lake build JuliaLean.Proofs.base.range.floating_validation`; compare with
`julia repro/floatranges-differential.jl`. -/
def main (args : List String) : IO Unit :=
  JuliaLean.FloatRanges.Validation.differential
    ((args[0]?.bind String.toNat?).getD 0)
    ((args[1]?.bind String.toNat?).getD 100000)

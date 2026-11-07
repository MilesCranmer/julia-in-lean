import JuliaLean.Proofs.base.float.Validation

/-- Run with `lake env lean --run JuliaLean/Proofs/base/float/Check.lean release|nightly [start] [count]`.
Compare output with `julia repro/float-differential.jl`.
Optional indices divide the deterministic corpus into smaller runs. -/
def main (args : List String) : IO Unit :=
  JuliaLean.Float.Validation.differential
    (args[0]? == some "release")
    ((args[1]?.bind String.toNat?).getD 0)
    ((args[2]?.bind String.toNat?).getD 2194)

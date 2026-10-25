import JuliaLean.Float.Validation

/-- Run with `lake env lean --run JuliaLean/Float/Check.lean release|nightly [start] [count]`.
Compare output with `julia repro/float-differential.jl` on the matching Julia version
(`release` is 1.13.2, `nightly` is master). Optional indices select a slice of the
deterministic corpus. -/
def main (args : List String) : IO Unit :=
  JuliaLean.Float.Validation.differential
    (args[0]? == some "release")
    ((args[1]?.bind String.toNat?).getD 0)
    ((args[2]?.bind String.toNat?).getD 2194)

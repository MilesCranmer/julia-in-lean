import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Julia's requested extent and the C array extent for
`jl_gc_page_utilization_stats`, `base/timing.jl:148-152`,
`src/gc-stock.c:942`, and `src/gc-mmtk/gc-mmtk.c:1433-1434`. -/
def gcPageUtilizationRequested : Nat := 51

def gcPageUtilizationStorage : List Unit := List.replicate 51 ()

/-- Julia's reason names and the matching C storage for
`jl_full_sweep_reasons`, `base/timing.jl:157-183` and
`src/gc-stock.h:571-579`. -/
def fullSweepReasonNames : List Nat := [0, 1, 2, 3, 4]

def fullSweepReasonStorage : List Unit := List.replicate 5 ()

/-- Both `unsafe_wrap` calls use extents computed by their matching Julia and C
constants. The later reason reads use indices from `enumerate(names)`. -/
def TimingGlobalsSafe : Prop :=
  gcPageUtilizationRequested ≤ gcPageUtilizationStorage.length ∧
  fullSweepReasonNames.length ≤ fullSweepReasonStorage.length ∧
  ∀ i ∈ oneBasedLoop fullSweepReasonNames.length,
    inOneBased fullSweepReasonStorage.length i

theorem timingGlobalsSafe_proven : TimingGlobalsSafe := by
  constructor
  · decide
  constructor
  · decide
  · intro i hi
    simp only [oneBasedLoop, fullSweepReasonNames, List.length_cons,
      List.length_nil, Nat.reduceAdd, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp [inOneBased, fullSweepReasonStorage]
    omega

end JuliaLean.MemSafety.G3

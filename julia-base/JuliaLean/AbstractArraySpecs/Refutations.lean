import JuliaLean.AbstractArraySpecs.Props

namespace JuliaLean.AbstractArraySpecs

/-- A 1×1 `IndexCartesian` array with axes `(5:5, 5:5)`. -/
def zeroIndexWitness : Arr Int := ⟨[⟨.unit, i64 5, i64 5⟩, ⟨.unit, i64 5, i64 5⟩], .cartesian, [7]⟩


/-- Two linear-style arrays of sizes 2×3 and 3×2. -/
def linear23 : Arr Int := ⟨[oneTo (i64 2), oneTo (i64 3)], .linear, [1, 2, 3, 4, 5, 6]⟩
def linear32 : Arr Int := ⟨[oneTo (i64 3), oneTo (i64 2)], .linear, [1, 2, 3, 4, 5, 6]⟩

/-- `eachindex` compares only `eachindex(IndexLinear(), X)`, which is `OneTo(6)` for
both, so it returns instead of throwing. -/
theorem eachindexSizeMismatch_refuted : ¬ EachindexSizeMismatch := by
  intro h
  have bad := h linear23 linear32 (by decide) (by decide) (by decide)
  revert bad
  decide

/-- An offset vector with axis `3:4` and a 1-based vector. -/
def catX : Arr Int := ⟨[⟨.unit, i64 3, i64 4⟩], .linear, [1, 2]⟩
def catY : Arr Int := ⟨[oneTo (i64 2)], .linear, [3, 4]⟩

/-- Block-diagonal `cat(catX, catY; dims=(1, 2))` writes `catX` into rows 3:4, where
`catY` then lands too: `[0 0; 0 0; 1 3; 2 4]` instead of `[1 0; 2 0; 0 3; 0 4]`. -/
theorem catOffsetInvariant_refuted : ¬ CatOffsetInvariant := by
  intro h
  have run : catKw 0 [.arr catX, .arr catY] [1, 2] =
      .ok ⟨[i64 4, i64 2], [some 0, some 0, some 1, some 2, some 0, some 0, some 3, some 4]⟩ := by
    decide
  have bad := h [1, 2] catX catY _ (by decide) (by decide) run
  revert bad
  decide

end JuliaLean.AbstractArraySpecs

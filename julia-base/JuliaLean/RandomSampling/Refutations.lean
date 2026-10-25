import JuliaLean.RandomSampling.Props

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 5000

namespace JuliaLean.RandomSampling

open JuliaLean JuliaLean.Float

/-- An RNG whose every answer is zero (the `ZeroWords` RNG of the reproducer). -/
def zeroRng : Rng Unit where
  next _ q := match q with
    | .int u => ((JInt.wrap u 0 : JInt u), ())
    | .raw52 => ((JInt.wrap .u64 0 : JInt .u64), ())

/-- An RNG answering `0, typemax, 0, ...` (the `AlternatingWords` RNG of the reproducer). -/
def alternatingRng : Rng Nat where
  next st q := match q with
    | .int u => ((JInt.wrap u (if st % 2 = 0 then 0 else 2 ^ 64 - 1) : JInt u), st + 1)
    | .raw52 => ((JInt.wrap .u64 (if st % 2 = 0 then 0 else 2 ^ 64 - 1) : JInt .u64), st + 1)

/-- `typemin(Int):1:typemax(Int)` is non-empty, but its length wraps to 0 and the index
sampler over `1:0` throws. -/
theorem stepRangeSamplerNonempty_refuted : ¬ StepRangeSamplerNonempty := by
  intro h
  have hr : Ranges.stepRange ⟨.bit .i64, JInt.typemin .i64⟩ ⟨.bit .i64, JInt.lit .i64 1⟩
      ⟨.bit .i64, JInt.typemax .i64⟩ =
      .ok ⟨.step, ⟨.bit .i64, JInt.typemin .i64⟩, ⟨.bit .i64, JInt.lit .i64 1⟩,
        ⟨.bit .i64, JInt.typemax .i64⟩⟩ := by decide
  exact h _ _ _ _ hr (by decide) emptyCollectionError (by decide)

/-- `String(UInt8[0x80])`: `isvalid(s, 1)` holds, but the sampler rejects position 1. -/
theorem stringSamplerAcceptsValid_refuted : ¬ StringSamplerAcceptsValid := by
  intro h
  have hh := h ⟨[0x80], by decide⟩ (JInt.lit .i64 1) (by decide) (by decide)
  revert hh
  decide

/-- `randstring(rng, UInt8[0xc3, 0xa9], 2)` with words `0, typemax` is `"é"`, of length 1. -/
theorem randstringCharacterLength_refuted : ¬ RandstringCharacterLength := by
  intro h
  have hh := h Nat alternatingRng 0 [0xc3, 0xa9] 2 0 [0xc3, 0xa9] 2 (by decide) (by decide)
    (by decide) (by decide)
  revert hh
  decide

/-- `randsubseq(rng, [10, 20, 30], 0.1)` with zero words: `randexp` returns `0.0`, the
skip `ceil(Int, 0.0)` is 0, and `A[0]` throws `BoundsError`. -/
theorem randsubseqTotal_refuted : ¬ RandsubseqTotal := by
  intro h
  have hrun : randsubseq zeroRng 1 [10, 20, 30] (F64.ofBits 0x3fb999999999999a) () =
      some (.error .boundsError) := by decide
  obtain ⟨_, _, hc⟩ := h Unit zeroRng 1 [10, 20, 30] (F64.ofBits 0x3fb999999999999a) ()
    (.error .boundsError) (by decide) (by decide) (by decide) hrun
  cases hc

end JuliaLean.RandomSampling

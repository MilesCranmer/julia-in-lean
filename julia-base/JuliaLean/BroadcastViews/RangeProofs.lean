import JuliaLean.BroadcastViews.Ranges

/-! Properties of broadcasting over ranges, and their refutations. -/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- `r1 .+ r2` for two `UnitRange{Int}`s equals broadcasting over the collected vectors: a
length-1 range is expanded, and only unequal non-singleton lengths throw `DimensionMismatch`. -/
def RangeBroadcastPair : Prop :=
  ∀ r1 r2 : URange, bcAddRanges r1 r2 = bcAddVectors r1.elems r2.elems

/-- `x .\ r` returns a range for every floating-point colon range `r = a:s:b`. -/
def RangeLdivTotal : Prop :=
  ∀ t : FloatT, ∃ f, bcLdivRange (colonRefT t) = .ok f

/-- `r .- x` for an unsigned `StepRange{UInt64,UInt64}` `r` and an integral `x::Float64` has the
elements `r[i] - x` of `collect(r) .- x` (for small values, where every `Float64` operation is
exact). -/
def RangeUnsignedFloat : Prop :=
  ∀ (a s n : U64) (x : Int) (i : Nat), 1 ≤ s.val → 1 ≤ i → (i : Int) ≤ n.val →
    a.val + (n.val - 1) * s.val < 2 ^ 20 → -2 ^ 20 < x → x < 2 ^ 20 →
    bcSubFloatElem a s n x i = .ok (a.val + ((i : Int) - 1) * s.val - x)

/-- `.-r` for `r::UnitRange{UInt8}` has the elements of `.-collect(r)` (each negated with
wrapping). -/
def RangeNegUnsigned : Prop :=
  ∀ lo hi : U8, bcNegU8 lo hi = .ok ((urange8Elems lo hi).map (fun v => -v))

/-- `(1:3) .+ (5:5)` throws `DimensionMismatch`; `[1, 2, 3] .+ [5]` is `[6, 7, 8]`. -/
theorem rangePair_example :
    bcAddRanges ⟨i64 1, i64 3⟩ ⟨i64 5, i64 5⟩ = .error .dimensionMismatch ∧
    bcAddVectors (URange.elems ⟨i64 1, i64 3⟩) (URange.elems ⟨i64 5, i64 5⟩) = .ok [i64 6, i64 7, i64 8] := by
  decide

theorem rangeBroadcastPair_refuted : ¬ RangeBroadcastPair := by
  intro h
  have := h ⟨i64 1, i64 3⟩ ⟨i64 5, i64 5⟩
  rw [rangePair_example.1, rangePair_example.2] at this
  exact absurd this (by decide)

/-- `2.0 .\ (0.0:0.5:2.0)` throws `MethodError` (`adjoint(::TwicePrecision{Float64})`). -/
theorem rangeLdiv_example : bcLdivRange (colonRefT .f64) = .error .methodError := by decide

theorem rangeLdivTotal_refuted : ¬ RangeLdivTotal := by
  intro h
  obtain ⟨f, hf⟩ := h .f64
  rw [rangeLdiv_example] at hf
  cases hf

/-- `(UInt(1):UInt(2):UInt(5)) .- 2.0` has first element `2^65 - 1` (printed
`3.6893488147419103e19`) instead of `-1.0`: `imin = 2`, `ref_n = 1`, and `u = 0x1 - 0x2` wraps. -/
theorem rangeUnsignedFloat_example :
    bcSubFloatElem (JInt.lit .u64 1) (JInt.lit .u64 2) (JInt.lit .u64 3) 2 1 = .ok (2 ^ 65 - 1) := by
  decide

theorem rangeUnsignedFloat_refuted : ¬ RangeUnsignedFloat := by
  intro h
  have := h (JInt.lit .u64 1) (JInt.lit .u64 2) (JInt.lit .u64 3) 2 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [rangeUnsignedFloat_example] at this
  exact absurd this (by decide)

/-- `.-(0x00:0x02)` is the empty `0x00:-1:0x01`; `.-collect(0x00:0x02) == [0x00, 0xff, 0xfe]`. -/
theorem rangeNegUnsigned_example :
    bcNegU8 (JInt.lit .u8 0) (JInt.lit .u8 2) = .ok [] ∧
    (urange8Elems (JInt.lit .u8 0) (JInt.lit .u8 2)).map (fun v => -v) =
      [JInt.lit .u8 0, JInt.lit .u8 255, JInt.lit .u8 254] := by
  decide

theorem rangeNegUnsigned_refuted : ¬ RangeNegUnsigned := by
  intro h
  have := h (JInt.lit .u8 0) (JInt.lit .u8 2)
  rw [rangeNegUnsigned_example.1, rangeNegUnsigned_example.2] at this
  exact absurd this (by decide)

end JuliaLean.BroadcastViews

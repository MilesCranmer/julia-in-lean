import JuliaLean.FloatRanges.Properties

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-!
`show(io, r::StepRangeLen)` for `StepRangeLen{Float64,TwicePrecision{Float64},
TwicePrecision{Float64},Int}` (the FloatRanges model `SRL`), `base/range.jl:1132-1138`
at Julia master `bbfa0ce4150`, and whether evaluating the printed text rebuilds the
range's elements.

`repr(x::Float64)` prints the shortest decimal that parses back to `x`
(`Ryu.writeshortest`, `base/ryu/Ryu.jl`), and `repr(n::Int)` prints `n` exactly. No
theorem in `JuliaLean.ParsePrint` proves this round trip, so `RangeText` records the
printed values themselves: evaluating `repr(a):repr(s):repr(b)` is modelled as the
Float64 colon constructor `FloatRanges.colon a s b` applied to the exact values. The
differential test reads the values back from Julia's
`repr(r)` text and checks them against this model.
-/

namespace JuliaLean.Show

open JuliaLean.Float JuliaLean.FloatRanges

/-- The text printed by `show(io, r::StepRangeLen)`, with each `repr` kept as the value
it denotes: `repr(first):repr(step):repr(last)` (`base/range.jl:1134`) or
`StepRangeLen(repr(first), repr(step), repr(length))` (`base/range.jl:1137`). -/
inductive RangeText where
  | colon (first step last : F64)
  | ctor (first step : F64) (len : I64)
  deriving DecidableEq, Repr

/-- `show(io, r::StepRangeLen)`, `base/range.jl:1132-1138`; `iszero(x) = x == zero(x)`,
`base/number.jl:44`; `first`, `step`, `last`, `length` are `SRL.first`
(`base/range.jl:869`), `SRL.stepF` (`base/twiceprecision.jl:438`), `SRL.last`
(`base/range.jl:878`) and `SRL.length` (`base/range.jl:807`). -/
def showSRL (r : SRL) : RangeText :=
  if !F64.eq r.stepF fzero then .colon r.first r.stepF r.last
  else .ctor r.first r.stepF r.length

/-- `UnitRange{Int}`, `base/range.jl:425-429`. -/
structure UnitRangeInt where
  start : I64
  stop : I64
  deriving DecidableEq, Repr

/-- `start:stop` for `Int`, `base/range.jl:5,428`; `unitrange_last`,
`base/range.jl:439-441`, with `_range_wrapping_sub(x, y) = x -% y`, `base/range.jl:36`. -/
def unitRange (start stop : I64) : UnitRangeInt :=
  ⟨start, if stop.val ≥ start.val then stop else start - i64 1⟩

/-- `length(r::AbstractUnitRange{Int})`, `base/range.jl:794-805`: `1 + (stop - start)`,
wrapping. -/
def UnitRangeInt.length (r : UnitRangeInt) : I64 := i64 1 + (r.stop - r.start)

/-- `r .* x` for `r::OrdinalRange` and `x::Float64`, `base/broadcast.jl:1226-1227`:
`range_start_step_length(first(r)*x, step(r)*x, length(r))`. `first(r)` is `r.start`
(`base/range.jl:867`), `step(r)` is `1` (`base/range.jl:736`), and `Int * Float64`
converts the `Int` to `Float64` (`base/promotion.jl:455`); the `Float64` method is
`FloatRanges.rangeStartStepLength` (`base/twiceprecision.jl:450-466`). -/
def unitRangeMulF (r : UnitRangeInt) (x : F64) : Jl SRL :=
  rangeStartStepLength (F64.mul (flt r.start) x) (F64.mul (flt (i64 1)) x) r.length

/-- Evaluating the printed text of a nonempty Float64 `StepRangeLen` that prints in colon
form, `a:s:b`, gives back the same elements: the same length and bitwise-identical
(`isequal`) Float64 values at every index, whenever the evaluation returns. -/
def RangeReprElements : Prop := ∀ r : SRL,
  1 ≤ r.len.val → 1 ≤ r.offset.val → r.offset.val ≤ r.len.val →
  ∀ a s b : F64, showSRL r = .colon a s b →
  okThen (colon a s b) (fun r' => r'.len = r.len ∧
    ∀ i : I64, 1 ≤ i.val → i.val ≤ r.len.val → r'.get i = r.get i)

/-- `(0:5) .* 0.1 .+ 0.3`, as Julia 1.13.2 and master hold it (`dump(r)`): `ref` is
`TwicePrecision(0.3, 0.0)`, `step` is
`TwicePrecision(0.09999999999999987, 1.3322676295501878e-16)`, `len = 6`, `offset = 1`. -/
def scaledRange : SRL :=
  ⟨⟨F64.ofBits 0x3fd3333333333333, F64.ofBits 0⟩,
    ⟨F64.ofBits 0x3fb9999999999990, F64.ofBits 0x3ca3333333333333⟩, i64 6, i64 1⟩

/-- The model builds `scaledRange` from `(0:5) .* 0.1 .+ 0.3`: `r .* x` is
`unitRangeMulF`, then `r .+ x` is `SRL.addScalar` (`base/broadcast.jl:1192-1193`). -/
theorem scaledRange_eq :
    ((unitRangeMulF (unitRange (i64 0) (i64 5)) (dec 1 10)).bind
      (fun r => r.addScalar (dec 3 10))) = .ok scaledRange := by
  decide +kernel

/-- `repr((0:5) .* 0.1 .+ 0.3) == "0.3:0.1:0.8"`, yet its second element is
`0.39999999999999997` while the second element of `0.3:0.1:0.8` is `0.4`. -/
theorem scaledRange_second :
    showSRL scaledRange = .colon (dec 3 10) (dec 1 10) (dec 8 10) ∧
    scaledRange.get (i64 2) = .ok (F64.ofBits 0x3fd9999999999999) ∧
    F64.ofBits 0x3fd9999999999999 = dec 39999999999999997 (10^17) ∧
    (colon (dec 3 10) (dec 1 10) (dec 8 10)).bind (fun r => r.get (i64 2)) = .ok (dec 4 10) := by
  decide +kernel

theorem rangeReprElements_refuted : ¬ RangeReprElements := by
  intro h
  have hh := h scaledRange (by decide) (by decide) (by decide) (dec 3 10) (dec 1 10) (dec 8 10)
    (by decide +kernel)
  have h2 : okThen (colon (dec 3 10) (dec 1 10) (dec 8 10))
      (fun r' => r'.get (i64 2) = scaledRange.get (i64 2)) := by
    revert hh
    unfold okThen
    split
    · exact fun hh => hh.2 (i64 2) (by decide) (by decide)
    · exact fun _ => trivial
  exact absurd h2 (by decide +kernel)

end JuliaLean.Show

import JuliaLean.RangesCov.Log

/-!
One registry entry per `base/range.jl` method for the integer-range models of
`Colon`, `Access`, `Compare` and `Ops`: each property is about one method's model and is
proven from the corresponding conjunct of the area-level theorem.
-/

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

namespace Methods

open Colon Access Compare Ops

/-- `OneTo{T}(stop)` (base/range.jl:487-491) and `OneTo(stop::T)` (base/range.jl:505): for a
non-Bool integer `n` the result is a OneTo storing `max(0, n)` (invariant `stop >= 0`);
a Bool stop throws ArgumentError (`throwbool`, base/range.jl:488). -/
def OneToStop : Prop :=
  (∀ t : IntTy, ∀ x : JInt t, ∃ r, oneTo (mkI t x) = .ok r ∧ r.kind = .oneTo ∧
    0 ≤ r.stop.val ∧ (0 ≤ x.val → r.stop.val = x.val) ∧ (x.val < 0 → r.stop.val = 0)) ∧
  (∀ b : Bool, ThrowsArg (oneTo ⟨.bool, b⟩))

theorem oneToStop_proven : OneToStop := ⟨oneToConstruction_proven.1, oneToConstruction_proven.2.1⟩

/-- `OneTo{T}(r::AbstractRange)` (base/range.jl:493-501) throws ArgumentError
(`throwstart`/`throwstep`) unless `first(r) == 1` and `step(r) == 1`. -/
def OneToOfRangeChecks : Prop :=
  (∀ T r, (Ranges.first r).val ≠ 1 → ThrowsArg (oneToOfRange T r)) ∧
  (∀ T r, (Ranges.first r).val = 1 → (Ranges.step r).val ≠ 1 → ThrowsArg (oneToOfRange T r))

theorem oneToOfRangeChecks_proven : OneToOfRangeChecks :=
  ⟨oneToConstruction_proven.2.2.1, oneToConstruction_proven.2.2.2.1⟩

/-- `unchecked_oneto(stop)` (base/range.jl:503) stores its argument unchanged. -/
def UncheckedOnetoStop : Prop := ∀ n : Num, (uncheckedOneto n).stop = n

theorem uncheckedOnetoStop_proven : UncheckedOnetoStop := oneToConstruction_proven.2.2.2.2.2

/-- `StepRange{T,S}(start, step, stop)` (base/range.jl:344-349) through
`StepRange(start::T, step::S, stop::T)`: a zero step throws ArgumentError and
`a:s:a` is the one-element range `a:s:a`. -/
def StepRangeZeroAndSingle : Prop :=
  (∀ a s b : Num, a.ty = b.ty → s.val = 0 → ThrowsArg (stepRangeOuter a s b)) ∧
  (∀ a s : Num, s.val ≠ 0 → stepRangeOuter a s a = .ok ⟨.step, a, s, a⟩)

theorem stepRangeZeroAndSingle_proven : StepRangeZeroAndSingle :=
  ⟨stepRangeConstruction_proven.1, stepRangeConstruction_proven.2.1⟩

/-- `UnitRange{T}(start::T, stop::T)` with `unitrange_last(::Integer, ::Integer)`
(base/range.jl:428, 431, 439-441): integer `a:b` keeps `b` when `a <= b`, and otherwise
stores `a - 1` and is empty (docstring of `(:)`, base/range.jl:54-55). -/
def IntegerUnitRange : Prop :=
  ∀ t : IntTy, ∀ x y : JInt t, ∀ r, unitRangeSame (mkI t x) (mkI t y) = .ok r →
    r.start = mkI t x ∧ (x.val ≤ y.val → r.stop = mkI t y) ∧
    (y.val < x.val → r.stop.val = x.val - 1 ∧ r.stop.ty = .bit t ∧ Ranges.isEmpty r = true)

theorem integerUnitRange_proven : IntegerUnitRange := unitRangeConstruction_proven.1

/-- `length(r::AbstractRange) = error("length implementation missing")`, base/range.jl:705. -/
def LengthFallbackThrows : Prop :=
  ∀ (α : Type) (r : α), lengthFallback r = .error (.errorException "length implementation missing")

theorem lengthFallbackThrows_proven : LengthFallbackThrows := rangeFallbacks_proven.1

/-- `size(r::AbstractRange) = (length(r),)`, base/range.jl:706: one dimension, the length. -/
def SizeIsLength : Prop :=
  ∀ (α β : Type) (len : α → JlX β) (r : α), size len r = (len r).map (fun n => [n])

theorem sizeIsLength_proven : SizeIsLength := rangeFallbacks_proven.2.1

/-- `has_offset_axes(::StepRange) = false`, base/range.jl:747: StepRanges are 1-based. -/
def StepRangeNoOffset : Prop := ∀ r : Rng, hasOffsetAxesStep r = false

theorem stepRangeNoOffset_proven : StepRangeNoOffset := rangeFallbacks_proven.2.2.1

/-- `copy(r::AbstractRange) = r` (base/range.jl:923) and `getindex(r, ::Colon) = copy(r)`
(base/range.jl:1000): ranges are immutable, so the copy is the range itself. -/
def CopyIsIdentity : Prop := ∀ (α : Type) (r : α), copy r = r ∧ getindexColon r = r

theorem copyIsIdentity_proven : CopyIsIdentity := rangeFallbacks_proven.2.2.2

/-- `isempty(r::AbstractUnitRange) = first(r) > last(r)`, base/range.jl:711: a constructed
integer `a:b` is empty exactly when `b < a`. -/
def IsemptyUnitRange : Prop :=
  ∀ t : IntTy, ∀ x y : JInt t, ∀ r, unitRangeSame (mkI t x) (mkI t y) = .ok r →
    (isemptyUnit r = true ↔ y.val < x.val)

theorem isemptyUnitRange_proven : IsemptyUnitRange := isemptyMethods_proven.2.2.1

/-- `isempty(r::LinRange) = length(r) == 0`, base/range.jl:713. -/
def IsemptyLinRange : Prop := ∀ r : FloatRanges.Lin, isemptyLin r = true ↔ r.len.val = 0

theorem isemptyLinRange_proven : IsemptyLinRange := isemptyMethods_proven.2.2.2

/-- `step(r::AbstractUnitRange{T}) = oneunit(T) - zero(T)`, base/range.jl:736: the step of
a unit range is 1 of the element type (step docstring). -/
def StepUnitRange : Prop := ∀ t : IntTy, (stepUnit (.bit t)).val = 1 ∧ (stepUnit (.bit t)).ty = .bit t

theorem stepUnitRange_proven : StepUnitRange := stepMethods_proven.2.1

/-- `length(r::AbstractUnitRange{<:smallints})` and `checked_length` of it
(base/range.jl:859,862): a nonempty `a:b` has `Int(b) - Int(a) + 1` elements. -/
def LengthSmallUnit : Prop :=
  ∀ t : IntTy, t.bits < 64 → ∀ x y : JInt t, x.val ≤ y.val →
    ∃ n, lengthUnitSmall ⟨.unit, mkI t x, Ranges.Num.one (.bit t), mkI t y⟩ = .ok n ∧
      n.val = y.val - x.val + 1 ∧ n.ty = .bit .i64 ∧
      Ranges.length ⟨.unit, mkI t x, Ranges.Num.one (.bit t), mkI t y⟩ = .ok n ∧
      Ranges.checkedLength ⟨.unit, mkI t x, Ranges.Num.one (.bit t), mkI t y⟩ = .ok n

theorem lengthSmallUnit_proven : LengthSmallUnit := lengthMethods_proven.1

/-- `length(r::OneTo)` (base/range.jl:806) and its big-integer method (base/range.jl:817):
the length of `OneTo(n)` with `n >= 0` is `n`. -/
def LengthOneTo : Prop :=
  ∀ t : IntTy, ∀ x : JInt t, 0 ≤ x.val →
    (lengthOneTo ⟨.oneTo, Ranges.Num.one (.bit t), Ranges.Num.one (.bit t), mkI t x⟩).val = x.val ∧
    lengthOneToBig ⟨.oneTo, Ranges.Num.one (.bit t), Ranges.Num.one (.bit t), mkI t x⟩ = mkI t x

theorem lengthOneTo_proven : LengthOneTo := lengthMethods_proven.2.1

/-- `firstindex(::StepRange{<:smallints,<:bitints}) = 1` and the big-integer method
(base/range.jl:850,864): ranges are 1-based. -/
def FirstindexOne : Prop := ∀ r : Rng, (firstindexSmall r).val = 1 ∧ (firstindexBig r).val = 1

theorem firstindexOne_proven : FirstindexOne := lengthMethods_proven.2.2.2.2

/-- `first(r::OneTo{T}) = oneunit(T)`, base/range.jl:868. -/
def FirstOneTo : Prop :=
  ∀ t : IntTy, ∀ r : Rng, r.stop.ty = .bit t → (firstOneTo r).val = 1 ∧ (firstOneTo r).ty = .bit t

theorem firstOneTo_proven : FirstOneTo := endpointMethods_proven.1

/-- `first(r::OneTo, n::Integer)`, base/range.jl:872-875, throws ArgumentError for `n < 0`. -/
def FirstOneToNegative : Prop := ∀ (r : Rng) (n : Num), n.val < 0 → ThrowsArg (firstOneToN r n)

theorem firstOneToNegative_proven : FirstOneToNegative := endpointMethods_proven.2.2.1

/-- `minimum(r::AbstractUnitRange)`, base/range.jl:881: ArgumentError when empty, else `first(r)`. -/
def MinimumUnit : Prop :=
  ∀ r : Rng, (isemptyUnit r = true → ThrowsArg (minimumUnit r)) ∧
    (isemptyUnit r = false → minimumUnit r = .ok (Ranges.first r))

theorem minimumUnit_proven : MinimumUnit := fun r =>
  ⟨fun h => (endpointMethods_proven.2.2.2.2.1 r h).1, fun h => (endpointMethods_proven.2.2.2.2.2 r h).1⟩

/-- `maximum(r::AbstractUnitRange)`, base/range.jl:882: ArgumentError when empty, else `last(r)`. -/
def MaximumUnit : Prop :=
  ∀ r : Rng, (isemptyUnit r = true → ThrowsArg (maximumUnit r)) ∧
    (isemptyUnit r = false → maximumUnit r = .ok (Ranges.last r))

theorem maximumUnit_proven : MaximumUnit := fun r =>
  ⟨fun h => (endpointMethods_proven.2.2.2.2.1 r h).2, fun h => (endpointMethods_proven.2.2.2.2.2 r h).2⟩

/-- `argmin(r::AbstractRange)`, base/range.jl:893-901: ArgumentError when empty; `1` for an
increasing range and `lastindex(r)` otherwise. -/
def ArgminRange : Prop :=
  (∀ r : Rng, Ranges.isEmpty r = true → ThrowsArg (argmin r)) ∧
  (∀ r : Rng, Ranges.isEmpty r = false → (Ranges.step r).val > 0 → argmin r = .ok (Ranges.Num.lit (.bit .i64) 1)) ∧
  (∀ r : Rng, Ranges.isEmpty r = false → ¬ (Ranges.step r).val > 0 → argmin r = Ranges.length r)

theorem argminRange_proven : ArgminRange :=
  ⟨fun r h => (argExtremaMethods_proven.1 r h).1, fun r h hs => (argExtremaMethods_proven.2.1 r h hs).1,
    fun r h hs => (argExtremaMethods_proven.2.2 r h hs).1⟩

/-- `argmax(r::AbstractRange)`, base/range.jl:910-918: ArgumentError when empty;
`lastindex(r)` for an increasing range and `1` otherwise. -/
def ArgmaxRange : Prop :=
  (∀ r : Rng, Ranges.isEmpty r = true → ThrowsArg (argmax r)) ∧
  (∀ r : Rng, Ranges.isEmpty r = false → (Ranges.step r).val > 0 → argmax r = Ranges.length r) ∧
  (∀ r : Rng, Ranges.isEmpty r = false → ¬ (Ranges.step r).val > 0 → argmax r = .ok (Ranges.Num.lit (.bit .i64) 1))

theorem argmaxRange_proven : ArgmaxRange :=
  ⟨fun r h => (argExtremaMethods_proven.1 r h).2, fun r h hs => (argExtremaMethods_proven.2.1 r h hs).2,
    fun r h hs => (argExtremaMethods_proven.2.2 r h hs).2⟩

/-- `iterate(r::Union{StepRangeLen,LinRange}, i)`, base/range.jl:928-933: from state `k`
the next element is `r[k+1]` while `k + 1 <= length(r)`, and iteration stops after
`length(r)` elements. -/
def IterateFloatRanges : Prop :=
  (∀ (r : FloatRanges.SRL) (k : I64), 0 ≤ k.val → k.val < IntTy.i64.max →
    iterateSrl r k = if r.len.val < k.val + 1 then none
      else some (r.unsafeGet (k + FloatRanges.i64 1), k + FloatRanges.i64 1)) ∧
  (∀ (r : FloatRanges.Lin) (k : I64), iterateLin r k = if r.len.val < (k + FloatRanges.i64 1).val then none
      else some (r.unsafeGet (k + FloatRanges.i64 1), k + FloatRanges.i64 1)) ∧
  (∀ (r : FloatRanges.SRL) (k : I64), 0 ≤ k.val → k.val < IntTy.i64.max → r.len.val ≤ k.val →
    iterateSrl r k = none)

theorem iterateFloatRanges_proven : IterateFloatRanges :=
  ⟨iterateMethods_proven.1, iterateMethods_proven.2.1, iterateMethods_proven.2.2.1⟩

/-- `isassigned(r::AbstractRange, i::Integer)`, base/range.jl:946-949: Bool indices throw
ArgumentError; otherwise the result is `1 <= i <= length(r)`. -/
def IsassignedRange : Prop :=
  (∀ (r : Rng) (b : Bool), ThrowsArg (isassigned r ⟨.bool, b⟩)) ∧
  (∀ (r : Rng) (i n : Num), i.ty ≠ .bool → Ranges.length r = .ok n →
    isassigned r i = .ok (decide (1 ≤ i.val ∧ i.val ≤ n.val)))

theorem isassignedRange_proven : IsassignedRange := ⟨scalarIndexMethods_proven.1, scalarIndexMethods_proven.2.1⟩

/-- `_getindex(v::AbstractRange, i::Integer)`, base/range.jl:952-955: an in-bounds index
returns `unsafe_getindex`, an out-of-bounds one throws BoundsError. -/
def GetindexChecked : Prop :=
  ∀ (u : Jl Num), getindexGeneric true u = u ∧ getindexGeneric false u = .error .boundsError

theorem getindexChecked_proven : GetindexChecked := scalarIndexMethods_proven.2.2.1

/-- `_getindex(v::UnitRange{T}, i::Integer)`, base/range.jl:959-963: a nonpositive index
throws BoundsError. -/
def GetindexUnitNonpositive : Prop :=
  ∀ (v : Rng) (i : Num), i.val ≤ 0 → getindexUnitSafe v i = .error .boundsError

theorem getindexUnitNonpositive_proven : GetindexUnitNonpositive := scalarIndexMethods_proven.2.2.2.1

/-- `_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}`, base/range.jl:968-972:
a nonpositive index throws BoundsError. -/
def GetindexUnitFloatNonpositive : Prop :=
  ∀ (v : UnitF) (i : I64), i.val ≤ 0 → getindexUnitF v i = .error .boundsError

theorem getindexUnitFloatNonpositive_proven : GetindexUnitFloatNonpositive :=
  scalarIndexMethods_proven.2.2.2.2.1

/-- `unsafe_getindex(v::OneTo{T}, i::Integer) = convert(T, i)`, base/range.jl:984:
`OneTo(n)[i] == i` in the element type. -/
def UnsafeGetindexOneTo : Prop := ∀ (v : Rng) (i : Num), unsafeGetindexOneTo v i = Ranges.Num.cast v.stop.ty i

theorem unsafeGetindexOneTo_proven : UnsafeGetindexOneTo := scalarIndexMethods_proven.2.2.2.2.2.1

/-- `==(r::AbstractUnitRange, s::AbstractUnitRange)`, base/range.jl:1153-1154: constructed
same-type integer unit ranges are equal exactly when they have the same elements. -/
def EqUnitRanges : Prop :=
  ∀ t : IntTy, ∀ x y x' y' : JInt t, ∀ r s,
    unitRangeSame (mkI t x) (mkI t y) = .ok r → unitRangeSame (mkI t x') (mkI t y') = .ok s →
    (eqUnit r s = true ↔ ((y.val < x.val ∧ y'.val < x'.val) ∨ (x.val ≤ y.val ∧ x = x' ∧ y = y')))

theorem eqUnitRanges_proven : EqUnitRanges := integerEquality_proven.1

/-- `==(r::OneTo, s::OneTo)`, base/range.jl:1156: `OneTo(n) == OneTo(m)` iff
`max(0, n) == max(0, m)`, i.e. iff they have the same elements. -/
def EqOneTos : Prop :=
  ∀ t : IntTy, ∀ x y : JInt t, ∀ r s, oneTo (mkI t x) = .ok r → oneTo (mkI t y) = .ok s →
    (eqOneTo r s = true ↔ max 0 x.val = max 0 y.val)

theorem eqOneTos_proven : EqOneTos := integerEquality_proven.2.1

/-- `==(r::OrdinalRange, s::OrdinalRange)`, base/range.jl:1147-1151: `==` is reflexive and
an empty range equals exactly the empty ranges. -/
def EqOrdinal : Prop :=
  (∀ r : Rng, eqOrdinal r r = true) ∧
  (∀ r s : Rng, Ranges.isEmpty r = true → (eqOrdinal r s = Ranges.isEmpty s))

theorem eqOrdinal_proven : EqOrdinal := ⟨integerEquality_proven.2.2.1, integerEquality_proven.2.2.2.1⟩

/-- `_findin(r::AbstractRange{<:Integer}, span::AbstractUnitRange{<:Integer})`,
base/range.jl:1286-1303: an increasing unit range inside `span` is found entirely, at
indices `1:length(r)`. -/
def FindinInside : Prop :=
  ∀ r span n : Rng, ∀ len : Num, r.kind = .unit → (Ranges.step r).val > 0 →
    (Ranges.first span).val ≤ (Ranges.first r).val → (Ranges.last r).val ≤ (Ranges.last span).val →
    Ranges.length r = .ok len → Ranges.colon2 (Ranges.Num.lit (.bit .i64) 1) len = .ok n →
    Ranges.findallInUnit r span = .ok n

theorem findinInside_proven : FindinInside := findinSubset_proven.1

/-- `in(x::AbstractChar, r::AbstractRange{<:AbstractChar})`, base/range.jl:1485-1488: the
first element of a nonempty Char range is in it, and characters outside
`[minimum(r), maximum(r)]` are not. -/
def InCharRange : Prop :=
  (∀ r : Colon.CharRng, (r.start != r.stop && (decide (r.step > 0) != decide (r.stop > r.start))) = false →
    inChar r.start r = true) ∧
  (∀ (x : Nat) (r : Colon.CharRng), r.step ≠ 0 → (x < min r.start r.stop ∨ max r.start r.stop < x) →
    inChar x r = false)

theorem inCharRange_proven : InCharRange := ⟨membershipMethods_proven.2.1, membershipMethods_proven.2.2⟩

/-- `$f(r1::OrdinalRange, r2::OrdinalRange)` for `+`/`-`, base/range.jl:1494-1499: operands
of different lengths throw DimensionMismatch. -/
def OrdinalOpMismatch : Prop :=
  ∀ f r1 r2 n1 n2, Ranges.length r1 = .ok n1 → Ranges.length r2 = .ok n2 → n1.val ≠ n2.val →
    ordinalOp f r1 r2 = .error (.dimensionMismatch "argument dimensions must match")

theorem ordinalOpMismatch_proven : OrdinalOpMismatch := rangeArithmetic_proven.1

/-- `$f(r1::LinRange{T}, r2::LinRange{T})`, base/range.jl:1501-1507: different lengths throw
DimensionMismatch; otherwise the result has endpoints `f(first(r1), first(r2))`,
`f(last(r1), last(r2))` and the common length. -/
def LinOpMethod : Prop :=
  (∀ f (r1 r2 : FloatRanges.Lin), r1.len ≠ r2.len →
    linOp f r1 r2 = .error (.dimensionMismatch "argument dimensions must match")) ∧
  (∀ f (r1 r2 : FloatRanges.Lin) out, linOp f r1 r2 = .ok out →
    out.start = f.flt r1.start r2.start ∧ out.stop = f.flt r1.stop r2.stop ∧ out.len = r1.len)

theorem linOpMethod_proven : LinOpMethod := ⟨rangeArithmetic_proven.2.1, rangeArithmetic_proven.2.2.2.2.1⟩

/-- `+(r1::StepRangeLen{T,S}, r2::StepRangeLen{T,S})`, base/range.jl:1517-1522: operands of
different lengths throw DimensionMismatch. -/
def AddCountedMismatch : Prop :=
  ∀ r1 r2 : Ranges.RngLen, r1.len.val ≠ r2.len.val →
    addCounted r1 r2 = .error (.dimensionMismatch "argument dimensions must match")

theorem addCountedMismatch_proven : AddCountedMismatch := rangeArithmetic_proven.2.2.2.2.2.1

/-- `issorted(r::AbstractUnitRange) = true` (base/range.jl:1447), `sort(r::AbstractUnitRange) = r`
and `sort!(r::AbstractUnitRange) = r` (base/range.jl:1450-1451): unit ranges are sorted. -/
def UnitRangesSorted : Prop := ∀ r, issortedUnit r = true ∧ sortUnit r = r ∧ sortBangUnit r = r

theorem unitRangesSorted_proven : UnitRangesSorted := sortingMethods_proven.1

/-- `sortperm(r::AbstractUnitRange) = eachindex(r)`, base/range.jl:1455: the identity
permutation `OneTo(length(r))`. -/
def SortpermUnit : Prop := ∀ r n, Ranges.length r = .ok n → sortpermUnit r = Colon.oneTo n

theorem sortpermUnit_proven : SortpermUnit := sortingMethods_proven.2.1

def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/range.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := []

end Methods

end JuliaLean.RangesCov

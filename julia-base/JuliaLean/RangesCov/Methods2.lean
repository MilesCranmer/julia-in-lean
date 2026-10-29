import JuliaLean.RangesCov.Methods

/-!
Per-method entries for the integer colon methods, the keyword `range` helpers and the
integer `StepRangeLen` constructors of `base/range.jl` (master `bbfa0ce4150`).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

namespace Methods2

open Colon

/-! ### Conversion lemmas -/

theorem cast_ty {ty : NType} {x y : Num} (h : Ranges.Num.cast ty x = .ok y) : y.ty = ty := by
  cases ty with
  | bool =>
    simp only [Ranges.Num.cast] at h
    by_cases hv : x.val = 0 ∨ x.val = 1
    · rw [if_pos hv] at h; cases h; rfl
    · rw [if_neg hv] at h; cases h
  | bit t =>
    simp only [Ranges.Num.cast] at h
    cases hc : JInt.convert t x.val with
    | error e => simp only [hc] at h; cases h
    | ok n =>
      simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl

theorem cast_val {ty : NType} {x y : Num} (h : Ranges.Num.cast ty x = .ok y) : y.val = x.val := by
  cases ty with
  | bool =>
    simp only [Ranges.Num.cast] at h
    by_cases hv : x.val = 0 ∨ x.val = 1
    · rw [if_pos hv] at h; cases h
      rcases hv with hv | hv <;> rw [hv] <;> decide
    · rw [if_neg hv] at h; cases h
  | bit t =>
    simp only [Ranges.Num.cast] at h
    cases hc : JInt.convert t x.val with
    | error e => simp only [hc] at h; cases h
    | ok n =>
      simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      unfold JInt.convert at hc
      split at hc
      · cases hc; rfl
      · cases hc

theorem unitRangeSame_start {a b : Num} {r : Rng} (h : unitRangeSame a b = .ok r) : r.start = a := by
  unfold unitRangeSame unitRangeT unitRangeInner at h
  rw [cast_self] at h
  cases hb : Ranges.Num.cast a.ty b with
  | error e => simp [hb, bind, Except.bind] at h
  | ok b' =>
    cases hz : unitrangeLastInt a b' with
    | error e => simp [hb, hz, bind, Except.bind] at h
    | ok z =>
      simp [hb, hz, bind, Except.bind, pure, Except.pure] at h
      subst h; rfl

theorem unitRangePromote_start {a b : Num} {r : Rng} (h : unitRangePromote a b = .ok r) :
    r.start.val = a.val := by
  unfold unitRangePromote at h
  cases ha : Ranges.Num.cast (Ranges.Num.promote a.ty b.ty) a with
  | error e => simp [ha, bind, Except.bind] at h
  | ok a' =>
    cases hb : Ranges.Num.cast (Ranges.Num.promote a.ty b.ty) b with
    | error e => simp [ha, hb, bind, Except.bind] at h
    | ok b' =>
      simp only [ha, hb, bind, Except.bind] at h
      rw [unitRangeSame_start h]
      exact cast_val ha

/-! ### Colon and `UnitRange` methods -/

/-- `(:)(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)`, base/range.jl:5:
integer `a:b` keeps `b` when `a <= b` and is the empty `a:a-1` otherwise. -/
def ColonSameUnit : Prop :=
  ∀ t : IntTy, ∀ x y : JInt t, ∀ r, colonSame2 (mkI t x) (mkI t y) = .ok r →
    r.start = mkI t x ∧ (x.val ≤ y.val → r.stop = mkI t y) ∧
    (y.val < x.val → r.stop.val = x.val - 1 ∧ r.stop.ty = .bit t ∧ Ranges.isEmpty r = true)

theorem colonSameUnit_proven : ColonSameUnit := fun t x y r h => Methods.integerUnitRange_proven t x y r h

/-- `UnitRange{T}(start, stop) where {T<:Real}`, base/range.jl:430, with endpoints already
of type `T`: the same normalization. -/
def UnitRangeTSame : Prop :=
  ∀ t : IntTy, ∀ x y : JInt t, ∀ r, unitRangeT (.bit t) (mkI t x) (mkI t y) = .ok r →
    r.start = mkI t x ∧ (x.val ≤ y.val → r.stop = mkI t y) ∧
    (y.val < x.val → r.stop.val = x.val - 1 ∧ r.stop.ty = .bit t ∧ Ranges.isEmpty r = true)

theorem unitRangeTSame_proven : UnitRangeTSame := fun t x y r h => Methods.integerUnitRange_proven t x y r h

/-- `(:)(a::Real, b::Real) = (:)(promote(a, b)...)`, base/range.jl:3: the first element of
a mixed-type integer `a:b` is `a`. -/
def ColonPromoteStart : Prop := ∀ (a b : Num) (r : Rng), colonPromote2 a b = .ok r → r.start.val = a.val

theorem colonPromoteStart_proven : ColonPromoteStart := by
  intro a b r h
  unfold colonPromote2 at h
  cases ha : Ranges.Num.cast (Ranges.Num.promote a.ty b.ty) a with
  | error e => simp [ha, bind, Except.bind] at h
  | ok a' =>
    cases hb : Ranges.Num.cast (Ranges.Num.promote a.ty b.ty) b with
    | error e => simp [ha, hb, bind, Except.bind] at h
    | ok b' =>
      simp only [ha, hb, bind, Except.bind] at h
      rw [unitRangeSame_start (a := a') (b := b') h]
      exact cast_val ha

/-- `UnitRange(start, stop)`, base/range.jl:432-436: the first element of a mixed-type
integer `UnitRange(a, b)` is `a`. -/
def UnitRangePromoteStart : Prop := ∀ (a b : Num) (r : Rng), unitRangePromote a b = .ok r → r.start.val = a.val

theorem unitRangePromoteStart_proven : UnitRangePromoteStart := fun _ _ _ h => unitRangePromote_start h

/-- `unitrange(x::AbstractUnitRange) = UnitRange(x)` (base/range.jl:447) and
`UnitRange(r::AbstractUnitRange) = UnitRange(first(r), last(r))` (base/range.jl:1342) keep
the first element. -/
def UnitrangeOfRangeStart : Prop :=
  (∀ (r out : Rng), unitrange r = .ok out → out.start.val = (Ranges.first r).val) ∧
  (∀ (r out : Rng), unitRangeOfRange r = .ok out → out.start.val = (Ranges.first r).val)

theorem unitrangeOfRangeStart_proven : UnitrangeOfRangeStart :=
  ⟨fun _ _ h => unitRangePromote_start h, fun _ _ h => unitRangePromote_start h⟩

/-- `range_start_stop(start, stop) = start:stop`, base/range.jl:230: the first element is
`start`. -/
def rangeStartStop (a b : Num) : Jl Rng := colonPromote2 a b

def RangeStartStopStart : Prop := ∀ (a b : Num) (r : Rng), rangeStartStop a b = .ok r → r.start.val = a.val

theorem rangeStartStopStart_proven : RangeStartStopStart := colonPromoteStart_proven

/-- `(:)(start::T, step::T, stop::T) where {T<:Real}`, base/range.jl:22-23: a zero step
throws ArgumentError. -/
def ColonSame3ZeroStep : Prop :=
  ∀ a s b : Num, a.ty = b.ty → s.val = 0 → ThrowsArg (colonSame3 a s b)

theorem colonSame3ZeroStep_proven : ColonSame3ZeroStep := stepRangeConstruction_proven.1

/-- `_colon(::Ordered, ::Any, start::T, step, stop::T) = StepRange(start, step, stop)`,
base/range.jl:24: a zero step throws ArgumentError. -/
def ColonOrderedZeroStep : Prop :=
  ∀ a s b : Num, a.ty = b.ty → s.val = 0 → ThrowsArg (colonOrdered a s b)

theorem colonOrderedZeroStep_proven : ColonOrderedZeroStep := stepRangeConstruction_proven.1

/-- `_colon(start::T, step, stop::T)`, base/range.jl:68-71: once both endpoints convert to
`typeof(start + zero(step))`, a zero step throws ArgumentError. -/
def ColonWidenZeroStep : Prop :=
  ∀ a s b a' b' : Num, Ranges.Num.cast (Ranges.Num.add a (Ranges.Num.zero s.ty)).ty a = .ok a' →
    Ranges.Num.cast (Ranges.Num.add a (Ranges.Num.zero s.ty)).ty b = .ok b' → s.val = 0 →
    ThrowsArg (colonWiden a s b)

theorem colonWidenZeroStep_proven : ColonWidenZeroStep := by
  intro a s b a' b' ha hb hs
  have hty : a'.ty = b'.ty := by rw [cast_ty ha, cast_ty hb]
  obtain ⟨m, hm⟩ := stepRangeConstruction_proven.1 a' s b' hty hs
  refine ⟨m, ?_⟩
  unfold colonWiden
  simp only [ha, hb, bind, Except.bind]
  exact hm

/-- `(:)(start::T, step, stop::T) where {T<:Real} = _colon(start, step, stop)` and
`(:)(start::T, step, stop::T) where {T}` (base/range.jl:64-65), for a same-type integer
step: a zero step throws ArgumentError. -/
def ColonTypedZeroStep : Prop :=
  ∀ a s b : Num, a.ty = b.ty → s.ty = a.ty → s.val = 0 → ThrowsArg (colonTyped a s b)

theorem colonTypedZeroStep_proven : ColonTypedZeroStep := by
  intro a s b hab hs h0
  unfold colonTyped
  rw [if_pos hs]
  exact stepRangeConstruction_proven.1 a s b hab h0

/-- `(:)(start::A, step, stop::C) where {A<:Real, C<:Real}`, base/range.jl:10-11, and
`range_start_step_stop(start, step, stop) = start:step:stop` (base/range.jl:241): for
same-type integers a zero step throws ArgumentError. -/
def rangeStartStepStop (a s b : Num) : Jl Rng := colonPromote3 a s b

def ColonPromote3ZeroStep : Prop :=
  (∀ a s b : Num, a.ty = b.ty → s.ty = a.ty → s.val = 0 → ThrowsArg (colonPromote3 a s b)) ∧
  (∀ a s b : Num, a.ty = b.ty → s.ty = a.ty → s.val = 0 → ThrowsArg (rangeStartStepStop a s b))

theorem colonPromote3ZeroStep_proven : ColonPromote3ZeroStep := by
  have key : ∀ a s b : Num, a.ty = b.ty → s.ty = a.ty → s.val = 0 → ThrowsArg (colonPromote3 a s b) := by
    intro a s b hab hs h0
    unfold colonPromote3
    have hp : Ranges.Num.promote a.ty b.ty = a.ty := by rw [← hab, promote_self]
    have hb : Ranges.Num.cast a.ty b = .ok b := by rw [hab]; exact cast_self b
    simp only [hp, cast_self, hb, bind, Except.bind]
    exact colonTypedZeroStep_proven a s b hab hs h0
  exact ⟨key, key⟩

/-! ### `range` helpers -/

/-- `range_length(len::Integer) = OneTo(len)`, base/range.jl:193. -/
def rangeLength (n : Num) : Jl Rng := oneTo n

/-- `range_stop(stop::Integer) = range_length(stop)`, base/range.jl:197. -/
def rangeStopInt (n : Num) : Jl Rng := rangeLength n

/-- `range(; length=n)` and `range(; stop=n)` for an integer `n`: `OneTo(n)`, which has
`max(0, n)` elements (range docstring). -/
def RangeLengthOneTo : Prop :=
  (∀ t : IntTy, ∀ x : JInt t, ∃ r, rangeLength (mkI t x) = .ok r ∧ r.kind = .oneTo ∧
    0 ≤ r.stop.val ∧ (0 ≤ x.val → r.stop.val = x.val) ∧ (x.val < 0 → r.stop.val = 0))

theorem rangeLengthOneTo_proven : RangeLengthOneTo := oneToConstruction_proven.1

def RangeStopOneTo : Prop :=
  (∀ t : IntTy, ∀ x : JInt t, ∃ r, rangeStopInt (mkI t x) = .ok r ∧ r.kind = .oneTo ∧
    0 ≤ r.stop.val ∧ (0 ≤ x.val → r.stop.val = x.val) ∧ (x.val < 0 → r.stop.val = 0))

theorem rangeStopOneTo_proven : RangeStopOneTo := oneToConstruction_proven.1

/-- `range(start, stop, length::Integer) = _range(start, nothing, stop, length)`,
base/range.jl:170, for `Int` endpoints: the result has `length` elements. -/
def range3 (a b n : I64) : Jl FloatRanges.SRL := Floats.rsslInt a b n

def Range3Length : Prop := ∀ a b n : I64, FloatRanges.LenIs n (range3 a b n)

theorem range3Length_proven : Range3Length := Twice.linspaceIntLength_proven

/-! ### `StepRangeLen` constructors -/

theorem countedNewTyped_ok {T L : NType} {ref st len off : Num} {r : Ranges.RngLen}
    (h : Ranges.countedNewTyped T L ref st len off = .ok r) :
    r.ref = ref ∧ r.stride = st ∧ r.elementTy = T ∧ 0 ≤ r.len.val ∧ 1 ≤ r.offset.val ∧
      r.offset.val ≤ max 1 r.len.val := by
  unfold Ranges.countedNewTyped at h
  cases hn : Ranges.Num.cast L len with
  | error e => simp [hn, bind, Except.bind] at h
  | ok n =>
    by_cases h1 : n.val < 0
    · simp [hn, h1, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · cases ho : Ranges.Num.cast L off with
      | error e => simp [hn, h1, ho, bind, Except.bind] at h
      | ok o =>
        by_cases h2 : o.val < 1 ∨ o.val > max 1 n.val
        · simp only [hn, h1, ho, bind, Except.bind, if_false, if_pos h2, throw, throwThe,
            MonadExceptOf.throw] at h
          cases h
        · simp only [hn, h1, ho, bind, Except.bind, if_false, if_neg h2, pure, Except.pure] at h
          cases h
          exact ⟨rfl, rfl, rfl, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩

/-- The integer `StepRangeLen{T,R,S,L}` inner constructor, base/range.jl:533-543: a result
stores `ref`, `step` and `T`, has a nonnegative length and an offset in `[1, max(1, len)]`
(the type invariant); a negative length throws ArgumentError. -/
def SrlInner : Prop :=
  (∀ T L ref st len off r, Ranges.countedNewTyped T L ref st len off = .ok r →
    r.ref = ref ∧ r.stride = st ∧ r.elementTy = T ∧ 0 ≤ r.len.val ∧ 1 ≤ r.offset.val ∧
      r.offset.val ≤ max 1 r.len.val) ∧
  (∀ T L ref st len off n, Ranges.Num.cast L len = .ok n → n.val < 0 →
    Ranges.countedNewTyped T L ref st len off = .error (.argumentError "length cannot be negative"))

theorem srlInner_proven : SrlInner := by
  refine ⟨fun _ _ _ _ _ _ _ h => countedNewTyped_ok h, ?_⟩
  intro T L ref st len off n hn h1
  simp [Ranges.countedNewTyped, hn, h1, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- `StepRangeLen{T,R,S}(ref, step, len, offset)`, base/range.jl:546-547: `L` is
`promote_type(Int, typeof(len))`. -/
def srlTRS (T : NType) (ref st len off : Num) : Jl Ranges.RngLen :=
  Ranges.countedNewTyped T (Ranges.Num.promote (.bit .i64) len.ty) ref st len off

/-- `StepRangeLen(ref, step, len, offset)`, base/range.jl:548-549: `T` is
`typeof(ref + zero(step))`. -/
def srlAuto (ref st len off : Num) : Jl Ranges.RngLen :=
  Ranges.countedNewTyped (Ranges.Num.add ref (Ranges.Num.zero st.ty)).ty
    (Ranges.Num.promote (.bit .i64) len.ty) ref st len off

/-- `StepRangeLen{T}(ref, step, len, offset)`, base/range.jl:550-551. -/
def srlT (T : NType) (ref st len off : Num) : Jl Ranges.RngLen := srlTRS T ref st len off

/-- Each outer `StepRangeLen` constructor returns a range storing `ref` and `step`, with a
nonnegative length and an offset in `[1, max(1, len)]`. -/
def SrlTRSInvariant : Prop :=
  ∀ T ref st len off r, srlTRS T ref st len off = .ok r →
    r.ref = ref ∧ r.stride = st ∧ r.elementTy = T ∧ 0 ≤ r.len.val ∧ 1 ≤ r.offset.val ∧
      r.offset.val ≤ max 1 r.len.val

theorem srlTRSInvariant_proven : SrlTRSInvariant := fun _ _ _ _ _ _ h => countedNewTyped_ok h

def SrlAutoInvariant : Prop :=
  ∀ ref st len off r, srlAuto ref st len off = .ok r →
    r.ref = ref ∧ r.stride = st ∧ r.elementTy = (Ranges.Num.add ref (Ranges.Num.zero st.ty)).ty ∧
      0 ≤ r.len.val ∧ 1 ≤ r.offset.val ∧ r.offset.val ≤ max 1 r.len.val

theorem srlAutoInvariant_proven : SrlAutoInvariant := fun _ _ _ _ _ h => countedNewTyped_ok h

def SrlTInvariant : Prop :=
  ∀ T ref st len off r, srlT T ref st len off = .ok r →
    r.ref = ref ∧ r.stride = st ∧ r.elementTy = T ∧ 0 ≤ r.len.val ∧ 1 ≤ r.offset.val ∧
      r.offset.val ≤ max 1 r.len.val

theorem srlTInvariant_proven : SrlTInvariant := fun _ _ _ _ _ _ h => countedNewTyped_ok h

def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/range.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := []

end Methods2

end JuliaLean.RangesCov

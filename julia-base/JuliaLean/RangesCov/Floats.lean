import JuliaLean.RangesCov.Twice

/-!
Floating-point and `LinRange` methods of `base/range.jl` (master `bbfa0ce4150`): the
`ArithmeticRounds` colon used by non-IEEE floats such as `BigFloat` (lines 14-29), the
floating-point `UnitRange` (lines 428-445), and the `LinRange` constructors and
`range_start_stop_length` (lines 597-632, 1315-1318).

Values of a non-IEEE float type are represented by Float64 values; every property below
holds or fails for exactly representable small integers, where the rounding of the
represented type does not matter.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

namespace Floats

/-! ### The `ArithmeticRounds` colon -/

/-- A `StepRangeLen{T,T,T,Int}` of a non-IEEE float type `T`. -/
structure GSrl where
  ref : F64
  step : F64
  len : Int
  offset : Int
  deriving DecidableEq

/-- `StepRangeLen(ref, step, len)`, base/range.jl:548-549, reaching the inner constructor
(base/range.jl:533-543); `T` is not an `Integer`, so the integer-step check is skipped. -/
def gsrlNew (ref step : F64) (len : Int) : Jl GSrl :=
  if len < 0 then .error (.argumentError "length cannot be negative")
  else if 1 ≤ (1 : Int) ∧ (1 : Int) ≤ max 1 len then .ok ⟨ref, step, len, 1⟩
  else .error (.argumentError "StepRangeLen: offset must be in [1,len]")

/-- `convert(Integer, x)` of a float: exact, an `InexactError` for non-integers. -/
def toInteger (x : F64) : Jl Int :=
  if Float.F64.isfinite x && Float.F64.isinteger x then
    .ok ((Float.F64.toRat x).1 / ((Float.F64.toRat x).2 : Int))
  else .error (.inexactError "Integer")

/-- `_colon(::Ordered, ::ArithmeticRounds, start, step, stop)`, base/range.jl:26-27:
`StepRangeLen(start, step, convert(Integer, fld(stop - start, step)) + 1)`. -/
def colonRounds (a s b : F64) : Jl GSrl := do
  let n ← toInteger (Float.F64.fld (Float.F64.sub b a) s)
  gsrlNew a s (n + 1)

/-- `_colon(::Any, ::Any, start, step, stop)`, base/range.jl:28-29 (the same body). -/
def colonAny (a s b : F64) : Jl GSrl := do
  let n ← toInteger (Float.F64.fld (Float.F64.sub b a) s)
  gsrlNew a s (n + 1)

/-- `(:)(start::T, step::T, stop::T) where {T<:AbstractFloat}`, base/range.jl:20-21:
`_colon(OrderStyle(T), ArithmeticStyle(T), start, step, stop)`; a non-IEEE float is
`Ordered()` and `ArithmeticRounds()`. -/
def colonFloat3 (ordered rounds : Bool) (a s b : F64) : Jl GSrl :=
  if ordered && rounds then colonRounds a s b else colonAny a s b

/-- `(:)(a::T, b::T) where {T<:AbstractFloat} = (:)(a, T(1), b)`, base/range.jl:14. -/
def colonFloat2 (a b : F64) : Jl GSrl := colonFloat3 true true a Float.F64.one b

/-- `a:b` with `b < a` is an empty range (docstring of `(:)`, base/range.jl:54-55), for a
non-IEEE float type. -/
def RoundsColonEmpty : Prop :=
  ∀ a b : F64, Float.F64.isfinite a = true → Float.F64.isfinite b = true → Float.F64.lt b a = true →
    ∃ r, colonFloat2 a b = .ok r ∧ r.len = 0

theorem roundsColonEmpty_refuted : ¬ RoundsColonEmpty := by
  intro h
  obtain ⟨r, hr, _⟩ := h (FloatRanges.dec 3) (FloatRanges.dec 1) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hbad : Twice.isOk (colonFloat2 (FloatRanges.dec 3) (FloatRanges.dec 1)) = false := by decide +kernel
  rw [hr] at hbad
  cases hbad

/-- The fallback colon `_colon(::Any, ::Any, start, step, stop)` returns a range that starts
at `start`, has step `step`, and a nonnegative length (StepRangeLen invariant). -/
def ColonAnyInvariant : Prop :=
  ∀ (a s b : F64) (r : GSrl), colonAny a s b = .ok r → r.ref = a ∧ r.step = s ∧ 0 ≤ r.len ∧ r.offset = 1

theorem colonAnyInvariant_proven : ColonAnyInvariant := by
  intro a s b r h
  unfold colonAny at h
  cases hn : toInteger (Float.F64.fld (Float.F64.sub b a) s) with
  | error e => simp [hn, bind, Except.bind] at h
  | ok n =>
    simp only [hn, bind, Except.bind, gsrlNew] at h
    split at h
    · cases h
    · split at h
      · cases h; exact ⟨rfl, rfl, by show 0 ≤ n + 1; omega, rfl⟩
      · cases h

/-! ### Floating-point `UnitRange` -/

/-- A `UnitRange{Float64}`. -/
structure UF where
  start : F64
  stop : F64
  deriving DecidableEq

/-- `unitrange_last(start, stop)` for non-integers, base/range.jl:443-445:
`stop >= start ? convert(typeof(stop), start + floor(stop - start)) :
convert(typeof(stop), start - oneunit(start - stop))`. -/
def unitrangeLastF (a b : F64) : F64 :=
  if Float.F64.le a b then Float.F64.add a (Float.F64.floor (Float.F64.sub b a))
  else Float.F64.sub a Float.F64.one

/-- `UnitRange{T}(start::T, stop::T) = new(start, unitrange_last(start, stop))`,
base/range.jl:428, reached from `UnitRange(start::T, stop::T)`, base/range.jl:431. -/
def unitRangeF (a b : F64) : UF := ⟨a, unitrangeLastF a b⟩

/-- A floating-point `UnitRange(a, b)` with `a <= b` has its last element at most `b`
(the stored stop is the last element `a + k <= b`). -/
def UnitRangeFloatStop : Prop :=
  ∀ a b : F64, Float.F64.isfinite a = true → Float.F64.isfinite b = true → Float.F64.le a b = true →
    Float.F64.le (unitRangeF a b).stop b = true

theorem unitRangeFloatStop_refuted : ¬ UnitRangeFloatStop := by
  intro h
  have := h (FloatRanges.dec 7 10) (FloatRanges.dec 36999999999999997 (10 ^ 16)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hbad : Float.F64.le (unitRangeF (FloatRanges.dec 7 10)
      (FloatRanges.dec 36999999999999997 (10 ^ 16))).stop
      (FloatRanges.dec 36999999999999997 (10 ^ 16)) = false := by decide +kernel
  rw [this] at hbad
  cases hbad

/-- A floating-point `UnitRange(a, b)` with `b < a` is normalized to `a:a-1`
(docstring of `(:)`, base/range.jl:54-55). -/
def UnitRangeFloatEmpty : Prop :=
  ∀ a b : F64, Float.F64.le a b = false → unitRangeF a b = ⟨a, Float.F64.sub a Float.F64.one⟩

theorem unitRangeFloatEmpty_proven : UnitRangeFloatEmpty := by
  intro a b h; simp [unitRangeF, unitrangeLastF, h]

/-! ### Integer `LinRange` -/

/-- A `LinRange{T,Int}` with integer element type `T`. -/
structure LinInt (t : IntTy) where
  start : JInt t
  stop : JInt t
  len : I64
  lendiv : I64
  deriving DecidableEq

/-- `LinRange{T,L}(start::T, stop::T, len::L)`, base/range.jl:597-609, for integer `T`
and `L = Int`; `stop - start` wraps in `T` and `mod` promotes it with `lendiv`. -/
def linIntNew {t : IntTy} (a b : JInt t) (len : I64) : Jl (LinInt t) :=
  if len.val < 0 then .error (.argumentError "negative length")
  else if len.val = 1 then
    if a = b then .ok ⟨a, b, len, len⟩ else .error (.argumentError "endpoints differ")
  else
    let lendiv := FloatRanges.imax (len - FloatRanges.i64 1) (FloatRanges.i64 1)
    match Ranges.Num.mod (Ranges.Num.sub (mkI t b) (mkI t a)) (mkI .i64 lendiv) with
    | .error e => .error e
    | .ok m =>
      if m.val ≠ 0 then .error (.argumentError "LinRange{<:Integer} cannot have non-integer step")
      else .ok ⟨a, b, len, lendiv⟩

/-- `lerpi(j, d, a::T, b::T)`, base/range.jl:992-996, for integer `T`: `t = j/d` and
`T((1-t)*a + t*b)`, an exact conversion. -/
def lerpiInt {t : IntTy} (j d : I64) (a b : JInt t) : Jl (JInt t) :=
  let tt := Float.F64.div (FloatRanges.flt j) (FloatRanges.flt d)
  Float.F64.int t (Float.F64.add (Float.F64.mul (Float.F64.sub Float.F64.one tt) (FloatRanges.flt a))
    (Float.F64.mul tt (FloatRanges.flt b)))

/-- `getindex(r::LinRange, i::Int)`: `checkbounds` then
`unsafe_getindex(r, i) = lerpi(i-1, r.lendiv, r.start, r.stop)`, base/range.jl:952-955,990. -/
def linIntGet {t : IntTy} (r : LinInt t) (i : I64) : Jl (JInt t) :=
  if 1 ≤ i.val ∧ i.val ≤ r.len.val then lerpiInt (i - FloatRanges.i64 1) r.lendiv r.start r.stop
  else .error .boundsError

/-- Every in-bounds element of a constructed integer `LinRange` can be read
(AbstractArray indexing invariant). -/
def LinIntElements : Prop :=
  ∀ (a b : JInt .i64) (n i : I64) (r : LinInt .i64), linIntNew a b n = .ok r →
    1 ≤ i.val → i.val ≤ n.val → Twice.isOk (linIntGet r i) = true

theorem linIntElements_refuted : ¬ LinIntElements := by
  intro h
  have hr : linIntNew (⟨-90, by decide⟩ : JInt .i64) ⟨90, by decide⟩ (FloatRanges.i64 4) =
      .ok ⟨⟨-90, by decide⟩, ⟨90, by decide⟩, FloatRanges.i64 4, FloatRanges.i64 3⟩ := by decide +kernel
  have := h _ _ _ (FloatRanges.i64 2) _ hr (by decide) (by decide)
  have hbad : Twice.isOk (linIntGet (⟨⟨-90, by decide⟩, ⟨90, by decide⟩, FloatRanges.i64 4,
      FloatRanges.i64 3⟩ : LinInt .i64) (FloatRanges.i64 2)) = false := by decide +kernel
  rw [this] at hbad
  cases hbad

/-! ### Float64 `LinRange` -/

/-- The inner `LinRange{Float64,Int}` constructor (base/range.jl:597-609) stores its
endpoints and length and rejects negative lengths and differing endpoints for length 1. -/
def LinConstructor : Prop :=
  (∀ (a b : F64) (n : I64) (r : FloatRanges.Lin), FloatRanges.Lin.mk' a b n = .ok r →
    r.start = a ∧ r.stop = b ∧ r.len = n ∧ 0 ≤ n.val) ∧
  (∀ (a b : F64) (n : I64), n.val < 0 → FloatRanges.Lin.mk' a b n = .error (.argumentError "negative length")) ∧
  (∀ (a b : F64) (n : I64), n.val = 1 → Float.F64.eq a b = false →
    FloatRanges.Lin.mk' a b n = .error (.argumentError "endpoints differ"))

theorem linConstructor_proven : LinConstructor := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b n r h
    have hf := Ops.linMk_fields h
    refine ⟨hf.1, hf.2.1, hf.2.2, ?_⟩
    unfold FloatRanges.Lin.mk' at h
    split at h
    · cases h
    · omega
  · intro a b n h; simp [FloatRanges.Lin.mk', h]
  · intro a b n h he; simp [FloatRanges.Lin.mk', h, he]

/-- `LinRange{T,L}(start, stop, len::Integer)`, base/range.jl:612-614, for `T = Float64`,
`L = Int` and `Int` endpoints and length: `convert(T, start)`, `convert(T, stop)`,
`convert(L, len)`. -/
def linTL (a b n : I64) : Jl FloatRanges.Lin :=
  FloatRanges.Lin.mk' (FloatRanges.flt a) (FloatRanges.flt b) n

/-- `LinRange{T}(start, stop, len::Integer) = LinRange{T,promote_type(Int,typeof(len))}(...)`,
base/range.jl:616-618. -/
def linT (a b n : I64) : Jl FloatRanges.Lin := linTL a b n

/-- `LinRange(start, stop, len::Integer)`, base/range.jl:620-623: `T` is
`typeof((zero(stop) - zero(start)) / oneunit(len))`, Float64 for `Int` arguments. -/
def linAuto (a b n : I64) : Jl FloatRanges.Lin := linT a b n

/-- `LinRange(a, b, n)` with `Int` arguments has `first == Float64(a)`,
`last == Float64(b)` and `length == n` (LinRange docstring: first and last are exactly
those provided), through the three outer constructors. -/
def LinOuterConstructors : Prop :=
  (∀ a b n r, linTL a b n = .ok r → r.first = FloatRanges.flt a ∧ r.last = FloatRanges.flt b ∧ r.len = n) ∧
  (∀ a b n r, linT a b n = .ok r → r.first = FloatRanges.flt a ∧ r.last = FloatRanges.flt b ∧ r.len = n) ∧
  (∀ a b n r, linAuto a b n = .ok r → r.first = FloatRanges.flt a ∧ r.last = FloatRanges.flt b ∧ r.len = n)

theorem linOuterConstructors_proven : LinOuterConstructors :=
  ⟨fun _ _ _ _ h => Ops.linMk_fields h, fun _ _ _ _ h => Ops.linMk_fields h,
    fun _ _ _ _ h => Ops.linMk_fields h⟩

/-- `-(r::LinRange) = LinRange{typeof(r.start)}(-r.start, -r.stop, length(r))`,
base/range.jl:1315-1318: the result has the negated endpoints and the same length. -/
def LinNegation : Prop :=
  ∀ r out : FloatRanges.Lin, r.neg = .ok out →
    out.first = Float.F64.neg r.first ∧ out.last = Float.F64.neg r.last ∧ out.len = r.len

theorem linNegation_proven : LinNegation := fun _ _ h => Ops.linMk_fields h

/-! ### `range_start_stop_length` -/

/-- `range_start_stop_length(start::T, stop::T, len) where {T<:Integer} =
_linspace(float(T), start, stop, len)`, base/range.jl:628-629, for `Int`. -/
def rsslInt (a b len : I64) : Jl FloatRanges.SRL := Twice.linspaceInt a b len

/-- `range_start_stop_length(start, stop, len) = range_start_stop_length(promote(start, stop)..., len)`,
base/range.jl:625-626, for an `Int` start and a Float64 stop (promoted to Float64). -/
def rsslPromote (a : I64) (b : F64) (len : I64) : Jl FloatRanges.SRL :=
  FloatRanges.rangeStartStopLength (FloatRanges.flt a) b len

/-- `range_start_stop_length(start::T, stop::T, len) where {T} = LinRange(start, stop, len)`,
base/range.jl:627, for a non-IEEE float type (values represented in Float64). -/
def rsslGeneric (a b : F64) (len : I64) : Jl FloatRanges.Lin := FloatRanges.Lin.mk' a b len

/-- `_linspace(::Type{T}, start::Integer, stop::Integer, len) where T = LinRange{T}(start, stop, len)`,
base/range.jl:632, for a non-IEEE float `T`. -/
def linspaceGeneric (a b len : I64) : Jl FloatRanges.Lin := linT a b len

/-- `range(a, b; length=n)` has `n` elements whenever it returns (range docstring), for
integer endpoints, promoted mixed endpoints, generic float endpoints and the generic
integer `_linspace`. -/
def StartStopLengthDispatch : Prop :=
  (∀ a b n : I64, FloatRanges.LenIs n (rsslInt a b n)) ∧
  (∀ (a : I64) (b : F64) (n : I64), FloatRanges.LenIs n (rsslPromote a b n)) ∧
  (∀ (a b : F64) (n : I64) r, rsslGeneric a b n = .ok r → r.len = n ∧ r.first = a ∧ r.last = b) ∧
  (∀ (a b n : I64) r, linspaceGeneric a b n = .ok r → r.len = n)

theorem startStopLengthDispatch_proven : StartStopLengthDispatch :=
  ⟨Twice.linspaceIntLength_proven, fun _ _ _ => FloatRanges.rangeStartStopLength_len _ _ _,
    fun _ _ _ _ h => ⟨(Ops.linMk_fields h).2.2, (Ops.linMk_fields h).1, (Ops.linMk_fields h).2.1⟩,
    fun _ _ _ _ h => (Ops.linMk_fields h).2.2⟩

def entries : List Entry := [
  { id := "rangescov-bigfloat-colon-empty", juliaFile := "base/range.jl"
    juliaFns := ["(:)(::T, ::T) where T<:AbstractFloat", "(:)(::T, ::T, ::T) where T<:AbstractFloat",
      "_colon(::Ordered, ::ArithmeticRounds, start, step, stop)"]
    statement := "a:b with b < a is an empty range for a non-IEEE float type."
    source := "docstring of (:), base/range.jl:54-55"
    status := .refuted, prop := ``RoundsColonEmpty, thm := some ``roundsColonEmpty_refuted
    issue := "none found (queries: issues BigFloat range empty; issues BigFloat colon; prs BigFloat range)"
    notes := "big(3.0):big(1.0) computes length fld(-2, 1) + 1 = -1 and throws ArgumentError(\"length cannot be negative\")." },
  { id := "rangescov-colon-any-invariant", juliaFile := "base/range.jl"
    juliaFns := ["_colon(::Any, ::Any, start, step, stop)"]
    statement := "The fallback colon returns a StepRangeLen starting at start with step step, offset 1 and nonnegative length."
    source := "StepRangeLen invariant; base/range.jl:28-29"
    status := .proven, prop := ``ColonAnyInvariant, thm := some ``colonAnyInvariant_proven },
  { id := "rangescov-unitrange-float-last", juliaFile := "base/range.jl"
    juliaFns := ["unitrange_last(start, stop)", "UnitRange{T}(::T, ::T) where T<:Real", "UnitRange(::T, ::T) where T<:Real"]
    statement := "A floating-point UnitRange(a, b) with a <= b has last element at most b."
    source := "UnitRange docstring (elements start, start+1, ... up to stop)"
    status := .refuted, prop := ``UnitRangeFloatStop, thm := some ``unitRangeFloatStop_refuted
    issue := "none found; related #60261 (queries: issues UnitRange Float64 stop; issues UnitRange float last)"
    notes := "UnitRange(0.7, 3.6999999999999997) stores stop 0.7 + floor(2.9999999999999996) = 3.7 > 3.6999999999999997." },
  { id := "rangescov-unitrange-float-empty", juliaFile := "base/range.jl"
    juliaFns := ["unitrange_last(start, stop)"]
    statement := "A floating-point UnitRange(a, b) with b < a is normalized to a:a-1."
    source := "docstring of (:), base/range.jl:54-55"
    status := .proven, prop := ``UnitRangeFloatEmpty, thm := some ``unitRangeFloatEmpty_proven },
  { id := "rangescov-linrange-integer-elements", juliaFile := "base/range.jl"
    juliaFns := ["LinRange{T,L}(::T, ::T, ::L) where {T,L<:Integer}", "unsafe_getindex(::LinRange, ::Integer)"]
    statement := "Every in-bounds element of a constructed integer LinRange can be read."
    source := "AbstractArray indexing invariant; LinRange docstring"
    status := .refuted, prop := ``LinIntElements, thm := some ``linIntElements_refuted
    issue := "none found (queries: issues LinRange integer InexactError; prs LinRange integer step)"
    notes := "LinRange{Int}(-90, 90, 4) passes the integer-step check, but lerpi computes (1-1/3)*-90 + (1/3)*90 = -30.000000000000007 in Float64 and Int(...) throws InexactError." },
  { id := "rangescov-linrange-constructor", juliaFile := "base/range.jl"
    juliaFns := ["LinRange{T,L}(::T, ::T, ::L) where {T,L<:Integer}"]
    statement := "The inner LinRange{Float64} constructor stores its endpoints and length, and rejects negative lengths and differing endpoints for length 1."
    source := "LinRange docstring; base/range.jl:597-609"
    status := .proven, prop := ``LinConstructor, thm := some ``linConstructor_proven },
  { id := "rangescov-linrange-outer-constructors", juliaFile := "base/range.jl"
    juliaFns := ["LinRange{T,L}(start, stop, ::Integer)", "LinRange{T}(start, stop, ::Integer)", "LinRange(start, stop, ::Integer)"]
    statement := "LinRange(a, b, n) with Int arguments has first Float64(a), last Float64(b) and length n through each outer constructor."
    source := "LinRange docstring (first and last are exactly those provided); base/range.jl:612-623"
    status := .proven, prop := ``LinOuterConstructors, thm := some ``linOuterConstructors_proven },
  { id := "rangescov-linrange-negation", juliaFile := "base/range.jl"
    juliaFns := ["-(::LinRange)"]
    statement := "-r for a LinRange has the negated endpoints and the same length."
    source := "unary minus on arrays is elementwise; base/range.jl:1315-1318"
    status := .proven, prop := ``LinNegation, thm := some ``linNegation_proven },
  { id := "rangescov-start-stop-length-dispatch", juliaFile := "base/range.jl"
    juliaFns := ["range_start_stop_length(start, stop, ::Integer)", "range_start_stop_length(::T, ::T, ::Integer) where T",
      "range_start_stop_length(::T, ::T, ::Integer) where T<:Integer", "_linspace(::Type{T}, ::Integer, ::Integer, ::Integer) where T"]
    statement := "range(a, b; length=n) has n elements whenever it returns, for integer, promoted, generic float endpoints and the generic integer _linspace."
    source := "range docstring; base/range.jl:625-632"
    status := .proven, prop := ``StartStopLengthDispatch, thm := some ``startStopLengthDispatch_proven }
]

end Floats

end JuliaLean.RangesCov

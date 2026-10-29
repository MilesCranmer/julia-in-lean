import JuliaLean.RangesCov.Colon

/-!
Interface methods of `base/range.jl` (master `bbfa0ce4150`, lines 703-1000):
length, size, emptiness, step, first/last, extrema, argmin/argmax, iteration and
scalar indexing, for integer ranges (`Ranges.Rng`, `Ranges.RngLen`) and Float64
ranges (`FloatRanges.SRL`, `FloatRanges.Lin`, and the plain-Float64 `FSRL`).
-/

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

set_option linter.unusedSimpArgs false

/-- `StepRangeLen{Float64,Float64,Float64,Int}` (no TwicePrecision), base/range.jl:527-531,
as `StepRangeLen(0.0, 0.1, 4)` builds it. -/
structure FSRL where
  ref : F64
  step : F64
  len : I64
  offset : I64
  deriving DecidableEq, Repr

namespace Access

/-! ### Size and emptiness -/

/-- `length(r::AbstractRange) = error("length implementation missing")`, base/range.jl:705. -/
def lengthFallback {α : Type} (_ : α) : JlX Num :=
  .error (.errorException "length implementation missing")

/-- `size(r::AbstractRange) = (length(r),)`, base/range.jl:706. -/
def size {α β : Type} (length : α → JlX β) (r : α) : JlX (List β) := do
  let n ← length r
  pure [n]

/-- `has_offset_axes(::StepRange) = false`, base/range.jl:747. -/
def hasOffsetAxesStep (_ : Rng) : Bool := false

/-- `copy(r::AbstractRange) = r`, base/range.jl:923. -/
def copy {α : Type} (r : α) : α := r

/-- `getindex(r::AbstractRange, ::Colon) = copy(r)`, base/range.jl:1000. -/
def getindexColon {α : Type} (r : α) : α := copy r

/-- `isempty(r::StepRange)`, base/range.jl:708-710. -/
def isemptyStep (r : Rng) : Bool :=
  (!Ranges.Num.eq r.start r.stop) && (decide (r.stride.val > 0) != decide (r.stop.val > r.start.val))

/-- `isempty(r::AbstractUnitRange) = first(r) > last(r)`, base/range.jl:711. -/
def isemptyUnit (r : Rng) : Bool := decide ((Ranges.first r).val > (Ranges.last r).val)

/-- `isempty(r::LinRange) = length(r) == 0`, base/range.jl:713. -/
def isemptyLin (r : FloatRanges.Lin) : Bool := decide (r.len.val = 0)

/-! ### Steps -/

/-- `step(r::StepRange) = r.step`, base/range.jl:735. -/
def stepStep (r : Rng) : Num := r.stride

/-- `step(r::AbstractUnitRange{T}) = oneunit(T) - zero(T)`, base/range.jl:736. -/
def stepUnit (T : NType) : Num := Ranges.Num.sub (Ranges.Num.one T) (Ranges.Num.zero T)

/-- `step(r::AbstractUnitRange{Bool}) = true`, base/range.jl:737. -/
def stepUnitBool : Num := ⟨.bool, true⟩

/-- `step(r::StepRangeLen) = r.step`, base/range.jl:738 (integer elements). -/
def stepCounted (r : Ranges.RngLen) : Num := r.stride

/-- `step(r::StepRangeLen{T}) where {T<:AbstractFloat} = T(r.step)`, base/range.jl:739. -/
def stepFloat (r : FSRL) : F64 := r.step

/-- `step_hp(r::StepRangeLen) = r.step`, base/range.jl:743 (TwicePrecision step). -/
def stepHpSrl (r : FloatRanges.SRL) : TP := r.step

/-- `step_hp(r::AbstractRange) = step(r)`, base/range.jl:744. -/
def stepHp (r : Rng) : Num := Ranges.step r

/-! ### Lengths (generic ordinal and unit; the BitInteger specializations are
`Ranges.length`/`Ranges.checkedLength`, which mirror base/range.jl:794-806,817-863) -/

/-- `length(r::OneTo) = Integer(r.stop - zero(r.stop))`, base/range.jl:806. -/
def lengthOneTo (r : Rng) : Num := Ranges.Num.sub r.stop (Ranges.Num.zero r.stop.ty)

/-- `length(r::OneTo{T}) where {T<:bigints} = r.stop`, base/range.jl:817. -/
def lengthOneToBig (r : Rng) : Num := r.stop

/-- `length(r::OneTo{<:smallints}) = Int(r.stop)`, base/range.jl:860. -/
def lengthOneToSmall (r : Rng) : Jl Num := Ranges.Num.cast (.bit .i64) r.stop

/-- `length(r::AbstractUnitRange{<:smallints}) = Int(last(r)) - Int(first(r)) + 1`,
base/range.jl:859. -/
def lengthUnitSmall (r : Rng) : Jl Num := do
  let b ← Ranges.Num.cast (.bit .i64) (Ranges.last r)
  let a ← Ranges.Num.cast (.bit .i64) (Ranges.first r)
  pure (Ranges.Num.add (Ranges.Num.sub b a) (Ranges.Num.one (.bit .i64)))

/-- `length(r::StepRangeLen) = r.len`, base/range.jl:807. -/
def lengthSrl (r : FloatRanges.SRL) : I64 := r.len

/-- `length(r::LinRange) = r.len`, base/range.jl:808. -/
def lengthLin (r : FloatRanges.Lin) : I64 := r.len

/-- `firstindex(r::StepRange{<:bigints,<:bitints}) = one(last(r)-first(r))`, base/range.jl:850. -/
def firstindexBig (r : Rng) : Num :=
  Ranges.Num.one (Ranges.Num.sub (Ranges.last r) (Ranges.first r)).ty

/-- `firstindex(::StepRange{<:smallints,<:bitints}) = 1`, base/range.jl:864. -/
def firstindexSmall (_ : Rng) : Num := Ranges.Num.lit (.bit .i64) 1

/-! ### Endpoints and extrema -/

/-- `first(r::OrdinalRange{T}) = convert(T, r.start)`, base/range.jl:867. -/
def firstOrdinal (r : Rng) : Jl Num := Ranges.Num.cast r.start.ty r.start

/-- `first(r::OneTo{T}) = oneunit(T)`, base/range.jl:868. -/
def firstOneTo (r : Rng) : Num := Ranges.Num.one r.stop.ty

/-- `first(r::OneTo, n::Integer)`, base/range.jl:872-875. -/
def firstOneToN (r : Rng) (n : Num) : Jl Rng := do
  if n.val < 0 then throw (.argumentError "Number of elements must be non-negative")
  let m ← Ranges.Num.cast r.stop.ty (Ranges.Num.min r.stop n)
  Colon.oneTo m

/-- `last(r::OrdinalRange{T}) = convert(T, r.stop)`, base/range.jl:877. -/
def lastOrdinal (r : Rng) : Jl Num := Ranges.Num.cast r.stop.ty r.stop

/-- `last(r::LinRange) = r.stop`, base/range.jl:879. -/
def lastLin (r : FloatRanges.Lin) : F64 := r.stop

/-- `minimum(r::AbstractUnitRange)`, base/range.jl:881. -/
def minimumUnit (r : Rng) : Jl Num :=
  if isemptyUnit r then .error (.argumentError "range must be non-empty") else .ok (Ranges.first r)

/-- `maximum(r::AbstractUnitRange)`, base/range.jl:882. -/
def maximumUnit (r : Rng) : Jl Num :=
  if isemptyUnit r then .error (.argumentError "range must be non-empty") else .ok (Ranges.last r)

/-- `argmin(r::AbstractRange)`, base/range.jl:893-901; `lastindex(r) = length(r)`. -/
def argmin (r : Rng) : Jl Num := do
  if Ranges.isEmpty r then throw (.argumentError "range must be non-empty")
  if (Ranges.step r).val > 0 then pure (Ranges.Num.lit (.bit .i64) 1) else Ranges.length r

/-- `argmax(r::AbstractRange)`, base/range.jl:910-918. -/
def argmax (r : Rng) : Jl Num := do
  if Ranges.isEmpty r then throw (.argumentError "range must be non-empty")
  if (Ranges.step r).val > 0 then Ranges.length r else pure (Ranges.Num.lit (.bit .i64) 1)

/-! ### Iteration -/

/-- `iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))`, base/range.jl:928-933,
for Float64 `StepRangeLen`. -/
def iterateSrl (r : FloatRanges.SRL) (i : I64 := FloatRanges.i64 0) : Option (F64 × I64) :=
  let i := i + FloatRanges.i64 1
  if r.len.val < i.val then none else some (r.unsafeGet i, i)

/-- The same method for `LinRange`, base/range.jl:928-933. -/
def iterateLin (r : FloatRanges.Lin) (i : I64 := FloatRanges.i64 0) : Option (F64 × I64) :=
  let i := i + FloatRanges.i64 1
  if r.len.val < i.val then none else some (r.unsafeGet i, i)

/-- `iterate(r::OrdinalRange{T}, i)`, base/range.jl:937-942. -/
def iterateOrdinal (r : Rng) (i : Num) : Jl (Option Num) := do
  if Ranges.Num.eq i (Ranges.last r) then return none
  let next ← Ranges.Num.cast r.start.ty (Ranges.Num.add i (Ranges.step r))
  pure (some next)

/-! ### Scalar indexing -/

/-- `isassigned(r::AbstractRange, i::Integer)`, base/range.jl:946-949. -/
def isassigned (r : Rng) (i : Num) : Jl Bool := do
  if i.ty = .bool then throw (.argumentError "invalid index of type Bool")
  let n ← Ranges.length r
  pure (decide (1 ≤ i.val ∧ i.val ≤ n.val))

/-- `_getindex(v::AbstractRange, i::Integer)`, base/range.jl:952-955: `checkbounds` then
`unsafe_getindex`. -/
def getindexGeneric (inbounds : Bool) (body : Jl Num) : Jl Num :=
  if inbounds then body else .error .boundsError

/-- `_in_unit_range(v::UnitRange, val, i::Integer)`, base/range.jl:957. -/
def inUnitRange (v : Rng) (val i : Num) : Bool :=
  decide (i.val > 0) && decide (val.val ≤ v.stop.val) && decide (val.val ≥ v.start.val)

/-- `_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}`, base/range.jl:968-972. -/
def getindexUnitSafe (v : Rng) (i : Num) : Jl Num :=
  let val := Ranges.Num.add v.start (Ranges.Num.sub i (Ranges.Num.one i.ty))
  if inUnitRange v val i then .ok (Ranges.Num.lit v.start.ty val.val) else .error .boundsError

/-- A Float64 `UnitRange` (start, normalized stop). -/
structure UnitF where
  start : F64
  stop : F64
  deriving DecidableEq, Repr

/-- `_getindex(v::UnitRange{T}, i::Integer) where T` (non-BitInteger `T`, here Float64),
base/range.jl:959-963: `val = convert(T, v.start + (i - oneunit(i)))`. -/
def getindexUnitF (v : UnitF) (i : I64) : Jl F64 :=
  let val := Float.F64.add v.start (FloatRanges.flt (i - FloatRanges.i64 1))
  if decide (i.val > 0) && Float.F64.le val v.stop && Float.F64.le v.start val then .ok val
  else .error .boundsError

/-- `unsafe_getindex(v::OneTo{T}, i::Integer) = convert(T, i)`, base/range.jl:984. -/
def unsafeGetindexOneTo (v : Rng) (i : Num) : Jl Num := Ranges.Num.cast v.stop.ty i

/-- `unsafe_getindex(v::AbstractRange{T}, i::Integer)`, base/range.jl:985:
`convert(T, first(v) + (i - oneunit(i))*step_hp(v))`. -/
def unsafeGetindexOrdinal (v : Rng) (i : Num) : Jl Num :=
  Ranges.Num.cast v.start.ty
    (Ranges.Num.add (Ranges.first v) (Ranges.Num.mul (Ranges.Num.sub i (Ranges.Num.one i.ty)) (stepHp v)))

/-- `unsafe_getindex(r::StepRangeLen{T}, i::Integer)`, base/range.jl:986-989, for a plain
Float64 `StepRangeLen`: `u = oftype(r.offset, i) - r.offset; convert(T, r.ref + u*r.step)`. -/
def unsafeGetindexF (r : FSRL) (i : I64) : F64 :=
  let u := i - r.offset
  Float.F64.add r.ref (Float.F64.mul (FloatRanges.flt u) r.step)

/-- The same method for integer `StepRangeLen`, base/range.jl:986-989. -/
def unsafeGetindexCounted (r : Ranges.RngLen) (i : Num) : Jl Num := do
  let i ← Ranges.Num.cast r.offset.ty i
  let u := Ranges.Num.sub i r.offset
  Ranges.Num.cast r.elementTy (Ranges.Num.add r.ref (Ranges.Num.mul u r.stride))

/-- `unsafe_getindex(r::LinRange, i::Integer) = lerpi(i-oneunit(i), r.lendiv, r.start, r.stop)`,
base/range.jl:990. -/
def unsafeGetindexLin (r : FloatRanges.Lin) (i : I64) : F64 :=
  FloatRanges.Lin.lerpi (i - FloatRanges.i64 1) r.lendiv r.start r.stop

/-- `checkbounds(::Type{Bool}, v::StepRange{<:BitInteger64,<:BitInteger64}, i::BitInteger64)`,
base/range.jl:975-978 (`Ranges.stepBounds64`). -/
def checkboundsStep64 (r : Rng) (i : Num) (hs : (Ranges.step r).ty.bits ≤ 64) (hi : i.ty.bits ≤ 64) :
    Bool := Ranges.stepBounds64 r i hs hi

/-! ### Properties -/

/-- Fallbacks: `length` of an `AbstractRange` without its own method throws
`ErrorException`; `size(r)` is `(length(r),)`; `has_offset_axes(::StepRange)` is false;
`copy(r)` and `r[:]` are `r` (ranges are immutable, base/range.jl:922-923). -/
def RangeFallbacks : Prop :=
  (∀ (α : Type) (r : α), lengthFallback r = .error (.errorException "length implementation missing")) ∧
  (∀ (α β : Type) (len : α → JlX β) (r : α), size len r = (len r).map (fun n => [n])) ∧
  (∀ r : Rng, hasOffsetAxesStep r = false) ∧
  (∀ (α : Type) (r : α), copy r = r ∧ getindexColon r = r)

theorem rangeFallbacks_proven : RangeFallbacks := by
  refine ⟨fun _ _ => rfl, ?_, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  intro α β len r
  cases h : len r <;> simp [size, h, bind, Except.bind, pure, Except.pure, Except.map]

/-- `isempty` methods: the StepRange and unit-range tests are the model's emptiness
predicate; a constructed integer `a:b` is empty exactly when `b < a`
(docstring of `(:)`, base/range.jl:54-55); a LinRange is empty iff its length is 0. -/
def IsemptyMethods : Prop :=
  (∀ r : Rng, r.kind = .step → isemptyStep r = Ranges.isEmpty r) ∧
  (∀ r : Rng, r.kind ≠ .step → isemptyUnit r = Ranges.isEmpty r) ∧
  (∀ t : IntTy, ∀ x y : JInt t, ∀ r, Colon.unitRangeSame (mkI t x) (mkI t y) = .ok r →
    (isemptyUnit r = true ↔ y.val < x.val)) ∧
  (∀ r : FloatRanges.Lin, isemptyLin r = true ↔ r.len.val = 0)

theorem isemptyMethods_proven : IsemptyMethods := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r h; simp [isemptyStep, Ranges.isEmpty, h]
  · intro r h; simp [isemptyUnit, Ranges.isEmpty, h]
  · intro t x y r h
    have hc := Colon.unitRangeConstruction_proven.1 t x y r h
    rw [Colon.unitRangeSame_mkI] at h
    by_cases hxy : x.val ≤ y.val
    · have hs := hc.2.1 hxy
      simp only [isemptyUnit, Ranges.first, Ranges.last]
      have hk : r.kind = .unit := by split at h <;> (cases h; rfl)
      simp [hk, hc.1, hs]
      all_goals omega
    · have hs := (hc.2.2 (by omega)).1
      have hk : r.kind = .unit := by split at h <;> (cases h; rfl)
      simp [isemptyUnit, Ranges.first, Ranges.last, hk, hc.1, hs]
      all_goals omega
  · intro r; simp [isemptyLin]

/-- `step` methods: a StepRange returns its stored step, a non-Bool unit range returns
`oneunit(T) - zero(T)` (value 1 of type `T`), a Bool unit range returns `true`, an
integer StepRangeLen its stored step; `step_hp` is `step` for ordinal ranges and the
TwicePrecision step for Float64 StepRangeLen; all agree with the model's `step`. -/
def StepMethods : Prop :=
  (∀ r : Rng, r.kind = .step → stepStep r = Ranges.step r) ∧
  (∀ t : IntTy, (stepUnit (.bit t)).val = 1 ∧ (stepUnit (.bit t)).ty = .bit t) ∧
  (stepUnitBool = Ranges.Num.one .bool) ∧
  (∀ r : Rng, r.kind ≠ .step → r.start.ty = .bool → Ranges.step r = stepUnitBool) ∧
  (∀ r : Ranges.RngLen, stepCounted r = Ranges.countedStep r) ∧
  (∀ r : FSRL, stepFloat r = r.step) ∧
  (∀ r : FloatRanges.SRL, (stepHpSrl r).hi = r.step.hi ∧ Float.F64.add (stepHpSrl r).hi (stepHpSrl r).lo = r.stepF) ∧
  (∀ r : Rng, stepHp r = Ranges.step r)

theorem stepMethods_proven : StepMethods := by
  refine ⟨?_, ?_, rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
  · intro r h; simp [stepStep, Ranges.step, h]
  · intro t
    simp only [stepUnit, one_mkI, zero_mkI, sub_mkI, mkI_val, mkI_ty, jsub_val, wrap_one_val,
      wrap_zero_val]
    refine ⟨?_, ?_⟩
    · exact wrapInt_of_inRange t 1 (by cases t <;> decide)
    · trivial
  · intro r h hb; simp [Ranges.step, h, hb, stepUnitBool]; rfl

/-- For a small integer type (Int8 to UInt32), a nonempty integer `a:b` has `length`
`Int(b) - Int(a) + 1`, exactly the number of elements, and `checked_length` agrees
(base/range.jl:859,862); `length(::OneTo)` of a nonnegative stop is the stop
(base/range.jl:806,817,860); `length(::StepRangeLen)` and `length(::LinRange)` are the
stored lengths (base/range.jl:807-808); the small-int `firstindex` is 1
(base/range.jl:864) and the big-int one is 1 of the difference type (base/range.jl:850). -/
def LengthMethods : Prop :=
  (∀ t : IntTy, t.bits < 64 → ∀ x y : JInt t, x.val ≤ y.val →
    ∃ n, lengthUnitSmall ⟨.unit, mkI t x, Ranges.Num.one (.bit t), mkI t y⟩ = .ok n ∧
      n.val = y.val - x.val + 1 ∧ n.ty = .bit .i64 ∧
      Ranges.length ⟨.unit, mkI t x, Ranges.Num.one (.bit t), mkI t y⟩ = .ok n ∧
      Ranges.checkedLength ⟨.unit, mkI t x, Ranges.Num.one (.bit t), mkI t y⟩ = .ok n) ∧
  (∀ t : IntTy, ∀ x : JInt t, 0 ≤ x.val →
    (lengthOneTo ⟨.oneTo, Ranges.Num.one (.bit t), Ranges.Num.one (.bit t), mkI t x⟩).val = x.val ∧
    lengthOneToBig ⟨.oneTo, Ranges.Num.one (.bit t), Ranges.Num.one (.bit t), mkI t x⟩ = mkI t x) ∧
  (∀ r : FloatRanges.SRL, lengthSrl r = r.length) ∧
  (∀ r : FloatRanges.Lin, lengthLin r = r.len) ∧
  (∀ r : Rng, (firstindexSmall r).val = 1 ∧ (firstindexBig r).val = 1)

theorem small_in_i64 (t : IntTy) (h : t.bits < 64) (x : JInt t) :
    IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max := by
  have hx := x.property
  cases t <;> simp [IntTy.bits] at h <;>
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx ⊢ <;> omega

theorem lengthMethods_proven : LengthMethods := by
  refine ⟨?_, ?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · intro t ht x y hxy
    have hx := small_in_i64 t ht x
    have hy := small_in_i64 t ht y
    have hd : IntTy.i64.min ≤ y.val - x.val ∧ y.val - x.val ≤ IntTy.i64.max := by
      have hxl := x.property; have hyl := y.property
      cases t <;> simp [IntTy.bits] at ht <;>
        simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hxl hyl ⊢ <;> omega
    have hd1 : IntTy.i64.min ≤ y.val - x.val + 1 ∧ y.val - x.val + 1 ≤ IntTy.i64.max := by
      have := small_in_i64 t ht x; have := small_in_i64 t ht y
      have hxl := x.property; have hyl := y.property
      cases t <;> simp [IntTy.bits] at ht <;>
        simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hxl hyl ⊢ <;> omega
    let n : Num := mkI .i64 (⟨y.val, hy⟩ - ⟨x.val, hx⟩ + JInt.wrap .i64 1)
    have hn : n.val = y.val - x.val + 1 := by
      show wrapInt .i64 (wrapInt .i64 (y.val - x.val) + (JInt.wrap .i64 1).val) = _
      rw [wrapInt_of_inRange .i64 _ hd, wrap_one_val, wrapInt_of_inRange .i64 _ hd1]
    have hsmall : (Ranges.NType.bit t).small = true := by simp [Ranges.NType.small, ht]
    refine ⟨n, ?_, hn, rfl, ?_, ?_⟩
    · simp [lengthUnitSmall, Ranges.first, Ranges.last, cast_mkI_ok hx, cast_mkI_ok hy, bind,
        Except.bind, pure, Except.pure, sub_mkI, one_mkI, add_mkI, n]
    · simp [Ranges.length, Ranges.first, Ranges.last, hsmall, cast_mkI_ok hx, cast_mkI_ok hy,
        bind, Except.bind, pure, Except.pure, sub_mkI, one_mkI, add_mkI, n]
    · simp [Ranges.checkedLength, Ranges.length, Ranges.first, Ranges.last, hsmall,
        cast_mkI_ok hx, cast_mkI_ok hy, bind, Except.bind, pure, Except.pure, sub_mkI, one_mkI,
        add_mkI, n]
  · intro t x hx
    refine ⟨?_, rfl⟩
    simp only [lengthOneTo, mkI_ty, zero_mkI, sub_mkI, mkI_val, jsub_val, wrap_zero_val, Int.sub_zero]
    exact wrapInt_of_inRange t _ x.property
  · intro r
    refine ⟨rfl, ?_⟩
    simp only [firstindexBig]
    generalize (Ranges.Num.sub (Ranges.last r) (Ranges.first r)).ty = ty
    cases ty with
    | bool => rfl
    | bit t => exact wrap_one_val

/-- Endpoints and extrema: `first(OneTo{T})` is 1 of type `T`; `first(r::OrdinalRange)`
and `last(r::OrdinalRange)` return the stored endpoints; `first(OneTo(m), n)` throws
for negative `n` and otherwise is `OneTo(min(m, n))` (when `min(m, n)` converts);
`last(::LinRange)` is its stop; `minimum`/`maximum` of a unit range throw ArgumentError
when empty (base/range.jl:881-882) and otherwise are `first`/`last`. -/
def EndpointMethods : Prop :=
  (∀ t : IntTy, ∀ r : Rng, r.stop.ty = .bit t → (firstOneTo r).val = 1 ∧ (firstOneTo r).ty = .bit t) ∧
  (∀ r : Rng, firstOrdinal r = .ok r.start ∧ lastOrdinal r = .ok r.stop) ∧
  (∀ (r : Rng) (n : Num), n.val < 0 → ThrowsArg (firstOneToN r n)) ∧
  (∀ r : FloatRanges.Lin, lastLin r = r.last) ∧
  (∀ r : Rng, isemptyUnit r = true →
    ThrowsArg (minimumUnit r) ∧ ThrowsArg (maximumUnit r)) ∧
  (∀ r : Rng, isemptyUnit r = false →
    minimumUnit r = .ok (Ranges.first r) ∧ maximumUnit r = .ok (Ranges.last r))

theorem endpointMethods_proven : EndpointMethods := by
  refine ⟨?_, fun r => ⟨cast_self _, cast_self _⟩, ?_, fun _ => rfl, ?_, ?_⟩
  · intro t r h
    simp only [firstOneTo, h, one_mkI, mkI_val, mkI_ty, wrap_one_val]
    constructor <;> trivial
  · intro r n h
    exact ⟨"Number of elements must be non-negative", by
      simp [firstOneToN, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]⟩
  · intro r h
    exact ⟨⟨"range must be non-empty", by simp [minimumUnit, h]⟩,
      ⟨"range must be non-empty", by simp [maximumUnit, h]⟩⟩
  · intro r h
    simp [minimumUnit, maximumUnit, h]

/-- `argmin`/`argmax` (base/range.jl:886-918): both throw ArgumentError on empty ranges;
an increasing range has `argmin == firstindex == 1` and `argmax == lastindex`, a
decreasing one the reverse. -/
def ArgExtremaMethods : Prop :=
  (∀ r : Rng, Ranges.isEmpty r = true → ThrowsArg (argmin r) ∧ ThrowsArg (argmax r)) ∧
  (∀ r : Rng, Ranges.isEmpty r = false → (Ranges.step r).val > 0 →
    argmin r = .ok (Ranges.Num.lit (.bit .i64) 1) ∧ argmax r = Ranges.length r) ∧
  (∀ r : Rng, Ranges.isEmpty r = false → ¬ (Ranges.step r).val > 0 →
    argmin r = Ranges.length r ∧ argmax r = .ok (Ranges.Num.lit (.bit .i64) 1))

theorem argExtremaMethods_proven : ArgExtremaMethods := by
  refine ⟨?_, ?_, ?_⟩
  · intro r h
    exact ⟨⟨"range must be non-empty", by simp [argmin, h, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind]⟩, ⟨"range must be non-empty", by simp [argmax, h, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind]⟩⟩
  · intro r h hs
    simp [argmin, argmax, h, hs, bind, Except.bind, pure, Except.pure]
  · intro r h hs
    simp [argmin, argmax, h, hs, bind, Except.bind, pure, Except.pure]

/-- Iteration: Float64 `StepRangeLen` and `LinRange` iteration from state `k` (for
`0 <= k < typemax(Int)`) yields `r[k+1]` while `k + 1 <= length(r)` and stops after
`length(r)` (base/range.jl:928-933); ordinal iteration from state `last(r)` stops and
otherwise advances by `step(r)` in the element type (base/range.jl:937-942), as the
model's `iterate`. -/
def IterateMethods : Prop :=
  (∀ (r : FloatRanges.SRL) (k : I64), 0 ≤ k.val → k.val < IntTy.i64.max →
    iterateSrl r k = if r.len.val < k.val + 1 then none
      else some (r.unsafeGet (k + FloatRanges.i64 1), k + FloatRanges.i64 1)) ∧
  (∀ (r : FloatRanges.Lin) (k : I64), iterateLin r k = if r.len.val < (k + FloatRanges.i64 1).val then none
      else some (r.unsafeGet (k + FloatRanges.i64 1), k + FloatRanges.i64 1)) ∧
  (∀ (r : FloatRanges.SRL) (k : I64), 0 ≤ k.val → k.val < IntTy.i64.max → r.len.val ≤ k.val →
    iterateSrl r k = none) ∧
  (∀ (r : Rng) (i : Num), iterateOrdinal r i = Ranges.iterate r (some i))

theorem iterateMethods_proven : IterateMethods := by
  have hk1 : ∀ k : I64, 0 ≤ k.val → k.val < IntTy.i64.max → (k + FloatRanges.i64 1).val = k.val + 1 := by
    intro k h0 h1
    show wrapInt .i64 (k.val + (FloatRanges.i64 1).val) = _
    have : (FloatRanges.i64 1).val = 1 := by decide
    rw [this]
    exact wrapInt_of_inRange .i64 _ ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega, by
      simp [IntTy.max, IntTy.signed, IntTy.bits] at h1 ⊢; omega⟩
  refine ⟨?_, fun _ _ => rfl, ?_, ?_⟩
  · intro r k h0 h1
    simp only [iterateSrl, hk1 k h0 h1]
  · intro r k h0 h1 hl
    simp only [iterateSrl, hk1 k h0 h1]
    rw [if_pos (by omega)]
  · intro r i
    simp [iterateOrdinal, Ranges.iterate, bind, Except.bind, pure, Except.pure]

/-- Scalar indexing: `isassigned` rejects Bool indices with ArgumentError and otherwise
tests `1 <= i <= length(r)` (base/range.jl:946-949); `_getindex` throws BoundsError
exactly when the bounds check fails (base/range.jl:952-955); the UnitRange methods
reject nonpositive indices with BoundsError (base/range.jl:957-972); OneTo indexing
returns the index converted to the element type (base/range.jl:984); a Float64
`StepRangeLen` returns `ref` at index `offset` (base/range.jl:986-989); the LinRange
element at index 1 interpolates with `t = 0` (base/range.jl:990). -/
def ScalarIndexMethods : Prop :=
  (∀ (r : Rng) (b : Bool), ThrowsArg (isassigned r ⟨.bool, b⟩)) ∧
  (∀ (r : Rng) (i n : Num), i.ty ≠ .bool → Ranges.length r = .ok n →
    isassigned r i = .ok (decide (1 ≤ i.val ∧ i.val ≤ n.val))) ∧
  (∀ (u : Jl Num), getindexGeneric true u = u ∧ getindexGeneric false u = .error .boundsError) ∧
  (∀ (v : Rng) (i : Num), i.val ≤ 0 → getindexUnitSafe v i = .error .boundsError) ∧
  (∀ (v : UnitF) (i : I64), i.val ≤ 0 → getindexUnitF v i = .error .boundsError) ∧
  (∀ (v : Rng) (i : Num), unsafeGetindexOneTo v i = Ranges.Num.cast v.stop.ty i) ∧
  (∀ r : FSRL, unsafeGetindexF r r.offset =
    Float.F64.add r.ref (Float.F64.mul (FloatRanges.flt (FloatRanges.i64 0)) r.step)) ∧
  (∀ r : FloatRanges.Lin, unsafeGetindexLin r (FloatRanges.i64 1) = r.unsafeGet (FloatRanges.i64 1)) ∧
  (∀ (v : Rng) (i : Num), unsafeGetindexOrdinal v i = Ranges.Num.cast v.start.ty
    (Ranges.Num.add (Ranges.first v) (Ranges.Num.mul (Ranges.Num.sub i (Ranges.Num.one i.ty)) (Ranges.step v)))) ∧
  (∀ (r : Ranges.RngLen) (i : Num), unsafeGetindexCounted r i = Ranges.countedUnsafeGetindex r i)

theorem scalarIndexMethods_proven : ScalarIndexMethods := by
  refine ⟨?_, ?_, fun _ => ⟨rfl, rfl⟩, ?_, ?_, fun _ _ => rfl, ?_, fun _ => rfl, fun _ _ => rfl, ?_⟩
  · intro r b
    exact ⟨"invalid index of type Bool", by
      simp [isassigned, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]⟩
  · intro r i n hi hn
    simp [isassigned, hi, hn, bind, Except.bind, pure, Except.pure]
  · intro v i hi
    simp [getindexUnitSafe, inUnitRange, show ¬ (i.val > 0) by omega]
  · intro v i hi
    simp [getindexUnitF, show ¬ (i.val > 0) by omega]
  · intro r
    simp only [unsafeGetindexF]
    congr 3
    exact Subtype.ext (by
      show wrapInt .i64 (r.offset.val - r.offset.val) = 0
      rw [Int.sub_self]; exact wrapInt_of_inRange .i64 0 (by decide))
  · intro r i
    simp only [unsafeGetindexCounted, Ranges.countedUnsafeGetindex, Ranges.countedHiprec]
    cases Ranges.Num.cast r.offset.ty i <;> rfl

def entries : List Entry := []

end Access

end JuliaLean.RangesCov

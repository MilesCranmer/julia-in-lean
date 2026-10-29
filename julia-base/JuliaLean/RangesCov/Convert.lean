import JuliaLean.RangesCov.Compare

/-!
Range conversion and promotion methods of `base/range.jl` (master `bbfa0ce4150`,
lines 285-288 and 1320-1401) and the TwicePrecision `StepRangeLen` conversions of
`base/twiceprecision.jl:541-589`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

set_option linter.unusedSimpArgs false

namespace Convert

/-! ### Type-level model -/

/-- Range types with built-in integer type parameters; `join` is a
`promote_typejoin` result. -/
inductive RT where
  | unit (T : NType)
  | oneTo (T : NType)
  | step (T S : NType)
  | srl (T R S L : NType)
  | lin (T L : NType)
  | join (a b : RT)
  deriving DecidableEq, Repr

/-- `eltype` of a range type. -/
def RT.eltype : RT → Option NType
  | .unit T | .oneTo T | .step T _ | .srl T _ _ _ | .lin T _ => some T
  | .join _ _ => none

/-- `promote_type` on built-in integer types, base/int.jl:809-822, base/bool.jl:6. -/
def pt : NType → NType → NType := Ranges.Num.promote

/-- `RangeStepStyle`: regular steps for integer element types. -/
inductive StepStyle where
  | regular | irregular
  deriving DecidableEq, Repr

/-- `RangeStepStyle(::Type{<:AbstractRange}) = RangeStepIrregular()`, base/range.jl:285, and
`RangeStepStyle(::Type{<:AbstractRange{<:Integer}}) = RangeStepRegular()`, base/range.jl:286. -/
def rangeStepStyle (integerEltype : Bool) : StepStyle :=
  if integerEltype then .regular else .irregular

/-- `convert(::Type{T}, r::AbstractRange) where {T<:AbstractRange} = r isa T ? r : T(r)::T`,
base/range.jl:288. -/
def convertRange {α : Type} (isaT : α → Bool) (ctor : α → Jl α) (r : α) : Jl α :=
  if isaT r then .ok r else ctor r

/-- `el_same`, base/range.jl:1321-1324: keep the container whose element type is already
the promoted one, else `promote_typejoin`. -/
def elSame (T : NType) (a b : RT) : RT :=
  if a.eltype = some T ∧ b.eltype = some T then a
  else if a.eltype = some T then a
  else if b.eltype = some T then b
  else .join a b

/-- `promote_rule(::Type{UnitRange{T1}}, ::Type{UnitRange{T2}})`, base/range.jl:1326-1327. -/
def promoteUnit (T1 T2 : NType) : RT := elSame (pt T1 T2) (.unit T1) (.unit T2)

/-- `promote_rule(::Type{OneTo{T1}}, ::Type{OneTo{T2}})`, base/range.jl:1331-1332. -/
def promoteOneTo (T1 T2 : NType) : RT := elSame (pt T1 T2) (.oneTo T1) (.oneTo T2)

/-- `promote_rule(a::Type{UnitRange{T1}}, ::Type{UR}) where UR<:AbstractUnitRange`,
base/range.jl:1339-1340: `promote_rule(a, UnitRange{eltype(UR)})`. -/
def promoteUnitUR (T1 E : NType) : RT := promoteUnit T1 E

/-- `promote_rule(a::Type{OneTo{T1}}, ::Type{UR})`, base/range.jl:1336-1337:
`promote_rule(UnitRange{T1}, UR)`. -/
def promoteOneToUR (T1 E : NType) : RT := promoteUnitUR T1 E

/-- `promote_rule(::Type{StepRange{T1a,T1b}}, ::Type{StepRange{T2a,T2b}})`, base/range.jl:1351-1355. -/
def promoteStep (T1a T1b T2a T2b : NType) : RT :=
  let Tb := pt T1b T2b
  elSame (pt T1a T2a) (.step T1a Tb) (.step T2a Tb)

/-- `promote_rule(a::Type{StepRange{T1a,T1b}}, ::Type{UR})`, base/range.jl:1360-1361. -/
def promoteStepUR (T1a T1b E : NType) : RT := promoteStep T1a T1b E E

/-- `promote_rule(::Type{StepRangeLen{T1,R1,S1,L1}}, ::Type{StepRangeLen{T2,R2,S2,L2}})`,
base/range.jl:1370-1373. -/
def promoteSrl (T1 R1 S1 L1 T2 R2 S2 L2 : NType) : RT :=
  let R := pt R1 R2
  let S := pt S1 S2
  let L := pt L1 L2
  elSame (pt T1 T2) (.srl T1 R S L) (.srl T2 R S L)

/-- `promote_rule(a::Type{StepRangeLen{T,R,S,L}}, ::Type{OR}) where OR<:AbstractRange`,
base/range.jl:1380-1381: against `StepRangeLen{E,E,E,Int}`. -/
def promoteSrlOR (T R S L E : NType) : RT := promoteSrl T R S L E E E (.bit .i64)

/-- `promote_rule(a::Type{LinRange{T1,L1}}, b::Type{LinRange{T2,L2}})`, base/range.jl:1388-1391. -/
def promoteLin (T1 L1 T2 L2 : NType) : RT :=
  let L := pt L1 L2
  elSame (pt T1 T2) (.lin T1 L) (.lin T2 L)

/-- `promote_rule(a::Type{LinRange{T,L}}, ::Type{OR}) where OR<:OrdinalRange`,
base/range.jl:1397-1398. -/
def promoteLinOR (T L E : NType) : RT := promoteLin T L E L

/-- `promote_rule(::Type{LinRange{A,L}}, b::Type{StepRangeLen{T2,R2,S2,L2}})`,
base/range.jl:1400-1401. -/
def promoteLinSrl (A L T2 R2 S2 L2 : NType) : RT := promoteSrl A A A L T2 R2 S2 L2

/-! ### Value conversions (integer element types) -/

/-- `UnitRange{T}(r::UnitRange{T}) where {T<:Real} = r`, base/range.jl:1328, and the
identity methods 1333, 1344, 1356-1358, 1374, 1392 (a conversion to the range's own type). -/
def convertSame {α : Type} (r : α) : α := r

/-- `UnitRange{T}(r::UnitRange) = UnitRange{T}(r.start, r.stop)`, base/range.jl:1329. -/
def unitRangeOfUnit (T : NType) (r : Rng) : Jl Rng := Colon.unitRangeT T r.start r.stop

/-- `UnitRange{T}(r::AbstractUnitRange) = UnitRange{T}(first(r), last(r))`, base/range.jl:1341. -/
def unitRangeOfAbstractUnit (T : NType) (r : Rng) : Jl Rng :=
  Colon.unitRangeT T (Ranges.first r) (Ranges.last r)

/-- `OneTo{T}(r::OneTo) = OneTo{T}(r.stop)`, base/range.jl:1334. -/
def oneToOfOneTo (T : NType) (r : Rng) : Jl Rng := Colon.oneToT T r.stop

/-- `AbstractUnitRange{T}(r::UnitRange) = UnitRange{T}(r)`, base/range.jl:1345, and
`AbstractUnitRange{T}(r::OneTo) = OneTo{T}(r)`, base/range.jl:1346 (the identity for
`AbstractUnitRange{T}(r::AbstractUnitRange{T})`, line 1344, is `convertSame`). -/
def abstractUnitRangeT (T : NType) (r : Rng) : Jl Rng :=
  if r.kind = .oneTo then oneToOfOneTo T r else unitRangeOfUnit T r

/-- `StepRange{T1,T2}(r::AbstractRange)`, base/range.jl:1362-1363. -/
def stepRangeOfRange (T1 T2 : NType) (r : Rng) : Jl Rng := do
  let a ← Ranges.Num.cast T1 (Ranges.first r)
  let s ← Ranges.Num.cast T2 (Ranges.step r)
  let b ← Ranges.Num.cast T1 (Ranges.last r)
  Colon.stepRangeTS T1 T2 a s b

/-- `StepRange(r::OrdinalRange{T,S}) = StepRange{T,S}(first(r), step(r), last(r))`,
base/range.jl:1364. -/
def stepRangeOfOrdinal (r : Rng) : Jl Rng :=
  Colon.stepRangeTS (Ranges.first r).ty (Ranges.step r).ty (Ranges.first r) (Ranges.step r) (Ranges.last r)

/-- `StepRange{T}(r::OrdinalRange{<:Any,S}) = StepRange{T,S}(first(r), step(r), last(r))`,
base/range.jl:1365. -/
def stepRangeTOfOrdinal (T : NType) (r : Rng) : Jl Rng :=
  Colon.stepRangeTS T (Ranges.step r).ty (Ranges.first r) (Ranges.step r) (Ranges.last r)

/-- `(StepRange{T1,T2} where T1)(r::AbstractRange) = StepRange{eltype(r),T2}(r)`, base/range.jl:1366. -/
def stepRangeS (T2 : NType) (r : Rng) : Jl Rng := stepRangeOfRange (Ranges.first r).ty T2 r

/-- `OrdinalRange{T, S}(r::OrdinalRange) = StepRange{T, S}(r)`, base/range.jl:1348. -/
def ordinalRangeTS (T S : NType) (r : Rng) : Jl Rng := stepRangeOfRange T S r

/-- `OrdinalRange{T, T}(r::AbstractUnitRange) = AbstractUnitRange{T}(r)`, base/range.jl:1349. -/
def ordinalRangeTT (T : NType) (r : Rng) : Jl Rng := abstractUnitRangeT T r

/-- `StepRange(r::StepRangeLen) = StepRange{eltype(r)}(r)` (base/range.jl:1367) and
`StepRange{T}(r::StepRangeLen{<:Any,<:Any,S}) = StepRange{T,S}(r)` (base/range.jl:1368),
for an integer `StepRangeLen` (`first`/`last` evaluate `unsafe_getindex`). -/
def stepRangeOfCounted (T : NType) (r : Ranges.RngLen) : Jl Rng := do
  let a ← Ranges.countedFirst r
  let b ← Ranges.countedLast r
  let a ← Ranges.Num.cast T a
  let s ← Ranges.Num.cast r.stride.ty r.stride
  let b ← Ranges.Num.cast T b
  Colon.stepRangeTS T r.stride.ty a s b

/-- `StepRange(r::StepRangeLen)`, base/range.jl:1367. -/
def stepRangeOfSrl (r : Ranges.RngLen) : Jl Rng := stepRangeOfCounted r.elementTy r

/-- `StepRangeLen{T,R,S,L}(r::StepRangeLen)`, base/range.jl:1375-1376. -/
def srlOfSrl (T R S L : NType) (r : Ranges.RngLen) : Jl Ranges.RngLen := do
  let ref ← Ranges.Num.cast R r.ref
  let st ← Ranges.Num.cast S r.stride
  let len ← Ranges.Num.cast L r.len
  let off ← Ranges.Num.cast L r.offset
  if len.val < 0 then throw (.argumentError "length cannot be negative")
  if off.val < 1 ∨ off.val > max 1 len.val then throw (.argumentError "StepRangeLen: offset")
  pure ⟨ref, st, len, off, T⟩

/-- `StepRangeLen{T}(r::StepRangeLen) = StepRangeLen(convert(T, r.ref), convert(T, r.step), r.len, r.offset)`,
base/range.jl:1377-1378. -/
def srlTOfSrl (T : NType) (r : Ranges.RngLen) : Jl Ranges.RngLen := do
  let ref ← Ranges.Num.cast T r.ref
  let st ← Ranges.Num.cast T r.stride
  srlOfSrl T T T (Ranges.Num.promote (.bit .i64) r.len.ty) ⟨ref, st, r.len, r.offset, T⟩

/-- `StepRangeLen{T,R,S,L}(r::AbstractRange) = StepRangeLen{T,R,S,L}(R(first(r)), S(step(r)), length(r))`,
base/range.jl:1382-1383. -/
def srlOfRange (T R S L : NType) (r : Rng) : Jl Ranges.RngLen := do
  let ref ← Ranges.Num.cast R (Ranges.first r)
  let st ← Ranges.Num.cast S (Ranges.step r)
  let len ← Ranges.length r
  srlOfSrl T R S L ⟨ref, st, len, Ranges.Num.lit (.bit .i64) 1, T⟩

/-- `StepRangeLen{T}(r::AbstractRange) = StepRangeLen(T(first(r)), T(step(r)), length(r))`,
base/range.jl:1384-1385. -/
def srlTOfRange (T : NType) (r : Rng) : Jl Ranges.RngLen := do
  let len ← Ranges.length r
  srlOfRange T T T (Ranges.Num.promote (.bit .i64) len.ty) r

/-- `StepRangeLen(r::AbstractRange) = StepRangeLen{eltype(r)}(r)`, base/range.jl:1386. -/
def srlOfRangeAuto (r : Rng) : Jl Ranges.RngLen := srlTOfRange (Ranges.first r).ty r

/-- An integer-element `LinRange{T,L}`: start, stop, len (the `lendiv` is recomputed). -/
structure LinI where
  start : Num
  stop : Num
  len : Num
  deriving DecidableEq

/-- `LinRange{T,L}(r::AbstractRange) = LinRange{T,L}(first(r), last(r), length(r))`,
base/range.jl:1393 (the endpoint and length conversions). -/
def linOfRange (T L : NType) (r : Rng) : Jl LinI := do
  let a ← Ranges.Num.cast T (Ranges.first r)
  let b ← Ranges.Num.cast T (Ranges.last r)
  let n ← Ranges.length r
  let n ← Ranges.Num.cast L n
  if n.val < 0 then throw (.argumentError "negative length")
  pure ⟨a, b, n⟩

/-- `LinRange{T}(r::AbstractRange) = LinRange{T,typeof(length(r))}(first(r), last(r), length(r))`,
base/range.jl:1394. -/
def linTOfRange (T : NType) (r : Rng) : Jl LinI := do
  let n ← Ranges.length r
  linOfRange T n.ty r

/-- `LinRange(r::AbstractRange{T}) = LinRange{T}(r)`, base/range.jl:1395. -/
def linOfRangeAuto (r : Rng) : Jl LinI := linTOfRange (Ranges.first r).ty r

/-- `LinRange{T,L}(r::LinRange{T,L}) = r`, base/range.jl:1392 (`convertSame`). -/
def linSame (r : LinI) : LinI := convertSame r

/-! ### TwicePrecision conversions, base/twiceprecision.jl:541-589 -/

/-- `StepRangeLen{T,R,S,L}(r::StepRangeLen{T,R,S,L}) = r` for TwicePrecision types,
base/twiceprecision.jl:541. -/
def srlTpSame (r : FloatRanges.SRL) : FloatRanges.SRL := r

/-- `_convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::StepRangeLen{<:Integer})`,
base/twiceprecision.jl:556-558, to `StepRangeLen{Float64,TwicePrecision,TwicePrecision,Int}`. -/
def convertSrlInt {t : IntTy} (ref stride : JInt t) (len offset : I64) : Jl FloatRanges.SRL := do
  let r ← FloatRanges.TP.ofInt ref
  let s ← FloatRanges.TP.ofInt stride
  FloatRanges.SRL.mk' r s len offset

/-- `_convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::AbstractRange{<:Integer})`,
base/twiceprecision.jl:560-562: `R(first(r)), S(step(r)), L(length(r))`. -/
def convertRangeInt {t : IntTy} (first stride : JInt t) (len : I64) : Jl FloatRanges.SRL :=
  convertSrlInt first stride len (FloatRanges.i64 1)

/-- `__convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::StepRangeLen{U})`, base/twiceprecision.jl:584-586,
for a plain Float64 `StepRangeLen`: `R(r.ref), S(r.step), L(length(r)), L(r.offset)`. -/
def convertSrlFloatFallback (r : FSRL) : Jl FloatRanges.SRL :=
  FloatRanges.SRL.mk' (FloatRanges.TP.ofF r.ref) (FloatRanges.TP.ofF r.step) r.len r.offset

/-- `__convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::AbstractRange{U})`, base/twiceprecision.jl:587-589:
`R(first(r)), S(step(r)), L(length(r))`. -/
def convertRangeFloatFallback (first step : F64) (len : I64) : Jl FloatRanges.SRL :=
  FloatRanges.SRL.mk' (FloatRanges.TP.ofF first) (FloatRanges.TP.ofF step) len (FloatRanges.i64 1)

/-- The rational-transfer test of `_convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::AbstractRange{U})`,
base/twiceprecision.jl:567-580: the scaled numerators and common denominator when start
and step have exact rational approximations that `floatrange` can use. -/
def ratTransfer (f s : F64) : Jl (Option (I64 × I64 × I64)) := do
  let (start_n, start_d) ← FloatRanges.rat f
  let (step_n, step_d) ← FloatRanges.rat s
  if start_d.val ≠ 0 ∧ step_d.val ≠ 0 ∧
      Float.F64.eq (Float.F64.div (FloatRanges.flt start_n) (FloatRanges.flt start_d)) f ∧
      Float.F64.eq (Float.F64.div (FloatRanges.flt step_n) (FloatRanges.flt step_d)) s then
    let den ← FloatRanges.lcmUnchecked start_d step_d
    let m := FloatRanges.maxintF
    if den.val ≠ 0 ∧ Float.F64.le (Float.F64.abs (Float.F64.mul f (FloatRanges.flt den))) m ∧
        Float.F64.le (Float.F64.abs (Float.F64.mul s (FloatRanges.flt den))) m then
      let r1 ← JInt.remInt den start_d
      let r2 ← JInt.remInt den step_d
      if r1.val = 0 ∧ r2.val = 0 then
        let q1 ← JInt.div den start_d
        let q2 ← JInt.div den step_d
        return some (start_n * q1, step_n * q2, den)
  return none

/-- `_convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::AbstractRange{U})`, base/twiceprecision.jl:564-582,
for a Float64 range with `first(r) = f`, `step(r) = s`: transfer exact rational
approximations through `floatrange`, else fall back to `__convertSRL`. -/
def convertSrlFloat (f s : F64) (len : I64) : Jl FloatRanges.SRL := do
  match ← ratTransfer f s with
  | some (a, st, den) => FloatRanges.floatrange a st len den
  | none => convertRangeFloatFallback f s len

/-- `StepRangeLen{T,R,S,L}(r::StepRangeLen)` for TwicePrecision `R`, `S`
(base/twiceprecision.jl:543-544), `StepRangeLen{Float64}(r::StepRangeLen)` (546-547) and
`StepRangeLen{Float64}(r::AbstractRange)` (551-552) all call `_convertSRL` with
`StepRangeLen{Float64,TwicePrecision{Float64},TwicePrecision{Float64},Int}`. -/
def srlFloat64OfInt {t : IntTy} (ref stride : JInt t) (len offset : I64) : Jl FloatRanges.SRL :=
  convertSrlInt ref stride len offset

/-- `StepRangeLen{T}(r::StepRangeLen) where {T<:IEEEFloat}` (base/twiceprecision.jl:548-549) and
`StepRangeLen{T}(r::AbstractRange) where {T<:IEEEFloat}` (553-554) use
`StepRangeLen{T,Float64,Float64,Int}`: for T = Float64 the reference and step are the
Float64 values of the integer ones. -/
def srlIeeeOfInt {t : IntTy} (ref stride : JInt t) (len offset : I64) : FSRL :=
  ⟨FloatRanges.flt ref, FloatRanges.flt stride, len, offset⟩

/-! ### Properties -/

theorem pt_cases (a b : NType) : pt a b = a ∨ pt a b = b := by
  cases a with
  | bool => right; cases b <;> rfl
  | bit s =>
    cases b with
    | bool => left; rfl
    | bit t =>
      cases s <;> cases t <;> simp [pt, Ranges.Num.promote, IntTy.promote, IntTy.bits, IntTy.signed]

/-- Promotion of range types (base/range.jl:1320-1401): every promote_rule between two
range types with built-in integer parameters produces a range type whose element type
is `promote_type` of the element types (never a `promote_typejoin`), and
`RangeStepStyle` is regular exactly for integer element types. -/
def PromotionRules : Prop :=
  (∀ T1 T2 : NType, (promoteUnit T1 T2).eltype = some (pt T1 T2) ∧
    (promoteOneTo T1 T2).eltype = some (pt T1 T2) ∧
    (promoteUnitUR T1 T2).eltype = some (pt T1 T2) ∧
    (promoteOneToUR T1 T2).eltype = some (pt T1 T2) ∧
    (∀ S1 S2, (promoteStep T1 S1 T2 S2).eltype = some (pt T1 T2)) ∧
    (promoteStepUR T1 T1 T2).eltype = some (pt T1 T2) ∧
    (∀ R1 S1 L1 R2 S2 L2, (promoteSrl T1 R1 S1 L1 T2 R2 S2 L2).eltype = some (pt T1 T2)) ∧
    (∀ R S L, (promoteSrlOR T1 R S L T2).eltype = some (pt T1 T2)) ∧
    (∀ L1 L2, (promoteLin T1 L1 T2 L2).eltype = some (pt T1 T2)) ∧
    (∀ L, (promoteLinOR T1 L T2).eltype = some (pt T1 T2)) ∧
    (∀ L R2 S2 L2, (promoteLinSrl T1 L T2 R2 S2 L2).eltype = some (pt T1 T2))) ∧
  (∀ T a b, a.eltype = some T → elSame T a b = a) ∧
  (rangeStepStyle true = .regular ∧ rangeStepStyle false = .irregular) ∧
  (∀ (α : Type) (isaT : α → Bool) (ctor : α → Jl α) (r : α), isaT r = true → convertRange isaT ctor r = .ok r)

theorem elSame_eltype (T : NType) (a b : RT) (ha : a.eltype = some T ∨ b.eltype = some T) :
    (elSame T a b).eltype = some T := by
  unfold elSame
  by_cases h1 : a.eltype = some T ∧ b.eltype = some T
  · simp [h1]
  · by_cases h2 : a.eltype = some T
    · simp [h1, h2]
    · have h3 : b.eltype = some T := by
        rcases ha with h | h
        · exact absurd h h2
        · exact h
      rw [if_neg h1, if_neg h2, if_pos h3]; exact h3

theorem promotionRules_proven : PromotionRules := by
  refine ⟨?_, ?_, ⟨rfl, rfl⟩, ?_⟩
  · intro T1 T2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp only [promoteUnit, promoteOneTo, promoteUnitUR, promoteOneToUR, promoteStep,
        promoteStepUR, promoteSrl, promoteSrlOR, promoteLin, promoteLinOR, promoteLinSrl] <;>
      apply elSame_eltype <;> rcases pt_cases T1 T2 with h | h <;> simp [h, RT.eltype]
  · intro T a b h
    unfold elSame
    by_cases h1 : b.eltype = some T <;> simp [h, h1]
  · intro α isaT ctor r h
    simp [convertRange, h]

/-- Converting an integer range to another integer element type succeeds whenever every
element is representable in the target type; in particular converting an empty range
always succeeds (convert(T, r) for AbstractRange, base/range.jl:288, as for the
collected vector). -/
def UnitRangeConvertEmpty : Prop :=
  ∀ (T : NType) (r : Rng), r.kind = .unit → Ranges.isEmpty r = true → T ≠ .bool →
    ∃ out, unitRangeOfUnit T r = .ok out ∧ Ranges.isEmpty out = true

theorem unitRangeConvertEmpty_refuted : ¬ UnitRangeConvertEmpty := by
  intro h
  let r : Rng := ⟨.unit, Ranges.Num.lit (.bit .i64) 0, Ranges.Num.lit (.bit .i64) 1,
    Ranges.Num.lit (.bit .i64) (-1)⟩
  obtain ⟨out, hout, _⟩ := h (.bit .u8) r rfl (by decide +kernel) (by decide)
  have hc : unitRangeOfUnit (.bit .u8) r = .error (.inexactError "UInt8") := by decide +kernel
  rw [hc] at hout
  cases hout

/-- Integer range conversions: the identity methods return their argument; converting
a nonempty same-type unit range keeps its endpoints; `OneTo{T}(OneTo(n))`,
`AbstractUnitRange{T}`, `OrdinalRange{T,S}`, `StepRange(r)`, `StepRangeLen{T}(r)` and
`LinRange(r)` are the documented compositions (base/range.jl:1328-1395). -/
def IntegerConversions : Prop :=
  (∀ (α : Type) (r : α), convertSame r = r) ∧
  (∀ t : IntTy, ∀ x y : JInt t, x.val ≤ y.val →
    unitRangeOfUnit (.bit t) ⟨.unit, mkI t x, mkI t (JInt.wrap t 1), mkI t y⟩ =
      .ok ⟨.unit, mkI t x, mkI t (JInt.wrap t 1), mkI t y⟩) ∧
  (∀ T r, abstractUnitRangeT T r = if r.kind = .oneTo then Colon.oneToT T r.stop else unitRangeOfUnit T r) ∧
  (∀ T S r, ordinalRangeTS T S r = stepRangeOfRange T S r) ∧
  (∀ T r, ordinalRangeTT T r = abstractUnitRangeT T r) ∧
  (∀ T2 r, stepRangeS T2 r = stepRangeOfRange (Ranges.first r).ty T2 r) ∧
  (∀ r : LinI, linSame r = r)

theorem integerConversions_proven : IntegerConversions := by
  refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl⟩
  · intro t x y hxy
    have h := Colon.unitRangeSame_mkI t x y
    simp only [unitRangeOfUnit]
    simp only [Colon.unitRangeSame, mkI_ty] at h
    rw [h, if_pos (by omega)]

/-- TwicePrecision conversions keep the length and offset, and the identity method
returns its argument (base/twiceprecision.jl:541-589); converting to
`StepRangeLen{Float64,Float64,Float64}` stores Float64 copies of the integer fields. -/
def TwiceConversions : Prop :=
  (∀ r : FloatRanges.SRL, srlTpSame r = r) ∧
  (∀ {t : IntTy} (ref stride : JInt t) (len offset : I64) out,
    convertSrlInt ref stride len offset = .ok out → out.len = len ∧ out.offset = offset) ∧
  (∀ r : FSRL, ∀ out, convertSrlFloatFallback r = .ok out →
    out.len = r.len ∧ out.ref = FloatRanges.TP.ofF r.ref ∧ out.step = FloatRanges.TP.ofF r.step) ∧
  (∀ (f s : F64) (len : I64) out, convertRangeFloatFallback f s len = .ok out → out.len = len) ∧
  (∀ (f s : F64) (len : I64) out, convertSrlFloat f s len = .ok out → out.len = len) ∧
  (∀ {t : IntTy} (ref stride : JInt t) (len offset : I64),
    srlFloat64OfInt ref stride len offset = convertSrlInt ref stride len offset) ∧
  (∀ {t : IntTy} (ref stride : JInt t) (len offset : I64),
    (srlIeeeOfInt ref stride len offset).ref = FloatRanges.flt ref ∧ (srlIeeeOfInt ref stride len offset).len = len)

theorem mk'_fields (ref step : TP) (len off : I64) (out : FloatRanges.SRL)
    (h : FloatRanges.SRL.mk' ref step len off = .ok out) :
    out.ref = ref ∧ out.step = step ∧ out.len = len ∧ out.offset = off := by
  unfold FloatRanges.SRL.mk' at h
  split at h
  · cases h
  · split at h
    · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
    · cases h

theorem twiceConversions_proven : TwiceConversions := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, fun _ _ _ _ => rfl, fun _ _ _ _ => ⟨rfl, rfl⟩⟩
  · intro t ref stride len offset out h
    simp only [convertSrlInt, bind, Except.bind] at h
    split at h <;> try cases h
    split at h <;> try cases h
    have := mk'_fields _ _ _ _ _ h
    exact ⟨this.2.2.1, this.2.2.2⟩
  · intro r out h
    have := mk'_fields _ _ _ _ _ h
    exact ⟨this.2.2.1, this.1, this.2.1⟩
  · intro f s len out h
    exact (mk'_fields _ _ _ _ _ h).2.2.1
  · intro f s len out h
    simp only [convertSrlFloat, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i o _
      cases o with
      | none => exact (mk'_fields _ _ _ _ _ h).2.2.1
      | some v =>
        obtain ⟨a, st, den⟩ := v
        exact FloatRanges.floatrange_len a st len den out h

def entries : List Entry := []

end Convert

end JuliaLean.RangesCov

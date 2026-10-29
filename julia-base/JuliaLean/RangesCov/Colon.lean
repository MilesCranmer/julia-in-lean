import JuliaLean.RangesCov.Basic

/-!
`(:)`, `range` dispatch, and the `StepRange`, `UnitRange` and `OneTo`
constructors of `base/range.jl` (master `bbfa0ce4150`) for built-in integer
element types, plus the `Char` (non-`Real`) colon methods.
-/

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Colon

/-! ### `_range_wrapping_*`, base/range.jl:31-39 -/

/-- `_range_wrapping_add(x::_RangeWrappingInteger, y::_RangeWrappingInteger) = x +% y`,
base/range.jl:34; `+%` promotes and wraps, base/promotion.jl:459, base/int.jl:93. -/
def wrappingAddInt (x y : Num) : Num := Ranges.Num.add x y
/-- `_range_wrapping_add(x, y) = x + y`, base/range.jl:35 (Bool arguments). -/
def wrappingAddAny (x y : Num) : Num := Ranges.Num.add x y
/-- `_range_wrapping_sub(x::_RangeWrappingInteger, y::_RangeWrappingInteger) = x -% y`,
base/range.jl:36. -/
def wrappingSubInt (x y : Num) : Num := Ranges.Num.sub x y
/-- `_range_wrapping_sub(x, y) = x - y`, base/range.jl:37. -/
def wrappingSubAny (x y : Num) : Num := Ranges.Num.sub x y
/-- `_range_wrapping_mul(x::_RangeWrappingInteger, y::_RangeWrappingInteger) = x *% y`,
base/range.jl:38. -/
def wrappingMulInt (x y : Num) : Num := Ranges.Num.mul x y
/-- `_range_wrapping_mul(x, y) = x * y`, base/range.jl:39. -/
def wrappingMulAny (x y : Num) : Num := Ranges.Num.mul x y

/-- `_RangeWrappingInteger`, base/range.jl:31-32: the ten BitInteger types (not Bool). -/
def isWrapping (x : Num) : Bool := x.ty != .bool

/-- Method selection among base/range.jl:34-35. -/
def rangeWrappingAdd (x y : Num) : Num :=
  if isWrapping x && isWrapping y then wrappingAddInt x y else wrappingAddAny x y
/-- Method selection among base/range.jl:36-37. -/
def rangeWrappingSub (x y : Num) : Num :=
  if isWrapping x && isWrapping y then wrappingSubInt x y else wrappingSubAny x y
/-- Method selection among base/range.jl:38-39. -/
def rangeWrappingMul (x y : Num) : Num :=
  if isWrapping x && isWrapping y then wrappingMulInt x y else wrappingMulAny x y

/-- The generic methods on Float64: `x + y`, `x - y`, `x * y`, base/range.jl:35,37,39. -/
def wrappingAddF (x y : F64) : F64 := Float.F64.add x y
def wrappingSubF (x y : F64) : F64 := Float.F64.sub x y
def wrappingMulF (x y : F64) : F64 := Float.F64.mul x y

/-! ### Integer `UnitRange` and `StepRange` construction -/

/-- `unitrange_last(start::Integer, stop::Integer)`, base/range.jl:439-441. -/
def unitrangeLastInt (a b : Num) : Jl Num :=
  if b.val ≥ a.val then .ok b
  else Ranges.Num.cast b.ty (rangeWrappingSub a (Ranges.Num.one (rangeWrappingSub a b).ty))

/-- `UnitRange{T}(start::T, stop::T)`, the inner constructor, base/range.jl:428. -/
def unitRangeInner (a b : Num) : Jl Rng := do
  let z ← unitrangeLastInt a b
  pure ⟨.unit, a, Ranges.Num.one a.ty, z⟩

/-- `UnitRange{T}(start, stop) where {T<:Real}`, base/range.jl:430. -/
def unitRangeT (T : NType) (a b : Num) : Jl Rng := do
  let a ← Ranges.Num.cast T a
  let b ← Ranges.Num.cast T b
  unitRangeInner a b

/-- `UnitRange(start::T, stop::T) where {T<:Real}`, base/range.jl:431. -/
def unitRangeSame (a b : Num) : Jl Rng := unitRangeT a.ty a b

/-- `UnitRange(start, stop)`, base/range.jl:432-436: promotion (`not_sametype` never
fires for built-in integers), then the same-type method. -/
def unitRangePromote (a b : Num) : Jl Rng := do
  let ty := Ranges.Num.promote a.ty b.ty
  let a ← Ranges.Num.cast ty a
  let b ← Ranges.Num.cast ty b
  unitRangeSame a b

/-- `UnitRange(r::AbstractUnitRange) = UnitRange(first(r), last(r))`, base/range.jl:1342. -/
def unitRangeOfRange (r : Rng) : Jl Rng := unitRangePromote (Ranges.first r) (Ranges.last r)

/-- `unitrange(x::AbstractUnitRange) = UnitRange(x)`, base/range.jl:447. -/
def unitrange (r : Rng) : Jl Rng := unitRangeOfRange r

/-- `steprange_last_empty(start::Integer, step, stop)::typeof(stop)`, base/range.jl:389-398. -/
def steprangeLastEmptyInt (a s b : Num) : Jl Num :=
  Ranges.Num.cast b.ty (if s.val > 0 then rangeWrappingSub a (Ranges.Num.one s.ty)
    else rangeWrappingAdd a (Ranges.Num.one s.ty))

/-- `steprange_last_empty(start::Bool, step, stop) = start ⊻ (step > zero(step))`,
base/range.jl:399. -/
def steprangeLastEmptyBool (a s : Num) : Num :=
  Ranges.Num.lit .bool (if decide (a.val ≠ 0) != decide (s.val > 0) then 1 else 0)

/-- Method selection among base/range.jl:389-399 for integer starts. -/
def steprangeLastEmpty (a s b : Num) : Jl Num :=
  if a.ty = .bool then .ok (steprangeLastEmptyBool a s) else steprangeLastEmptyInt a s b

/-- `overflow_case(absdiff, absstep) = convert(typeof(absdiff), unsigned(absdiff) % absstep)`,
base/range.jl:377. -/
def overflowCase (absdiff absstep : Num) : Jl Num := do
  let r ← Ranges.Num.rem (Ranges.Num.unsigned absdiff) absstep
  Ranges.Num.cast absdiff.ty r

/-- `StepRange{T,S}(start, step, stop)`, the inner constructor, base/range.jl:344-349:
convert start, step and stop, then store `steprange_last`. -/
def stepRangeTS (T S : NType) (a s b : Num) : Jl Rng := do
  let a ← Ranges.Num.cast T a
  let s ← Ranges.Num.cast S s
  let b ← Ranges.Num.cast T b
  let z ← Ranges.steprangeLast a s b
  pure ⟨.step, a, s, z⟩

/-- `StepRange{T}(start, step::S, stop) = StepRange{T,S}(start, step, stop)`, base/range.jl:403. -/
def stepRangeT (T : NType) (a s b : Num) : Jl Rng := stepRangeTS T s.ty a s b

/-- `StepRange(start::T, step::S, stop::T)`, base/range.jl:404 (a `MethodError` when the
endpoint types differ). -/
def stepRangeOuter (a s b : Num) : Jl Rng :=
  if a.ty ≠ b.ty then .error (.methodError "StepRange") else stepRangeTS a.ty s.ty a s b

/-! ### Integer colon methods -/

/-- `(:)(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)`, base/range.jl:5. -/
def colonSame2 (a b : Num) : Jl Rng := unitRangeT a.ty a b

/-- `(:)(a::Real, b::Real) = (:)(promote(a, b)...)`, base/range.jl:3. -/
def colonPromote2 (a b : Num) : Jl Rng := do
  let ty := Ranges.Num.promote a.ty b.ty
  let a ← Ranges.Num.cast ty a
  let b ← Ranges.Num.cast ty b
  colonSame2 a b

/-- `_colon(::Ordered, ::Any, start::T, step, stop::T) = StepRange(start, step, stop)`,
base/range.jl:24 (integers are `ArithmeticWraps`). -/
def colonOrdered (a s b : Num) : Jl Rng := stepRangeOuter a s b

/-- `(:)(start::T, step::T, stop::T) where {T<:Real}`, base/range.jl:22-23. -/
def colonSame3 (a s b : Num) : Jl Rng := colonOrdered a s b

/-- `_colon(start::T, step, stop::T)`, base/range.jl:68-71: `T′ = typeof(start+zero(step))`. -/
def colonWiden (a s b : Num) : Jl Rng := do
  let T' := (Ranges.Num.add a (Ranges.Num.zero s.ty)).ty
  let a ← Ranges.Num.cast T' a
  let b ← Ranges.Num.cast T' b
  stepRangeOuter a s b

/-- `(:)(start::T, step, stop::T) where {T<:Real} = _colon(start, step, stop)`, base/range.jl:65,
with base/range.jl:22 chosen when the step has the endpoint type too. -/
def colonTyped (a s b : Num) : Jl Rng :=
  if s.ty = a.ty then colonSame3 a s b else colonWiden a s b

/-- `(:)(start::A, step, stop::C) where {A<:Real, C<:Real}`, base/range.jl:10-11. -/
def colonPromote3 (a s b : Num) : Jl Rng := do
  let ty := Ranges.Num.promote a.ty b.ty
  let a ← Ranges.Num.cast ty a
  let b ← Ranges.Num.cast ty b
  colonTyped a s b

/-! ### `Char` (non-`Real`) colon methods -/

/-- A `StepRange{Char,Int}`: code points and an `Int` step. -/
structure CharRng where
  start : Nat
  step : Int
  stop : Nat
  deriving DecidableEq, Repr

/-- `x::Char - y::Char = Int(x) - Int(y)`, base/char.jl:281. -/
def charSub (x y : Nat) : Int := (x : Int) - y

/-- `x::Char + y::Integer`, base/char.jl:286-289: `Char(UInt32(x) + y)`, an
`InexactError` outside `UInt32`. -/
def charAdd (x : Nat) (y : Int) : Jl Nat :=
  if 0 ≤ (x : Int) + y ∧ (x : Int) + y < 2 ^ 32 then .ok ((x : Int) + y).toNat
  else .error (.inexactError "UInt32")

/-- `steprange_last` for `Char` endpoints, base/range.jl:353-387: the generic
`steprange_last_empty(start, step, stop) = stop` (base/range.jl:401) keeps a
user-supplied stop for empty ranges. -/
def charSteprangeLast (a : Nat) (s : Int) (b : Nat) : Jl Nat := do
  if s = 0 then throw (.argumentError "step cannot be zero")
  if b = a then return b
  if decide (s > 0) != decide (b > a) then return b
  let (absdiff, absstep) := if b > a then (charSub b a, s) else (charSub a b, -s)
  let remain := absdiff.tmod absstep
  if b > a then charAdd b (-remain) else charAdd b remain

/-- `StepRange{Char,Int}(start, step, stop)`, base/range.jl:344-349. -/
def charStepRange (a : Nat) (s : Int) (b : Nat) : Jl CharRng := do
  let z ← charSteprangeLast a s b
  pure ⟨a, s, z⟩

/-- `_colon(start::T, step, stop::T)`, base/range.jl:68-71, for `Char`:
`typeof(start + zero(step)) == Char`. -/
def charColonWiden (a : Nat) (s : Int) (b : Nat) : Jl CharRng := do
  let a ← charAdd a 0
  let b ← charAdd b 0
  charStepRange a s b

/-- `(:)(start::T, step, stop::T) where {T} = _colon(start, step, stop)`, base/range.jl:64. -/
def charColon3 (a : Nat) (s : Int) (b : Nat) : Jl CharRng := charColonWiden a s b

/-- `(:)(start::T, stop::T) where {T}`, base/range.jl:7: the step is
`oftype(stop >= start ? stop - start : start - stop, 1)`, an `Int` one. -/
def charColon2 (a b : Nat) : Jl CharRng :=
  let d := if b ≥ a then charSub b a else charSub a b
  let one : Int := d - d + 1
  charColon3 a one b

/-! ### `OneTo`, base/range.jl:485-507 -/

/-- `OneTo{T}(stop)`, base/range.jl:487-491, for an integer `stop` converted to `T`;
`throwbool` (line 488) is the Bool rejection. -/
def oneToT (T : NType) (n : Num) : Jl Rng := do
  if T = .bool then throw (.argumentError "invalid index of type Bool")
  let m := Ranges.Num.max (Ranges.Num.zero T) n
  let m ← Ranges.Num.cast T m
  pure ⟨.oneTo, Ranges.Num.one T, Ranges.Num.one T, m⟩

/-- `OneTo{T}(r::AbstractRange)`, base/range.jl:493-501; `throwstart`, `throwstep`
and `throwbool` are lines 494-496. -/
def oneToOfRange (T : NType) (r : Rng) : Jl Rng := do
  if (Ranges.first r).val ≠ 1 then throw (.argumentError "first element must be 1")
  if (Ranges.step r).val ≠ 1 then throw (.argumentError "step must be 1")
  if T = .bool then throw (.argumentError "invalid index: of type Bool")
  let m ← Ranges.Num.cast T (Ranges.Num.max (Ranges.Num.zero T) (Ranges.last r))
  pure ⟨.oneTo, Ranges.Num.one T, Ranges.Num.one T, m⟩

/-- `unchecked_oneto(stop::Integer) = new{typeof(stop)}(stop)`, base/range.jl:503. -/
def uncheckedOneto (n : Num) : Rng := ⟨.oneTo, Ranges.Num.one n.ty, Ranges.Num.one n.ty, n⟩

/-- `OneTo(stop::T) where {T<:Integer} = OneTo{T}(stop)`, base/range.jl:505. -/
def oneTo (n : Num) : Jl Rng := oneToT n.ty n

/-- `OneTo(r::AbstractRange{T}) where {T<:Integer} = OneTo{T}(r)`, base/range.jl:506. -/
def oneToRange (r : Rng) : Jl Rng := oneToOfRange (Ranges.first r).ty r

/-- `oneto(r) = OneTo(r)`, base/range.jl:507. -/
def oneto (r : Rng) : Jl Rng := oneToRange r

/-! ### Properties -/

/-- The wrapping helpers agree with Julia's `+`, `-`, `*` on every pair of built-in
integers (they never throw and wrap exactly where Julia's operators wrap), and the
generic Float64 methods are the IEEE operations. -/
def RangeWrappingArith : Prop :=
  (∀ x y : Num, rangeWrappingAdd x y = Ranges.Num.add x y ∧
    rangeWrappingSub x y = Ranges.Num.sub x y ∧ rangeWrappingMul x y = Ranges.Num.mul x y) ∧
  (∀ t : IntTy, ∀ x y : JInt t,
    (rangeWrappingAdd (mkI t x) (mkI t y)).val = wrapInt t (x.val + y.val) ∧
    (rangeWrappingSub (mkI t x) (mkI t y)).val = wrapInt t (x.val - y.val) ∧
    (rangeWrappingMul (mkI t x) (mkI t y)).val = wrapInt t (x.val * y.val)) ∧
  (∀ x y : F64, wrappingAddF x y = Float.F64.add x y ∧ wrappingSubF x y = Float.F64.sub x y ∧
    wrappingMulF x y = Float.F64.mul x y)

theorem rangeWrappingArith_proven : RangeWrappingArith := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simp only [rangeWrappingAdd, rangeWrappingSub, rangeWrappingMul, wrappingAddInt,
      wrappingAddAny, wrappingSubInt, wrappingSubAny, wrappingMulInt, wrappingMulAny]
    split <;> exact ⟨rfl, rfl, rfl⟩
  · intro t x y
    have hw : isWrapping (mkI t x) = true ∧ isWrapping (mkI t y) = true := by
      simp [isWrapping]
    simp only [rangeWrappingAdd, rangeWrappingSub, rangeWrappingMul, hw.1, hw.2, Bool.and_self,
      if_true, wrappingAddInt, wrappingSubInt, wrappingMulInt, add_mkI, sub_mkI, mul_mkI, mkI_val]
    exact ⟨rfl, rfl, rfl⟩
  · intro x y
    exact ⟨rfl, rfl, rfl⟩

theorem unitRangeSame_mkI (t : IntTy) (x y : JInt t) :
    unitRangeSame (mkI t x) (mkI t y) =
      if y.val ≥ x.val then .ok ⟨.unit, mkI t x, mkI t (JInt.wrap t 1), mkI t y⟩
      else .ok ⟨.unit, mkI t x, mkI t (JInt.wrap t 1), mkI t (x - JInt.wrap t 1)⟩ := by
  have hw : ∀ z : JInt t, isWrapping (mkI t z) = true := by intro z; simp [isWrapping]
  by_cases hxy : y.val ≥ x.val
  · simp [unitRangeSame, unitRangeT, cast_mkI, bind, Except.bind, unitRangeInner,
      unitrangeLastInt, hxy, one_mkI, pure, Except.pure]
  · simp [unitRangeSame, unitRangeT, cast_mkI, bind, Except.bind, unitRangeInner,
      unitrangeLastInt, hxy, one_mkI, pure, Except.pure, rangeWrappingSub, hw, wrappingSubInt,
      sub_mkI]

/-- `a:b` and `UnitRange(a, b)` on built-in integers: the endpoints are kept when
`b >= a`; otherwise the stop is normalized to `a-1`, which makes the range empty
(docstring of `(:)`, base/range.jl:54-55: "when `b < a`, an empty range will be
constructed and normalized to `a:a-1`"). Mixed-type construction is construction
from the promoted endpoints, and `unitrange(r)` is `UnitRange(first(r), last(r))`. -/
def UnitRangeConstruction : Prop :=
  (∀ t : IntTy, ∀ x y : JInt t, ∀ r, unitRangeSame (mkI t x) (mkI t y) = .ok r →
    r.start = mkI t x ∧ (x.val ≤ y.val → r.stop = mkI t y) ∧
    (y.val < x.val → r.stop.val = x.val - 1 ∧ r.stop.ty = .bit t ∧ Ranges.isEmpty r = true)) ∧
  (∀ a b : Num, colonPromote2 a b = unitRangePromote a b) ∧
  (∀ r : Rng, unitrange r = unitRangePromote (Ranges.first r) (Ranges.last r))

theorem unitRangeConstruction_proven : UnitRangeConstruction := by
  refine ⟨?_, fun _ _ => rfl, fun _ => rfl⟩
  intro t x y r h
  rw [unitRangeSame_mkI] at h
  by_cases hxy : y.val ≥ x.val
  · rw [if_pos hxy] at h
    cases h
    exact ⟨rfl, fun _ => rfl, fun h' => absurd hxy (by omega)⟩
  · rw [if_neg hxy] at h
    cases h
    have hbits : t.min ≤ x.val - 1 ∧ x.val - 1 ≤ t.max := by
      have := y.property; have := x.property; constructor <;> omega
    have hv : (x - JInt.wrap t 1).val = x.val - 1 := by
      rw [jsub_val, wrap_one_val]; exact wrapInt_of_inRange t _ hbits
    refine ⟨rfl, fun h' => absurd h' (by omega), fun _ => ⟨by simp [hv], rfl, ?_⟩⟩
    simp [Ranges.isEmpty, Ranges.first, Ranges.last, hv] <;> omega

/-- `StepRange` construction on built-in integers: a zero step throws ArgumentError
("step cannot be zero", base/range.jl:361) whenever the arguments convert; `a:s:a`
is the one-element range ending at `a`; `StepRange{T}` is `StepRange{T,typeof(step)}`;
endpoints of different types are a `MethodError`; same-type `a:s:b` is
`StepRange(a, s, b)`. -/
def StepRangeConstruction : Prop :=
  (∀ a s b : Num, a.ty = b.ty → s.val = 0 → ThrowsArg (stepRangeOuter a s b)) ∧
  (∀ a s : Num, s.val ≠ 0 → stepRangeOuter a s a = .ok ⟨.step, a, s, a⟩) ∧
  (∀ T a s b, stepRangeT T a s b = stepRangeTS T s.ty a s b) ∧
  (∀ a s b : Num, a.ty ≠ b.ty → stepRangeOuter a s b = .error (.methodError "StepRange")) ∧
  (∀ a s b : Num, colonSame3 a s b = stepRangeOuter a s b)

theorem stepRangeConstruction_proven : StepRangeConstruction := by
  refine ⟨?_, ?_, fun _ _ _ _ => rfl, ?_, fun _ _ _ => rfl⟩
  · intro a s b hab hs
    refine ⟨"step cannot be zero", ?_⟩
    simp only [stepRangeOuter, hab, ne_eq, not_true_eq_false, ite_false, stepRangeTS]
    rw [← hab, cast_self, cast_self, hab, cast_self]
    simp [bind, Except.bind, Ranges.steprangeLast, hs]
  · intro a s hs
    simp only [stepRangeOuter, ne_eq, not_true_eq_false, ite_false, stepRangeTS, cast_self]
    simp [bind, Except.bind, Ranges.steprangeLast, hs, pure, Except.pure]
  · intro a s b h; simp [stepRangeOuter, h]

/-- An empty integer `StepRange` (the step points away from the stop) is constructed
whenever its endpoints have one type, and it is empty (docstring of `(:)`,
base/range.jl:54-55; `StepRange(1, Int8(2), 10)` in the StepRange docstring shows
that the step type may differ). -/
def StepRangeEmptyMixed : Prop :=
  ∀ a s b : Num, a.ty = b.ty → s.val ≠ 0 → b.val ≠ a.val →
    (decide (s.val > 0) != decide (b.val > a.val)) = true →
    ∃ r, stepRangeOuter a s b = .ok r ∧ Ranges.isEmpty r = true

theorem stepRangeEmptyMixed_refuted : ¬ StepRangeEmptyMixed := by
  intro h
  obtain ⟨r, hr, _⟩ := h (Ranges.Num.lit (.bit .i8) (-5)) (Ranges.Num.lit (.bit .u8) 1)
    (Ranges.Num.lit (.bit .i8) (-10)) rfl (by decide) (by decide) (by decide)
  have hc : stepRangeOuter (Ranges.Num.lit (.bit .i8) (-5)) (Ranges.Num.lit (.bit .u8) 1)
      (Ranges.Num.lit (.bit .i8) (-10)) = .error (.inexactError "Int8") := by decide
  rw [hc] at hr
  cases hr

/-- The `Char` colon `a:b` is `a:1:b`; a zero step throws ArgumentError; `a:s:a` has the
single element `a`; an empty `Char` range keeps the given stop (the generic
`steprange_last_empty`, base/range.jl:400-401). -/
def CharColon : Prop :=
  (∀ a b : Nat, charColon2 a b = charColon3 a 1 b) ∧
  (∀ a b : Nat, a < 2 ^ 32 → b < 2 ^ 32 → ThrowsArg (charColon3 a 0 b)) ∧
  (∀ (a : Nat) (s : Int), a < 2 ^ 32 → s ≠ 0 → charColon3 a s a = .ok ⟨a, s, a⟩) ∧
  (∀ (a b : Nat) (s : Int), a < 2 ^ 32 → b < 2 ^ 32 → s ≠ 0 → b ≠ a →
    (decide (s > 0) != decide (b > a)) = true → charColon3 a s b = .ok ⟨a, s, b⟩)

theorem charColon_two (a b : Nat) : charColon2 a b = charColon3 a 1 b := by
  simp only [charColon2]
  split <;> simp

theorem charAdd_zero (a : Nat) (ha : a < 2 ^ 32) : charAdd a 0 = .ok a := by
  unfold charAdd
  rw [if_pos (by constructor <;> omega)]
  simp

theorem charWiden_ok (a b : Nat) (s : Int) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    charColon3 a s b = charStepRange a s b := by
  unfold charColon3 charColonWiden
  rw [charAdd_zero a ha, charAdd_zero b hb]
  rfl

theorem charLast_zero (a b : Nat) :
    charSteprangeLast a 0 b = .error (.argumentError "step cannot be zero") := rfl

theorem charColon_zero (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ThrowsArg (charColon3 a 0 b) := by
  refine ⟨"step cannot be zero", ?_⟩
  rw [charWiden_ok a b 0 ha hb]
  unfold charStepRange
  rw [charLast_zero]
  rfl

theorem charLast_same (a : Nat) (s : Int) (hs : s ≠ 0) : charSteprangeLast a s a = .ok a := by
  unfold charSteprangeLast; simp [hs]; rfl

theorem charLast_empty (a b : Nat) (s : Int) (hs : s ≠ 0) (hba : b ≠ a)
    (hdir : (decide (s > 0) != decide (b > a)) = true) : charSteprangeLast a s b = .ok b := by
  unfold charSteprangeLast; simp [hs, hba, hdir]; rfl

theorem charColon_single (a : Nat) (s : Int) (ha : a < 2 ^ 32) (hs : s ≠ 0) :
    charColon3 a s a = .ok ⟨a, s, a⟩ := by
  rw [charWiden_ok a a s ha ha]
  unfold charStepRange
  rw [charLast_same a s hs]
  rfl

theorem charColon_empty (a b : Nat) (s : Int) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hs : s ≠ 0)
    (hba : b ≠ a) (hdir : (decide (s > 0) != decide (b > a)) = true) :
    charColon3 a s b = .ok ⟨a, s, b⟩ := by
  rw [charWiden_ok a b s ha hb]
  unfold charStepRange
  rw [charLast_empty a b s hs hba hdir]
  rfl

theorem charColon_proven : CharColon :=
  ⟨charColon_two, charColon_zero, charColon_single, charColon_empty⟩

theorem oneTo_mkI (t : IntTy) (x : JInt t) :
    oneTo (mkI t x) = .ok ⟨.oneTo, mkI t (JInt.wrap t 1), mkI t (JInt.wrap t 1),
      mkI t (JInt.wrap t (if (JInt.wrap t 0).val < x.val then x.val else (JInt.wrap t 0).val))⟩ := by
  simp [oneTo, oneToT, Ranges.Num.max, zero_mkI, one_mkI, lit_mkI, promote_self, cast_mkI,
    bind, Except.bind, pure, Except.pure]
  try rfl

/-- `OneTo(n)`: the invariant `stop >= zero(stop)` (base/range.jl:486) holds for every
non-Bool integer `n` (negative `n` gives the empty `OneTo(0)`, nonnegative `n` is kept);
Bool is rejected with ArgumentError; `OneTo{T}(r)` rejects ranges whose first element
or step is not 1; `oneto` is `OneTo`; `unchecked_oneto` stores `stop` unchanged. -/
def OneToConstruction : Prop :=
  (∀ t : IntTy, ∀ x : JInt t, ∃ r, oneTo (mkI t x) = .ok r ∧ r.kind = .oneTo ∧
    0 ≤ r.stop.val ∧ (0 ≤ x.val → r.stop.val = x.val) ∧ (x.val < 0 → r.stop.val = 0)) ∧
  (∀ b : Bool, ThrowsArg (oneTo ⟨.bool, b⟩)) ∧
  (∀ T r, (Ranges.first r).val ≠ 1 → ThrowsArg (oneToOfRange T r)) ∧
  (∀ T r, (Ranges.first r).val = 1 → (Ranges.step r).val ≠ 1 → ThrowsArg (oneToOfRange T r)) ∧
  (∀ r, oneto r = oneToRange r) ∧
  (∀ n : Num, (uncheckedOneto n).stop = n)

theorem oneToConstruction_proven : OneToConstruction := by
  refine ⟨?_, fun _ => ⟨_, rfl⟩, ?_, ?_, fun _ => rfl, fun _ => rfl⟩
  · intro t x
    refine ⟨_, oneTo_mkI t x, rfl, ?_⟩
    have hz : wrapInt t 0 = 0 := wrapInt_of_inRange t 0 (by cases t <;> decide)
    have hw : wrapInt t x.val = x.val := wrapInt_of_inRange t _ x.property
    by_cases hx0 : 0 < x.val
    · simp only [mkI_val, wrap_val', hz, hx0, ite_true, hw]
      refine ⟨?_, ?_, ?_⟩ <;> intros <;> first | trivial | omega
    · simp only [mkI_val, wrap_val', hz, hx0, ite_false]
      refine ⟨?_, ?_, ?_⟩ <;> intros <;> first | trivial | omega
  · intro T r h
    exact ⟨"first element must be 1", by
      simp [oneToOfRange, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]⟩
  · intro T r h1 h2
    exact ⟨"step must be 1", by
      simp [oneToOfRange, h1, h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]⟩

def entries : List Entry := []

end Colon

end JuliaLean.RangesCov

import JuliaLean.Ranges.Ordinal
import JuliaLean.Registry.Types

namespace JuliaLean.Ranges

/-- Integer-element `StepRangeLen` fields, base/range.jl:530-535. -/
structure RngLen where
  ref : Num
  stride : Num
  len : Num
  offset : Num
  elementTy : NType
  deriving DecidableEq

inductive ResultRng where
  | ordinal (r : Rng)
  | counted (r : RngLen)
  deriving DecidableEq

/-- `StepRangeLen{T,R,S}` and default length promotion, base/range.jl:537-561.
Only integer reference and step types are in this model. -/
def countedRange (elementTy : NType) (ref stride len : Num)
    (offset : Num := Num.lit (.bit .i64) 1) : Jl ResultRng := do
  let L := Num.promote (.bit .i64) len.ty
  let n ← Num.cast L len
  if n.val < 0 then
    throw (.argumentError "length cannot be negative")
  let o ← Num.cast L offset
  if o.val < 1 ∨ o.val > max 1 n.val then
    throw (.argumentError "StepRangeLen: offset must be in range")
  return .counted ⟨ref, stride, n, o, elementTy⟩

/-- `range_start_length`, base/range.jl:217-226. -/
def rangeStartLength (a len : Num) : Jl ResultRng := do
  let stride ← Num.cast (Num.sub a a).ty (Num.lit (.bit .i64) 1)
  let stop := Num.add a (Num.sub len (Num.one len.ty))
  match stop.ty with
  | .bit t =>
    if t.signed then
      let start ← Num.cast stop.ty a
      return .ordinal (← unit start stop)
    else
      countedRange stop.ty a stride len
  | .bool => countedRange stop.ty a stride len

/-- `range_stop_length`, base/range.jl:206-215. -/
def rangeStopLength (a len : Num) : Jl ResultRng := do
  let stride ← Num.cast (Num.sub a a).ty (Num.lit (.bit .i64) 1)
  let start := Num.sub a (Num.sub len (Num.one len.ty))
  match start.ty with
  | .bit t =>
    if t.signed then
      let stop ← Num.cast start.ty a
      return .ordinal (← unit start stop)
    else
      countedRange start.ty start stride len
  | .bool => countedRange start.ty start stride len

/-- `range_start_step_length`, base/range.jl:230-238. -/
def rangeStartStepLength (a stride len : Num) : Jl ResultRng := do
  let stop := Num.add a (Num.mul stride (Num.sub len (Num.one len.ty)))
  match stop.ty with
  | .bit t =>
    if t.signed then
      let start ← Num.cast stop.ty a
      return .ordinal (← stepRange start stride stop)
    else
      countedRange stop.ty a stride len
  | .bool => countedRange stop.ty a stride len

/-- `range_step_stop_length`, base/range.jl:195-204. -/
def rangeStepStopLength (stride a len : Num) : Jl ResultRng := do
  let start := Num.sub a (Num.mul stride (Num.sub len (Num.one len.ty)))
  match start.ty with
  | .bit t =>
    if t.signed then
      let stop ← Num.cast start.ty a
      return .ordinal (← stepRange start stride stop)
    else
      countedRange start.ty start stride len
  | .bool => countedRange start.ty start stride len

/-- `length(::StepRangeLen)` and ordinal dispatch, base/range.jl:811-813. -/
def resultLength : ResultRng → Jl Num
  | .ordinal r => length r
  | .counted r => .ok r.len

/-- `unsafe_getindex(::StepRangeLen)` with generic scalar index validation,
base/range.jl:976-984 and base/abstractarray.jl scalar Bool-index rejection. -/
def resultGetindex (r : ResultRng) (i : Num) : Jl Num := do
  match r with
  | .ordinal r => getindex r i
  | .counted r =>
    if i.ty = .bool then throw (.argumentError "invalid index of type Bool")
    if i.val < 1 ∨ i.val > r.len.val then throw .boundsError
    let ii ← Num.cast r.offset.ty i
    let u := Num.sub ii r.offset
    Num.cast r.elementTy (Num.add r.ref (Num.mul u r.stride))

/-- `range_error` hint, base/range.jl:243-259. Line 247 reads
`haslength = start !== nothing`, so `haslength` copies `hasstart`. Only the hint
line of the ArgumentError message (base/range.jl:261-269) is modelled. -/
def rangeErrorHint (start step stop _len : Option Num) : String :=
  let hasstart := start.isSome
  let hasstep := step.isSome
  let hasstop := stop.isSome
  let haslength := start.isSome
  if hasstart && hasstep && hasstop && haslength then "Try specifying only three arguments"
  else if !hasstop && !haslength then "At least one of `length` or `stop` must be specified."
  else if !hasstep && !haslength then "At least one of `length` or `step` must be specified."
  else if !hasstart && !hasstop then "At least one of `start` or `stop` must be specified."
  else "Try specifying more arguments."

/-- `range_error`, base/range.jl:243-270: always throws an ArgumentError. -/
def rangeError (start step stop len : Option Num) : Jl ResultRng :=
  .error (.argumentError (rangeErrorHint start step stop len))

/-- `range(...)` front ends (base/range.jl:167-173) and the sixteen `_range`
methods (base/range.jl:175-190); `none` is an argument left as `nothing`.
`range_length`/`range_stop(::Integer)` build `OneTo` (base/range.jl:193,197).
The result is `none` only for start/stop/length (base/range.jl:186), whose
integer arguments produce floating-point elements outside this model. -/
def rangeKw : Option Num → Option Num → Option Num → Option Num → Option (Jl ResultRng)
  | none, none, none, some n => some (.ordinal <$> oneTo n)
  | none, none, some b, none => some (.ordinal <$> oneTo b)
  | none, none, some b, some n => some (rangeStopLength b n)
  | none, some s, some b, some n => some (rangeStepStopLength s b n)
  | some a, none, none, some n => some (rangeStartLength a n)
  | some a, none, some b, none => some (.ordinal <$> colon2 a b)
  | some _, none, some _, some _ => none
  | some a, some s, none, some n => some (rangeStartStepLength a s n)
  | some a, some s, some b, none => some (.ordinal <$> colon3 a s b)
  | a, s, b, n => some (rangeError a s b n)

/-- Ordinal integer scalar addition specialization, base/broadcast.jl:1199-1205.
OneTo uses the AbstractUnitRange method and returns a UnitRange. -/
def broadcastAdd (r : Rng) (x : Num) : Jl ResultRng := do
  let a := Num.add (first r) x
  let b := Num.add (last r) x
  if r.kind = .step then
    return .ordinal (← colon3 a (step r) b)
  else
    return .ordinal (← colon2 a b)

/-- Integer scalar multiplication specialization, base/broadcast.jl:1241-1253. -/
def broadcastMul (r : Rng) (x : Num) : Jl ResultRng := do
  let a := Num.mul (first r) x
  let s := Num.mul (step r) x
  let n ← length r
  countedRange (Num.add a (Num.zero s.ty)).ty a s n

/-- `mod(i, r)` and `mod1` dispatch, base/range.jl:1548-1549,
base/operators.jl:914, base/promotion.jl:522. -/
def modRange (i : Num) (r : Rng) : Jl Num := do
  if r.kind = .oneTo then
    let ty := Num.promote i.ty (last r).ty
    let i ← Num.cast ty i
    let stop ← Num.cast ty (last r)
    let m ← Num.mod i stop
    pure (if m.val = 0 then stop else m)
  else
    let n ← length r
    let m ← Num.mod (Num.sub i (first r)) n
    pure (Num.add m (first r))

/-- Every length-taking `range` form respects a requested nonnegative length
whenever construction succeeds. -/
def KeywordLengthPreserved : Prop :=
  ∀ (a s b : Option Num) (n : Num) (r : ResultRng), 0 ≤ n.val →
    rangeKw a s b (some n) = some (.ok r) →
      match resultLength r with
      | .ok m => m.val = n.val
      | .error _ => False

/-- Dotted scalar addition preserves the number of elements. -/
def BroadcastAddLengthPreserved : Prop :=
  ∀ (a b x : Num) (r : Rng) (s : ResultRng),
    colon2 a b = .ok r → broadcastAdd r x = .ok s →
      (resultLength s).map Num.val = (length r).map Num.val

/-- A negative requested element count is invalid. -/
def NegativeKeywordLengthRejected : Prop :=
  ∀ (a n : Num), n.val < 0 →
    ∃ e, rangeStartLength a n = .error e

/-- The documented modulus result is congruent to its input modulo the range count. -/
def ModRangeCongruence : Prop :=
  ∀ (a b i : Num) (r : Rng), colon2 a b = .ok r →
    0 < trueCount r →
      match modRange i r with
      | .ok y => (i.val - y.val) % trueCount r = 0
      | .error _ => False

/-- Broadcast `r .* x` has the elements `r[i] * x` of the elementwise broadcast. -/
def BroadcastMulElementwise : Prop :=
  ∀ (a b x i : Num) (r : Rng) (s : ResultRng),
    colon2 a b = .ok r → broadcastMul r x = .ok s →
    i.ty = .bit .i64 → 1 ≤ i.val → i.val ≤ trueCount r →
      (resultGetindex s i).map Num.val = (getindex r i).map (fun y => (Num.mul y x).val)

/-- The `range_error` hint never names an argument the caller supplied as missing. -/
def RangeErrorHintAccurate : Prop :=
  ∀ (a s b n : Option Num) (msg : String),
    rangeKw a s b n = some (.error (.argumentError msg)) →
      (msg = "At least one of `length` or `stop` must be specified." → b = none ∧ n = none) ∧
      (msg = "At least one of `length` or `step` must be specified." → s = none ∧ n = none) ∧
      (msg = "At least one of `start` or `stop` must be specified." → a = none ∧ b = none)

/-- `range` docstring, base/range.jl:159-161: integer `stop` and `length` alone
produce a `UnitRange`. -/
def StopLengthGivesUnitRange : Prop :=
  ∀ (b n : Num) (r : ResultRng), b.ty ≠ .bool → n.ty ≠ .bool →
    rangeKw none none (some b) (some n) = some (.ok r) →
      ∃ u : Rng, r = .ordinal u ∧ u.kind = .unit

private def i8 (x : Int) : Num := Num.lit (.bit .i8) x
private def i64 (x : Int) : Num := Num.lit (.bit .i64) x
private def empty127 : Rng := ⟨.unit, i8 127, i8 1, i8 126⟩
private def pair126 : Rng := ⟨.unit, i8 126, i8 1, i8 127⟩

set_option maxRecDepth 4096 in
theorem keywordLength_refuted : ¬ KeywordLengthPreserved := by
  intro h
  have bad := h (some (i64 9223372036854775806)) none none (i64 5)
    (.ordinal ⟨.unit, i64 9223372036854775806, i64 1, i64 9223372036854775805⟩)
    (by decide) rfl
  change (0 : Int) = 5 at bad
  omega

set_option maxRecDepth 4096 in
theorem broadcastAddLength_refuted : ¬ BroadcastAddLengthPreserved := by
  intro h
  have bad := h (i8 126) (i8 127) (i8 1) pair126 (.ordinal empty127)
    (by decide) (by decide)
  change (Except.ok (0 : Int) : Jl Int) = .ok 2 at bad
  cases bad

set_option maxRecDepth 4096 in
theorem negativeKeywordLength_refuted : ¬ NegativeKeywordLengthRejected := by
  intro h
  obtain ⟨e, bad⟩ := h (i64 1) (i64 (-1)) (by decide)
  have actual : rangeStartLength (i64 1) (i64 (-1)) =
      .ok (.ordinal ⟨.unit, i64 1, i64 1, i64 0⟩) := by decide
  rw [actual] at bad
  cases bad

set_option maxRecDepth 4096 in
theorem modRangeCongruence_refuted : ¬ ModRangeCongruence := by
  intro h
  have bad := h (i64 1) (i64 3) (i64 (-9223372036854775808))
    ⟨.unit, i64 1, i64 1, i64 3⟩ (by decide) (by decide)
  change ((-9223372036854775808 : Int) - 2) % 3 = 0 at bad
  have : ((-9223372036854775808 : Int) - 2) % 3 ≠ 0 := by decide
  exact this bad

set_option maxRecDepth 4096 in
theorem broadcastMulElementwise_refuted : ¬ BroadcastMulElementwise := by
  intro h
  have bad := h (i8 1) (i8 3) (i8 64) (i64 2) ⟨.unit, i8 1, i8 1, i8 3⟩
    (.counted ⟨i8 64, i8 64, i64 3, i64 1, .bit .i8⟩) rfl rfl rfl (by decide) (by decide)
  change (Except.error (JlError.inexactError "Int8") : Jl Int) = .ok (-128) at bad
  cases bad

theorem rangeErrorHintAccurate_refuted : ¬ RangeErrorHintAccurate := by
  intro h
  have bad := ((h none (some (i64 1)) none (some (i64 3))
    "At least one of `length` or `stop` must be specified." rfl).1 rfl).2
  cases bad

theorem stopLengthGivesUnitRange_refuted : ¬ StopLengthGivesUnitRange := by
  intro h
  obtain ⟨u, hu, _⟩ := h (Num.lit (.bit .u64) 10) (i64 5)
    (.counted ⟨Num.lit (.bit .u64) 6, Num.lit (.bit .u64) 1, i64 5, i64 1, .bit .u64⟩)
    (by decide) (by decide) rfl
  cases hu

open JuliaLean.Registry

def keywordEntries : List Entry := []

end JuliaLean.Ranges

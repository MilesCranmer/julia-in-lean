import JuliaLean.Ranges.Common

namespace JuliaLean.Ranges

open JuliaLean.Registry

/-- `base/range.jl:339-350,425-429,486-511`: integer ordinal range representations. -/
inductive RangeKind where
  | unit | step | oneTo
  deriving DecidableEq, Repr

/-- `base/range.jl:339-350,425-429,486-511`: stored endpoints and step. -/
structure Rng where
  kind : RangeKind
  start : Num
  stride : Num
  stop : Num
  deriving DecidableEq

/-- `base/range.jl:867-868`: OneTo supplies a type-level lower endpoint. -/
def first (r : Rng) : Num :=
  if r.kind = .oneTo then Num.one r.stop.ty else r.start

/-- `base/range.jl:877`: constructors store the normalized last endpoint. -/
def last (r : Rng) : Num := r.stop

/-- `base/range.jl:735-737`: Bool unit steps stay Bool; other units subtract zero. -/
def step (r : Rng) : Num :=
  if r.kind = .step then r.stride
  else if r.start.ty = .bool then Num.one .bool
  else Num.sub (Num.one r.start.ty) (Num.zero r.start.ty)

/-- `base/range.jl:708-711`: emptiness uses direction and normalized endpoints. -/
def isEmpty (r : Rng) : Bool :=
  if r.kind = .step then
    !Num.eq r.start r.stop && ((decide (r.stride.val > 0)) != (decide (r.stop.val > r.start.val)))
  else decide ((first r).val > (last r).val)

/-- `base/range.jl:439-441`: integral UnitRange empty normalization. -/
def unitrangeLast (a b : Num) : Jl Num :=
  if b.val ≥ a.val then .ok b
  else Num.cast b.ty (Num.sub a (Num.one (Num.sub a b).ty))

/-- `base/range.jl:428-435`: UnitRange promotes endpoints by exact conversion. -/
def unit (a b : Num) : Jl Rng := do
  let ty := Num.promote a.ty b.ty
  let a ← Num.cast ty a
  let b ← Num.cast ty b
  let z ← unitrangeLast a b
  pure ⟨.unit, a, Num.one ty, z⟩

/-- `base/range.jl:389-399`: empty StepRange uses oneunit(step), with a Bool xor specialization. -/
def steprangeLastEmpty (a s b : Num) : Jl Num :=
  if a.ty = .bool then
    .ok (Num.lit .bool (if decide (a.val ≠ 0) != decide (s.val > 0) then 1 else 0))
  else Num.cast b.ty (if s.val > 0 then Num.sub a (Num.one s.ty) else Num.add a (Num.one s.ty))

/-- `base/range.jl:353-387`: signed-overflow remainder uses unsigned(absdiff), including typemin steps. -/
def steprangeLast (a s b : Num) : Jl Num := do
  if s.val = 0 then .error (.argumentError "step cannot be zero")
  else if b.val = a.val then pure b
  else if decide (s.val > 0) != decide (b.val > a.val) then steprangeLastEmpty a s b
  else
    let (diff, st) := if b.val > a.val then (Num.sub b a, s) else (Num.sub a b, Num.neg s)
    let rem ← Num.rem (if diff.ty.signed && decide (diff.val < 0) then Num.unsigned diff else diff) st
    let rem ← Num.cast diff.ty rem
    Num.cast b.ty (if b.val > a.val then Num.sub b rem else Num.add b rem)

/-- `base/range.jl:339-350,404-405`: the unparameterized StepRange requires equal endpoint types. -/
def stepRange (a s b : Num) : Jl Rng := do
  if a.ty ≠ b.ty then .error (.methodError "StepRange")
  else
    let z ← steprangeLast a s b
    pure ⟨.step, a, s, z⟩

/-- `base/range.jl:3-5`: two-argument colon promotes exactly and constructs UnitRange. -/
def colon2 (a b : Num) : Jl Rng := unit a b

/-- `base/range.jl:10-11,22-24,64-70`: colon preserves step type, widening endpoints through start+zero(step). -/
def colon3 (a s b : Num) : Jl Rng := do
  let ty := Num.promote a.ty b.ty
  let a ← Num.cast ty a
  let b ← Num.cast ty b
  if ty = s.ty then stepRange a s b
  else
    let ty' := (Num.add a (Num.zero s.ty)).ty
    let a ← Num.cast ty' a
    let b ← Num.cast ty' b
    stepRange a s b

/-- `base/range.jl:486-492,513`: OneTo rejects Bool, then clips negative stops to zero. -/
def oneTo (n : Num) : Jl Rng :=
  if n.ty = .bool then .error (.argumentError "invalid index of type Bool")
  else .ok ⟨.oneTo, Num.one n.ty, Num.one n.ty, Num.max (Num.zero n.ty) n⟩

/-- `base/range.jl:777-791`: generic ordinal length, used for Bool element ranges. -/
def genericLength (r : Rng) : Jl Num := do
  let s := step r
  let a := first r
  if isEmpty r then Num.div (Num.sub a a) (Num.one s.ty)
  else
    let (diff, s) := if s.val < 0 then (Num.sub a (last r), Num.neg s) else (Num.sub (last r) a, s)
    let q ← Num.div diff s
    pure (Num.add q (Num.one q.ty))

/-- `base/range.jl:794-806,817-829,853-860`: all built-in integer length specializations. -/
def length (r : Rng) : Jl Num := do
  let a := first r
  let b := last r
  if r.kind = .oneTo then
    if b.ty.small then Num.cast (.bit .i64) b else pure b
  else if a.ty.small then
    let a ← Num.cast (.bit .i64) a
    let b ← Num.cast (.bit .i64) b
    if r.kind ≠ .step then pure (Num.add (Num.sub b a) (Num.one (.bit .i64)))
    else if isEmpty r then pure (Num.zero (.bit .i64))
    else
      let q ← Num.div (Num.sub b a) (step r)
      let q ← Num.cast (.bit .i64) q
      pure (Num.add q (Num.one (.bit .i64)))
  else if r.kind ≠ .step then
    let unit := Num.one (Num.sub (Num.zero b.ty) (Num.zero a.ty)).ty
    if unit.ty.signed || decide (b.val ≥ a.val) then pure (Num.add unit (Num.sub b a))
    else pure (Num.zero unit.ty)
  else if a.ty = .bool then genericLength r
  else
    let s := step r
    let diff := Num.sub b a
    if isEmpty r then pure (Num.zero diff.ty)
    else
      let q ← Num.div (Num.unsigned (Num.flipsign diff s)) s
      let q := Num.lit diff.ty q.val
      pure (Num.add (Num.flipsign q s) (Num.one q.ty))

/-- `base/range.jl:751-775`: generic checked ordinal/unit length (Bool element specialization). -/
def genericCheckedLength (r : Rng) : Jl Num := do
  let a := first r
  if r.kind ≠ .step then
    if isEmpty r then pure (Num.sub a a)
    else
      let q ← Num.checkedSub (last r) a
      Num.checkedAdd q (Num.one q.ty)
  else
    let s := step r
    if isEmpty r then Num.div (Num.sub a a) (Num.one s.ty)
    else
      let diff ← if s.val < 0 then Num.checkedSub a (last r) else Num.checkedSub (last r) a
      let q ← Num.div diff (if s.val < 0 then Num.neg s else s)
      Num.checkedAdd q (Num.one q.ty)

/-- `base/range.jl:768-775,831-848,861-863`: checked length preserves intermediate conversions/errors. -/
def checkedLength (r : Rng) : Jl Num := do
  let a := first r
  if a.ty.small then length r
  else if r.kind ≠ .step ∨ a.ty = .bool then genericCheckedLength r
  else
    let s := step r
    let b := last r
    let ty := Num.promote b.ty a.ty
    if isEmpty r then pure (Num.zero ty)
    else
      let q ← if s.val > 1 then
          Num.div (Num.unsigned (Num.sub b a)) s
        else if s.val < -1 then
          Num.div (Num.unsigned (Num.sub a b)) (Num.neg s)
        else if s.val > 0 then do
          let diff ← Num.checkedSub b a
          Num.div diff s
        else do
          let diff ← Num.checkedSub a b
          Num.div diff (Num.neg s)
      let q ← Num.cast ty q
      Num.checkedAdd q (Num.one q.ty)

/-- Mathematical cardinality of normalized ordinal ranges, without machine-width overflow. -/
def trueCount (r : Rng) : Int :=
  if isEmpty r then 0
  else if r.kind ≠ .step then (last r).val - (first r).val + 1
  else ((last r).val - (first r).val).tdiv (step r).val + 1

/-- `base/range.jl:974-978`: specialized bounds arithmetic widens products before adding first. -/
def stepBounds64 (r : Rng) (i : Num) (hs : (step r).ty.bits ≤ 64) (hi : i.ty.bits ≤ 64) : Bool :=
  let j := Num.sub i (Num.one i.ty)
  let res := Num.add (Num.widemul64 (step r) j hs (Num.sub_one_bits_le64 i hi)) (first r)
  decide (0 < i.val) && (if (step r).val > 0 then decide (res.val ≤ (last r).val) else decide (res.val ≥ (last r).val))

/-- `base/range.jl:950-953,974-978`, `base/abstractarray.jl` linear bounds: StepRange64 avoids length. -/
def scalarBounds (r : Rng) (i : Num) : Jl Bool := do
  if h : r.kind = .step ∧ r.start.ty ≠ .bool ∧ r.stride.ty ≠ .bool ∧ i.ty ≠ .bool ∧
      r.start.ty.bits ≤ 64 ∧ r.stride.ty.bits ≤ 64 ∧ i.ty.bits ≤ 64 then
    have hs : (step r).ty.bits ≤ 64 := by simpa [step, h.1] using h.2.2.2.2.2.1
    pure (stepBounds64 r i hs h.2.2.2.2.2.2)
  else
    let n ← length r
    pure (decide (1 ≤ i.val ∧ i.val ≤ n.val))

/-- `base/range.jl:950-971,984-985`, `base/abstractarray.jl`: scalar indexing rejects Bool before bounds. -/
def getindex (r : Rng) (i : Num) : Jl Num := do
  if i.ty = .bool then .error (.argumentError "invalid index of type Bool")
  else if r.kind = .unit then
    let v := Num.add r.start (Num.sub i (Num.one i.ty))
    if i.val > 0 ∧ v.val ≤ r.stop.val ∧ v.val ≥ r.start.val then
      pure (Num.lit r.start.ty v.val)
    else .error .boundsError
  else
    let valid ← scalarBounds r i
    if !valid then .error .boundsError
    else if r.kind = .oneTo then Num.cast r.stop.ty i
    else Num.cast r.start.ty (Num.add (first r) (Num.mul (Num.sub i (Num.one i.ty)) (step r)))

/-- `base/range.jl:935-942`: ordinal iteration carries the current element, terminating at last. -/
def iterate (r : Rng) (state : Option Num := none) : Jl (Option Num) := do
  match state with
  | none => pure (if isEmpty r then none else some (first r))
  | some i =>
      if Num.eq i (last r) then pure none
      else
        let n ← Num.cast r.start.ty (Num.add i (step r))
        pure (some n)

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

/-- `base/range.jl:935-942`: the element reached by repeated Julia iteration (zero-based position). -/
def iterateAt (r : Rng) : Nat → Jl (Option Num)
  | 0 => iterate r
  | n + 1 => do
      let previous ← iterateAt r n
      match previous with
      | none => pure none
      | some v => iterate r (some v)

/-- Every valid non-Bool scalar position in a UnitRange agrees with its first element and unit step. -/
def UnsignedIndexAgreement : Prop :=
  ∀ a b i r, unit a b = .ok r → i.ty ≠ .bool →
    1 ≤ i.val → i.val ≤ trueCount r →
    ∃ v, getindex r i = .ok v ∧ iterateAt r (i.val - 1).toNat = .ok (some v) ∧
      v.val = (first r).val + i.val - 1

/-- Concrete normalized range constructed by `Int8(-1):Int8(1)`. -/
def negativeUnit : Rng :=
  ⟨.unit, Num.lit (.bit .i8) (-1), Num.one (.bit .i8), Num.lit (.bit .i8) 1⟩

theorem unsignedIndexAgreement_refuted : ¬ UnsignedIndexAgreement := by
  intro h
  obtain ⟨v, hv, _⟩ := h (Num.lit (.bit .i8) (-1)) (Num.lit (.bit .i8) 1)
    (Num.lit (.bit .u8) 1) negativeUnit (by decide) (by decide) (by decide) (by decide)
  have failure : getindex negativeUnit (Num.lit (.bit .u8) 1) = .error .boundsError := by decide
  rw [failure] at hv
  cases hv

/-- A representable mathematical cardinality is returned by checked_length, including extreme negative steps. -/
def CheckedLengthCapacity : Prop :=
  ∀ a s b r, colon3 a s b = .ok r →
    0 ≤ trueCount r → trueCount r ≤ IntTy.i64.max →
    ∃ n, checkedLength r = .ok n ∧ n.val = trueCount r

/-- Concrete two-element range with the most negative Int64 step. -/
def typeminStep : Rng :=
  ⟨.step, Num.zero (.bit .i64), Num.lit (.bit .i64) IntTy.i64.min,
    Num.lit (.bit .i64) IntTy.i64.min⟩

theorem checkedLengthCapacity_refuted : ¬ CheckedLengthCapacity := by
  intro h
  obtain ⟨n, hn, _⟩ := h (Num.zero (.bit .i64)) (Num.lit (.bit .i64) IntTy.i64.min)
    (Num.lit (.bit .i64) IntTy.i64.min) typeminStep (by decide) (by decide) (by decide)
  have failure : checkedLength typeminStep = .error (.inexactError "Int64") := by decide
  rw [failure] at hn
  cases hn

/-- `base/range.jl:428-441`: full-width UnitRange constructor inputs, for each of the ten BitIntegers. -/
def fullWidthUnit (t : IntTy) : Rng :=
  ⟨.unit, Num.lit (.bit t) t.min, Num.one (.bit t), Num.lit (.bit t) t.max⟩

/-- Small element types use Int64 length; large full-width ranges wrap, while checked_length reports overflow. -/
def FullWidthCountBehavior : Prop :=
  ∀ t : IntTy,
    trueCount (fullWidthUnit t) = 2 ^ t.bits ∧
    length (fullWidthUnit t) =
      .ok (Num.lit (if t.bits < 64 then .bit .i64 else .bit t) (2 ^ t.bits)) ∧
    checkedLength (fullWidthUnit t) =
      (if t.bits < 64 then length (fullWidthUnit t)
       else .error (.overflowError "checked arithmetic")) ∧
    isEmpty (fullWidthUnit t) = false

theorem fullWidthCountBehavior_proven : FullWidthCountBehavior := by
  intro t
  cases t <;> decide

/-- Ordinal iteration starts at the same element returned by first. -/
def IterationFirstAgreement : Prop :=
  ∀ r : Rng, isEmpty r = false → iterate r = .ok (some (first r))

theorem iterationFirstAgreement_proven : IterationFirstAgreement := by
  intro r h
  simp [iterate, h]
  rfl

/-- Ordinal iteration stops exactly when its current state equals last. -/
def IterationLastAgreement : Prop :=
  ∀ r i, Num.eq i (last r) = true → iterate r (some i) = .ok none

theorem iterationLastAgreement_proven : IterationLastAgreement := by
  intro r i h
  simp [iterate, h]
  rfl

/-- `base/range.jl:339-350`: a signed endpoint range with a positive unsigned step. -/
def unsignedStepNegative : Rng :=
  ⟨.step, Num.lit (.bit .i64) (-2), Num.one (.bit .u64), Num.lit (.bit .i64) (-1)⟩

/-- A nonempty constructed range reaches last through both scalar indexing and iteration. -/
def OrdinalLastAgreement : Prop :=
  ∀ a s b r n, stepRange a s b = .ok r → length r = .ok n → 0 < n.val →
    getindex r n = .ok (last r) ∧
    iterateAt r (n.val - 1).toNat = .ok (some (last r)) ∧
    iterateAt r n.val.toNat = .ok none

theorem ordinalLastAgreement_refuted : ¬ OrdinalLastAgreement := by
  intro h
  have agreement := h (Num.lit (.bit .i64) (-2)) (Num.one (.bit .u64))
    (Num.lit (.bit .i64) (-1)) unsignedStepNegative (Num.lit (.bit .i64) 2)
    (by decide) (by decide) (by decide)
  have failure : getindex unsignedStepNegative (Num.lit (.bit .i64) 2) =
      .error (.inexactError "Int64") := by decide
  rw [failure] at agreement
  cases agreement.1

/-- `base/range.jl:339-350`: two-element ranges immediately adjacent to each integer extremum. -/
def extremalPair (t : IntTy) (descending : Bool) : Rng :=
  let a := Num.lit (.bit t) (if descending then t.max else t.min)
  let s := Num.lit (.bit .i64) (if descending then -1 else 1)
  let b := Num.lit (.bit t) (if descending then t.max - 1 else t.min + 1)
  ⟨.step, a, s, b⟩

/-- For each width and signedness, ±1 two-element edge ranges agree on first, step, count, indexing and iteration. -/
def ExtremalPairAgreement : Prop :=
  ∀ t : IntTy, ∀ descending : Bool,
    let r := extremalPair t descending
    stepRange (first r) (step r) (last r) = .ok r ∧
    trueCount r = 2 ∧
    length r = .ok (Num.lit (if t.bits < 64 then .bit .i64 else .bit t) 2) ∧
    checkedLength r = length r ∧
    getindex r (Num.lit (.bit .i64) 2) = .ok (last r) ∧
    iterateAt r 1 = .ok (some (last r)) ∧ iterateAt r 2 = .ok none

theorem extremalPairAgreement_proven : ExtremalPairAgreement := by
  intro t descending
  cases t <;> cases descending <;> decide

/-- `base/range.jl:428-441`: large unsigned ranges whose nonzero length exceeds typemax(Int). -/
def unsignedLargeUnit (t : IntTy) : Rng :=
  ⟨.unit, Num.one (.bit t), Num.one (.bit t), Num.lit (.bit t) t.max⟩

/-- UInt64/UInt128 counts need not fit Int64, and their unsigned length still indexes last correctly. -/
def UnsignedLargeCountAgreement : Prop :=
  ∀ t : IntTy, t = .u64 ∨ t = .u128 →
    let r := unsignedLargeUnit t
    let n := Num.lit (.bit t) t.max
    trueCount r = t.max ∧ IntTy.i64.max < trueCount r ∧
    length r = .ok n ∧ checkedLength r = .ok n ∧
    getindex r n = .ok (last r) ∧ isEmpty r = false

theorem unsignedLargeCountAgreement_proven : UnsignedLargeCountAgreement := by
  intro t h
  rcases h with rfl | rfl <;> decide

/-- `base/range.jl:968-971`: a nonpositive scalar UnitRange index is out of bounds. -/
def UnitInvalidLowerIndex : Prop :=
  ∀ r i, r.kind = .unit → i.ty ≠ .bool → i.val ≤ 0 →
    getindex r i = .error .boundsError

theorem unitInvalidLowerIndex_proven : UnitInvalidLowerIndex := by
  intro r i hr hi hn
  have hpos : ¬ i.val > 0 := by omega
  simp [getindex, hr, hi, hpos]

/-- Bool UnitRanges retain Bool steps, reject Bool scalar indices, and agree on emptiness and count. -/
def BoolUnitAgreement : Prop :=
  ∀ a b : Bool,
    let n : Int := if a && !b then 0 else (if b then 1 else 0) - (if a then 1 else 0) + 1
    let r : Rng := ⟨.unit, ⟨.bool, a⟩, Num.one .bool, ⟨.bool, b⟩⟩
    unit ⟨.bool, a⟩ ⟨.bool, b⟩ = .ok r ∧
    step r = Num.one .bool ∧
    length r = .ok (Num.lit (.bit .i64) n) ∧
    checkedLength r = length r ∧
    isEmpty r = decide (n = 0) ∧
    iterateAt r n.toNat = .ok none ∧
    getindex r ⟨.bool, true⟩ = .error (.argumentError "invalid index of type Bool")

theorem boolUnitAgreement_proven : BoolUnitAgreement := by
  intro a b
  cases a <;> cases b <;> decide

def ordinalEntries : List Entry := []

end JuliaLean.Ranges

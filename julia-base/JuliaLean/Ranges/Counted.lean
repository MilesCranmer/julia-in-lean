import JuliaLean.Ranges.Keywords
import JuliaLean.Float.Extras

namespace JuliaLean.Ranges

open JuliaLean.Registry

/-- `base/range.jl:537-550`: the integer-only inner constructor, including exact length/offset conversions. -/
def countedNewTyped (elementTy lengthTy : NType) (ref stride len offset : Num) : Jl RngLen := do
  let n ← Num.cast lengthTy len
  if n.val < 0 then throw (.argumentError "length cannot be negative")
  let o ← Num.cast lengthTy offset
  if o.val < 1 ∨ o.val > max 1 n.val then
    throw (.argumentError "StepRangeLen: offset must be in range")
  return ⟨ref, stride, n, o, elementTy⟩

/-- `base/range.jl:554-561`: `StepRangeLen{T}` promotes the length type with Int. -/
def countedNew (elementTy : NType) (ref stride len : Num)
    (offset : Num := Num.lit (.bit .i64) 1) : Jl RngLen :=
  countedNewTyped elementTy (Num.promote (.bit .i64) len.ty) ref stride len offset

/-- `base/range.jl:1095-1098`: high-precision indexing retains the reference and step types. -/
def countedHiprec (r : RngLen) (i : Num) : Jl Num := do
  let i ← Num.cast r.offset.ty i
  return Num.add r.ref (Num.mul (Num.sub i r.offset) r.stride)

/-- `base/range.jl:981-984`: conversion to the element type occurs after the arithmetic. -/
def countedUnsafeGetindex (r : RngLen) (i : Num) : Jl Num := do
  Num.cast r.elementTy (← countedHiprec r i)

/-- `base/range.jl:869`: first indexes at the literal Int 1, even for an empty range. -/
def countedFirst (r : RngLen) : Jl Num :=
  countedUnsafeGetindex r (Num.lit (.bit .i64) 1)

/-- `base/range.jl:878`: last indexes at the stored length, including zero. -/
def countedLast (r : RngLen) : Jl Num := countedUnsafeGetindex r r.len

/-- `base/range.jl:738`: the integer element specialization returns the stored step. -/
def countedStep (r : RngLen) : Num := r.stride

/-- `base/range.jl:712`: emptiness tests length, independently of endpoint overflow. -/
def countedIsEmpty (r : RngLen) : Bool := decide (r.len.val = 0)

/-- `base/checked.jl:376`, `base/range.jl:807`: checked length uses the stored-length fallback. -/
def countedCheckedLength (r : RngLen) : Jl Num := .ok r.len

/-- `base/range.jl:928-933`: iteration increments its integer state before testing length. -/
def countedIterate (r : RngLen) (state : Option Num := none) : Jl (Option (Num × Num)) := do
  let i := state.getD (Num.zero r.len.ty)
  let i := Num.add i (Num.one i.ty)
  if r.len.val < i.val then return none
  return some (← countedUnsafeGetindex r i, i)

/-- `base/range.jl:1436-1442`: reverse preserves all four type parameters. -/
def countedReverse (r : RngLen) : Jl RngLen := do
  let offset := if countedIsEmpty r then r.offset
    else Num.add (Num.sub r.len r.offset) (Num.lit (.bit .i64) 1)
  let stride ← Num.negate r.stride
  if stride.ty ≠ r.stride.ty then throw (.methodError "StepRangeLen")
  countedNewTyped r.elementTy r.len.ty r.ref stride r.len offset

/-- `base/broadcast.jl:1208-1211`: scalar addition converts the reference before inferring element type. -/
def countedBroadcastAdd (r : RngLen) (x : Num) (scalarLeft : Bool := false) : Jl RngLen := do
  let refT ← Num.cast r.elementTy r.ref
  let element := if scalarLeft then Num.add x refT else Num.add refT x
  let ref := if scalarLeft then Num.add x r.ref else Num.add r.ref x
  countedNew element.ty ref r.stride r.len r.offset

/-- `base/broadcast.jl:1243-1244,1251-1252`: multiplication preserves offset and wraps every product separately. -/
def countedBroadcastMul (r : RngLen) (x : Num) (scalarLeft : Bool := false) : Jl RngLen := do
  let refT ← Num.cast r.elementTy r.ref
  let element := if scalarLeft then Num.mul x refT else Num.mul refT x
  let ref := if scalarLeft then Num.mul x r.ref else Num.mul r.ref x
  let stride := if scalarLeft then Num.mul x r.stride else Num.mul r.stride x
  countedNew element.ty ref stride r.len r.offset

/-- `base/range.jl:881-884`: extrema inspect endpoints, with the empty check first. -/
def countedMinimum (r : RngLen) : Jl Num := do
  if countedIsEmpty r then throw (.argumentError "range must be non-empty")
  let a ← countedFirst r
  let b ← countedLast r
  return Num.min a b

/-- `base/range.jl:881-884`: maximum uses endpoint max after the empty check. -/
def countedMaximum (r : RngLen) : Jl Num := do
  if countedIsEmpty r then throw (.argumentError "range must be non-empty")
  let a ← countedFirst r
  let b ← countedLast r
  return Num.max a b

/-- `base/range.jl:920`: evaluate minimum before maximum. -/
def countedExtrema (r : RngLen) : Jl (Num × Num) := do
  let a ← countedMinimum r
  let b ← countedMaximum r
  return (a, b)

/-- `base/range.jl:1481-1484`: integer-element membership retains both separate mod calls. -/
def countedContains (r : RngLen) (x : Num) : Jl Bool := do
  if countedIsEmpty r then return false
  if r.stride.val = 0 then return Num.eq x (← countedFirst r)
  let lo ← countedMinimum r
  if x.val < lo.val then return false
  let hi ← countedMaximum r
  if x.val > hi.val then return false
  let x ← Num.cast r.elementTy x
  let a ← Num.mod x r.stride
  let b ← Num.mod (← countedFirst r) r.stride
  return decide ((Num.sub a b).val = 0)

/-- `base/range.jl:1458-1463`, `base/int.jl:610-620`: arithmetic right shift by one. -/
def countedHalf (x : Num) : Num := Num.lit x.ty (x.val / 2)

/-- `base/range.jl:1458-1463`: arithmetic-series sum, retaining parity and product order. -/
def countedSum (r : RngLen) : Jl Num := do
  let l := r.len
  let a ← countedFirst r
  let lm1 := Num.sub l (Num.lit (.bit .i64) 1)
  let tail := if l.val % 2 = 0 then
      Num.mul (Num.mul r.stride lm1) (countedHalf l)
    else Num.mul (Num.mul r.stride l) (countedHalf lm1)
  return Num.add (Num.mul l a) tail

/-- `base/abstractarray.jl:756-757`, `base/multidimensional.jl:910-917`: logical masks check length; ordinary ranges check endpoints. -/
def countedSliceBounds (r : RngLen) (s : Rng) : Jl Bool := do
  if (first s).ty = .bool then
    return Num.eq (← length s) r.len
  if isEmpty s then return true
  return decide (1 ≤ (first s).val ∧ (first s).val ≤ r.len.val ∧
    1 ≤ (last s).val ∧ (last s).val ≤ r.len.val)

/-- `base/int.jl:100-102`, `base/float.jl:243-305`: integer `/` converts each input to binary64. -/
def countedFloat (x : Num) : JuliaLean.Float.F64 :=
  match x with
  | ⟨.bool, _⟩ => JuliaLean.Float.F64.ofInt x.val
  | ⟨.bit _, v⟩ => JuliaLean.Float.F64.ofJInt v

/-- `base/range.jl:1089`, `base/rounding.jl:485-491`: round the binary64 quotient to the index-length type. -/
def countedRoundQuotient (ty : NType) (a b : Num) : Jl Num := do
  let x := JuliaLean.Float.F64.div (countedFloat a) (countedFloat b)
  match ty with
  | .bit t => return ⟨.bit t, ← JuliaLean.Float.F64.roundInt t x⟩
  | .bool =>
    let x ← JuliaLean.Float.F64.roundInt .i64 x
    Num.cast .bool ⟨.bit .i64, x⟩

/-- `base/range.jl:1065-1094`: counted slicing, including logical masks and binary64 offset selection. -/
def countedSlice (r : RngLen) (s : Rng) : Jl RngLen := do
  if !(← countedSliceBounds r s) then throw .boundsError
  let len ← length s
  let sstep := step s
  let rstep := r.stride
  if (first s).ty = .bool then
    let rstep := Num.mul rstep (Num.one sstep.ty)
    if len.val = 0 then
      countedNew r.elementTy (← countedFirst r) rstep (Num.zero len.ty) (Num.one len.ty)
    else if len.val = 1 then
      if (first s).val ≠ 0 then
        countedNew r.elementTy (← countedFirst r) rstep (Num.one len.ty) (Num.one len.ty)
      else
        countedNew r.elementTy (← countedFirst r) rstep (Num.zero len.ty) (Num.one len.ty)
    else
      countedNew r.elementTy (← countedLast r) rstep (Num.one len.ty) (Num.one len.ty)
  else
    let q ← countedRoundQuotient len.ty (Num.sub r.offset (first s)) sstep
    let offset ← Num.cast len.ty (Num.max
      (Num.min (Num.add (Num.lit (.bit .i64) 1) q) len) (Num.one len.ty))
    let ref ← countedHiprec r (Num.add (first s)
      (Num.mul (Num.sub offset (Num.one offset.ty)) sstep))
    countedNew r.elementTy ref (Num.mul rstep sstep) len offset

/-- `base/range.jl:1158-1159`: all four parameters determine identical counted range types. -/
def countedSameType (r s : RngLen) : Bool :=
  decide (r.elementTy = s.elementTy ∧ r.ref.ty = s.ref.ty ∧
    r.stride.ty = s.stride.ty ∧ r.len.ty = s.len.ty)

/-- `base/range.jl:1158-1159`: same-type counted equality eagerly compares first, length, and last. -/
def countedSameTypeEq (r s : RngLen) : Jl Bool := do
  let empty := countedIsEmpty r && countedIsEmpty s
  let rf ← countedFirst r
  let sf ← countedFirst s
  let rl ← countedLast r
  let sl ← countedLast s
  return empty || (Num.eq rf sf && Num.eq r.len s.len && Num.eq rl sl)

/-- `base/range.jl:1161-1165`: the same-element/reference specialization short-circuits empty and singleton ranges. -/
def countedExactEq (r s : RngLen) : Jl Bool := do
  if countedIsEmpty r then return countedIsEmpty s
  if r.len.val = 1 then
    let a ← countedFirst r
    let b ← countedFirst s
    return decide (s.len.val = 1) && Num.eq a b
  let a ← countedFirst r
  let b ← countedFirst s
  let c ← countedLast r
  let d ← countedLast s
  return Num.eq a b && Num.eq r.stride s.stride && Num.eq c d

/-- `base/range.jl:1161-1165`: the StepRange/StepRangeLen{T,T} specialization, in either argument order. -/
def countedOrdinalExactEq (r : RngLen) (s : Rng) (countedLeft : Bool) : Jl Bool := do
  if countedLeft then
    if countedIsEmpty r then return isEmpty s
    if r.len.val = 1 then return Num.eq (first s) (last s) && Num.eq (← countedFirst r) (first s)
  else
    if isEmpty s then return countedIsEmpty r
    if Num.eq (first s) (last s) then return decide (r.len.val = 1) && Num.eq (first s) (← countedFirst r)
  let a ← countedFirst r
  let b ← countedLast r
  return Num.eq a (first s) && Num.eq r.stride (step s) && Num.eq b (last s)

/-- `base/range.jl:928-942`: generic equality observes both yielded element and Julia iteration state. -/
def countedResultIterate (r : ResultRng) (state : Option Num := none) : Jl (Option (Num × Num)) := do
  match r with
  | .counted r => countedIterate r state
  | .ordinal r =>
    let next ← iterate r state
    return next.map (fun x => (x, x))

/-- `base/range.jl:1178-1183`: finite evaluations of the generic equality loop.
An inductive execution relation preserves wrapping iteration states without an artificial fuel cutoff. -/
inductive CountedEqLoop (r s : ResultRng) :
    Jl (Option (Num × Num)) → Jl (Option (Num × Num)) → Jl Bool → Prop where
  | leftError (e) (ys) : CountedEqLoop r s (.error e) ys (.error e)
  | rightError (yr) (e) : CountedEqLoop r s (.ok yr) (.error e) (.error e)
  | stop (ys) : CountedEqLoop r s (.ok none) (.ok ys) (.ok true)
  | rightAbsent (x : Num × Num) :
      CountedEqLoop r s (.ok (some x)) (.ok none) (.error (.methodError "getindex"))
  | mismatch (x y : Num × Num) (h : Num.eq x.1 y.1 = false) :
      CountedEqLoop r s (.ok (some x)) (.ok (some y)) (.ok false)
  | next (x y : Num × Num) (out) (h : Num.eq x.1 y.1 = true)
      (tail : CountedEqLoop r s (countedResultIterate r (some x.2))
        (countedResultIterate s (some y.2)) out) :
      CountedEqLoop r s (.ok (some x)) (.ok (some y)) out

/-- `base/range.jl:1170-1184`: generic equality compares lengths before entering iteration. -/
def countedGenericEq (r s : ResultRng) (out : Jl Bool) : Prop :=
  match resultLength r, resultLength s with
  | .error e, _ => out = .error e
  | .ok _, .error e => out = .error e
  | .ok lr, .ok ls =>
    if !Num.eq lr ls then out = .ok false
    else if lr.val = 0 then out = .ok true
    else CountedEqLoop r s (countedResultIterate r) (countedResultIterate s) out

/-- `base/range.jl:1158-1184`: counted/counted equality dispatch. -/
def countedEq (r s : RngLen) (out : Jl Bool) : Prop :=
  if r.elementTy = s.elementTy ∧ r.ref.ty = r.elementTy ∧ s.ref.ty = s.elementTy then
    out = countedExactEq r s
  else if countedSameType r s then out = countedSameTypeEq r s
  else countedGenericEq (.counted r) (.counted s) out

/-- `base/range.jl:1161-1184`: counted/ordinal equality dispatch, including argument order. -/
def countedOrdinalEq (r : RngLen) (s : Rng) (out : Jl Bool)
    (countedLeft : Bool := true) : Prop :=
  if s.kind = .step ∧ r.elementTy = (first s).ty ∧ r.ref.ty = r.elementTy then
    out = countedOrdinalExactEq r s countedLeft
  else if countedLeft then countedGenericEq (.counted r) (.ordinal s) out
  else countedGenericEq (.ordinal s) (.counted r) out

/-- Stored cardinality remains exact even when reference/step arithmetic wraps in a narrow unsigned type. -/
def CountedCardinalityIndependentOfOverflow : Prop :=
  ∀ (ref stride : JInt .u8) (n offset : Num),
    let r : RngLen := ⟨⟨.bit .u8, ref⟩, ⟨.bit .u8, stride⟩, n, offset, .bit .u8⟩
    countedCheckedLength r = .ok n ∧ (countedIsEmpty r = true ↔ n.val = 0)

theorem countedCardinalityIndependentOfOverflow : CountedCardinalityIndependentOfOverflow := by
  intro ref stride n offset
  simp [countedCheckedLength, countedIsEmpty]

/-- An empty counted range rejects extrema before evaluating possibly inexact endpoints. -/
def CountedEmptyExtremaRejected : Prop :=
  ∀ r : RngLen, r.len.val = 0 →
    countedMinimum r = .error (.argumentError "range must be non-empty") ∧
    countedMaximum r = .error (.argumentError "range must be non-empty")

theorem countedEmptyExtremaRejected : CountedEmptyExtremaRejected := by
  intro r h
  simp [countedMinimum, countedMaximum, countedIsEmpty, h]
  constructor <;> rfl

/-- Iteration stops by its incremented state, with no endpoint comparisons. -/
def CountedIterationStopsPastLength : Prop :=
  ∀ (r : RngLen) (i : Num), r.len.val < (Num.add i (Num.one i.ty)).val →
    countedIterate r (some i) = .ok none

theorem countedIterationStopsPastLength : CountedIterationStopsPastLength := by
  intro r i h
  simp [countedIterate, h]
  rfl

/-- Last scalar indexing agrees with last, including any exact-conversion exception after wrapping arithmetic. -/
def CountedLastIndexConsistent : Prop :=
  ∀ r : RngLen, r.len.ty ≠ .bool → 0 < r.len.val →
    resultGetindex (.counted r) r.len = countedLast r

theorem countedLastIndexConsistent : CountedLastIndexConsistent := by
  intro r hty hpos
  have hbound : ¬ r.len.val < 1 := by omega
  simp [resultGetindex, countedLast, countedUnsafeGetindex, countedHiprec, hty, hbound]

def countedEntries : List Entry := []

end JuliaLean.Ranges

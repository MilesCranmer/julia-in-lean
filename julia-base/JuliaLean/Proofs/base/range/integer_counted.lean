import JuliaLean.base.range
import JuliaLean.base.broadcast
import JuliaLean.base.rounding
import JuliaLean.Registry.Types

namespace JuliaLean.Ranges

open JuliaLean.Registry



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

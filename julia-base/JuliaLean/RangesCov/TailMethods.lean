import JuliaLean.RangesCov.Ops
import JuliaLean.RangesCov.Log

namespace JuliaLean.RangesCov
namespace TailMethods

open JuliaLean JuliaLean.Registry

def SortpermRangeBehaviour : Prop := ∀ r, Ops.sortpermRange r = do
  let sorted ← Ops.issortedRange r
  let n ← Ranges.length r
  let one := Ranges.Num.lit (.bit .i64) 1
  if sorted then Colon.colonPromote3 one one n
  else Colon.colonPromote3 n (Ranges.Num.lit (.bit .i64) (-1)) one
theorem sortpermRangeBehaviour_proven : SortpermRangeBehaviour := fun _ => rfl

/-- `in(x::T, r::AbstractRange{T}) = _in_range(x,r)`, base/range.jl:1477. -/
def inSameType (inRange : α → β → γ) (x : α) (r : β) : γ := inRange x r
def InSameTypeBehaviour : Prop := ∀ (α β γ : Type) (f : α → β → γ) x r,
  inSameType f x r = f x r
theorem inSameTypeBehaviour_proven : InSameTypeBehaviour := fun _ _ _ _ _ _ => rfl

def DefineRangeOpBehaviour : Prop := ∀ f,
  Ops.defineRangeOp f = (Ops.ordinalOp f, Ops.linOp f)
theorem defineRangeOpBehaviour_proven : DefineRangeOpBehaviour := fun _ => rfl

def PromotedOpBehaviour : Prop := ∀ (α β γ : Type)
    (promote : α → β → JlX (γ × γ)) (op : γ → γ → JlX γ) a b,
  Ops.promotedOp promote op a b = do
    let p ← promote a b
    op p.1 p.2
theorem promotedOpBehaviour_proven : PromotedOpBehaviour := fun _ _ _ _ _ _ _ => rfl

def SubCountedBehaviour : Prop := ∀ r s,
  Ops.subCounted r s = Ops.addCounted r (Ops.negCounted s)
theorem subCountedBehaviour_proven : SubCountedBehaviour := fun _ _ => rfl

def ModOneToBehaviour : Prop := ∀ i r,
  Ops.modOneTo i r = Ops.mod1 i (Ranges.last r)
theorem modOneToBehaviour_proven : ModOneToBehaviour := fun _ _ => rfl

def LogExtraGenericBehaviour : Prop := ∀ log a b len,
  Log.lograngeExtraGeneric log a b len =
    let la := log (Float.F64.mul Float.F64.one a)
    let lb := log (Float.F64.mul Float.F64.one b)
    (Float.F64.div la (FloatRanges.flt (len - FloatRanges.i64 1)),
      Float.F64.div lb (FloatRanges.flt (len - FloatRanges.i64 1)))
theorem logExtraGenericBehaviour_proven : LogExtraGenericBehaviour := fun _ _ _ _ => rfl

def LogExtraFloatBehaviour : Prop := ∀ logTwice a b len,
  Log.lograngeExtra logTwice a b len =
    let la := logTwice a
    let lb := logTwice b
    (la.divF (FloatRanges.flt (len - FloatRanges.i64 1)),
      lb.divF (FloatRanges.flt (len - FloatRanges.i64 1)))
theorem logExtraFloatBehaviour_proven : LogExtraFloatBehaviour := fun _ _ _ _ => rfl

/-- A binding partition result needed by `_resolve_in_world`, base/range.jl:1729-1736. -/
structure BindingPartition where
  maxWorld : Nat

inductive ResolveError where
  | bindingDoesNotCoverRange
  deriving DecidableEq

def resolveInWorld (lookup : Nat → α → BindingPartition) (resolve : Nat → α → β)
    (first last : Nat) (gr : α) : Except ResolveError β :=
  let bpart := lookup first gr
  if bpart.maxWorld < last then .error .bindingDoesNotCoverRange
  else .ok (resolve last gr)

def ResolveInWorldBehaviour : Prop := ∀ (α β : Type)
    (lookup : Nat → α → BindingPartition) (resolve : Nat → α → β) first last (gr : α),
  resolveInWorld lookup resolve first last gr =
    let bpart := lookup first gr
    if bpart.maxWorld < last then .error .bindingDoesNotCoverRange
    else .ok (resolve last gr)
theorem resolveInWorldBehaviour_proven : ResolveInWorldBehaviour := fun _ _ _ _ _ _ _ => rfl

def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/range.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := []

end TailMethods
end JuliaLean.RangesCov

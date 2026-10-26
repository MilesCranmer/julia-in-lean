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

def entries : List Entry := [
  entry "rangescov-r1456-sortperm" "sortperm(::AbstractRange)" "A sorted range maps to ascending indices and an unsorted range to descending indices." "sortperm invariant; base/range.jl:1456" ``SortpermRangeBehaviour ``sortpermRangeBehaviour_proven,
  entry "rangescov-r1477-in-same" "in(x::T, r::AbstractRange{T})" "Same-type membership delegates to _in_range without changing either argument." "membership invariant; base/range.jl:1477" ``InSameTypeBehaviour ``inSameTypeBehaviour_proven,
  entry "rangescov-r1492-define-op" "_define_range_op(f)" "The generator installs the ordinal and LinRange implementations for its operator." "base/range.jl:1492-1513" ``DefineRangeOpBehaviour ``defineRangeOpBehaviour_proven,
  entry "rangescov-r1509-promoted-op" "generated f(::Union{StepRangeLen,OrdinalRange,LinRange}, ...)" "The generated fallback promotes both ranges and applies the same operator." "base/range.jl:1509-1511" ``PromotedOpBehaviour ``promotedOpBehaviour_proven,
  entry "rangescov-r1524-sub-counted" "-(::StepRangeLen, ::StepRangeLen)" "Counted subtraction adds the negated second range." "base/range.jl:1524" ``SubCountedBehaviour ``subCountedBehaviour_proven,
  entry "rangescov-r1548-mod-oneto" "mod(::Integer, ::OneTo)" "OneTo modular reduction is mod1(i,last(r))." "mod docstring; base/range.jl:1548" ``ModOneToBehaviour ``modOneToBehaviour_proven,
  entry "rangescov-r1691-log-extra" "_logrange_extra(::Real, ::Real, ::Int)" "The generic helper widens inputs, takes logs and divides both by len-1." "base/range.jl:1691-1695" ``LogExtraGenericBehaviour ``logExtraGenericBehaviour_proven,
  entry "rangescov-r1696-log-extra-f64" "_logrange_extra(::Float64, ::Float64, ::Int)" "The Float64 helper computes twice-precision logs and divides both by len-1." "base/range.jl:1696-1702" ``LogExtraFloatBehaviour ``logExtraFloatBehaviour_proven,
  entry "rangescov-r1729-resolve-world" "_resolve_in_world(::UnitRange, ::GlobalRef)" "The method errors unless the binding partition covers the full world range, then resolves at the last world." "base/range.jl:1729-1736" ``ResolveInWorldBehaviour ``resolveInWorldBehaviour_proven
]

end TailMethods
end JuliaLean.RangesCov

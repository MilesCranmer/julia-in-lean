import JuliaLean.FloatRanges.Properties

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

namespace JuliaLean.BroadcastCov.Refutations

open JuliaLean
open JuliaLean.Float
open JuliaLean.FloatRanges

def okThen {α : Type} (x : Jl α) (p : α → Prop) : Prop :=
  match x with
  | .ok a => p a
  | .error _ => True

instance {α : Type} (x : Jl α) (p : α → Prop) [∀ a, Decidable (p a)] :
    Decidable (okThen x p) := by
  unfold okThen
  split <;> infer_instance

/-- The LinRange `.+` and `.-` fast paths at lines 1196 and 1210. -/
def linShift (r : Lin) (x : F64) (subtract : Bool) : Jl Lin :=
  if subtract then
    Lin.mk' (F64.sub r.start x) (F64.sub r.stop x) r.len
  else
    Lin.mk' (F64.add r.start x) (F64.add r.stop x) r.len

/-- A range-returning broadcast has the same elements as applying the operator
to each LinRange element, as promised by the broadcast docstring. -/
def LinRangeShiftElementwise : Prop :=
  ∀ (a b x : F64) (n i : I64) (subtract : Bool),
    okThen (Lin.mk' a b n) fun r =>
      okThen (linShift r x subtract) fun q =>
        1 ≤ i.val → i.val ≤ r.len.val →
          F64.isequal (q.unsafeGet i)
            (if subtract then F64.sub (r.unsafeGet i) x
             else F64.add (r.unsafeGet i) x) = true

theorem linRangeShiftElementwise_refuted : ¬ LinRangeShiftElementwise := fun h =>
  absurd (h fzero F64.one (dec 2) (i64 7) (i64 2) false) (by decide +kernel)

/-- The StepRangeLen `./` fast path at lines 1231-1232. -/
def stepRangeLenDiv (r : SRL) (x : F64) : Jl SRL :=
  SRL.mk' (r.ref.divF x) (r.step.divF x) r.len r.offset

/-- Broadcast division has the same elements as dividing each original
StepRangeLen element. -/
def StepRangeLenDivElementwise : Prop :=
  ∀ (a s x : F64) (n i : I64),
    okThen (rangeStartStepLength a s n) fun r =>
      okThen (stepRangeLenDiv r x) fun q =>
        1 ≤ i.val → i.val ≤ r.len.val →
          F64.isequal (q.unsafeGet i) (F64.div (r.unsafeGet i) x) = true

theorem stepRangeLenDivElementwise_refuted : ¬ StepRangeLenDivElementwise := fun h =>
  absurd (h fzero (dec 1 4) (dec 3) (i64 6) (i64 6)) (by decide +kernel)

end JuliaLean.BroadcastCov.Refutations

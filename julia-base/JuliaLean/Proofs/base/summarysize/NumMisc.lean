import JuliaLean.base.summarysize

namespace JuliaLean.NumMisc.Coverage

def SummarySizeBehavior : Prop :=
  (∀ object index, nthPointerDefined object index = (index ≥ 1 && index ≤ object.pointers.length)) ∧
  (∀ object index, getNthPointer object index = object.pointers.getD (index - 1) 0) ∧
  (∀ count object, chargeObject count object = if count then 1 else object.bytes) ∧
  (∀ object, summaryChildren object = match object.kind with
    | .string | .bigint => []
    | .memoryInline | .memoryBoxed | .tuple | .cancellation | .waitEntry | .generic
    | .datatype | .typename | .simpleVector | .module | .task => object.pointers) ∧
  (∀ count excluded charge object state, summaryVisit count excluded charge object state =
    if state.seen.contains object.identity then state
    else if excluded && !charge then { state with seen := object.identity :: state.seen }
    else { seen := object.identity :: state.seen,
           frontier := (summaryChildren object).map (fun identity => { object with identity }) ++ state.frontier,
           size := state.size + chargeObject count object }) ∧
  (∀ count objects state, summaryLoop count objects state = match objects with
    | [] => state
    | object :: rest => summaryLoop count rest (summaryVisit count false false object state))

theorem summarySizeBehavior : SummarySizeBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro object
    cases object with
    | mk identity bytes pointers kind => cases kind <;> rfl
  · intros; rfl
  · intro count objects; cases objects <;> intros <;> rfl

end JuliaLean.NumMisc.Coverage

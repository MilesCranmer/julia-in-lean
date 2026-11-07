import JuliaLean.base.reducedim
import JuliaLean.Registry.Types

/-!
# Specifications of `base/reducedim.jl`

The statements remain open (`todo`) for the proof worker. Array, index, iterator,
comparison, and scalar-reduction operations are the typed interfaces used by the
source mirror. The slice and reduction statements quantify over those interfaces
and over the model's actual methods.
-/

namespace JuliaLean.Proofs.base.reducedim

open JuliaLean JuliaLean.base.reducedim JuliaLean.Registry

def AxesShapeExact (ops : Operations) (region : ops.Region) :
    List ops.Axis → List ops.Axis → Nat → Prop
  | [], [], _ => True
  | input :: inputs, output :: outputs, dimension =>
      (ops.inRegion region (int (Int.ofNat dimension + 1)) = .ok true →
        ops.axisLength output = int 1) ∧
      (ops.inRegion region (int (Int.ofNat dimension + 1)) = .ok false →
        ops.axisEqual input output = true) ∧
      AxesShapeExact ops region inputs outputs (dimension + 1)
  | _, _, _ => False

def ReducedIndicesShape (ops : Operations) : Prop :=
  ∀ {α : Type} (A : ops.Input α) region inputAxes outputAxes,
    check_valid_region ops region = .ok () →
    ops.axesInput A = .ok inputAxes →
    reduced_indices_input ops A region = .ok outputAxes →
    AxesShapeExact ops region inputAxes outputAxes 0

def reductionSliceAxes (ops : Operations) (region : ops.Region) :
    List ops.Axis → List ops.Index → Nat → Result (List ops.Axis)
  | [], [], _ => .ok []
  | axis :: axes, coordinate :: coordinates, dimension => do
      let selected ← ops.inRegion region (int (Int.ofNat dimension + 1))
      let sliceAxis ← if selected then pure axis else ops.unitRange coordinate coordinate
      let rest ← reductionSliceAxes ops region axes coordinates (dimension + 1)
      pure (sliceAxis :: rest)
  | _, _, _ => ops.iteratorError

def reductionSlice {α : Type} (ops : Operations) (A : ops.Input α)
    (region : ops.Region) (coordinate : List ops.Index) : Result (ops.Input α) := do
  let axes ← ops.axesInput A
  let selectedAxes ← reductionSliceAxes ops region axes coordinate 0
  ops.view A selectedAxes

def reductionSliceValue {α β γ : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (init : InitArg β) (A : ops.Input α)
    (region : ops.Region) (coordinate : List ops.Index) : Result β := do
  let slice ← reductionSlice ops A region coordinate
  match init with
  | .implicit => _mapreduce_dim_colon_implicit ops f op slice
  | .explicit value => _mapreduce_dim_colon_init (γ := γ) ops f op value slice

def MapreduceDimsShape (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (op : ops.Operator) (A : ops.Input α)
    (dims : ops.Region) (init : InitArg β) (R : ops.Array β) inputAxes outputAxes,
    ops.isColon dims = false →
    check_valid_region ops dims = .ok () →
    mapreduce (γ := γ) ops f op A dims init = .ok (.array R) →
    ops.axesInput A = .ok inputAxes →
    ops.axesArray R = .ok outputAxes →
    AxesShapeExact ops dims inputAxes outputAxes 0

def MapreduceDimsSliceValues (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (op : ops.Operator) (A : ops.Input α)
    (dims : ops.Region) (init : InitArg β) (R : ops.Array β)
    (coordinate : List ops.Index) (value : β),
    ops.isColon dims = false →
    mapreduce (γ := γ) ops f op A dims init = .ok (.array R) →
    ops.getArray R coordinate = .ok value →
    reductionSliceValue (γ := γ) ops f op init A dims coordinate = .ok value

def MapreduceDimsExact (ops : Operations) : Prop :=
  MapreduceDimsShape ops ∧ MapreduceDimsSliceValues ops

def ReductionOutputAxesExact (ops : Operations) {α β : Type}
    (A : ops.Input α) (dims : ops.Region) (R : ops.Array β) : Prop :=
  ops.isColon dims = false →
  check_valid_region ops dims = .ok () →
  ∀ inputAxes outputAxes,
    ops.axesInput A = .ok inputAxes →
    ops.axesArray R = .ok outputAxes →
    AxesShapeExact ops dims inputAxes outputAxes 0

def ReductionArraySliceValues (ops : Operations) {α β γ : Type}
    (f : ops.Function) (op : ops.Operator) (A : ops.Input α)
    (dims : ops.Region) (init : InitArg β) (R : ops.Array β) : Prop :=
  ∀ coordinate value,
    ops.getArray R coordinate = .ok value →
    reductionSliceValue (γ := γ) ops f op init A dims coordinate = .ok value

def widenedSumTypeTag : TypeTag → Option TypeTag
  | .named "Bool" | .named "Int8" | .named "Int16" | .named "Int32" =>
      some (.named "Int64")
  | .named "UInt8" | .named "UInt16" | .named "UInt32" =>
      some (.named "UInt64")
  | .named "Int64" => some (.named "Int64")
  | .named "UInt64" => some (.named "UInt64")
  | .named "Int128" => some (.named "Int128")
  | .named "UInt128" => some (.named "UInt128")
  | _ => none

def SumWidenedTypeExact (ops : Operations) {α β : Type}
    (A : ops.Input α) (init : InitArg β) (R : ops.Array β) : Prop :=
  match init with
  | .explicit _ => True
  | .implicit =>
      match widenedSumTypeTag (ops.elementType A) with
      | none => True
      | some resultType =>
          ∀ coordinate value, ops.getArray R coordinate = .ok value →
            ops.valueType value = resultType

def SumDimsExact (ops : Operations) : Prop :=
  ∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (init : InitArg β)
    (R : ops.Array β),
    sum ops A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := α) ops ops.identity ops.addSum A dims init R ∧
    SumWidenedTypeExact ops A init R

def ProdDimsExact (ops : Operations) : Prop :=
  ∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (init : InitArg β)
    (R : ops.Array β),
    prod ops A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := α) ops ops.identity ops.mulProd A dims init R

def MaxMinDimsExact (ops : Operations) : Prop :=
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (init : InitArg β)
      (R : ops.Array β),
    maximum ops A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := α) ops ops.identity ops.maximum A dims init R) ∧
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (init : InitArg β)
      (R : ops.Array β),
    minimum ops A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := α) ops ops.identity ops.minimum A dims init R)

def AnyAllDimsExact (ops : Operations) : Prop :=
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (init : InitArg β)
      (R : ops.Array β),
    any ops A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := α) ops ops.identity
      ops.orAny A dims init R) ∧
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (init : InitArg β)
      (R : ops.Array β),
    all ops A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := α) ops ops.identity
      ops.andAll A dims init R)
def MapreducedimInPlaceContract (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (R : ops.Array β) (A : ops.Input α) error,
    check_reducedims ops R A = .error error →
      _mapreducedim! (γ := γ) ops f op R A = .error error

def MapreducedimInPlaceSliceValues (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (R : ops.Array β) (A : ops.Input α) (region : ops.Region)
    (result : ops.Array β) (coordinate : List ops.Index)
    (initial value : β) (outputAxes reducedAxes : List ops.Axis),
    ops.axesArray R = .ok outputAxes →
    reduced_indices_input ops A region = .ok reducedAxes →
    ops.axesEqual outputAxes reducedAxes = true →
    mapreducedim! (γ := γ) ops f op R A = .ok result →
    ops.getArray R coordinate = .ok initial →
    ops.getArray result coordinate = .ok value →
    reductionSliceValue (γ := γ) ops f op (.explicit initial) A region coordinate =
      .ok value

def MapreducedimInPlaceExact (ops : Operations) : Prop :=
  MapreducedimInPlaceContract ops ∧ MapreducedimInPlaceSliceValues ops

def MapfirstExact (ops : Operations) : Prop :=
  ∀ {α β : Type} (f : ops.Function) (R : ops.Array β) (A : ops.Input α)
    (result : ops.Array β) (resultAxes inputAxes sliceAxes : List ops.Axis)
    (sourceSlice : ops.Input α),
    mapfirst! ops f R A = .ok result →
    ops.axesArray R = .ok resultAxes →
    ops.axesInput A = .ok inputAxes →
    firstReducedSlice ops resultAxes inputAxes = .ok sliceAxes →
    ops.view A sliceAxes = .ok sourceSlice →
    ops.mapInto f R sourceSlice = .ok result

def MapreducedimKernelExact (ops : Operations) : Prop :=
  MapfirstExact ops ∧ MapreducedimInPlaceExact ops

def MinMaxEmptySliceError (ops : Operations) : Prop :=
  ∀ {α β : Type} (f : ops.Function) (A : ops.Input α) (region : ops.Region),
    hasEmptyRegionAxis ops A (ops.regionItems region) = .ok true →
    reducedimInitMinMax (β := β) ops true f A region =
      ops.emptyReduce (α := ops.Array β)

def MaximumNaNSeed (ops : Operations) : Prop :=
  ∀ {α β : Type} (f : ops.Function) (A : ops.Input α) (region : ops.Region)
    (axes : List ops.Axis) (slice : ops.Input α) (initial seed : β)
    (R : ops.Array β) (coordinate : List ops.Index) value,
    reduced_indices_input ops A region = .ok axes →
    ops.view A axes = .ok slice →
    mapreduceNoInit ops f ops.minimum slice = .ok initial →
    ops.isNumber initial = true →
    ops.isNaN initial = true →
    ops.infinity initial false = .ok seed →
    reducedimInitMinMax ops true f A region = .ok R →
    ops.getArray R coordinate = .ok value →
    value = seed
def MinMaxInitializationExact (ops : Operations) : Prop :=
  MinMaxEmptySliceError ops ∧ MaximumNaNSeed ops

def PromoteUnionExact (ops : Operations) : Prop :=
  ∀ left right promoted leftResult rightResult,
    promote_union ops (.union left right) = .ok promoted →
    promote_union ops left = .ok leftResult →
    promote_union ops right = .ok rightResult →
    ops.promoteType leftResult rightResult = .ok promoted


def countTrueLoop {α β : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (one : β) : List ops.Index → β → Result β
  | [], accumulator => .ok accumulator
  | key :: keys, accumulator => do
      let value ← ops.getInputLinear A key
      let predicate ← ops.applyFunction (F := ops.Function) (α := α) (β := Bool)
        (ops.boolFunction f) value
      let truth ← ops.toBool predicate
      if truth then
        let next ← ops.applyOperator (O := ops.Operator) (A := β) (B := β)
          ops.addSum accumulator one
        countTrueLoop ops f A one keys next
      else
        countTrueLoop ops f A one keys accumulator

def countExpected {α β : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (initial : β) : Result β := do
  let one ← ops.oneType (ops.valueTypeOf initial)
  let keys ← ops.eachIndexInput A
  countTrueLoop ops f A one keys initial

def CountColonExact (ops : Operations) : Prop :=
  ∀ {α β : Type} (f : ops.Function) (A : ops.Input α) (initial expected : β),
    countExpected ops f A initial = .ok expected →
    count_function ops f A ops.colonRegion initial = .ok (.scalar expected)

def CountDimsExact (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α) (dims : ops.Region)
    (initial : β) (R : ops.Array β) (coordinate : List ops.Index) (value : β),
    ops.isColon dims = false →
    count_function ops f A dims initial = .ok (.array R) →
    ops.getArray R coordinate = .ok value →
    reductionSliceValue (γ := γ) ops (ops.boolFunction f) ops.addSum
      (.explicit initial) A dims coordinate = .ok value

def CountExact (ops : Operations) : Prop := CountColonExact ops ∧ CountDimsExact ops

def FindIndexMatchesSlice (ops : Operations) (isMax : Bool)
    {α γ : Type} (f : ops.Function) (A : ops.Input α) (dims : ops.Region)
    (R : FindResult ops.Array ops.Index γ) (coordinate : List ops.Index) : Prop :=
  ∀ value key slice sliceKeys input,
    reductionSlice ops A dims coordinate = .ok slice →
    ops.getArray R.values coordinate = .ok value →
    ops.getArray R.indices coordinate = .ok key →
    ops.getInputLinear A key = .ok input →
    ops.applyFunction (F := ops.Function) (α := α) (β := γ) f input = .ok value →
    ops.eachIndexInput slice = .ok sliceKeys →
    ∀ otherKey candidate mapped, otherKey ∈ sliceKeys →
      ops.getInputLinear slice otherKey = .ok candidate →
      ops.applyFunction (F := ops.Function) (α := α) (β := γ) f candidate = .ok mapped →
      (isMax = true → ops.applyPredicate ops.less value mapped = .ok false) ∧
      (isMax = false → ops.applyPredicate ops.greater value mapped = .ok false)

def FindDimsExact (ops : Operations) : Prop :=
  ∀ {α γ : Type} (f : ops.Function) (A : ops.Input α) (dims : ops.Region)
    (minimum maximum : FindResult ops.Array ops.Index γ),
    findmax_function ops f A dims = .ok maximum →
    findmin_function ops f A dims = .ok minimum →
    ∀ coordinate,
      FindIndexMatchesSlice ops true f A dims maximum coordinate ∧
      FindIndexMatchesSlice ops false f A dims minimum coordinate

def FindIdentityDimsExact (ops : Operations) : Prop :=
  ∀ {α : Type} (A : ops.Input α) (dims : ops.Region)
    (minimum maximum : FindResult ops.Array ops.Index α),
    findmax ops A dims = .ok maximum →
    findmin ops A dims = .ok minimum →
    ∀ coordinate,
      FindIndexMatchesSlice ops true ops.identity A dims maximum coordinate ∧
      FindIndexMatchesSlice ops false ops.identity A dims minimum coordinate

def FindDimsShapeExact (ops : Operations) : Prop :=
  ∀ {α : Type} (A : ops.Input α) (dims : ops.Region)
    (minimum maximum : FindResult ops.Array ops.Index α) axes,
    reduced_indices_input ops A dims = .ok axes →
    findmax ops A dims = .ok maximum →
    findmin ops A dims = .ok minimum →
    ∀ outputAxes,
      ops.axesArray maximum.values = .ok outputAxes →
      ops.axesEqual axes outputAxes = true
      ∧ ops.axesArray maximum.indices = .ok outputAxes
      ∧ ops.axesArray minimum.values = .ok outputAxes
      ∧ ops.axesArray minimum.indices = .ok outputAxes
      ∧ (∀ indices,
        argmax ops A dims = .ok indices →
        ops.axesArray indices = .ok outputAxes)
      ∧ (∀ indices,
        argmin ops A dims = .ok indices →
        ops.axesArray indices = .ok outputAxes)

def ArgFindDimsExact (ops : Operations) : Prop :=
  (∀ {α : Type} (A : ops.Input α) (dims : ops.Region)
      (result : FindResult ops.Array ops.Index α) indices,
    findmax ops A dims = .ok result →
    argmax ops A dims = .ok indices →
    indices = result.indices) ∧
  (∀ {α : Type} (A : ops.Input α) (dims : ops.Region)
      (result : FindResult ops.Array ops.Index α) indices,
    findmin ops A dims = .ok result →
    argmin ops A dims = .ok indices →
    indices = result.indices)
def EmptyReductionIdentities (ops : Operations) : Prop :=
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (R : ops.Array β)
      (coordinate : List ops.Index),
    ops.isColon dims = false →
    hasEmptyRegionAxis ops A (ops.regionItems dims) = .ok true →
    sum ops A dims (.implicit : InitArg β) = .ok (.array R) →
    ∀ value, ops.getArray R coordinate = .ok value →
      ops.zeroArray R = .ok value) ∧
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (R : ops.Array β)
      (coordinate : List ops.Index),
    ops.isColon dims = false →
    hasEmptyRegionAxis ops A (ops.regionItems dims) = .ok true →
    prod ops A dims (.implicit : InitArg β) = .ok (.array R) →
    ∀ value, ops.getArray R coordinate = .ok value →
      ops.oneArray R = .ok value) ∧
  (∀ {α : Type} (A : ops.Input α) (dims : ops.Region) (R : ops.Array Bool)
      (coordinate : List ops.Index),
    ops.isColon dims = false →
    hasEmptyRegionAxis ops A (ops.regionItems dims) = .ok true →
    any (β := Bool) ops A dims .implicit = .ok (.array R) →
    ∀ value, ops.getArray R coordinate = .ok value →
      value = ops.falseArrayValue) ∧
  (∀ {α : Type} (A : ops.Input α) (dims : ops.Region) (R : ops.Array Bool)
      (coordinate : List ops.Index),
    ops.isColon dims = false →
    hasEmptyRegionAxis ops A (ops.regionItems dims) = .ok true →
    all (β := Bool) ops A dims .implicit = .ok (.array R) →
    ∀ value, ops.getArray R coordinate = .ok value →
      value = ops.trueArrayValue) ∧
  (∀ {α : Type} (A : ops.Input α) (dims : ops.Region) (R : ops.Array I64)
      (coordinate : List ops.Index),
    ops.isColon dims = false →
    hasEmptyRegionAxis ops A (ops.regionItems dims) = .ok true →
    count ops A dims (int 0) = .ok (.array R) →
    ops.getArray R coordinate = .ok (int 0))

def MaxMinEmptySlicesError (ops : Operations) : Prop :=
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) error,
    ops.isColon dims = false →
    hasEmptyRegionAxis ops A (ops.regionItems dims) = .ok true →
    maximum (β := β) ops A dims .implicit = .error error) ∧
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) error,
    ops.isColon dims = false →
    hasEmptyRegionAxis ops A (ops.regionItems dims) = .ok true →
    minimum (β := β) ops A dims .implicit = .error error) ∧
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) error,
    ops.isColon dims = false →
    hasEmptyRegionAxis ops A (ops.regionItems dims) = .ok true →
    extrema (β := β) ops A dims .implicit = .error error)

/-- `ops.Array` is a value, so "updates and returns its output array" means the returned
array keeps the output's axes; slice values are `MapreducedimInPlaceSliceValues`. -/
def InPlaceReductionOutputs (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) result,
    (sumInPlace (γ := γ) ops f R A init = .ok result → ops.axesArray result = ops.axesArray R) ∧
    (prodInPlace (γ := γ) ops f R A init = .ok result → ops.axesArray result = ops.axesArray R) ∧
    (maximumInPlace (γ := γ) ops f R A init = .ok result → ops.axesArray result = ops.axesArray R) ∧
    (minimumInPlace (γ := γ) ops f R A init = .ok result → ops.axesArray result = ops.axesArray R) ∧
    (extremaInPlace (γ := γ) ops f R A init = .ok result → ops.axesArray result = ops.axesArray R) ∧
    (allInPlace (γ := γ) ops f R A init = .ok result → ops.axesArray result = ops.axesArray R) ∧
    (anyInPlace (γ := γ) ops f R A init = .ok result → ops.axesArray result = ops.axesArray R) ∧
    (countInPlace (γ := γ) ops f R A init = .ok result → ops.axesArray result = ops.axesArray R)

def InPlaceSizeMismatchError (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) mismatch,
    check_reducedims ops R A = .error mismatch →
    (∃ failure, sumInPlace (γ := γ) ops f R A init = .error failure) ∧
    (∃ failure, prodInPlace (γ := γ) ops f R A init = .error failure) ∧
    (∃ failure, maximumInPlace (γ := γ) ops f R A init = .error failure) ∧
    (∃ failure, minimumInPlace (γ := γ) ops f R A init = .error failure) ∧
    (∃ failure, extremaInPlace (γ := γ) ops f R A init = .error failure) ∧
    (∃ failure, allInPlace (γ := γ) ops f R A init = .error failure) ∧
    (∃ failure, anyInPlace (γ := γ) ops f R A init = .error failure) ∧
    (∃ failure, countInPlace (γ := γ) ops f R A init = .error failure)

def SliceHasNaN (ops : Operations) {α : Type} (slice : ops.Input α) : Prop :=
  ∃ keys key value,
    ops.eachIndexInput slice = .ok keys ∧
    key ∈ keys ∧
    ops.getInputLinear slice key = .ok value ∧
    ops.isNaN value = true

def MaxMinNaNPropagation (ops : Operations) : Prop :=
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (R : ops.Array β)
      (coordinate : List ops.Index) (slice : ops.Input α) value,
    ops.containsMissing (ops.elementType A) = false →
    maximum ops A dims .implicit = .ok (.array R) →
    reductionSlice ops A dims coordinate = .ok slice →
    SliceHasNaN ops slice →
    ops.getArray R coordinate = .ok value →
    ops.isNaN value = true) ∧
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (R : ops.Array β)
      (coordinate : List ops.Index) (slice : ops.Input α) value,
    ops.containsMissing (ops.elementType A) = false →
    minimum ops A dims .implicit = .ok (.array R) →
    reductionSlice ops A dims coordinate = .ok slice →
    SliceHasNaN ops slice →
    ops.getArray R coordinate = .ok value →
    ops.isNaN value = true)

def SumFunctionDimsExact (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
    (dims : ops.Region) (init : InitArg β) (R : ops.Array β),
    sum_function (γ := γ) ops f A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := γ) ops f ops.addSum A dims init R

def ProdFunctionDimsExact (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
    (dims : ops.Region) (init : InitArg β) (R : ops.Array β),
    prod_function (γ := γ) ops f A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := γ) ops f ops.mulProd A dims init R

def MaxMinFunctionDimsExact (ops : Operations) : Prop :=
  (∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
      (dims : ops.Region) (init : InitArg β) (R : ops.Array β),
    maximum_function (γ := γ) ops f A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := γ) ops f ops.maximum A dims init R) ∧
  (∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
      (dims : ops.Region) (init : InitArg β) (R : ops.Array β),
    minimum_function (γ := γ) ops f A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := γ) ops f ops.minimum A dims init R)

def ExtremaFunctionDimsExact (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
    (dims : ops.Region) (init : InitArg β) (R : ops.Array β),
    extrema_function (γ := γ) ops f A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := γ × γ) ops (ops.makeExtremaMap f)
      ops.extremaRF A dims init R

def AnyAllFunctionDimsExact (ops : Operations) : Prop :=
  (∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
      (dims : ops.Region) (init : InitArg β) (R : ops.Array β),
    any_function (γ := γ) ops f A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := γ) ops f
      ops.orAny A dims init R) ∧
  (∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
      (dims : ops.Region) (init : InitArg β) (R : ops.Array β),
    all_function (γ := γ) ops f A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := γ) ops f
      ops.andAll A dims init R)

def GeneratedReductionFunctionsExact (ops : Operations) : Prop :=
  SumFunctionDimsExact ops ∧ ProdFunctionDimsExact ops ∧
  MaxMinFunctionDimsExact ops ∧ ExtremaFunctionDimsExact ops ∧
  AnyAllFunctionDimsExact ops

def GeneratedReductionContract (ops : Operations) : Prop :=
  MapreduceDimsExact ops ∧ SumDimsExact ops ∧ ProdDimsExact ops ∧
  MaxMinDimsExact ops ∧ AnyAllDimsExact ops ∧
  GeneratedReductionFunctionsExact ops ∧
  EmptyReductionIdentities ops ∧ MaxMinEmptySlicesError ops ∧
  MaxMinNaNPropagation ops ∧ InPlaceReductionOutputs ops ∧
  InPlaceSizeMismatchError ops

def MaxMinUnionSuccess (ops : Operations) : Prop :=
  ∀ {α : Type} (A : ops.Input α) (dims : ops.Region),
    ops.isEmptyInput A = .ok false →
    ops.isColon dims = false →
    (ops.elementType A = .named "Int" ∨
      ops.elementType A = .named "Int64" ∨
      ops.elementType A = .named "Float64" ∨
      ops.elementType A = .union (.named "Int") (.named "Float64") ∨
      ops.elementType A = .union (.named "Float64") (.named "Int") ∨
      ops.elementType A = .union (.named "Int64") (.named "Float64") ∨
      ops.elementType A = .union (.named "Float64") (.named "Int64")) →
    ∃ (β : Type) (R : ops.Array β),
      maximum (β := β) ops A dims .implicit = .ok (.array R)

def MaxMinUnionDimsExact (ops : Operations) : Prop :=
  MaxMinUnionSuccess ops ∧ MaxMinDimsExact ops

def AllInputMissing (ops : Operations) {α : Type} (A : ops.Input α) : Prop :=
  ∀ key value, ops.getInputLinear A key = .ok value →
    ops.isInstance value ops.missingType = true

def MaxMinAllMissingValues (ops : Operations) : Prop :=
  ∀ {α : Type} (A : ops.Input α) (dims : ops.Region),
    ops.isEmptyInput A = .ok false →
    ops.isColon dims = false →
    AllInputMissing ops A →
    ∃ (βmax : Type) (Rmax : ops.Array βmax) (βmin : Type)
      (Rmin : ops.Array βmin),
      maximum (β := βmax) ops A dims .implicit = .ok (.array Rmax) ∧
      minimum (β := βmin) ops A dims .implicit = .ok (.array Rmin) ∧
      (∀ coordinate value, ops.getArray Rmax coordinate = .ok value →
        ops.isInstance value ops.missingType = true) ∧
      (∀ coordinate value, ops.getArray Rmin coordinate = .ok value →
        ops.isInstance value ops.missingType = true)

def InPlaceMaxMinEmptySliceErrorClaim (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (R : ops.Array β) (A : ops.Input α)
    outputAxes region reducedAxes,
    ops.axesArray R = .ok outputAxes →
    reduced_indices_input ops A region = .ok reducedAxes →
    ops.axesEqual outputAxes reducedAxes = true →
    hasEmptyRegionAxis ops A (ops.regionItems region) = .ok true →
    (∃ error, maximumInPlace (γ := γ) ops f R A true = .error error) ∧
    (∃ error, minimumInPlace (γ := γ) ops f R A true = .error error) ∧
    (∃ error, extremaInPlace (γ := γ) ops f R A true = .error error)

def FindInPlaceReturnsArrays (ops : Operations) : Prop :=
  (∀ {α : Type} (Rval : ops.Array α) (Rind : ops.Array ops.Index)
      (A : ops.Input α) (init : Bool) values indices,
    findminInPlace ops Rval Rind A init = .ok (values, indices) →
    values = Rval ∧ indices = Rind) ∧
  (∀ {α : Type} (Rval : ops.Array α) (Rind : ops.Array ops.Index)
      (A : ops.Input α) (init : Bool) values indices,
    findmaxInPlace ops Rval Rind A init = .ok (values, indices) →
    values = Rval ∧ indices = Rind)


def RegionValuesPositive (ops : Operations) (region : ops.Region) : Prop :=
  ∀ dimensions, ops.regionItems region = dimensions →
    ∀ dimension, dimension ∈ dimensions →
      ops.isInteger dimension = true →
      ∃ value, ops.toInt dimension = .ok value ∧ value.val ≥ 1


def ValidRegionExact (ops : Operations) : Prop :=
  ∀ region, check_valid_region ops region = .ok () → RegionValuesPositive ops region

def UnsupportedUnitRangeExact (ops : Operations) : Prop :=
  ∀ axis message,
    reduced_index_unitRange ops axis = .error
      (.julia (.argumentError message)) →
    message = "\nNo method is implemented for reducing index range of type " ++
      ops.typeName axis ++ ". Please implement\nreduced_index for this index type or report this as an issue.\n"

def ReducedInitTypeExact (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (A : ops.Input α) (region : ops.Region) (R : ops.Array β)
    (expectedAxes outputAxes : List ops.Axis),
    reducedim_init_dispatch (γ := γ) ops f op A region = .ok R →
    reduced_indices_input ops A region = .ok expectedAxes →
    ops.axesArray R = .ok outputAxes →
    ops.axesEqual expectedAxes outputAxes = true

def FindInPlaceReturnsAxes (ops : Operations) : Prop :=
  ∀ {α : Type} (Rval : ops.Array α) (Rind : ops.Array ops.Index)
    (A : ops.Input α) (init : Bool) values indices axes,
    ops.isEmptyArray Rval = .ok false →
    ops.isEmptyInput A = .ok false →
    findminInPlace ops Rval Rind A init = .ok (values, indices) →
    ops.axesArray values = .ok axes →
    ops.axesArray indices = .ok axes
def FindInPlaceInitFalsePreservesExtremum (ops : Operations) : Prop :=
  (∀ {α : Type} (Rval : ops.Array α) (Rind : ops.Array ops.Index)
      (A : ops.Input α) values indices coordinate initial result,
    findminInPlace ops Rval Rind A false = .ok (values, indices) →
    ops.getArray Rval coordinate = .ok initial →
    ops.getArray values coordinate = .ok result →
    ops.applyPredicate ops.greater result initial = .ok false) ∧
  (∀ {α : Type} (Rval : ops.Array α) (Rind : ops.Array ops.Index)
      (A : ops.Input α) values indices coordinate initial result,
    findmaxInPlace ops Rval Rind A false = .ok (values, indices) →
    ops.getArray Rval coordinate = .ok initial →
    ops.getArray values coordinate = .ok result →
    ops.applyPredicate ops.less result initial = .ok false)

def FindInPlaceContract (ops : Operations) : Prop :=
  FindInPlaceReturnsAxes ops ∧ FindInPlaceReturnsArrays ops ∧
  FindInPlaceInitFalsePreservesExtremum ops

def CountReductionContract (ops : Operations) : Prop :=
  CountExact ops ∧ InPlaceReductionOutputs ops

def FindReductionContract (ops : Operations) : Prop :=
  FindDimsExact ops ∧ FindIdentityDimsExact ops ∧ FindDimsShapeExact ops ∧
  ArgFindDimsExact ops ∧ FindInPlaceContract ops

def FindIdentityContract (ops : Operations) : Prop :=
  FindIdentityDimsExact ops ∧ FindDimsShapeExact ops ∧
  ArgFindDimsExact ops ∧ FindInPlaceContract ops

def ReducedInitializationExact (ops : Operations) : Prop :=
  ReducedInitTypeExact ops ∧ PromoteUnionExact ops ∧
  MinMaxInitializationExact ops ∧ EmptyReductionIdentities ops ∧
  InPlaceReductionOutputs ops


/-! ## Nothing to promise

`copyfirst!@239`: copies the first slice through `mapfirst!`; its independent
observable behavior is covered by the reduction-kernel slice statement.
`reducedim!@298`: fixes `identity` before calling `mapreducedim!`.
`_mapreduce_dim@345-358`: dispatches the already specified scalar and dimensional
reduction methods, including the `ReshapedArray` parent path.
`_findmin@1117` and `_findmax@1190`: fix `identity` before the mapped find method.
`argmin@1263` and `argmax@1288`: return the index component of `findmin` and
`findmax`; the find-index statement covers their behavior.
-/

end JuliaLean.Proofs.base.reducedim


namespace JuliaLean.ChatGPT.Batch4.Group20

open JuliaLean
open JuliaLean.base.reducedim
open JuliaLean.Proofs.base.reducedim

/-- The argument-reduction wrappers return precisely the find-result indices. -/
theorem reducedim_argFindDimsExact (ops : Operations) : ArgFindDimsExact ops := by
  constructor
  · intro α A dims result indices hfind harg
    simp only [argmax, hfind, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at harg
    exact harg.symm
  · intro α A dims result indices hfind harg
    simp only [argmin, hfind, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at harg
    exact harg.symm

/-- Bounds/shape failures are propagated before the kernel accesses array data. -/
theorem reducedim_kernel_check_error (ops : Operations)
    {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (R : ops.Array β) (A : ops.Input α) error
    (h : check_reducedims ops R A = .error error) :
    _mapreducedim! (γ := γ) ops f op R A = .error error := by
  simp only [_mapreducedim!, h, bind, Except.bind]

/-- The error-propagation component of the kernel contract. -/
theorem reducedim_mapreducedimInPlaceContract (ops : Operations) :
    MapreducedimInPlaceContract ops := by
  intro α β γ f op R A error
  exact reducedim_kernel_check_error (γ := γ) ops f op R A error

/-- The first-slice wrapper really invokes the specified map operation. -/
theorem reducedim_mapfirstExact (ops : Operations) : MapfirstExact ops := by
  intro α β f R A result resultAxes inputAxes sliceAxes sourceSlice
    hmap hresultAxes hinputAxes hslice hview
  cases hcheck : check_reducedims ops R A with
  | error error =>
      simp only [mapfirst!, hcheck, bind, Except.bind,
        reduceCtorEq] at hmap
  | ok length =>
      simpa only [mapfirst!, hcheck, hresultAxes, hinputAxes, hslice,
        hview, bind, Except.bind] using hmap

/-- No initialization is needed for an empty scalar reduction with explicit init. -/
theorem reducedim_empty_scalar_explicit (ops : Operations)
    {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (initial : β) (A : ops.Input α)
    (hempty : ops.iterate A = .ok none) :
    _mapreduce_dim_colon_init (γ := γ) ops f op initial A = .ok initial := by
  simp only [_mapreduce_dim_colon_init, hempty, bind, Except.bind, pure,
    Except.pure]

/-- The kernel's empty-input branch preserves the output array. -/
theorem reducedim_empty_kernel (ops : Operations)
    {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (R : ops.Array β) (A : ops.Input α) length
    (hcheck : check_reducedims ops R A = .ok length)
    (hempty : ops.isEmptyInput A = .ok true) :
    _mapreducedim! (γ := γ) ops f op R A = .ok R := by
  simp only [_mapreducedim!, hcheck, hempty, bind, Except.bind,
    Bool.true_eq, ite_true, pure, Except.pure]

/-- Successful mapped extrema imply the corresponding identity-map property. -/
theorem reducedim_findIdentity_of_findDims (ops : Operations)
    (h : FindDimsExact ops) : FindIdentityDimsExact ops := by
  intro α A dims minimum maximum hmax hmin coordinate
  exact h ops.identity A dims minimum maximum hmax hmin coordinate

/-- The array-index component of the full find contract needs no interface laws. -/
theorem reducedim_findIdentityContract_of_components (ops : Operations)
    (hvalues : FindIdentityDimsExact ops) (hshape : FindDimsShapeExact ops)
    (hinplace : FindInPlaceContract ops) : FindIdentityContract ops := by
  exact ⟨hvalues, hshape, reducedim_argFindDimsExact ops, hinplace⟩

/-- The full mapped find contract follows from its genuinely semantic components. -/
theorem reducedim_findReductionContract_of_components (ops : Operations)
    (hvalues : FindDimsExact ops) (hshape : FindDimsShapeExact ops)
    (hinplace : FindInPlaceContract ops) : FindReductionContract ops := by
  exact ⟨hvalues, reducedim_findIdentity_of_findDims ops hvalues,
    hshape, reducedim_argFindDimsExact ops, hinplace⟩

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.Proofs.base.reducedim
open JuliaLean.Registry

def entries : List Entry := [
  { id := "reduce-sumdims-exact", juliaFile := "base/reducedim.jl",
    juliaFns := ["sum(A; dims)", "mapreducedim!", "reducedim_init"],
    statement := "sum(A; dims=1 or 2) over a BitInteger matrix has the reduced shape and returns exact slice sums in Julia's widened result type (Int/UInt for small inputs), including the pairwise path.",
    source := "base/reducedim.jl:464-510 (sum dimensions docstrings)",
    status := .todo, prop := ``SumDimsExact,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reduce-maxdims-int", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum(A; dims)", "minimum(A; dims)", "reducedim_init"],
    statement := "maximum/minimum(A; dims=1 or 2) on a nonempty Matrix{Int} has the reduced shape and equals maximum/minimum of each slice.",
    source := "base/reducedim.jl:613-743 (maximum/minimum dimensions docstrings)",
    status := .todo, prop := ``MaxMinDimsExact,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reduce-finddims-slices", juliaFile := "base/reducedim.jl",
    juliaFns := ["findmax(A; dims)", "findmin(A; dims)", "findminmax!"],
    statement := "findmax/findmin(A; dims=1 or 2) on a nonempty Matrix{Float64} returns each slice's extremal value and CartesianIndex.",
    source := "base/reducedim.jl:1096-1212 (findmin/findmax dimensions docstrings)",
    status := .todo, prop := ``FindIdentityContract,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reduce-any-dims-missing", juliaFile := "base/reducedim.jl",
    juliaFns := ["any(A; dims)", "all(A; dims)", "or_any", "and_all"],
    statement := "any(A; dims) returns any(slice) for each slice of a Bool-and-missing matrix, with the same three-valued behavior as any(A).",
    source := "base/reducedim.jl:841-988 (all/any dimensions docstrings)",
    status := .todo, prop := ``AnyAllDimsExact,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reduce-maxdims-union-eltype", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum(A; dims)", "minimum(A; dims)", "reducedim_init"],
    statement := "maximum(A; dims) succeeds on nonempty matrices of Int, Float64, or Union{Int, Float64}, and each output is the maximum of its slice.",
    source := "base/reducedim.jl:613-743 (maximum/minimum dimensions docstrings)",
    status := .todo, prop := ``MaxMinUnionDimsExact,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reduce-maxdims-all-missing", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum(A; dims)", "minimum(A; dims)", "reducedim_init"],
    statement := "maximum(A; dims) and minimum(A; dims) of a nonempty all-missing matrix return missing for every slice.",
    source := "base/reducedim.jl:613-743; base/missing.jl:129-137",
    status := .todo, prop := ``MaxMinAllMissingValues,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reduce-maxabs-dims-typemin", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum(f, A; dims)", "maximum(abs, A; dims)", "maximum(abs2, A; dims)", "reducedim_init"],
    statement := "maximum(abs, A; dims) on a nonempty Matrix{Int} equals maximum(abs, slice) for every slice.",
    source := "base/reducedim.jl:641-664 (maximum(f, A; dims) docstring)",
    status := .todo, prop := ``MaxMinFunctionDimsExact,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reduce-sumdims-init-narrow", juliaFile := "base/reducedim.jl",
    juliaFns := ["sum(A; dims, init)", "count(A; dims, init)", "mapreduce(f, op, A; dims, init)"],
    statement := "sum(A; dims, init=zero(S)) over a small-integer matrix equals sum(slice; init=zero(S)) for every slice.",
    source := "base/reducedim.jl:328-352,485-510; base/reduce.jl:546-557",
    status := .todo, prop := ``MapreduceDimsSliceValues,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reduce-finddims-empty-shape", juliaFile := "base/reducedim.jl",
    juliaFns := ["findmax(A; dims)", "findmin(A; dims)", "argmax(A; dims)", "argmin(A; dims)"],
    statement := "findmax(A; dims) returns value and index arrays with the same reduced shape as sum(A; dims), including singleton axes for selected dimensions.",
    source := "base/reducedim.jl:1096-1212 (findmin/findmax dimensions docstrings)",
    status := .todo, prop := ``FindDimsShapeExact,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },

  { id := "multidimcov-reducedim-repair-find", juliaFile := "base/reducedim.jl",
    juliaFns := ["findminmax!(f, op, Rval, Rind, A)", "findmin!", "findmax!", "findmin(A; dims)", "findmax(A; dims)", "findmin(f, A; dims)", "findmax(f, A; dims)", "argmin", "argmax"],
    statement := "Find reductions return a matching extremal input index per slice; their value and index arrays have the reduced shape, argmin/argmax return the matching index array, and in-place methods update both outputs.",
    source := "base/reducedim.jl:1032-1288 (find methods)",
    status := .todo, prop := ``FindReductionContract,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reducedim-count-contract", juliaFile := "base/reducedim.jl",
    juliaFns := ["count(A; dims)", "count(f, A; dims)", "_count", "count!(R, A)", "count!(f, R, A)"],
    statement := "Count returns true predicate totals over the input or each selected slice, and count! updates its supplied output array.",
    source := "base/reducedim.jl:397-461 (count docstring and methods)",
    status := .todo, prop := ``CountReductionContract,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reducedim-generated-wrappers", juliaFile := "base/reducedim.jl",
    juliaFns := ["mapreduce(f, op, A; dims)", "reduce(op, A; dims)", "sum(A; dims)", "sum(f, A; dims)", "prod(A; dims)", "prod(f, A; dims)", "maximum(A; dims)", "maximum(f, A; dims)", "minimum(A; dims)", "minimum(f, A; dims)", "extrema(A; dims)", "extrema(f, A; dims)", "all(A; dims)", "all(f, A; dims)", "any(A; dims)", "any(f, A; dims)", "sum!(f, R, A)", "prod!(f, R, A)", "maximum!(f, R, A)", "minimum!(f, R, A)", "extrema!(f, R, A)", "all!(f, R, A)", "any!(f, R, A)"],
    statement := "Dimensional wrappers return the full reduction of each corresponding slice with reduced axes, honor initial and empty-input behavior, propagate NaN for maximum/minimum, and update the supplied array in in-place forms.",
    source := "base/reducedim.jl:328-392,485-1027 (reduction methods and generated wrappers)",
    status := .todo, prop := ``GeneratedReductionContract,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reducecov-maximum-inplace-empty", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum!", "maximum!(f, r, A)", "minimum!", "minimum!(f, r, A)", "extrema!", "extrema!(f, r, A)"],
    statement := "In-place maximum, minimum, and extrema throw when the output axes describe a selected empty slice.",
    source := "base/reducedim.jl:89-128,1020-1022 (extrema initialization and in-place wrappers)",
    status := .todo, prop := ``InPlaceMaxMinEmptySliceErrorClaim,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
  { id := "reducecov-findmax-inplace-init", juliaFile := "base/reducedim.jl",
    juliaFns := ["findmin!", "findmax!"],
    statement := "With init=false, an existing in-place find value remains a bound on the result; findmin! cannot return a larger value and findmax! cannot return a smaller value.",
    source := "base/reducedim.jl:1091-1094,1164-1167 (find in-place methods)",
    status := .todo, prop := ``FindInPlaceContract,
    notes := "The registered constant has type Operations → Prop, with no concrete Operations binding in the frozen target." },
]

end JuliaLean.Proofs.base.reducedim

namespace JuliaLean.ChatGPT.Batch8.Group11

open JuliaLean
open JuliaLean.base.reducedim
open JuliaLean.Proofs.base.reducedim

/-- The wrapper is the kernel. -/
theorem reducedim_wrapper_success_iff (ops : Operations)
    {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (R : ops.Array β) (A : ops.Input α) (result : ops.Array β) :
    mapreducedim! (γ := γ) ops f op R A = .ok result ↔
      _mapreducedim! (γ := γ) ops f op R A = .ok result :=
  Iff.rfl

/-- Exact successful-path decomposition of explicit dimensional initialization. -/
theorem reducedim_explicit_success_iff (ops : Operations)
    {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (initialValue : β) (A : ops.Input α) (dims : ops.Region)
    (result : ops.Array β) :
    _mapreduce_dim_dims_init (γ := γ) ops f op initialValue A dims = .ok result ↔
      ∃ initial,
        reducedim_initarray ops A dims initialValue = .ok initial ∧
        _mapreducedim! (γ := γ) ops f op initial A = .ok result := by
  constructor
  · intro h
    cases hinit : reducedim_initarray ops A dims initialValue with
    | error error =>
        simp only [_mapreduce_dim_dims_init, hinit, bind, Except.bind,
          reduceCtorEq] at h
    | ok initial =>
        exact ⟨initial, rfl, by
          simpa only [_mapreduce_dim_dims_init, hinit, bind, Except.bind,
            mapreducedim!] using h⟩
  · rintro ⟨initial, hinit, hupdated⟩
    simp only [_mapreduce_dim_dims_init, hinit, bind, Except.bind,
      mapreducedim!, hupdated]

/-- Exact successful-path decomposition of implicit dimensional initialization. -/
theorem reducedim_implicit_success_iff (ops : Operations)
    {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (A : ops.Input α) (dims : ops.Region) (result : ops.Array β) :
    _mapreduce_dim_dims_implicit (γ := γ) ops f op A dims = .ok result ↔
      ∃ initial,
        reducedim_init_dispatch (γ := γ) ops f op A dims = .ok initial ∧
        _mapreducedim! (γ := γ) ops f op initial A = .ok result := by
  constructor
  · intro h
    cases hinit : reducedim_init_dispatch (β := β) (γ := γ) ops f op A dims with
    | error error =>
        simp only [_mapreduce_dim_dims_implicit, hinit, bind, Except.bind,
          reduceCtorEq] at h
    | ok initial =>
        exact ⟨initial, rfl, by
          simpa only [_mapreduce_dim_dims_implicit, hinit, bind, Except.bind,
            mapreducedim!] using h⟩
  · rintro ⟨initial, hinit, hupdated⟩
    simp only [_mapreduce_dim_dims_implicit, hinit, bind, Except.bind,
      mapreducedim!, hupdated]

/-- The two axis reducers agree when every source axis is nonempty.
This isolates the extra condition needed to transfer ordinary reduced-shape
lemmas to the find-reduction allocation path. -/
theorem reducedim_nonempty_axes_loops_agree (ops : Operations)
    (region : ops.Region) (axes : List ops.Axis) (dim : Nat)
    (hne : ∀ axis, axis ∈ axes → ops.axisEmpty axis = false) :
    reducedIndicesLoop0 ops region dim axes =
      reducedIndicesLoop ops region dim axes := by
  induction axes generalizing dim with
  | nil => rfl
  | cons axis axes ih =>
      have ha : ops.axisEmpty axis = false := hne axis (by simp only [List.mem_cons_self])
      have ht : ∀ item, item ∈ axes → ops.axisEmpty item = false := by
        intro item hitem
        exact hne item (List.mem_cons_of_mem axis hitem)
      simp only [reducedIndicesLoop0, reducedIndicesLoop, ha,
        Bool.not_false, Bool.and_true, ih (dim + 1) ht]

/-- Input-level consequence of nonempty-axis agreement. -/
theorem reducedim_nonempty_input_axes_agree (ops : Operations)
    {α : Type} (A : ops.Input α) (region : ops.Region) (axes : List ops.Axis)
    (haxes : ops.axesInput A = .ok axes)
    (hne : ∀ axis, axis ∈ axes → ops.axisEmpty axis = false) :
    reduced_indices0_input ops A region = reduced_indices_input ops A region := by
  simp only [reduced_indices0_input, reduced_indices_input, haxes,
    bind, Except.bind, reduced_indices0_axes, reduced_indices_axes,
    reducedim_nonempty_axes_loops_agree ops region axes 0 hne]

end JuliaLean.ChatGPT.Batch8.Group11


namespace JuliaLean.ChatGPT.Batch8.Group12

open JuliaLean JuliaLean.base.reducedim JuliaLean.Proofs.base.reducedim

/-- Invalid dimensions fail before the axis-reduction loop. -/
theorem reducedim_invalidRegionAxes (ops : Operations) (axes : List ops.Axis)
    (region : ops.Region) (failure : JuliaLean.base.abstractarray.ArrayError)
    (h : check_valid_region ops region = .error failure) :
    reduced_indices_axes ops axes region = .error failure := by
  simp only [reduced_indices_axes, h, bind, Except.bind]

/-- The input wrapper preserves the dimension-validation error after reading axes. -/
theorem reducedim_invalidRegionInput (ops : Operations) {α : Type}
    (A : ops.Input α) (region : ops.Region) (axes : List ops.Axis)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (ha : ops.axesInput A = .ok axes)
    (hv : check_valid_region ops region = .error failure) :
    reduced_indices_input ops A region = .error failure := by
  simp only [reduced_indices_input, ha, bind, Except.bind,
    reduced_indices_axes, hv]

/-- A failed reduced-axis computation precedes every min/max seed operation. -/
theorem reducedim_minMaxIndicesFailure (ops : Operations) {α β : Type}
    (isMax : Bool) (f : ops.Function) (A : ops.Input α) (region : ops.Region)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (h : reduced_indices_input ops A region = .error failure) :
    reducedimInitMinMax (β := β) ops isMax f A region = .error failure := by
  simp only [reducedimInitMinMax, h, bind, Except.bind]

/-- A selected empty slice fails when the empty-reduction callback raises an error. -/
theorem reducedim_minMaxEmptyFailure (ops : Operations) {α β : Type}
    (isMax : Bool) (f : ops.Function) (A : ops.Input α) (region : ops.Region)
    (axes : List ops.Axis) (failure : JuliaLean.base.abstractarray.ArrayError)
    (ha : reduced_indices_input ops A region = .ok axes)
    (he : hasEmptyRegionAxis ops A (ops.regionItems region) = .ok true)
    (hf : ops.emptyReduce (α := Unit) = .error failure) :
    reducedimInitMinMax (β := β) ops isMax f A region = .error failure := by
  simp only [reducedimInitMinMax, ha, he, hf, bind, Except.bind,
    ite_true]

/-- A nonnumeric unordered first-slice seed is retained if the slice is all unordered. -/
theorem reducedim_allUnorderedSeed (ops : Operations) {α β : Type}
    (isMax : Bool) (f : ops.Function) (A slice : ops.Input α)
    (region : ops.Region) (axes : List ops.Axis) (seed : β) (promoted : TypeTag)
    (ha : reduced_indices_input ops A region = .ok axes)
    (he : hasEmptyRegionAxis ops A (ops.regionItems region) = .ok false)
    (hv : ops.view A axes = .ok slice)
    (hn : ops.isEmptyInput slice = .ok false)
    (hs : mapreduceNoInit ops f (if isMax then ops.minimum else ops.maximum) slice =
      .ok seed)
    (hp : promote_union ops (ops.elementType A) = .ok promoted)
    (hnum : ops.isNumber seed = false)
    (hu : ops.isUnordered seed = true)
    (hm : ops.machineNumericType (ops.nonmissingType
      (if ops.isInstance seed (realtype ops f promoted) then realtype ops f promoted
       else ops.valueTypeOf seed)) = false)
    (hall : ops.allUnordered slice = .ok true) :
    reducedimInitMinMax ops isMax f A region =
      reducedim_initarray_type ops A region seed
        (if ops.isInstance seed (realtype ops f promoted) then realtype ops f promoted
         else ops.valueTypeOf seed) := by
  simp only [reducedimInitMinMax, ha, he, hv, hn, hs, hp, hnum, hu, hm, hall,
    bind, Except.bind, pure, Except.pure, Bool.false_and, Bool.false_eq_true,
    ite_false, ite_true]

/-- A min/max first-slice view failure propagates through initialization. -/
theorem reducedim_mapfirstViewFailure (ops : Operations) {α β : Type}
    (f : ops.Function) (R : ops.Array β) (A : ops.Input α)
    (outputAxes inputAxes sliceAxes : List ops.Axis) (length : I64)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (hc : check_reducedims ops R A = .ok length)
    (hr : ops.axesArray R = .ok outputAxes)
    (ha : ops.axesInput A = .ok inputAxes)
    (hs : firstReducedSlice ops outputAxes inputAxes = .ok sliceAxes)
    (hv : ops.view A sliceAxes = .error failure) :
    mapfirst! ops f R A = .error failure := by
  simp only [mapfirst!, hc, hr, ha, hs, hv, bind, Except.bind]

/-- The min/max initializer exposes exactly the first-slice error. -/
theorem reducedim_initMinMaxFailure (ops : Operations) {α β : Type}
    (f : ops.Function) (R : ops.Array β) (A : ops.Input α)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (h : mapfirst! ops f R A = .error failure) :
    initarray_minmax (F := ops.Function) ops R f A true = .error failure := by
  simp only [initarray_minmax, ite_true, h]

/-- Successful validation supplies both integer typing and a positive converted dimension. -/
theorem reducedim_validRegionLoopMember (ops : Operations)
    (dimensions : List ops.Dimension)
    (h : checkValidRegionLoop ops dimensions = .ok ()) :
    ∀ dimension ∈ dimensions, ops.isInteger dimension = true ∧
      ∃ value, ops.toInt dimension = .ok value ∧ value.val ≥ 1 := by
  induction dimensions with
  | nil =>
      intro dimension hmem
      cases hmem
  | cons d ds ih =>
      cases hint : ops.isInteger d with
      | false =>
          simp only [checkValidRegionLoop, hint, Bool.not_false,             ite_true, bind, Except.bind, reduceCtorEq] at h
      | true =>
          cases hval : ops.toInt d with
          | error failure =>
              simp only [checkValidRegionLoop, hint, Bool.not_true,
                Bool.false_eq_true, ite_false, hval, bind, Except.bind,
                reduceCtorEq] at h
          | ok value =>
              by_cases hbad : value.val < 1
              · simp only [checkValidRegionLoop, hint, Bool.not_true,
                  Bool.false_eq_true, ite_false, hval, bind, Except.bind,
                  hbad, ite_true, reduceCtorEq] at h
              · have htail : checkValidRegionLoop ops ds = .ok () := by
                  simpa only [checkValidRegionLoop, hint, Bool.not_true,
                    Bool.false_eq_true, ite_false, hval, bind, Except.bind,
                    hbad] using h
                intro dimension hmem
                rcases List.mem_cons.mp hmem with hd | ht
                · subst dimension
                  exact ⟨hint, value, hval, by omega⟩
                · exact ih htail dimension ht

/-- The positive-dimension consequence holds for every operation interface. -/
theorem reducedim_validRegionApplied (ops : Operations) : ValidRegionExact ops := by
  intro region h dimensions hdim dimension hmem _
  subst dimensions
  exact (reducedim_validRegionLoopMember ops (ops.regionItems region) h dimension hmem).2

/-- The maximum wrapper propagates a first-slice initialization failure. -/
theorem reducedim_maximumFirstSliceFailure (ops : Operations) {α β γ : Type}
    (f : ops.Function) (R : ops.Array β) (A : ops.Input α)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (hk : ops.operatorKind ops.maximum = "max")
    (hf : mapfirst! ops f R A = .error failure) :
    maximumInPlace (γ := γ) ops f R A true = .error failure := by
  simp only [maximumInPlace, initarray!, hk, initarray_minmax,     ite_true, hf, bind, Except.bind]

/-- The minimum wrapper propagates a first-slice initialization failure. -/
theorem reducedim_minimumFirstSliceFailure (ops : Operations) {α β γ : Type}
    (f : ops.Function) (R : ops.Array β) (A : ops.Input α)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (hk : ops.operatorKind ops.minimum = "min")
    (hf : mapfirst! ops f R A = .error failure) :
    minimumInPlace (γ := γ) ops f R A true = .error failure := by
  simp only [minimumInPlace, initarray!, hk, initarray_minmax,     ite_true, hf, bind, Except.bind]

/-- The extrema wrapper propagates a failure for its mapped first-slice initializer. -/
theorem reducedim_extremaFirstSliceFailure (ops : Operations) {α β γ : Type}
    (f : ops.Function) (R : ops.Array β) (A : ops.Input α)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (hk : ops.operatorKind ops.extremaRF = "extrema")
    (hf : mapfirst! ops (ops.makeExtremaMap f) R A = .error failure) :
    extremaInPlace (γ := γ) ops f R A true = .error failure := by
  simp only [extremaInPlace, initarray!, hk, initarray_minmax,     ite_true, hf, bind, Except.bind]

/-- This explicit shape/view law is a sufficient source-dependent obligation
for the in-place selected-empty-slice claim. -/
def EmptySliceFirstMapFails (ops : Operations) : Prop :=
  ∀ {α β : Type} (f : ops.Function) (R : ops.Array β) (A : ops.Input α)
      outputAxes region reducedAxes,
    ops.axesArray R = .ok outputAxes →
    reduced_indices_input ops A region = .ok reducedAxes →
    ops.axesEqual outputAxes reducedAxes = true →
    hasEmptyRegionAxis ops A (ops.regionItems region) = .ok true →
    ∃ failure, mapfirst! ops f R A = .error failure

/-- The full applied empty-slice error claim follows from the first-slice law
and faithful operator dispatch, with no change to the frozen property. -/
theorem reducedim_inPlaceEmptyClaim_of_firstMap (ops : Operations)
    (hkmax : ops.operatorKind ops.maximum = "max")
    (hkmin : ops.operatorKind ops.minimum = "min")
    (hkextrema : ops.operatorKind ops.extremaRF = "extrema")
    (hfirst : EmptySliceFirstMapFails ops) :
    InPlaceMaxMinEmptySliceErrorClaim ops := by
  intro α β γ f R A outputAxes region reducedAxes hr ha heq hempty
  obtain ⟨failure, hf⟩ := hfirst f R A outputAxes region reducedAxes hr ha heq hempty
  obtain ⟨mappedFailure, hmapped⟩ := hfirst (ops.makeExtremaMap f)
    R A outputAxes region reducedAxes hr ha heq hempty
  exact ⟨⟨failure, reducedim_maximumFirstSliceFailure (γ := γ) ops f R A
      failure hkmax hf⟩,
    ⟨failure, reducedim_minimumFirstSliceFailure (γ := γ) ops f R A
      failure hkmin hf⟩,
    ⟨mappedFailure, reducedim_extremaFirstSliceFailure (γ := γ) ops f R A
      mappedFailure hkextrema hmapped⟩⟩

/-- A failed extremal replacement of an unordered seed propagates from the
initializer. This is the branch exercised by the all-Missing Julia example. -/
theorem reducedim_unorderedExtremeFailure (ops : Operations) {α β : Type}
    (isMax : Bool) (f : ops.Function) (A slice : ops.Input α)
    (region : ops.Region) (axes : List ops.Axis) (seed : β) (promoted : TypeTag)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (ha : reduced_indices_input ops A region = .ok axes)
    (he : hasEmptyRegionAxis ops A (ops.regionItems region) = .ok false)
    (hv : ops.view A axes = .ok slice)
    (hn : ops.isEmptyInput slice = .ok false)
    (hs : mapreduceNoInit ops f (if isMax then ops.minimum else ops.maximum) slice =
      .ok seed)
    (hp : promote_union ops (ops.elementType A) = .ok promoted)
    (hnum : ops.isNumber seed = false)
    (hu : ops.isUnordered seed = true)
    (hm : ops.machineNumericType (ops.nonmissingType
      (if ops.isInstance seed (realtype ops f promoted) then realtype ops f promoted
       else ops.valueTypeOf seed)) = true)
    (hf : ops.typeExtreme (α := β) (ops.nonmissingType
      (if ops.isInstance seed (realtype ops f promoted) then realtype ops f promoted
       else ops.valueTypeOf seed)) (!isMax) = .error failure) :
    reducedimInitMinMax (β := β) ops isMax f A region = .error failure := by
  simp only [reducedimInitMinMax, ha, he, hv, hn, hs, hp, hnum, hu, hm, hf,
    bind, Except.bind, pure, Except.pure, Bool.false_and, Bool.false_eq_true,
    ite_false, ite_true]

/-- A constructible witness still needs failure for every permitted result type
before it can negate the applied all-missing family. -/
theorem reducedim_allMissing_obstruction (ops : Operations) {α : Type}
    (A : ops.Input α) (dims : ops.Region)
    (hn : ops.isEmptyInput A = .ok false)
    (hd : ops.isColon dims = false)
    (hm : AllInputMissing ops A)
    (hf : ∀ (β : Type), ∃ failure,
      maximum (β := β) ops A dims .implicit = .error failure) :
    ¬ MaxMinAllMissingValues ops := by
  intro h
  obtain ⟨βmax, Rmax, βmin, Rmin, hmax, _⟩ := h A dims hn hd hm
  obtain ⟨failure, hfail⟩ := hf βmax
  rw [hfail] at hmax
  cases hmax

end JuliaLean.ChatGPT.Batch8.Group12

namespace JuliaLean.ChatGPT.Batch8.Group12

open JuliaLean JuliaLean.base.reducedim JuliaLean.Proofs.base.reducedim

/-- Disabling value initialization still initializes the index buffer. -/
theorem findmin_false_dispatch (ops : Operations) {α : Type}
    (Rval : ops.Array α) (Rind zeroed : ops.Array ops.Index) (A : ops.Input α)
    (empty : Bool) (zeroIndex : ops.Index)
    (hempty : ops.isEmptyInput A = .ok empty)
    (hzero : ops.indexZero A = .ok zeroIndex)
    (hfill : ops.fill Rind zeroIndex = .ok zeroed) :
    findminInPlace ops Rval Rind A false =
      findminmax! ops ops.identity ops.greater Rval zeroed A := by
  simp only [findminInPlace, hempty, hzero, hfill, bind, Except.bind,
    pure, Except.pure, Bool.false_and, Bool.false_eq_true, ite_false]

/-- The maximum wrapper also resets its index buffer when value init is false. -/
theorem findmax_false_dispatch (ops : Operations) {α : Type}
    (Rval : ops.Array α) (Rind zeroed : ops.Array ops.Index) (A : ops.Input α)
    (empty : Bool) (zeroIndex : ops.Index)
    (hempty : ops.isEmptyInput A = .ok empty)
    (hzero : ops.indexZero A = .ok zeroIndex)
    (hfill : ops.fill Rind zeroIndex = .ok zeroed) :
    findmaxInPlace ops Rval Rind A false =
      findminmax! ops ops.identity ops.less Rval zeroed A := by
  simp only [findmaxInPlace, hempty, hzero, hfill, bind, Except.bind,
    pure, Except.pure, Bool.false_and, Bool.false_eq_true, ite_false]

/-- A zero index causes the first-axis kernel to replace the old value,
regardless of the successful comparison's Boolean answer. -/
theorem find_axis_first_zero_replaces (ops : Operations) {α β : Type}
    (f : ops.Function) (op : ops.Operator) (zeroIndex index key i : ops.Index)
    (A : ops.Input α) (outer remaining rest : List ops.Index)
    (initial mapped : β) (input : α) (comparison : Bool)
    (hget : ops.getInput A (i :: outer) = .ok input)
    (hmap : ops.applyFunction (F := ops.Function) (α := α) (β := β) f input =
      .ok mapped)
    (hindex : ops.indexEqual index zeroIndex = true)
    (hcompare : ops.applyPredicate (O := ops.Operator) (A := β) (B := β)
      op initial mapped = .ok comparison) :
    findMinMaxAxisFirst ops f op zeroIndex A outer (key :: remaining) (i :: rest)
      initial index =
    findMinMaxAxisFirst ops f op zeroIndex A outer remaining rest mapped key := by
  rw [findMinMaxAxisFirst]
  simp only [hget, hmap, hindex, hcompare, bind, Except.bind,
    Bool.true_or, ite_true]

/-- A singleton slice with a reset index returns its mapped input, not an old bound. -/
theorem find_axis_first_singleton_zero (ops : Operations) {α β : Type}
    (f : ops.Function) (op : ops.Operator) (zeroIndex index key i : ops.Index)
    (A : ops.Input α) (outer remaining : List ops.Index)
    (initial mapped : β) (input : α) (comparison : Bool)
    (hget : ops.getInput A (i :: outer) = .ok input)
    (hmap : ops.applyFunction (F := ops.Function) (α := α) (β := β) f input =
      .ok mapped)
    (hindex : ops.indexEqual index zeroIndex = true)
    (hcompare : ops.applyPredicate (O := ops.Operator) (A := β) (B := β)
      op initial mapped = .ok comparison) :
    findMinMaxAxisFirst ops f op zeroIndex A outer (key :: remaining) [i]
      initial index = .ok (mapped, key, remaining) := by
  rw [find_axis_first_zero_replaces ops f op zeroIndex index key i A outer
    remaining [] initial mapped input comparison hget hmap hindex hcompare]
  simp only [findMinMaxAxisFirst, pure, Except.pure]

/-- Returning the same pure array forces the before/after reads to agree. -/
theorem find_same_array_same_read (ops : Operations) {α : Type}
    (before after : ops.Array α) (coordinate : List ops.Index) (initial result : α)
    (harray : after = before)
    (hbefore : ops.getArray before coordinate = .ok initial)
    (hafter : ops.getArray after coordinate = .ok result) : result = initial := by
  rw [harray, hbefore] at hafter
  exact (Except.ok.inj hafter).symm

/-- The bound clause follows formally from array-value equality and irreflexive
comparisons; this exposes the additional laws absent from the frozen family. -/
theorem find_init_false_bound_of_return_identity (ops : Operations)
    (hreturns : FindInPlaceReturnsArrays ops)
    (hgreater : ∀ {α : Type} (x : α),
      ops.applyPredicate (O := ops.Operator) (A := α) (B := α)
        ops.greater x x = .ok false)
    (hless : ∀ {α : Type} (x : α),
      ops.applyPredicate (O := ops.Operator) (A := α) (B := α)
        ops.less x x = .ok false) :
    FindInPlaceInitFalsePreservesExtremum ops := by
  constructor
  · intro α Rval Rind A values indices coordinate initial result hfind hbefore hafter
    have harray := (hreturns.1 Rval Rind A false values indices hfind).1
    have hread := find_same_array_same_read ops Rval values coordinate initial result
      harray hbefore hafter
    rw [hread]
    exact hgreater initial
  · intro α Rval Rind A values indices coordinate initial result hfind hbefore hafter
    have harray := (hreturns.2 Rval Rind A false values indices hfind).1
    have hread := find_same_array_same_read ops Rval values coordinate initial result
      harray hbefore hafter
    rw [hread]
    exact hless initial

/-- Every applied full contract already includes the identity-map contract. -/
theorem find_identity_contract_of_full (ops : Operations)
    (h : FindReductionContract ops) : FindIdentityContract ops := by
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- A successful first-axis pass preserves any value/index invariant that holds
initially and for the mapped inputs paired with the traversed keys. -/
theorem find_axis_first_invariant (ops : Operations) {α β : Type}
    (f : ops.Function) (op : ops.Operator) (zeroIndex : ops.Index)
    (A : ops.Input α) (outer : List ops.Index) (P : β → ops.Index → Prop)
    (axis keys : List ops.Index) (initial : β) (initialIndex : ops.Index)
    (value : β) (index : ops.Index) (remaining : List ops.Index)
    (hlen : axis.length ≤ keys.length)
    (hinitial : P initial initialIndex)
    (hmapped : ∀ i key input mapped,
      (i, key) ∈ axis.zip keys →
      ops.getInput A (i :: outer) = .ok input →
      ops.applyFunction (F := ops.Function) (α := α) (β := β) f input = .ok mapped →
      P mapped key)
    (hresult : findMinMaxAxisFirst ops f op zeroIndex A outer keys axis
      initial initialIndex = .ok (value, index, remaining)) : P value index := by
  induction axis generalizing keys initial initialIndex with
  | nil =>
      simp only [findMinMaxAxisFirst, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at hresult
      rcases hresult with ⟨hvalue, hindex, hkeys⟩
      rw [← hvalue, ← hindex]
      exact hinitial
  | cons i rest ih =>
      cases keys with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen
          omega
      | cons key tail =>
          have htail : rest.length ≤ tail.length := by
            simp only [List.length_cons] at hlen
            omega
          have htailMapped : ∀ j k input mapped,
              (j, k) ∈ rest.zip tail →
              ops.getInput A (j :: outer) = .ok input →
              ops.applyFunction (F := ops.Function) (α := α) (β := β) f input =
                .ok mapped → P mapped k := by
            intro j k input mapped hmem hget hmap
            exact hmapped j k input mapped (List.mem_cons_of_mem (i, key) hmem)
              hget hmap
          rw [findMinMaxAxisFirst] at hresult
          cases hget : ops.getInput A (i :: outer) with
          | error failure =>
              simp only [hget, bind, Except.bind,
                reduceCtorEq] at hresult
          | ok input =>
              cases hmap : ops.applyFunction (F := ops.Function) (α := α)
                  (β := β) f input with
              | error failure =>
                  simp only [hget, hmap, bind, Except.bind,
                    reduceCtorEq] at hresult
              | ok mapped =>
                  cases hcompare : ops.applyPredicate (O := ops.Operator)
                      (A := β) (B := β) op initial mapped with
                  | error failure =>
                      simp only [hget, hmap, hcompare,
                        bind, Except.bind, reduceCtorEq] at hresult
                  | ok comparison =>
                      by_cases hreplace :
                          (ops.indexEqual initialIndex zeroIndex || comparison) = true
                      · have hnew : P mapped key :=
                          hmapped i key input mapped
                            List.mem_cons_self hget hmap
                        have hrec : findMinMaxAxisFirst ops f op zeroIndex A outer
                            tail rest mapped key = .ok (value, index, remaining) := by
                          simpa only [hget, hmap, hcompare,
                            bind, Except.bind, hreplace, ite_true] using hresult
                        exact ih tail mapped key htail hnew htailMapped hrec
                      · have hrec : findMinMaxAxisFirst ops f op zeroIndex A outer
                            tail rest initial initialIndex =
                              .ok (value, index, remaining) := by
                          simpa only [hget, hmap, hcompare,
                            bind, Except.bind, hreplace, Bool.false_eq_true, ite_false] using hresult
                        exact ih tail initial initialIndex htail hinitial htailMapped hrec

/-- Once the first zero-index entry is initialized, a successful nonempty
first-axis pass returns a value and key taken together from a traversed input. -/
theorem find_axis_first_has_source (ops : Operations) {α β : Type}
    (f : ops.Function) (op : ops.Operator) (zeroIndex initialIndex firstKey firstAxis : ops.Index)
    (A : ops.Input α) (outer tail axisTail : List ops.Index)
    (initial firstMapped value : β) (firstInput : α) (comparison : Bool)
    (index : ops.Index) (remaining : List ops.Index)
    (hlen : axisTail.length ≤ tail.length)
    (hget : ops.getInput A (firstAxis :: outer) = .ok firstInput)
    (hmap : ops.applyFunction (F := ops.Function) (α := α) (β := β) f firstInput =
      .ok firstMapped)
    (hindex : ops.indexEqual initialIndex zeroIndex = true)
    (hcompare : ops.applyPredicate (O := ops.Operator) (A := β) (B := β)
      op initial firstMapped = .ok comparison)
    (hresult : findMinMaxAxisFirst ops f op zeroIndex A outer
      (firstKey :: tail) (firstAxis :: axisTail) initial initialIndex =
        .ok (value, index, remaining)) :
    ∃ i input,
      (i, index) ∈ (firstAxis :: axisTail).zip (firstKey :: tail) ∧
      ops.getInput A (i :: outer) = .ok input ∧
      ops.applyFunction (F := ops.Function) (α := α) (β := β) f input = .ok value := by
  let P : β → ops.Index → Prop := fun result key =>
    ∃ i input,
      (i, key) ∈ (firstAxis :: axisTail).zip (firstKey :: tail) ∧
      ops.getInput A (i :: outer) = .ok input ∧
      ops.applyFunction (F := ops.Function) (α := α) (β := β) f input = .ok result
  have hstart : P firstMapped firstKey :=
    ⟨firstAxis, firstInput,
      List.mem_cons_self, hget, hmap⟩
  have hnext : findMinMaxAxisFirst ops f op zeroIndex A outer tail axisTail
      firstMapped firstKey = .ok (value, index, remaining) := by
    rw [find_axis_first_zero_replaces ops f op zeroIndex initialIndex firstKey firstAxis
      A outer tail axisTail initial firstMapped firstInput comparison
      hget hmap hindex hcompare] at hresult
    exact hresult
  exact find_axis_first_invariant ops f op zeroIndex A outer P axisTail tail
    firstMapped firstKey value index remaining hlen hstart
    (by
      intro i key input mapped hmem hread hfun
      exact ⟨i, input, List.mem_cons_of_mem (firstAxis, firstKey) hmem, hread, hfun⟩)
    hnext

/-- The two reduced-axis loops agree when every input axis is nonempty. -/
theorem find_reduced_axis_loops_nonempty (ops : Operations)
    (region : ops.Region) (dim : Nat) (axes : List ops.Axis)
    (hnonempty : ∀ axis, axis ∈ axes → ops.axisEmpty axis = false) :
    reducedIndicesLoop0 ops region dim axes = reducedIndicesLoop ops region dim axes := by
  induction axes generalizing dim with
  | nil => rfl
  | cons axis rest ih =>
      have hhead : ops.axisEmpty axis = false :=
        hnonempty axis List.mem_cons_self
      have hrest : ∀ a, a ∈ rest → ops.axisEmpty a = false :=
        fun a ha => hnonempty a (List.mem_cons_of_mem axis ha)
      simp only [reducedIndicesLoop0, reducedIndicesLoop, hhead,
        Bool.not_false, Bool.and_true, ih (dim + 1) hrest]

/-- On nonempty input axes, the find allocation shape equals the ordinary
reduction shape, including any shared region-validation failure. -/
theorem find_reduced_axes_nonempty (ops : Operations)
    (region : ops.Region) (axes : List ops.Axis)
    (hnonempty : ∀ axis, axis ∈ axes → ops.axisEmpty axis = false) :
    reduced_indices0_axes ops axes region = reduced_indices_axes ops axes region := by
  simp only [reduced_indices0_axes, reduced_indices_axes,
    find_reduced_axis_loops_nonempty ops region 0 axes hnonempty]

end JuliaLean.ChatGPT.Batch8.Group12

namespace JuliaLean.ChatGPT.Batch8.Group12

open JuliaLean JuliaLean.base.reducedim JuliaLean.Proofs.base.reducedim

/-- With a recognized colon, counting dispatches to its scalar callback. -/
theorem countColon_dispatch (ops : Operations) {α β : Type}
    (f : ops.Function) (A : ops.Input α) (initial : β)
    (hcolon : ops.isColon ops.colonRegion = true) :
    count_function ops f A ops.colonRegion initial =
      (ops.simpleCount f A initial).map ReducedResult.scalar := by
  cases hcount : ops.simpleCount f A initial with
  | error e =>
      simp only [count_function, _count, hcolon, Bool.true_eq, ite_true,
        _count_colon, hcount, bind, Except.bind, Except.map]
  | ok value =>
      simp only [count_function, _count, hcolon, Bool.true_eq, ite_true,
        _count_colon, hcount, bind, Except.bind, pure, Except.pure, Except.map]

/-- The scalar contract is exactly the missing success law for `simpleCount`. -/
theorem countColonExact_iff_callback (ops : Operations)
    (hcolon : ops.isColon ops.colonRegion = true) :
    CountColonExact ops ↔
      (∀ {α β : Type} (f : ops.Function) (A : ops.Input α)
        (initial expected : β),
        countExpected ops f A initial = .ok expected →
        ops.simpleCount f A initial = .ok expected) := by
  constructor
  · intro h α β f A initial expected hexpected
    have hresult := h f A initial expected hexpected
    rw [countColon_dispatch ops f A initial hcolon] at hresult
    cases hcount : ops.simpleCount f A initial with
    | error e =>
        simp only [hcount, Except.map, reduceCtorEq] at hresult
    | ok value =>
        simp only [hcount, Except.map, Except.ok.injEq,
          ReducedResult.scalar.injEq] at hresult
        cases hresult
        rfl
  · intro h α β f A initial expected hexpected
    rw [countColon_dispatch ops f A initial hcolon,
      h f A initial expected hexpected]
    rfl

/-- On dimensional input, count uses the Boolean-map reduction without alteration. -/
theorem countDims_dispatch (ops : Operations) {α β : Type}
    (f : ops.Function) (A : ops.Input α) (dims : ops.Region) (initial : β)
    (hcolon : ops.isColon dims = false) :
    count_function ops f A dims initial =
      mapreduce (γ := Bool) ops (ops.boolFunction f) ops.addSum A dims
        (.explicit initial) := by
  cases hresult : _mapreduce_dim_dims_init (γ := Bool) ops
      (ops.boolFunction f) ops.addSum initial A dims with
  | error e =>
      simp only [count_function, _count, hcolon, Bool.false_eq_true, ite_false,
        _count_dims, mapreduce, hresult, bind, Except.bind]
  | ok R =>
      simp only [count_function, _count, hcolon, Bool.false_eq_true, ite_false,
        _count_dims, mapreduce, hresult, bind, Except.bind, pure, Except.pure]

/-- The Boolean specialization of the dimensional count claim follows from the
corresponding map-reduction slice law. -/
theorem countDims_boolean_slice (ops : Operations)
    (hslices : MapreduceDimsSliceValues ops)
    {α β : Type} (f : ops.Function) (A : ops.Input α) (dims : ops.Region)
    (initial : β) (R : ops.Array β) (coordinate : List ops.Index) (value : β)
    (hcolon : ops.isColon dims = false)
    (hcount : count_function ops f A dims initial = .ok (.array R))
    (hvalue : ops.getArray R coordinate = .ok value) :
    reductionSliceValue (γ := Bool) ops (ops.boolFunction f) ops.addSum
      (.explicit initial) A dims coordinate = .ok value := by
  rw [countDims_dispatch ops f A dims initial hcolon] at hcount
  exact hslices (γ := Bool) (ops.boolFunction f) ops.addSum A dims
    (.explicit initial) R coordinate value hcolon hcount hvalue

/-- The frozen dimensional contract also quantifies over an arbitrary mapped type;
this explicit coherence premise identifies that extra obligation. -/
theorem countDimsExact_of_slice_coherence (ops : Operations)
    (hslices : MapreduceDimsSliceValues ops)
    (hcoherent : ∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
      (dims : ops.Region) (initial : β) (coordinate : List ops.Index),
      reductionSliceValue (γ := γ) ops (ops.boolFunction f) ops.addSum
        (.explicit initial) A dims coordinate =
      reductionSliceValue (γ := Bool) ops (ops.boolFunction f) ops.addSum
        (.explicit initial) A dims coordinate) : CountDimsExact ops := by
  intro α β γ f A dims initial R coordinate value hcolon hcount hvalue
  rw [hcoherent (γ := γ) f A dims initial coordinate]
  exact countDims_boolean_slice ops hslices f A dims initial R coordinate value
    hcolon hcount hvalue

/-- An inhabited first iteration cannot produce a mapped value of the empty type.
This is a typed-model obstruction, independent of any Julia input claim. -/
theorem countEmptyMapped_no_success (ops : Operations) {α β : Type}
    (f : ops.Function) (op : ops.Operator) (slice : ops.Input α)
    (initial result : β) (first : α) (state : ops.State)
    (hfirst : ops.iterate slice = .ok (some (first, state))) :
    _mapreduce_dim_colon_init (γ := Empty) ops f op initial slice ≠ .ok result := by
  intro h
  cases hmapped : ops.applyFunction (F := ops.Function) (α := α) (β := Empty) f first with
  | error failure =>
      simp only [_mapreduce_dim_colon_init, hfirst, hmapped, bind, Except.bind,
        reduceCtorEq] at h
  | ok impossible => exact Empty.elim impossible

/-- The arbitrary mapped type in the frozen count specification precludes a
successful nonempty slice. This diagnoses the specification, not Julia behavior. -/
theorem countDimsExact_nonempty_obstruction (ops : Operations) {α β : Type}
    (f : ops.Function) (A slice : ops.Input α) (dims : ops.Region)
    (initial : β) (R : ops.Array β) (coordinate : List ops.Index) (value : β)
    (first : α) (state : ops.State)
    (hcolon : ops.isColon dims = false)
    (hcount : count_function ops f A dims initial = .ok (.array R))
    (hvalue : ops.getArray R coordinate = .ok value)
    (hslice : reductionSlice ops A dims coordinate = .ok slice)
    (hfirst : ops.iterate slice = .ok (some (first, state))) :
    ¬ CountDimsExact ops := by
  intro hcontract
  have hs := hcontract (γ := Empty) f A dims initial R coordinate value
    hcolon hcount hvalue
  have hscalar : _mapreduce_dim_colon_init (γ := Empty) ops
      (ops.boolFunction f) ops.addSum initial slice = .ok value := by
    simpa only [reductionSliceValue, hslice, bind, Except.bind] using hs
  exact countEmptyMapped_no_success ops (ops.boolFunction f) ops.addSum slice
    initial value first state hfirst hscalar

/-- Counting a concatenated key list factors through the intermediate accumulator. -/
theorem countTrueLoop_append_keys (ops : Operations) {α β : Type}
    (f : ops.Function) (A : ops.Input α) (one : β)
    (first rest : List ops.Index) (initial : β) :
    countTrueLoop ops f A one (first ++ rest) initial =
      (countTrueLoop ops f A one first initial >>= fun middle =>
        countTrueLoop ops f A one rest middle) := by
  induction first generalizing initial with
  | nil => rfl
  | cons key keys ih =>
      simp only [List.cons_append, countTrueLoop]
      cases hget : ops.getInputLinear A key with
      | error e => simp only [hget, bind, Except.bind]
      | ok value =>
          simp only [hget, bind, Except.bind]
          cases hpred : ops.applyFunction (F := ops.Function) (α := α) (β := Bool)
              (ops.boolFunction f) value with
          | error e => simp only [hpred, bind, Except.bind]
          | ok predicate =>
              simp only [hpred, bind, Except.bind]
              cases htruth : ops.toBool predicate with
              | error e => simp only [htruth, bind, Except.bind]
              | ok truth =>
                  cases truth with
                  | false =>
                      simp only [htruth, bind, Except.bind, Bool.false_eq_true, ite_false]
                      exact ih initial
                  | true =>
                      simp only [htruth, bind, Except.bind, Bool.true_eq, ite_true]
                      cases hadd : ops.applyOperator (O := ops.Operator) (A := β) (B := β)
                          ops.addSum initial one with
                      | error e => simp only [hadd, bind, Except.bind]
                      | ok next =>
                          simp only [hadd, bind, Except.bind]
                          exact ih next

/-- Empty index enumeration returns the initial scalar after obtaining its unit. -/
theorem countExpected_empty_keys (ops : Operations) {α β : Type}
    (f : ops.Function) (A : ops.Input α) (initial one : β)
    (hone : ops.oneType (ops.valueTypeOf initial) = .ok one)
    (hkeys : ops.eachIndexInput A = .ok []) :
    countExpected ops f A initial = .ok initial := by
  simp only [countExpected, hone, hkeys, bind, Except.bind, countTrueLoop]

/-- The applied contract follows from the displayed callback, slice, type-coherence,
and in-place output premises; no premise is established for a faithful Julia model. -/
theorem countReductionContract_of_laws (ops : Operations)
    (hcolon : ops.isColon ops.colonRegion = true)
    (hcallback : ∀ {α β : Type} (f : ops.Function) (A : ops.Input α)
      (initial expected : β),
      countExpected ops f A initial = .ok expected →
      ops.simpleCount f A initial = .ok expected)
    (hslices : MapreduceDimsSliceValues ops)
    (hcoherent : ∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
      (dims : ops.Region) (initial : β) (coordinate : List ops.Index),
      reductionSliceValue (γ := γ) ops (ops.boolFunction f) ops.addSum
        (.explicit initial) A dims coordinate =
      reductionSliceValue (γ := Bool) ops (ops.boolFunction f) ops.addSum
        (.explicit initial) A dims coordinate)
    (hinplace : InPlaceReductionOutputs ops) : CountReductionContract ops := by
  exact ⟨⟨(countColonExact_iff_callback ops hcolon).mpr hcallback,
      countDimsExact_of_slice_coherence ops hslices hcoherent⟩, hinplace⟩

end JuliaLean.ChatGPT.Batch8.Group12

namespace JuliaLean.ChatGPT.Batch8.Group12

open JuliaLean JuliaLean.base.reducedim JuliaLean.Proofs.base.reducedim

/-- The comparison error propagates at every incumbent index, including a zero
index. This identifies the extra callback in the current model. -/
theorem find_axis_first_comparison_failure (ops : Operations) {α β : Type}
    (f : ops.Function) (op : ops.Operator) (zeroIndex index key i : ops.Index)
    (A : ops.Input α) (outer remaining rest : List ops.Index)
    (initial mapped : β) (input : α)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (hget : ops.getInput A (i :: outer) = .ok input)
    (hmap : ops.applyFunction (F := ops.Function) (α := α) (β := β) f input =
      .ok mapped)
    (hcompare : ops.applyPredicate (O := ops.Operator) (A := β) (B := β)
      op initial mapped = .error failure) :
    findMinMaxAxisFirst ops f op zeroIndex A outer (key :: remaining) (i :: rest)
      initial index = .error failure := by
  rw [findMinMaxAxisFirst]
  simp only [hget, hmap, hcompare, bind, Except.bind]

/-- Both in-place wrappers evaluate the emptiness callback even with init false. -/
theorem find_inPlace_false_emptiness_failure (ops : Operations) {α : Type}
    (Rval : ops.Array α) (Rind : ops.Array ops.Index) (A : ops.Input α)
    (failure : JuliaLean.base.abstractarray.ArrayError)
    (hempty : ops.isEmptyInput A = .error failure) :
    findminInPlace ops Rval Rind A false = .error failure ∧
      findmaxInPlace ops Rval Rind A false = .error failure := by
  simp only [findminInPlace, findmaxInPlace, hempty, bind, Except.bind,
    and_self]

/-- The allocating model evaluates ordinary reduction axes before its emptiness
test; an error there is propagated even without an empty-input premise. -/
theorem find_allocating_extra_axes_failure (ops : Operations) {α γ : Type}
    (f : ops.Function) (A : ops.Input α) (dims : ops.Region)
    (axes : List ops.Axis) (failure : JuliaLean.base.abstractarray.ArrayError)
    (haxes0 : reduced_indices0_input ops A dims = .ok axes)
    (haxes : reduced_indices_input ops A dims = .error failure) :
    _findmin (γ := γ) ops f A dims = .error failure ∧
      _findmax (γ := γ) ops f A dims = .error failure := by
  simp only [_findmin, _findmax, haxes0, haxes, bind, Except.bind, and_self]

end JuliaLean.ChatGPT.Batch8.Group12

namespace JuliaLean.ChatGPT.Batch8.Group12

open JuliaLean JuliaLean.base.reducedim JuliaLean.Proofs.base.reducedim

/-- With a nonzero incumbent index and nonzero traversal keys, the first-axis
kernel returns an incumbent dominating its initial value and every visited input.
Only local comparison laws and a reflexive, transitive dominance relation are used. -/
theorem find_axis_first_dominates (ops : Operations) {α β : Type}
    (f : ops.Function) (op : ops.Operator) (zeroIndex : ops.Index)
    (A : ops.Input α) (outer : List ops.Index) (dominates : β → β → Prop)
    (hrefl : ∀ x, dominates x x)
    (htrans : ∀ x y z, dominates x y → dominates y z → dominates x z)
    (htrue : ∀ old fresh,
      ops.applyPredicate (O := ops.Operator) (A := β) (B := β) op old fresh = .ok true →
      dominates fresh old)
    (hfalse : ∀ old fresh,
      ops.applyPredicate (O := ops.Operator) (A := β) (B := β) op old fresh = .ok false →
      dominates old fresh)
    (axis keys : List ops.Index) (initial : β) (initialIndex : ops.Index)
    (value : β) (index : ops.Index) (remaining : List ops.Index)
    (hlen : axis.length ≤ keys.length)
    (hindex : ops.indexEqual initialIndex zeroIndex = false)
    (hkeys : ∀ key, key ∈ keys → ops.indexEqual key zeroIndex = false)
    (hresult : findMinMaxAxisFirst ops f op zeroIndex A outer keys axis
      initial initialIndex = .ok (value, index, remaining)) :
    dominates value initial ∧
      ∀ i key input mapped,
        (i, key) ∈ axis.zip keys →
        ops.getInput A (i :: outer) = .ok input →
        ops.applyFunction (F := ops.Function) (α := α) (β := β) f input = .ok mapped →
        dominates value mapped := by
  induction axis generalizing keys initial initialIndex with
  | nil =>
      simp only [findMinMaxAxisFirst, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at hresult
      rcases hresult with ⟨hvalue, hindexOut, hremaining⟩
      constructor
      · rw [← hvalue]
        exact hrefl initial
      · intro i key input mapped hmem
        cases hmem
  | cons i rest ih =>
      cases keys with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen
          omega
      | cons key tail =>
          have htail : rest.length ≤ tail.length := by
            simp only [List.length_cons] at hlen
            omega
          have hkey : ops.indexEqual key zeroIndex = false :=
            hkeys key List.mem_cons_self
          have htailKeys : ∀ k, k ∈ tail → ops.indexEqual k zeroIndex = false :=
            fun k hk => hkeys k (List.mem_cons_of_mem key hk)
          rw [findMinMaxAxisFirst] at hresult
          cases hget : ops.getInput A (i :: outer) with
          | error failure =>
              simp only [hget, bind, Except.bind, reduceCtorEq] at hresult
          | ok input =>
              cases hmap : ops.applyFunction (F := ops.Function) (α := α)
                  (β := β) f input with
              | error failure =>
                  simp only [hget, hmap, bind, Except.bind, reduceCtorEq] at hresult
              | ok mapped =>
                  have hcombine (hfirst : dominates value mapped)
                      (htails : ∀ j k input' candidate,
                        (j, k) ∈ rest.zip tail →
                        ops.getInput A (j :: outer) = .ok input' →
                        ops.applyFunction (F := ops.Function) (α := α) (β := β)
                          f input' = .ok candidate → dominates value candidate) :
                      ∀ j k input' candidate,
                        (j, k) ∈ (i :: rest).zip (key :: tail) →
                        ops.getInput A (j :: outer) = .ok input' →
                        ops.applyFunction (F := ops.Function) (α := α) (β := β)
                          f input' = .ok candidate → dominates value candidate := by
                    intro j k input' candidate hmem hread hfun
                    change (j, k) ∈ (i, key) :: rest.zip tail at hmem
                    rcases List.mem_cons.mp hmem with hpair | htailMem
                    · have hj : j = i := congrArg Prod.fst hpair
                      rw [hj] at hread
                      have hinput : input' = input := Except.ok.inj (hread.symm.trans hget)
                      rw [hinput] at hfun
                      have hcandidate : candidate = mapped :=
                        Except.ok.inj (hfun.symm.trans hmap)
                      rw [hcandidate]
                      exact hfirst
                    · exact htails j k input' candidate htailMem hread hfun
                  cases hcompare : ops.applyPredicate (O := ops.Operator)
                      (A := β) (B := β) op initial mapped with
                  | error failure =>
                      simp only [hget, hmap, hcompare, bind, Except.bind,
                        reduceCtorEq] at hresult
                  | ok comparison =>
                      cases comparison with
                      | false =>
                          have hrec : findMinMaxAxisFirst ops f op zeroIndex A outer
                              tail rest initial initialIndex =
                                .ok (value, index, remaining) := by
                            simpa only [hget, hmap, hcompare, hindex, bind, Except.bind,
                              Bool.false_or, Bool.false_eq_true, ite_false] using hresult
                          have htailResult := ih tail initial initialIndex htail hindex htailKeys hrec
                          constructor
                          · exact htailResult.1
                          · exact hcombine
                              (htrans value initial mapped htailResult.1
                                (hfalse initial mapped hcompare)) htailResult.2
                      | true =>
                          have hrec : findMinMaxAxisFirst ops f op zeroIndex A outer
                              tail rest mapped key = .ok (value, index, remaining) := by
                            simpa only [hget, hmap, hcompare, hindex, bind, Except.bind,
                              Bool.false_or, ite_true] using hresult
                          have htailResult := ih tail mapped key htail hkey htailKeys hrec
                          constructor
                          · exact htrans value mapped initial htailResult.1
                              (htrue initial mapped hcompare)
                          · exact hcombine htailResult.1 htailResult.2

/-- After zero-index initialization of a nonempty first-axis slice, a successful
pass dominates every mapped input in that slice. No bound on the discarded old
value is promised. -/
theorem find_axis_first_zero_dominates (ops : Operations) {α β : Type}
    (f : ops.Function) (op : ops.Operator) (zeroIndex initialIndex firstKey firstAxis : ops.Index)
    (A : ops.Input α) (outer : List ops.Index) (dominates : β → β → Prop)
    (hrefl : ∀ x, dominates x x)
    (htrans : ∀ x y z, dominates x y → dominates y z → dominates x z)
    (htrue : ∀ old fresh,
      ops.applyPredicate (O := ops.Operator) (A := β) (B := β) op old fresh = .ok true →
      dominates fresh old)
    (hfalse : ∀ old fresh,
      ops.applyPredicate (O := ops.Operator) (A := β) (B := β) op old fresh = .ok false →
      dominates old fresh)
    (tail axisTail : List ops.Index) (initial firstMapped value : β)
    (firstInput : α) (comparison : Bool) (index : ops.Index) (remaining : List ops.Index)
    (hlen : axisTail.length ≤ tail.length)
    (hkeys : ∀ key, key ∈ firstKey :: tail → ops.indexEqual key zeroIndex = false)
    (hget : ops.getInput A (firstAxis :: outer) = .ok firstInput)
    (hmap : ops.applyFunction (F := ops.Function) (α := α) (β := β) f firstInput =
      .ok firstMapped)
    (hindex : ops.indexEqual initialIndex zeroIndex = true)
    (hcompare : ops.applyPredicate (O := ops.Operator) (A := β) (B := β)
      op initial firstMapped = .ok comparison)
    (hresult : findMinMaxAxisFirst ops f op zeroIndex A outer
      (firstKey :: tail) (firstAxis :: axisTail) initial initialIndex =
        .ok (value, index, remaining)) :
    ∀ i key input mapped,
      (i, key) ∈ (firstAxis :: axisTail).zip (firstKey :: tail) →
      ops.getInput A (i :: outer) = .ok input →
      ops.applyFunction (F := ops.Function) (α := α) (β := β) f input = .ok mapped →
      dominates value mapped := by
  rw [findMinMaxAxisFirst] at hresult
  have hnext : findMinMaxAxisFirst ops f op zeroIndex A outer tail axisTail
      firstMapped firstKey = .ok (value, index, remaining) := by
    simpa only [hget, hmap, hcompare, hindex, bind, Except.bind,
      Bool.true_or, ite_true] using hresult
  have hfirstKey : ops.indexEqual firstKey zeroIndex = false :=
    hkeys firstKey List.mem_cons_self
  have htailKeys : ∀ key, key ∈ tail → ops.indexEqual key zeroIndex = false :=
    fun key hkey => hkeys key (List.mem_cons_of_mem firstKey hkey)
  have htailResult := find_axis_first_dominates ops f op zeroIndex A outer dominates
    hrefl htrans htrue hfalse axisTail tail firstMapped firstKey value index remaining
    hlen hfirstKey htailKeys hnext
  intro i key input mapped hmem hread hfun
  change (i, key) ∈ (firstAxis, firstKey) :: axisTail.zip tail at hmem
  rcases List.mem_cons.mp hmem with hpair | htailMem
  · have hi : i = firstAxis := congrArg Prod.fst hpair
    rw [hi] at hread
    have hinput : input = firstInput := Except.ok.inj (hread.symm.trans hget)
    rw [hinput] at hfun
    have hmapped : mapped = firstMapped := Except.ok.inj (hfun.symm.trans hmap)
    rw [hmapped]
    exact htailResult.1
  · exact htailResult.2 i key input mapped htailMem hread hfun

end JuliaLean.ChatGPT.Batch8.Group12

namespace JuliaLean.ChatGPT.Batch8.Group12

open JuliaLean JuliaLean.base.reducedim JuliaLean.Proofs.base.reducedim

/-- The count loop adds precisely the number of true predicate outcomes in its
key list. `tally` may encode natural counts in any accumulator type, provided
one successful addition advances that encoding by one. -/
theorem countTrueLoop_tally (ops : Operations) {α β : Type}
    (f : ops.Function) (A : ops.Input α) (one : β)
    (truth : ops.Index → Bool) (tally : Nat → β)
    (hstep : ∀ n : Nat,
      ops.applyOperator (O := ops.Operator) (A := β) (B := β)
        ops.addSum (tally n) one = .ok (tally (n + 1))) :
    ∀ (keys : List ops.Index) (initialCount : Nat),
      (∀ key ∈ keys, ∃ (value : α) (predicate : Bool),
        ops.getInputLinear A key = .ok value ∧
        ops.applyFunction (F := ops.Function) (α := α) (β := Bool)
          (ops.boolFunction f) value = .ok predicate ∧
        ops.toBool predicate = .ok (truth key)) →
      countTrueLoop ops f A one keys (tally initialCount) =
        .ok (tally (initialCount + keys.countP truth)) := by
  intro keys
  induction keys with
  | nil =>
      intro initialCount _
      simp only [countTrueLoop, List.countP_nil, Nat.add_zero]
  | cons key keys ih =>
      intro initialCount hlocal
      obtain ⟨value, predicate, hget, hpredicate, hbool⟩ :=
        hlocal key List.mem_cons_self
      have htail : ∀ next ∈ keys, ∃ (value : α) (predicate : Bool),
          ops.getInputLinear A next = .ok value ∧
          ops.applyFunction (F := ops.Function) (α := α) (β := Bool)
            (ops.boolFunction f) value = .ok predicate ∧
          ops.toBool predicate = .ok (truth next) := by
        intro next hmem
        exact hlocal next (List.mem_cons_of_mem key hmem)
      simp only [countTrueLoop, hget, hpredicate, hbool, bind, Except.bind]
      cases htruth : truth key with
      | false =>
          simpa only [List.countP_cons, htruth, Bool.false_eq_true, ite_false,
            Nat.add_zero] using ih initialCount htail
      | true =>
          have harith : initialCount + 1 + keys.countP truth =
              initialCount + (keys.countP truth + 1) := by omega
          simp only [ite_true, hstep initialCount]
          simpa only [List.countP_cons, htruth, Bool.true_eq, ite_true, harith]
            using ih (initialCount + 1) htail

/-- The scalar expected-count computation returns the encoded initial count
plus the number of true outcomes when unit lookup, index enumeration, and the
per-index operations succeed. -/
theorem countExpected_tally (ops : Operations) {α β : Type}
    (f : ops.Function) (A : ops.Input α) (one : β)
    (truth : ops.Index → Bool) (tally : Nat → β)
    (keys : List ops.Index) (initialCount : Nat)
    (hstep : ∀ n : Nat,
      ops.applyOperator (O := ops.Operator) (A := β) (B := β)
        ops.addSum (tally n) one = .ok (tally (n + 1)))
    (hone : ops.oneType (ops.valueTypeOf (tally initialCount)) = .ok one)
    (hkeys : ops.eachIndexInput A = .ok keys)
    (hlocal : ∀ key ∈ keys, ∃ (value : α) (predicate : Bool),
      ops.getInputLinear A key = .ok value ∧
      ops.applyFunction (F := ops.Function) (α := α) (β := Bool)
        (ops.boolFunction f) value = .ok predicate ∧
      ops.toBool predicate = .ok (truth key)) :
    countExpected ops f A (tally initialCount) =
      .ok (tally (initialCount + keys.countP truth)) := by
  simpa only [countExpected, hone, hkeys, bind, Except.bind]
    using countTrueLoop_tally ops f A one truth tally hstep keys initialCount hlocal

end JuliaLean.ChatGPT.Batch8.Group12

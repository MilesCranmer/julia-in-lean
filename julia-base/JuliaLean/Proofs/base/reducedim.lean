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
    ReductionArraySliceValues (γ := Bool) ops (ops.boolFunction ops.identity)
      ops.orAny A dims init R) ∧
  (∀ {α β : Type} (A : ops.Input α) (dims : ops.Region) (init : InitArg β)
      (R : ops.Array β),
    all ops A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := Bool) ops (ops.boolFunction ops.identity)
      ops.andAll A dims init R)
def MapreducedimInPlaceContract (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (op : ops.Operator)
    (R : ops.Array β) (A : ops.Input α) error result,
    (check_reducedims ops R A = .error error →
      _mapreducedim! (γ := γ) ops f op R A = .error error) ∧
    (mapreducedim! (γ := γ) ops f op R A = .ok result → result = R)

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

def InPlaceReductionOutputs (ops : Operations) : Prop :=
  ∀ {α β γ : Type} (f : ops.Function) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) result,
    (sumInPlace (γ := γ) ops f R A init = .ok result → result = R) ∧
    (prodInPlace (γ := γ) ops f R A init = .ok result → result = R) ∧
    (maximumInPlace (γ := γ) ops f R A init = .ok result → result = R) ∧
    (minimumInPlace (γ := γ) ops f R A init = .ok result → result = R) ∧
    (extremaInPlace (γ := γ) ops f R A init = .ok result → result = R) ∧
    (allInPlace (γ := γ) ops f R A init = .ok result → result = R) ∧
    (anyInPlace (γ := γ) ops f R A init = .ok result → result = R) ∧
    (countInPlace (γ := γ) ops f R A init = .ok result → result = R)

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
    ReductionArraySliceValues (γ := Bool) ops (ops.boolFunction f)
      ops.orAny A dims init R) ∧
  (∀ {α β γ : Type} (f : ops.Function) (A : ops.Input α)
      (dims : ops.Region) (init : InitArg β) (R : ops.Array β),
    all_function (γ := γ) ops f A dims init = .ok (.array R) →
    ReductionOutputAxesExact ops A dims R →
    ReductionArraySliceValues (γ := Bool) ops (ops.boolFunction f)
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

def entries : List Entry := [
  { id := "reduce-sumdims-exact", juliaFile := "base/reducedim.jl",
    juliaFns := ["sum(A; dims)", "mapreducedim!", "reducedim_init"],
    statement := "sum(A; dims=1 or 2) over a BitInteger matrix has the reduced shape and returns exact slice sums in Julia's widened result type (Int/UInt for small inputs), including the pairwise path.",
    source := "base/reducedim.jl:464-510 (sum dimensions docstrings)",
    status := .todo, prop := ``SumDimsExact },
  { id := "reduce-maxdims-int", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum(A; dims)", "minimum(A; dims)", "reducedim_init"],
    statement := "maximum/minimum(A; dims=1 or 2) on a nonempty Matrix{Int} has the reduced shape and equals maximum/minimum of each slice.",
    source := "base/reducedim.jl:613-743 (maximum/minimum dimensions docstrings)",
    status := .todo, prop := ``MaxMinDimsExact },
  { id := "reduce-finddims-slices", juliaFile := "base/reducedim.jl",
    juliaFns := ["findmax(A; dims)", "findmin(A; dims)", "findminmax!"],
    statement := "findmax/findmin(A; dims=1 or 2) on a nonempty Matrix{Float64} returns each slice's extremal value and CartesianIndex.",
    source := "base/reducedim.jl:1096-1212 (findmin/findmax dimensions docstrings)",
    status := .todo, prop := ``FindIdentityContract },
  { id := "reduce-any-dims-missing", juliaFile := "base/reducedim.jl",
    juliaFns := ["any(A; dims)", "all(A; dims)", "or_any", "and_all"],
    statement := "any(A; dims) returns any(slice) for each slice of a Bool-and-missing matrix, with the same three-valued behavior as any(A).",
    source := "base/reducedim.jl:841-988 (all/any dimensions docstrings)",
    status := .todo, prop := ``AnyAllDimsExact },
  { id := "reduce-maxdims-union-eltype", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum(A; dims)", "minimum(A; dims)", "reducedim_init"],
    statement := "maximum(A; dims) succeeds on nonempty matrices of Int, Float64, or Union{Int, Float64}, and each output is the maximum of its slice.",
    source := "base/reducedim.jl:613-743 (maximum/minimum dimensions docstrings)",
    status := .todo, prop := ``MaxMinUnionDimsExact },
  { id := "reduce-maxdims-all-missing", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum(A; dims)", "minimum(A; dims)", "reducedim_init"],
    statement := "maximum(A; dims) and minimum(A; dims) of a nonempty all-missing matrix return missing for every slice.",
    source := "base/reducedim.jl:613-743; base/missing.jl:129-137",
    status := .todo, prop := ``MaxMinAllMissingValues },
  { id := "reduce-maxabs-dims-typemin", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum(f, A; dims)", "maximum(abs, A; dims)", "maximum(abs2, A; dims)", "reducedim_init"],
    statement := "maximum(abs, A; dims) on a nonempty Matrix{Int} equals maximum(abs, slice) for every slice.",
    source := "base/reducedim.jl:641-664 (maximum(f, A; dims) docstring)",
    status := .todo, prop := ``MaxMinFunctionDimsExact },
  { id := "reduce-sumdims-init-narrow", juliaFile := "base/reducedim.jl",
    juliaFns := ["sum(A; dims, init)", "count(A; dims, init)", "mapreduce(f, op, A; dims, init)"],
    statement := "sum(A; dims, init=zero(S)) over a small-integer matrix equals sum(slice; init=zero(S)) for every slice.",
    source := "base/reducedim.jl:328-352,485-510; base/reduce.jl:546-557",
    status := .todo, prop := ``MapreduceDimsSliceValues },
  { id := "reduce-finddims-empty-shape", juliaFile := "base/reducedim.jl",
    juliaFns := ["findmax(A; dims)", "findmin(A; dims)", "argmax(A; dims)", "argmin(A; dims)"],
    statement := "findmax(A; dims) returns value and index arrays with the same reduced shape as sum(A; dims), including singleton axes for selected dimensions.",
    source := "base/reducedim.jl:1096-1212 (findmin/findmax dimensions docstrings)",
    status := .todo, prop := ``FindDimsShapeExact },
  { id := "multidimcov-reducedim-repair-shapes", juliaFile := "base/reducedim.jl",
    juliaFns := ["reduced_index", "reduced_indices", "reduced_indices0", "_check_valid_region"],
    statement := "Valid reduced-index results preserve rank, preserve unselected axes, and use singleton axes for selected dimensions.",
    source := "base/reducedim.jl:6-35 (index and region methods)",
    status := .todo, prop := ``ReducedIndicesShape },
  { id := "multidimcov-reducedim-range-error", juliaFile := "base/reducedim.jl",
    juliaFns := ["reduced_index(i::AbstractUnitRange)"],
    statement := "Unsupported range types raise an ArgumentError naming the actual range type and giving the method implementation guidance.",
    source := "base/reducedim.jl:8-14 (unsupported reduced-index method)",
    status := .todo, prop := ``UnsupportedUnitRangeExact },
  { id := "multidimcov-reducedim-valid-region", juliaFile := "base/reducedim.jl",
    juliaFns := ["_check_valid_region"],
    statement := "Every dimension value in a successful region is an Integer whose Int conversion is at least one.",
    source := "base/reducedim.jl:30-35 (region validation)",
    status := .todo, prop := ``ValidRegionExact },
  { id := "multidimcov-reducedim-promote-union", juliaFile := "base/reducedim.jl",
    juliaFns := ["promote_union(::Union)"],
    statement := "Union element types are recursively promoted from both branches before the result type is returned.",
    source := "base/reducedim.jl:59-60 (union promotion)",
    status := .todo, prop := ``PromoteUnionExact },

  { id := "multidimcov-reducedim-repair-init-a", juliaFile := "base/reducedim.jl",
    juliaFns := ["initarray!", "reducedim_initarray", "promote_union", "_realtype", "_reducedim_init"],
    statement := "Initialization preserves reduced axes, applies the source-selected identities and extrema seeds, and keeps in-place initialization in the supplied array.",
    source := "base/reducedim.jl:42-85 (initialization methods)",
    status := .todo, prop := ``ReducedInitializationExact },
  { id := "multidimcov-reducedim-repair-find", juliaFile := "base/reducedim.jl",
    juliaFns := ["findminmax!(f, op, Rval, Rind, A)", "findmin!", "findmax!", "findmin(A; dims)", "findmax(A; dims)", "findmin(f, A; dims)", "findmax(f, A; dims)", "argmin", "argmax"],
    statement := "Find reductions return a matching extremal input index per slice; their value and index arrays have the reduced shape, argmin/argmax return the matching index array, and in-place methods update both outputs.",
    source := "base/reducedim.jl:1032-1288 (find methods)",
    status := .todo, prop := ``FindReductionContract },
  { id := "reducedim-kernel-contract", juliaFile := "base/reducedim.jl",
    juliaFns := ["check_reducedims", "copyfirst!", "mapfirst!(f, R, A)", "_mapreducedim!(f, op, R, A)", "mapreducedim!(f, op, R, A)", "reducedim!(op, R, A)"],
    statement := "Each output receives the reduction of its matching input slice, first-slice initialization copies the matching slice, in-place methods return the supplied output, and incompatible axes error.",
    source := "base/reducedim.jl:205-299 (reduction checks, slices and kernels)",
    status := .todo, prop := ``MapreducedimKernelExact },
  { id := "reducedim-count-contract", juliaFile := "base/reducedim.jl",
    juliaFns := ["count(A; dims)", "count(f, A; dims)", "_count", "count!(R, A)", "count!(f, R, A)"],
    statement := "Count returns true predicate totals over the input or each selected slice, and count! updates its supplied output array.",
    source := "base/reducedim.jl:397-461 (count docstring and methods)",
    status := .todo, prop := ``CountReductionContract },
  { id := "reducedim-generated-wrappers", juliaFile := "base/reducedim.jl",
    juliaFns := ["mapreduce(f, op, A; dims)", "reduce(op, A; dims)", "sum(A; dims)", "sum(f, A; dims)", "prod(A; dims)", "prod(f, A; dims)", "maximum(A; dims)", "maximum(f, A; dims)", "minimum(A; dims)", "minimum(f, A; dims)", "extrema(A; dims)", "extrema(f, A; dims)", "all(A; dims)", "all(f, A; dims)", "any(A; dims)", "any(f, A; dims)", "sum!(f, R, A)", "prod!(f, R, A)", "maximum!(f, R, A)", "minimum!(f, R, A)", "extrema!(f, R, A)", "all!(f, R, A)", "any!(f, R, A)"],
    statement := "Dimensional wrappers return the full reduction of each corresponding slice with reduced axes, honor initial and empty-input behavior, propagate NaN for maximum/minimum, and update the supplied array in in-place forms.",
    source := "base/reducedim.jl:328-392,485-1027 (reduction methods and generated wrappers)",
    status := .todo, prop := ``GeneratedReductionContract },
  { id := "reducecov-dims-unsigned-large", juliaFile := "base/reducedim.jl",
    juliaFns := ["_check_valid_region", "reduced_indices"],
    statement := "Dimension validation accepts every positive integer dimension supported by the source conversion, including trailing dimensions.",
    source := "base/reducedim.jl:30-35 (region validation)",
    status := .todo, prop := ``ValidRegionExact },
  { id := "reducecov-maximum-inplace-empty", juliaFile := "base/reducedim.jl",
    juliaFns := ["maximum!", "maximum!(f, r, A)", "minimum!", "minimum!(f, r, A)", "extrema!", "extrema!(f, r, A)"],
    statement := "In-place maximum, minimum, and extrema throw when the output axes describe a selected empty slice.",
    source := "base/reducedim.jl:89-128,1020-1022 (extrema initialization and in-place wrappers)",
    status := .todo, prop := ``InPlaceMaxMinEmptySliceErrorClaim },
  { id := "reducecov-findmax-inplace-init", juliaFile := "base/reducedim.jl",
    juliaFns := ["findmin!", "findmax!"],
    statement := "With init=false, an existing in-place find value remains a bound on the result; findmin! cannot return a larger value and findmax! cannot return a smaller value.",
    source := "base/reducedim.jl:1091-1094,1164-1167 (find in-place methods)",
    status := .todo, prop := ``FindInPlaceContract },
]

end JuliaLean.Proofs.base.reducedim

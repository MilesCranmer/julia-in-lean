import JuliaLean.base.slicearray
import JuliaLean.Bindings.base.reshapedarray
import JuliaLean.Registry.Types

/-!
# Properties of `base/slicearray.jl`

Statements over the source-mirrored model of `JuliaLean/base/slicearray.lean`. Methods run in
`SM E`, whose exception is the lossless sum `SliceErr E` of every callee's exception type.
Numeric claims are stated for native `Int` dimensions (`nativeDims`), whose `<=`, `==`,
`isequal` and `max` are the installed `int.jl` methods, so no law about the `IntegerMethods` record
is assumed; shape and parent claims are stated for every `Integer` family. The parent type's own
methods (`SliceParentOps`) and its `size`/`reshape` are typed inputs with no laws.

The lookup and assignment statements (`SlicesElementsAreParentViews`,
`SlicesAssignmentTargetsMappedParent`) keep the parent `view`/`setindex!`/read laws of the earlier
statements: `view`, the parent `setindex!` and `checkbounds` have no installed binding yet
(slicearray-bind3 gaps), so these entries stay blocked on the model.
-/

namespace JuliaLean.Proofs.base.slicearray

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.slicearray

/-- Every exception a sliced-array method or its parent can raise. -/
inductive SliceErr (E : Type) where
  | array (error : ArrayError)
  | tuple (error : TupleError)
  | ntuple (error : NtupleError)
  | print (error : JuliaLean.base.strings.io.Error E)
  | reshaped (error : JuliaLean.base.reshapedarray.ReshapedError)

abbrev SM (E : Type) := Except (SliceErr E)

instance {E : Type} : MonadExceptOf ArrayError (SM E) where
  throw e := .error (.array e)
  tryCatch x h := match x with
    | .error (.array e) => h e
    | r => r

instance {E : Type} : MonadExceptOf TupleError (SM E) where
  throw e := .error (.tuple e)
  tryCatch x h := match x with
    | .error (.tuple e) => h e
    | r => r

instance {E : Type} : MonadExceptOf NtupleError (SM E) where
  throw e := .error (.ntuple e)
  tryCatch x h := match x with
    | .error (.ntuple e) => h e
    | r => r

instance {E : Type} : MonadExceptOf (JuliaLean.base.strings.io.Error E) (SM E) where
  throw e := .error (.print e)
  tryCatch x h := match x with
    | .error (.print e) => h e
    | r => r

/-- A tuple of `Int` dimensions. -/
def nativeDims {Code : Type} {Payload : Code → Type} (dims : List I64) :
    List (IntegerValue Code Payload) :=
  dims.map .native

/-- `max(ndims(A), dims...)` on `Int` values. -/
def rankOf (n : I64) (dims : List I64) : Int :=
  dims.foldl (fun rank d => max rank d.val) n.val

/-- Whether position `p` (zero-based) is a requested dimension. -/
def isRequested (dims : List I64) (p : Nat) : Bool :=
  dims.any fun d => d.val == (p : Int) + 1

def IsColonSelector : Option I64 → Bool
  | none => true
  | some _ => false

def ParentCoordinatesFollowSelectors
    (selected : List (Option I64)) (inner parent : List I64) : Prop :=
  parent.length = selected.length ∧
    inner.length = selected.countP IsColonSelector ∧
    ∀ dimension, dimension < selected.length →
      match selected[dimension]? with
      | some (some coordinate) => parent[dimension]? = some coordinate
      | some none =>
          parent[dimension]? = inner[(selected.take dimension).countP IsColonSelector]?
      | none => False

/-- The parent's reads used to observe a view or an assignment. -/
structure ParentReads (E Parent View Value Element : Type) where
  getindexView : View → List I64 → SM E Element
  getindexParent : Parent → List I64 → SM E Element
  getindexValue : Value → List I64 → SM E Element

def ParentViewGetindexLaw {E Parent View Value Element : Type}
    (access : SliceAccessOps (SM E) Parent View Value)
    (reads : ParentReads E Parent View Value Element) : Prop :=
  ∀ parent selected viewValue inner parentCoordinates,
    access.view parent selected = .ok viewValue →
    ParentCoordinatesFollowSelectors selected inner parentCoordinates →
    reads.getindexView viewValue inner = reads.getindexParent parent parentCoordinates

def ParentSetindexEffectLaw {E Parent View Value Element : Type}
    (access : SliceAccessOps (SM E) Parent View Value)
    (reads : ParentReads E Parent View Value Element) : Prop :=
  ∀ parent selected value,
    access.setindexParent parent selected value = .ok value →
    ∃ updatedParent,
      (∀ inner parentCoordinates,
        ParentCoordinatesFollowSelectors selected inner parentCoordinates →
        reads.getindexParent updatedParent parentCoordinates = reads.getindexValue value inner) ∧
      (∀ parentCoordinates,
        (∀ inner, ¬ ParentCoordinatesFollowSelectors selected inner parentCoordinates) →
        reads.getindexParent updatedParent parentCoordinates =
          reads.getindexParent parent parentCoordinates)

/-- The parent coordinates `_slice_index` selects for outer index `indices` of a slice array made
from `Int` dimensions `dims`. -/
def RequestedSliceCoordinates {Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (s : Slices Parent Ax Code Payload N) (dims : List I64)
    (drop : Bool) (indices : IntegerIndices N) (selected : List (Option I64)) : Prop :=
  selected.length = s.slicemap.length ∧
    ∀ parentDimension, parentDimension < s.slicemap.length →
      if drop then
        match dims.findIdx? (fun d => d.val == (parentDimension : Int) + 1) with
        | some outerDimension =>
            ∃ coordinate,
              indices.values[outerDimension]? = some coordinate ∧
                selected[parentDimension]? = some (some coordinate)
        | none => selected[parentDimension]? = some none
      else if isRequested dims parentDimension then
        ∃ coordinate,
          indices.values[parentDimension]? = some coordinate ∧
            selected[parentDimension]? = some (some coordinate)
      else
        selected[parentDimension]? = some none

/-- Axes of a successful `_eachslice(A, dims, drop)` with `Int` dimensions. -/
def AxesOutcome {E Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload) (a : Parent)
    (dims : List I64) (drop : Bool) (s : Slices Parent Ax Code Payload N) : Prop :=
  ∃ n, ops.ndims a = .ok n ∧ (s.slicemap.length : Int) = rankOf n dims ∧
    if drop then
      N = dims.length ∧ (nativeDims dims).mapM (axesAt ops methods a) = .ok s.axes
    else
      (N : Int) = rankOf n dims ∧
      ∀ p (hp : p < s.axes.length),
        if isRequested dims p then
          axesAt ops methods a (.native (int ((p : Int) + 1))) = .ok s.axes[p]
        else s.axes[p] = unitaxis ops.oneTo a

/-- `size(s)` of a successful `_eachslice(A, dims, drop)` with `Int` dimensions. -/
def SizeOutcome {E Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload) (a : Parent)
    (dims : List I64) (drop : Bool) (s : Slices Parent Ax Code Payload N) : Prop :=
  if drop then
    ∃ ax, (nativeDims dims).mapM (axesAt ops methods a) = .ok ax ∧
      size ops.axisLength s = ax.mapM ops.axisLength
  else
    size ops.axisLength s = (List.range N).mapM fun p =>
      if isRequested dims p then do
        let axis ← axesAt ops methods a (.native (int ((p : Int) + 1)))
        ops.axisLength axis
      else ops.axisLength (unitaxis ops.oneTo a)

/-- Every successful `_slice_index` of the result selects the requested coordinates. -/
def SelectionOutcome {Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (methods : IntegerMethods Code Payload) (dims : List I64) (drop : Bool)
    (s : Slices Parent Ax Code Payload N) : Prop :=
  ∀ (E : Type) (indices : IntegerIndices N) selected,
    (sliceIndex methods s indices.values : SM E _) = .ok selected →
    RequestedSliceCoordinates s dims drop indices selected

def SlicesConstructorRejectsShortMap : Prop :=
  ∀ {E Parent Ax Code : Type} {Payload : Code → Type} (ops : SliceParentOps (SM E) Parent Ax)
      (methods : IntegerMethods Code Payload) (a : Parent)
      (slicemap : List (Option (IntegerValue Code Payload))) (outerAxes : List Ax) (n : I64),
    ops.ndims a = .ok n → (slicemap.length : Int) < n.val →
    ∃ message, slicesConstructor ops methods a slicemap outerAxes =
      .error (.array (.julia (.argumentError message)))

def SlicesConstructorPreservesInput : Prop :=
  ∀ {E Parent Ax Code : Type} {Payload : Code → Type} (ops : SliceParentOps (SM E) Parent Ax)
      (methods : IntegerMethods Code Payload) (a : Parent)
      (slicemap : List (Option (IntegerValue Code Payload))) (outerAxes : List Ax)
      (N : Nat) (s : Slices Parent Ax Code Payload N),
    slicesConstructor ops methods a slicemap outerAxes = .ok ⟨N, s⟩ →
    parent s = a ∧ s.slicemap = slicemap ∧ axes s = outerAxes ∧ N = outerAxes.length ∧
      ∃ parentAxes,
        (JuliaLean.base.ntuple.ntupleInt (fun d => axesAt ops methods a (.native d))
          (int slicemap.length) ntupleRange : SM E (List Ax)) = .ok parentAxes ∧
        s.viewType = ops.promoteView ops.parentType (List.zipWith
          (fun axis entry => match entry with
            | none => SliceViewArgument.colon
            | some _ => .index (ops.axisEltype axis))
          parentAxes slicemap)

def SlicesConstructorInvariant : Prop :=
  SlicesConstructorRejectsShortMap ∧ SlicesConstructorPreservesInput

def UnitAxisIsSingleton : Prop :=
  ∀ {A Ax : Type} (oneTo : I64 → Ax) (a : A), unitaxis oneTo a = oneTo (int 1)

def EmptyDimensionsProduceWholeParentSlice : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (n : I64)
      (N : Nat) (s : Slices Parent Ax Code Payload N),
    ops.ndims a = .ok n →
    eachsliceTuple ops methods printing a [] true = .ok ⟨N, s⟩ →
    N = 0 ∧ axes s = [] ∧ (s.slicemap.length : Int) = n.val ∧
      (∀ entry, entry ∈ s.slicemap → entry = none) ∧ parent s = a

/-- Restricted: the message is printed through the `IntegerPrinting` environment, whose `show.jl`
inputs have no installed binding, so a printing exception may replace the `DimensionMismatch`. -/
def InvalidDimensionsThrow : Prop :=
  ∀ {E V Ty Code : Type} {Payload : Code → Type} (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (dims : List I64),
    (((∃ d, d ∈ dims ∧ d.val < 1) ∨ ¬ List.Pairwise (fun l r : I64 => l.val ≠ r.val) dims) →
      match (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) with
      | .error (.array (.dimensionMismatch _)) => True
      | .error (.print _) => True
      | _ => False) ∧
    ((∀ d, d ∈ dims → d.val ≥ 1) → List.Pairwise (fun l r : I64 => l.val ≠ r.val) dims →
      (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) = .ok ())

def TupleEachsliceAxes : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dims : List I64)
      (drop : Bool) (N : Nat) (s : Slices Parent Ax Code Payload N),
    eachsliceTuple ops methods printing a (nativeDims dims) drop = .ok ⟨N, s⟩ →
    AxesOutcome ops methods a dims drop s

def TupleEachsliceSizeMatchesAxes : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dims : List I64)
      (drop : Bool) (N : Nat) (s : Slices Parent Ax Code Payload N),
    eachsliceTuple ops methods printing a (nativeDims dims) drop = .ok ⟨N, s⟩ →
    SizeOutcome ops methods a dims drop s

def TupleEachsliceSelectsRequestedDimensions : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dims : List I64)
      (drop : Bool) (N : Nat) (s : Slices Parent Ax Code Payload N),
    eachsliceTuple ops methods printing a (nativeDims dims) drop = .ok ⟨N, s⟩ →
    SelectionOutcome methods dims drop s

def TupleEachsliceContract : Prop :=
  TupleEachsliceAxes ∧ TupleEachsliceSizeMatchesAxes ∧
    TupleEachsliceSelectsRequestedDimensions

def IntegerEachsliceUsesItsAxis : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dim : I64)
      (drop : Bool) (N : Nat) (s : Slices Parent Ax Code Payload N),
    eachslice ops methods printing a (.integer (.native dim)) drop = .ok ⟨N, s⟩ →
    AxesOutcome ops methods a [dim] drop s ∧ SizeOutcome ops methods a [dim] drop s ∧
      SelectionOutcome methods [dim] drop s

def DropFalseKeepsSingletonAxes : Prop :=
  UnitAxisIsSingleton ∧ TupleEachsliceAxes ∧ IntegerEachsliceUsesItsAxis

def EachsliceTupleParentIdentity : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent)
      (dims : List (IntegerValue Code Payload)) (drop : Bool) (N : Nat)
      (s : Slices Parent Ax Code Payload N),
    eachslice ops methods printing a (.tuple dims) drop = .ok ⟨N, s⟩ → parent s = a

def EachsliceIntegerParentIdentity : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent)
      (dim : IntegerValue Code Payload) (drop : Bool) (N : Nat)
      (s : Slices Parent Ax Code Payload N),
    eachslice ops methods printing a (.integer dim) drop = .ok ⟨N, s⟩ → parent s = a

def EachsliceParentIdentity : Prop :=
  EachsliceTupleParentIdentity ∧ EachsliceIntegerParentIdentity

def EachslicePublicTupleSelectsRequestedDimensions : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dims : List I64)
      (drop : Bool) (N : Nat) (s : Slices Parent Ax Code Payload N),
    eachslice ops methods printing a (.tuple (nativeDims dims)) drop = .ok ⟨N, s⟩ →
    SelectionOutcome methods dims drop s

def EachslicePublicIntegerSelectsRequestedDimension : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dim : I64)
      (drop : Bool) (N : Nat) (s : Slices Parent Ax Code Payload N),
    eachslice ops methods printing a (.integer (.native dim)) drop = .ok ⟨N, s⟩ →
    SelectionOutcome methods [dim] drop s

def EachslicePublicSelectsRequestedDimensions : Prop :=
  EachslicePublicTupleSelectsRequestedDimensions ∧
    EachslicePublicIntegerSelectsRequestedDimension

def EachslicePublicContract : Prop :=
  EachsliceParentIdentity ∧ EachslicePublicSelectsRequestedDimensions ∧
    TupleEachsliceAxes ∧ TupleEachsliceSizeMatchesAxes ∧
    IntegerEachsliceUsesItsAxis

def EachrowMatrixUsesRows : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent)
      (N : Nat) (s : Slices Parent Ax Code Payload N),
    ops.ndims a = .ok (int 2) →
    eachrowMatrix ops methods printing a = .ok ⟨N, s⟩ →
    N = 1 ∧ parent s = a ∧
      (∃ axis, axesAt ops methods a (.native (int 1)) = .ok axis ∧ axes s = [axis]) ∧
      SelectionOutcome methods [int 1] true s

def EachcolMatrixUsesColumns : Prop :=
  ∀ {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (a : Parent)
      (N : Nat) (s : Slices Parent Ax Code Payload N),
    ops.ndims a = .ok (int 2) →
    eachcolMatrix ops methods printing a = .ok ⟨N, s⟩ →
    N = 1 ∧ parent s = a ∧
      (∃ axis, axesAt ops methods a (.native (int 2)) = .ok axis ∧ axes s = [axis]) ∧
      SelectionOutcome methods [int 2] true s

/-- `reshape(a::Array, dims::NTuple{2,Int})` of an `Array` vector, the installed
`reshapeArrayHeader`; the vector methods always pass two dimensions. -/
def arrayReshapeToMatrix {E T Ref : Type} (a : JuliaLean.base.reshapedarray.ArrayValue T 1 Ref) :
    List I64 → SM E (JuliaLean.base.reshapedarray.ArrayValue T 2 Ref)
  | [rows, cols] =>
      (JuliaLean.Bindings.base.reshapedarray.reshapeArrayHeader a #v[rows, cols]).mapError
        SliceErr.reshaped
  | _ => .error (.array (.julia (.methodError "reshape")))

/-- `size(a::Array)`, the installed header read. -/
def arraySize {T Ref : Type} (a : JuliaLean.base.reshapedarray.ArrayValue T 1 Ref) :
    JuliaLean.base.abstractarray.Result (List I64) :=
  .ok (JuliaLean.Bindings.base.reshapedarray.arrayHeaderSize a)

/-- The reshape result of a vector `eachrow`/`eachcol`: the vector type's own `size` and
`reshape(A, dims::Dims)` through the installed `sizeDim` and `reshape(A, dims::Int...)`. -/
def VectorReshape {E Vec Parent : Type} (size : Vec → JuliaLean.base.abstractarray.Result (List I64))
    (reshapeDims : Vec → List I64 → SM E Parent) (v : Vec) (b : Parent) : Prop :=
  ∃ rows,
    JuliaLean.base.abstractarray.sizeDim
      (fun d : I64 => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 d))
      size v (int 1) = .ok rows ∧
    JuliaLean.base.reshapedarray.reshapeIntVarargs reshapeDims v [rows, int 1] = .ok b

def EachrowVectorUsesRows : Prop :=
  (∀ {E V Ty Vec Parent Ax Code : Type} {Payload : Code → Type}
      (size : Vec → JuliaLean.base.abstractarray.Result (List I64))
      (reshapeDims : Vec → List I64 → SM E Parent)
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (v : Vec)
      (N : Nat) (s : Slices Parent Ax Code Payload N),
    eachrowVector size reshapeDims ops methods printing v = .ok ⟨N, s⟩ →
    N = 1 ∧ VectorReshape size reshapeDims v (parent s) ∧
      SelectionOutcome methods [int 1] true s) ∧
  (∀ {E V Ty T Ref Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) (JuliaLean.base.reshapedarray.ArrayValue T 2 Ref) Ax)
      (methods : IntegerMethods Code Payload) (printing : IntegerPrinting E V Ty Code Payload)
      (v : JuliaLean.base.reshapedarray.ArrayValue T 1 Ref) (N : Nat)
      (s : Slices (JuliaLean.base.reshapedarray.ArrayValue T 2 Ref) Ax Code Payload N),
    eachrowVector arraySize arrayReshapeToMatrix ops methods printing v = .ok ⟨N, s⟩ →
    (parent s).ref = v.ref ∧ (parent s).dims.toList = [v.dims[0], int 1])

def EachcolVectorUsesSingleColumn : Prop :=
  (∀ {E V Ty Vec Parent Ax Code : Type} {Payload : Code → Type}
      (size : Vec → JuliaLean.base.abstractarray.Result (List I64))
      (reshapeDims : Vec → List I64 → SM E Parent)
      (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
      (printing : IntegerPrinting E V Ty Code Payload) (v : Vec)
      (N : Nat) (s : Slices Parent Ax Code Payload N),
    eachcolVector size reshapeDims ops methods printing v = .ok ⟨N, s⟩ →
    N = 1 ∧ VectorReshape size reshapeDims v (parent s) ∧
      SelectionOutcome methods [int 2] true s) ∧
  (∀ {E V Ty T Ref Ax Code : Type} {Payload : Code → Type}
      (ops : SliceParentOps (SM E) (JuliaLean.base.reshapedarray.ArrayValue T 2 Ref) Ax)
      (methods : IntegerMethods Code Payload) (printing : IntegerPrinting E V Ty Code Payload)
      (v : JuliaLean.base.reshapedarray.ArrayValue T 1 Ref) (N : Nat)
      (s : Slices (JuliaLean.base.reshapedarray.ArrayValue T 2 Ref) Ax Code Payload N),
    eachcolVector arraySize arrayReshapeToMatrix ops methods printing v = .ok ⟨N, s⟩ →
    (parent s).ref = v.ref ∧ (parent s).dims.toList = [v.dims[0], int 1])

def SlicesParentIdentity : Prop :=
  EachsliceParentIdentity ∧ EachrowMatrixUsesRows ∧ EachrowVectorUsesRows ∧
    EachcolMatrixUsesColumns ∧ EachcolVectorUsesSingleColumn

def SlicesConstructBehavior : Prop :=
  SlicesConstructorInvariant ∧ TupleEachsliceContract ∧
    IntegerEachsliceUsesItsAxis ∧ EachslicePublicContract ∧ SlicesParentIdentity

/-- `_slice_index(s, c...)`: colon entries stay colons; an `Int` entry `l` reads `c[l]`; another
`Integer` entry reads `c[convert(Int, l)]` with the entry type's own conversion. -/
def SliceIndexFollowsSlicemap : Prop :=
  ∀ {E Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
      (methods : IntegerMethods Code Payload) (s : Slices Parent Ax Code Payload N)
      (coordinates : List I64) (selected : List (Option I64)),
    (sliceIndex methods s coordinates : SM E _) = .ok selected →
    selected.length = s.slicemap.length ∧
    ∀ parentDimension, parentDimension < s.slicemap.length →
      match s.slicemap[parentDimension]? with
      | some none => selected[parentDimension]? = some none
      | some (some (.native l)) =>
          1 ≤ l.val ∧ ∃ coordinate,
            coordinates[(l.val - 1).toNat]? = some coordinate ∧
              selected[parentDimension]? = some (some coordinate)
      | some (some (.other code l)) =>
          ∃ j coordinate, methods.convertInt code l = .ok j ∧ 1 ≤ j.val ∧
            coordinates[(j.val - 1).toNat]? = some coordinate ∧
              selected[parentDimension]? = some (some coordinate)
      | none => False

/-- A missing coordinate of an `Int` entry throws `BoundsError` when every entry is a colon or an
`Int`, and the first non-colon entry's conversion error propagates unchanged. -/
def SliceIndexRejectsMissingCoordinates : Prop :=
  (∀ {E Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
      (methods : IntegerMethods Code Payload) (s : Slices Parent Ax Code Payload N)
      (coordinates : List I64) (parentDimension : Nat) (l : I64),
    (∀ entry, entry ∈ s.slicemap → ∀ code x, entry ≠ some (.other code x)) →
    s.slicemap[parentDimension]? = some (some (.native l)) →
    (l.val < 1 ∨ coordinates[(l.val - 1).toNat]? = none) →
    (sliceIndex methods s coordinates : SM E _) = .error (.tuple (.julia .boundsError))) ∧
  (∀ {E Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
      (methods : IntegerMethods Code Payload) (s : Slices Parent Ax Code Payload N)
      (coordinates : List I64) (k : Nat) (code : Code) (l : Payload code)
      (rest : List (Option (IntegerValue Code Payload))) (e : JlError),
    s.slicemap = List.replicate k none ++ some (.other code l) :: rest →
    methods.convertInt code l = .error e →
    (sliceIndex methods s coordinates : SM E _) = .error (.array (.julia e)))

def SliceIndexBehavior : Prop :=
  SliceIndexRejectsMissingCoordinates ∧ SliceIndexFollowsSlicemap

/-- Blocked on the `view`/`checkbounds` bindings: keeps the parent-read law of the earlier
statement. -/
def SlicesElementsAreParentViews : Prop :=
  ∀ {E Parent View Value Element Ax Code : Type} {Payload : Code → Type} {N : Nat}
      (access : SliceAccessOps (SM E) Parent View Value)
      (reads : ParentReads E Parent View Value Element)
      (methods : IntegerMethods Code Payload) (s : Slices Parent Ax Code Payload N)
      (indices : IntegerIndices N)
      (checkbounds : Slices Parent Ax Code Payload N → IntegerIndices N → SM E Unit),
    ParentViewGetindexLaw access reads →
    checkbounds s indices = .ok () →
    ((∀ selected viewValue,
      (sliceIndex methods s indices.values : SM E _) = .ok selected →
      access.view s.parent selected = .ok viewValue →
      getindex checkbounds access methods s indices = .ok viewValue ∧
      ∀ inner parentCoordinates,
        ParentCoordinatesFollowSelectors selected inner parentCoordinates →
        reads.getindexView viewValue inner = reads.getindexParent s.parent parentCoordinates) ∧
    (∀ selected error,
      (sliceIndex methods s indices.values : SM E _) = .ok selected →
      access.view s.parent selected = .error error →
      getindex checkbounds access methods s indices = .error error))

/-- Blocked on the parent `setindex!`/`checkbounds` bindings: keeps the parent-effect law of the
earlier statement. -/
def SlicesAssignmentTargetsMappedParent : Prop :=
  ∀ {E Parent View Value Element Ax Code : Type} {Payload : Code → Type} {N : Nat}
      (access : SliceAccessOps (SM E) Parent View Value)
      (reads : ParentReads E Parent View Value Element)
      (methods : IntegerMethods Code Payload) (s : Slices Parent Ax Code Payload N)
      (value : Value) (indices : IntegerIndices N)
      (checkbounds : Slices Parent Ax Code Payload N → IntegerIndices N → SM E Unit),
    ParentSetindexEffectLaw access reads →
    checkbounds s indices = .ok () →
    ∀ selected,
      (sliceIndex methods s indices.values : SM E _) = .ok selected →
      setindex! checkbounds access methods s value indices = .ok value →
      ∃ updatedParent,
        access.setindexParent s.parent selected value = .ok value ∧
        (∀ inner parentCoordinates,
          ParentCoordinatesFollowSelectors selected inner parentCoordinates →
          reads.getindexParent updatedParent parentCoordinates =
            reads.getindexValue value inner) ∧
        (∀ parentCoordinates,
          (∀ inner, ¬ ParentCoordinatesFollowSelectors selected inner parentCoordinates) →
          reads.getindexParent updatedParent parentCoordinates =
            reads.getindexParent s.parent parentCoordinates)

def SlicesAccessesInBounds : Prop :=
  SliceIndexBehavior ∧ SlicesElementsAreParentViews ∧
    SlicesAssignmentTargetsMappedParent

private def provenEntry (id : String) (juliaFns : List String)
    (statement source : String) (prop thm : Lean.Name) : Entry :=
  { id
    juliaFile := "base/slicearray.jl"
    juliaFns
    statement
    source
    status := .proven
    prop
    thm := some thm }

end JuliaLean.Proofs.base.slicearray

section
/-! Completed batch 4 group 10 slice-array proofs. All helper declarations are local to the group namespace. -/


namespace JuliaLean.ChatGPT.Batch4.Group10

open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

/-- The canonical list of consecutive positive native indices. -/
def sa_indices (n : I64) : List I64 :=
  (List.range n.val.toNat).map fun p : Nat => int ((p : Int) + 1)

theorem sa_int_val (z : Int) (h : IntTy.i64.min ≤ z ∧ z ≤ IntTy.i64.max) :
    (int z).val = z := wrapInt_of_inRange .i64 z h

theorem sa_unitRange (n : I64) (hn : 0 ≤ n.val) :
    JuliaLean.base.range.unitRangeList (int 1) n = sa_indices n := by
  unfold JuliaLean.base.range.unitRangeList sa_indices
  change (if n.val < 1 then [] else
    (List.range (n.val - 1 + 1).toNat).map
      (fun k : Nat => int 1 + JuliaLean.base.range.jint (k : Int))) = _
  by_cases hz : n.val = 0
  · simp only [hz]
    rfl
  · have hp : ¬ n.val < 1 := by omega
    rw [if_neg hp]
    have hsub : n.val - 1 + 1 = n.val := by omega
    rw [hsub]
    apply List.map_congr_left
    intro p hp
    have hp' : p < n.val.toNat := List.mem_range.mp hp
    have hb := n.property
    have hmin : IntTy.i64.min ≤ 0 := by decide
    have hpn : (p : Int) < n.val := by omega
    have hi : (JuliaLean.base.range.jint (p : Int)).val = (p : Int) :=
      wrapInt_of_inRange .i64 (p : Int) (by constructor <;> omega)
    apply Subtype.ext
    change wrapInt .i64 ((int 1).val + (JuliaLean.base.range.jint (p : Int)).val) = _
    rw [hi]
    change wrapInt .i64 (1 + (p : Int)) = wrapInt .i64 ((p : Int) + 1)
    rw [Int.add_comm]

/-- Normal form of the installed native ntuple method for a nonnegative length. -/
theorem sa_ntuple_nonneg {E α : Type} (f : I64 → SM E α) (n : I64)
    (hn : 0 ≤ n.val) :
    JuliaLean.base.ntuple.ntupleInt f n ntupleRange =
      (sa_indices n).mapM f := by
  by_cases h0 : n.val = 0
  · have he : n = int 0 := Subtype.ext h0
    subst n
    rfl
  by_cases h1 : n.val = 1
  · have he : n = int 1 := Subtype.ext h1
    subst n
    rfl
  by_cases h2 : n.val = 2
  · have he : n = int 2 := Subtype.ext h2
    subst n
    rfl
  by_cases h3 : n.val = 3
  · have he : n = int 3 := Subtype.ext h3
    subst n
    rfl
  by_cases h4 : n.val = 4
  · have he : n = int 4 := Subtype.ext h4
    subst n
    rfl
  by_cases h5 : n.val = 5
  · have he : n = int 5 := Subtype.ext h5
    subst n
    rfl
  by_cases h6 : n.val = 6
  · have he : n = int 6 := Subtype.ext h6
    subst n
    rfl
  by_cases h7 : n.val = 7
  · have he : n = int 7 := Subtype.ext h7
    subst n
    rfl
  by_cases h8 : n.val = 8
  · have he : n = int 8 := Subtype.ext h8
    subst n
    rfl
  by_cases h9 : n.val = 9
  · have he : n = int 9 := Subtype.ext h9
    subst n
    rfl
  by_cases h10 : n.val = 10
  · have he : n = int 10 := Subtype.ext h10
    subst n
    rfl
  simp only [JuliaLean.base.ntuple.ntupleInt, h0, h1, h2, h3, h4, h5, h6,
    h7, h8, h9, h10, ite_false, JuliaLean.base.ntuple._ntuple, hn, ite_true,
    ntupleRange, pure, Except.pure, bind, Except.bind]
  rw [sa_unitRange n hn]

theorem sa_ntuple_negative {E α : Type} (f : I64 → SM E α) (n : I64)
    (hn : n.val < 0) :
    JuliaLean.base.ntuple.ntupleInt f n ntupleRange =
      .error (.ntuple (.base (.argumentError
        ("tuple length should be ≥ 0, got " ++ toString n.val)))) := by
  have h0 : n.val ≠ 0 := by omega
  have h1 : n.val ≠ 1 := by omega
  have h2 : n.val ≠ 2 := by omega
  have h3 : n.val ≠ 3 := by omega
  have h4 : n.val ≠ 4 := by omega
  have h5 : n.val ≠ 5 := by omega
  have h6 : n.val ≠ 6 := by omega
  have h7 : n.val ≠ 7 := by omega
  have h8 : n.val ≠ 8 := by omega
  have h9 : n.val ≠ 9 := by omega
  have h10 : n.val ≠ 10 := by omega
  have hn' : ¬ n.val ≥ 0 := by omega
  simp only [JuliaLean.base.ntuple.ntupleInt, h0, h1, h2, h3, h4, h5, h6,
    h7, h8, h9, h10, ite_false, JuliaLean.base.ntuple._ntuple, hn', ite_false]
  rfl

theorem sa_ntuple_success {E α : Type} (f : I64 → SM E α) (n : I64) (ys : List α)
    (h : JuliaLean.base.ntuple.ntupleInt f n ntupleRange = .ok ys) :
    0 ≤ n.val ∧ (sa_indices n).mapM f = .ok ys := by
  by_cases hn : 0 ≤ n.val
  · exact ⟨hn, (sa_ntuple_nonneg f n hn).symm.trans h⟩
  · rw [sa_ntuple_negative f n (by omega)] at h
    cases h

end JuliaLean.ChatGPT.Batch4.Group10


namespace JuliaLean.ChatGPT.Batch4.Group10

open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

/-- The signed value recovered from a native dimension's bit pattern. -/
theorem sc_fromJInt_toInt (x : I64) : (JuliaLean.C.fromJInt x).toInt = x.val := by
  have hx := x.property
  simp only [JuliaLean.C.fromJInt, BitVec.toInt_ofInt]
  simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, Int.bmod_def] <;> split <;> omega

/-- Re-encoding a native value preserves it. -/

theorem sc_lit_val_self (x : I64) : JInt.lit .i64 x.val = x := by
  apply Subtype.ext
  exact wrapInt_of_inRange .i64 x.val x.property


theorem sc_int_le_eq (x y : I64) :
    JuliaLean.base.int.le x y = decide (x.val ≤ y.val) := by
  change JuliaLean.base.int.leSame
    (JuliaLean.base.int.widenTo .i64 x) (JuliaLean.base.int.widenTo .i64 y) = _
  change JuliaLean.base.int.leSame (JInt.lit .i64 x.val) (JInt.lit .i64 y.val) = _
  rw [sc_lit_val_self, sc_lit_val_self]
  change decide ((JuliaLean.C.fromJInt x).toInt ≤ (JuliaLean.C.fromJInt y).toInt) = _
  rw [sc_fromJInt_toInt, sc_fromJInt_toInt]


theorem sc_int_lt_eq (x y : I64) :
    JuliaLean.base.int.lt x y = decide (x.val < y.val) := by
  change JuliaLean.base.int.ltSame
    (JuliaLean.base.int.widenTo .i64 x) (JuliaLean.base.int.widenTo .i64 y) = _
  change JuliaLean.base.int.ltSame (JInt.lit .i64 x.val) (JInt.lit .i64 y.val) = _
  rw [sc_lit_val_self, sc_lit_val_self]
  change decide ((JuliaLean.C.fromJInt x).toInt < (JuliaLean.C.fromJInt y).toInt) = _
  rw [sc_fromJInt_toInt, sc_fromJInt_toInt]


theorem sc_int_eq_eq (x y : I64) :
    JuliaLean.base.int.eq x y = decide (x.val = y.val) := by
  change JuliaLean.base.int.eqSame
    (JuliaLean.base.int.widenTo .i64 x) (JuliaLean.base.int.widenTo .i64 y) = _
  change JuliaLean.base.int.eqSame (JInt.lit .i64 x.val) (JInt.lit .i64 y.val) = _
  rw [sc_lit_val_self, sc_lit_val_self]
  change (JuliaLean.C.fromJInt x == JuliaLean.C.fromJInt y) = _
  by_cases h : x.val = y.val
  · have heq : x = y := Subtype.ext h
    simp only [heq, BEq.rfl, decide_true]
  · have hb : JuliaLean.C.fromJInt x ≠ JuliaLean.C.fromJInt y := by
      intro heq
      have he := congrArg BitVec.toInt heq
      rw [sc_fromJInt_toInt, sc_fromJInt_toInt] at he
      exact h he
    rw [decide_eq_false h]
    exact beq_false_of_ne hb


theorem sc_anyTupleLoop_any {α : Type} (p : α → Bool) (xs : List α)
    (colon : JuliaLean.base.anyall.Colon) :
    JuliaLean.base.anyall.anyTupleLoop (ε := Empty) (fun y => .ok (.bool (p y))) xs colon =
      .ok (some (xs.any p)) := by
  unfold JuliaLean.base.anyall.anyTupleLoop
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x <;>
        simp only [JuliaLean.base.anyall.anyTupleLoop.loop, hp, List.any_cons,
          Bool.false_or, Bool.true_or, ih]

theorem sc_anyTupleStep_any {α : Type} (p : α → Bool) (xs : List α) :
    JuliaLean.base.anyall.anyTupleStep (ε := Empty) JuliaLean.base.anyall.anyTupleDone
      (fun y => .ok (.bool (p y))) false xs = .ok (some (xs.any p)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x <;>
        simp only [JuliaLean.base.anyall.anyTupleStep, hp, List.any_cons,
          Bool.false_or, Bool.true_or, ih]

theorem sc_inTupleHelper_any {A : Type} (eq : A → A → Bool) (x : A) (xs : List A) :
    JuliaLean.base.operators.inTupleHelper (Elem := fun _ : Unit => A)
      (fun {_} y x => if eq y x then .true else .false) x (asTuple xs) .false =
      if xs.any (fun y => eq y x) then .true else .false := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      cases hp : eq y x <;>
        simp only [asTuple, JuliaLean.base.operators.inTupleHelper, hp,
          Bool.false_eq_true, ite_false, ite_true, JuliaLean.base.operators.Truth.or,
          List.any_cons, Bool.false_or, Bool.true_or, ih]

theorem sc_anyTuple_any {Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) {FT XT : Type} {fTag : FT} {xTag : XT}
    (f : JuliaLean.base.operators.Fix 2
      (IntegerValue Code Payload → IntegerValue Code Payload → Unit → Bool)
      (IntegerValue Code Payload) fTag xTag)
    (xs : List (IntegerValue Code Payload)) :
    anyTuple methods f xs = .ok (some (xs.any (fun y => f.f y f.x ()))) := by
  unfold anyTuple JuliaLean.base.anyall.anyTupleMethod
  split
  · exact sc_anyTupleLoop_any _ _ _
  · exact sc_anyTupleStep_any _ _

theorem sc_integerIn_any {Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (x : IntegerValue Code Payload)
    (xs : List (IntegerValue Code Payload)) :
    integerIn methods x xs = xs.any (fun y => integerEq methods y x) := by
  unfold integerIn
  split
  · unfold JuliaLean.base.operators.inTuple
    rw [sc_inTupleHelper_any]
    cases xs.any (fun y => integerEq methods y x) <;> rfl
  · change (match anyTuple methods (JuliaLean.base.operators.fixEqual (integerEq methods) x) xs with
      | .ok (some true) => true
      | _ => false) = _
    rw [sc_anyTuple_any]
    change (match Except.ok (ε := JuliaLean.base.anyall.AnyAllError Empty)
        (some (xs.any (fun y => integerEq methods y x))) with
      | .ok (some true) => true
      | _ => false) = _
    cases xs.any (fun y => integerEq methods y x) <;> rfl

theorem sc_integerIn_native {Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (d : I64) (dims : List I64) :
    integerIn methods (.native d) (nativeDims dims) =
      dims.any (fun x => decide (x.val = d.val)) := by
  rw [sc_integerIn_any]
  simp only [nativeDims, List.any_map, Function.comp_def, integerEq, sc_int_eq_eq]

end JuliaLean.ChatGPT.Batch4.Group10
namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

def sc_printDimensionError {E V Ty Code : Type} {Payload : Code → Type}
    (printing : IntegerPrinting E V Ty Code Payload)
    (xs : List (JuliaLean.base.strings.io.StrArg E V)) : SM E Unit := do
  let message ← printString printing xs
  throwThe ArrayError (.dimensionMismatch message)

theorem sc_printDimensionError_class {E V Ty Code : Type} {Payload : Code → Type}
    (printing : IntegerPrinting E V Ty Code Payload)
    (xs : List (JuliaLean.base.strings.io.StrArg E V)) :
    (∃ message, sc_printDimensionError printing xs = .error (.array (.dimensionMismatch message))) ∨
    (∃ e, sc_printDimensionError printing xs = .error (.print e)) := by
  unfold sc_printDimensionError printString
  cases hp : JuliaLean.base.strings.io.printToString printing.digits printing.displaySize
      printing.anyOps xs with
  | error e => exact Or.inr ⟨e, rfl⟩
  | ok s => exact Or.inl ⟨messageText s, rfl⟩

theorem sc_check_cons {E V Ty Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (printing : IntegerPrinting E V Ty Code Payload)
    (d : I64) (dims : List I64) :
    (sliceCheckDims methods printing (nativeDims (d :: dims)) : SM E Unit) =
      if 1 ≤ d.val then
        if dims.any (fun x => decide (x.val = d.val)) then
          sc_printDimensionError printing [.string dimensionsText, tupleArg printing (nativeDims dims),
            .string notUniqueText]
        else sliceCheckDims methods printing (nativeDims dims)
      else sc_printDimensionError printing [.string invalidDimensionText, dimensionArg printing (.native d)] := by
  change sliceCheckDims methods printing (.native d :: nativeDims dims) = _
  simp only [sliceCheckDims, integerLe, sc_int_le_eq, sc_integerIn_native]
  have h1 : (int 1).val = 1 := rfl
  rw [h1]
  by_cases hd : 1 ≤ d.val
  · simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    cases hm : dims.any (fun x => decide (x.val = d.val))
    · simp only [hm, Bool.false_eq_true, ite_false, bind, Except.bind, pure, Except.pure]
    · simp only [hm, ite_true]
      unfold sc_printDimensionError
      cases hp : (printString printing
          [.string dimensionsText, tupleArg printing (nativeDims dims), .string notUniqueText] : SM E String) <;>
        simp only [hp, bind, Except.bind] <;> rfl
  · simp only [hd, decide_false, Bool.not_false, ite_true, ite_false]
    unfold sc_printDimensionError
    cases hp : (printString printing
        [.string invalidDimensionText, dimensionArg printing (.native d)] : SM E String) <;>
      simp only [hp, bind, Except.bind] <;> rfl

theorem sc_any_val_eq_false (dims : List I64) (d : I64) :
    dims.any (fun x => decide (x.val = d.val)) = false ↔
      ∀ x, x ∈ dims → d.val ≠ x.val := by
  induction dims with
  | nil => simp only [List.any_nil, List.not_mem_nil, false_implies, implies_true, iff_self]
  | cons x xs ih =>
      simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not, ih,
        List.mem_cons, forall_eq_or_imp]
      constructor
      · intro ⟨h1, h2⟩
        exact ⟨fun h => h1 h.symm, h2⟩
      · intro ⟨h1, h2⟩
        exact ⟨fun h => h1 h.symm, h2⟩

theorem sc_check_success {E V Ty Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (printing : IntegerPrinting E V Ty Code Payload)
    (dims : List I64)
    (h : (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) = .ok ()) :
    (∀ d, d ∈ dims → 1 ≤ d.val) ∧ List.Pairwise (fun l r : I64 => l.val ≠ r.val) dims := by
  induction dims with
  | nil => exact ⟨fun d hd => False.elim (List.not_mem_nil hd), .nil⟩
  | cons d dims ih =>
      rw [sc_check_cons] at h
      by_cases hd : 1 ≤ d.val
      · rw [if_pos hd] at h
        cases hm : dims.any (fun x => decide (x.val = d.val)) with
        | true =>
            rw [hm, if_pos rfl] at h
            obtain ⟨msg, he⟩ | ⟨e, he⟩ := sc_printDimensionError_class printing
              [.string dimensionsText, tupleArg printing (nativeDims dims), .string notUniqueText]
            · rw [he] at h; cases h
            · rw [he] at h; cases h
        | false =>
            rw [hm, if_neg Bool.false_ne_true] at h
            obtain ⟨hpos, hpair⟩ := ih h
            refine ⟨?_, List.Pairwise.cons ((sc_any_val_eq_false dims d).mp hm) hpair⟩
            intro x hx
            obtain rfl | hx := List.mem_cons.mp hx
            · exact hd
            · exact hpos x hx
      · rw [if_neg hd] at h
        obtain ⟨msg, he⟩ | ⟨e, he⟩ := sc_printDimensionError_class printing
          [.string invalidDimensionText, dimensionArg printing (.native d)]
        · rw [he] at h; cases h
        · rw [he] at h; cases h


theorem sc_check_class {E V Ty Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (printing : IntegerPrinting E V Ty Code Payload)
    (dims : List I64) :
    (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) = .ok () ∨
    (∃ message, (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) =
      .error (.array (.dimensionMismatch message))) ∨
    (∃ e, (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) = .error (.print e)) := by
  induction dims with
  | nil => exact Or.inl rfl
  | cons d dims ih =>
      rw [sc_check_cons]
      by_cases hd : 1 ≤ d.val
      · rw [if_pos hd]
        cases hm : dims.any (fun x => decide (x.val = d.val)) with
        | false =>
            simp only [Bool.false_eq_true, ite_false]
            exact ih
        | true =>
            simp only [ite_true]
            exact Or.inr (sc_printDimensionError_class printing _)
      · rw [if_neg hd]
        exact Or.inr (sc_printDimensionError_class printing _)

theorem sc_check_complete {E V Ty Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (printing : IntegerPrinting E V Ty Code Payload)
    (dims : List I64)
    (hpos : ∀ d, d ∈ dims → 1 ≤ d.val)
    (hpair : List.Pairwise (fun l r : I64 => l.val ≠ r.val) dims) :
    (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) = .ok () := by
  induction dims with
  | nil => rfl
  | cons d dims ih =>
      have hd := hpos d (by simp only [List.mem_cons, true_or])
      have hp := List.pairwise_cons.mp hpair
      have hn := (sc_any_val_eq_false dims d).mpr hp.1
      rw [sc_check_cons, if_pos hd, hn, if_neg Bool.false_ne_true]
      exact ih (fun x hx => hpos x (List.mem_cons_of_mem d hx)) hp.2

theorem MultidimcovSliceL52Check_proven : JuliaLean.Proofs.base.slicearray.InvalidDimensionsThrow := by
  intro E V Ty Code Payload methods printing dims
  constructor
  · intro hbad
    obtain hok | herr | herr := sc_check_class methods printing dims
    · obtain ⟨hpos, hpair⟩ := sc_check_success methods printing dims hok
      obtain ⟨d, hd, hlt⟩ | hnotpair := hbad
      · have := hpos d hd
        omega
      · exact False.elim (hnotpair hpair)
    · obtain ⟨message, he⟩ := herr
      rw [he]
      trivial
    · obtain ⟨e, he⟩ := herr
      rw [he]
      trivial
  · exact sc_check_complete methods printing dims

theorem MultidimcovSlicearrayFaithful52_proven : JuliaLean.Proofs.base.slicearray.InvalidDimensionsThrow :=
  MultidimcovSliceL52Check_proven

end JuliaLean.ChatGPT.Batch4.Group10

namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

theorem sc_constructor_fields {E Parent Ax Code : Type} {Payload : Code → Type}
    (ops : SliceParentOps (SM E) Parent Ax) (a : Parent)
    (slicemap : List (Option (IntegerValue Code Payload))) (outerAxes parentAxes : List Ax)
    (N : Nat) (s : Slices Parent Ax Code Payload N)
    (h : (⟨outerAxes.length, {
      parent := a
      slicemap := slicemap
      axes := outerAxes
      axes_length := rfl
      viewType := ops.promoteView ops.parentType (List.zipWith
        (fun axis entry => match entry with
          | none => SliceViewArgument.colon
          | some _ => .index (ops.axisEltype axis)) parentAxes slicemap) }⟩ :
       SliceConstruction Parent Ax Code Payload) = ⟨N, s⟩) :
    parent s = a ∧ s.slicemap = slicemap ∧ axes s = outerAxes ∧ N = outerAxes.length ∧
       s.viewType = ops.promoteView ops.parentType (List.zipWith
          (fun axis entry => match entry with
            | none => SliceViewArgument.colon
            | some _ => .index (ops.axisEltype axis)) parentAxes slicemap) := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def sc_guarded_build {E α β : Type} (rank : SM E I64) (check : I64 → Bool)
    (getAxes : SM E α) (build : α → β) : SM E β := do
  if !(check (← rank)) then
    throwThe ArrayError (.julia (.argumentError
      "Slices cannot be constructed with a slicemap of fewer elements than the parent has dimensions"))
  let xs ← getAxes
  pure (build xs)

theorem sc_guarded_build_success {E α β : Type} (rank : SM E I64) (check : I64 → Bool)
    (getAxes : SM E α) (build : α → β) (result : β)
    (h : sc_guarded_build rank check getAxes build = .ok result) :
    ∃ xs, getAxes = .ok xs ∧ build xs = result := by
  unfold sc_guarded_build at h
  cases hr : rank with
  | error e => simp only [hr, bind, Except.bind] at h; cases h
  | ok n =>
    simp only [hr, bind, Except.bind] at h
    cases hc : check n with
    | false => simp only [hc, Bool.not_false, ite_true] at h; cases h
    | true =>
      simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false] at h
      cases ha : getAxes with
      | error e => simp only [ha, bind, Except.bind] at h; cases h
      | ok xs =>
        simp only [ha, bind, Except.bind, pure, Except.pure] at h
        exact ⟨xs, rfl, Except.ok.inj h⟩

theorem sc_guarded_build_rejects {E α β : Type} (rank : SM E I64) (check : I64 → Bool)
    (getAxes : SM E α) (build : α → β) (n : I64)
    (hr : rank = .ok n) (hc : check n = false) :
    sc_guarded_build rank check getAxes build =
      .error (.array (.julia (.argumentError
        "Slices cannot be constructed with a slicemap of fewer elements than the parent has dimensions"))) := by
  simp only [sc_guarded_build, hr, bind, Except.bind, hc, Bool.not_false, ite_true]
  rfl

theorem sc_constructor_preserves : SlicesConstructorPreservesInput := by
  intro E Parent Ax Code Payload ops methods a slicemap outerAxes N s h
  have hs : sc_guarded_build (ops.ndims a)
      (fun n => JuliaLean.base.int.le n (int slicemap.length))
      (JuliaLean.base.ntuple.ntupleInt
        (fun d => axesAt ops methods a (.native d)) (int slicemap.length) ntupleRange)
      (fun parentAxes => (⟨outerAxes.length, {
        parent := a
        slicemap := slicemap
        axes := outerAxes
        axes_length := rfl
        viewType := ops.promoteView ops.parentType (List.zipWith
          (fun axis entry => match entry with
            | none => SliceViewArgument.colon
            | some _ => .index (ops.axisEltype axis)) parentAxes slicemap) }⟩ :
        SliceConstruction Parent Ax Code Payload)) = .ok ⟨N, s⟩ := h
  obtain ⟨parentAxes, hp, he⟩ := sc_guarded_build_success _ _ _ _ _ hs
  have hf := sc_constructor_fields ops a slicemap outerAxes parentAxes N s he
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, parentAxes, hp, hf.2.2.2.2⟩

theorem sc_constructor_rejects : SlicesConstructorRejectsShortMap := by
  intro E Parent Ax Code Payload ops methods a slicemap outerAxes n hn hshort
  have hfit : IntTy.i64.min ≤ (slicemap.length : Int) ∧
      (slicemap.length : Int) ≤ IntTy.i64.max := by
    have hnmax := n.property.2
    constructor
    · have hmin : IntTy.i64.min ≤ 0 := by decide
      exact Int.le_trans hmin (Int.natCast_nonneg _)
    · omega
  have hval : (int slicemap.length).val = (slicemap.length : Int) :=
    wrapInt_of_inRange .i64 _ hfit
  have hle : JuliaLean.base.int.le n (int slicemap.length) = false := by
    rw [sc_int_le_eq, hval]
    exact decide_eq_false (by omega)
  refine ⟨"Slices cannot be constructed with a slicemap of fewer elements than the parent has dimensions", ?_⟩
  exact sc_guarded_build_rejects (ops.ndims a)
    (fun n => JuliaLean.base.int.le n (int slicemap.length))
    (JuliaLean.base.ntuple.ntupleInt
      (fun d => axesAt ops methods a (.native d)) (int slicemap.length) ntupleRange)
    (fun parentAxes => (⟨outerAxes.length, {
      parent := a
      slicemap := slicemap
      axes := outerAxes
      axes_length := rfl
      viewType := ops.promoteView ops.parentType (List.zipWith
        (fun axis entry => match entry with
          | none => SliceViewArgument.colon
          | some _ => .index (ops.axisEltype axis)) parentAxes slicemap) }⟩ :
      SliceConstruction Parent Ax Code Payload)) n hn hle


theorem MultidimcovSliceL41Constructor_proven : JuliaLean.Proofs.base.slicearray.SlicesConstructorInvariant :=
  ⟨sc_constructor_rejects, sc_constructor_preserves⟩

theorem MultidimcovSlicearrayFaithful41_proven : JuliaLean.Proofs.base.slicearray.SlicesConstructorInvariant :=
  MultidimcovSliceL41Constructor_proven


end JuliaLean.ChatGPT.Batch4.Group10


namespace JuliaLean.ChatGPT.Batch4.Group10

open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

/-- Successful effectful maps preserve length and realize every indexed input/output pair. -/
theorem sliceMapMOk {α β ε : Type} (f : α → Except ε β) (xs : List α) :
    ∀ ys, xs.mapM f = .ok ys →
      ys.length = xs.length ∧
      ∀ p, p < xs.length → ∃ x y,
        xs[p]? = some x ∧ ys[p]? = some y ∧ f x = .ok y := by
  induction xs with
  | nil =>
      intro ys h
      have hy : [] = ys := Except.ok.inj h
      subst ys
      exact ⟨rfl, fun p hp => False.elim (Nat.not_lt_zero p hp)⟩
  | cons x xs ih =>
      intro ys h
      cases hx : f x with
      | error e =>
          simp only [List.mapM_cons, hx, Bind.bind, Except.bind] at h
          cases h
      | ok y =>
          cases hr : xs.mapM f with
          | error e =>
              simp only [List.mapM_cons, hx, hr, Bind.bind, Except.bind] at h
              cases h
          | ok rest =>
              have hy : y :: rest = ys := by
                simpa only [List.mapM_cons, hx, hr, Bind.bind, Except.bind,
                  Pure.pure, Except.pure, Except.ok.injEq] using h
              subst ys
              obtain ⟨hl, hp⟩ := ih rest hr
              refine ⟨by simp only [List.length_cons, hl], ?_⟩
              intro p hlt
              cases p with
              | zero => exact ⟨x, y, rfl, rfl, hx⟩
              | succ p =>
                  obtain ⟨x', y', hxi, hyi, hxy⟩ := hp p (Nat.lt_of_succ_lt_succ hlt)
                  exact ⟨x', y', hxi, hyi, hxy⟩

/-- The result of mapping one slice-map entry. -/
def sliceEntry {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (coordinates : List I64) :
    Option (IntegerValue Code Payload) → SM E (Option I64)
  | none => pure none
  | some (.native l) => do
      let coordinate ← liftTuple (JuliaLean.base.tuple.getindexInt coordinates l)
      pure (some coordinate)
  | some (.other code l) => do
      let coordinate ← JuliaLean.base.tuple.getindexInteger
        (convert := ⟨fun l => liftJl (methods.convertInt code l)⟩) coordinates l liftTuple
      pure (some coordinate)

theorem sliceIndexMapM {E Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (methods : IntegerMethods Code Payload) (s : Slices Parent Ax Code Payload N)
    (coordinates : List I64) :
    (sliceIndex methods s coordinates : SM E _) =
      s.slicemap.mapM (sliceEntry methods coordinates) := rfl

theorem sliceNativeEntry {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (coordinates : List I64) (l : I64) :
    (sliceEntry methods coordinates (some (.native l)) : SM E _) =
      if 1 ≤ l.val then
        match coordinates[(l.val - 1).toNat]? with
        | some coordinate => .ok (some coordinate)
        | none => .error (.tuple (.julia .boundsError))
      else .error (.tuple (.julia .boundsError)) := by
  simp only [sliceEntry, JuliaLean.base.tuple.getindexInt, JuliaLean.base.tuple.getfield]
  split
  · cases coordinates[(l.val - 1).toNat]? <;> rfl
  · rfl

theorem sliceOtherEntry {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (coordinates : List I64)
    (code : Code) (l : Payload code) :
    (sliceEntry methods coordinates (some (.other code l)) : SM E _) =
      match methods.convertInt code l with
      | .ok j => sliceEntry methods coordinates (some (.native j))
      | .error e => .error (.array (.julia e)) := by
  unfold sliceEntry JuliaLean.base.tuple.getindexInteger
  cases h : methods.convertInt code l <;>
    simp only [liftJl, JuliaLean.base.abstractarray.liftJulia, liftResult, h,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    <;> rfl

/-- A native slice-map entry can succeed only at a positive, existing coordinate. -/
theorem sliceNativeEntryOk {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (coordinates : List I64) (l : I64)
    (selected : Option I64)
    (h : (sliceEntry methods coordinates (some (.native l)) : SM E _) = .ok selected) :
    1 ≤ l.val ∧ ∃ coordinate,
      coordinates[(l.val - 1).toNat]? = some coordinate ∧ selected = some coordinate := by
  rw [sliceNativeEntry] at h
  split at h
  next hpos =>
    cases hc : coordinates[(l.val - 1).toNat]? with
    | none => simp only [hc] at h; cases h
    | some coordinate =>
        rw [hc] at h
        exact ⟨hpos, coordinate, rfl, (Except.ok.inj h).symm⟩
  next => cases h

/-- Arbitrary integer entries retain their conversion and successful coordinate read. -/
theorem sliceOtherEntryOk {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (coordinates : List I64)
    (code : Code) (l : Payload code) (selected : Option I64)
    (h : (sliceEntry methods coordinates (some (.other code l)) : SM E _) = .ok selected) :
    ∃ j coordinate, methods.convertInt code l = .ok j ∧ 1 ≤ j.val ∧
      coordinates[(j.val - 1).toNat]? = some coordinate ∧ selected = some coordinate := by
  rw [sliceOtherEntry] at h
  cases hj : methods.convertInt code l with
  | error e => rw [hj] at h; cases h
  | ok j =>
      rw [hj] at h
      obtain ⟨hpos, coordinate, hc, hs⟩ := sliceNativeEntryOk methods coordinates j selected h
      exact ⟨j, coordinate, rfl, hpos, hc, hs⟩

theorem sliceIndexFollowsSlicemap : SliceIndexFollowsSlicemap := by
  intro E Parent Ax Code Payload N methods s coordinates selected h
  rw [sliceIndexMapM] at h
  obtain ⟨hlen, hlookup⟩ := sliceMapMOk (sliceEntry methods coordinates) s.slicemap selected h
  refine ⟨hlen, ?_⟩
  intro p hp
  obtain ⟨entry, output, he, ho, hentry⟩ := hlookup p hp
  rw [he]
  cases entry with
  | none =>
      have hz : output = none := (Except.ok.inj hentry).symm
      simpa only [hz] using ho
  | some entry =>
      cases entry with
      | native l =>
          obtain ⟨hpos, coordinate, hc, hs⟩ :=
            sliceNativeEntryOk methods coordinates l output hentry
          exact ⟨hpos, coordinate, hc, by simpa only [hs] using ho⟩
      | other code l =>
          obtain ⟨j, coordinate, hj, hpos, hc, hs⟩ :=
            sliceOtherEntryOk methods coordinates code l output hentry
          exact ⟨j, coordinate, hj, hpos, hc, by simpa only [hs] using ho⟩

/-- A fixed exception is returned if some entry fails and no different exception is possible. -/
theorem sliceMapMError {α β ε : Type} (f : α → Except ε β) (e : ε) (xs : List α)
    (herrors : ∀ x, x ∈ xs → ∀ e', f x = .error e' → e' = e)
    (hfailed : ∃ x, x ∈ xs ∧ f x = .error e) : xs.mapM f = .error e := by
  induction xs with
  | nil =>
      obtain ⟨x, hx, _⟩ := hfailed
      cases hx
  | cons x xs ih =>
      cases hx : f x with
      | error e' =>
          have he := herrors x (by exact List.mem_cons_self) e' hx
          subst e'
          simp only [List.mapM_cons, hx, Bind.bind, Except.bind]
      | ok value =>
          have htail : ∃ x', x' ∈ xs ∧ f x' = .error e := by
            obtain ⟨x', hmem, hf⟩ := hfailed
            rcases List.mem_cons.mp hmem with heq | hmem
            · subst x'
              rw [hx] at hf
              cases hf
            · exact ⟨x', hmem, hf⟩
          have hrest := ih (fun x' hmem => herrors x' (List.mem_cons_of_mem x hmem)) htail
          simp only [List.mapM_cons, hx, hrest, Bind.bind, Except.bind]

theorem sliceNativeEntryError {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (coordinates : List I64) (l : I64)
    (e : SliceErr E)
    (h : (sliceEntry methods coordinates (some (.native l)) : SM E _) = .error e) :
    e = .tuple (.julia .boundsError) := by
  rw [sliceNativeEntry] at h
  split at h
  · cases hc : coordinates[(l.val - 1).toNat]? with
    | none => rw [hc] at h; exact (Except.error.inj h).symm
    | some coordinate => rw [hc] at h; cases h
  · exact (Except.error.inj h).symm

theorem sliceNativeEntryMissing {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (coordinates : List I64) (l : I64)
    (h : l.val < 1 ∨ coordinates[(l.val - 1).toNat]? = none) :
    (sliceEntry methods coordinates (some (.native l)) : SM E _) =
      .error (.tuple (.julia .boundsError)) := by
  rw [sliceNativeEntry]
  split
  next hp =>
    rcases h with hlt | hmissing
    · omega
    · rw [hmissing]
  next => rfl

/-- A prefix of colons leaves the rest of the mapping's effects unchanged. -/
theorem sliceMapMColonPrefix {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (coordinates : List I64) (k : Nat)
    (rest : List (Option (IntegerValue Code Payload))) (e : SliceErr E)
    (h : rest.mapM (sliceEntry methods coordinates) = .error e) :
    (List.replicate k none ++ rest).mapM (sliceEntry methods coordinates) = .error e := by
  induction k with
  | zero => exact h
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, List.mapM_cons,
        sliceEntry, Bind.bind, Except.bind, Pure.pure, Except.pure, ih]

theorem sliceIndexRejectsMissingCoordinates : SliceIndexRejectsMissingCoordinates := by
  constructor
  · intro E Parent Ax Code Payload N methods s coordinates p l htypes hentry hmissing
    rw [sliceIndexMapM]
    apply sliceMapMError (sliceEntry methods coordinates) (.tuple (.julia .boundsError))
    · intro entry hmem e he
      cases entry with
      | none => change Except.ok none = Except.error e at he; cases he
      | some entry =>
          cases entry with
          | native j => exact sliceNativeEntryError methods coordinates j e he
          | other code x => exact False.elim (htypes _ hmem code x rfl)
    · exact ⟨some (.native l), List.mem_of_getElem? hentry,
        sliceNativeEntryMissing methods coordinates l hmissing⟩
  · intro E Parent Ax Code Payload N methods s coordinates k code l rest e hmap hconversion
    rw [sliceIndexMapM, hmap]
    apply sliceMapMColonPrefix
    have hentry : (sliceEntry methods coordinates (some (.other code l)) : SM E _) =
        .error (.array (.julia e)) := by
      rw [sliceOtherEntry, hconversion]
    simp only [List.mapM_cons, hentry, Bind.bind, Except.bind]

theorem sliceIndexBehavior : SliceIndexBehavior :=
  ⟨sliceIndexRejectsMissingCoordinates, sliceIndexFollowsSlicemap⟩

/-- A successful parent-view lookup has exactly the stipulated parent read. -/
theorem sliceViews : SlicesElementsAreParentViews := by
  intro E Parent View Value Element Ax Code Payload N access reads methods s indices checkbounds
    hview hcheck
  constructor
  · intro selected viewValue hselected hvalue
    constructor
    · simp only [getindex, hcheck, hselected, Bind.bind, Except.bind, hvalue]
    · intro inner parentCoordinates hcoords
      exact hview s.parent selected viewValue inner parentCoordinates hvalue hcoords
  · intro selected error hselected herror
    simp only [getindex, hcheck, hselected, Bind.bind, Except.bind, herror]

/-- The parent setter law supplies the exact effect of a successful slice assignment. -/
theorem sliceAssignment : SlicesAssignmentTargetsMappedParent := by
  intro E Parent View Value Element Ax Code Payload N access reads methods s value indices checkbounds
    hset hcheck selected hselected hvalue
  have hparent : access.setindexParent s.parent selected value = .ok value := by
    simpa only [setindex!, hcheck, hselected, Bind.bind, Except.bind] using hvalue
  obtain ⟨updated, hchanged, hunchanged⟩ := hset s.parent selected value hparent
  exact ⟨updated, hparent, hchanged, hunchanged⟩


theorem MultidimcovSliceL236Index_proven : JuliaLean.Proofs.base.slicearray.SliceIndexBehavior :=
  sliceIndexBehavior

theorem MultidimcovSliceIndexChecked_proven : JuliaLean.Proofs.base.slicearray.SliceIndexBehavior :=
  sliceIndexBehavior

theorem MultidimcovSlicearrayFaithful236_proven : JuliaLean.Proofs.base.slicearray.SliceIndexBehavior :=
  sliceIndexBehavior

theorem MultidimcovSliceL240Getindex_proven : JuliaLean.Proofs.base.slicearray.SlicesElementsAreParentViews :=
  sliceViews

theorem MultidimcovSlicesGetFull_proven : JuliaLean.Proofs.base.slicearray.SlicesElementsAreParentViews :=
  sliceViews

theorem MultidimcovSlicearrayFaithful240_proven : JuliaLean.Proofs.base.slicearray.SlicesElementsAreParentViews :=
  sliceViews

theorem MultidimcovSliceL244Setindex_proven : JuliaLean.Proofs.base.slicearray.SlicesAssignmentTargetsMappedParent :=
  sliceAssignment

theorem MultidimcovSlicesSetFull_proven : JuliaLean.Proofs.base.slicearray.SlicesAssignmentTargetsMappedParent :=
  sliceAssignment

theorem MultidimcovSlicearrayFaithful244_proven : JuliaLean.Proofs.base.slicearray.SlicesAssignmentTargetsMappedParent :=
  sliceAssignment

theorem MemsafetySlicesConstructorAxes_proven : JuliaLean.Proofs.base.slicearray.SlicesAccessesInBounds :=
  ⟨sliceIndexBehavior, sliceViews, sliceAssignment⟩

end JuliaLean.ChatGPT.Batch4.Group10

namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

theorem sa_ntuple_fields {E α : Type} (f : I64 → SM E α) (n : I64) (ys : List α)
    (h : JuliaLean.base.ntuple.ntupleInt f n ntupleRange = .ok ys) :
    (ys.length : Int) = n.val ∧
      ∀ p (hp : p < ys.length), f (int ((p : Int) + 1)) = .ok ys[p] := by
  obtain ⟨hn, hs⟩ := sa_ntuple_success f n ys h
  obtain ⟨hlen, hindex⟩ := sliceMapMOk f (sa_indices n) ys hs
  have hl : ys.length = n.val.toNat := by
    simpa only [sa_indices, List.length_map, List.length_range] using hlen
  refine ⟨by omega, ?_⟩
  intro p hp
  have hp' : p < n.val.toNat := by omega
  obtain ⟨x, y, hx, hy, hf⟩ := hindex p (by simpa only [sa_indices,
    List.length_map, List.length_range] using hp')
  have hx' : int ((p : Int) + 1) = x := by
    simpa only [sa_indices, List.getElem?_map, List.getElem?_range hp', Option.map_some,
      Option.some.injEq] using hx
  have hy' : ys[p] = y := by
    simpa only [List.getElem?_eq_getElem hp, Option.some.injEq] using hy
  rw [hx', hy']
  exact hf

def sa_max (x y : I64) : I64 := JuliaLean.base.int.max_BitInteger x y

theorem sa_max_value (x y : I64) : (sa_max x y).val = max x.val y.val := by
  unfold sa_max JuliaLean.base.int.max_BitInteger
  rw [sc_int_lt_eq]
  simp only [JuliaLean.base.int.ifelse, JuliaLean.base.int.remT,
    JuliaLean.base.int.rem_same, dite_true]
  by_cases h : x.val < y.val
  · simp only [h, decide_true, ite_true, Int.max_def, Int.le_of_lt h]
    rfl
  · have hge : y.val ≤ x.val := by omega
    simp only [h, decide_false, Bool.false_eq_true, ite_false]
    exact (Int.max_eq_left hge).symm

def sa_rank (n : I64) (dims : List I64) : I64 := dims.foldl sa_max n

theorem sa_rank_value (n : I64) (dims : List I64) : (sa_rank n dims).val = rankOf n dims := by
  unfold sa_rank rankOf
  induction dims generalizing n with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.foldl_cons]
      rw [ih, sa_max_value]

theorem sa_native_fold {Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (n : I64) (dims : List I64) :
    (nativeDims dims).foldl (integerMax methods) (.native n) = .native (sa_rank n dims) := by
  unfold nativeDims sa_rank
  induction dims generalizing n with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, List.foldl_cons, integerMax]
      exact ih (sa_max n d)

end JuliaLean.ChatGPT.Batch4.Group10

namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

/-- Callback constructing one entry of a dropped slice map. -/
def sa_drop_entry {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (dims : List I64) (dim : I64) :
    SM E (Option (IntegerValue Code Payload)) := do
  let entry ← liftJl (JuliaLean.base.some.something
    [findfirstValue (JuliaLean.base.tuple.findFirstTuple
      (fun d => integerIsequal methods d (.native dim)) (nativeDims dims)), .scalar none])
  pure (entryOfValue entry)

theorem sa_tuple_true_success {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
    (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dims : List I64)
    (N : Nat) (s : Slices Parent Ax Code Payload N)
    (h : eachsliceTuple ops methods printing a (nativeDims dims) true = .ok ⟨N, s⟩) :
    ∃ (n : I64) (sm : List (Option (IntegerValue Code Payload))) (ax : List Ax),
      ops.ndims a = .ok n ∧
      (nativeDims dims).mapM (axesAt ops methods a) = .ok ax ∧
      JuliaLean.base.ntuple.ntupleInt (sa_drop_entry (E := E) methods dims)
        (sa_rank n dims) ntupleRange = .ok sm ∧
      slicesConstructor ops methods a sm ax = .ok ⟨N, s⟩ := by
  unfold eachsliceTuple at h
  cases hc : (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) with
  | error e => simp only [hc, bind, Except.bind] at h; cases h
  | ok u =>
      cases hn : ops.ndims a with
      | error e => simp only [hc, hn, bind, Except.bind] at h; cases h
      | ok n =>
          simp only [hc, hn, bind, Except.bind, sa_native_fold, ite_true,
            ntupleDispatch] at h
          cases ha : (nativeDims dims).mapM (axesAt ops methods a) with
          | error e => simp only [ha, bind, Except.bind] at h; cases h
          | ok ax =>
              simp only [ha, bind, Except.bind] at h
              change (do
                let sm ← JuliaLean.base.ntuple.ntupleInt (sa_drop_entry (E := E) methods dims)
                  (sa_rank n dims) ntupleRange
                slicesConstructor ops methods a sm ax) = .ok ⟨N, s⟩ at h
              cases hm : (JuliaLean.base.ntuple.ntupleInt (sa_drop_entry (E := E) methods dims)
                  (sa_rank n dims) ntupleRange : SM E _) with
              | error e => simp only [hm, bind, Except.bind] at h; cases h
              | ok sm =>
                  simp only [hm, bind, Except.bind] at h
                  exact ⟨n, sm, ax, rfl, rfl, hm, h⟩

theorem sa_tuple_false_success {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
    (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dims : List I64)
    (N : Nat) (s : Slices Parent Ax Code Payload N)
    (h : eachsliceTuple ops methods printing a (nativeDims dims) false = .ok ⟨N, s⟩) :
    ∃ (n : I64) (sm : List (Option (IntegerValue Code Payload))) (ax : List Ax),
      ops.ndims a = .ok n ∧
      JuliaLean.base.ntuple.ntupleInt (fun dim =>
        if integerIn methods (.native dim) (nativeDims dims) then axesAt ops methods a (.native dim)
        else pure (unitaxis ops.oneTo a)) (sa_rank n dims) ntupleRange = .ok ax ∧
      (JuliaLean.base.ntuple.ntupleInt (fun dim => pure
        (if integerIn methods (.native dim) (nativeDims dims) then
          some (IntegerValue.native (Code := Code) (Payload := Payload) dim) else none))
        (sa_rank n dims) ntupleRange : SM E _) = .ok sm ∧
      slicesConstructor ops methods a sm ax = .ok ⟨N, s⟩ := by
  unfold eachsliceTuple at h
  cases hc : (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) with
  | error e => simp only [hc, bind, Except.bind] at h; cases h
  | ok u =>
      cases hn : ops.ndims a with
      | error e => simp only [hc, hn, bind, Except.bind] at h; cases h
      | ok n =>
          simp only [hc, hn, bind, Except.bind, sa_native_fold, Bool.false_eq_true,
            ite_false, ntupleDispatch] at h
          cases ha : (JuliaLean.base.ntuple.ntupleInt (fun dim =>
              if integerIn methods (.native dim) (nativeDims dims) then
                axesAt ops methods a (.native dim) else pure (unitaxis ops.oneTo a))
              (sa_rank n dims) ntupleRange : SM E _) with
          | error e => simp only [ha, bind, Except.bind] at h; cases h
          | ok ax =>
              cases hm : (JuliaLean.base.ntuple.ntupleInt (fun dim => pure
                  (if integerIn methods (.native dim) (nativeDims dims) then
                    some (IntegerValue.native (Code := Code) (Payload := Payload) dim) else none))
                  (sa_rank n dims) ntupleRange : SM E _) with
              | error e => simp only [ha, hm, bind, Except.bind] at h; cases h
              | ok sm =>
                  simp only [ha, hm, bind, Except.bind] at h
                  exact ⟨n, sm, ax, rfl, ha, hm, h⟩

end JuliaLean.ChatGPT.Batch4.Group10

namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

theorem sa_requested {Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (dims : List I64) (p : Nat)
    (hfit : (p : Int) + 1 ≤ IntTy.i64.max) :
    integerIn methods (.native (int ((p : Int) + 1))) (nativeDims dims) =
      isRequested dims p := by
  rw [sc_integerIn_native]
  have hv : (int ((p : Int) + 1)).val = (p : Int) + 1 :=
    sa_int_val _ (by
      constructor
      · have hm : IntTy.i64.min ≤ 0 := by decide
        omega
      · exact hfit)
  rw [hv]
  unfold isRequested
  apply List.any_congr rfl
  intro d
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]

theorem sa_axes (constructorLaw : SlicesConstructorPreservesInput) : TupleEachsliceAxes := by
  intro E V Ty Parent Ax Code Payload ops methods printing a dims drop N s h
  cases drop with
  | true =>
      obtain ⟨n, sm, ax, hn, ha, hm, hc⟩ :=
        sa_tuple_true_success ops methods printing a dims N s h
      obtain ⟨hparent, hsm, hax, hN, hview⟩ := constructorLaw ops methods a sm ax N s hc
      obtain ⟨hmlen, _⟩ := sa_ntuple_fields _ _ _ hm
      have halen := (sliceMapMOk (axesAt ops methods a) (nativeDims dims) ax ha).1
      refine ⟨n, hn, ?_, ?_⟩
      · rw [hsm, hmlen, sa_rank_value]
      · change N = dims.length ∧ (nativeDims dims).mapM (axesAt ops methods a) = .ok s.axes
        refine ⟨?_, ?_⟩
        · rw [hN, halen]
          exact List.length_map _
        · change s.axes = ax at hax
          rw [hax]
          exact ha
  | false =>
      obtain ⟨n, sm, ax, hn, ha, hm, hc⟩ :=
        sa_tuple_false_success ops methods printing a dims N s h
      obtain ⟨hparent, hsm, hax, hN, hview⟩ := constructorLaw ops methods a sm ax N s hc
      obtain ⟨hmlen, _⟩ := sa_ntuple_fields _ _ _ hm
      obtain ⟨halen, haxes⟩ := sa_ntuple_fields _ _ _ ha
      change s.axes = ax at hax
      refine ⟨n, hn, ?_, ?_⟩
      · rw [hsm, hmlen, sa_rank_value]
      · change (N : Int) = rankOf n dims ∧ _
        refine ⟨?_, ?_⟩
        · rw [hN, halen, sa_rank_value]
        · intro p hp
          have hpa : p < ax.length := by simpa only [hax] using hp
          have hfit : (p : Int) + 1 ≤ IntTy.i64.max := by
            have hb := (sa_rank n dims).property.2
            omega
          have hentry := haxes p hpa
          rw [sa_requested methods dims p hfit] at hentry
          split
          · rename_i hreq
            simpa only [hreq, ite_true, hax] using hentry
          · rename_i hreq
            have he : unitaxis ops.oneTo a = ax[p] := by
              simpa only [hreq, Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq] using hentry
            simpa only [hax] using he.symm

end JuliaLean.ChatGPT.Batch4.Group10

namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

theorem sa_mapM_congr {α β ε : Type} (xs : List α) (f g : α → Except ε β)
    (h : ∀ x, x ∈ xs → f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp only [List.mem_cons, true_or])
      have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.mapM_cons, hx, ht]

theorem sa_mapM_indexed {α β ε : Type} (xs : List α) (f : α → Except ε β)
    (g : Nat → Except ε β) (h : ∀ p (hp : p < xs.length), f xs[p] = g p) :
    xs.mapM f = (List.range xs.length).mapM g := by
  calc
    xs.mapM f = (xs.zipIdx).mapM (fun xp => f xp.1) := by
      simpa only [List.mapM_map, Function.comp_def] using
        congrArg (fun ys => ys.mapM f) (List.zipIdx_map_fst 0 xs).symm
    _ = (xs.zipIdx).mapM (fun xp => g xp.2) := by
      apply sa_mapM_congr
      intro xp hx
      obtain ⟨hk, hp, he⟩ := List.mem_zipIdx hx
      have hp' : xp.2 < xs.length := by omega
      have he' : xp.1 = xs[xp.2] := by simpa only [Nat.sub_zero] using he
      rw [he']
      exact h xp.2 hp'
    _ = (List.range xs.length).mapM g := by
      have he := congrArg (fun ys => ys.mapM g) (List.zipIdx_map_snd 0 xs)
      simpa only [List.mapM_map, Function.comp_def, ← List.range_eq_range'] using he

theorem sa_size_from_axes (axesLaw : TupleEachsliceAxes) : TupleEachsliceSizeMatchesAxes := by
  intro E V Ty Parent Ax Code Payload ops methods printing a dims drop N s h
  have haxes := axesLaw ops methods printing a dims drop N s h
  obtain ⟨n, hn, hlen, hshape⟩ := haxes
  cases drop with
  | true =>
      change N = dims.length ∧ (nativeDims dims).mapM (axesAt ops methods a) = .ok s.axes at hshape
      exact ⟨s.axes, hshape.2, rfl⟩
  | false =>
      change (N : Int) = rankOf n dims ∧
        ∀ p (hp : p < s.axes.length),
          if isRequested dims p then
            axesAt ops methods a (.native (int ((p : Int) + 1))) = .ok s.axes[p]
          else s.axes[p] = unitaxis ops.oneTo a at hshape
      let g : Nat → SM E I64 := fun p =>
        if isRequested dims p then do
          let axis ← axesAt ops methods a (.native (int ((p : Int) + 1)))
          ops.axisLength axis
        else ops.axisLength (unitaxis ops.oneTo a)
      change s.axes.mapM ops.axisLength = (List.range N).mapM g
      calc
        s.axes.mapM ops.axisLength = (List.range s.axes.length).mapM g := by
          apply sa_mapM_indexed
          intro p hp
          have ha := hshape.2 p hp
          split at ha
          · rename_i hreq
            simp only [g, hreq, ite_true, ha, bind, Except.bind]
          · rename_i hreq
            simp only [g, hreq, Bool.false_eq_true, ite_false, ha]
        _ = (List.range N).mapM g := by rw [s.axes_length]

end JuliaLean.ChatGPT.Batch4.Group10


namespace JuliaLean.ChatGPT.Batch4.Group10

open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

/-- The recursive tuple search records a zero-based search position plus its initial offset. -/
theorem ss_findFirstRec {α : Type} (f : α → Bool) (t : List α) (i : Nat) :
    JuliaLean.base.tuple.findFirstRec f i t = (t.findIdx? f).map (· + i) := by
  induction t generalizing i with
  | nil => rfl
  | cons a r ih =>
      simp only [JuliaLean.base.tuple.findFirstRec, List.findIdx?_cons]
      cases hf : f a
      · simp only [hf, Bool.false_eq_true, ite_false, ih, Option.map_map]
        congr 1
        funext x
        simp only [Function.comp_apply]
        omega
      · simp only [hf, ite_true, Option.map_some, Nat.zero_add]

/-- The loop and recursive tuple-search implementations have the same ordered search result. -/
theorem ss_findFirstLoop {α : Type} (f : α → Bool) (t : List α) (i k : Nat)
    (h : i + k = t.length) :
    JuliaLean.base.tuple.findFirstLoopLocal f t i k =
      ((t.drop i).findIdx? f).map (· + i + 1) := by
  induction k generalizing i with
  | zero =>
      have h0 : t.length ≤ i := by omega
      simp only [JuliaLean.base.tuple.findFirstLoopLocal, List.drop_eq_nil_of_le h0,
        List.findIdx?_nil, Option.map_none]
  | succ k ih =>
      have hi : i < t.length := by omega
      rw [JuliaLean.base.tuple.findFirstLoopLocal, List.getElem?_eq_getElem hi,
        ih (i + 1) (by omega), List.drop_eq_getElem_cons hi, List.findIdx?_cons]
      cases hf : f t[i]
      · simp only [hf, Bool.false_eq_true, ite_false, Option.map_map]
        congr 1
        funext x
        simp only [Function.comp_apply]
        omega
      · simp only [hf, ite_true, Option.map_some, Nat.zero_add]

theorem ss_findFirstTuple {α : Type} (f : α → Bool) (t : List α) :
    JuliaLean.base.tuple.findFirstTuple f t = (t.findIdx? f).map (· + 1) := by
  unfold JuliaLean.base.tuple.findFirstTuple
  split
  · exact ss_findFirstRec f t 1
  · rw [JuliaLean.base.tuple.findFirstLoop,
      ss_findFirstLoop f t 0 t.length (by omega)]
    simp only [List.drop_zero, Nat.add_zero]

/-- Positive, distinct native dimensions have a representable dimension count. -/
theorem ss_dimsLength (dims : List I64)
    (hpos : ∀ d, d ∈ dims → 1 ≤ d.val)
    (hunique : List.Pairwise (fun l r : I64 => l.val ≠ r.val) dims) :
    (dims.length : Int) ≤ IntTy.i64.max := by
  let keys := dims.map (fun d => (d.val - 1).toNat)
  have hnodup : keys.Nodup := by
    unfold keys
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ hunique
    intro a b ha hb hab heq
    have hpa := hpos a ha
    have hpb := hpos b hb
    apply hab
    omega
  have hsubset : keys ⊆ List.range IntTy.i64.max.toNat := by
    intro k hk
    obtain ⟨d, hd, heq⟩ := List.mem_map.mp hk
    subst k
    apply List.mem_range.mpr
    have hpd := hpos d hd
    have hbd := d.property
    have hm : 0 ≤ IntTy.i64.max := by decide
    omega
  have hlen := hnodup.length_le_of_subset hsubset
  simp only [keys, List.length_map, List.length_range] at hlen
  have hm : 0 ≤ IntTy.i64.max := by decide
  omega


theorem ss_nativeFindFirst {Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (dims : List I64) (dim : I64) :
    JuliaLean.base.tuple.findFirstTuple
        (fun d => integerIsequal methods d (.native dim)) (nativeDims dims) =
      (dims.findIdx? (fun d => d.val == dim.val)).map (· + 1) := by
  rw [ss_findFirstTuple]
  simp only [nativeDims, List.findIdx?_map, Function.comp_def, integerIsequal,
    sc_int_eq_eq, Bool.beq_eq_decide_eq]

/-- The dropping branch's selector callback is the first matching requested dimension. -/
theorem ss_dropEntry {E Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (dims : List I64) (dim : I64) :
    (do
      let entry ← liftJl (JuliaLean.base.some.something
        [findfirstValue (JuliaLean.base.tuple.findFirstTuple
          (fun d => integerIsequal methods d (.native dim)) (nativeDims dims)), .scalar none])
      pure (entryOfValue entry) : SM E (Option (IntegerValue Code Payload))) =
      .ok ((dims.findIdx? (fun d => d.val == dim.val)).map
        (fun i => IntegerValue.native (int ((i : Int) + 1)))) := by
  rw [something_findfirst, ss_nativeFindFirst]
  cases hi : dims.findIdx? (fun d => d.val == dim.val) <;> rfl

/-- The retained-rank branch tests the same requested parent dimension as the specification. -/
theorem ss_integerIn_position {Code : Type} {Payload : Code → Type}
    (methods : IntegerMethods Code Payload) (dims : List I64) (p : Nat)
    (hfit : IntTy.i64.min ≤ (p : Int) + 1 ∧ (p : Int) + 1 ≤ IntTy.i64.max) :
    integerIn methods (.native (int ((p : Int) + 1))) (nativeDims dims) =
      isRequested dims p := by
  rw [sc_integerIn_native]
  have hv : (int ((p : Int) + 1)).val = (p : Int) + 1 :=
    wrapInt_of_inRange .i64 _ hfit
  simp only [hv, isRequested, Bool.beq_eq_decide_eq]


/-- The exact native slice-map entry associated with a parent dimension. -/
def ss_selector {Code : Type} {Payload : Code → Type}
    (dims : List I64) (drop : Bool) (p : Nat) : Option (IntegerValue Code Payload) :=
  if drop then
    (dims.findIdx? (fun d => d.val == (p : Int) + 1)).map
      (fun i => .native (int ((i : Int) + 1)))
  else if isRequested dims p then some (.native (int ((p : Int) + 1)))
  else none

/-- A slice map with the documented entries realizes the documented coordinate selection. -/
theorem ss_selectionFromMap {Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (methods : IntegerMethods Code Payload) (dims : List I64) (drop : Bool)
    (s : Slices Parent Ax Code Payload N)
    (hdims : (dims.length : Int) ≤ IntTy.i64.max)
    (hrank : (s.slicemap.length : Int) ≤ IntTy.i64.max)
    (hmap : ∀ p, p < s.slicemap.length →
      s.slicemap[p]? = some (ss_selector dims drop p)) :
    SelectionOutcome methods dims drop s := by
  intro E indices selected hselected
  obtain ⟨hlen, hlookup⟩ := sliceIndexFollowsSlicemap methods s indices.values selected hselected
  refine ⟨hlen, ?_⟩
  intro p hp
  have hs := hlookup p hp
  rw [hmap p hp] at hs
  cases drop with
  | false =>
      simp only [ss_selector, Bool.false_eq_true, ite_false] at hs ⊢
      by_cases hreq : isRequested dims p = true
      · simp only [hreq, ite_true] at hs ⊢
        have hfit : IntTy.i64.min ≤ (p : Int) + 1 ∧ (p : Int) + 1 ≤ IntTy.i64.max := by
          have hmin : IntTy.i64.min ≤ 0 := by decide
          constructor <;> omega
        have hv : (int ((p : Int) + 1)).val = (p : Int) + 1 :=
          wrapInt_of_inRange .i64 _ hfit
        have he : (((int ((p : Int) + 1)).val - 1).toNat) = p := by rw [hv]; omega
        obtain ⟨_, coordinate, hc, ho⟩ := hs
        exact ⟨coordinate, by simpa only [he] using hc, ho⟩
      · simp only [hreq, ite_false] at hs ⊢
        exact hs
  | true =>
      simp only [ss_selector, ite_true] at hs ⊢
      cases hidx : dims.findIdx? (fun d => d.val == (p : Int) + 1) with
      | none =>
          simp only [hidx, Option.map_none] at hs ⊢
          exact hs
      | some j =>
          simp only [hidx, Option.map_some] at hs ⊢
          obtain ⟨hj, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
          have hfit : IntTy.i64.min ≤ (j : Int) + 1 ∧ (j : Int) + 1 ≤ IntTy.i64.max := by
            have hmin : IntTy.i64.min ≤ 0 := by decide
            constructor <;> omega
          have hv : (int ((j : Int) + 1)).val = (j : Int) + 1 :=
            wrapInt_of_inRange .i64 _ hfit
          have he : (((int ((j : Int) + 1)).val - 1).toNat) = j := by rw [hv]; omega
          obtain ⟨_, coordinate, hc, ho⟩ := hs
          exact ⟨coordinate, by simpa only [he] using hc, ho⟩


theorem ss_checkSuccess {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
    (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dims : List I64)
    (drop : Bool) (N : Nat) (s : Slices Parent Ax Code Payload N)
    (h : eachsliceTuple ops methods printing a (nativeDims dims) drop = .ok ⟨N, s⟩) :
    (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) = .ok () := by
  unfold eachsliceTuple at h
  cases hc : (sliceCheckDims methods printing (nativeDims dims) : SM E Unit) with
  | error e => simp only [hc, Bind.bind, Except.bind] at h; cases h
  | ok u => cases u; rfl

/-- Successful tuple construction supplies exactly the map required by the selection contract. -/
theorem ss_tupleSelectionFromConstructor (hconstructor : SlicesConstructorPreservesInput) :
    TupleEachsliceSelectsRequestedDimensions := by
  intro E V Ty Parent Ax Code Payload ops methods printing a dims drop N s h
  have hc := ss_checkSuccess ops methods printing a dims drop N s h
  obtain ⟨hpos, hdistinct⟩ := sc_check_success methods printing dims hc
  have hdimlen := ss_dimsLength dims hpos hdistinct
  cases drop with
  | true =>
      obtain ⟨n, sm, ax, hn, ha, hm, hs⟩ :=
        sa_tuple_true_success ops methods printing a dims N s h
      obtain ⟨_, hsmap, _, _, _⟩ := hconstructor ops methods a sm ax N s hs
      obtain ⟨hsm, hentries⟩ := sa_ntuple_fields _ (sa_rank n dims) sm hm
      have hrank : (s.slicemap.length : Int) ≤ IntTy.i64.max := by
        rw [hsmap, hsm]
        exact (sa_rank n dims).property.2
      apply ss_selectionFromMap methods dims true s hdimlen hrank
      intro p hp
      have hp' : p < sm.length := by simpa only [hsmap] using hp
      have hentry := hentries p hp'
      have hfit : IntTy.i64.min ≤ (p : Int) + 1 ∧ (p : Int) + 1 ≤ IntTy.i64.max := by
        have hmin : IntTy.i64.min ≤ 0 := by decide
        have hmax := (sa_rank n dims).property.2
        constructor <;> omega
      have hv : (int ((p : Int) + 1)).val = (p : Int) + 1 :=
        wrapInt_of_inRange .i64 _ hfit
      unfold sa_drop_entry at hentry
      rw [ss_dropEntry, hv] at hentry
      rw [hsmap, List.getElem?_eq_getElem hp']
      exact congrArg some (Except.ok.inj hentry).symm
  | false =>
      obtain ⟨n, sm, ax, hn, ha, hm, hs⟩ :=
        sa_tuple_false_success ops methods printing a dims N s h
      obtain ⟨_, hsmap, _, _, _⟩ := hconstructor ops methods a sm ax N s hs
      obtain ⟨hsm, hentries⟩ := sa_ntuple_fields _ (sa_rank n dims) sm hm
      have hrank : (s.slicemap.length : Int) ≤ IntTy.i64.max := by
        rw [hsmap, hsm]
        exact (sa_rank n dims).property.2
      apply ss_selectionFromMap methods dims false s hdimlen hrank
      intro p hp
      have hp' : p < sm.length := by simpa only [hsmap] using hp
      have hentry := hentries p hp'
      have hfit : IntTy.i64.min ≤ (p : Int) + 1 ∧ (p : Int) + 1 ≤ IntTy.i64.max := by
        have hmin : IntTy.i64.min ≤ 0 := by decide
        have hmax := (sa_rank n dims).property.2
        constructor <;> omega
      rw [ss_integerIn_position methods dims p hfit] at hentry
      rw [hsmap, List.getElem?_eq_getElem hp']
      exact congrArg some (Except.ok.inj hentry).symm

end JuliaLean.ChatGPT.Batch4.Group10

namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

theorem sc_empty_dimensions (constructorLaw : SlicesConstructorPreservesInput) :
    EmptyDimensionsProduceWholeParentSlice := by
  intro E V Ty Parent Ax Code Payload ops methods printing a n N s hn h
  simp only [eachsliceTuple, sliceCheckDims, sliceCheckDimsEmpty, List.foldl_nil,
    List.mapM_nil, hn, bind, Except.bind, pure, Except.pure, ite_true, ntupleDispatch] at h
  have hfind (dim : I64) : JuliaLean.base.tuple.findFirstTuple
      (fun d => integerIsequal methods d (.native dim)) [] = none := rfl
  simp only [hfind, something_findfirst, Option.map_none, liftJl,
    JuliaLean.base.abstractarray.liftJulia, liftResult, bind, Except.bind,
    pure, Except.pure, entryOfValue] at h
  change (do
    let sm ← JuliaLean.base.ntuple.ntupleInt
      (fun _ => (pure none : SM E (Option (IntegerValue Code Payload)))) n ntupleRange
    slicesConstructor ops methods a sm []) = .ok ⟨N, s⟩ at h
  cases ht : (JuliaLean.base.ntuple.ntupleInt
      (fun _ => (pure none : SM E (Option (IntegerValue Code Payload)))) n ntupleRange) with
  | error e => simp only [ht, bind, Except.bind] at h; cases h
  | ok sm =>
      simp only [ht, bind, Except.bind] at h
      obtain ⟨hp, hsm, hax, hN, _⟩ := constructorLaw ops methods a sm [] N s h
      obtain ⟨hnonneg, hm⟩ := sa_ntuple_success
        (fun _ => (pure none : SM E (Option (IntegerValue Code Payload)))) n sm ht
      rw [List.mapM_pure] at hm
      have he : (sa_indices n).map (fun _ => (none : Option (IntegerValue Code Payload))) = sm :=
        Except.ok.inj hm
      have hlen : (sm.length : Int) = n.val := by
        rw [← he, List.length_map]
        simp only [sa_indices, List.length_map, List.length_range]
        omega
      refine ⟨hN, hax, ?_, ?_, hp⟩
      · rw [hsm]
        exact hlen
      · intro entry hentry
        rw [hsm, ← he] at hentry
        obtain ⟨i, _, hi⟩ := List.mem_map.mp hentry
        exact hi.symm

theorem MultidimcovSliceL51CheckEmpty_proven : JuliaLean.Proofs.base.slicearray.EmptyDimensionsProduceWholeParentSlice :=
  sc_empty_dimensions sc_constructor_preserves

end JuliaLean.ChatGPT.Batch4.Group10


namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean JuliaLean.base.slicearray JuliaLean.Proofs.base.slicearray

theorem sw_eachsliceTuple_parent (constructorLaw : SlicesConstructorPreservesInput)
    {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
    (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload) (a : Parent)
    (dims : List (IntegerValue Code Payload)) (drop : Bool) (N : Nat)
    (s : Slices Parent Ax Code Payload N)
    (h : eachsliceTuple ops methods printing a dims drop = .ok ⟨N, s⟩) :
    parent s = a := by
  unfold eachsliceTuple at h
  cases hc : (sliceCheckDims methods printing dims : SM E Unit) with
  | error e => simp only [hc, bind, Except.bind] at h; cases h
  | ok u =>
    simp only [hc, bind, Except.bind] at h
    cases hn : ops.ndims a with
    | error e => simp only [hn, bind, Except.bind] at h; cases h
    | ok n =>
      simp only [hn, bind, Except.bind] at h
      cases drop
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · cases h
        · split at h
          · cases h
          · exact (constructorLaw ops methods a _ _ N s h).1
      · simp only [↓reduceIte] at h
        split at h
        · cases h
        · split at h
          · cases h
          · exact (constructorLaw ops methods a _ _ N s h).1

theorem sw_eachslice_parent (constructorLaw : SlicesConstructorPreservesInput) :
    EachsliceParentIdentity := by
  constructor
  · intro E V Ty Parent Ax Code Payload ops methods printing a dims drop N s h
    exact sw_eachsliceTuple_parent constructorLaw ops methods printing a dims drop N s h
  · intro E V Ty Parent Ax Code Payload ops methods printing a dim drop N s h
    exact sw_eachsliceTuple_parent constructorLaw ops methods printing a [dim] drop N s h

theorem sw_integer_contract (tupleLaw : TupleEachsliceContract) :
    IntegerEachsliceUsesItsAxis := by
  intro E V Ty Parent Ax Code Payload ops methods printing a dim drop N s h
  exact ⟨tupleLaw.1 ops methods printing a [dim] drop N s h,
    tupleLaw.2.1 ops methods printing a [dim] drop N s h,
    tupleLaw.2.2 ops methods printing a [dim] drop N s h⟩

theorem sw_public_contract (constructorLaw : SlicesConstructorPreservesInput)
    (tupleLaw : TupleEachsliceContract) : EachslicePublicContract := by
  refine ⟨sw_eachslice_parent constructorLaw, ?_, tupleLaw.1, tupleLaw.2.1,
    sw_integer_contract tupleLaw⟩
  constructor
  · intro E V Ty Parent Ax Code Payload ops methods printing a dims drop N s h
    exact tupleLaw.2.2 ops methods printing a dims drop N s h
  · intro E V Ty Parent Ax Code Payload ops methods printing a dim drop N s h
    exact tupleLaw.2.2 ops methods printing a [dim] drop N s h

theorem sw_singleton_result (constructorLaw : SlicesConstructorPreservesInput)
    (axesLaw : TupleEachsliceAxes) (selectionLaw : TupleEachsliceSelectsRequestedDimensions)
    {E V Ty Parent Ax Code : Type} {Payload : Code → Type}
    (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload) (a : Parent) (dim : I64)
    (N : Nat) (s : Slices Parent Ax Code Payload N)
    (h : eachsliceTuple ops methods printing a [.native dim] true = .ok ⟨N, s⟩) :
    N = 1 ∧ parent s = a ∧
      (∃ axis, axesAt ops methods a (.native dim) = .ok axis ∧ axes s = [axis]) ∧
      SelectionOutcome methods [dim] true s := by
  have hp := sw_eachsliceTuple_parent constructorLaw ops methods printing a [.native dim] true N s h
  have hs := selectionLaw ops methods printing a [dim] true N s h
  obtain ⟨n, hn, hlen, hN, hax⟩ := axesLaw ops methods printing a [dim] true N s h
  refine ⟨hN, hp, ?_, hs⟩
  simp only [nativeDims, List.map_cons, List.map_nil, List.mapM_cons,
    List.mapM_nil, bind, Except.bind, pure, Except.pure] at hax
  cases ha : axesAt ops methods a (.native dim) with
  | error e => simp only [ha] at hax; cases hax
  | ok ax =>
    simp only [ha] at hax
    have he : [ax] = s.axes := Except.ok.inj hax
    exact ⟨ax, rfl, he.symm⟩

theorem sw_rows_matrix (constructorLaw : SlicesConstructorPreservesInput)
    (axesLaw : TupleEachsliceAxes) (selectionLaw : TupleEachsliceSelectsRequestedDimensions) :
    EachrowMatrixUsesRows := by
  intro E V Ty Parent Ax Code Payload ops methods printing a N s hn h
  exact sw_singleton_result constructorLaw axesLaw selectionLaw ops methods printing a (int 1) N s h

theorem sw_cols_matrix (constructorLaw : SlicesConstructorPreservesInput)
    (axesLaw : TupleEachsliceAxes) (selectionLaw : TupleEachsliceSelectsRequestedDimensions) :
    EachcolMatrixUsesColumns := by
  intro E V Ty Parent Ax Code Payload ops methods printing a N s hn h
  exact sw_singleton_result constructorLaw axesLaw selectionLaw ops methods printing a (int 2) N s h

theorem sw_row_vector_generic (constructorLaw : SlicesConstructorPreservesInput)
    (axesLaw : TupleEachsliceAxes) (selectionLaw : TupleEachsliceSelectsRequestedDimensions)
    {E V Ty Vec Parent Ax Code : Type} {Payload : Code → Type}
    (size : Vec → JuliaLean.base.abstractarray.Result (List I64))
    (reshapeDims : Vec → List I64 → SM E Parent)
    (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload) (v : Vec)
    (N : Nat) (s : Slices Parent Ax Code Payload N)
    (h : eachrowVector size reshapeDims ops methods printing v = .ok ⟨N, s⟩) :
    N = 1 ∧ VectorReshape size reshapeDims v (parent s) ∧
      SelectionOutcome methods [int 1] true s := by
  unfold eachrowVector at h
  cases hz : JuliaLean.base.abstractarray.sizeDim
      (fun d : I64 => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 d))
      size v (int 1) with
  | error e => simp only [hz, liftResult, bind, Except.bind] at h; cases h
  | ok rows =>
    simp only [hz, liftResult, bind, Except.bind, pure, Except.pure] at h
    cases hr : JuliaLean.base.reshapedarray.reshapeIntVarargs reshapeDims v [rows, int 1] with
    | error e => simp only [hr, bind, Except.bind] at h; cases h
    | ok b =>
      simp only [hr, bind, Except.bind] at h
      obtain ⟨hN, hp, haxes, hs⟩ := sw_singleton_result constructorLaw axesLaw selectionLaw
        ops methods printing b (int 1) N s h
      refine ⟨hN, ⟨rows, hz, ?_⟩, hs⟩
      rw [hp]
      exact hr

theorem sw_col_vector_generic (constructorLaw : SlicesConstructorPreservesInput)
    (axesLaw : TupleEachsliceAxes) (selectionLaw : TupleEachsliceSelectsRequestedDimensions)
    {E V Ty Vec Parent Ax Code : Type} {Payload : Code → Type}
    (size : Vec → JuliaLean.base.abstractarray.Result (List I64))
    (reshapeDims : Vec → List I64 → SM E Parent)
    (ops : SliceParentOps (SM E) Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload) (v : Vec)
    (N : Nat) (s : Slices Parent Ax Code Payload N)
    (h : eachcolVector size reshapeDims ops methods printing v = .ok ⟨N, s⟩) :
    N = 1 ∧ VectorReshape size reshapeDims v (parent s) ∧
      SelectionOutcome methods [int 2] true s := by
  unfold eachcolVector at h
  cases hz : JuliaLean.base.abstractarray.sizeDim
      (fun d : I64 => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 d))
      size v (int 1) with
  | error e => simp only [hz, liftResult, bind, Except.bind] at h; cases h
  | ok rows =>
    simp only [hz, liftResult, bind, Except.bind, pure, Except.pure] at h
    cases hr : JuliaLean.base.reshapedarray.reshapeIntVarargs reshapeDims v [rows, int 1] with
    | error e => simp only [hr, bind, Except.bind] at h; cases h
    | ok b =>
      simp only [hr, bind, Except.bind] at h
      obtain ⟨hN, hp, haxes, hs⟩ := sw_singleton_result constructorLaw axesLaw selectionLaw
        ops methods printing b (int 2) N s h
      refine ⟨hN, ⟨rows, hz, ?_⟩, hs⟩
      rw [hp]
      exact hr

theorem sw_reshapeArray_success {T Ref : Type} {M N : Nat}
    (checkedDims : Vector JuliaLean.base.reshapedarray.I64 N → JuliaLean.base.reshapedarray.RResult JuliaLean.base.reshapedarray.I64)
    (length : JuliaLean.base.reshapedarray.ArrayValue T M Ref → JuliaLean.base.reshapedarray.RResult JuliaLean.base.reshapedarray.I64)
    (a : JuliaLean.base.reshapedarray.ArrayValue T M Ref)
    (dims : Vector JuliaLean.base.reshapedarray.I64 N)
    (b : JuliaLean.base.reshapedarray.ArrayValue T N Ref)
    (h : JuliaLean.base.reshapedarray.reshapeArray checkedDims length a dims = .ok b) :
    b.ref = a.ref ∧ b.dims = dims := by
  unfold JuliaLean.base.reshapedarray.reshapeArray at h
  cases hc : checkedDims dims with
  | error e => simp only [hc, bind, Except.bind] at h; cases h
  | ok p =>
    simp only [hc, bind, Except.bind] at h
    cases hl : length a with
    | error e => simp only [hl, bind, Except.bind] at h; cases h
    | ok l =>
      simp only [hl, bind, Except.bind] at h
      split at h
      · cases h
      · cases h
        exact ⟨rfl, rfl⟩

theorem sw_array_size_first {T Ref : Type}
    (v : JuliaLean.base.reshapedarray.ArrayValue T 1 Ref) :
    JuliaLean.base.abstractarray.sizeDim
      (fun d : I64 => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 d))
      arraySize v (int 1) = .ok v.dims[0] := by
  have hc : JuliaLean.base.int.convert .i64 (int 1) = .ok (int 1) := by decide
  have hv : (int 1).val = 1 := by decide
  simp only [JuliaLean.base.abstractarray.sizeDim, hc, JuliaLean.base.abstractarray.liftJulia,
    Except.mapError, arraySize, JuliaLean.Bindings.base.reshapedarray.arrayHeaderSize,
    bind, Except.bind, Vector.length_toList, hv, Int.natCast_one, Int.le_refl, ↓reduceIte,
    JuliaLean.base.abstractarray.tupleGet, Int.reduceLT, Int.reduceSub, Int.toNat_zero,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem (by decide : 0 < 1)]

theorem sw_array_vector_reshape {E T Ref : Type}
    (v : JuliaLean.base.reshapedarray.ArrayValue T 1 Ref)
    (b : JuliaLean.base.reshapedarray.ArrayValue T 2 Ref)
    (h : VectorReshape arraySize (arrayReshapeToMatrix (E := E)) v b) :
    b.ref = v.ref ∧ b.dims.toList = [v.dims[0], int 1] := by
  obtain ⟨rows, hsz, hr⟩ := h
  rw [sw_array_size_first] at hsz
  cases hsz
  change (JuliaLean.Bindings.base.reshapedarray.reshapeArrayHeader v #v[v.dims[0], int 1]).mapError
    SliceErr.reshaped = Except.ok b at hr
  cases he : JuliaLean.Bindings.base.reshapedarray.reshapeArrayHeader v #v[v.dims[0], int 1] with
  | error e => simp only [he, Except.mapError] at hr; cases hr
  | ok b' =>
    simp only [he, Except.mapError] at hr
    cases hr
    have hp := sw_reshapeArray_success
      JuliaLean.Bindings.base.reshapedarray.checkedDimsArray
      JuliaLean.Bindings.base.reshapedarray.arrayHeaderLength v #v[v.dims[0], int 1] b he
    refine ⟨hp.1, ?_⟩
    rw [hp.2]
    rfl

theorem sw_rows_vector (constructorLaw : SlicesConstructorPreservesInput)
    (axesLaw : TupleEachsliceAxes) (selectionLaw : TupleEachsliceSelectsRequestedDimensions) :
    EachrowVectorUsesRows := by
  constructor
  · intro E V Ty Vec Parent Ax Code Payload size reshapeDims ops methods printing v N s h
    exact sw_row_vector_generic constructorLaw axesLaw selectionLaw
      size reshapeDims ops methods printing v N s h
  · intro E V Ty T Ref Ax Code Payload ops methods printing v N s h
    have hg := sw_row_vector_generic constructorLaw axesLaw selectionLaw
      arraySize arrayReshapeToMatrix ops methods printing v N s h
    exact sw_array_vector_reshape v (parent s) hg.2.1

theorem sw_cols_vector (constructorLaw : SlicesConstructorPreservesInput)
    (axesLaw : TupleEachsliceAxes) (selectionLaw : TupleEachsliceSelectsRequestedDimensions) :
    EachcolVectorUsesSingleColumn := by
  constructor
  · intro E V Ty Vec Parent Ax Code Payload size reshapeDims ops methods printing v N s h
    exact sw_col_vector_generic constructorLaw axesLaw selectionLaw
      size reshapeDims ops methods printing v N s h
  · intro E V Ty T Ref Ax Code Payload ops methods printing v N s h
    have hg := sw_col_vector_generic constructorLaw axesLaw selectionLaw
      arraySize arrayReshapeToMatrix ops methods printing v N s h
    exact sw_array_vector_reshape v (parent s) hg.2.1

end JuliaLean.ChatGPT.Batch4.Group10

namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean.Proofs.base.slicearray

/-- multidimcov-slice-l233-axes -/
theorem MultidimcovSliceL233Axes_proven : JuliaLean.Proofs.base.slicearray.TupleEachsliceAxes :=
  sa_axes sc_constructor_preserves

/-- multidimcov-slice-l234-size -/
theorem MultidimcovSliceL234Size_proven : JuliaLean.Proofs.base.slicearray.TupleEachsliceSizeMatchesAxes :=
  sa_size_from_axes MultidimcovSliceL233Axes_proven

/-- multidimcov-slice-l58-eachslice-tuple -/
theorem MultidimcovSliceL58EachsliceTuple_proven : JuliaLean.Proofs.base.slicearray.TupleEachsliceContract :=
  ⟨MultidimcovSliceL233Axes_proven, MultidimcovSliceL234Size_proven,
    ss_tupleSelectionFromConstructor sc_constructor_preserves⟩

/-- multidimcov-slicearray-faithful-58 -/
theorem MultidimcovSlicearrayFaithful58_proven : JuliaLean.Proofs.base.slicearray.TupleEachsliceContract :=
  MultidimcovSliceL58EachsliceTuple_proven

/-- multidimcov-slice-l78-eachslice-dim -/
theorem MultidimcovSliceL78EachsliceDim_proven : JuliaLean.Proofs.base.slicearray.IntegerEachsliceUsesItsAxis :=
  sw_integer_contract MultidimcovSliceL58EachsliceTuple_proven

/-- multidimcov-slicearray-faithful-78 -/
theorem MultidimcovSlicearrayFaithful78_proven : JuliaLean.Proofs.base.slicearray.IntegerEachsliceUsesItsAxis :=
  MultidimcovSliceL78EachsliceDim_proven

/-- multidimcov-slice-l39-unitaxis -/
theorem MultidimcovSliceL39Unitaxis_proven : JuliaLean.Proofs.base.slicearray.DropFalseKeepsSingletonAxes :=
  ⟨by intro A Ax oneTo a; rfl, MultidimcovSliceL233Axes_proven,
    MultidimcovSliceL78EachsliceDim_proven⟩

/-- multidimcov-slice-l132-eachslice -/
theorem MultidimcovSliceL132Eachslice_proven : JuliaLean.Proofs.base.slicearray.EachslicePublicContract :=
  sw_public_contract sc_constructor_preserves MultidimcovSliceL58EachsliceTuple_proven

/-- multidimcov-slicearray-faithful-132 -/
theorem MultidimcovSlicearrayFaithful132_proven : JuliaLean.Proofs.base.slicearray.EachslicePublicContract :=
  MultidimcovSliceL132Eachslice_proven

/-- multidimcov-slice-l171-eachrow-matrix -/
theorem MultidimcovSliceL171EachrowMatrix_proven : JuliaLean.Proofs.base.slicearray.EachrowMatrixUsesRows :=
  sw_rows_matrix sc_constructor_preserves MultidimcovSliceL233Axes_proven
    MultidimcovSliceL58EachsliceTuple_proven.2.2

/-- multidimcov-slicearray-faithful-171 -/
theorem MultidimcovSlicearrayFaithful171_proven : JuliaLean.Proofs.base.slicearray.EachrowMatrixUsesRows :=
  MultidimcovSliceL171EachrowMatrix_proven

/-- multidimcov-slice-l209-eachcol-matrix -/
theorem MultidimcovSliceL209EachcolMatrix_proven : JuliaLean.Proofs.base.slicearray.EachcolMatrixUsesColumns :=
  sw_cols_matrix sc_constructor_preserves MultidimcovSliceL233Axes_proven
    MultidimcovSliceL58EachsliceTuple_proven.2.2

/-- multidimcov-slicearray-faithful-209 -/
theorem MultidimcovSlicearrayFaithful209_proven : JuliaLean.Proofs.base.slicearray.EachcolMatrixUsesColumns :=
  MultidimcovSliceL209EachcolMatrix_proven

/-- multidimcov-slice-l172-eachrow-vector -/
theorem MultidimcovSliceL172EachrowVector_proven : JuliaLean.Proofs.base.slicearray.EachrowVectorUsesRows :=
  sw_rows_vector sc_constructor_preserves MultidimcovSliceL233Axes_proven
    MultidimcovSliceL58EachsliceTuple_proven.2.2

/-- multidimcov-slicearray-faithful-172 -/
theorem MultidimcovSlicearrayFaithful172_proven : JuliaLean.Proofs.base.slicearray.EachrowVectorUsesRows :=
  MultidimcovSliceL172EachrowVector_proven

/-- multidimcov-slice-l210-eachcol-vector -/
theorem MultidimcovSliceL210EachcolVector_proven : JuliaLean.Proofs.base.slicearray.EachcolVectorUsesSingleColumn :=
  sw_cols_vector sc_constructor_preserves MultidimcovSliceL233Axes_proven
    MultidimcovSliceL58EachsliceTuple_proven.2.2

/-- multidimcov-slicearray-faithful-210 -/
theorem MultidimcovSlicearrayFaithful210_proven : JuliaLean.Proofs.base.slicearray.EachcolVectorUsesSingleColumn :=
  MultidimcovSliceL210EachcolVector_proven

/-- multidimcov-slice-l249-parent -/
theorem MultidimcovSliceL249Parent_proven : JuliaLean.Proofs.base.slicearray.SlicesParentIdentity :=
  ⟨sw_eachslice_parent sc_constructor_preserves, MultidimcovSliceL171EachrowMatrix_proven,
    MultidimcovSliceL172EachrowVector_proven, MultidimcovSliceL209EachcolMatrix_proven,
    MultidimcovSliceL210EachcolVector_proven⟩

/-- multidimcov-slicearray-faithful-249 -/
theorem MultidimcovSlicearrayFaithful249_proven : JuliaLean.Proofs.base.slicearray.SlicesParentIdentity :=
  MultidimcovSliceL249Parent_proven

/-- multidimcov-slices-construct-full -/
theorem MultidimcovSlicesConstructFull_proven : JuliaLean.Proofs.base.slicearray.SlicesConstructBehavior :=
  ⟨MultidimcovSliceL41Constructor_proven, MultidimcovSliceL58EachsliceTuple_proven,
    MultidimcovSliceL78EachsliceDim_proven, MultidimcovSliceL132Eachslice_proven,
    MultidimcovSliceL249Parent_proven⟩

end JuliaLean.ChatGPT.Batch4.Group10
end

namespace JuliaLean.Proofs.base.slicearray
def entries : List JuliaLean.Registry.Entry := [
  provenEntry "memsafety-slices-constructor-axes"
    ["Slices(A, slicemap, ax)", "getindex(::Slices, I...)", "setindex!(::Slices, val, I...)"]
    "Under the parent view, getindex, and setindex! laws, S[I][k] reads the parent at coordinates selected by I and k; S[I]=v updates those positions and leaves others unchanged."
    "Slices axes and the AbstractArray bounds invariant; base/slicearray.jl:41-49,236-247"
    ``SlicesAccessesInBounds
    ``JuliaLean.ChatGPT.Batch4.Group10.MemsafetySlicesConstructorAxes_proven,
  provenEntry "multidimcov-slice-l39-unitaxis" ["unitaxis(::AbstractArray)"]
    "drop=false preserves selected axes and gives every unselected position a OneTo(1) axis."
    "base/slicearray.jl:39 and the eachslice drop=false docstring at 89-92"
    ``DropFalseKeepsSingletonAxes
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL39Unitaxis_proven,
  provenEntry "multidimcov-slice-l41-constructor" ["Slices(A,slicemap,axes)"]
    "A short slicemap throws ArgumentError; successful construction keeps its parent, map, axes, and promoted view type."
    "Slices constructor invariant; base/slicearray.jl:41-49"
    ``SlicesConstructorInvariant
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL41Constructor_proven,
  provenEntry "multidimcov-slice-l51-check-empty" ["_slice_check_dims()"]
    "The empty dimensions tuple yields one zero-dimensional slice that selects the whole parent."
    "base/slicearray.jl:51-52 and eachslice dimensions contract"
    ``EmptyDimensionsProduceWholeParentSlice
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL51CheckEmpty_proven,
  provenEntry "multidimcov-slice-l52-check" ["_slice_check_dims(dim,dims...)"]
    "Nonpositive or repeated dimensions raise DimensionMismatch; positive, pairwise-distinct dimensions pass."
    "eachslice invalid-dimension contract; base/slicearray.jl:52-56,85-92"
    ``InvalidDimensionsThrow
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL52Check_proven,
  provenEntry "multidimcov-slice-l58-eachslice-tuple" ["_eachslice(::AbstractArray,::NTuple,::Bool)"]
    "For any dimension tuple, each slice fixes the requested parent coordinates and leaves other coordinates unsliced; output axes and size follow drop."
    "eachslice docstring; base/slicearray.jl:58-77,82-92"
    ``TupleEachsliceContract
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL58EachsliceTuple_proven,
  provenEntry "multidimcov-slice-l78-eachslice-dim" ["_eachslice(::AbstractArray,::Integer,::Bool)"]
    "For integer dims, each slice fixes that parent coordinate; drop=true keeps its axis, while drop=false preserves rank and singleton axes."
    "eachslice docstring; base/slicearray.jl:78-80,85-92"
    ``IntegerEachsliceUsesItsAxis
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL78EachsliceDim_proven,
  provenEntry "multidimcov-slice-l132-eachslice" ["eachslice(A;dims,drop)"]
    "The public eachslice result retains its parent and returns the documented axes, size, and parent-coordinate selection for integer and tuple dims."
    "eachslice docstring; base/slicearray.jl:82-92,132-134"
    ``EachslicePublicContract
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL132Eachslice_proven,
  provenEntry "multidimcov-slice-l171-eachrow-matrix" ["eachrow(::AbstractMatrix)"]
    "eachrow on a matrix returns one-dimensional row slices with the input parent, each fixing only dimension one."
    "eachrow docstring; base/slicearray.jl:136-169,171"
    ``EachrowMatrixUsesRows
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL171EachrowMatrix_proven,
  provenEntry "multidimcov-slice-l172-eachrow-vector" ["eachrow(::AbstractVector)"]
    "eachrow on a vector returns one-dimensional row slices of its two-dimensional reshape, each fixing only dimension one."
    "eachrow docstring; base/slicearray.jl:136-172"
    ``EachrowVectorUsesRows
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL172EachrowVector_proven,
  provenEntry "multidimcov-slice-l209-eachcol-matrix" ["eachcol(::AbstractMatrix)"]
    "eachcol on a matrix returns one-dimensional column slices with the input parent, each fixing only dimension two."
    "eachcol docstring; base/slicearray.jl:174-207,209"
    ``EachcolMatrixUsesColumns
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL209EachcolMatrix_proven,
  provenEntry "multidimcov-slice-l210-eachcol-vector" ["eachcol(::AbstractVector)"]
    "eachcol on a vector returns one-dimensional column slices of its reshape, each fixing only dimension two."
    "eachcol docstring; base/slicearray.jl:174-210"
    ``EachcolVectorUsesSingleColumn
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL210EachcolVector_proven,
  provenEntry "multidimcov-slice-l233-axes" ["axes(::Slices)"]
    "drop=true preserves requested parent axes in order; drop=false keeps rank max(ndims(A), greatest dims), using ndims(A) for empty dims, with OneTo(1) elsewhere."
    "eachslice docstring; base/slicearray.jl:82-92,233"
    ``TupleEachsliceAxes
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL233Axes_proven,
  provenEntry "multidimcov-slice-l234-size" ["size(::Slices)"]
    "For any dimension count, size is the selected parent-axis lengths with drop=true and adds ones at unselected positions with drop=false."
    "eachslice docstring; base/slicearray.jl:82-92,234"
    ``TupleEachsliceSizeMatchesAxes
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL234Size_proven,
  provenEntry "multidimcov-slice-l236-index" ["_slice_index(::Slices,...)"]
    "Each non-colon map entry uses its matching outer coordinate, colon entries retain every parent coordinate, and missing coordinates throw BoundsError."
    "Slices indexing behavior; base/slicearray.jl:236-238"
    ``SliceIndexBehavior
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL236Index_proven,
  provenEntry "multidimcov-slice-l240-getindex" ["getindex(::Slices,::Vararg{Int})"]
    "For every in-bounds outer index I and inner index k, S[I][k] reads the parent coordinate formed by filling colon slots with k and fixed slots with I."
    "eachslice, eachrow, and eachcol docstrings; base/slicearray.jl:119-123,165-168,203-206,240-243"
    ``SlicesElementsAreParentViews
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL240Getindex_proven,
  provenEntry "multidimcov-slice-l244-setindex" ["setindex!(::Slices,val,::Vararg{Int})"]
    "After a successful S[I]=v, selected parent positions contain the corresponding elements of v; other positions remain unchanged under the parent setter law."
    "AbstractArray indexing invariant; base/slicearray.jl:244-247"
    ``SlicesAssignmentTargetsMappedParent
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL244Setindex_proven,
  provenEntry "multidimcov-slice-l249-parent" ["parent(::Slices)"]
    "eachslice, eachrow, and eachcol results retain their original array or reshape parent."
    "AbstractSlices and Slices docstrings; base/slicearray.jl:1-20,249"
    ``SlicesParentIdentity
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceL249Parent_proven,
  provenEntry "multidimcov-slices-construct-full" ["_eachslice/eachslice/eachrow/eachcol"]
    "Valid dimensions produce Slices with the documented parent, view type, axes, size, and selected coordinates."
    "eachslice, eachrow, and eachcol docstrings; base/slicearray.jl:41-210"
    ``SlicesConstructBehavior
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicesConstructFull_proven,
  provenEntry "multidimcov-slice-index-checked" ["_slice_index(::Slices,c...)"]
    "A missing mapped outer coordinate throws BoundsError; successful mapping preserves colon coordinates and selects the corresponding parent values."
    "Sliced-array indexing invariant; base/slicearray.jl:236-238"
    ``SliceIndexBehavior
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSliceIndexChecked_proven,
  provenEntry "multidimcov-slices-get-full" ["getindex(::Slices,I...)"]
    "A successful Slices lookup returns a view whose read at each inner index equals the parent read at the slicemap-selected coordinates."
    "AbstractArray indexing invariant; base/slicearray.jl:240-243"
    ``SlicesElementsAreParentViews
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicesGetFull_proven,
  provenEntry "multidimcov-slices-set-full" ["setindex!(::Slices,val,I...)"]
    "A successful Slices assignment updates each selected parent position from the corresponding value element and leaves other positions unchanged."
    "AbstractArray indexing invariant; base/slicearray.jl:244-247"
    ``SlicesAssignmentTargetsMappedParent
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicesSetFull_proven,
  provenEntry "multidimcov-slicearray-faithful-41" ["Slices"]
    "Construction rejects maps shorter than the parent rank and otherwise preserves the parent, slicemap, axes, and promoted view type."
    "Slices constructor invariant; base/slicearray.jl:41-49"
    ``SlicesConstructorInvariant
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful41_proven,
  provenEntry "multidimcov-slicearray-faithful-52" ["_slice_check_dims"]
    "Nonpositive or repeated dimensions raise DimensionMismatch; positive, pairwise-distinct dimensions pass."
    "eachslice invalid-dimension contract; base/slicearray.jl:52-60"
    ``InvalidDimensionsThrow
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful52_proven,
  provenEntry "multidimcov-slicearray-faithful-58" ["_eachslice"]
    "For every dimension tuple, slice coordinates, axes, and size match the requested dimensions and drop setting."
    "eachslice docstring; base/slicearray.jl:58-77,82-92"
    ``TupleEachsliceContract
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful58_proven,
  provenEntry "multidimcov-slicearray-faithful-78" ["_eachslice(single dim)"]
    "The integer overload fixes the selected coordinate and preserves its axis when dropping or singleton axes elsewhere when retaining rank."
    "eachslice docstring; base/slicearray.jl:78-80,85-92"
    ``IntegerEachsliceUsesItsAxis
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful78_proven,
  provenEntry "multidimcov-slicearray-faithful-132" ["eachslice"]
    "The public eachslice result retains its parent and maps each output index to the requested fixed parent coordinates."
    "eachslice docstring; base/slicearray.jl:82-92,132-134"
    ``EachslicePublicContract
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful132_proven,
  provenEntry "multidimcov-slicearray-faithful-171" ["eachrow(matrix)"]
    "Matrix rows have the input parent, one outer index per row, and only the first parent dimension selected."
    "eachrow docstring; base/slicearray.jl:136-171"
    ``EachrowMatrixUsesRows
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful171_proven,
  provenEntry "multidimcov-slicearray-faithful-172" ["eachrow(vector)"]
    "Vector rows are one-dimensional slices of the reshaped vector, selected only along dimension one."
    "eachrow docstring; base/slicearray.jl:136-172"
    ``EachrowVectorUsesRows
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful172_proven,
  provenEntry "multidimcov-slicearray-faithful-209" ["eachcol(matrix)"]
    "Matrix columns have the input parent, one outer index per column, and only the second parent dimension selected."
    "eachcol docstring; base/slicearray.jl:174-209"
    ``EachcolMatrixUsesColumns
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful209_proven,
  provenEntry "multidimcov-slicearray-faithful-210" ["eachcol(vector)"]
    "A vector's column slices select only dimension two of its two-dimensional reshape."
    "eachcol docstring; base/slicearray.jl:174-210"
    ``EachcolVectorUsesSingleColumn
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful210_proven,
  provenEntry "multidimcov-slicearray-faithful-236" ["_slice_index"]
    "Successful indexing maps selected coordinates to fixed parent positions, preserves colon dimensions, and rejects missing outer indices."
    "Slices indexing behavior; base/slicearray.jl:236-238"
    ``SliceIndexBehavior
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful236_proven,
  provenEntry "multidimcov-slicearray-faithful-240" ["getindex"]
    "For every valid outer index and inner view index, the read matches the parent at coordinates obtained by filling colons from the inner index."
    "eachslice, eachrow, and eachcol docstrings; base/slicearray.jl:119-123,165-168,203-206,240-243"
    ``SlicesElementsAreParentViews
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful240_proven,
  provenEntry "multidimcov-slicearray-faithful-244" ["setindex!"]
    "A successful assignment changes the mapped parent positions to the corresponding value elements and leaves all other positions unchanged."
    "AbstractArray indexing invariant; base/slicearray.jl:244-247"
    ``SlicesAssignmentTargetsMappedParent
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful244_proven,
  provenEntry "multidimcov-slicearray-faithful-249" ["parent"]
    "eachslice, eachrow, and eachcol results retain their array or reshape parent and preserve the documented selected axes."
    "AbstractSlices and Slices docstrings; base/slicearray.jl:1-20,249"
    ``SlicesParentIdentity
    ``JuliaLean.ChatGPT.Batch4.Group10.MultidimcovSlicearrayFaithful249_proven,
]

end JuliaLean.Proofs.base.slicearray

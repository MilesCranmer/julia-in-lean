import JuliaLean.base.slicearray
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.slicearray

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.slicearray

def i64Value (value : I64) : Int := value.val
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
def ParentViewGetindexLaw {Parent View Value Element : Type}
    (ops : SliceArrayOps Parent View Value Element) : Prop :=
  ∀ parent selected viewValue inner parentCoordinates,
    ops.view parent selected = .ok viewValue →
    ParentCoordinatesFollowSelectors selected inner parentCoordinates →
    ops.getindexView viewValue inner = ops.getindexParent parent parentCoordinates

def ParentSetindexEffectLaw {Parent View Value Element : Type}
    (ops : SliceArrayOps Parent View Value Element) : Prop :=
  ∀ parent selected value,
    ops.setindexParent parent selected value = .ok value →
    ∃ updatedParent,
      (∀ inner parentCoordinates,
        ParentCoordinatesFollowSelectors selected inner parentCoordinates →
        ops.getindexParent updatedParent parentCoordinates = ops.getindexValue value inner) ∧
      (∀ parentCoordinates,
        (∀ inner, ¬ ParentCoordinatesFollowSelectors selected inner parentCoordinates) →
        ops.getindexParent updatedParent parentCoordinates =
          ops.getindexParent parent parentCoordinates)



def RequestedSliceCoordinates {Parent D : Type} {N : Nat}
    (s : Slices Parent N) (dimensionValue : D → Int) (dims : List D)
    (drop : Bool) (indices : IntegerIndices N) (selected : List (Option I64)) : Prop :=
  selected.length = s.slicemap.length ∧
    ∀ parentDimension, parentDimension < s.slicemap.length →
      if drop then
        match dims.findIdx? (fun dimension =>
          dimensionValue dimension == Int.ofNat (parentDimension + 1)) with
        | some outerDimension =>
            ∃ coordinate,
              indices.values[outerDimension]? = some coordinate ∧
                selected[parentDimension]? = some (some coordinate)
        | none => selected[parentDimension]? = some none
      else if dims.any (fun dimension =>
          dimensionValue dimension == Int.ofNat (parentDimension + 1)) then
        ∃ coordinate,
          indices.values[parentDimension]? = some coordinate ∧
            selected[parentDimension]? = some (some coordinate)
      else
        selected[parentDimension]? = some none




def SlicesConstructorRejectsShortMap : Prop :=
  ∀ {A View Value Element : Type} (ops : SliceArrayOps A View Value Element) (a : A)
      (slicemap : List (Option Nat)) (outerAxes : List SliceAxis),
    slicemap.length < ops.ndims a →
    match slicesConstructor ops a slicemap outerAxes with
    | .error (.julia (.argumentError _)) => True
    | _ => False

def SlicesConstructorPreservesInput : Prop :=
  ∀ {A View Value Element : Type} (ops : SliceArrayOps A View Value Element) (a : A)
      (slicemap : List (Option Nat)) (outerAxes : List SliceAxis)
      (N : Nat) (s : Slices A N),
    let parentAxes := (List.range slicemap.length).map fun d : Nat =>
      ops.axes a (int (Int.ofNat (d + 1)))
    let argumentTypes := List.zipWith
      (fun axis entry => match entry with
        | none => .colon
        | some _ => .index axis.indexType)
      parentAxes slicemap
    parent s = a ∧ s.slicemap = slicemap ∧ axes s = outerAxes ∧
      s.viewType = ops.promoteView ops.parentType argumentTypes

def SlicesConstructorInvariant : Prop :=
  SlicesConstructorRejectsShortMap ∧ SlicesConstructorPreservesInput

def UnitAxisIsSingleton : Prop :=
  ∀ {A : Type} (a : A),
    (unitaxis a).first = int 1 ∧ (unitaxis a).length = int 1

def EmptyDimensionsProduceWholeParentSlice : Prop :=
  ∀ {A View Value Element : Type} (ops : SliceArrayOps A View Value Element) (a : A) (N : Nat) (s : Slices A N),
    eachsliceTuple ops i64Value a ([] : List I64) true = .ok ⟨N, s⟩ →
    N = 0 ∧ size s = [] ∧ s.slicemap.length = ops.ndims a ∧
      (∀ entry, entry ∈ s.slicemap → entry = none) ∧ parent s = a

def InvalidDimensionsThrow : Prop :=
  ∀ {A D View Value Element : Type} (ops : SliceArrayOps A View Value Element) (dimensionValue : D → Int)
      (dims : List D),
    (((∃ dimension, dimension ∈ dims ∧ dimensionValue dimension < 1) ∨
      ¬ List.Pairwise (fun left right =>
        dimensionValue left ≠ dimensionValue right) dims) →
      match sliceCheckDims dimensionValue ops.showInteger ops.showIntegerTuple dims with
      | .error (.dimensionMismatch _) => True
      | _ => False) ∧
    ((∀ dimension, dimension ∈ dims → dimensionValue dimension ≥ 1) →
      List.Pairwise (fun left right =>
        dimensionValue left ≠ dimensionValue right) dims →
      sliceCheckDims dimensionValue ops.showInteger ops.showIntegerTuple dims = .ok ())
def TupleEachsliceAxes : Prop :=
  ∀ {A D View Value Element : Type} (ops : SliceArrayOps A View Value Element) (dimensionValue : D → Int)
      (a : A) (dims : List D) (drop : Bool) (N : Nat) (s : Slices A N),
    eachsliceTuple ops dimensionValue a dims drop = .ok ⟨N, s⟩ →
    if drop then
      N = dims.length ∧ axes s = dims.map (ops.axes a)
    else
      N = dims.foldl (fun rank dimension => max rank (dimensionValue dimension).toNat) (ops.ndims a) ∧
      ∀ position, position < N →
        if dims.any (fun dimension =>
          dimensionValue dimension == Int.ofNat (position + 1)) then
          (axes s)[position]? = some (ops.axes a (int (Int.ofNat (position + 1))))
        else
          (axes s)[position]? = some (unitaxis a)
def TupleEachsliceSizeMatchesAxes : Prop :=
  ∀ {A D View Value Element : Type} (ops : SliceArrayOps A View Value Element) (dimensionValue : D → Int)
      (a : A) (dims : List D) (drop : Bool) (N : Nat) (s : Slices A N),
    eachsliceTuple ops dimensionValue a dims drop = .ok ⟨N, s⟩ →
    if drop then
      N = dims.length ∧
        size s = dims.map fun dimension => (ops.axes a dimension).length
    else
      N = dims.foldl (fun rank dimension => max rank (dimensionValue dimension).toNat) (ops.ndims a) ∧
      size s = (List.range N).map fun position =>
        if dims.any (fun dimension =>
          dimensionValue dimension == Int.ofNat (position + 1)) then
          (ops.axes a (int (Int.ofNat (position + 1)))).length
        else int 1

def TupleEachsliceSelectsRequestedDimensions : Prop :=
  ∀ {A D View Value Element : Type} (ops : SliceArrayOps A View Value Element) (dimensionValue : D → Int)
      (a : A) (dims : List D) (drop : Bool) (N : Nat) (s : Slices A N),
    eachsliceTuple ops dimensionValue a dims drop = .ok ⟨N, s⟩ →
    ∀ indices selected,
      sliceIndex s indices.values = .ok selected →
      RequestedSliceCoordinates s dimensionValue dims drop indices selected
def TupleEachsliceContract : Prop :=
  TupleEachsliceAxes ∧ TupleEachsliceSizeMatchesAxes ∧
    TupleEachsliceSelectsRequestedDimensions

def IntegerEachsliceUsesItsAxis : Prop :=
  ∀ {A D View Value Element : Type} (ops : SliceArrayOps A View Value Element) (dimensionValue : D → Int)
      (a : A) (dimension : D) (drop : Bool) (N : Nat) (s : Slices A N),
    eachslice (eachsliceDimension ops dimensionValue) a dimension drop = .ok ⟨N, s⟩ →
    (if drop then
      N = 1 ∧ size s = [(ops.axes a dimension).length] ∧
        axes s = [ops.axes a dimension]
    else
      N = max (ops.ndims a) (dimensionValue dimension).toNat ∧
      size s = ((List.range N).map fun position =>
        if dimensionValue dimension == Int.ofNat (position + 1) then
          (ops.axes a (int (Int.ofNat (position + 1)))).length
        else int 1) ∧
      ∀ position, position < N →
        if dimensionValue dimension == Int.ofNat (position + 1) then
          (axes s)[position]? = some (ops.axes a (int (Int.ofNat (position + 1))))
        else
          (axes s)[position]? = some (unitaxis a)) ∧
    ∀ indices selected,
      sliceIndex s indices.values = .ok selected →
      RequestedSliceCoordinates s dimensionValue [dimension] drop indices selected
def DropFalseKeepsSingletonAxes : Prop :=
  UnitAxisIsSingleton ∧ TupleEachsliceAxes ∧ IntegerEachsliceUsesItsAxis

def EachsliceTupleParentIdentity : Prop :=
  ∀ {A D View Value Element : Type} (ops : SliceArrayOps A View Value Element) (dimensionValue : D → Int)
      (a : A) (dims : List D) (drop : Bool) (N : Nat) (s : Slices A N),
    eachslice (eachsliceTuple ops dimensionValue) a dims drop = .ok ⟨N, s⟩ →
    parent s = a

def EachsliceIntegerParentIdentity : Prop :=
  ∀ {A D View Value Element : Type} (ops : SliceArrayOps A View Value Element) (dimensionValue : D → Int)
      (a : A) (dimension : D) (drop : Bool) (N : Nat) (s : Slices A N),
    eachslice (eachsliceDimension ops dimensionValue) a dimension drop = .ok ⟨N, s⟩ →
    parent s = a

def EachsliceParentIdentity : Prop :=
  EachsliceTupleParentIdentity ∧ EachsliceIntegerParentIdentity
def EachslicePublicTupleSelectsRequestedDimensions : Prop :=
  ∀ {A D View Value Element : Type} (ops : SliceArrayOps A View Value Element) (dimensionValue : D → Int)
      (a : A) (dims : List D) (drop : Bool) (N : Nat) (s : Slices A N),
    eachslice (eachsliceTuple ops dimensionValue) a dims drop = .ok ⟨N, s⟩ →
    ∀ indices selected,
      sliceIndex s indices.values = .ok selected →
      RequestedSliceCoordinates s dimensionValue dims drop indices selected

def EachslicePublicIntegerSelectsRequestedDimension : Prop :=
  ∀ {A D View Value Element : Type} (ops : SliceArrayOps A View Value Element) (dimensionValue : D → Int)
      (a : A) (dimension : D) (drop : Bool) (N : Nat) (s : Slices A N),
    eachslice (eachsliceDimension ops dimensionValue) a dimension drop = .ok ⟨N, s⟩ →
    ∀ indices selected,
      sliceIndex s indices.values = .ok selected →
      RequestedSliceCoordinates s dimensionValue [dimension] drop indices selected

def EachslicePublicSelectsRequestedDimensions : Prop :=
  EachslicePublicTupleSelectsRequestedDimensions ∧
    EachslicePublicIntegerSelectsRequestedDimension

def EachslicePublicContract : Prop :=
  EachsliceParentIdentity ∧ EachslicePublicSelectsRequestedDimensions ∧
    TupleEachsliceAxes ∧ TupleEachsliceSizeMatchesAxes ∧
    IntegerEachsliceUsesItsAxis


def EachrowMatrixUsesRows : Prop :=
  ∀ {A View Value Element : Type} (ops : SliceArrayOps A View Value Element) (a : A) (N : Nat) (s : Slices A N),
    eachrowMatrix (eachsliceTuple ops i64Value) a = .ok ⟨N, s⟩ →
    N = 1 ∧ parent s = a ∧ size s = [(ops.axes a (int 1)).length] ∧
    ∀ indices selected,
      sliceIndex s indices.values = .ok selected →
      RequestedSliceCoordinates s i64Value [int 1] true indices selected

def EachrowVectorUsesRows : Prop :=
  ∀ {A B View Value Element : Type} (ops : SliceArrayOps B View Value Element)
      (sizeDim : A → I64 → Result I64)
      (reshape : A → I64 → I64 → Result B)
      (a : A) (firstSize : I64) (b : B) (N : Nat) (s : Slices B N),
    sizeDim a (int 1) = .ok firstSize →
    reshape a firstSize (int 1) = .ok b →
    ops.ndims b = 2 →
    (ops.axes b (int 1)).length = firstSize →
    (ops.axes b (int 2)).length = int 1 →
    eachrowVector sizeDim reshape
      (eachrowMatrix (eachsliceTuple ops i64Value)) a = .ok ⟨N, s⟩ →
    N = 1 ∧ parent s = b ∧ size s = [firstSize] ∧
    ∀ indices selected,
      sliceIndex s indices.values = .ok selected →
      RequestedSliceCoordinates s i64Value [int 1] true indices selected

def EachcolMatrixUsesColumns : Prop :=
  ∀ {A View Value Element : Type} (ops : SliceArrayOps A View Value Element) (a : A) (N : Nat) (s : Slices A N),
    eachcolMatrix (eachsliceTuple ops i64Value) a = .ok ⟨N, s⟩ →
    N = 1 ∧ parent s = a ∧ size s = [(ops.axes a (int 2)).length] ∧
    ∀ indices selected,
      sliceIndex s indices.values = .ok selected →
      RequestedSliceCoordinates s i64Value [int 2] true indices selected

def EachcolVectorUsesSingleColumn : Prop :=
  ∀ {A B View Value Element : Type} (ops : SliceArrayOps B View Value Element)
      (sizeDim : A → I64 → Result I64)
      (reshape : A → I64 → I64 → Result B)
      (a : A) (firstSize : I64) (b : B) (N : Nat) (s : Slices B N),
    sizeDim a (int 1) = .ok firstSize →
    reshape a firstSize (int 1) = .ok b →
    ops.ndims b = 2 →
    (ops.axes b (int 1)).length = firstSize →
    (ops.axes b (int 2)).length = int 1 →
    eachcolVector sizeDim reshape
      (eachcolMatrix (eachsliceTuple ops i64Value)) a = .ok ⟨N, s⟩ →
    N = 1 ∧ parent s = b ∧ size s = [int 1] ∧
    ∀ indices selected,
      sliceIndex s indices.values = .ok selected →
      RequestedSliceCoordinates s i64Value [int 2] true indices selected
def SlicesParentIdentity : Prop :=
  EachsliceParentIdentity ∧ EachrowMatrixUsesRows ∧ EachrowVectorUsesRows ∧
    EachcolMatrixUsesColumns ∧ EachcolVectorUsesSingleColumn
def SlicesConstructBehavior : Prop :=
  SlicesConstructorInvariant ∧ TupleEachsliceContract ∧
    IntegerEachsliceUsesItsAxis ∧ EachslicePublicContract ∧ SlicesParentIdentity

def SliceIndexFollowsSlicemap : Prop :=
  ∀ {Parent : Type} {N : Nat} (s : Slices Parent N)
      (coordinates : List I64) (selected : List (Option I64)),
    sliceIndex s coordinates = .ok selected →
    selected.length = s.slicemap.length ∧
    ∀ parentDimension, parentDimension < s.slicemap.length →
      match s.slicemap[parentDimension]? with
      | some none => selected[parentDimension]? = some none
      | some (some outerDimension) =>
          outerDimension > 0 ∧
          ∃ coordinate,
            coordinates[(outerDimension - 1)]? = some coordinate ∧
              selected[parentDimension]? = some (some coordinate)
      | none => False

def SlicesElementsAreParentViews : Prop :=
  ∀ {Parent View Value Element : Type} {N : Nat}
      (ops : SliceArrayOps Parent View Value Element) (s : Slices Parent N)
      (indices : IntegerIndices N)
      (checkbounds : Slices Parent N → IntegerIndices N → Result Unit),
    ParentViewGetindexLaw ops →
    checkbounds s indices = .ok () →
    ((∀ selected viewValue,
      sliceIndex s indices.values = .ok selected →
      ops.view s.parent selected = .ok viewValue →
      getindex checkbounds ops s indices = .ok viewValue ∧
      ∀ inner parentCoordinates,
        ParentCoordinatesFollowSelectors selected inner parentCoordinates →
        ops.getindexView viewValue inner = ops.getindexParent s.parent parentCoordinates) ∧
    (∀ selected error,
      sliceIndex s indices.values = .ok selected →
      ops.view s.parent selected = .error error →
      getindex checkbounds ops s indices = .error error))

def SlicesAssignmentTargetsMappedParent : Prop :=
  ∀ {Parent View Value Element : Type} {N : Nat}
      (ops : SliceArrayOps Parent View Value Element) (s : Slices Parent N)
      (value : Value) (indices : IntegerIndices N)
      (checkbounds : Slices Parent N → IntegerIndices N → Result Unit),
    ParentSetindexEffectLaw ops →
    checkbounds s indices = .ok () →
    ∀ selected,
      sliceIndex s indices.values = .ok selected →
      setindex! checkbounds ops s value indices = .ok value →
      ∃ updatedParent,
        ops.setindexParent s.parent selected value = .ok value ∧
        (∀ inner parentCoordinates,
          ParentCoordinatesFollowSelectors selected inner parentCoordinates →
          ops.getindexParent updatedParent parentCoordinates =
            ops.getindexValue value inner) ∧
        (∀ parentCoordinates,
          (∀ inner, ¬ ParentCoordinatesFollowSelectors selected inner parentCoordinates) →
          ops.getindexParent updatedParent parentCoordinates =
            ops.getindexParent s.parent parentCoordinates)

def SliceIndexRejectsMissingCoordinates : Prop :=
  ∀ {Parent : Type} {N : Nat} (s : Slices Parent N)
      (coordinates : List I64) (parentDimension outerDimension : Nat),
    s.slicemap[parentDimension]? = some (some outerDimension) →
    outerDimension > 0 →
    coordinates[(outerDimension - 1)]? = none →
    sliceIndex s coordinates = .error (.julia .boundsError)
def SliceIndexBehavior : Prop :=
  SliceIndexRejectsMissingCoordinates ∧ SliceIndexFollowsSlicemap

def SlicesAccessesInBounds : Prop :=
  SliceIndexBehavior ∧ SlicesElementsAreParentViews ∧
    SlicesAssignmentTargetsMappedParent
private def todoEntry (id : String) (juliaFns : List String)
    (statement source : String) (prop : Lean.Name) : Entry :=
  { id
    juliaFile := "base/slicearray.jl"
    juliaFns
    statement
    source
    status := .todo
    prop
    thm := none }

def entries : List Entry := [
  todoEntry "memsafety-slices-constructor-axes"
    ["Slices(A, slicemap, ax)", "getindex(::Slices, I...)", "setindex!(::Slices, val, I...)"]
    "Under the parent view, getindex, and setindex! laws, S[I][k] reads the parent at coordinates selected by I and k; S[I]=v updates those positions and leaves others unchanged."
    "Slices axes and the AbstractArray bounds invariant; base/slicearray.jl:41-49,236-247"
    ``SlicesAccessesInBounds,
  todoEntry "multidimcov-slice-l39-unitaxis" ["unitaxis(::AbstractArray)"]
    "drop=false preserves selected axes and gives every unselected position a OneTo(1) axis."
    "base/slicearray.jl:39 and the eachslice drop=false docstring at 89-92"
    ``DropFalseKeepsSingletonAxes,
  todoEntry "multidimcov-slice-l41-constructor" ["Slices(A,slicemap,axes)"]
    "A short slicemap throws ArgumentError; successful construction keeps its parent, map, axes, and promoted view type."
    "Slices constructor invariant; base/slicearray.jl:41-49"
    ``SlicesConstructorInvariant,
  todoEntry "multidimcov-slice-l51-check-empty" ["_slice_check_dims()"]
    "The empty dimensions tuple yields one zero-dimensional slice that selects the whole parent."
    "base/slicearray.jl:51-52 and eachslice dimensions contract"
    ``EmptyDimensionsProduceWholeParentSlice,
  todoEntry "multidimcov-slice-l52-check" ["_slice_check_dims(dim,dims...)"]
    "Nonpositive or repeated dimensions raise DimensionMismatch; positive, pairwise-distinct dimensions pass."
    "eachslice invalid-dimension contract; base/slicearray.jl:52-56,85-92"
    ``InvalidDimensionsThrow,
  todoEntry "multidimcov-slice-l58-eachslice-tuple" ["_eachslice(::AbstractArray,::NTuple,::Bool)"]
    "For any dimension tuple, each slice fixes the requested parent coordinates and leaves other coordinates unsliced; output axes and size follow drop."
    "eachslice docstring; base/slicearray.jl:58-77,82-92"
    ``TupleEachsliceContract,
  todoEntry "multidimcov-slice-l78-eachslice-dim" ["_eachslice(::AbstractArray,::Integer,::Bool)"]
    "For integer dims, each slice fixes that parent coordinate; drop=true keeps its axis, while drop=false preserves rank and singleton axes."
    "eachslice docstring; base/slicearray.jl:78-80,85-92"
    ``IntegerEachsliceUsesItsAxis,
  todoEntry "multidimcov-slice-l132-eachslice" ["eachslice(A;dims,drop)"]
    "The public eachslice result retains its parent and returns the documented axes, size, and parent-coordinate selection for integer and tuple dims."
    "eachslice docstring; base/slicearray.jl:82-92,132-134"
    ``EachslicePublicContract,
  todoEntry "multidimcov-slice-l171-eachrow-matrix" ["eachrow(::AbstractMatrix)"]
    "eachrow on a matrix returns one-dimensional row slices with the input parent, each fixing only dimension one."
    "eachrow docstring; base/slicearray.jl:136-169,171"
    ``EachrowMatrixUsesRows,
  todoEntry "multidimcov-slice-l172-eachrow-vector" ["eachrow(::AbstractVector)"]
    "eachrow on a vector returns one-dimensional row slices of its two-dimensional reshape, each fixing only dimension one."
    "eachrow docstring; base/slicearray.jl:136-172"
    ``EachrowVectorUsesRows,
  todoEntry "multidimcov-slice-l209-eachcol-matrix" ["eachcol(::AbstractMatrix)"]
    "eachcol on a matrix returns one-dimensional column slices with the input parent, each fixing only dimension two."
    "eachcol docstring; base/slicearray.jl:174-207,209"
    ``EachcolMatrixUsesColumns,
  todoEntry "multidimcov-slice-l210-eachcol-vector" ["eachcol(::AbstractVector)"]
    "eachcol on a vector returns one-dimensional column slices of its reshape, each fixing only dimension two."
    "eachcol docstring; base/slicearray.jl:174-210"
    ``EachcolVectorUsesSingleColumn,
  todoEntry "multidimcov-slice-l233-axes" ["axes(::Slices)"]
    "drop=true preserves requested parent axes in order; drop=false keeps rank max(ndims(A), greatest dims), using ndims(A) for empty dims, with OneTo(1) elsewhere."
    "eachslice docstring; base/slicearray.jl:82-92,233"
    ``TupleEachsliceAxes,
  todoEntry "multidimcov-slice-l234-size" ["size(::Slices)"]
    "For any dimension count, size is the selected parent-axis lengths with drop=true and adds ones at unselected positions with drop=false."
    "eachslice docstring; base/slicearray.jl:82-92,234"
    ``TupleEachsliceSizeMatchesAxes,
  todoEntry "multidimcov-slice-l236-index" ["_slice_index(::Slices,...)"]
    "Each non-colon map entry uses its matching outer coordinate, colon entries retain every parent coordinate, and missing coordinates throw BoundsError."
    "Slices indexing behavior; base/slicearray.jl:236-238"
    ``SliceIndexBehavior,
  todoEntry "multidimcov-slice-l240-getindex" ["getindex(::Slices,::Vararg{Int})"]
    "For every in-bounds outer index I and inner index k, S[I][k] reads the parent coordinate formed by filling colon slots with k and fixed slots with I."
    "eachslice, eachrow, and eachcol docstrings; base/slicearray.jl:119-123,165-168,203-206,240-243"
    ``SlicesElementsAreParentViews,
  todoEntry "multidimcov-slice-l244-setindex" ["setindex!(::Slices,val,::Vararg{Int})"]
    "After a successful S[I]=v, selected parent positions contain the corresponding elements of v; other positions remain unchanged under the parent setter law."
    "AbstractArray indexing invariant; base/slicearray.jl:244-247"
    ``SlicesAssignmentTargetsMappedParent,
  todoEntry "multidimcov-slice-l249-parent" ["parent(::Slices)"]
    "eachslice, eachrow, and eachcol results retain their original array or reshape parent."
    "AbstractSlices and Slices docstrings; base/slicearray.jl:1-20,249"
    ``SlicesParentIdentity,
  todoEntry "multidimcov-slices-construct-full" ["_eachslice/eachslice/eachrow/eachcol"]
    "Valid dimensions produce Slices with the documented parent, view type, axes, size, and selected coordinates."
    "eachslice, eachrow, and eachcol docstrings; base/slicearray.jl:41-210"
    ``SlicesConstructBehavior,
  todoEntry "multidimcov-slice-index-checked" ["_slice_index(::Slices,c...)"]
    "A missing mapped outer coordinate throws BoundsError; successful mapping preserves colon coordinates and selects the corresponding parent values."
    "Sliced-array indexing invariant; base/slicearray.jl:236-238"
    ``SliceIndexBehavior,
  todoEntry "multidimcov-slices-get-full" ["getindex(::Slices,I...)"]
    "A successful Slices lookup returns a view whose read at each inner index equals the parent read at the slicemap-selected coordinates."
    "AbstractArray indexing invariant; base/slicearray.jl:240-243"
    ``SlicesElementsAreParentViews,
  todoEntry "multidimcov-slices-set-full" ["setindex!(::Slices,val,I...)"]
    "A successful Slices assignment updates each selected parent position from the corresponding value element and leaves other positions unchanged."
    "AbstractArray indexing invariant; base/slicearray.jl:244-247"
    ``SlicesAssignmentTargetsMappedParent,
  todoEntry "multidimcov-slicearray-faithful-41" ["Slices"]
    "Construction rejects maps shorter than the parent rank and otherwise preserves the parent, slicemap, axes, and promoted view type."
    "Slices constructor invariant; base/slicearray.jl:41-49"
    ``SlicesConstructorInvariant,
  todoEntry "multidimcov-slicearray-faithful-52" ["_slice_check_dims"]
    "Nonpositive or repeated dimensions raise DimensionMismatch; positive, pairwise-distinct dimensions pass."
    "eachslice invalid-dimension contract; base/slicearray.jl:52-60"
    ``InvalidDimensionsThrow,
  todoEntry "multidimcov-slicearray-faithful-58" ["_eachslice"]
    "For every dimension tuple, slice coordinates, axes, and size match the requested dimensions and drop setting."
    "eachslice docstring; base/slicearray.jl:58-77,82-92"
    ``TupleEachsliceContract,
  todoEntry "multidimcov-slicearray-faithful-78" ["_eachslice(single dim)"]
    "The integer overload fixes the selected coordinate and preserves its axis when dropping or singleton axes elsewhere when retaining rank."
    "eachslice docstring; base/slicearray.jl:78-80,85-92"
    ``IntegerEachsliceUsesItsAxis,
  todoEntry "multidimcov-slicearray-faithful-132" ["eachslice"]
    "The public eachslice result retains its parent and maps each output index to the requested fixed parent coordinates."
    "eachslice docstring; base/slicearray.jl:82-92,132-134"
    ``EachslicePublicContract,
  todoEntry "multidimcov-slicearray-faithful-171" ["eachrow(matrix)"]
    "Matrix rows have the input parent, one outer index per row, and only the first parent dimension selected."
    "eachrow docstring; base/slicearray.jl:136-171"
    ``EachrowMatrixUsesRows,
  todoEntry "multidimcov-slicearray-faithful-172" ["eachrow(vector)"]
    "Vector rows are one-dimensional slices of the reshaped vector, selected only along dimension one."
    "eachrow docstring; base/slicearray.jl:136-172"
    ``EachrowVectorUsesRows,
  todoEntry "multidimcov-slicearray-faithful-209" ["eachcol(matrix)"]
    "Matrix columns have the input parent, one outer index per column, and only the second parent dimension selected."
    "eachcol docstring; base/slicearray.jl:174-209"
    ``EachcolMatrixUsesColumns,
  todoEntry "multidimcov-slicearray-faithful-210" ["eachcol(vector)"]
    "A vector's column slices select only dimension two of its two-dimensional reshape."
    "eachcol docstring; base/slicearray.jl:174-210"
    ``EachcolVectorUsesSingleColumn,
  todoEntry "multidimcov-slicearray-faithful-236" ["_slice_index"]
    "Successful indexing maps selected coordinates to fixed parent positions, preserves colon dimensions, and rejects missing outer indices."
    "Slices indexing behavior; base/slicearray.jl:236-238"
    ``SliceIndexBehavior,
  todoEntry "multidimcov-slicearray-faithful-240" ["getindex"]
    "For every valid outer index and inner view index, the read matches the parent at coordinates obtained by filling colons from the inner index."
    "eachslice, eachrow, and eachcol docstrings; base/slicearray.jl:119-123,165-168,203-206,240-243"
    ``SlicesElementsAreParentViews,
  todoEntry "multidimcov-slicearray-faithful-244" ["setindex!"]
    "A successful assignment changes the mapped parent positions to the corresponding value elements and leaves all other positions unchanged."
    "AbstractArray indexing invariant; base/slicearray.jl:244-247"
    ``SlicesAssignmentTargetsMappedParent,
  todoEntry "multidimcov-slicearray-faithful-249" ["parent"]
    "eachslice, eachrow, and eachcol results retain their array or reshape parent and preserve the documented selected axes."
    "AbstractSlices and Slices docstrings; base/slicearray.jl:1-20,249"
    ``SlicesParentIdentity
]

end JuliaLean.Proofs.base.slicearray

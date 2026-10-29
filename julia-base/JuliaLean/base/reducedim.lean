import JuliaLean.Core
import JuliaLean.base.abstractarray
import JuliaLean.base.array
import JuliaLean.base.reduce
import JuliaLean.base.indices
import JuliaLean.base.range

set_option linter.unusedVariables false

/-!
# Typed model of `base/reducedim.jl`

The array, mutation, range, integer, and scalar-reduction interfaces are typed
operations. Dimension normalization and all reduction methods in this file
call the local source mirrors directly.
-/

namespace JuliaLean.base.reducedim

open JuliaLean

abbrev Result := JuliaLean.base.abstractarray.Result
abbrev I64 := JInt .i64

def int (n : Int) : I64 := JInt.lit .i64 n

def iadd (a b : I64) : I64 := JInt.wrap .i64 (a.val + b.val)
def imul (a b : I64) : I64 := JInt.wrap .i64 (a.val * b.val)

inductive AxisKind where
  | oneTo
  | wrapped
  | unitRange
  deriving Repr, DecidableEq
inductive TypeTag where
  | any
  | abstractComplex
  | complex (realPart : TypeTag)
  | union (left right : TypeTag)
  | named (name : String)
  deriving Repr, DecidableEq

structure ShapeIndexer (Index : Type) where
  keep : List Nat
  default : List Index

inductive InitArg (α : Type) where
  | implicit
  | explicit (value : α)
  deriving Repr

inductive ReducedResult (Array : Type → Type) (α : Type) where
  | scalar (value : α)
  | array (value : Array α)

structure FindResult (Array : Type → Type) (Index Value : Type) where
  values : Array Value
  indices : Array Index

structure Operations where
  Input : Type → Type
  Array : Type → Type
  Reshaped : Type → Type
  Axis : Type
  Dimension : Type
  Region : Type
  Index : Type
  State : Type
  Function : Type
  Operator : Type
  typeName : Axis → String
  axisKind : Axis → AxisKind
  oneForAxis : Axis → Result Index
  makeOneTo : Index → Result Axis
  firstIndex : Axis → Result Index
  unitRange : Index → Index → Result Axis
  ofType : Axis → Axis → Result Axis
  isSlice : Axis → Bool
  firstSliceOneTo : Axis → Result Axis
  sliceIndices : Axis → Axis
  wrapSlice : Axis → Result Axis
  axisGetRange : Axis → Axis → Result Axis
  axesEqual : List Axis → List Axis → Bool
  renderAxes : List Axis → String
  axisEqual : Axis → Axis → Bool
  indexEqual : Index → Index → Bool
  axisLength : Axis → I64
  axisEmpty : Axis → Bool
  axisAt : List Axis → I64 → Result Axis
  axisInputAt : {α : Type} → Input α → I64 → Result Axis
  axisArrayAt : {α : Type} → Array α → I64 → Result Axis
  axesInput : {α : Type} → Input α → Result (List Axis)
  axesArray : {α : Type} → Array α → Result (List Axis)
  ndimsInput : {α : Type} → Input α → I64
  ndimsArray : {α : Type} → Array α → I64
  regionItems : Region → List Dimension
  isInteger : Dimension → Bool
  toInt : Dimension → Result I64
  showDimension : Dimension → String
  inRegion : Region → I64 → Result Bool
  isColon : Region → Bool
  colonRegion : Region
  similar : {α β : Type} → Input α → TypeTag → List Axis → Result (Array β)
  fill : {α : Type} → Array α → α → Result (Array α)
  view : {α : Type} → Input α → List Axis → Result (Input α)
  mapArray : {F α β : Type} → F → Input α → Result (Array β)
  mapInto : {F α β : Type} → F → Array β → Input α → Result (Array β)
  isEmptyInput : {α : Type} → Input α → Result Bool
  isEmptyArray : {α : Type} → Array α → Result Bool
  getInput : {α : Type} → Input α → List Index → Result α
  getInputLinear : {α : Type} → Input α → Index → Result α
  getArray : {α : Type} → Array α → List Index → Result α
  eachIndexInput : {α : Type} → Input α → Result (List Index)
  setArray : {α : Type} → Array α → α → List Index → Result (Array α)
  getArrayLinear : {α : Type} → Array α → Index → Result α
  setArrayLinear : {α : Type} → Array α → α → Index → Result (Array α)
  axisIndices : Axis → Result (List Index)
  cartesianIndices : List Axis → Result (List (List Index))
  safeTail : List Axis → List Axis
  shapeIndexer : List Axis → Result (ShapeIndexer Index)
  newIndex : List Index → ShapeIndexer Index → List Index → Result (List Index)
  firstAxis : Axis → Result Index
  axes1 : {α : Type} → Array α → Result Axis
  eachIndexArray : {α : Type} → Array α → Result (List Index)
  firstLinearIndex : {α : Type} → Input α → Result Index
  indexZero : {α : Type} → Input α → Result Index
  indexOne : Index
  indexAdd : Index → Index → Result Index
  indexSub : Index → Index → Result Index
  indexAddLength : Index → I64 → Result Index
  hasFastLinearIndex : {α : Type} → Input α → Bool
  mapreduceImpl : {F O α β γ : Type} → F → O → Input α → Index → Index → Result γ
  iterate : {α : Type} → Input α → Result (Option (α × State))
  rest : {α : Type} → Input α → State → Result (List α)
  mapreduceNoInit : {F O α β γ : Type} → F → O → Input α → Result γ
  mapMany : {F α β : Type} → F → Input α → List (Input α) → Result (Input β)
  parent : {α : Type} → Reshaped α → Input α
  applyFunction : {F α β : Type} → F → α → Result β
  applyOperator : {O A B : Type} → O → A → B → Result A
  applyPredicate : {O A B : Type} → O → A → B → Result Bool
  identity : Function
  addSum : Operator
  mulProd : Operator
  maximum : Operator
  minimum : Operator
  extremaRF : Operator
  andAll : Operator
  orAny : Operator
  bitAnd : Operator
  bitOr : Operator
  sum : {α β : Type} → Function → Input α → Result β
  makeExtremaMap : Function → Function
  less : Operator
  greater : Operator
  prod : {α β : Type} → Function → Input α → Result β
  functionKind : Function → JuliaLean.base.reduce.MappingIdentity
  operatorKind : {O : Type} → O → String
  operatorResultType : Operator → TypeTag
  convertValue : {α β : Type} → α → Result β
  convertArray : {α β : Type} → Array α → TypeTag → Result (Array β)
  elementType : {α : Type} → Input α → TypeTag
  valueType : {α : Type} → α → TypeTag
  promoteType : TypeTag → TypeTag → Result TypeTag
  abstractComplex : TypeTag → Bool
  complexParameter : TypeTag → Option TypeTag
  realType : TypeTag
  applicableZero : TypeTag → Bool
  isAnyType : TypeTag → Bool
  zeroType : {α : Type} → TypeTag → Result α
  oneType : {α : Type} → TypeTag → Result α
  zeroValue : {α : Type} → α → Result α
  oneValue : {α : Type} → α → Result α
  valueTypeOf : {α : Type} → α → TypeTag
  isInstance : {α : Type} → α → TypeTag → Bool
  isNumber : {α : Type} → α → Bool
  isNaN : {α : Type} → α → Bool
  isUnordered : {α : Type} → α → Bool
  infinity : {α : Type} → α → Bool → Result α
  nonmissingType : TypeTag → TypeTag
  machineNumericType : TypeTag → Bool
  typeExtreme : {α : Type} → TypeTag → Bool → Result α
  allUnordered : {α : Type} → Input α → Result Bool
  filterOrdered : {α : Type} → Input α → Result (Input α)
  emptyReduce : {α : Type} → Result α
  simpleCount : {α β : Type} → Function → Input α → β → Result β
  boolFunction : Function → Function
  iteratorError : {α : Type} → Result α
  containsMissing : TypeTag → Bool
  missingType : TypeTag
  toBool : {α : Type} → α → Result Bool
  zeroArray : {α : Type} → Array α → Result α
  oneArray : {α : Type} → Array α → Result α
  trueArrayValue : Bool
  falseArrayValue : Bool
  promoteOp : {F : Type} → F → TypeTag → TypeTag
  keysElementType : {α : Type} → Input α → TypeTag
  zeroIndexOfType : TypeTag → Result Index
  firstInput : {α : Type} → Input α → Result α
  findInitialType : {F α : Type} → F → Input α → TypeTag
  isVector : {α : Type} → Input α → Bool
  indexStyle : {α : Type} → Input α → JuliaLean.base.indices.IndexStyle

/-!
The source uses Julia dispatch on range types. `axisKind` records the already
selected range method; it does not replace the method bodies below.
-/

def reducedIndexOneTo (ops : Operations) (i : ops.Axis) : Result ops.Axis := do
  ops.makeOneTo (← ops.oneForAxis i)

def reducedIndexWrapped (ops : Operations) (i : ops.Axis) : Result ops.Axis := do
  let first ← ops.firstIndex i
  let singleton ← ops.unitRange first first
  ops.ofType i singleton

def reducedIndexUnitRange (ops : Operations) (i : ops.Axis) : Result ops.Axis :=
  .error (.julia (.argumentError ("\nNo method is implemented for reducing index range of type " ++
    ops.typeName i ++ ". Please implement\nreduced_index for this index type or report this as an issue.\n")))

def reducedIndex (ops : Operations) (i : ops.Axis) : Result ops.Axis :=
  match ops.axisKind i with
  | .oneTo => reducedIndexOneTo ops i
  | .wrapped => reducedIndexWrapped ops i
  | .unitRange => reducedIndexUnitRange ops i

/-!
Julia source: base/reducedim.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduced_index(i::OneTo{T}) where {T} = OneTo(one(T))
```
-/
def reduced_index_oneTo (ops : Operations) (i : ops.Axis) : Result ops.Axis :=
  reducedIndexOneTo ops i

/-!
Julia source: base/reducedim.jl:7-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduced_index(i::Union{Slice, IdentityUnitRange}) = oftype(i, first(i):first(i))
```
-/
def reduced_index_wrapped (ops : Operations) (i : ops.Axis) : Result ops.Axis :=
  reducedIndexWrapped ops i

/-!
Julia source: base/reducedim.jl:8-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduced_index(i::AbstractUnitRange) =
    throw(ArgumentError(
"""
No method is implemented for reducing index range of type $(typeof(i)). Please implement
reduced_index for this index type or report this as an issue.
"""
    ))
```
-/
def reduced_index_unitRange (ops : Operations) (i : ops.Axis) : Result ops.Axis :=
  reducedIndexUnitRange ops i

def checkValidRegionLoop (ops : Operations) : List ops.Dimension → Result Unit
  | [] => pure ()
  | d :: ds => do
      if !ops.isInteger d then
        throw (.julia (.argumentError "reduced dimension(s) must be integers"))
      let dInt ← ops.toInt d
      if dInt.val < 1 then
        throw (.julia (.argumentError ("region dimension(s) must be ≥ 1, got " ++ ops.showDimension d)))
      checkValidRegionLoop ops ds

/-!
Julia source: base/reducedim.jl:30-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _check_valid_region(region)
    for d in region
        isa(d, Integer) || throw(ArgumentError("reduced dimension(s) must be integers"))
        Int(d) < 1 && throw(ArgumentError("region dimension(s) must be ≥ 1, got $d"))
    end
end
```
-/
def check_valid_region (ops : Operations) (region : ops.Region) : Result Unit :=
  checkValidRegionLoop ops (ops.regionItems region)

def reducedIndicesLoop (ops : Operations) (region : ops.Region) (dim : Nat) :
    List ops.Axis → Result (List ops.Axis)
  | [] => pure []
  | axis :: rest => do
      let position := int (Int.ofNat (dim + 1))
      let selected ← ops.inRegion region position
      let outAxis ← if selected then reducedIndex ops axis else pure axis
      let outRest ← reducedIndicesLoop ops region (dim + 1) rest
      pure (outAxis :: outRest)

def reducedIndicesLoop0 (ops : Operations) (region : ops.Region) (dim : Nat) :
    List ops.Axis → Result (List ops.Axis)
  | [] => pure []
  | axis :: rest => do
      let position := int (Int.ofNat (dim + 1))
      let selected ← ops.inRegion region position
      let outAxis ← if selected && !ops.axisEmpty axis then reducedIndex ops axis else pure axis
      let outRest ← reducedIndicesLoop0 ops region (dim + 1) rest
      pure (outAxis :: outRest)

/-!
Julia source: base/reducedim.jl:20-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reduced_indices(axs::Indices{N}, region) where N
    _check_valid_region(region)
    ntuple(d -> d in region ? reduced_index(axs[d]) : axs[d], Val(N))
end
```
-/
def reduced_indices_axes (ops : Operations) (axes : List ops.Axis) (region : ops.Region) :
    Result (List ops.Axis) := do
  check_valid_region ops region
  reducedIndicesLoop ops region 0 axes

/-!
Julia source: base/reducedim.jl:25-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reduced_indices0(axs::Indices{N}, region) where N
    _check_valid_region(region)
    ntuple(d -> d in region && !isempty(axs[d]) ? reduced_index(axs[d]) : axs[d], Val(N))
end
```
-/
def reduced_indices0_axes (ops : Operations) (axes : List ops.Axis) (region : ops.Region) :
    Result (List ops.Axis) := do
  check_valid_region ops region
  reducedIndicesLoop0 ops region 0 axes

/-!
Julia source: base/reducedim.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduced_indices(a::AbstractArrayOrBroadcasted, region) = reduced_indices(axes(a), region)
```
-/
def reduced_indices_input {α : Type} (ops : Operations) (a : ops.Input α) (region : ops.Region) :
    Result (List ops.Axis) := do
  reduced_indices_axes ops (← ops.axesInput a) region

/-!
Julia source: base/reducedim.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduced_indices0(a::AbstractArray, region) = reduced_indices0(axes(a), region)
```
-/
def reduced_indices0_input {α : Type} (ops : Operations) (a : ops.Input α) (region : ops.Region) :
    Result (List ops.Axis) := do
  reduced_indices0_axes ops (← ops.axesInput a) region

def checkReducedimsLoop (ops : Operations) {α β : Type}
    (R : ops.Array β) (A : ops.Input α) (rank : Nat) (dim : Nat)
    (lsiz : I64) (hadNonreduc : Bool) : Result I64 := do
  if dim > rank then
    return lsiz
  let d := int (Int.ofNat dim)
  let Ri ← ops.axisArrayAt R d
  let Ai ← ops.axisInputAt A d
  let sRi := ops.axisLength Ri
  let sAi := ops.axisLength Ai
  if sRi.val == 1 then
    if sAi.val > 1 then
      if hadNonreduc then
        checkReducedimsLoop ops R A rank (dim + 1) (int 0) hadNonreduc
      else
        checkReducedimsLoop ops R A rank (dim + 1) (imul lsiz sAi) hadNonreduc
    else
      checkReducedimsLoop ops R A rank (dim + 1) lsiz hadNonreduc
  else if ops.axisEqual Ri Ai then
    checkReducedimsLoop ops R A rank (dim + 1) lsiz true
  else
    throw (.dimensionMismatch
      ("reduction on array with indices " ++ ops.renderAxes (← ops.axesInput A) ++
        " with output with indices " ++ ops.renderAxes (← ops.axesArray R)))
termination_by rank + 1 - dim
decreasing_by all_goals omega

/-!
Julia source: base/reducedim.jl:205-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_reducedims(R, A)
    # Check whether R has compatible dimensions w.r.t. A for reduction
    #
    # It returns an integer value (useful for choosing implementation)
    # - If it reduces only along leading dimensions, e.g. sum(A, dims=1) or sum(A, dims=(1,2)),
    #   it returns the length of the leading slice. For the two examples above,
    #   it will be size(A, 1) or size(A, 1) * size(A, 2).
    # - Otherwise, e.g. sum(A, dims=2) or sum(A, dims=(1,3)), it returns 0.
    #
    ndims(R) <= ndims(A) || throw(DimensionMismatch("cannot reduce $(ndims(A))-dimensional array to $(ndims(R)) dimensions"))
    lsiz = 1
    had_nonreduc = false
    for i = 1:ndims(A)
        Ri, Ai = axes(R, i), axes(A, i)
        sRi, sAi = length(Ri), length(Ai)
        if sRi == 1
            if sAi > 1
                if had_nonreduc
                    lsiz = 0  # to reduce along i, but some previous dimensions were non-reducing
                else
                    lsiz *= sAi  # if lsiz was set to zero, it will stay to be zero
                end
            end
        else
            Ri == Ai || throw(DimensionMismatch("reduction on array with indices $(axes(A)) with output with indices $(axes(R))"))
            had_nonreduc = true
        end
    end
    return lsiz
end
```
-/
def check_reducedims {α β : Type} (ops : Operations) (R : ops.Array β)
    (A : ops.Input α) : Result I64 := do
  let ndR := ops.ndimsArray R
  let ndA := ops.ndimsInput A
  if ndR.val > ndA.val then
    throw (.dimensionMismatch
      ("cannot reduce " ++ toString ndA.val ++ "-dimensional array to " ++
        toString ndR.val ++ " dimensions"))
  checkReducedimsLoop ops R A ndA.val.toNat 1 (int 1) false

/-!
Julia source: base/reducedim.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_firstreducedslice(::Tuple{}, a::Tuple{}) = ()
```
-/
def firstReducedSliceEmpty : List Axis → Result (List Axis)
  | [] => pure []
  | _ :: _ => pure []

/-!
Julia source: base/reducedim.jl:249-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_firstreducedslice(::Tuple, ::Tuple{}) = ()
```
-/
def firstReducedSliceNoInput : List Axis → Result (List Axis)
  | _ => pure []

def firstSliceGeneric (ops : Operations) (i : ops.Axis) : Result ops.Axis := do
  let first ← ops.firstIndex i
  let last ← ops.firstIndex i
  let singleton ← ops.unitRange first last
  ops.axisGetRange i singleton

/-!
Julia source: base/reducedim.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_firstslice(i::OneTo) = OneTo(1)
```
-/
def firstSliceOneTo (ops : Operations) (i : ops.Axis) : Result ops.Axis :=
  ops.firstSliceOneTo i

/-!
Julia source: base/reducedim.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_firstslice(i::Slice) = Slice(_firstslice(i.indices))
```
-/
def firstSliceSlice (ops : Operations) (i : ops.Axis) : Result ops.Axis := do
  let indices := ops.sliceIndices i
  let first ← firstSliceGeneric ops indices
  ops.wrapSlice first

/-!
Julia source: base/reducedim.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_firstslice(i) = i[firstindex(i):firstindex(i)]
```
-/
def firstSliceOther (ops : Operations) (i : ops.Axis) : Result ops.Axis :=
  firstSliceGeneric ops i
def firstSlice (ops : Operations) (i : ops.Axis) : Result ops.Axis := do
  match ops.axisKind i with
  | .oneTo => firstSliceOneTo ops i
  | .wrapped => if ops.isSlice i then firstSliceSlice ops i else firstSliceOther ops i
  | .unitRange => firstSliceOther ops i


/-!
Julia source: base/reducedim.jl:250-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _firstreducedslice(::Tuple{}, a::Tuple) = (_firstslice(a[1]), _firstreducedslice((), tail(a))...)
```
-/
def firstReducedSliceNoOutput (ops : Operations) : List ops.Axis → Result (List ops.Axis)
  | [] => pure []
  | a :: as => do
      let first ← firstSlice ops a
      pure (first :: (← firstReducedSliceNoOutput ops as))

/-!
Julia source: base/reducedim.jl:251-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _firstreducedslice(r::Tuple, a::Tuple) = (length(r[1])==1 ? _firstslice(a[1]) : r[1], _firstreducedslice(tail(r), tail(a))...)
```
-/
def firstReducedSlice (ops : Operations) : List ops.Axis → List ops.Axis → Result (List ops.Axis)
  | [], [] => pure []
  | _ :: _, [] => pure []
  | [], a :: as => do
      let first ← firstSlice ops a
      pure (first :: (← firstReducedSliceNoOutput ops as))
  | r :: rs, a :: as => do
      let first ← if (ops.axisLength r).val == 1 then firstSlice ops a else pure r
      pure (first :: (← firstReducedSlice ops rs as))

/-!
Julia source: base/reducedim.jl:241-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mapfirst!(f::F, R::AbstractArray, A::AbstractArray{<:Any,N}) where {N, F}
    check_reducedims(R, A)
    t = _firstreducedslice(axes(R), axes(A))
    map!(f, R, view(A, t...))
end
```
-/
def mapfirst! {α β : Type} (ops : Operations) (f : ops.Function) (R : ops.Array β)
    (A : ops.Input α) : Result (ops.Array β) := do
  let _ ← check_reducedims ops R A
  let firstSlice ← firstReducedSlice ops (← ops.axesArray R) (← ops.axesInput A)
  ops.mapInto f R (← ops.view A firstSlice)

/-!
Julia source: base/reducedim.jl:239-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyfirst!(R::AbstractArray, A::AbstractArray) = mapfirst!(identity, R, A)
```
-/
def copyfirst! {α β : Type} (ops : Operations) (R : ops.Array β) (A : ops.Input α) :
    Result (ops.Array β) :=
  mapfirst! ops ops.identity R A

/-!
Julia source: base/reducedim.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_fast_linear_indexing(a::AbstractArrayOrBroadcasted) = IndexStyle(a) === IndexLinear()
```
-/
def has_fast_linear_indexing_generic {α : Type} (ops : Operations) (a : ops.Input α) : Bool :=
  ops.indexStyle a == .linear

/-!
Julia source: base/reducedim.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_fast_linear_indexing(a::AbstractVector) = true
```
-/
def has_fast_linear_indexing_vector {α : Type} (ops : Operations) (_a : ops.Input α) : Bool :=
  true

def hasFastLinearIndexing {α : Type} (ops : Operations) (a : ops.Input α) : Bool :=
  if ops.isVector a then has_fast_linear_indexing_vector ops a
  else has_fast_linear_indexing_generic ops a
/-!
Julia source: base/reducedim.jl:1238-1238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reducedim1(R) = length(axes1(R)) == 1
```
-/
def reducedim1 {α : Type} (ops : Operations) (R : ops.Array α) : Result Bool := do
  return (ops.axisLength (← ops.axes1 R)).val == 1

/-!
Julia source: base/reducedim.jl:256-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mapreducedim!(f, op, R::AbstractArray, A::AbstractArrayOrBroadcasted)
    lsiz = check_reducedims(R,A)
    isempty(A) && return R

    if has_fast_linear_indexing(A) && lsiz > 16
        # use mapreduce_impl, which is probably better tuned to achieve higher performance
        ibase = first(LinearIndices(A))-1
        for i in eachindex(R)
            r = op(@inbounds(R[i]), mapreduce_impl(f, op, A, ibase+1, ibase+lsiz))
            @inbounds R[i] = r
            ibase += lsiz
        end
        return R
    end
    indsAt, indsRt = safe_tail(axes(A)), safe_tail(axes(R)) # handle d=1 manually
    keep, Idefault = Broadcast.shapeindexer(indsRt)
    if reducedim1(R)
        # keep the accumulator as a local variable when reducing along the first dimension
        i1 = first(axes1(R))
        for IA in CartesianIndices(indsAt)
            IR = Broadcast.newindex(IA, keep, Idefault)
            @inbounds r = R[i1,IR]
            @simd for i in axes(A, 1)
                r = op(r, f(@inbounds(A[i, IA])))
            end
            @inbounds R[i1,IR] = r
        end
    else
        for IA in CartesianIndices(indsAt)
            IR = Broadcast.newindex(IA, keep, Idefault)
            @simd for i in axes(A, 1)
                v = op(@inbounds(R[i,IR]), f(@inbounds(A[i,IA])))
                @inbounds R[i,IR] = v
            end
        end
    end
    return R
end
```
-/
def _mapreducedim! {α β γ : Type} (ops : Operations) (f : ops.Function) (op : ops.Operator)
    (R : ops.Array β) (A : ops.Input α) : Result (ops.Array β) := do
  let lsiz ← check_reducedims ops R A
  if ← ops.isEmptyInput A then return R
  if hasFastLinearIndexing ops A && lsiz.val > 16 then
    let ibase ← ops.indexSub (← ops.firstLinearIndex A) ops.indexOne
    let indices ← ops.eachIndexArray R
    let (R, _) ← indices.foldlM (fun (R, ibase) i => do
      let start ← ops.indexAdd ibase ops.indexOne
      let stop ← ops.indexAddLength ibase lsiz
      let current ← ops.getArrayLinear R i
      let reduced ← ops.mapreduceImpl (F := ops.Function) (O := ops.Operator)
        (α := α) (β := γ) (γ := β) f op A start stop
      let value ← ops.applyOperator (O := ops.Operator) (A := β) (B := β)
        op current reduced
      let R ← ops.setArrayLinear R value i
      let ibase ← ops.indexAddLength ibase lsiz
      pure (R, ibase)) (R, ibase)
    return R
  let indsAt := ops.safeTail (← ops.axesInput A)
  let indsRt := ops.safeTail (← ops.axesArray R)
  let shape ← ops.shapeIndexer indsRt
  let outer ← ops.cartesianIndices indsAt
  if ← reducedim1 ops R then
    let i1 ← ops.firstAxis (← ops.axes1 R)
    let axis ← ops.axisInputAt A (int 1)
    let indices ← ops.axisIndices axis
    outer.foldlM (fun R IA => do
      let IR ← ops.newIndex IA shape shape.default
      let initial ← ops.getArray R (i1 :: IR)
      let value ← indices.foldlM (fun value i => do
        let x ← ops.getInput A (i :: IA)
        let mapped ← ops.applyFunction (F := ops.Function) (α := α) (β := γ) f x
        ops.applyOperator (O := ops.Operator) (A := β) (B := γ) op value mapped) initial
      ops.setArray R value (i1 :: IR)) R
  else
    let axis ← ops.axisInputAt A (int 1)
    let indices ← ops.axisIndices axis
    outer.foldlM (fun R IA => do
      let IR ← ops.newIndex IA shape shape.default
      indices.foldlM (fun R i => do
        let current ← ops.getArray R (i :: IR)
        let x ← ops.getInput A (i :: IA)
        let mapped ← ops.applyFunction (F := ops.Function) (α := α) (β := γ) f x
        let value ← ops.applyOperator (O := ops.Operator) (A := β) (B := γ)
          op current mapped
        ops.setArray R value (i :: IR)) R) R

/-!
Julia source: base/reducedim.jl:295-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreducedim!(f, op, R::AbstractArray, A::AbstractArrayOrBroadcasted) =
    (_mapreducedim!(f, op, R, A); R)
```
-/
def mapreducedim! {α β γ : Type} (ops : Operations) (f : ops.Function) (op : ops.Operator)
    (R : ops.Array β) (A : ops.Input α) : Result (ops.Array β) := do
  let _ ← _mapreducedim! (γ := γ) ops f op R A
  pure R

/-!
Julia source: base/reducedim.jl:298-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reducedim!(op, R::AbstractArray{RT}, A::AbstractArrayOrBroadcasted) where {RT} =
    mapreducedim!(identity, op, R, A)
```
-/
def reducedim! {α β : Type} (ops : Operations) (op : ops.Operator)
    (R : ops.Array β) (A : ops.Input α) : Result (ops.Array β) :=
  mapreducedim! (γ := α) ops ops.identity op R A


def reducedim_initarray_type {α β : Type} (ops : Operations) (A : ops.Input α)
    (region : ops.Region) (init : β) (resultType : TypeTag) : Result (ops.Array β) := do
  let axes ← reduced_indices_input ops A region
  let result ← ops.similar A resultType axes
  ops.fill result init

/-!
Julia source: base/reducedim.jl:52-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reducedim_initarray(A::AbstractArrayOrBroadcasted, region, init, ::Type{R}) where {R} = fill!(similar(A,R,reduced_indices(A,region)), init)
```
-/
def reducedim_initarray_explicit {α β : Type} (ops : Operations) (A : ops.Input α)
    (region : ops.Region) (init : β) (resultType : TypeTag) : Result (ops.Array β) :=
  reducedim_initarray_type ops A region init resultType

/-!
Julia source: base/reducedim.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reducedim_initarray(A::AbstractArrayOrBroadcasted, region, init::T) where {T} = reducedim_initarray(A, region, init, T)
```
-/
def reducedim_initarray {α β : Type} (ops : Operations) (A : ops.Input α)
    (region : ops.Region) (init : β) : Result (ops.Array β) :=
  reducedim_initarray_explicit ops A region init (ops.valueTypeOf init)

/-!
Julia source: base/reducedim.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval initarray!(a::AbstractArray{T}, ::Any, ::$(Op), init::Bool, src::AbstractArray) where {T} = (init && fill!(a, $(initfun)(T)); a)
```
-/
def initarray_sum {α : Type} (ops : Operations) (a : ops.Array α) (init : Bool) :
    Result (ops.Array α) := do
  if init then
    ops.fill a (← ops.zeroArray a)
  else
    pure a

/-!
Julia source: base/reducedim.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval initarray!(a::AbstractArray{T}, ::Any, ::$(Op), init::Bool, src::AbstractArray) where {T} = (init && fill!(a, $(initfun)(T)); a)
```
-/
def initarray_prod {α : Type} (ops : Operations) (a : ops.Array α) (init : Bool) :
    Result (ops.Array α) := do
  if init then
    ops.fill a (← ops.oneArray a)
  else
    pure a

/-!
Julia source: base/reducedim.jl:45-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
initarray!(a::AbstractArray{T}, f, ::Union{typeof(min),typeof(max),typeof(_extrema_rf)},
    init::Bool, src::AbstractArray) where {T} = (init && mapfirst!(f, a, src); a)
```
-/
def initarray_minmax {F α β : Type} (ops : Operations) (a : ops.Array β) (f : ops.Function)
    (src : ops.Input α) (init : Bool) : Result (ops.Array β) := do
  if init then
    mapfirst! ops f a src
  else
    pure a

/-!
Julia source: base/reducedim.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval initarray!(a::AbstractArray, ::Any, ::$(Op), init::Bool, src::AbstractArray) = (init && fill!(a, $initval); a)
```
-/
def initarray_all {β : Type} (ops : Operations) (a : ops.Array β) (init : Bool) :
    Result (ops.Array β) := do
  if init then
    ops.fill a (← ops.convertValue (α := Bool) (β := β) true)
  else
    pure a

/-!
Julia source: base/reducedim.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval initarray!(a::AbstractArray, ::Any, ::$(Op), init::Bool, src::AbstractArray) = (init && fill!(a, $initval); a)
```
-/
def initarray_any {β : Type} (ops : Operations) (a : ops.Array β) (init : Bool) :
    Result (ops.Array β) := do
  if init then
    ops.fill a (← ops.convertValue (α := Bool) (β := β) false)
  else
    pure a

def promote_union (ops : Operations) : TypeTag → Result TypeTag
  | .union left right => do
      let left ← promote_union ops left
      let right ← promote_union ops right
      ops.promoteType left right
  | t => pure t

/-!
Julia source: base/reducedim.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_union(T::Union) = promote_type(promote_union(T.a), promote_union(T.b))
```
-/
def promote_union_union (ops : Operations) (left right : TypeTag) : Result TypeTag := do
  let left ← promote_union ops left
  let right ← promote_union ops right
  ops.promoteType left right

/-!
Julia source: base/reducedim.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_union(T) = T
```
-/
def promote_union_other (_ops : Operations) (t : TypeTag) : Result TypeTag :=
  pure t

/-!
Julia source: base/reducedim.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_realtype(::Type{<:Complex}) = Real
```
-/
def realtype_complex (ops : Operations) (_t : TypeTag) : TypeTag :=
  ops.realType

/-!
Julia source: base/reducedim.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_realtype(::Type{Complex{T}}) where T<:Real = T
```
-/
def realtype_complexValue (_ops : Operations) (realPart : TypeTag) : TypeTag :=
  realPart

/-!
Julia source: base/reducedim.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_realtype(T::Type) = T
```
-/
def realtype_type (_ops : Operations) (t : TypeTag) : TypeTag :=
  t

def realtype_dispatch (ops : Operations) (f : ops.Function) (t : TypeTag) : TypeTag :=
  match ops.functionKind f with
  | .abs | .abs2 =>
      match t with
      | .abstractComplex => realtype_complex ops t
      | .complex realPart => realtype_complexValue ops realPart
      | _ => realtype_type ops t
  | _ => t

/-!
Julia source: base/reducedim.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_realtype(::Union{typeof(abs),typeof(abs2)}, T) = _realtype(T)
```
-/
def realtype_abs (ops : Operations) (f : ops.Function) (t : TypeTag) : TypeTag :=
  realtype_dispatch ops f t

/-!
Julia source: base/reducedim.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_realtype(::Any, T) = T
```
-/
def realtype_other (ops : Operations) (_f : ops.Function) (t : TypeTag) : TypeTag :=
  t

def realtype (ops : Operations) (f : ops.Function) (t : TypeTag) : TypeTag :=
  match ops.functionKind f with
  | .abs | .abs2 => realtype_abs ops f t
  | _ => realtype_other ops f t

/-!
Julia source: base/reducedim.jl:74-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reducedim_init(f, op, fv, fop, A, region)
    T = _realtype(f, promote_union(eltype(A)))
    if T !== Any && applicable(zero, T)
        x = f(zero(T))
        z = op(fv(x), fv(x))
        Tr = z isa T ? T : typeof(z)
    else
        z = fv(fop(f, A))
        Tr = typeof(z)
    end
    return reducedim_initarray(A, region, z, Tr)
end
```
-/
def _reducedim_init {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (zeroType : TypeTag → Result α) (fv : β → Result β)
    (fop : ops.Function → ops.Input α → Result β) (A : ops.Input α)
    (region : ops.Region) : Result (ops.Array β) := do
  let T := realtype ops f (← promote_union ops (ops.elementType A))
  let z ← if !ops.isAnyType T && ops.applicableZero T then do
    let x ← ops.applyFunction f (← zeroType T)
    let left ← fv x
    let right ← fv x
    let z ← ops.applyOperator (O := ops.Operator) (A := β) (B := β) op left right
    pure z
  else do
    fv (← fop f A)
  let resultType := if ops.isInstance z T then T else ops.valueTypeOf z
  reducedim_initarray_type ops A region z resultType

/-!
Julia source: base/reducedim.jl:68-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reducedim_init(f, op::Union{typeof(+),typeof(add_sum)}, A::AbstractArray, region)
    _reducedim_init(f, op, zero, sum, A, region)
end
```
-/
def reducedim_init_add {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (A : ops.Input α) (region : ops.Region) : Result (ops.Array β) :=
  _reducedim_init ops f op ops.zeroType ops.zeroValue ops.sum A region

/-!
Julia source: base/reducedim.jl:71-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reducedim_init(f, op::Union{typeof(*),typeof(mul_prod)}, A::AbstractArray, region)
    _reducedim_init(f, op, one, prod, A, region)
end
```
-/
def reducedim_init_prod {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (A : ops.Input α) (region : ops.Region) : Result (ops.Array β) :=
  _reducedim_init ops f op ops.oneType ops.oneValue ops.prod A region

def hasEmptyRegionAxis {α : Type} (ops : Operations) (A : ops.Input α) :
    List ops.Dimension → Result Bool
  | [] => pure false
  | d :: ds => do
      let dimension ← ops.toInt d
      let axis ← ops.axisInputAt A dimension
      if ops.axisEmpty axis then pure true else hasEmptyRegionAxis ops A ds

def mapreduceNoInit {F O α β : Type} (ops : Operations) (f : F) (op : O)
    (A : ops.Input α) : Result β :=
  ops.mapreduceNoInit (F := F) (O := O) (α := α) (β := β) (γ := β) f op A

def reducedimInitMinMax {α β : Type} (ops : Operations) (isMax : Bool)
    (f : ops.Function) (A : ops.Input α) (region : ops.Region) :
    Result (ops.Array β) := do
  let reducedAxes ← reduced_indices_input ops A region
  if ← hasEmptyRegionAxis ops A (ops.regionItems region) then
    ops.emptyReduce
  let A1 ← ops.view A reducedAxes
  if ← ops.isEmptyInput A1 then
    ops.mapArray f A1
  else
    let opposite := if isMax then ops.minimum else ops.maximum
    let v0 ← mapreduceNoInit ops f opposite A1
    let T := realtype ops f (← promote_union ops (ops.elementType A))
    let initialType := if ops.isInstance v0 T then T else ops.valueTypeOf v0
    let v1 ← if ops.isNumber v0 && ops.isNaN v0 then
        ops.infinity v0 (!isMax)
      else if ops.isUnordered v0 then
        let orderedType := ops.nonmissingType initialType
        if ops.machineNumericType orderedType then
          ops.typeExtreme orderedType (!isMax)
        else if ← ops.allUnordered A1 then
          pure v0
        else do
          mapreduceNoInit ops f opposite (← ops.filterOrdered A1)
      else
        pure v0
    let resultType := if ops.isInstance v1 T then T else ops.valueTypeOf v1
    reducedim_initarray_type ops A region v1 resultType

/-!
Julia source: base/reducedim.jl:89-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function reducedim_init(f, op::typeof($f1), A::AbstractArray, region)
        # First compute the reduce indices. This will throw an ArgumentError
        # if any region is invalid
        ri = reduced_indices(A, region)

        # Next, throw if reduction is over a region with length zero
        any(i -> isempty(axes(A, i)), region) && _empty_reduce_error()

        # Make a view of the first slice of the region
        A1 = view(A, ri...)

        if isempty(A1)
            # If the slice is empty just return non-view version as the initial array
            return map(f, A1)
        else
            # otherwise use the min/max of the first slice as initial value
            v0 = mapreduce(f, $f2, A1)

            T = _realtype(f, promote_union(eltype(A)))
            Tr = v0 isa T ? T : typeof(v0)

            # but NaNs, missing and unordered values need to be avoided as initial values
            if v0 isa Number && isnan(v0)
                # v0 is NaN
                v0 = oftype(v0, $initval)
            elseif isunordered(v0)
                # v0 is missing or a third-party unordered value
                Tnm = nonmissingtype(Tr)
                if Tnm <: Union{BitInteger, IEEEFloat, BigFloat}
                    v0 = $typeextreme(Tnm)
                elseif !all(isunordered, A1)
                    v0 = mapreduce(f, $f2, Iterators.filter(!isunordered, A1))
                end
            end
            # v0 may have changed type.
            Tr = v0 isa T ? T : typeof(v0)

            return reducedim_initarray(A, region, v0, Tr)
        end
    end
```
-/
def reducedim_init_min {α β : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (region : ops.Region) : Result (ops.Array β) :=
  reducedimInitMinMax ops false f A region

/-!
Julia source: base/reducedim.jl:89-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function reducedim_init(f, op::typeof($f1), A::AbstractArray, region)
        # First compute the reduce indices. This will throw an ArgumentError
        # if any region is invalid
        ri = reduced_indices(A, region)

        # Next, throw if reduction is over a region with length zero
        any(i -> isempty(axes(A, i)), region) && _empty_reduce_error()

        # Make a view of the first slice of the region
        A1 = view(A, ri...)

        if isempty(A1)
            # If the slice is empty just return non-view version as the initial array
            return map(f, A1)
        else
            # otherwise use the min/max of the first slice as initial value
            v0 = mapreduce(f, $f2, A1)

            T = _realtype(f, promote_union(eltype(A)))
            Tr = v0 isa T ? T : typeof(v0)

            # but NaNs, missing and unordered values need to be avoided as initial values
            if v0 isa Number && isnan(v0)
                # v0 is NaN
                v0 = oftype(v0, $initval)
            elseif isunordered(v0)
                # v0 is missing or a third-party unordered value
                Tnm = nonmissingtype(Tr)
                if Tnm <: Union{BitInteger, IEEEFloat, BigFloat}
                    v0 = $typeextreme(Tnm)
                elseif !all(isunordered, A1)
                    v0 = mapreduce(f, $f2, Iterators.filter(!isunordered, A1))
                end
            end
            # v0 may have changed type.
            Tr = v0 isa T ? T : typeof(v0)

            return reducedim_initarray(A, region, v0, Tr)
        end
    end
```
-/
def reducedim_init_max {α β : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (region : ops.Region) : Result (ops.Array β) :=
  reducedimInitMinMax ops true f A region

/-!
Julia source: base/reducedim.jl:131-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reducedim_init(f::ExtremaMap, op::typeof(_extrema_rf), A::AbstractArray, region)
    # First compute the reduce indices. This will throw an ArgumentError
    # if any region is invalid
    ri = reduced_indices(A, region)

    # Next, throw if reduction is over a region with length zero
    any(i -> isempty(axes(A, i)), region) && _empty_reduce_error()

    # Make a view of the first slice of the region
    A1 = view(A, ri...)

    isempty(A1) && return map(f, A1)
    # use the max/min of the first slice as initial value for non-empty cases
    v0 = reverse(mapreduce(f, op, A1)) # turn minmax to maxmin

    T = _realtype(f.f, promote_union(eltype(A)))
    Tmin = v0[1] isa T ? T : typeof(v0[1])
    Tmax = v0[2] isa T ? T : typeof(v0[2])

    # but NaNs and missing need to be avoided as initial values
    if v0[1] isa Number && isnan(v0[1])
        # v0 is NaN
        v0 = oftype(v0[1], Inf), oftype(v0[2], -Inf)
    elseif isunordered(v0[1])
        # v0 is missing or a third-party unordered value
        Tminnm = nonmissingtype(Tmin)
        Tmaxnm = nonmissingtype(Tmax)
        if Tminnm <: Union{BitInteger, IEEEFloat, BigFloat} &&
            Tmaxnm <: Union{BitInteger, IEEEFloat, BigFloat}
            v0 = (typemax(Tminnm), typemin(Tmaxnm))
        elseif !all(isunordered, A1)
            v0 = reverse(mapreduce(f, op, Iterators.filter(!isunordered, A1)))
        end
    end
    # v0 may have changed type.
    Tmin = v0[1] isa T ? T : typeof(v0[1])
    Tmax = v0[2] isa T ? T : typeof(v0[2])

    return reducedim_initarray(A, region, v0, Tuple{Tmin,Tmax})
end
```
-/
def reducedim_init_extrema {α β : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (region : ops.Region) : Result (ops.Array (β × β)) := do
  let reducedAxes ← reduced_indices_input ops A region
  if ← hasEmptyRegionAxis ops A (ops.regionItems region) then
    ops.emptyReduce
  let A1 ← ops.view A reducedAxes
  let mappedF : JuliaLean.base.reduce.ExtremaMap ops.Function := ⟨f⟩
  if ← ops.isEmptyInput A1 then
    ops.mapArray mappedF A1
  else
    let reduced ← ops.mapreduceNoInit (F := JuliaLean.base.reduce.ExtremaMap ops.Function)
      (O := ops.Operator) (α := α) (β := β × β) (γ := β × β)
      mappedF ops.extremaRF A1
    let v0 := (reduced.2, reduced.1)
    let T := realtype ops f (← promote_union ops (ops.elementType A))
    let minType := if ops.isInstance v0.1 T then T else ops.valueTypeOf v0.1
    let maxType := if ops.isInstance v0.2 T then T else ops.valueTypeOf v0.2
    let v1 ← if ops.isNumber v0.1 && ops.isNaN v0.1 then do
        pure (← ops.infinity v0.1 true, ← ops.infinity v0.2 false)
      else if ops.isUnordered v0.1 then
        let minOrdered := ops.nonmissingType minType
        let maxOrdered := ops.nonmissingType maxType
        if ops.machineNumericType minOrdered && ops.machineNumericType maxOrdered then
          pure (← ops.typeExtreme minOrdered true, ← ops.typeExtreme maxOrdered false)
        else if ← ops.allUnordered A1 then
          pure v0
        else
          let filtered ← ops.filterOrdered A1
          let result ← ops.mapreduceNoInit (F := JuliaLean.base.reduce.ExtremaMap ops.Function)
            (O := ops.Operator) (α := α) (β := β × β) (γ := β × β)
            mappedF ops.extremaRF filtered
          pure (result.2, result.1)
      else
        pure v0
    reducedim_initarray ops A region v1

/-!
Julia source: base/reducedim.jl:172-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reducedim_init(f::Union{typeof(abs),typeof(abs2)}, op::typeof(max), A::AbstractArray{T}, region) where {T} =
    reducedim_initarray(A, region, zero(f(zero(T))), _realtype(f, T))
```
-/
def reducedim_init_absmax {α β : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (region : ops.Region) : Result (ops.Array β) := do
  let elementType := ops.elementType A
  let initial ← ops.zeroType (α := α) elementType
  let mapped ← ops.applyFunction (F := ops.Function) (α := α) (β := β) f initial
  let z ← ops.zeroValue (α := β) mapped
  reducedim_initarray_type ops A region z (realtype ops f elementType)

/-!
Julia source: base/reducedim.jl:175-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reducedim_init(f, op::typeof(and_all), A::AbstractArrayOrBroadcasted, region) = reducedim_initarray(A, region, true)
```
-/
def reducedim_init_all {α : Type} (ops : Operations) (A : ops.Input α) (region : ops.Region) :
    Result (ops.Array Bool) :=
  reducedim_initarray ops A region true

/-!
Julia source: base/reducedim.jl:176-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reducedim_init(f, op::typeof(or_any), A::AbstractArrayOrBroadcasted, region) = reducedim_initarray(A, region, false)
```
-/
def reducedim_init_any {α : Type} (ops : Operations) (A : ops.Input α) (region : ops.Region) :
    Result (ops.Array Bool) :=
  reducedim_initarray ops A region false

/-!
Julia source: base/reducedim.jl:179-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reducedim_init(f, op::typeof(&), A::AbstractArrayOrBroadcasted, region) = reducedim_initarray(A, region, true)
```
-/
def reducedim_init_bitAnd {α : Type} (ops : Operations) (A : ops.Input α)
    (region : ops.Region) : Result (ops.Array Bool) :=
  reducedim_initarray ops A region true

/-!
Julia source: base/reducedim.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reducedim_init(f, op::typeof(|), A::AbstractArrayOrBroadcasted, region) = reducedim_initarray(A, region, false)
```
-/
def reducedim_init_bitOr {α : Type} (ops : Operations) (A : ops.Input α)
    (region : ops.Region) : Result (ops.Array Bool) :=
  reducedim_initarray ops A region false

/-!
Julia source: base/reducedim.jl:190-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global function reducedim_init(f, op::Union{typeof(+),typeof(add_sum)}, A::T, region)
        z = zero(f(zero(eltype(A))))
        reducedim_initarray(A, region, op(z, z))
    end
```
-/
def reducedim_init_add_numeric {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (A : ops.Input α) (region : ops.Region) : Result (ops.Array β) := do
  let initial ← ops.zeroType (α := α) (ops.elementType A)
  let mapped ← ops.applyFunction (F := ops.Function) (α := α) (β := β) f initial
  let z ← ops.zeroValue (α := β) mapped
  let initial ← ops.applyOperator (O := ops.Operator) (A := β) (B := β) op z z
  reducedim_initarray ops A region initial

/-!
Julia source: base/reducedim.jl:194-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global function reducedim_init(f, op::Union{typeof(*),typeof(mul_prod)}, A::T, region)
        u = one(f(one(eltype(A))))
        reducedim_initarray(A, region, op(u, u))
    end
```
-/
def reducedim_init_prod_numeric {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (A : ops.Input α) (region : ops.Region) : Result (ops.Array β) := do
  let initial ← ops.oneType (α := α) (ops.elementType A)
  let mapped ← ops.applyFunction (F := ops.Function) (α := α) (β := β) f initial
  let u ← ops.oneValue (α := β) mapped
  let initial ← ops.applyOperator (O := ops.Operator) (A := β) (B := β) op u u
  reducedim_initarray ops A region initial

def reducedim_init_dispatch {α β γ : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (A : ops.Input α) (region : ops.Region) :
    Result (ops.Array β) := do
  let kind := ops.operatorKind op
  let functionKind := ops.functionKind f
  let elementType := ops.elementType A
  if kind == "add_sum" then
    if ops.machineNumericType elementType then
      reducedim_init_add_numeric ops f op A region
    else
      reducedim_init_add ops f op A region
  else if kind == "mul_prod" then
    if ops.machineNumericType elementType then
      reducedim_init_prod_numeric ops f op A region
    else
      reducedim_init_prod ops f op A region
  else if kind == "min" then
    reducedim_init_min ops f A region
  else if kind == "max" && (functionKind == .abs || functionKind == .abs2) then
    reducedim_init_absmax ops f A region
  else if kind == "max" then
    reducedim_init_max ops f A region
  else if kind == "extrema" then do
    let result ← reducedim_init_extrema (β := γ) ops f A region
    ops.convertArray result (ops.operatorResultType op)
  else if kind == "and_all" then do
    let result ← reducedim_init_all ops A region
    ops.convertArray result (ops.operatorResultType op)
  else if kind == "or_any" then do
    let result ← reducedim_init_any ops A region
    ops.convertArray result (ops.operatorResultType op)
  else if kind == "&" then do
    let result ← reducedim_init_bitAnd ops A region
    ops.convertArray result (ops.operatorResultType op)
  else if kind == "|" then do
    let result ← reducedim_init_bitOr ops A region
    ops.convertArray result (ops.operatorResultType op)
  else
    ops.emptyReduce

def foldMappedRest {F O α β γ : Type} (ops : Operations) (f : F) (op : O)
    (initial : β) : List α → Result β
  | [] => pure initial
  | x :: xs => do
      let mapped ← ops.applyFunction (F := F) (α := α) (β := γ) f x
      let value ← ops.applyOperator (O := O) (A := β) (B := γ) op initial mapped
      foldMappedRest (γ := γ) ops f op value xs

/-!
Julia source: base/reducedim.jl:333-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mapreduce_dim(f, op, nt, A::AbstractArrayOrBroadcasted, ::Colon)
    # equivalent to `mapfoldl_impl(f, op, nt, A)` this logic is expanded here
    # to work around limitations in inference's recursion heuristic
    y = iterate(A)
    y === nothing && return nt
    v = op(nt, f(y[1]))
    for x in Iterators.rest(A, y[2])
        v = op(v, f(x))
    end
    return v
end
```
-/
def _mapreduce_dim_colon_init {α β γ : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (initial : β) (A : ops.Input α) : Result β := do
  let first ← ops.iterate A
  match first with
  | none => pure initial
  | some (x, state) => do
      let mapped ← ops.applyFunction (F := ops.Function) (α := α) (β := γ) f x
      let value ← ops.applyOperator (O := ops.Operator) (A := β) (B := γ) op initial mapped
      foldMappedRest (γ := γ) ops f op value (← ops.rest A state)

/-!
Julia source: base/reducedim.jl:345-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mapreduce_dim(f, op, ::_InitialValue, A::AbstractArrayOrBroadcasted, ::Colon) =
    _mapreduce(f, op, IndexStyle(A), A)
```
-/
def _mapreduce_dim_colon_implicit {α β : Type} (ops : Operations)
    (f : ops.Function) (op : ops.Operator) (A : ops.Input α) : Result β :=
  mapreduceNoInit ops f op A

/-!
Julia source: base/reducedim.jl:348-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mapreduce_dim(f, op, nt, A::AbstractArrayOrBroadcasted, dims::D) where {D} =
    mapreducedim!(f, op, reducedim_initarray(A, dims, nt), A)
```
-/
def _mapreduce_dim_dims_init {α β γ : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (initial : β) (A : ops.Input α) (dims : ops.Region) :
    Result (ops.Array β) := do
  let R ← reducedim_initarray ops A dims initial
  mapreducedim! (γ := γ) ops f op R A

/-!
Julia source: base/reducedim.jl:351-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mapreduce_dim(f, op, ::_InitialValue, A::AbstractArrayOrBroadcasted, dims::D) where {D} =
    mapreducedim!(f, op, reducedim_init(f, op, A, dims), A)
```
-/
def _mapreduce_dim_dims_implicit {α β γ : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (A : ops.Input α) (dims : ops.Region) : Result (ops.Array β) := do
  let R ← reducedim_init_dispatch (γ := γ) ops f op A dims
  mapreducedim! (γ := γ) ops f op R A

/-!
Julia source: base/reducedim.jl:354-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mapreduce_dim(f, op, nt, R::ReshapedArray, ::Colon) =
    _mapreduce_dim(f, op, nt, parent(R), :)
```
-/
def _mapreduce_dim_reshaped_init {α β γ : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (initial : β) (A : ops.Reshaped α) : Result β :=
  _mapreduce_dim_colon_init (γ := γ) ops f op initial (ops.parent A)

/-!
Julia source: base/reducedim.jl:357-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mapreduce_dim(f, op, i::_InitialValue, R::ReshapedArray, ::Colon) =
    _mapreduce_dim(f, op, i, parent(R), :)
```
-/
def _mapreduce_dim_reshaped_implicit {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (A : ops.Reshaped α) : Result β :=
  _mapreduce_dim_colon_implicit ops f op (ops.parent A)

/-!
Julia source: base/reducedim.jl:328-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce(f, op, A::AbstractArrayOrBroadcasted; dims::D=:, init=_InitialValue()) where {D} =
    _mapreduce_dim(f, op, init, A, dims)
```
-/
def mapreduce {α β γ : Type} (ops : Operations) (f : ops.Function) (op : ops.Operator)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) := do
  if ops.isColon dims then
    match init with
    | .implicit => return .scalar (← _mapreduce_dim_colon_implicit (β := β) ops f op A)
    | .explicit value => return .scalar (← _mapreduce_dim_colon_init (γ := γ) ops f op value A)
  else
    match init with
    | .implicit => return .array (← _mapreduce_dim_dims_implicit (γ := γ) ops f op A dims)
    | .explicit value => return .array (← _mapreduce_dim_dims_init (γ := γ) ops f op value A dims)

/-!
Julia source: base/reducedim.jl:392-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce(op, A::AbstractArray; kw...) = mapreduce(identity, op, A; kw...)
```
-/
def reduce {α β : Type} (ops : Operations) (op : ops.Operator) (A : ops.Input α)
    (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  mapreduce (γ := α) ops ops.identity op A dims init

/-!
Julia source: base/reducedim.jl:330-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce(f, op, A::AbstractArrayOrBroadcasted, B::AbstractArrayOrBroadcasted...; kw...) =
    reduce(op, map(f, A, B...); kw...)
```
-/
def mapreduce_multi {α β γ : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (A : ops.Input α) (rest : List (ops.Input α))
    (dims : ops.Region) (init : InitArg γ) :
    Result (ReducedResult ops.Array γ) := do
  let mapped ← ops.mapMany (F := ops.Function) (α := α) (β := β) f A rest
  reduce (β := γ) ops op mapped dims init
mutual
/--
Julia source: base/reducedim.jl:996-996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(a, dims; kw...)
```
-/
def sum {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _sum ops A dims init

/--
Julia source: base/reducedim.jl:997-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(f, a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(f, a, dims; kw...)
```
-/
def sum_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  _sum_function (γ := γ) ops f A dims init

/--
Julia source: base/reducedim.jl:1024-1024 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(A, dims::D; kw...) where {D} = $(_fname)(identity, A, dims; kw...)
```
-/
def _sum {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _sum_function (γ := α) ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:1025-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(f, A, dims::D; kw...) where {D} = mapreduce($mapf, $(op), A; dims=dims, kw...)
```
-/
def _sum_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops f ops.addSum A dims init

/--
Julia source: base/reducedim.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(a, ::Colon; kw...) = ($_fname)(identity, a, :; kw...)
```
-/
def _sum_colon {α β : Type} (ops : Operations) (A : ops.Input α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _sum_function_colon (γ := α) ops ops.identity A init

/--
Julia source: base/reducedim.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(f, a, ::Colon; kw...) = mapreduce($mapf, $op, a; kw...)
```
-/
def _sum_function_colon {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops f ops.addSum A ops.colonRegion init

/--
Julia source: base/reducedim.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(R::ReshapedArray, ::Colon) = ($fname)(parent(R))
```
-/
def _sum_reshaped_colon {α β : Type} (ops : Operations) (A : ops.Reshaped α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  sum ops (ops.parent A) ops.colonRegion init

/--
Julia source: base/reducedim.jl:996-996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(a, dims; kw...)
```
-/
def prod {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _prod ops A dims init

/--
Julia source: base/reducedim.jl:997-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(f, a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(f, a, dims; kw...)
```
-/
def prod_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  _prod_function (γ := γ) ops f A dims init

/--
Julia source: base/reducedim.jl:1024-1024 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(A, dims::D; kw...) where {D} = $(_fname)(identity, A, dims; kw...)
```
-/
def _prod {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _prod_function (γ := α) ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:1025-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(f, A, dims::D; kw...) where {D} = mapreduce($mapf, $(op), A; dims=dims, kw...)
```
-/
def _prod_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops f ops.mulProd A dims init

/--
Julia source: base/reducedim.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(a, ::Colon; kw...) = ($_fname)(identity, a, :; kw...)
```
-/
def _prod_colon {α β : Type} (ops : Operations) (A : ops.Input α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _prod_function_colon (γ := α) ops ops.identity A init

/--
Julia source: base/reducedim.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(f, a, ::Colon; kw...) = mapreduce($mapf, $op, a; kw...)
```
-/
def _prod_function_colon {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops f ops.mulProd A ops.colonRegion init

/--
Julia source: base/reducedim.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(R::ReshapedArray, ::Colon) = ($fname)(parent(R))
```
-/
def _prod_reshaped_colon {α β : Type} (ops : Operations) (A : ops.Reshaped α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  prod ops (ops.parent A) ops.colonRegion init

/--
Julia source: base/reducedim.jl:996-996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(a, dims; kw...)
```
-/
def maximum {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _maximum ops A dims init

/--
Julia source: base/reducedim.jl:997-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(f, a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(f, a, dims; kw...)
```
-/
def maximum_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  _maximum_function (γ := γ) ops f A dims init

/--
Julia source: base/reducedim.jl:1024-1024 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(A, dims::D; kw...) where {D} = $(_fname)(identity, A, dims; kw...)
```
-/
def _maximum {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _maximum_function (γ := α) ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:1025-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(f, A, dims::D; kw...) where {D} = mapreduce($mapf, $(op), A; dims=dims, kw...)
```
-/
def _maximum_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops f ops.maximum A dims init

/--
Julia source: base/reducedim.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(a, ::Colon; kw...) = ($_fname)(identity, a, :; kw...)
```
-/
def _maximum_colon {α β : Type} (ops : Operations) (A : ops.Input α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _maximum_function_colon (γ := α) ops ops.identity A init

/--
Julia source: base/reducedim.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(f, a, ::Colon; kw...) = mapreduce($mapf, $op, a; kw...)
```
-/
def _maximum_function_colon {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops f ops.maximum A ops.colonRegion init

/--
Julia source: base/reducedim.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(R::ReshapedArray, ::Colon) = ($fname)(parent(R))
```
-/
def _maximum_reshaped_colon {α β : Type} (ops : Operations) (A : ops.Reshaped α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  maximum ops (ops.parent A) ops.colonRegion init

/--
Julia source: base/reducedim.jl:996-996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(a, dims; kw...)
```
-/
def minimum {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _minimum ops A dims init

/--
Julia source: base/reducedim.jl:997-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(f, a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(f, a, dims; kw...)
```
-/
def minimum_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  _minimum_function (γ := γ) ops f A dims init

/--
Julia source: base/reducedim.jl:1024-1024 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(A, dims::D; kw...) where {D} = $(_fname)(identity, A, dims; kw...)
```
-/
def _minimum {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _minimum_function (γ := α) ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:1025-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(f, A, dims::D; kw...) where {D} = mapreduce($mapf, $(op), A; dims=dims, kw...)
```
-/
def _minimum_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops f ops.minimum A dims init

/--
Julia source: base/reducedim.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(a, ::Colon; kw...) = ($_fname)(identity, a, :; kw...)
```
-/
def _minimum_colon {α β : Type} (ops : Operations) (A : ops.Input α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _minimum_function_colon (γ := α) ops ops.identity A init

/--
Julia source: base/reducedim.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(f, a, ::Colon; kw...) = mapreduce($mapf, $op, a; kw...)
```
-/
def _minimum_function_colon {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops f ops.minimum A ops.colonRegion init

/--
Julia source: base/reducedim.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(R::ReshapedArray, ::Colon) = ($fname)(parent(R))
```
-/
def _minimum_reshaped_colon {α β : Type} (ops : Operations) (A : ops.Reshaped α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  minimum ops (ops.parent A) ops.colonRegion init

/--
Julia source: base/reducedim.jl:996-996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(a, dims; kw...)
```
-/
def extrema {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _extrema ops A dims init

/--
Julia source: base/reducedim.jl:997-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline ($fname)(f, a::AbstractArray; dims::D=:, kw...) where {D} = ($_fname)(f, a, dims; kw...)
```
-/
def extrema_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  _extrema_function (γ := γ × γ) ops f A dims init

/--
Julia source: base/reducedim.jl:1024-1024 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(A, dims::D; kw...) where {D} = $(_fname)(identity, A, dims; kw...)
```
-/
def _extrema {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _extrema_function (γ := α × α) ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:1025-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(f, A, dims::D; kw...) where {D} = mapreduce($mapf, $(op), A; dims=dims, kw...)
```
-/
def _extrema_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops (ops.makeExtremaMap f) ops.extremaRF A dims init

/--
Julia source: base/reducedim.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(a, ::Colon; kw...) = ($_fname)(identity, a, :; kw...)
```
-/
def _extrema_colon {α β : Type} (ops : Operations) (A : ops.Input α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _extrema_function_colon (γ := α × α) ops ops.identity A init

/--
Julia source: base/reducedim.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(f, a, ::Colon; kw...) = mapreduce($mapf, $op, a; kw...)
```
-/
def _extrema_function_colon {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  mapreduce (γ := γ) ops (ops.makeExtremaMap f) ops.extremaRF A ops.colonRegion init

/--
Julia source: base/reducedim.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($_fname)(R::ReshapedArray, ::Colon) = ($fname)(parent(R))
```
-/
def _extrema_reshaped_colon {α β : Type} (ops : Operations) (A : ops.Reshaped α)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  extrema ops (ops.parent A) ops.colonRegion init
end

def initarray! {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (R : ops.Array β) (A : ops.Input α) (init : Bool) :
    Result (ops.Array β) := do
  match ops.operatorKind op with
  | "add_sum" => initarray_sum ops R init
  | "mul_prod" => initarray_prod ops R init
  | "min" | "max" | "extrema" => initarray_minmax (F := ops.Function) ops R f A init
  | "and_all" => initarray_all ops R init
  | "or_any" => initarray_any ops R init
  | _ => ops.emptyReduce

mutual
/--
Julia source: base/reducedim.jl:1007-1007 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
any(a::AbstractArray; kw...) = any(identity, a; kw...)
```
-/
def any {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  any_function (γ := α) ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:1008-1008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
any(f, a::AbstractArray; dims::D=:) where D = _any(f, a, dims)
```
-/
def any_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  _any_function (γ := γ) ops f A dims init

/--
Julia source: base/reducedim.jl:1009-1009 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
all(a::AbstractArray; kw...) = all(identity, a; kw...)
```
-/
def all {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  all_function (γ := α) ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:1010-1010 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
all(f, a::AbstractArray; dims::D=:) where D = _all(f, a, dims)
```
-/
def all_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  _all_function (γ := γ) ops f A dims init

/--
Julia source: base/reducedim.jl:1024-1024 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(A, dims::D; kw...) where {D} = $(_fname)(identity, A, dims; kw...)
```
-/
def _any {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _any_function (γ := α) ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:1025-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(f, A, dims::D; kw...) where {D} = mapreduce($mapf, $(op), A; dims=dims, kw...)
```
-/
def _any_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  mapreduce (γ := Bool) ops (ops.boolFunction f) ops.orAny A dims init

/--
Julia source: base/reducedim.jl:1024-1024 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(A, dims::D; kw...) where {D} = $(_fname)(identity, A, dims; kw...)
```
-/
def _all {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : InitArg β) : Result (ReducedResult ops.Array β) :=
  _all_function (γ := α) ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:1025-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(_fname)(f, A, dims::D; kw...) where {D} = mapreduce($mapf, $(op), A; dims=dims, kw...)
```
-/
def _all_function {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : InitArg β) :
    Result (ReducedResult ops.Array β) :=
  mapreduce (γ := Bool) ops (ops.boolFunction f) ops.andAll A dims init

end

mutual
/--
Julia source: base/reducedim.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
count(A::AbstractArrayOrBroadcasted; dims::D=:, init=0) where {D} = count(identity, A; dims, init)
```
-/
def count {α β : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region)
    (init : β) : Result (ReducedResult ops.Array β) :=
  count_function ops ops.identity A dims init

/--
Julia source: base/reducedim.jl:426-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
count(f, A::AbstractArrayOrBroadcasted; dims::D=:, init=0) where {D} = _count(f, A, dims, init)
```
-/
def count_function {α β : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : β) :
    Result (ReducedResult ops.Array β) :=
  _count (γ := Bool) ops f A dims init

/--
Julia source: base/reducedim.jl:428-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_count(f, A::AbstractArrayOrBroadcasted, dims::Colon, init) = _simple_count(f, A, init)
```
-/
def _count {α β γ : Type} (ops : Operations) (f : ops.Function) (A : ops.Input α)
    (dims : ops.Region) (init : β) : Result (ReducedResult ops.Array β) := do
  if ops.isColon dims then
    return .scalar (← _count_colon ops f A init)
  else
    return .array (← _count_dims (γ := Bool) ops f A dims init)

def _count_colon {α β : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (init : β) : Result β :=
  ops.simpleCount f A init

/--
Julia source: base/reducedim.jl:429-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_count(f, A::AbstractArrayOrBroadcasted, dims, init) = mapreduce(_bool(f), add_sum, A; dims, init)
```
-/
def _count_dims {α β γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) (init : β) : Result (ops.Array β) :=
  do mapreduce (γ := Bool) ops (ops.boolFunction f) ops.addSum A dims (.explicit init) >>= fun result =>
      match result with
      | .array values => pure values
      | .scalar _ => ops.emptyReduce

end

mutual
/--
Julia source: base/reducedim.jl:459-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
count!(r::AbstractArray, A::AbstractArrayOrBroadcasted; init::Bool=true) = count!(identity, r, A; init=init)
```
-/
def countInPlaceIdentity {α β : Type} (ops : Operations) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) : Result (ops.Array β) :=
  countInPlace (γ := α) ops ops.identity R A init

/--
Julia source: base/reducedim.jl:460-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
count!(f, r::AbstractArray, A::AbstractArrayOrBroadcasted; init::Bool=true) =
    mapreducedim!(_bool(f), add_sum, initarray!(r, f, add_sum, init, A), A)
```
-/
def countInPlace {α β γ : Type} (ops : Operations) (f : ops.Function)
    (R : ops.Array β) (A : ops.Input α) (init : Bool) :
    Result (ops.Array β) := do
  let initial ← initarray! ops f ops.addSum R A init
  mapreducedim! (γ := Bool) ops (ops.boolFunction f) ops.addSum initial A

end

/-!
Julia source: base/reducedim.jl:1020-1021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(f, r::AbstractArray, A::AbstractArray; init::Bool=true) =
            mapreducedim!($mapf, $(op), initarray!(r, $mapf, $(op), init, A), A)
```
-/
def sumInPlace {α β γ : Type} (ops : Operations) (f : ops.Function)
    (R : ops.Array β) (A : ops.Input α) (init : Bool) :
    Result (ops.Array β) := do
  let initial ← initarray! ops f ops.addSum R A init
  mapreducedim! (γ := γ) ops f ops.addSum initial A

/-!
Julia source: base/reducedim.jl:1022-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(r::AbstractArray, A::AbstractArray; init::Bool=true) = $(fname!)(identity, r, A; init=init)
```
-/
def sumInPlaceIdentity {α β γ : Type} (ops : Operations) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) : Result (ops.Array β) :=
  sumInPlace (γ := α) ops ops.identity R A init

/-!
Julia source: base/reducedim.jl:1020-1021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(f, r::AbstractArray, A::AbstractArray; init::Bool=true) =
            mapreducedim!($mapf, $(op), initarray!(r, $mapf, $(op), init, A), A)
```
-/
def prodInPlace {α β γ : Type} (ops : Operations) (f : ops.Function)
    (R : ops.Array β) (A : ops.Input α) (init : Bool) :
    Result (ops.Array β) := do
  let initial ← initarray! ops f ops.mulProd R A init
  mapreducedim! (γ := γ) ops f ops.mulProd initial A

/-!
Julia source: base/reducedim.jl:1022-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(r::AbstractArray, A::AbstractArray; init::Bool=true) = $(fname!)(identity, r, A; init=init)
```
-/
def prodInPlaceIdentity {α β γ : Type} (ops : Operations) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) : Result (ops.Array β) :=
  prodInPlace (γ := α) ops ops.identity R A init

/-!
Julia source: base/reducedim.jl:1020-1021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(f, r::AbstractArray, A::AbstractArray; init::Bool=true) =
            mapreducedim!($mapf, $(op), initarray!(r, $mapf, $(op), init, A), A)
```
-/
def maximumInPlace {α β γ : Type} (ops : Operations) (f : ops.Function)
    (R : ops.Array β) (A : ops.Input α) (init : Bool) :
    Result (ops.Array β) := do
  let initial ← initarray! ops f ops.maximum R A init
  mapreducedim! (γ := γ) ops f ops.maximum initial A

/-!
Julia source: base/reducedim.jl:1022-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(r::AbstractArray, A::AbstractArray; init::Bool=true) = $(fname!)(identity, r, A; init=init)
```
-/
def maximumInPlaceIdentity {α β γ : Type} (ops : Operations) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) : Result (ops.Array β) :=
  maximumInPlace (γ := α) ops ops.identity R A init

/-!
Julia source: base/reducedim.jl:1020-1021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(f, r::AbstractArray, A::AbstractArray; init::Bool=true) =
            mapreducedim!($mapf, $(op), initarray!(r, $mapf, $(op), init, A), A)
```
-/
def minimumInPlace {α β γ : Type} (ops : Operations) (f : ops.Function)
    (R : ops.Array β) (A : ops.Input α) (init : Bool) :
    Result (ops.Array β) := do
  let initial ← initarray! ops f ops.minimum R A init
  mapreducedim! (γ := γ) ops f ops.minimum initial A

/-!
Julia source: base/reducedim.jl:1022-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(r::AbstractArray, A::AbstractArray; init::Bool=true) = $(fname!)(identity, r, A; init=init)
```
-/
def minimumInPlaceIdentity {α β γ : Type} (ops : Operations) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) : Result (ops.Array β) :=
  minimumInPlace (γ := α) ops ops.identity R A init

/-!
Julia source: base/reducedim.jl:1020-1021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(f, r::AbstractArray, A::AbstractArray; init::Bool=true) =
            mapreducedim!($mapf, $(op), initarray!(r, $mapf, $(op), init, A), A)
```
-/
def extremaInPlace {α β γ : Type} (ops : Operations) (f : ops.Function)
    (R : ops.Array β) (A : ops.Input α) (init : Bool) :
    Result (ops.Array β) := do
  let mapped := ops.makeExtremaMap f
  let initial ← initarray! ops mapped ops.extremaRF R A init
  mapreducedim! (γ := γ × γ) ops mapped ops.extremaRF initial A

/-!
Julia source: base/reducedim.jl:1022-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(r::AbstractArray, A::AbstractArray; init::Bool=true) = $(fname!)(identity, r, A; init=init)
```
-/
def extremaInPlaceIdentity {α β γ : Type} (ops : Operations) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) : Result (ops.Array β) :=
  extremaInPlace (γ := α) ops ops.identity R A init

/-!
Julia source: base/reducedim.jl:1020-1021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(f, r::AbstractArray, A::AbstractArray; init::Bool=true) =
            mapreducedim!($mapf, $(op), initarray!(r, $mapf, $(op), init, A), A)
```
-/
def allInPlace {α β γ : Type} (ops : Operations) (f : ops.Function)
    (R : ops.Array β) (A : ops.Input α) (init : Bool) :
    Result (ops.Array β) := do
  let mapped := ops.boolFunction f
  let initial ← initarray! ops mapped ops.andAll R A init
  mapreducedim! (γ := Bool) ops mapped ops.andAll initial A

/-!
Julia source: base/reducedim.jl:1022-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(r::AbstractArray, A::AbstractArray; init::Bool=true) = $(fname!)(identity, r, A; init=init)
```
-/
def allInPlaceIdentity {α β γ : Type} (ops : Operations) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) : Result (ops.Array β) :=
  allInPlace (γ := α) ops ops.identity R A init

/-!
Julia source: base/reducedim.jl:1020-1021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(f, r::AbstractArray, A::AbstractArray; init::Bool=true) =
            mapreducedim!($mapf, $(op), initarray!(r, $mapf, $(op), init, A), A)
```
-/
def anyInPlace {α β γ : Type} (ops : Operations) (f : ops.Function)
    (R : ops.Array β) (A : ops.Input α) (init : Bool) :
    Result (ops.Array β) := do
  let mapped := ops.boolFunction f
  let initial ← initarray! ops mapped ops.orAny R A init
  mapreducedim! (γ := Bool) ops mapped ops.orAny initial A

/-!
Julia source: base/reducedim.jl:1022-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $(fname!)(r::AbstractArray, A::AbstractArray; init::Bool=true) = $(fname!)(identity, r, A; init=init)
```
-/
def anyInPlaceIdentity {α β γ : Type} (ops : Operations) (R : ops.Array β)
    (A : ops.Input α) (init : Bool) : Result (ops.Array β) :=
  anyInPlace (γ := α) ops ops.identity R A init

def productAxisLengths (ops : Operations) : List ops.Axis → I64
  | [] => int 1
  | axis :: rest => imul (ops.axisLength axis) (productAxisLengths ops rest)

def findMinMaxAxisFirst {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (zeroIndex : ops.Index) (A : ops.Input α)
    (outer : List ops.Index) (keys : List ops.Index) (axis : List ops.Index)
    (value : β) (index : ops.Index) :
    Result (β × ops.Index × List ops.Index) := do
  match axis with
  | [] => pure (value, index, keys)
  | i :: rest =>
      match keys with
      | [] => ops.iteratorError
      | key :: remaining => do
          let input ← ops.getInput A (i :: outer)
          let mapped ← ops.applyFunction (F := ops.Function) (α := α) (β := β) f input
          let replace := ops.indexEqual index zeroIndex ||
            (← ops.applyPredicate (O := ops.Operator) (A := β) (B := β) op value mapped)
          if replace then
            findMinMaxAxisFirst ops f op zeroIndex A outer remaining rest mapped key
          else
            findMinMaxAxisFirst ops f op zeroIndex A outer remaining rest value index
termination_by axis.length

def findMinMaxOuterFirst {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (zeroIndex : ops.Index) (A : ops.Input α)
    (shape : ShapeIndexer ops.Index) (first : ops.Index) (axis : List ops.Index)
    (coords : List (List ops.Index)) (keys : List ops.Index)
    (Rval : ops.Array β) (Rind : ops.Array ops.Index) :
    Result (ops.Array β × ops.Array ops.Index × List ops.Index) := do
  match coords with
  | [] => pure (Rval, Rind, keys)
  | outer :: rest => do
      let resultIndices ← ops.newIndex outer shape shape.default
      let coordinate := first :: resultIndices
      let value ← ops.getArray Rval coordinate
      let index ← ops.getArray Rind coordinate
      let (value, index, keys) ←
        findMinMaxAxisFirst ops f op zeroIndex A outer keys axis value index
      let Rval ← ops.setArray Rval value coordinate
      let Rind ← ops.setArray Rind index coordinate
      findMinMaxOuterFirst ops f op zeroIndex A shape first axis rest keys Rval Rind
termination_by coords.length

def findMinMaxAxisSlow {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (zeroIndex : ops.Index) (A : ops.Input α)
    (outer : List ops.Index) (keys : List ops.Index) (axis : List ops.Index)
    (Rval : ops.Array β) (Rind : ops.Array ops.Index) (resultIndices : List ops.Index) :
    Result (ops.Array β × ops.Array ops.Index × List ops.Index) := do
  match axis with
  | [] => pure (Rval, Rind, keys)
  | i :: rest =>
      match keys with
      | [] => ops.iteratorError
      | key :: remaining => do
          let coordinate := i :: resultIndices
          let input ← ops.getInput A (i :: outer)
          let mapped ← ops.applyFunction (F := ops.Function) (α := α) (β := β) f input
          let value ← ops.getArray Rval coordinate
          let index ← ops.getArray Rind coordinate
          let replace := ops.indexEqual index zeroIndex ||
            (← ops.applyPredicate (O := ops.Operator) (A := β) (B := β) op value mapped)
          if replace then
            let Rval ← ops.setArray Rval mapped coordinate
            let Rind ← ops.setArray Rind key coordinate
            findMinMaxAxisSlow ops f op zeroIndex A outer remaining rest Rval Rind resultIndices
          else
            findMinMaxAxisSlow ops f op zeroIndex A outer remaining rest Rval Rind resultIndices
termination_by axis.length

def findMinMaxOuterSlow {α β : Type} (ops : Operations) (f : ops.Function)
    (op : ops.Operator) (zeroIndex : ops.Index) (A : ops.Input α)
    (shape : ShapeIndexer ops.Index) (axis : List ops.Index)
    (coords : List (List ops.Index)) (keys : List ops.Index)
    (Rval : ops.Array β) (Rind : ops.Array ops.Index) :
    Result (ops.Array β × ops.Array ops.Index × List ops.Index) := do
  match coords with
  | [] => pure (Rval, Rind, keys)
  | outer :: rest => do
      let resultIndices ← ops.newIndex outer shape shape.default
      let (Rval, Rind, keys) ←
        findMinMaxAxisSlow ops f op zeroIndex A outer keys axis Rval Rind resultIndices
      findMinMaxOuterSlow ops f op zeroIndex A shape axis rest keys Rval Rind
termination_by coords.length
/-!
Julia source: base/reducedim.jl:1032-1080 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findminmax!(f, op, Rval, Rind, A::AbstractArray{T,N}) where {T,N}
    (isempty(Rval) || isempty(A)) && return Rval, Rind
    check_reducedims(Rval, A)
    for i = 1:N
        axes(Rval, i) == axes(Rind, i) || throw(DimensionMismatch("Find-reduction: outputs must have the same indices"))
    end
    # If we're reducing along dimension 1, for efficiency we can make use of a temporary.
    # Otherwise, keep the result in Rval/Rind so that we traverse A in storage order.
    indsAt, indsRt = safe_tail(axes(A)), safe_tail(axes(Rval))
    keep, Idefault = Broadcast.shapeindexer(indsRt)
    ks = keys(A)
    y = iterate(ks)
    zi = zero(eltype(ks))
    if reducedim1(Rval)
        i1 = first(axes1(Rval))
        for IA in CartesianIndices(indsAt)
            IR = Broadcast.newindex(IA, keep, Idefault)
            @inbounds tmpRv = Rval[i1,IR]
            @inbounds tmpRi = Rind[i1,IR]
            for i in axes(A,1)
                k, kss = y::Tuple
                tmpAv = f(@inbounds(A[i,IA]))
                if tmpRi == zi || op(tmpRv, tmpAv)
                    tmpRv = tmpAv
                    tmpRi = k
                end
                y = iterate(ks, kss)
            end
            @inbounds Rval[i1,IR] = tmpRv
            @inbounds Rind[i1,IR] = tmpRi
        end
    else
        for IA in CartesianIndices(indsAt)
            IR = Broadcast.newindex(IA, keep, Idefault)
            for i in axes(A, 1)
                k, kss = y::Tuple
                tmpAv = f(@inbounds(A[i,IA]))
                @inbounds tmpRv = Rval[i,IR]
                @inbounds tmpRi = Rind[i,IR]
                if tmpRi == zi || op(tmpRv, tmpAv)
                    @inbounds Rval[i,IR] = tmpAv
                    @inbounds Rind[i,IR] = k
                end
                y = iterate(ks, kss)
            end
        end
    end
    Rval, Rind
end
```
-/
def findminmax! {α β : Type} (ops : Operations) (f : ops.Function) (op : ops.Operator)
    (Rval : ops.Array β) (Rind : ops.Array ops.Index) (A : ops.Input α) :
    Result (ops.Array β × ops.Array ops.Index) := do
  if ← ops.isEmptyArray Rval then
    return (Rval, Rind)
  if ← ops.isEmptyInput A then
    return (Rval, Rind)
  let _ ← check_reducedims ops Rval A
  let axesVal ← ops.axesArray Rval
  let axesInd ← ops.axesArray Rind
  if !ops.axesEqual axesVal axesInd then
    throw (.dimensionMismatch "Find-reduction: outputs must have the same indices")
  let axesInput ← ops.axesInput A
  let indsAt := ops.safeTail axesInput
  let indsRt := ops.safeTail axesVal
  let shape ← ops.shapeIndexer indsRt
  let keys ← ops.eachIndexInput A
  let zeroIndex ← ops.indexZero A
  let firstAxis ← ops.axisInputAt A (int 1)
  let axis ← ops.axisIndices firstAxis
  let outer ← ops.cartesianIndices indsAt
  if ← reducedim1 ops Rval then
    let resultFirst ← ops.firstAxis (← ops.axes1 Rval)
    let (Rval, Rind, _) ← findMinMaxOuterFirst ops f op zeroIndex A shape resultFirst
      axis outer keys Rval Rind
    return (Rval, Rind)
  else
    let (Rval, Rind, _) ←
      findMinMaxOuterSlow ops f op zeroIndex A shape axis outer keys Rval Rind
    return (Rval, Rind)

/-!
Julia source: base/reducedim.jl:1091-1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findmin!(rval::AbstractArray, rind::AbstractArray, A::AbstractArray;
                  init::Bool=true)
    findminmax!(identity, isgreater, init && !isempty(A) ? fill!(rval, first(A)) : rval, fill!(rind,zero(eltype(keys(A)))), A)
end
```
-/
def findminInPlace {α : Type} (ops : Operations) (Rval : ops.Array α)
    (Rind : ops.Array ops.Index) (A : ops.Input α) (init : Bool) :
    Result (ops.Array α × ops.Array ops.Index) := do
  let empty ← ops.isEmptyInput A
  let Rval ← if init && !empty then ops.fill Rval (← ops.firstInput A) else pure Rval
  let Rind ← ops.fill Rind (← ops.indexZero A)
  findminmax! ops ops.identity ops.greater Rval Rind A

/-!
Julia source: base/reducedim.jl:1164-1167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findmax!(rval::AbstractArray, rind::AbstractArray, A::AbstractArray;
                  init::Bool=true)
    findminmax!(identity, isless, init && !isempty(A) ? fill!(rval, first(A)) : rval, fill!(rind,zero(eltype(keys(A)))), A)
end
```
-/
def findmaxInPlace {α : Type} (ops : Operations) (Rval : ops.Array α)
    (Rind : ops.Array ops.Index) (A : ops.Input α) (init : Bool) :
    Result (ops.Array α × ops.Array ops.Index) := do
  let empty ← ops.isEmptyInput A
  let Rval ← if init && !empty then ops.fill Rval (← ops.firstInput A) else pure Rval
  let Rind ← ops.fill Rind (← ops.indexZero A)
  findminmax! ops ops.identity ops.less Rval Rind A

def findMinMaxInitialType {α γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) : Result TypeTag := do
  let T ← promote_union ops (ops.elementType A)
  let T := realtype ops f T
  let value ← ops.applyFunction (F := ops.Function) (α := α) (β := γ) f (← ops.firstInput A)
  if ops.isInstance value T then
    pure T
  else if ops.containsMissing (ops.elementType A) then
    pure (.union ops.missingType (ops.valueType value))
  else
    pure (ops.valueType value)


/-!
Julia source: base/reducedim.jl:1141-1153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findmin(f, A, region::D) where {D}
    ri = reduced_indices0(A, region)
    if isempty(A)
        if prod(map(length, reduced_indices(A, region))) != 0
            throw(ArgumentError("collection slices must be non-empty"))
        end
        similar(A, promote_op(f, eltype(A)), ri), zeros(eltype(keys(A)), ri)
    else
        fA = f(first(A))
        findminmax!(f, isgreater, fill!(similar(A, _findminmax_inittype(f, A), ri), fA),
                    zeros(eltype(keys(A)), ri), A)
    end
end
```
-/
def _findmin {α γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (region : ops.Region) :
    Result (FindResult ops.Array ops.Index γ) := do
  let resultAxes ← reduced_indices0_input ops A region
  let reducedAxes ← reduced_indices_input ops A region
  if ← ops.isEmptyInput A then
    if (productAxisLengths ops reducedAxes).val != 0 then
      throw (.julia (.argumentError "collection slices must be non-empty"))
    let values ← ops.similar A (ops.promoteOp (F := ops.Function) f (ops.elementType A)) resultAxes
    let indexType := ops.keysElementType A
    let indices ← ops.similar A indexType resultAxes
    let zeroIndex ← ops.zeroIndexOfType indexType
    let indices ← ops.fill indices zeroIndex
    return ⟨values, indices⟩
  let first ← ops.firstInput A
  let firstMapped ← ops.applyFunction (F := ops.Function) (α := α) (β := γ) f first
  let valueType ← findMinMaxInitialType (γ := γ) ops f A
  let values ← ops.similar A valueType resultAxes
  let values ← ops.fill values firstMapped
  let indexType := ops.keysElementType A
  let indices ← ops.similar A indexType resultAxes
  let zeroIndex ← ops.zeroIndexOfType indexType
  let indices ← ops.fill indices zeroIndex
  let (values, indices) ← findminmax! ops f ops.greater values indices A
  return ⟨values, indices⟩

/-!
Julia source: base/reducedim.jl:1139-1139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findmin(f, A::AbstractArray; dims::D=:) where {D} = _findmin(f, A, dims)
```
-/
def findmin_function {α γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) :
    Result (FindResult ops.Array ops.Index γ) :=
  _findmin ops f A dims

/-!
Julia source: base/reducedim.jl:1117-1117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_findmin(A, dims::D) where {D} = _findmin(identity, A, dims)
```
-/
def _findmin_identity {α : Type} (ops : Operations) (A : ops.Input α)
    (dims : ops.Region) : Result (FindResult ops.Array ops.Index α) :=
  _findmin ops ops.identity A dims

/-!
Julia source: base/reducedim.jl:1116-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findmin(A::AbstractArray; dims::D=:) where {D} = _findmin(A, dims)
```
-/
def findmin {α : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region) :
    Result (FindResult ops.Array ops.Index α) :=
  _findmin_identity ops A dims
/-!
Julia source: base/reducedim.jl:1214-1226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findmax(f, A, region::D) where {D}
    ri = reduced_indices0(A, region)
    if isempty(A)
        if prod(map(length, reduced_indices(A, region))) != 0
            throw(ArgumentError("collection slices must be non-empty"))
        end
        similar(A, promote_op(f, eltype(A)), ri), zeros(eltype(keys(A)), ri)
    else
        fA = f(first(A))
        findminmax!(f, isless, fill!(similar(A, _findminmax_inittype(f, A), ri), fA),
                    zeros(eltype(keys(A)), ri), A)
    end
end
```
-/
def _findmax {α γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (region : ops.Region) :
    Result (FindResult ops.Array ops.Index γ) := do
  let resultAxes ← reduced_indices0_input ops A region
  let reducedAxes ← reduced_indices_input ops A region
  if ← ops.isEmptyInput A then
    if (productAxisLengths ops reducedAxes).val != 0 then
      throw (.julia (.argumentError "collection slices must be non-empty"))
    let values ← ops.similar A (ops.promoteOp (F := ops.Function) f (ops.elementType A)) resultAxes
    let indexType := ops.keysElementType A
    let indices ← ops.similar A indexType resultAxes
    let zeroIndex ← ops.zeroIndexOfType indexType
    let indices ← ops.fill indices zeroIndex
    return ⟨values, indices⟩
  let first ← ops.firstInput A
  let firstMapped ← ops.applyFunction (F := ops.Function) (α := α) (β := γ) f first
  let valueType ← findMinMaxInitialType (γ := γ) ops f A
  let values ← ops.similar A valueType resultAxes
  let values ← ops.fill values firstMapped
  let indexType := ops.keysElementType A
  let indices ← ops.similar A indexType resultAxes
  let zeroIndex ← ops.zeroIndexOfType indexType
  let indices ← ops.fill indices zeroIndex
  let (values, indices) ← findminmax! ops f ops.less values indices A
  return ⟨values, indices⟩

/-!
Julia source: base/reducedim.jl:1190-1190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_findmax(A, dims::D) where {D} = _findmax(identity, A, dims)
```
-/
def _findmax_identity {α : Type} (ops : Operations) (A : ops.Input α)
    (dims : ops.Region) : Result (FindResult ops.Array ops.Index α) :=
  _findmax ops ops.identity A dims

/-!
Julia source: base/reducedim.jl:1189-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findmax(A::AbstractArray; dims::D=:) where {D} = _findmax(A, dims)
```
-/
def findmax {α : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region) :
    Result (FindResult ops.Array ops.Index α) :=
  _findmax_identity ops A dims

/-!
Julia source: base/reducedim.jl:1212-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findmax(f, A::AbstractArray; dims::D=:) where {D} = _findmax(f, A, dims)
```
-/
def findmax_function {α γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) (dims : ops.Region) :
    Result (FindResult ops.Array ops.Index γ) :=
  _findmax ops f A dims

/-!
Julia source: base/reducedim.jl:1228-1236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findminmax_inittype(f, A::AbstractArray)
    T = _realtype(f, promote_union(eltype(A)))
    v0 = f(first(A))
    # First conditional: T is >: typeof(v0), so return it
    # Second conditional: handle missing specifically, as most often, f(missing) = missing;
    # certainly, some predicate functions return Bool, but not all.
    # Else, return the type of the transformation.
    return v0 isa T ? T : Missing <: eltype(A) ? Union{Missing, typeof(v0)} : typeof(v0)
end
```
-/
def _findminmax_inittype {α γ : Type} (ops : Operations) (f : ops.Function)
    (A : ops.Input α) : Result TypeTag :=
  findMinMaxInitialType (γ := γ) ops f A

/-!
Julia source: base/reducedim.jl:1263-1263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argmin(A::AbstractArray; dims::D=:) where {D} = findmin(A; dims=dims)[2]
```
-/
def argmin {α : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region) :
    Result (ops.Array ops.Index) := do
  let result ← findmin ops A dims
  pure result.indices

/-!
Julia source: base/reducedim.jl:1288-1288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argmax(A::AbstractArray; dims::D=:) where {D} = findmax(A; dims=dims)[2]
```
-/
def argmax {α : Type} (ops : Operations) (A : ops.Input α) (dims : ops.Region) :
    Result (ops.Array ops.Index) := do
  let result ← findmax ops A dims
  pure result.indices
end JuliaLean.base.reducedim

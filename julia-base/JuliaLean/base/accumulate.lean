import JuliaLean.Core
import JuliaLean.base.reduce
import JuliaLean.base.reducedim

/-!
# Model of `base/accumulate.jl`

Typed cumulative-operation models for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Array indexing, mutation, index arithmetic, range iteration, operator calls, iterator collection,
and Julia's type-inference-driven result allocation are explicit interfaces. `_accumulate_promote_op` passes its nested mock
functions to the type-inference interface `promote_op`; the mocks' run-time bodies are modelled too.
-/

-- Source: base/accumulate.jl:1-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # `accumulate_pairwise` runs slightly slower than `accumulate`, but more numerically
-- # stable in certain situations (e.g. sums).
-- # It does double the number of operations compared to `accumulate`,
-- # though for cheap operations like `+` this does not have much impact (20%).
-- /Source

namespace JuliaLean.base.accumulate

open JuliaLean

inductive AccumulateError where
  | julia (error : JlError)
  | dimensionMismatch (message : String)
  deriving Repr, DecidableEq

abbrev AccResult (α : Type) := Except AccumulateError α

private def argumentError {α : Type} (message : String) : AccResult α :=
  .error (.julia (.argumentError message))

private def dimensionMismatch {α : Type} (message : String) : AccResult α :=
  .error (.dimensionMismatch message)

structure AccumulateKeywords (Init : Type) where
  keys : List String
  init : Option Init
  renderSet : List String → String

inductive AccumulationArithmeticStyle where
  | rounds
  | unknown
  | other
  deriving Repr, DecidableEq

structure AccumulateArrayOps (A B I X Y : Type) where
  axes : A → List (List I)
  outputAxes : B → List (List I)
  axesEqual : List (List I) → List (List I) → Bool
  linearIndices : A → List I
  outputLinearIndices : B → List I
  linearIndicesEqual : List I → List I → Bool
  isEmpty : A → Bool
  isVector : A → Bool
  get : A → List I → AccResult X
  getOutput : B → List I → AccResult Y
  set : B → List I → Y → AccResult B
  getLinear : A → I → AccResult X
  setLinear : B → I → Y → AccResult B
  copyTo : B → A → AccResult B

structure AccumulateOps (Op A B I X Y P Init D : Type) where
  arrays : AccumulateArrayOps A B I X Y
  apply : Op → Y → X → AccResult Y
  reduceFirst : Op → X → AccResult Y
  applyInit : Op → Init → X → AccResult Y
  similarPromoted : Op → A → Option Init → AccResult B
  iteratorAccumulate : Op → A → AccumulateKeywords Init → AccResult B
  dimPositive : D → Bool
  dimGreaterThan : D → Nat → Bool
  dimEquals : D → Nat → Bool
  dimToNat : D → AccResult Nat
  oneDim : D
  oneIndex : I
  /-- Index operations of the `first(ind)+1:last(ind)` and `i-1` expressions
  at base/accumulate.jl:393,412-415,428-431. Native Int instances wrap. -/
  indexSucc : I → I
  indexPred : I → I
  indexRange : I → I → List I
  prefixFirst : X → P
  prefixStep : Op → P → X → AccResult P
  prefixApply : Op → Y → P → AccResult Y
  prefixCombine : Op → P → P → AccResult P
  sumOp : Op
  productOp : Op
  arithmeticStyle : B → AccumulationArithmeticStyle
  emptyKeywords : AccumulateKeywords Init

private def equalIndices {I : Type} (equal : I → I → Bool) : List I → List I → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      equal left right && equalIndices equal leftRest rightRest
  | _, _ => false

def cartesianIndices {I : Type} : List (List I) → List (List I)
  | [] => [[]]
  | axis :: rest =>
      let suffixes := cartesianIndices rest
      suffixes.flatMap (fun suffix => axis.map (fun index => index :: suffix))

private def coordinates {I : Type} (before : List I) (index : I) (after : List I) : List I :=
  before ++ [index] ++ after

def initialAccumulator {Op X Y Init : Type}
    (applyInit : Op → Init → X → AccResult Y)
    (reduceFirst : Op → X → AccResult Y) (op : Op) (init : Option Init) (value : X) : AccResult Y :=
  match init with
  | none => reduceFirst op value
  | some initial => applyInit op initial value

private def accumulateLinearRest {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (accumulator : Y) : List I → AccResult B
  | [] => .ok out
  | index :: rest => do
      let value ← ops.arrays.getLinear input index
      let next ← ops.apply op accumulator value
      let out ← ops.arrays.setLinear out index next
      accumulateLinearRest ops op out input next rest

private def accumulateAlongRows {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (firstIndex : I) (after : List I) (init : Option Init) :
    List (List I) → AccResult B
  | [] => .ok out
  | row :: rows => do
      let position := coordinates row firstIndex after
      let value ← ops.arrays.get input position
      let first ← initialAccumulator ops.applyInit ops.reduceFirst op init value
      let out ← ops.arrays.set out position first
      accumulateAlongRows ops op out input firstIndex after init rows

private def accumulateInitialSlices {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (before : List (List I)) (firstIndex : I) (after : List (List I))
    (init : Option Init) : List (List I) → AccResult B
  | [] => .ok out
  | suffix :: suffixes => do
      let out ← accumulateAlongRows ops op out input firstIndex suffix init
        (cartesianIndices before)
      accumulateInitialSlices ops op out input before firstIndex after init suffixes

private def accumulateRowStep {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (previous current : I) (after : List I) :
    List (List I) → AccResult B
  | [] => .ok out
  | row :: rows => do
      let previousPosition := coordinates row previous after
      let currentPosition := coordinates row current after
      let previousValue ← ops.arrays.getOutput out previousPosition
      let currentValue ← ops.arrays.get input currentPosition
      let next ← ops.apply op previousValue currentValue
      let out ← ops.arrays.set out currentPosition next
      accumulateRowStep ops op out input previous current after rows

private def accumulateAxisSteps {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (before : List (List I)) (after : List I) : List I → AccResult B
  | [] => .ok out
  | current :: rest => do
      let out ← accumulateRowStep ops op out input (ops.indexPred current) current after
        (cartesianIndices before)
      accumulateAxisSteps ops op out input before after rest

private def accumulateSlices {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (before : List (List I)) (axisRest : List I) (firstIndex : I)
    (after : List (List I)) : List (List I) → AccResult B
  | [] => .ok out
  | suffix :: suffixes => do
      let out ← accumulateAxisSteps ops op out input before suffix axisRest
      accumulateSlices ops op out input before axisRest firstIndex after suffixes

private def accumulateAlongDimensionCore {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (before : List (List I)) (axis : List I) (after : List (List I))
    (init : Option Init) : AccResult B := do
  match axis with
  | [] => throw (.julia .boundsError)
  | firstIndex :: rest => do
      let out ← accumulateInitialSlices ops op out input before firstIndex after init
        (cartesianIndices after)
      let indices := ops.indexRange (ops.indexSucc firstIndex) (rest.getLast?.getD firstIndex)
      accumulateSlices ops op out input before indices firstIndex after (cartesianIndices after)

def accumulateFirstAxisRest {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (accumulator : Y) (after : List I) : List I → AccResult B
  | [] => .ok out
  | index :: rest => do
      let position := [index] ++ after
      let value ← ops.arrays.get input position
      let next ← ops.apply op accumulator value
      let out ← ops.arrays.set out position next
      accumulateFirstAxisRest ops op out input next after rest

def accumulateFirstAxisSlice {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (axis : List I) (after : List I) (init : Option Init) : AccResult B := do
  match axis with
  | [] => throw (.julia .boundsError)
  | firstIndex :: rest => do
      let value ← ops.arrays.get input ([firstIndex] ++ after)
      let first ← initialAccumulator ops.applyInit ops.reduceFirst op init value
      let out ← ops.arrays.set out ([firstIndex] ++ after) first
      let indices := ops.indexRange (ops.indexSucc firstIndex) (rest.getLast?.getD firstIndex)
      accumulateFirstAxisRest ops op out input first after indices

def accumulateFirstAxisSlices {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (axis : List I) (init : Option Init) :
    List (List I) → AccResult B
  | [] => .ok out
  | tailIndex :: tailIndices => do
      let out ← accumulateFirstAxisSlice ops op out input axis tailIndex init
      accumulateFirstAxisSlices ops op out input axis init tailIndices

private def accumulatePairwiseSmallRest {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (seed : Y) (runningFold : P) : List I → AccResult (B × P)
  | [] => .ok (out, runningFold)
  | index :: rest => do
      let value ← ops.arrays.getLinear input index
      let nextPrefix ← ops.prefixStep op runningFold value
      let nextOutput ← ops.prefixApply op seed nextPrefix
      let out ← ops.arrays.setLinear out index nextOutput
      accumulatePairwiseSmallRest ops op out input seed nextPrefix rest

private def accumulatePairwiseSmall {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (seed : Y) : List I → AccResult (B × P)
  | [] => .error (.julia .boundsError)
  | index :: rest => do
      let value ← ops.arrays.getLinear input index
      let runningFold := ops.prefixFirst value
      let firstOutput ← ops.prefixApply op seed runningFold
      let out ← ops.arrays.setLinear out index firstOutput
      accumulatePairwiseSmallRest ops op out input seed runningFold rest

/--
Julia source: base/accumulate.jl:7-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _accumulate_pairwise!(op::Op, c::AbstractVector{T}, v::AbstractVector, s, i1, n)::T where {T,Op}
    if n < 128
        @inbounds s_ = v[i1]
        ci1 = op(s, s_)
        @inbounds c[i1] = ci1
        for i = i1+1:i1+n-1
            s_ = op(s_, @inbounds(v[i]))
            ci = op(s, s_)
            @inbounds c[i] = ci
        end
    else
        n2 = n >> 1
        s_ = _accumulate_pairwise!(op, c, v, s, i1, n2)
        s_ = op(s_, _accumulate_pairwise!(op, c, v, op(s, s_), i1+n2, n-n2))
    end
    return s_
end

```
-/
private def accumulatePairwiseLoop {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (seed : Y) (indices : List I) : AccResult (B × P) := do
  if indices.length < 128 then
    accumulatePairwiseSmall ops op out input seed indices
  else
    let half := indices.length / 2
    let left := indices.take half
    let right := indices.drop half
    let (out, leftPrefix) ← accumulatePairwiseLoop ops op out input seed left
    let rightSeed ← ops.prefixApply op seed leftPrefix
    let (out, rightPrefix) ← accumulatePairwiseLoop ops op out input rightSeed right
    let total ← ops.prefixCombine op leftPrefix rightPrefix
    pure (out, total)
termination_by indices.length
decreasing_by
  all_goals
    simp_wf
    omega

private def unsupportedKeywords {Init α : Type}
    (errorPrefix : String) (keywords : AccumulateKeywords Init) : AccResult α :=
  let extra := keywords.keys.filter (fun key => key != "init")
  argumentError (errorPrefix ++ keywords.renderSet extra)


/--
Julia source: base/accumulate.jl:436-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _accumulate1!(op, B, v1, A::AbstractVector, dim::Integer)
    dim > 0 || throw(ArgumentError("dim must be a positive integer"))
    inds = LinearIndices(A)
    inds == LinearIndices(B) || throw(DimensionMismatch("LinearIndices of A and B don't match"))
    dim > 1 && return copyto!(B, A)
    (i1, state) = iterate(inds)::NTuple{2,Any} # We checked earlier that A isn't empty
    cur_val = v1
    B[i1] = cur_val
    next = iterate(inds, state)
    while next !== nothing
        (i, state) = next
        cur_val = op(cur_val, @inbounds(A[i]))
        @inbounds B[i] = cur_val
        next = iterate(inds, state)
    end
    return B
end

```
-/
def accumulateLinear {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (firstValue : Y) (dim : D) : AccResult B := do
  if !ops.dimPositive dim then
    throw (.julia (.argumentError "dim must be a positive integer"))
  let indices := ops.arrays.linearIndices input
  if !ops.arrays.linearIndicesEqual indices (ops.arrays.outputLinearIndices out) then
    throw (.dimensionMismatch "LinearIndices of A and B don't match")
  if ops.dimGreaterThan dim 1 then
    ops.arrays.copyTo out input
  else
    match indices with
    | [] => throw (.julia .boundsError)
    | firstIndex :: rest => do
        let out ← ops.arrays.setLinear out firstIndex firstValue
        accumulateLinearRest ops op out input firstValue rest

/--
Julia source: base/accumulate.jl:362-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _accumulate!(op, B, A::AbstractVector, dims::Nothing, init::Nothing)
    isempty(A) && return B
    v1 = reduce_first(op, first(A))
    _accumulate1!(op, B, v1, A, 1)
end

```
-/
private def accumulateVectorNoInit {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A) :
    AccResult B := do
  if ops.arrays.isEmpty input then return out
  match ops.arrays.linearIndices input with
  | [] => throw (.julia .boundsError)
  | firstIndex :: _ => do
      let firstInput ← ops.arrays.getLinear input firstIndex
      let firstValue ← ops.reduceFirst op firstInput
      accumulateLinear ops op out input firstValue ops.oneDim

/--
Julia source: base/accumulate.jl:368-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _accumulate!(op, B, A::AbstractVector, dims::Nothing, init::Some)
    isempty(A) && return B
    v1 = op(something(init), first(A))
    _accumulate1!(op, B, v1, A, 1)
end

```
-/
private def accumulateVectorWithInit {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (init : Init) : AccResult B := do
  if ops.arrays.isEmpty input then return out
  match ops.arrays.linearIndices input with
  | [] => throw (.julia .boundsError)
  | firstIndex :: _ => do
      let firstInput ← ops.arrays.getLinear input firstIndex
      let firstValue ← ops.applyInit op init firstInput
      accumulateLinear ops op out input firstValue ops.oneDim

/--
Julia source: base/accumulate.jl:358-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _accumulate!(op, B, A, dims::Nothing, init::Union{Nothing, Some})
    throw(ArgumentError("Keyword argument dims must be provided for multidimensional arrays"))
end

```
-/
def accumulateDimensionsMissing {Op A B I X Y P Init D : Type}
    (_ops : AccumulateOps Op A B I X Y P Init D) (_op : Op) (_out : B) (_input : A)
    (_init : Option Init) : AccResult B :=
  argumentError "Keyword argument dims must be provided for multidimensional arrays"

/--
Julia source: base/accumulate.jl:404-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _accumulaten!(op, B, A, R1, ind, R2, init::Nothing)
    # Copy the initial element in each 1d vector along dimension `dim`
    ii = first(ind)
    for J in R2, I in R1
        tmp = reduce_first(op, @inbounds(A[I, ii, J]))
        @inbounds B[I, ii, J] = tmp
    end
    # Accumulate
    for J in R2, i in first(ind)+1:last(ind), I in R1
        @inbounds Bv, Av = B[I, i-1, J], A[I, i, J]
        tmp = op(Bv, Av)
        @inbounds B[I, i, J] = tmp
    end
    B
end

```
-/
def accumulateNNoInit {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (before : List (List I)) (axis : List I) (after : List (List I)) : AccResult B :=
  accumulateAlongDimensionCore ops op out input before axis after none

/--
Julia source: base/accumulate.jl:420-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _accumulaten!(op, B, A, R1, ind, R2, init::Some)
    # Copy the initial element in each 1d vector along dimension `dim`
    ii = first(ind)
    for J in R2, I in R1
        tmp = op(something(init), @inbounds(A[I, ii, J]))
        @inbounds B[I, ii, J] = tmp
    end
    # Accumulate
    for J in R2, i in first(ind)+1:last(ind), I in R1
        @inbounds Bv, Av = B[I, i-1, J], A[I, i, J]
        tmp = op(Bv, Av)
        @inbounds B[I, i, J] = tmp
    end
    B
end

```
-/
def accumulateNWithInit {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (before : List (List I)) (axis : List I) (after : List (List I)) (init : Init) :
    AccResult B :=
  accumulateAlongDimensionCore ops op out input before axis after (some init)

/--
Julia source: base/accumulate.jl:374-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _accumulate!(op, B, A, dims::Integer, init::Union{Nothing, Some})
    dims > 0 || throw(ArgumentError("dims must be a positive integer"))
    inds_t = axes(A)
    axes(B) == inds_t || throw(DimensionMismatch("shape of B must match A"))
    dims > ndims(A) && return _accumulaten!(op, B, A, CartesianIndices(inds_t), OneTo(1), CartesianIndices(()), init)
    isempty(inds_t[dims]) && return B
    if dims == 1
        # We can accumulate to a temporary variable, which allows
        # register usage and will be slightly faster
        ind1 = inds_t[1]
        for I in CartesianIndices(tail(inds_t))
            if init === nothing
                tmp = reduce_first(op, @inbounds(A[first(ind1), I]))
            else
                tmp = op(something(init), @inbounds(A[first(ind1), I]))
            end
            @inbounds B[first(ind1), I] = tmp
            for i_1 = first(ind1)+1:last(ind1)
                tmp = op(tmp, @inbounds(A[i_1, I]))
                @inbounds B[i_1, I] = tmp
            end
        end
    else
        R1 = CartesianIndices(axes(A)[1:dims-1])   # not type-stable
        R2 = CartesianIndices(axes(A)[dims+1:end])
        _accumulaten!(op, B, A, R1, inds_t[dims], R2, init) # use function barrier
    end
    return B
end

```
-/
def accumulateAlongDimension {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (dim : D) (init : Option Init) : AccResult B := do
  if !ops.dimPositive dim then
    throw (.julia (.argumentError "dims must be a positive integer"))
  let axes := ops.arrays.axes input
  if !ops.arrays.axesEqual (ops.arrays.outputAxes out) axes then
    throw (.dimensionMismatch "shape of B must match A")
  if ops.dimGreaterThan dim axes.length then
    accumulateAlongDimensionCore ops op out input axes [ops.oneIndex] [] init
  else do
    let dimension ← ops.dimToNat dim
    match (axes.drop (dimension - 1)).head? with
    | none => throw (.julia .boundsError)
    | some axis =>
        if axis.isEmpty then return out
        if ops.dimEquals dim 1 then
          accumulateFirstAxisSlices ops op out input axis init (cartesianIndices (axes.drop 1))
        else
          let before := axes.take (dimension - 1)
          let after := axes.drop dimension
          accumulateAlongDimensionCore ops op out input before axis after init

def accumulateBangCore {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (dims : Option D) (init : Option Init) : AccResult B := do
  match dims with
  | none =>
      if !ops.arrays.isVector input then
        accumulateDimensionsMissing ops op out input init
      else
        match init with
        | none => accumulateVectorNoInit ops op out input
        | some value => accumulateVectorWithInit ops op out input value
  | some dimension => accumulateAlongDimension ops op out input dimension init

/--
Julia source: base/accumulate.jl:305-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    accumulate!(op, B, A; [dims], [init])

Cumulative operation `op` on `A` along the dimension `dims`, storing the result in `B`.
Providing `dims` is optional for vectors.  If the keyword argument `init` is given, its
value is used to instantiate the accumulation.

$(_DOCS_ALIASING_WARNING)

See also [`accumulate`](@ref), [`cumsum!`](@ref), [`cumprod!`](@ref).

# Examples
```jldoctest
julia> x = [1, 0, 2, 0, 3];

julia> y = rand(5);

julia> accumulate!(+, y, x);

julia> y
5-element Vector{Float64}:
 1.0
 1.0
 3.0
 3.0
 6.0

julia> A = [1 2 3; 4 5 6];

julia> B = similar(A);

julia> accumulate!(-, B, A, dims=1)
2×3 Matrix{Int64}:
  1   2   3
 -3  -3  -3

julia> accumulate!(*, B, A, dims=2, init=10)
2×3 Matrix{Int64}:
 10   20    60
 40  200  1200
```
"""
function accumulate!(op, B, A; dims::Union{Integer, Nothing} = nothing, kw...)
    nt = values(kw)
    if isempty(kw)
        _accumulate!(op, B, A, dims, nothing)
    elseif keys(kw) === (:init,)
        _accumulate!(op, B, A, dims, Some(nt.init))
    else
        throw(ArgumentError("accumulate! does not support the keyword arguments $(setdiff(keys(nt), (:init,)))"))
    end
end

````
-/
def accumulateBang {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A)
    (dims : Option D) (keywords : AccumulateKeywords Init) : AccResult B := do
  if keywords.keys.isEmpty then
    accumulateBangCore ops op out input dims none
  else if keywords.keys == ["init"] then
    match keywords.init with
    | some init => accumulateBangCore ops op out input dims (some init)
    | none => argumentError "missing init keyword value"
  else
    unsupportedKeywords "accumulate! does not support the keyword arguments " keywords

/--
Julia source: base/accumulate.jl:234-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    accumulate(op, A; dims::Integer, [init])

Cumulative operation `op` along the dimension `dims` of `A` (providing `dims` is optional
for vectors). An initial value `init` may optionally be provided by a keyword argument. See
also [`accumulate!`](@ref) to use a preallocated output array, both for performance and
to control the precision of the output (e.g. to avoid overflow).

For common operations there are specialized variants of `accumulate`,
see [`cumsum`](@ref), [`cumprod`](@ref). For a lazy version, see
[`Iterators.accumulate`](@ref).

!!! compat "Julia 1.5"
    `accumulate` on a non-array iterator requires at least Julia 1.5.

# Examples
```jldoctest
julia> accumulate(+, [1,2,3])
3-element Vector{Int64}:
 1
 3
 6

julia> accumulate(min, (1, -2, 3, -4, 5), init=0)
(0, -2, -2, -4, -4)

julia> accumulate(/, (2, 4, Inf), init=100)
(50.0, 12.5, 0.0)

julia> accumulate(=>, i^2 for i in 1:3)
3-element Vector{Any}:
          1
        1 => 4
 (1 => 4) => 9

julia> accumulate(+, fill(1, 3, 4))
3×4 Matrix{Int64}:
 1  4  7  10
 2  5  8  11
 3  6  9  12

julia> accumulate(+, fill(1, 2, 5), dims=2, init=100.0)
2×5 Matrix{Float64}:
 101.0  102.0  103.0  104.0  105.0
 101.0  102.0  103.0  104.0  105.0
```
"""
function accumulate(op, A; dims::Union{Nothing,Integer}=nothing, kw...)
    if dims === nothing && !(A isa AbstractVector)
        # This branch takes care of the cases not handled by `_accumulate!`.
        return collect(Iterators.accumulate(op, A; kw...))
    end

    nt = values(kw)
    if !(isempty(kw) || keys(nt) === (:init,))
        throw(ArgumentError("accumulate does not support the keyword arguments $(setdiff(keys(nt), (:init,)))"))
    end

    out = similar(A, _accumulate_promote_op(op, A; kw...))
    accumulate!(op, out, A; dims=dims, kw...)
end

````
-/
def accumulateArray {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (input : A)
    (dims : Option D) (keywords : AccumulateKeywords Init) : AccResult B := do
  if dims.isNone && !ops.arrays.isVector input then
    ops.iteratorAccumulate op input keywords
  else if keywords.keys.isEmpty || keywords.keys == ["init"] then do
    let out ← ops.similarPromoted op input keywords.init
    accumulateBang ops op out input dims keywords
  else
    unsupportedKeywords "accumulate does not support the keyword arguments " keywords

structure TupleAccumulateOps (Op X Y Init R : Type) where
  apply : Op → Y → X → AccResult Y
  reduceFirst : Op → X → AccResult Y
  applyInit : Op → Init → X → AccResult Y
  build : List Y → R

private def accumulateTupleLoop {Op X Y Init R : Type}
    (ops : TupleAccumulateOps Op X Y Init R) (op : Op) (reversed : List Y)
    (accumulator : Option Y) (init : Option Init) (values : List X) :
    AccResult (List Y × Option Y) := do
  match values with
  | [] => pure (reversed, accumulator)
  | value :: rest => do
      let next ← match accumulator with
        | some current => ops.apply op current value
        | none => initialAccumulator ops.applyInit ops.reduceFirst op init value
      accumulateTupleLoop ops op (next :: reversed) (some next) init rest
termination_by values.length

/--
Julia source: base/accumulate.jl:296-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function accumulate(op, xs::Tuple; init = _InitialValue())
    rf = BottomRF(op)
    ys, = afoldl(((), init), xs...) do (ys, acc), x
        acc = rf(acc, x)
        (ys..., acc), acc
    end
    return ys
end

```
-/
def accumulateTuple {Op X Y Init R : Type}
    (ops : TupleAccumulateOps Op X Y Init R) (op : Op) (values : List X)
    (init : Option Init) : AccResult R := do
  let (reversed, _) ← accumulateTupleLoop ops op [] none init values
  pure (ops.build reversed.reverse)

/--
Julia source: base/accumulate.jl:25-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function accumulate_pairwise!(op::Op, result::AbstractVector, v::AbstractVector) where Op
    li = LinearIndices(v)
    li != LinearIndices(result) && throw(DimensionMismatch("input and output array sizes and indices must match"))
    n = length(li)
    n == 0 && return result
    i1 = first(li)
    v1 = reduce_first(op, @inbounds(v[i1]))
    @inbounds result[i1] = v1
    n == 1 && return result
    _accumulate_pairwise!(op, result, v, v1, i1+1, n-1)
    return result
end

```
-/
def accumulatePairwiseBang {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (out : B) (input : A) :
    AccResult B := do
  let indices := ops.arrays.linearIndices input
  if !ops.arrays.linearIndicesEqual indices (ops.arrays.outputLinearIndices out) then
    throw (.dimensionMismatch "input and output array sizes and indices must match")
  if indices.isEmpty then return out
  match indices with
  | [] => return out
  | firstIndex :: rest => do
      let firstInput ← ops.arrays.getLinear input firstIndex
      let firstValue ← ops.reduceFirst op firstInput
      let out ← ops.arrays.setLinear out firstIndex firstValue
      if rest.isEmpty then return out
      let (out, _) ← accumulatePairwiseLoop ops op out input firstValue rest
      return out

/--
Julia source: base/accumulate.jl:38-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function accumulate_pairwise(op, v::AbstractVector{T}) where T
    out = similar(v, _accumulate_promote_op(op, v))
    return accumulate_pairwise!(op, out, v)
end


```
-/
def accumulatePairwise {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (op : Op) (input : A) : AccResult B := do
  let out ← ops.similarPromoted op input none
  accumulatePairwiseBang ops op out input

/--
Julia source: base/accumulate.jl:59-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cumsum!(out::AbstractArray{T}, v, dim, ::ArithmeticRounds) where {T}
    dim == 1 ? accumulate_pairwise!(add_sum, out, v) : copyto!(out, v)
end
```
-/
def cumsumDimRounds {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (out : B) (input : A) (dim : D) :
    AccResult B :=
  if ops.dimEquals dim 1 then accumulatePairwiseBang ops ops.sumOp out input
  else ops.arrays.copyTo out input

/--
Julia source: base/accumulate.jl:62-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cumsum!(out::AbstractArray, v, dim, ::ArithmeticUnknown)
    _cumsum!(out, v, dim, ArithmeticRounds())
end
```
-/
def cumsumDimUnknown {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (out : B) (input : A) (dim : D) :
    AccResult B :=
  cumsumDimRounds ops out input dim

/--
Julia source: base/accumulate.jl:65-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cumsum!(out::AbstractArray{T}, v, dim, ::ArithmeticStyle) where {T}
    dim == 1 ? accumulate!(add_sum, out, v) : copyto!(out, v)
end

```
-/
def cumsumDimGeneric {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (out : B) (input : A) (dim : D) :
    AccResult B :=
  if ops.dimEquals dim 1 then
    accumulateBangCore ops ops.sumOp out input none none
  else
    ops.arrays.copyTo out input

/--
Julia source: base/accumulate.jl:44-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    cumsum!(B, A; dims::Integer)

Cumulative sum of `A` along the dimension `dims`, storing the result in `B`. See also [`cumsum`](@ref).

$(_DOCS_ALIASING_WARNING)
"""
cumsum!(B::AbstractArray{T}, A; dims::Integer) where {T} =
    accumulate!(add_sum, B, A, dims=dims)

```
-/
def cumsumBangArray {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (out : B) (input : A) (dim : D) :
    AccResult B :=
  accumulateBang ops ops.sumOp out input (some dim) ops.emptyKeywords

/--
Julia source: base/accumulate.jl:54-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cumsum!(out::AbstractArray, v::AbstractVector; dims::Integer=1)
    # we dispatch on the possibility of numerical stability issues
    _cumsum!(out, v, dims, ArithmeticStyle(eltype(out)))
end

```
-/
def cumsumBangVector {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (out : B) (input : A) (dim : D) :
    AccResult B :=
  match ops.arithmeticStyle out with
  | .rounds => cumsumDimRounds ops out input dim
  | .unknown => cumsumDimUnknown ops out input dim
  | .other => cumsumDimGeneric ops out input dim

/--
Julia source: base/accumulate.jl:69-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    cumsum(A; dims::Integer)

Cumulative sum along the dimension `dims`. See also [`cumsum!`](@ref) to use a
preallocated output array, both for performance and to control the precision of
the output (e.g. to avoid overflow).

# Examples
```jldoctest
julia> a = [1 2 3; 4 5 6]
2×3 Matrix{Int64}:
 1  2  3
 4  5  6

julia> cumsum(a, dims=1)
2×3 Matrix{Int64}:
 1  2  3
 5  7  9

julia> cumsum(a, dims=2)
2×3 Matrix{Int64}:
 1  3   6
 4  9  15
```

!!! note
    The return array's `eltype` is `Int` for signed integers of less than system
    word size  and `UInt` for unsigned integers of less than system word size.
    To preserve `eltype` of arrays with small signed or unsigned integer
    `accumulate(+, A)` should be used.

    ```jldoctest
    julia> cumsum(Int8[100, 28])
    2-element Vector{Int64}:
     100
     128

    julia> accumulate(+,Int8[100, 28])
    2-element Vector{Int8}:
      100
     -128
    ```

    In the former case, the integers are widened to system word size and
    therefore the result is `Int64[100, 128]`. In the latter case, no such
    widening happens and integer overflow results in `Int8[100, -128]`.
"""
function cumsum(A::AbstractArray{T}; dims::Integer) where T
    out = similar(A, _accumulate_promote_op(add_sum, A))
    return cumsum!(out, A, dims=dims)
end

````
-/
def cumsumArray {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (input : A) (dim : D) : AccResult B := do
  let out ← ops.similarPromoted ops.sumOp input none
  cumsumBangArray ops out input dim

/--
Julia source: base/accumulate.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cumsum(x::AbstractVector) = cumsum(x, dims=1)
```
-/
def cumsumVectorDefault {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (input : A) : AccResult B :=
  cumsumArray ops input ops.oneDim

-- Source: base/accumulate.jl:121-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     cumsum(itr)
-- 
-- Cumulative sum of an iterator.
-- 
-- See also [`accumulate`](@ref) to apply functions other than `+`.
-- 
-- !!! compat "Julia 1.5"
--     `cumsum` on a non-array iterator requires at least Julia 1.5.
-- 
-- # Examples
-- ```jldoctest
-- julia> cumsum(1:3)
-- 3-element Vector{Int64}:
--  1
--  3
--  6
-- 
-- julia> cumsum((true, false, true, false, true))
-- (1, 1, 2, 2, 3)
-- 
-- julia> cumsum(fill(1, 2) for i in 1:3)
-- 3-element Vector{Vector{Int64}}:
--  [1, 1]
--  [2, 2]
--  [3, 3]
-- ```
-- """
-- /Source
/--
Julia source: base/accumulate.jl:150-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cumsum(itr) = accumulate(add_sum, itr)


```
-/
def cumsumIterator {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (input : A) : AccResult B :=
  ops.iteratorAccumulate ops.sumOp input ops.emptyKeywords

/--
Julia source: base/accumulate.jl:153-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    cumprod!(B, A; dims::Integer)

Cumulative product of `A` along the dimension `dims`, storing the result in `B`.
See also [`cumprod`](@ref).

$(_DOCS_ALIASING_WARNING)
"""
cumprod!(B::AbstractArray{T}, A; dims::Integer) where {T} =
```
-/
def cumprodBangArray {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (out : B) (input : A) (dim : D) :
    AccResult B :=
  accumulateBang ops ops.productOp out input (some dim) ops.emptyKeywords

/--
Julia source: base/accumulate.jl:162-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    accumulate!(mul_prod, B, A, dims=dims)

"""
    cumprod!(y::AbstractVector, x::AbstractVector)

Cumulative product of a vector `x`, storing the result in `y`.
See also [`cumprod`](@ref).

$(_DOCS_ALIASING_WARNING)
"""
cumprod!(y::AbstractVector, x::AbstractVector) = cumprod!(y, x, dims=1)

```
-/
def cumprodBangVector {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (out : B) (input : A) : AccResult B :=
  cumprodBangArray ops out input ops.oneDim

/--
Julia source: base/accumulate.jl:174-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    cumprod(A; dims::Integer)

Cumulative product along the dimension `dim`. See also
[`cumprod!`](@ref) to use a preallocated output array, both for performance and
to control the precision of the output (e.g. to avoid overflow).

# Examples
```jldoctest
julia> a = Int8[1 2 3; 4 5 6];

julia> cumprod(a, dims=1)
2×3 Matrix{Int64}:
 1   2   3
 4  10  18

julia> cumprod(a, dims=2)
2×3 Matrix{Int64}:
 1   2    6
 4  20  120
```
"""
function cumprod(A::AbstractArray; dims::Integer)
    return accumulate(mul_prod, A, dims=dims)
end
````
-/
def cumprodArray {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (input : A) (dim : D) : AccResult B :=
  accumulateArray ops ops.productOp input (some dim) ops.emptyKeywords

/--
Julia source: base/accumulate.jl:230-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cumprod(x::AbstractVector) = cumprod(x, dims=1)
```
-/
def cumprodVectorDefault {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (input : A) : AccResult B :=
  cumprodArray ops input ops.oneDim

-- Source: base/accumulate.jl:199-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     cumprod(itr)
-- 
-- Cumulative product of an iterator.
-- 
-- See also [`cumprod!`](@ref), [`accumulate`](@ref), [`cumsum`](@ref).
-- 
-- !!! compat "Julia 1.5"
--     `cumprod` on a non-array iterator requires at least Julia 1.5.
-- 
-- # Examples
-- ```jldoctest
-- julia> cumprod(fill(1//2, 3))
-- 3-element Vector{Rational{Int64}}:
--  1//2
--  1//4
--  1//8
-- 
-- julia> cumprod((1, 2, 1, 3, 1))
-- (1, 2, 2, 6, 6)
-- 
-- julia> cumprod("julia")
-- 5-element Vector{String}:
--  "j"
--  "ju"
--  "jul"
--  "juli"
--  "julia"
-- ```
-- """
-- /Source
/--
Julia source: base/accumulate.jl:231-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cumprod(itr) = accumulate(mul_prod, itr)


```
-/
def cumprodIterator {Op A B I X Y P Init D : Type}
    (ops : AccumulateOps Op A B I X Y P Init D) (input : A) : AccResult B :=
  ops.iteratorAccumulate ops.productOp input ops.emptyKeywords
/-- The nested functions `f`, `g` and `h` of `_accumulate_promote_op`, passed to `promote_op` as
function values. -/
inductive PromoteOpMock where
  | f
  | g
  | h
  deriving Repr, DecidableEq

/-- The callees of `_accumulate_promote_op`. Julia values (the operation, the collection, the
initial value and the iterated elements) are `X`; types are `T`. -/
structure PromoteOpOps (X T : Type) where
  typeof : X → T
  /-- `Base.promote_op(fn, argtypes...)`: the type inference of a call. -/
  promoteOp : PromoteOpMock → List T → AccResult T
  /-- `Base.promote_type(R, K)`. -/
  promoteType : T → T → AccResult T
  /-- `nothing`, `isnothing(x)`. -/
  nothing : X
  isnothing : X → Bool
  /-- The run-time callees of the mock functions: `iterate(v)`, the elements of `for val in v`,
  `Base.reduce_first(op, val)` and the call `op(a, b)`. -/
  iterate : X → AccResult (Option X)
  elements : X → AccResult (List X)
  reduceFirst : X → X → AccResult X
  call : X → X → X → AccResult X

/-- The errors of a run of a mock function: an accumulate error, or the `UndefVarError` of the
unassigned local `k` of `g`. -/
inductive PromoteMockError where
  | accumulate (error : AccumulateError)
  | undefVarError (name : String)
  deriving Repr, DecidableEq


/--
Julia source: base/accumulate.jl:454-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Internal function used to identify the widest possible eltype required for accumulate results
function _accumulate_promote_op(op, v; init=nothing)
    # Nested mock functions used to infer the widest necessary eltype
    # NOTE: We are just passing this to promote_op for inference and should never be run.

    # Initialization function used to identify initial type of `r`
    # NOTE: reduce_first may have a different return type than calling `op`
    function f(op, v, init)
        val = first(something(iterate(v)))
        return isnothing(init) ? Base.reduce_first(op, val) : op(init, val)
    end

    # Infer iteration type independent of the initialization type
    # If `op` fails then this will return `Union{}` as `k` will be undefined.
    # Returning `Union{}` is desirable as it won't break the `promote_type` call in the
    # outer scope below
    function g(op, v, r)
        local k
        for val in v
            k = op(r, val)
        end
        return k
    end

    # Finally loop again with the two types promoted together
    # If the `op` fails and reduce_first was used then this will still just
    # return the initial type, allowing the `op` to error during execution.
    function h(op, v, r)
        for val in v
            r = op(r, val)
        end
        return r
    end

    R = Base.promote_op(f, typeof(op), typeof(v), typeof(init))
    K = Base.promote_op(g, typeof(op), typeof(v), R)
    return Base.promote_op(h, typeof(op), typeof(v), Base.promote_type(R, K))
end
```
-/
def _accumulate_promote_op {X T : Type} (o : PromoteOpOps X T) (op v : X) (init : Option X := none) :
    AccResult T := do
  let init := init.getD o.nothing
  let R ← o.promoteOp .f [o.typeof op, o.typeof v, o.typeof init]
  let K ← o.promoteOp .g [o.typeof op, o.typeof v, R]
  o.promoteOp .h [o.typeof op, o.typeof v, ← o.promoteType R K]

namespace PromoteOpMock
variable {X T : Type}

/-- `f(op, v, init)`: `first(something(iterate(v)))` reduced with `init`. -/
def runF (o : PromoteOpOps X T) (op v init : X) : AccResult X := do
  -- `something(nothing)` throws `ArgumentError`; `first` of the `(value, state)` tuple is `value`
  let some val ← o.iterate v | .error (.julia (.argumentError "No value arguments present"))
  if o.isnothing init then o.reduceFirst op val else o.call op init val

/-- `g(op, v, r)`: the last `op(r, val)`, with `k` unassigned when `v` is empty. -/
def runG (o : PromoteOpOps X T) (op v r : X) : Except PromoteMockError X := do
  let vals ← (o.elements v).mapError .accumulate
  let mut k : Option X := none
  for val in vals do
    k := some (← (o.call op r val).mapError .accumulate)
  match k with
  | some value => pure value
  | none => throw (.undefVarError "k")

/-- `h(op, v, r)`: `r = op(r, val)` over `v`. -/
def runH (o : PromoteOpOps X T) (op v r : X) : AccResult X := do
  let mut r := r
  for val in ← o.elements v do
    r ← o.call op r val
  pure r

end PromoteOpMock

end JuliaLean.base.accumulate

namespace JuliaLean.Reduce

variable {α β : Type}

/-- `_accumulate1!` loop, `base/accumulate.jl:436-452`: `cur_val = op(cur_val, A[i])`. -/
def accumulateLoop (op : β → α → β) (cur : β) : List α → List β
  | [] => []
  | x :: rest => let c := op cur x; c :: accumulateLoop op c rest

/-- `_accumulate!(op, B, A::AbstractVector, nothing, init)`, `base/accumulate.jl:362-372`:
`v1 = reduce_first(op, first(A))` (`first`) without `init`, `op(init, first(A))` with it. -/
def accumulateVec (op : β → α → β) (first : α → β) (init : Option β) : List α → List β
  | [] => []
  | x :: rest =>
    let v1 := match init with | some i => op i x | none => first x
    v1 :: accumulateLoop op v1 rest

end JuliaLean.Reduce

namespace JuliaLean.BroadcastCov.Accumulate

inductive AccError where
  | argumentError
  | dimensionMismatch
  | emptyIterator
  | undefinedLocal
  deriving Repr, DecidableEq

abbrev R (α : Type) := Except AccError α

/-- `accumulate_pairwise`, lines 38-41, after allocating the output. -/
def accumulatePairwiseWrapper (op : Int → Int → Int) (xs : List Int) : List Int :=
  JuliaLean.Reduce.accumulateVec op id none xs

/-- `cumsum!` at lines 51-52 and `cumprod!` at lines 161-162 delegate to
`accumulate!`. -/
def cumsumBang (xs : List Int) : List Int :=
  JuliaLean.Reduce.accumulateVec (· + ·) id none xs

def cumprodBang (xs : List Int) : List Int :=
  JuliaLean.Reduce.accumulateVec (· * ·) id none xs

/-- `_cumsum!`, lines 59-67. Rounds selects pairwise only in dimension one;
the ordinary style selects the normal accumulator there. Other dimensions copy. -/
inductive ArithmeticKind where
  | rounds
  | unknown
  | other
  deriving Repr, DecidableEq

def cumsumDispatch (kind : ArithmeticKind) (dim : Int) (xs : List Int) : List Int :=
  match kind with
  | .rounds | .unknown =>
      if dim = 1 then accumulatePairwiseWrapper (· + ·) xs else xs
  | .other => if dim = 1 then cumsumBang xs else xs

/-- `cumsum(A; dims)`, lines 116-119, and iterator `cumsum`, line 150. -/
def cumsum (xs : List Int) : List Int := cumsumBang xs

/-- The four public `cumprod` wrappers at lines 172, 196-198 and 230-231. -/
def cumprod (xs : List Int) : List Int := cumprodBang xs

/-- `accumulate(op, xs::Tuple; init)`, lines 296-303. -/
def accumulateTuple (op : Int → Int → Int) (xs : List Int) (init : Option Int) : List Int :=
  JuliaLean.Reduce.accumulateVec op id init xs

/-- `_accumulate1!`, lines 436-452. A dimension past one copies; dimension zero
throws; dimension one stores `v1` and scans the tail. -/
def accumulate1 (op : Int → Int → Int) (v1 : Int) (xs : List Int) (dim : Int) : R (List Int) :=
  if dim ≤ 0 then .error .argumentError
  else if dim > 1 then .ok xs
  else
    match xs with
    | [] => .ok []
    | _ :: rest => .ok (v1 :: JuliaLean.Reduce.accumulateLoop op v1 rest)

inductive KeywordShape where
  | none
  | init
  | unsupported
  deriving Repr, DecidableEq

/-- `accumulate!`, lines 347-356, reduced to its keyword dispatch. -/
def accumulateBangDispatch (keywords : KeywordShape) : R Bool :=
  match keywords with
  | .none => .ok false
  | .init => .ok true
  | .unsupported => .error .argumentError

/-- `accumulate`, lines 281-294. `isVector=false` with no dimension takes the
iterator path before keyword validation, as the Julia source does. -/
inductive AccumulatePath where
  | iterator
  | array (hasInit : Bool)
  deriving Repr, DecidableEq

def accumulateDispatch (isVector : Bool) (dims : Option Int) (keywords : KeywordShape) :
    R AccumulatePath :=
  if dims.isNone && !isVector then .ok .iterator
  else
    match keywords with
    | .none => .ok (.array false)
    | .init => .ok (.array true)
    | .unsupported => .error .argumentError

/-- Nested mock `f`, lines 461-464. -/
def promoteF (op : Int → Int → Int) (xs : List Int) (init : Option Int) : R Int :=
  match xs with
  | [] => .error .emptyIterator
  | x :: _ => .ok (match init with | none => x | some i => op i x)

/-- Nested mock `g`, lines 470-476. `k` is undefined for an empty input. -/
def promoteG (op : Int → Int → Int) (xs : List Int) (r : Int) : R Int :=
  match xs with
  | [] => .error .undefinedLocal
  | x :: rest => .ok (rest.foldl (fun _ val => op r val) (op r x))

/-- Nested mock `h`, lines 481-486. -/
def promoteH (op : Int → Int → Int) (xs : List Int) (r : Int) : Int :=
  xs.foldl op r

/-- `_accumulate_promote_op`, lines 455-491, invokes the three inference passes
in order. The observation records their results on a representative value pass. -/
def promotePasses (op : Int → Int → Int) (xs : List Int) (init : Option Int) :
    R (Int × R Int × Int) := do
  let r ← promoteF op xs init
  pure (r, promoteG op xs r, promoteH op xs r)

end JuliaLean.BroadcastCov.Accumulate

namespace JuliaLean.Reduce
/-! ### `accumulate` with `dims` -/

section
variable {α β : Type}

/-- `_accumulate!(op, B, A, dims::Integer, init)` for a matrix, `base/accumulate.jl:374-434`:
`dims ≤ 0` throws, `dims > 2` treats each element as a singleton scan,
`dims = 1` scans each column, `dims = 2` scans each row (`_accumulaten!`). Entries are
returned in column-major order. -/
def accumulateDims [Inhabited α] [Inhabited β] (op : β → α → β) (first : α → β)
    (_copy : α → β) (init : Option β) (A : Mat α) (d : Int) : R (Mat β) :=
  if d ≤ 0 then .error .argumentError
  else if d > 2 then .ok ⟨A.m, A.n, A.data.map (fun x => match init with | none => first x | some i => op i x)⟩
  else if (d = 1 ∧ A.m = 0) ∨ (d = 2 ∧ A.n = 0) then .ok ⟨A.m, A.n, []⟩
  else if d = 1 then
    .ok ⟨A.m, A.n, ((List.range A.n).map fun j => accumulateVec op first init (A.col j)).flatten⟩
  else
    let rows := (List.range A.m).map fun i => accumulateVec op first init (A.row i)
    .ok ⟨A.m, A.n, ((List.range A.n).map fun j => rows.map fun r => r.getD j default).flatten⟩

/-- `accumulate(op, v; dims = d, init)` for a vector: `_accumulate!` with an integer `dims`
(`base/accumulate.jl:374-402`); the `dims == 1` branch is the column scan. -/
def accumulateVecDims (op : β → α → β) (first : α → β) (_copy : α → β) (init : Option β)
    (v : List α) (d : Int) : R (List β) :=
  if d ≤ 0 then .error .argumentError
  else if d > 1 then .ok (v.map (fun x => match init with | none => first x | some i => op i x))
  else .ok (accumulateVec op first init v)

/-- `cumsum(v::AbstractVector; dims)` for an integer vector: `cumsum!(out, v; dims)` →
`_cumsum!(out, v, dims, ArithmeticWraps())`, `base/accumulate.jl:54-67, 116-119`:
`dims == 1 ? accumulate!(add_sum, out, v) : copyto!(out, v)`. -/
def cumsumVecDims (first : α → β) (op : β → α → β) (copy : α → β) (v : List α) (d : Int) :
    R (List β) :=
  if d = 1 then .ok (accumulateVec op first none v) else .ok (v.map copy)

end

end JuliaLean.Reduce

namespace JuliaLean.ArrayOps

open JuliaLean

variable {α β : Type}

/-- `_accumulate1!` loop, `base/accumulate.jl:436-453`: `cur_val = op(cur_val, A[i])`. -/
def accumulateLoop (op : β → α → β) (cur : β) : List α → List β
  | [] => []
  | x :: rest => let c := op cur x; c :: accumulateLoop op c rest

/-- `accumulate(op, v; init)` for a vector, `base/accumulate.jl:281-293, 368-372`:
`v1 = op(init, first(A))`, then the loop. Without `init` (`base/accumulate.jl:362-366`)
`v1 = reduce_first(op, first(A))`, given here as `first`. -/
def accumulate (op : β → α → β) (init : Option β) (first : α → β) (v : List α) : List β :=
  match v with
  | [] => []
  | x :: rest =>
    let v1 := match init with | some i => op i x | none => first x
    v1 :: accumulateLoop op v1 rest

/-- `cumsum(v::AbstractVector{T})` for a `BitInteger` `T`, `base/accumulate.jl:116-149, 64-66`:
`accumulate!(add_sum, out, v)` into `Vector{sumTy T}`. -/
def cumsum {t : IntTy} (v : List (JInt t)) : List (JInt (sumTy t)) :=
  accumulate (fun c x => c + widen x) none widen v

end JuliaLean.ArrayOps

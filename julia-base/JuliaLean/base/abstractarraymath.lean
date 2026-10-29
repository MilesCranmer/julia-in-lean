import JuliaLean.base.array
import JuliaLean.base.abstractarray
import JuliaLean.base.indices

/-!
# Model of `base/abstractarraymath.jl`

Typed source models for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit
platform. Arrays, index operations, reshaping, broadcasting, and iterator operations remain typed
parameters. Tuple values are represented by lists where only their ordered contents matter.
Stateful writes use `JuliaLean.base.array.MutationM`, whose backing store is the typed mutable heap.
Julia dispatch is trusted; the dispatch helpers below select among the source-mirrored overloads.
The `reim(::AbstractArray)` signature has no method body in this file; its generic implementation is
in `base/complex.jl`.
-/

namespace JuliaLean.base.abstractarraymath

open JuliaLean JuliaLean.base.array JuliaLean.base.indices

abbrev I64 := JInt .i64
abbrev Result (α : Type) := Except Error α
abbrev MutationM (α : Type) := JuliaLean.base.array.MutationM α

abbrev TypeToken := String

def int (n : Int) : I64 := JInt.lit .i64 n

def mapMList {α β : Type} {M : Type → Type} [Monad M]
    (f : α → M β) : List α → M (List β)
  | [] => pure []
  | x :: xs => do
      let y ← f x
      let ys ← mapMList f xs
      pure (y :: ys)

private def mapCheckedMul {C : Type} {M : Type → Type} [Monad M]
    (checkedMul : C → C → M C) : List C → List C → M (List C)
  | [], _ => pure []
  | _, [] => pure []
  | x :: xs, y :: ys => do
      let z ← checkedMul x y
      let rest ← mapCheckedMul checkedMul xs ys
      pure (z :: rest)
/-! ## Array predicates and vector shape -/

/--
Julia source: base/abstractarraymath.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isreal(x::AbstractArray) = all(isreal,x)
```
-/
def isrealArray {E A : Type} (all : (E → Bool) → A → Result Bool)
    (isreal : E → Bool) (x : A) : Result Bool := all isreal x

/--
Julia source: base/abstractarraymath.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iszero(x::AbstractArray) = all(iszero,x)
```
-/
def iszeroArray {E A : Type} (all : (E → Bool) → A → Result Bool)
    (iszero : E → Bool) (x : A) : Result Bool := all iszero x

/--
Julia source: base/abstractarraymath.jl:7-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isreal(x::AbstractArray{<:Real}) = true
```
-/
def isrealRealArray {A : Type} (_x : A) : Bool := true

/--
Julia source: base/abstractarraymath.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vec(a::AbstractArray) = reshape(a,length(a))
```
-/
def vecArray {A B : Type} (length : A → Result I64) (reshape : A → I64 → Result B)
    (a : A) : Result B := do
  let n ← length a
  reshape a n

/--
Julia source: base/abstractarraymath.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vec(a::AbstractVector) = a
```
-/
def vecVector {A : Type} (a : A) : A := a

/-! `_sub` models tuple-tail overloads; `NonemptyTuple` stands for a tuple whose first element
and tail are available separately. -/
structure NonemptyTuple (α : Type) where
  head : α
  tail : List α

def subEmptyPair (_pair : Unit × Unit) : Unit := ()

/--
Julia source: base/abstractarraymath.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub(::Tuple{}, ::Tuple{}) = ()
```
-/
def subTupleEmptyPair : Unit := subEmptyPair ((), ())

/--
Julia source: base/abstractarraymath.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub(t::Tuple, ::Tuple{}) = t
```
-/
def subTupleEmptySecond {A : Type} (t : List A) (_s : Unit) : List A := t

/--
Julia source: base/abstractarraymath.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub(t::Tuple, s::Tuple) = _sub(tail(t), tail(s))
```
-/
def subTupleNonempty {A B R : Type} (sub : List A → List B → R)
    (t : NonemptyTuple A) (s : NonemptyTuple B) : R :=
  sub t.tail s.tail

def subTupleDispatch {A B : Type} : List A → List B → Result (List A)
  | t, [] => .ok t
  | _ :: t, _ :: s => subTupleDispatch t s
  | [], _ :: _ => .error (.method "_sub")


/-! ## Dimension-changing views -/

/--
Julia source: base/abstractarraymath.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dropdims(A; dims) = _dropdims(A, dims)
```
-/
def dropdims {A D B : Type} (drop : A → D → Result B) (a : A) (dims : D) : Result B :=
  drop a dims

/--
Julia source: base/abstractarraymath.jl:86-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _dropdims(A::AbstractArray, dims::Dims)
    for i in eachindex(dims)
        1 <= dims[i] <= ndims(A) || throw(ArgumentError("dropped dims must be in range 1:ndims(A)"))
        length(axes(A, dims[i])) == 1 || throw(ArgumentError("dropped dims must all be size 1"))
        for j = 1:i-1
            dims[j] == dims[i] && throw(ArgumentError("dropped dims must be unique"))
        end
    end
    ox = axes(A)
    ax = _foldoneto((ds, d) -> d in dims ? ds : (ds..., axes(A,d)), (), Val(ndims(A)))
    if isconcretetype(eltype(ox))
        # if all the axes are the same type, we can use the tail as the
        # axes of the result rather than extracting one at each index
        return reshape(A, ax::typeof(_sub(ox, dims)))
    else
        return reshape(A, ax)
    end
end
```
-/
def dropdimsDims {A Ax B : Type} {M : Type → Type} [Monad M] [MonadExceptOf Error M]
    (eachindex : List I64 → List I64) (getindex : List I64 → I64 → M I64)
    (ndims : A → I64) (axesDim : A → I64 → M Ax) (axisLength : Ax → M I64)
    (axes : A → M (List Ax))
    (foldOneto : {S : Type} → (S → I64 → M S) → S → I64 → M S)
    (isConcreteAxesType : List Ax → Bool) (sub : List Ax → List I64 → M (List Ax))
    (typeofAxes : List Ax → TypeToken) (assertAxesType : TypeToken → List Ax → M (List Ax))
    (reshape : A → List Ax → M B) (a : A) (dims : List I64) : M B := do
  for i in eachindex dims do
    let d ← getindex dims i
    if !(int 1 ≤ d ∧ d ≤ ndims a) then
      throw (.argument "dropped dims must be in range 1:ndims(A)")
    if (← axisLength (← axesDim a d)) != int 1 then
      throw (.argument "dropped dims must all be size 1")
    for j in eachindex (dims.take (i.val - 1).toNat) do
      if (← getindex dims j) == d then
        throw (.argument "dropped dims must be unique")
  let ox ← axes a
  let ax ← foldOneto (fun ds d => do
    if dims.contains d then pure ds
    else pure (ds ++ [← axesDim a d])) [] (ndims a)
  if isConcreteAxesType ox then
    let subAxes ← sub ox dims
    let typedAxes ← assertAxesType (typeofAxes subAxes) ax
    reshape a typedAxes
  else
    reshape a ax

/--
Julia source: base/abstractarraymath.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_dropdims(A::AbstractArray, dim::Integer) = _dropdims(A, (Int(dim),))
```
-/
def dropdimsInteger {A D B : Type} {M : Type → Type} [Monad M] [MonadExceptOf Error M]
    (toInt : D → M I64) (drop : A → List I64 → M B) (a : A) (dim : D) : M B := do
  let d ← toInt dim
  drop a [d]

/--
Julia source: base/abstractarraymath.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
insertdims(A; dims) = _insertdims(A, dims)
```
-/
def insertdims {A D B : Type} (insert : A → D → Result B) (a : A) (dims : D) : Result B :=
  insert a dims

/--
Julia source: base/abstractarraymath.jl:147-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _insertdims(A::AbstractArray{T, N}, dims::NTuple{M, Int}) where {T, N, M}
    for i in eachindex(dims)
        1 ≤ dims[i] || throw(ArgumentError("the smallest entry in dims must be ≥ 1."))
        dims[i] ≤ N+M || throw(ArgumentError("the largest entry in dims must be not larger than the dimension of the array and the length of dims added"))
        for j = 1:i-1
            dims[j] == dims[i] && throw(ArgumentError("inserted dims must be unique"))
        end
    end

    # acc is a tuple, where the first entry is the final shape
    # the second entry of acc is a counter for the axes of A
    inds= Base._foldoneto((acc, i) ->
                            i ∈ dims
                                ? ((acc[1]..., Base.OneTo(1)), acc[2])
                                : ((acc[1]..., axes(A, acc[2])), acc[2] + 1),
                            ((), 1), Val(N+M))
    new_shape = inds[1]
    return reshape(A, new_shape)
end
```
-/
def insertdimsDims {A Ax B : Type} {M : Type → Type} [Monad M] [MonadExceptOf Error M]
    (eachindex : List I64 → List I64) (getindex : List I64 → I64 → M I64)
    (rank : Nat) (axesDim : A → I64 → M Ax) (oneTo : I64 → Ax)
    (foldOneto : {S : Type} → (S → I64 → M S) → S → I64 → M S)
    (reshape : A → List Ax → M B) (a : A) (dims : List I64) : M B := do
  for i in eachindex dims do
    let d ← getindex dims i
    if !(int 1 ≤ d) then
      throw (.argument "the smallest entry in dims must be ≥ 1.")
    if d.val > Int.ofNat (rank + dims.length) then
      throw (.argument "the largest entry in dims must be not larger than the dimension of the array and the length of dims added")
    for j in eachindex (dims.take (i.val - 1).toNat) do
      if (← getindex dims j) == d then
        throw (.argument "inserted dims must be unique")
  let inds ← foldOneto (fun acc i => do
    if dims.contains i then
      pure (acc.1 ++ [oneTo (int 1)], acc.2)
    else
      pure (acc.1 ++ [← axesDim a acc.2], acc.2 + int 1)) ([], int 1) (int (rank + dims.length))
  reshape a inds.1

/--
Julia source: base/abstractarraymath.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_insertdims(A::AbstractArray, dim::Integer) = _insertdims(A, (Int(dim),))
```
-/
def insertdimsInteger {A D B : Type} {M : Type → Type} [Monad M] [MonadExceptOf Error M]
    (toInt : D → M I64) (insert : A → List I64 → M B) (a : A) (dim : D) : M B := do
  let d ← toInt dim
  insert a [d]

/-! ## Unary array operations -/

/--
Julia source: base/abstractarraymath.jl:194-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
conj!(A::AbstractArray{<:Number}) = (@inbounds broadcast!(conj, A, A); A)
```
-/
def conjBangNumbers {α A E : Type}
    (broadcastBang : (E → E) → A → A → MutationM α Unit)
    (conj : E → E) (a : A) : MutationM α A := do
  broadcastBang conj a a
  pure a

/--
Julia source: base/abstractarraymath.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
conj!(x::AbstractArray{<:Real}) = x
```
-/
def conjBangReal {A : Type} (a : A) : A := a

/--
Julia source: base/abstractarraymath.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
conj!(A::AbstractArray) = (foreach(conj!, A); A)
```
-/
def conjBangNested {α A E : Type}
    (foreach : (E → MutationM α Unit) → A → MutationM α Unit)
    (conjBang : E → MutationM α Unit) (a : A) : MutationM α A := do
  foreach conjBang a
  pure a

/--
Julia source: base/abstractarraymath.jl:220-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
conj(A::AbstractArray) = broadcast_preserving_zero_d(conj, A)
```
-/
def conjArray {A E F B : Type} (broadcastPreservingZeroD : (E → F) → A → Result B)
    (conj : E → F) (a : A) : Result B :=
  broadcastPreservingZeroD conj a

/--
Julia source: base/abstractarraymath.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
conj(A::AbstractArray{<:Real}) = A
```
-/
def conjRealArray {A : Type} (a : A) : A := a

/--
Julia source: base/abstractarraymath.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
real(A::AbstractArray) = broadcast_preserving_zero_d(real, A)
```
-/
def realArray {A E F B : Type} (broadcastPreservingZeroD : (E → F) → A → Result B)
    (real : E → F) (a : A) : Result B :=
  broadcastPreservingZeroD real a

/--
Julia source: base/abstractarraymath.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
real(A::AbstractArray{<:Real}) = A
```
-/
def realRealArray {A : Type} (a : A) : A := a

/--
Julia source: base/abstractarraymath.jl:269-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
imag(A::AbstractArray) = broadcast_preserving_zero_d(imag, A)
```
-/
def imagArray {A E F B : Type} (broadcastPreservingZeroD : (E → F) → A → Result B)
    (imag : E → F) (a : A) : Result B :=
  broadcastPreservingZeroD imag a

/--
Julia source: base/abstractarraymath.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
imag(A::AbstractArray{<:Real}) = zero(A)
```
-/
def imagRealArray {A B : Type} (zero : A → Result B) (a : A) : Result B := zero a

-- UNTRANSLATED: Function declaration without a method body; the generic method is in base/complex.jl.
/-!
Julia source: base/abstractarraymath.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reim(A::AbstractArray)
```
-/

/--
Julia source: base/abstractarraymath.jl:293-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(A::AbstractArray) = broadcast_preserving_zero_d(-, A)
```
-/
def negArray {A E F B : Type} (broadcastPreservingZeroD : (E → F) → A → Result B)
    (neg : E → F) (a : A) : Result B :=
  broadcastPreservingZeroD neg a

/--
Julia source: base/abstractarraymath.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::AbstractArray{<:Number}) = x
```
-/
def unaryPlusArray {A : Type} (a : A) : A := a

/--
Julia source: base/abstractarraymath.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::AbstractArray{<:Number,2}) = x
```
-/
def unaryMulArray {A : Type} (a : A) : A := a

/-! ## Dimension selection -/

/--
Julia source: base/abstractarraymath.jl:328-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _selectdim(A, d, i, idxs)
    d >= 1 || throw(ArgumentError("dimension must be ≥ 1, got $d"))
    nd = ndims(A)
    d > nd && (i == 1 || throw(BoundsError(A, (ntuple(Returns(Colon()),d-1)..., i))))
    return view(A, idxs...)
end
```
-/
def selectdimInternal {A D Ix V : Type} {M : Type → Type} [Monad M] [MonadExceptOf Error M]
    (dimensionAtLeastOne : D → M Bool) (ndims : A → I64)
    (dimensionGreater : D → I64 → M Bool) (indexEqualsOne : Ix → M Bool)
    (minusOne : D → M D) (ntupleColons : D → M (List Ix))
    (boundsError : A → List Ix → Error) (view : A → List Ix → M V)
    (a : A) (d : D) (i : Ix) (idxs : List Ix) : M V := do
  if !(← dimensionAtLeastOne d) then
    throw (.argument "dimension must be ≥ 1")
  let nd := ndims a
  if ← dimensionGreater d nd then
    if !(← indexEqualsOne i) then
      let n ← minusOne d
      let colons ← ntupleColons n
      throw (boundsError a (colons ++ [i]))
  view a idxs

/--
Julia source: base/abstractarraymath.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline selectdim(A::AbstractArray, d::Integer, i) = _selectdim(A, d, i, _setindex(i, d, map(Returns(:), axes(A))...))
```
-/
def selectdim {A D Ix Ax V : Type} {M : Type → Type} [Monad M] [MonadExceptOf Error M]
    (axes : A → M (List Ax)) (colon : Ix)
    (setindex : Ix → D → List Ix → List Ix)
    (select : A → D → Ix → List Ix → M V) (a : A) (d : D) (i : Ix) : M V := do
  let ax ← axes a
  select a d i (setindex i d (ax.map fun _ => colon))

/-! ## Circular shifts -/

/--
Julia source: base/abstractarraymath.jl:335-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function circshift(a::AbstractArray, shiftamt::Real)
    circshift!(similar(a), a, (Integer(shiftamt),))
end
```
-/
def circshiftReal {α A R : Type}
    (similar : A → MutationM α A) (toInteger : R → MutationM α I64)
    (circshiftBang : A → A → List I64 → MutationM α A)
    (a : A) (shiftamt : R) : MutationM α A := do
  let b ← similar a
  let shift ← toInteger shiftamt
  circshiftBang b a [shift]

/--
Julia source: base/abstractarraymath.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
circshift(a::AbstractArray, shiftamt::DimsInteger) = circshift!(similar(a), a, shiftamt)
```
-/
def circshiftDims {α A D : Type}
    (similar : A → MutationM α A) (circshiftBang : A → A → D → MutationM α A)
    (a : A) (shiftamt : D) : MutationM α A := do
  let b ← similar a
  circshiftBang b a shiftamt

/--
Julia source: base/abstractarraymath.jl:411-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function circshift(a::AbstractArray, shiftamt)
    circshift!(similar(a), a, map(Integer, (shiftamt...,)))
end
```
-/
def circshiftGeneric {α A S V : Type}
    (similar : A → MutationM α A) (splat : S → MutationM α (List V))
    (toInteger : V → MutationM α I64)
    (circshiftBang : A → A → List I64 → MutationM α A)
    (a : A) (shiftamt : S) : MutationM α A := do
  let b ← similar a
  let values ← splat shiftamt
  let shifts ← mapMList toInteger values
  circshiftBang b a shifts

/-! ## Repetition helpers -/

/--
Julia source: base/abstractarraymath.jl:445-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat(A::AbstractArray, counts...)
    return repeat(A, outer=counts)
end
```
-/
inductive CountArg (C I : Type) where
  | tuple (values : List C)
  | integer (value : C)
  | iterable (value : I)

def repeatPositional {α A C I : Type}
    (repeatKeyword : A → Option (CountArg C I) → Option (CountArg C I) → MutationM α A)
    (a : A) (counts : List C) : MutationM α A :=
  repeatKeyword a none (some (.tuple counts))

/--
Julia source: base/abstractarraymath.jl:482-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat(A::AbstractArray; inner = nothing, outer = nothing)
    return _RepeatInnerOuter.repeat(A, inner=inner, outer=outer)
end
```
-/
def repeatKeyword {α A C I : Type}
    (repeatModule : A → Option (CountArg C I) → Option (CountArg C I) → MutationM α A)
    (a : A) (inner : Option (CountArg C I) := none)
    (outer : Option (CountArg C I) := none) : MutationM α A :=
  repeatModule a inner outer


namespace RepeatInnerOuter

/--
Julia source: base/abstractarraymath.jl:488-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat(arr; inner=nothing, outer=nothing)
    check(arr, inner, outer)
    arr, inner, outer = resolve(arr, inner, outer)
    repeat_inner_outer(arr, inner, outer)
end
```
-/
def repeatModule {α A C I : Type}
    (check : A → Option (CountArg C I) → Option (CountArg C I) → MutationM α Unit)
    (resolve : A → Option (CountArg C I) → Option (CountArg C I) →
      MutationM α (A × Option (List C) × Option (List C)))
    (repeatFn : A → Option (List C) → Option (List C) → MutationM α A)
    (arr : A) (inner : Option (CountArg C I) := none)
    (outer : Option (CountArg C I) := none) : MutationM α A := do
  check arr inner outer
  let resolved ← resolve arr inner outer
  repeatFn resolved.1 resolved.2.1 resolved.2.2

/--
Julia source: base/abstractarraymath.jl:494-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_tuple(t::Tuple) = t
```
-/
def toTupleTuple {C : Type} (t : List C) : List C := t

/--
Julia source: base/abstractarraymath.jl:495-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_tuple(x::Integer) = (x,)
```
-/
def toTupleInteger {C : Type} (x : C) : List C := [x]

/--
Julia source: base/abstractarraymath.jl:496-496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_tuple(itr) = tuple(itr...)
```
-/
def toTupleIterator {α C I : Type}
    (collect : I → MutationM α (List C)) (tuple : List C → List C)
    (itr : I) : MutationM α (List C) := do
  let values ← collect itr
  pure (tuple values)

def toTupleDispatch {α C I : Type}
    (collect : I → MutationM α (List C)) (tuple : List C → List C)
    (value : CountArg C I) : MutationM α (List C) :=
  match value with
  | .tuple t => pure (toTupleTuple t)
  | .integer x => pure (toTupleInteger x)
  | .iterable itr => toTupleIterator collect tuple itr

/--
Julia source: base/abstractarraymath.jl:498-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pad(a, b)
    N = max(length(a), length(b))
    Base.fill_to_length(a, 1, Val(N)), Base.fill_to_length(b, 1, Val(N))
end
```
-/
def padTwo {A B C : Type} (lengthA : A → Nat) (lengthB : B → Nat)
    (fillA : A → C → Nat → A) (fillB : B → C → Nat → B) (one : C)
    (a : A) (b : B) : A × B :=
  let N := max (lengthA a) (lengthB b)
  (fillA a one N, fillB b one N)

/--
Julia source: base/abstractarraymath.jl:502-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pad(a, b, c)
    N = max(max(length(a), length(b)), length(c))
    Base.fill_to_length(a, 1, Val(N)), Base.fill_to_length(b, 1, Val(N)), Base.fill_to_length(c, 1, Val(N))
end
```
-/
def padThree {A B C D : Type} (lengthA : A → Nat) (lengthB : B → Nat)
    (lengthC : C → Nat) (fillA : A → D → Nat → A) (fillB : B → D → Nat → B)
    (fillC : C → D → Nat → C) (one : D) (a : A) (b : B) (c : C) : A × B × C :=
  let N := max (max (lengthA a) (lengthB b)) (lengthC c)
  (fillA a one N, fillB b one N, fillC c one N)

/--
Julia source: base/abstractarraymath.jl:507-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function resolve(arr::AbstractArray{<:Any, N}, inner::NTuple{N, Any}, outer::NTuple{N,Any}) where {N}
    arr, inner, outer
end
```
-/
def resolveSameRank {A C : Type} (arr : A) (inner outer : List C) : A × List C × List C :=
  (arr, inner, outer)

/--
Julia source: base/abstractarraymath.jl:510-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function resolve(arr, inner, outer)
    dims, inner, outer = pad(size(arr), to_tuple(inner), to_tuple(outer))
    reshape(arr, dims), inner, outer
end
```
-/
def resolveGeneric {α A C I : Type}
    (size : A → MutationM α (List C))
    (toTuple : CountArg C I → MutationM α (List C))
    (pad : List C → List C → List C → List C × List C × List C)
    (reshape : A → List C → MutationM α A)
    (arr : A) (inner outer : CountArg C I) :
    MutationM α (A × List C × List C) := do
  let dims ← size arr
  let inner ← toTuple inner
  let outer ← toTuple outer
  let (dims, inner, outer) := pad dims inner outer
  let arr ← reshape arr dims
  pure (arr, inner, outer)

/--
Julia source: base/abstractarraymath.jl:514-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function resolve(arr, inner::Nothing, outer::Nothing)
    return arr, inner, outer
end
```
-/
def resolveNoCounts {A C : Type} (arr : A) : A × Option (List C) × Option (List C) :=
  (arr, none, none)

/--
Julia source: base/abstractarraymath.jl:517-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function resolve(arr, inner::Nothing, outer)
    dims, outer = pad(size(arr), to_tuple(outer))
    reshape(arr, dims), inner, outer
end
```
-/
def resolveOuterOnly {α A C I : Type}
    (size : A → MutationM α (List C)) (toTuple : CountArg C I → MutationM α (List C))
    (pad : List C → List C → List C × List C) (reshape : A → List C → MutationM α A)
    (arr : A) (outer : CountArg C I) :
    MutationM α (A × Option (List C) × Option (List C)) := do
  let dims ← size arr
  let outer ← toTuple outer
  let (dims, outer) := pad dims outer
  let arr ← reshape arr dims
  pure (arr, none, some outer)

/--
Julia source: base/abstractarraymath.jl:521-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function resolve(arr, inner, outer::Nothing)
    dims, inner = pad(size(arr), to_tuple(inner))
    reshape(arr, dims), inner, outer
end
```
-/
def resolveInnerOnly {α A C I : Type}
    (size : A → MutationM α (List C)) (toTuple : CountArg C I → MutationM α (List C))
    (pad : List C → List C → List C × List C) (reshape : A → List C → MutationM α A)
    (arr : A) (inner : CountArg C I) :
    MutationM α (A × Option (List C) × Option (List C)) := do
  let dims ← size arr
  let inner ← toTuple inner
  let (dims, inner) := pad dims inner
  let arr ← reshape arr dims
  pure (arr, some inner, none)

def padListsTwo {C : Type} (fill : List C → C → Nat → List C) (one : C)
    (a b : List C) : List C × List C :=
  padTwo List.length List.length fill fill one a b

def padListsThree {C : Type} (fill : List C → C → Nat → List C) (one : C)
    (a b c : List C) : List C × List C × List C :=
  padThree List.length List.length List.length fill fill fill one a b c

def resolveDispatch {α A C I : Type}
    (rank : A → Nat) (size : A → MutationM α (List C))
    (collect : I → MutationM α (List C)) (tuple : List C → List C)
    (fill : List C → C → Nat → List C) (one : C)
    (reshape : A → List C → MutationM α A) (arr : A)
    (inner outer : Option (CountArg C I)) :
    MutationM α (A × Option (List C) × Option (List C)) := do
  match inner, outer with
  | none, none => pure (resolveNoCounts arr)
  | none, some outer =>
      resolveOuterOnly size (toTupleDispatch collect tuple) (padListsTwo fill one)
        reshape arr outer
  | some inner, none =>
      resolveInnerOnly size (toTupleDispatch collect tuple) (padListsTwo fill one)
        reshape arr inner
  | some (.tuple inner), some (.tuple outer) =>
      if rank arr = inner.length ∧ rank arr = outer.length then
        let resolved := resolveSameRank arr inner outer
        pure (resolved.1, some resolved.2.1, some resolved.2.2)
      else
        let resolved ← resolveGeneric size (toTupleDispatch collect tuple)
          (padListsThree fill one) reshape arr (.tuple inner) (.tuple outer)
        pure (resolved.1, some resolved.2.1, some resolved.2.2)
  | some inner, some outer =>
      let resolved ← resolveGeneric size (toTupleDispatch collect tuple)
        (padListsThree fill one) reshape arr inner outer
      pure (resolved.1, some resolved.2.1, some resolved.2.2)

/--
Julia source: base/abstractarraymath.jl:526-552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check(arr, inner, outer)
    if inner !== nothing
        # TODO: Currently one based indexing is demanded for inner !== nothing,
        # but not for outer !== nothing. Decide for something consistent.
        Base.require_one_based_indexing(arr)
        if !all(n -> n isa Integer, inner)
            throw(ArgumentError("repeat requires integer counts, got inner = $inner"))
        end
        if any(<(0), inner)
            throw(ArgumentError("no inner repetition count may be negative; got $inner"))
        end
        if length(inner) < ndims(arr)
            throw(ArgumentError("number of inner repetitions ($(length(inner))) cannot be less than number of dimensions of input array ($(ndims(arr)))"))
        end
    end
    if outer !== nothing
        if !all(n -> n isa Integer, outer)
            throw(ArgumentError("repeat requires integer counts, got outer = $outer"))
        end
        if any(<(0), outer)
            throw(ArgumentError("no outer repetition count may be negative; got $outer"))
        end
        if (length(outer) < ndims(arr)) && (inner !== nothing)
            throw(ArgumentError("number of outer repetitions ($(length(outer))) cannot be less than number of dimensions of input array ($(ndims(arr)))"))
        end
    end
end
```
-/
def check {α A C I : Type}
    (requireOneBased : A → MutationM α Unit)
    (isInteger : C → Bool) (isNegative : C → Bool)
    (all : (C → MutationM α Bool) → CountArg C I → MutationM α Bool)
    (any : (C → MutationM α Bool) → CountArg C I → MutationM α Bool)
    (length : CountArg C I → MutationM α I64) (ndims : A → I64)
    (arr : A) (inner outer : Option (CountArg C I)) : MutationM α Unit := do
  if let some inner := inner then
    requireOneBased arr
    if !(← all (fun n => pure (isInteger n)) inner) then
      throw (.argument "repeat requires integer counts in inner")
    if ← any (fun n => pure (isNegative n)) inner then
      throw (.argument "no inner repetition count may be negative")
    if (← length inner) < ndims arr then
      throw (.argument "number of inner repetitions cannot be less than number of dimensions")
  if let some outer := outer then
    if !(← all (fun n => pure (isInteger n)) outer) then
      throw (.argument "repeat requires integer counts in outer")
    if ← any (fun n => pure (isNegative n)) outer then
      throw (.argument "no outer repetition count may be negative")
    if (← length outer) < ndims arr then
      if inner.isSome then
        throw (.argument "number of outer repetitions cannot be less than number of dimensions")

def checkDispatch {α A C I : Type}
    (requireOneBased : A → MutationM α Unit)
    (isInteger : C → Bool) (isNegative : C → Bool)
    (all : (C → MutationM α Bool) → CountArg C I → MutationM α Bool)
    (any : (C → MutationM α Bool) → CountArg C I → MutationM α Bool)
    (length : CountArg C I → MutationM α I64) (ndims : A → I64) :
    A → Option (CountArg C I) → Option (CountArg C I) → MutationM α Unit :=
  check requireOneBased isInteger isNegative all any length ndims

/--
Julia source: base/abstractarraymath.jl:554-554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repeat_inner_outer(arr, inner::Nothing, outer::Nothing) = arr
```
-/
def repeatInnerOuterNoneNone {α A : Type} (arr : A)
    : MutationM α A := pure arr

/--
Julia source: base/abstractarraymath.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repeat_inner_outer(arr, ::Nothing, outer) = repeat_outer(arr, outer)
```
-/
def repeatInnerOuterNone {α A C : Type}
    (repeatOuter : A → List C → MutationM α A) (arr : A) (outer : List C) :
    MutationM α A := repeatOuter arr outer

/--
Julia source: base/abstractarraymath.jl:556-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repeat_inner_outer(arr, inner, ::Nothing) = repeat_inner(arr, inner)
```
-/
def repeatInnerOuterInnerNone {α A C : Type}
    (repeatInner : A → List C → MutationM α A) (arr : A) (inner : List C) :
    MutationM α A := repeatInner arr inner

/--
Julia source: base/abstractarraymath.jl:557-557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repeat_inner_outer(arr, inner, outer) = repeat_outer(repeat_inner(arr, inner), outer)
```
-/
def repeatInnerOuterBoth {α A C : Type}
    (repeatInner : A → List C → MutationM α A) (repeatOuter : A → List C → MutationM α A)
    (arr : A) (inner outer : List C) : MutationM α A := do
  let innerResult ← repeatInner arr inner
  repeatOuter innerResult outer

end RepeatInnerOuter

/-! Typed operations used by `repeat_outer` and `repeat_inner`. -/
structure RepeatArrayOps (α A E C Ix Selector : Type) where
  size : A → MutationM α (List C)
  sizeAt : A → C → MutationM α C
  length : A → MutationM α C
  similar1 : A → C → MutationM α A
  similar2 : A → C → C → MutationM α A
  similarDims : A → List C → MutationM α A
  one : C
  add : C → C → C
  sub : C → C → C
  mul : C → C → C
  checkedMul : C → C → MutationM α C
  range : C → C → MutationM α (List C)
  rangeSelector : C → C → MutationM α Selector
  matrixIndex : Selector → Selector → Ix
  vectorIndex : Selector → Ix
  cartesianIndicesArray : A → MutationM α (List Ix)
  cartesianIndicesDims : List C → MutationM α (List Ix)
  tupleIndex : Ix → List C
  cartesianIndex : List C → Ix
  zipMap3 : List C → List C → List C → (C → C → C → C) → List C
  getindex : A → Ix → MutationM α E
  setindex : A → Ix → E → MutationM α Unit
  setBlock : A → Ix → A → MutationM α Unit

end JuliaLean.base.abstractarraymath

namespace JuliaLean.base.abstractarraymath.RepeatInnerOuter

open JuliaLean JuliaLean.base.abstractarraymath JuliaLean.base.array

/--
Julia source: base/abstractarraymath.jl:559-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat_outer(a::AbstractMatrix, (m,n)::NTuple{2, Any})
    o, p = size(a,1), size(a,2)
    b = similar(a, Base.checked_mul(o, m), Base.checked_mul(p, n))
    for j=1:n
        d = (j-1)*p+1
        R = d:d+p-1
        for i=1:m
            c = (i-1)*o+1
            @inbounds b[c:c+o-1, R] = a
        end
    end
    return b
end
```
-/
def repeatOuterMatrix {α A E C Ix Selector : Type}
    (ops : RepeatArrayOps α A E C Ix Selector) (a : A) (m n : C) : MutationM α A := do
  let o ← ops.sizeAt a ops.one
  let p ← ops.sizeAt a (ops.add ops.one ops.one)
  let rows ← ops.checkedMul o m
  let cols ← ops.checkedMul p n
  let b ← ops.similar2 a rows cols
  for j in ← ops.range ops.one n do
    let d := ops.add (ops.mul (ops.sub j ops.one) p) ops.one
    let rstop := ops.sub (ops.add d p) ops.one
    let r ← ops.rangeSelector d rstop
    for i in ← ops.range ops.one m do
      let c := ops.add (ops.mul (ops.sub i ops.one) o) ops.one
      let cstop := ops.sub (ops.add c o) ops.one
      let cRange ← ops.rangeSelector c cstop
      ops.setBlock b (ops.matrixIndex cRange r) a
  pure b

/--
Julia source: base/abstractarraymath.jl:573-581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat_outer(a::AbstractVector, (m,)::Tuple{Any})
    o = length(a)
    b = similar(a, Base.checked_mul(o, m))
    for i=1:m
        c = (i-1)*o+1
        @inbounds b[c:c+o-1] = a
    end
    return b
end
```
-/
def repeatOuterVector {α A E C Ix Selector : Type}
    (ops : RepeatArrayOps α A E C Ix Selector) (a : A) (m : C) : MutationM α A := do
  let o ← ops.length a
  let size ← ops.checkedMul o m
  let b ← ops.similar1 a size
  for i in ← ops.range ops.one m do
    let c := ops.add (ops.mul (ops.sub i ops.one) o) ops.one
    let cstop := ops.sub (ops.add c o) ops.one
    let cRange ← ops.rangeSelector c cstop
    ops.setBlock b (ops.vectorIndex cRange) a
  pure b

/--
Julia source: base/abstractarraymath.jl:583-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat_outer(arr::AbstractArray{<:Any,N}, dims::NTuple{N,Any}) where {N}
    insize  = size(arr)
    outsize = map(Base.checked_mul, insize, dims)
    out = similar(arr, outsize)
    for I in CartesianIndices(arr)
        for J in CartesianIndices(dims)
            TIJ = map(Tuple(I), Tuple(J), insize) do i, j, d
                i + d * (j-1)
            end
            IJ = CartesianIndex(TIJ)
            @inbounds out[IJ] = arr[I]
        end
    end
    return out
end
```
-/
def repeatOuterArray {α A E C Ix Selector : Type}
    (ops : RepeatArrayOps α A E C Ix Selector) (arr : A) (dims : List C) : MutationM α A := do
  let insize ← ops.size arr
  let outsize ← mapCheckedMul ops.checkedMul insize dims
  let out ← ops.similarDims arr outsize
  for I in ← ops.cartesianIndicesArray arr do
    for J in ← ops.cartesianIndicesDims dims do
      let tij := ops.zipMap3 (ops.tupleIndex I) (ops.tupleIndex J) insize
        (fun i j d => ops.add i (ops.mul d (ops.sub j ops.one)))
      let IJ := ops.cartesianIndex tij
      let value ← ops.getindex arr I
      ops.setindex out IJ value
  pure out

/--
Julia source: base/abstractarraymath.jl:599-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat_inner(arr, inner)
    outsize = map(Base.checked_mul, size(arr), inner)
    out = similar(arr, outsize)
    for I in CartesianIndices(arr)
        for J in CartesianIndices(inner)
            TIJ = map(Tuple(I), Tuple(J), inner) do i, j, d
                (i-1) * d + j
            end
            IJ = CartesianIndex(TIJ)
            @inbounds out[IJ] = arr[I]
        end
    end
    return out
end
```
-/
def repeatInner {α A E C Ix Selector : Type}
    (ops : RepeatArrayOps α A E C Ix Selector) (arr : A) (inner : List C) : MutationM α A := do
  let size ← ops.size arr
  let outsize ← mapCheckedMul ops.checkedMul size inner
  let out ← ops.similarDims arr outsize
  for I in ← ops.cartesianIndicesArray arr do
    for J in ← ops.cartesianIndicesDims inner do
      let tij := ops.zipMap3 (ops.tupleIndex I) (ops.tupleIndex J) inner
        (fun i j d => ops.add (ops.mul (ops.sub i ops.one) d) j)
      let IJ := ops.cartesianIndex tij
      let value ← ops.getindex arr I
      ops.setindex out IJ value
  pure out

def repeatOuterDispatch {α A E C Ix Selector : Type}
    (ops : RepeatArrayOps α A E C Ix Selector) (rank : A → Nat)
    (arr : A) (dims : List C) : MutationM α A :=
  match rank arr, dims with
  | 2, [m, n] => repeatOuterMatrix ops arr m n
  | 1, [m] => repeatOuterVector ops arr m
  | _, _ => repeatOuterArray ops arr dims

def repeatInnerOuterDispatch {α A E C Ix Selector : Type}
    (ops : RepeatArrayOps α A E C Ix Selector) (rank : A → Nat)
    (arr : A) (inner outer : Option (List C)) : MutationM α A :=
  match inner, outer with
  | none, none => repeatInnerOuterNoneNone arr
  | none, some outer => repeatInnerOuterNone (repeatOuterDispatch ops rank) arr outer
  | some inner, none => repeatInnerOuterInnerNone (repeatInner ops) arr inner
  | some inner, some outer =>
      repeatInnerOuterBoth (repeatInner ops) (repeatOuterDispatch ops rank) arr inner outer


end JuliaLean.base.abstractarraymath.RepeatInnerOuter

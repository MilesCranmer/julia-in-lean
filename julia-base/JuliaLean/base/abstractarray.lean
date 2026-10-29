import JuliaLean.Core

/-!
# Model of `base/abstractarray.jl`

Target: `f755f49a9e41380d7da126b3c1db9fe7f83dd027`, 64-bit Julia.
Array interface calls, including size, axes, indexing, allocation and iteration,
are typed parameters. No array representation or dispatch interpreter is imposed.
Mutating methods are polymorphic in their effect monad so interfaces can share
mutable storage. `ForIn` and `whileLoop` supply language-level iteration; the
method bodies retain every check, read, write, and iterator advance.
Each definition carries its exact Julia source. Untranslated blocks identify
methods outside the translated prefix explicitly.
-/

namespace JuliaLean.base.abstractarray

open JuliaLean

abbrev I64 := JInt .i64

def int (z : Int) : I64 := JInt.lit .i64 z

/-- The Base error types used by this file. -/
inductive ArrayError where
  | julia (error : JlError)
  | dimensionMismatch (message : String)
  | canonicalIndex (functionName typeName : String)
  | errorException (message : String)
  | assertionError (message : String)
  deriving DecidableEq, Repr

/-- Runtime type objects remain typed payloads; type-name tokens suffice in
the exception channel, whose observable contract concerns exception classes. -/
structure CanonicalError (Ty : Type) where
  functionName : String
  typeToken : Ty

def canonicalError (e : CanonicalError String) : ArrayError :=
  .canonicalIndex e.functionName e.typeToken

abbrev Result (α : Type) := Except ArrayError α

def liftJulia (r : Jl α) : Result α := r.mapError ArrayError.julia

/-- Checked indexing of the native tuple returned by an interface call. -/
def tupleGet (xs : List α) (i : I64) : Result α :=
  if i.val < 1 then .error (.julia .boundsError)
  else match xs[(i.val - 1).toNat]? with
    | some x => .ok x
    | none => .error (.julia .boundsError)

/-- Short-circuit evaluation of a tuple predicate, with its initial result. -/
def anyTupleM (p : α → Result Bool) (initial : Bool) : List α → Result Bool
  | [] => pure initial
  | x :: xs => do
      if initial then return true
      if ← p x then return true
      anyTupleM p false xs

/-- Short-circuit all, preserving predicate exceptions and evaluation order. -/
def allTupleM (p : α → Result Bool) : List α → Result Bool
  | [] => pure true
  | x :: xs => do
      if ← p x then allTupleM p xs else return false

/--
Julia source: base/abstractarray.jl:16-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, a::T) where {T<:AbstractArray} = a
```
-/
def convertSame {A : Type} (a : A) : A := a

/--
Julia source: base/abstractarray.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{AbstractArray{T}}, a::AbstractArray) where {T} = AbstractArray{T}(a)::AbstractArray{T}
```
-/
def convertAbstract {A B : Type} (construct : A → Result B) (a : A) : Result B :=
  construct a

/--
Julia source: base/abstractarray.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{AbstractArray{T,N}}, a::AbstractArray{<:Any,N}) where {T,N} = AbstractArray{T,N}(a)::AbstractArray{T,N}
```
-/
def convertAbstractN {A B : Type} (construct : A → Result B) (a : A) : Result B :=
  construct a

/--
Julia source: base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function size(t::AbstractArray, dim)
    d = Int(dim)::Int
    s = size(t)
    d <= length(s) ? s[d] : 1
end
```
-/
def sizeDim {A D : Type} (toInt : D → Result I64)
    (size : A → Result (List I64)) (a : A) (dim : D) : Result I64 := do
  let d ← toInt dim
  let s ← size a
  if d.val ≤ (s.length : Int) then tupleGet s d else pure (int 1)

/--
Julia source: base/abstractarray.jl:79-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function axes(A::AbstractArray{T,N}, d) where {T,N}
    @inline
    d::Integer <= N ? axes(A)[d] : OneTo(1)
end
```
-/
def axesDim {A D Ax R : Type} (leN : D → I64 → Bool)
    (axes : A → Result Ax) (get : Ax → D → Result R) (oneTo : I64 → R)
    (n : I64) (a : A) (d : D) : Result R :=
  if leN d n then do get (← axes a) d else pure (oneTo (int 1))

/--
Julia source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function axes(A)
    @inline
    map(unchecked_oneto, size(A))
end
```
-/
def axesDefault {A R : Type} (size : A → Result (List I64))
    (uncheckedOneTo : I64 → R) (a : A) : Result (List R) := do
  return (← size a).map uncheckedOneTo

/--
Julia source: base/abstractarray.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_offset_axes() = false
```
-/
def hasOffsetNone : Bool := false

/--
Julia source: base/abstractarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
```
-/
def hasOffset {A R I : Type} (axes : A → Result (List R))
    (first : R → Result I) (toInt : I → Result I64) (a : A) : Result Bool := do
  anyTupleM (fun x => do return (← toInt (← first x)).val != 1) false (← axes a)

/--
Julia source: base/abstractarray.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_offset_axes(A::AbstractVector) = Int(firstindex(A))::Int != 1 # improve performance of a common case (ranges)
```
-/
def hasOffsetVector {A I : Type} (firstindex : A → Result I)
    (toInt : I → Result I64) (a : A) : Result Bool := do
  return (← toInt (← firstindex a)).val != 1

/--
Julia source: base/abstractarray.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_offset_axes(::Colon) = false
```
-/
def hasOffsetColon : Bool := false

/--
Julia source: base/abstractarray.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_offset_axes(::Array) = false
```
-/
def hasOffsetArray {A : Type} (_a : A) : Bool := false

/--
Julia source: base/abstractarray.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_offset_axes(A, As...) = has_offset_axes(A) || has_offset_axes(As...)
```
-/
def hasOffsetMany {A Rest : Type} (hasOffset : A → Result Bool)
    (hasOffsetRest : Rest → Result Bool) (a : A) (as : Rest) : Result Bool := do
  if ← hasOffset a then return true else hasOffsetRest as

/--
Julia source: base/abstractarray.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
require_one_based_indexing(A...) = !has_offset_axes(A...) || throw(ArgumentError("offset arrays are not supported but got an array with index other than 1"))
```
-/
def requireOneBased {Args : Type} (hasOffset : Args → Result Bool)
    (as : Args) : Result Bool := do
  if !(← hasOffset as) then return true
  else throw (.julia (.argumentError "offset arrays are not supported but got an array with index other than 1"))

/--
Julia source: base/abstractarray.jl:140-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(A::AbstractArray{<:Any,0}) = OneTo(1)
```
-/
def axes1Zero {R : Type} (oneTo : I64 → R) : R := oneTo (int 1)

/--
Julia source: base/abstractarray.jl:141-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(A::AbstractArray) = (@inline; axes(A)[1])
```
-/
def axes1 {A R : Type} (axes : A → Result (List R)) (a : A) : Result R := do
  tupleGet (← axes a) (int 1)

/--
Julia source: base/abstractarray.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(iter) = oneto(length(iter))
```
-/
def axes1Iterator {A R : Type} (length : A → Result I64)
    (oneTo : I64 → Result R) (a : A) : Result R := do
  oneTo (← length a)

/--
Julia source: base/abstractarray.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(a::AbstractArray) = CartesianIndices(axes(a))
```
-/
def keysArray {A Ax K : Type} (axes : A → Result Ax)
    (cartesianIndices : Ax → Result K) (a : A) : Result K := do
  cartesianIndices (← axes a)

/--
Julia source: base/abstractarray.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(a::AbstractVector) = LinearIndices(a)
```
-/
def keysVector {A K : Type} (linearIndices : A → Result K) (a : A) : Result K :=
  linearIndices a

/--
Julia source: base/abstractarray.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(a::AbstractArray) = keytype(typeof(a))
```
-/
def keytypeValue {A : Type} {K : Sort u} (typeof : A → Type)
    (keytype : Type → K) (a : A) : K := keytype (typeof a)

/--
Julia source: base/abstractarray.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(::Type{Union{}}, slurp...) = eltype(Union{})
```
-/
def keytypeBottom {K : Sort u} (eltype : Type → K) (bottom : Type) : K :=
  eltype bottom

/--
Julia source: base/abstractarray.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(A::Type{<:AbstractArray}) = CartesianIndex{ndims(A)}
```
-/
def keytypeArray (ndims : Type → I64) (cartesianIndex : I64 → Type)
    (a : Type) : Type := cartesianIndex (ndims a)

/--
Julia source: base/abstractarray.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(A::Type{<:AbstractVector}) = Int
```
-/
def keytypeVector : Type := I64

/--
Julia source: base/abstractarray.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
valtype(a::AbstractArray) = valtype(typeof(a))
```
-/
def valtypeValue {A : Type} {K : Sort u} (typeof : A → Type)
    (valtype : Type → K) (a : A) : K := valtype (typeof a)

/--
Julia source: base/abstractarray.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
valtype(::Type{Union{}}, slurp...) = eltype(Union{})
```
-/
def valtypeBottom {K : Sort u} (eltype : Type → K) (bottom : Type) : K :=
  eltype bottom

/--
Julia source: base/abstractarray.jl:217-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
valtype(A::Type{<:AbstractArray}) = eltype(A)
```
-/
def valtypeArray (eltype : Type → Type) (a : Type) : Type := eltype a

/--
Julia source: base/abstractarray.jl:219-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prevind(::AbstractArray, i::Integer) = Int(i)-1
```
-/
def prevind {A D : Type} (toInt : D → Result I64) (_a : A) (i : D) : Result I64 := do
  return (← toInt i) - int 1

/--
Julia source: base/abstractarray.jl:220-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextind(::AbstractArray, i::Integer) = Int(i)+1
```
-/
def nextind {A D : Type} (toInt : D → Result I64) (_a : A) (i : D) : Result I64 := do
  return (← toInt i) + int 1

/--
Julia source: base/abstractarray.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type) = Any
```
-/
def eltypeDefault (anyType : Type) (_a : Type) : Type := anyType

/--
Julia source: base/abstractarray.jl:244-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Bottom}, slurp...) = throw(ArgumentError("Union{} does not have elements"))
```
-/
def eltypeBottom {α : Type} : Result α :=
  throw (.julia (.argumentError "Union{} does not have elements"))

/--
Julia source: base/abstractarray.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(x) = eltype(typeof(x))
```
-/
def eltypeValue {A : Type} (typeof : A → Type) (eltype : Type → Type)
    (a : A) : Type := eltype (typeof a)

/--
Julia source: base/abstractarray.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:AbstractArray{E}}) where {E} = @isdefined(E) ? E : Any
```
-/
def eltypeArray (anyType : Type) (elementType : Option Type) : Type :=
  match elementType with | some e => e | none => anyType

/--
Julia source: base/abstractarray.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
elsize(A::AbstractArray) = elsize(typeof(A))
```
-/
def elsize {A : Type} (typeof : A → Type) (elsize : Type → Result I64)
    (a : A) : Result I64 := elsize (typeof a)

/--
Julia source: base/abstractarray.jl:278-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(::AbstractArray{T,N}) where {T,N} = N::Int
```
-/
def ndimsValue {A : Type} (n : I64) (_a : A) : I64 := n

/--
Julia source: base/abstractarray.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(::Type{<:AbstractArray{<:Any,N}}) where {N} = N::Int
```
-/
def ndimsType (n : I64) (_a : Type) : I64 := n

/--
Julia source: base/abstractarray.jl:280-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(::Type{Union{}}, slurp...) = throw(ArgumentError("Union{} does not have elements"))
```
-/
def ndimsBottom {α : Type} : Result α :=
  throw (.julia (.argumentError "Union{} does not have elements"))

/--
Julia source: base/abstractarray.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(itrs...) = keys(itrs...)
```
-/
def eachindexIterators {Args K : Type} (keys : Args → Result K)
    (as : Args) : Result K := keys as

/--
Julia source: base/abstractarray.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(A::AbstractVector) = (@inline(); axes1(A))
```
-/
def eachindexVector {A R : Type} (axes1 : A → Result R) (a : A) : Result R := axes1 a

/--
Julia source: base/abstractarray.jl:329-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
```
-/
def joinCommaAndTwo (a b : String) : String := a ++ " and " ++ b

/--
Julia source: base/abstractarray.jl:330-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
```
-/
def joinCommaAndMany (joinRest : String → List String → String)
    (a b : String) (cs : List String) : String := a ++ ", " ++ joinRest b cs

/--
Julia source: base/abstractarray.jl:331-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function throw_eachindex_mismatch_indices(indices_str, indsA, indsBs...)
    throw(DimensionMismatch(
            LazyString("all inputs to eachindex must have the same ", indices_str, ", got ",
                _join_comma_and(indsA, indsBs...))))
end
```
-/
def throwEachindexMismatch {α : Type} (join : String → List String → String)
    (indices a : String) (bs : List String) : Result α :=
  throw (.dimensionMismatch ("all inputs to eachindex must have the same " ++ indices ++
    ", got " ++ join a bs))

/--
Julia source: base/abstractarray.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(A::AbstractArray) = (@inline(); eachindex(IndexStyle(A), A))
```
-/
def eachindexArray {A S K : Type} (indexStyle : A → Result S)
    (eachindex : S → A → Result K) (a : A) : Result K := do
  eachindex (← indexStyle a) a

/--
Julia source: base/abstractarray.jl:386-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eachindex(A::AbstractArray, B::AbstractArray)
    @inline
    eachindex(IndexStyle(A,B), A, B)
end
```
-/
def eachindexTwo {A B S K : Type} (indexStyle : A → B → Result S)
    (eachindex : S → A → B → Result K) (a : A) (b : B) : Result K := do
  eachindex (← indexStyle a b) a b

/--
Julia source: base/abstractarray.jl:390-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eachindex(A::AbstractArray, B::AbstractArray...)
    @inline
    eachindex(IndexStyle(A,B...), A, B...)
end
```
-/
def eachindexMany {A Rest S K : Type} (indexStyle : A → Rest → Result S)
    (eachindex : S → A → Rest → Result K) (a : A) (bs : Rest) : Result K := do
  eachindex (← indexStyle a bs) a bs

/--
Julia source: base/abstractarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(::IndexLinear, A::Union{Array, Memory}) = unchecked_oneto(length(A))
```
-/
def eachindexDense {m : Type → Type} [Monad m] {A R : Type}
    (length : A → m I64) (uncheckedOneTo : I64 → R) (a : A) : m R := do
  return uncheckedOneTo (← length a)

/--
Julia source: base/abstractarray.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(::IndexLinear, A::AbstractArray) = (@inline; oneto(length(A)))
```
-/
def eachindexLinear {A R : Type} (length : A → Result I64)
    (oneTo : I64 → Result R) (a : A) : Result R := do
  oneTo (← length a)

/--
Julia source: base/abstractarray.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(::IndexLinear, A::AbstractVector) = (@inline; axes1(A))
```
-/
def eachindexLinearVector {A R : Type} (axes1 : A → Result R) (a : A) : Result R := axes1 a

/--
Julia source: base/abstractarray.jl:397-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eachindex(::IndexLinear, A::AbstractArray, B::AbstractArray...)
    @inline
    indsA = eachindex(IndexLinear(), A)
    indsBs = map(X -> eachindex(IndexLinear(), X), B)
    all(==(indsA), indsBs) ||
        throw_eachindex_mismatch_indices("indices", indsA, indsBs...)
    indsA
end
```
-/
def eachindexLinearMany {A R : Type} {n : Nat} {B : Fin n → Type}
    (eachindexA : A → Result R) (eachindexB : (i : Fin n) → B i → Result R)
    (eq : R → R → Bool) (mismatch : R → List R → Result R)
    (a : A) (bs : (i : Fin n) → B i) : Result R := do
  let indsA ← eachindexA a
  let indsBs ← (List.finRange n).mapM (fun i => eachindexB i (bs i))
  if !(indsBs.all (eq indsA)) then return ← mismatch indsA indsBs
  return indsA

/--
Julia source: base/abstractarray.jl:407-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(s::IndexStyle, A::AbstractArray, B::AbstractArray...) = eachindex(s, A, B...)
```
-/
def keysStyle {S A Rest K : Type} (eachindex : S → A → Rest → Result K)
    (s : S) (a : A) (bs : Rest) : Result K := eachindex s a bs

/--
Julia source: base/abstractarray.jl:429-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(a::AbstractArray) = (@inline; last(eachindex(IndexLinear(), a)))
```
-/
def lastindexArray {A R I : Type} (eachindexLinear : A → Result R)
    (last : R → Result I) (a : A) : Result I := do last (← eachindexLinear a)

/--
Julia source: base/abstractarray.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(a, d) = (@inline; last(axes(a, d)))
```
-/
def lastindexDim {A D R I : Type} (axes : A → D → Result R)
    (last : R → Result I) (a : A) (d : D) : Result I := do last (← axes a d)

/--
Julia source: base/abstractarray.jl:452-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(a::AbstractArray) = (@inline; first(eachindex(IndexLinear(), a)))
```
-/
def firstindexArray {A R I : Type} (eachindexLinear : A → Result R)
    (first : R → Result I) (a : A) : Result I := do first (← eachindexLinear a)

/--
Julia source: base/abstractarray.jl:453-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(a, d) = (@inline; first(axes(a, d)))
```
-/
def firstindexDim {A D R I : Type} (axes : A → D → Result R)
    (first : R → Result I) (a : A) (d : D) : Result I := do first (← axes a d)

/--
Julia source: base/abstractarray.jl:455-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds first(a::AbstractArray) = a[first(eachindex(a))]
```
-/
def firstArray {A R I E : Type} (eachindex : A → Result R)
    (first : R → Result I) (getindex : A → I → Result E) (a : A) : Result E := do
  getindex a (← first (← eachindex a))

/--
Julia source: base/abstractarray.jl:474-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function first(itr)
    x = iterate(itr)
    x === nothing && throw(ArgumentError("collection must be non-empty"))
    x[1]
end
```
-/
def firstIterator {A E S : Type} (iterate : A → Result (Option (E × S)))
    (a : A) : Result E := do
  let x ← iterate a
  match x with
  | none => throw (.julia (.argumentError "collection must be non-empty"))
  | some x => return x.1

/--
Julia source: base/abstractarray.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(itr, n::Integer) = collect(Iterators.take(itr, n))
```
-/
def firstN {A D Taken Out : Type} (take : A → D → Result Taken)
    (collect : Taken → Result Out) (a : A) (n : D) : Result Out := do collect (← take a n)

/--
Julia source: base/abstractarray.jl:507-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function first(v::AbstractVector, n::Integer)
    n < 0 && throw(ArgumentError("Number of elements must be non-negative"))
    v[range(begin, length=min(n, checked_length(v)))]
end
```
-/
def firstVectorN {A B D I L R : Type} (negative : D → Bool)
    (firstindex : A → Result I) (checkedLength : A → Result I64)
    (minLength : D → I64 → Result L) (range : I → L → Result R)
    (getindex : A → R → Result B) (a : A) (n : D) : Result B := do
  if negative n then throw (.julia (.argumentError "Number of elements must be non-negative"))
  let start ← firstindex a
  let len ← minLength n (← checkedLength a)
  getindex a (← range start len)

/--
Julia source: base/abstractarray.jl:530-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(a) = a[end]
```
-/
def last {A I E : Type} (lastindex : A → Result I)
    (getindex : A → I → Result E) (a : A) : Result E := do getindex a (← lastindex a)

/--
Julia source: base/abstractarray.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(itr, n::Integer) = reverse!(collect(Iterators.take(Iterators.reverse(itr), n)))
```
-/
def lastN {A Rev D Taken Out : Type} (reverseIterator : A → Result Rev)
    (take : Rev → D → Result Taken) (collect : Taken → Result Out)
    (reverseBang : Out → Result Out) (a : A) (n : D) : Result Out := do
  reverseBang (← collect (← take (← reverseIterator a) n))

/--
Julia source: base/abstractarray.jl:557-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function last(v::AbstractVector, n::Integer)
    n < 0 && throw(ArgumentError("Number of elements must be non-negative"))
    v[range(stop=lastindex(v), length=min(n, checked_length(v)))]
end
```
-/
def lastVectorN {A B D I L R : Type} (negative : D → Bool)
    (lastindex : A → Result I) (checkedLength : A → Result I64)
    (minLength : D → I64 → Result L) (rangeStop : I → L → Result R)
    (getindex : A → R → Result B) (a : A) (n : D) : Result B := do
  if negative n then throw (.julia (.argumentError "Number of elements must be non-negative"))
  let stop ← lastindex a
  let len ← minLength n (← checkedLength a)
  getindex a (← rangeStop stop len)

/- UNTRANSLATED: Function declaration without a method body.
Julia source: base/abstractarray.jl:577-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function strides end
```
-/

/--
Julia source: base/abstractarray.jl:597-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function stride(A::AbstractArray, k::Integer)
    st = strides(A)
    k ≤ ndims(A) && return st[k]
    ndims(A) == 0 && return 1
    sz = size(A)
    s = st[1] * sz[1]
    for i in 2:ndims(A)
        s += st[i] * sz[i]
    end
    return s
end
```
-/
def stride {A D : Type} (strides : A → Result (List I64))
    (ndims : A → Result I64) (le : D → I64 → Bool)
    (getStride : List I64 → D → Result I64) (size : A → Result (List I64))
    (a : A) (k : D) : Result I64 := do
  let st ← strides a
  if le k (← ndims a) then return ← getStride st k
  if (← ndims a).val == 0 then return int 1
  let sz ← size a
  let mut s := (← tupleGet st (int 1)) * (← tupleGet sz (int 1))
  let n ← ndims a
  for i in List.range (n.val - 1).toNat do
    let j := int ((i : Int) + 2)
    s := s + (← tupleGet st j) * (← tupleGet sz j)
  return s

/--
Julia source: base/abstractarray.jl:609-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline size_to_strides(s, d, sz...) = (s, size_to_strides(s * d, sz...)...)
```
-/
def sizeToStrides {S D Product Tail Rest : Type} (mul : S → D → Product)
    (recurse : Product → Tail → Rest) (s : S) (d : D) (sz : Tail) : S × Rest :=
  (s, recurse (mul s d) sz)

/--
Julia source: base/abstractarray.jl:610-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size_to_strides(s, d) = (s,)
```
-/
def sizeToStridesLast {S D : Type} (s : S) (_d : D) : List S := [s]

/--
Julia source: base/abstractarray.jl:611-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size_to_strides(s) = ()
```
-/
def sizeToStridesEmpty {S : Type} (_s : S) : List S := []

/--
Julia source: base/abstractarray.jl:613-616 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isstored(A::AbstractArray{<:Any,N}, I::Vararg{Integer,N}) where {N}
    @boundscheck checkbounds(A, I...)
    return true
end
```
-/
def isstored {m : Type → Type} [Monad m] {A I : Type}
    (checkbounds : A → List I → m Unit) (a : A) (is : List I) : m Bool := do
  checkbounds a is
  return true

/--
Julia source: base/abstractarray.jl:619-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function trailingsize(A, n)
    s = 1
    for i=n:ndims(A)
        s *= size(A,i)
    end
    return s
end
```
-/
def trailingSize {A D : Type} (indices : D → I64 → List D)
    (ndims : A → Result I64) (size : A → D → Result I64) (a : A) (n : D) : Result I64 := do
  let mut s := int 1
  for i in indices n (← ndims a) do s := s * (← size a i)
  return s

/--
Julia source: base/abstractarray.jl:626-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function trailingsize(inds::Indices, n)
    s = 1
    for i=n:length(inds)
        s *= length(inds[i])
    end
    return s
end
```
-/
def trailingSizeIndices {R D : Type} (indices : D → I64 → List D)
    (lengthTuple : List R → I64) (get : List R → D → Result R)
    (length : R → Result I64) (inds : List R) (n : D) : Result I64 := do
  let mut s := int 1
  for i in indices n (lengthTuple inds) do s := s * (← length (← get inds i))
  return s

/--
Julia source: base/abstractarray.jl:634-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function trailingsize(inds::Indices)
    @inline
    prod(map(length, inds))
end
```
-/
def trailingSizeAll {R : Type} (length : R → Result I64)
    (prod : List I64 → Result I64) (inds : List R) : Result I64 := do
  prod (← inds.mapM length)

/--
Julia source: base/abstractarray.jl:682-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(::Type{Bool}, A::AbstractArray, I...)
    @inline
    checkbounds_indices(Bool, axes(A), I)
end
```
-/
def checkboundsMany {A Ax I : Type} (axes : A → Result Ax)
    (checkboundsIndices : Ax → List I → Result Bool) (a : A) (is : List I) : Result Bool := do
  checkboundsIndices (← axes a) is

/--
Julia source: base/abstractarray.jl:690-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(::Type{Bool}, A::AbstractArray, i)
    @inline
    return checkindex(Bool, eachindex(IndexLinear(), A), i)
end
```
-/
def checkboundsOne {A R I : Type} (eachindexLinear : A → Result R)
    (checkindex : R → I → Result Bool) (a : A) (i : I) : Result Bool := do
  checkindex (← eachindexLinear a) i

/--
Julia source: base/abstractarray.jl:722-726 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
    @inline
    return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
        checkbounds_indices(Bool, safe_tail(inds), tail(I))
end
```
-/
def checkboundsIndicesCons {R I : Type} (oneToOne : R)
    (checkindex : R → I → Result Bool)
    (recurse : List R → List I → Result Bool)
    (inds : List R) (i : I) (is : List I) : Result Bool := do
  if ← checkindex (inds.headD oneToOne) i then recurse inds.tail is else return false

/--
Julia source: base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
```
-/
def checkboundsIndicesNil {R : Type} (length : R → Result I64)
    (inds : List R) : Result Bool := allTupleM (fun x => do return (← length x).val == 1) inds

/--
Julia source: base/abstractarray.jl:750-750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds, i) = throw(ArgumentError(LazyString("unable to check bounds for indices of type ", typeof(i))))
```
-/
def checkindexUnsupported {R I : Type} (typeName : I → String)
    (_inds : R) (i : I) : Result Bool :=
  throw (.julia (.argumentError ("unable to check bounds for indices of type " ++ typeName i)))

/--
Julia source: base/abstractarray.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, i::Real) = (first(inds) <= i) & (i <= last(inds))
```
-/
def checkindexReal {R L I : Type} (first last : R → Result L)
    (leLower : L → I → Result Bool) (leUpper : I → L → Result Bool)
    (inds : R) (i : I) : Result Bool := do
  let lo ← leLower (← first inds) i
  let hi ← leUpper i (← last inds)
  return lo && hi

/--
Julia source: base/abstractarray.jl:752-752 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::IdentityUnitRange, i::Real) = checkindex(Bool, inds.indices, i)
```
-/
def checkindexIdentity {R W I : Type} (checkindex : R → I → Result Bool)
    (indices : W → R) (inds : W) (i : I) : Result Bool := checkindex (indices inds) i

/--
Julia source: base/abstractarray.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger} = unsigned(i -% one(i)) < unsigned(last(inds))
```
-/
def checkindexOneTo {t : IntTy} (last : JInt t) (i : JInt t) : Bool :=
  decide ((JInt.rem t.toUnsigned (i - JInt.lit t 1)).val <
    (JInt.rem t.toUnsigned last).val)

/--
Julia source: base/abstractarray.jl:754-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Colon) = true
```
-/
def checkindexColon {R : Type} (_inds : R) : Bool := true

/--
Julia source: base/abstractarray.jl:755-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Slice) = true
```
-/
def checkindexSlice {R S : Type} (_inds : R) (_slice : S) : Bool := true

/--
Julia source: base/abstractarray.jl:756-757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, i::AbstractRange) =
    isempty(i) | (checkindex(Bool, inds, first(i)) & checkindex(Bool, inds, last(i)))
```
-/
def checkindexRange {R Range I : Type} (isempty : Range → Result Bool)
    (first last : Range → Result I) (checkindex : R → I → Result Bool)
    (inds : R) (i : Range) : Result Bool := do
  let empty ← isempty i
  let lo ← checkindex inds (← first i)
  let hi ← checkindex inds (← last i)
  return empty || (lo && hi)

/--
Julia source: base/abstractarray.jl:759-760 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, i::LinearIndices) =
    isempty(i) | (checkindex(Bool, inds, first(i)) & checkindex(Bool, inds, last(i)))
```
-/
def checkindexLinearIndices {R Range I : Type} (isempty : Range → Result Bool)
    (first last : Range → Result I) (checkindex : R → I → Result Bool)
    (inds : R) (i : Range) : Result Bool := do
  let empty ← isempty i
  let lo ← checkindex inds (← first i)
  let hi ← checkindex inds (← last i)
  return empty || (lo && hi)

/--
Julia source: base/abstractarray.jl:762-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkindex(::Type{Bool}, inds, I::AbstractArray)
    @inline
    b = true
    for i in I
        b &= checkindex(Bool, inds, i)
    end
    b
end
```
-/
def checkindexArray {R A I : Type} [ForIn Result A I]
    (checkindex : R → I → Result Bool) (inds : R) (is : A) : Result Bool := do
  let mut b := true
  for i in is do
    let c ← checkindex inds i
    b := b && c
  return b

/--
Julia source: base/abstractarray.jl:819-819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::AbstractArray{T}) where {T}                             = similar(a, T)
```
-/
def similarDefault {m : Type → Type} [Monad m] {A B : Type}
    (similar : A → Type → m B) (elementType : Type) (a : A) : m B := similar a elementType

/--
Julia source: base/abstractarray.jl:820-820 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::AbstractArray, ::Type{T}) where {T}                     = similar(a, T, axes(a))
```
-/
def similarType {m : Type → Type} [Monad m] {A Ax B : Type}
    (axes : A → m Ax) (similar : A → Type → Ax → m B) (a : A) (t : Type) : m B := do
  similar a t (← axes a)

/--
Julia source: base/abstractarray.jl:821-821 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::AbstractArray{T}, dims::Tuple) where {T}                = similar(a, T, dims)
```
-/
def similarDims {m : Type → Type} [Monad m] {A D B : Type}
    (similar : A → Type → D → m B) (elementType : Type) (a : A) (dims : D) : m B :=
  similar a elementType dims

/--
Julia source: base/abstractarray.jl:822-822 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::AbstractArray{T}, dims::DimOrInd...) where {T}          = similar(a, T, dims)
```
-/
def similarVarargs {m : Type → Type} [Monad m] {A D B : Type}
    (similar : A → Type → D → m B) (elementType : Type) (a : A) (dims : D) : m B :=
  similar a elementType dims

/--
Julia source: base/abstractarray.jl:823-823 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::AbstractArray, ::Type{T}, dims::DimOrInd...) where {T}  = similar(a, T, dims)
```
-/
def similarTypeVarargs {m : Type → Type} [Monad m]
    {A D B : Type} {Ty : Type u} (similar : A → Ty → D → m B)
    (a : A) (t : Ty) (dims : D) : m B := similar a t dims

/--
Julia source: base/abstractarray.jl:829-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::AbstractArray, ::Type{T}, dims::Tuple{Union{Integer, AbstractOneTo}, Vararg{Union{Integer, AbstractOneTo}}}) where {T} = similar(a, T, to_shape(dims))
```
-/
def similarOneTo {m : Type → Type} [Monad m] {A D Shape B : Type}
    (toShape : D → m Shape) (similar : A → Type → Shape → m B)
    (a : A) (t : Type) (dims : D) : m B := do
  similar a t (← toShape dims)

/--
Julia source: base/abstractarray.jl:832-832 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::AbstractArray, ::Type{T}, dims::Tuple{Union{Integer, OneTo}, Vararg{Union{Integer, OneTo}}}) where {T} = similar(a, T, to_shape(dims))
```
-/
def similarLegacyOneTo {m : Type → Type} [Monad m] {A D Shape B : Type}
    (toShape : D → m Shape) (similar : A → Type → Shape → m B)
    (a : A) (t : Type) (dims : D) : m B := do
  similar a t (← toShape dims)

/--
Julia source: base/abstractarray.jl:834-834 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::AbstractArray, ::Type{T}, dims::Dims{N}) where {T,N}    = Array{T,N}(undef, dims)
```
-/
def similarFallback {m : Type → Type} [Monad m] {A B : Type} {Ty : Type u}
    (arrayUndef : Ty → List I64 → m B) (_a : A) (t : Ty) (dims : List I64) : m B :=
  arrayUndef t dims

/--
Julia source: base/abstractarray.jl:836-836 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_shape(::Tuple{}) = ()
```
-/
def toShapeEmpty : List I64 := []

/--
Julia source: base/abstractarray.jl:837-837 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_shape(dims::Dims) = dims
```
-/
def toShapeDims (dims : List I64) : List I64 := dims

/--
Julia source: base/abstractarray.jl:838-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_shape(dims::DimsOrInds) = map(to_shape, dims)::DimsOrInds
```
-/
def toShapeMixed {m : Type → Type} [Monad m] {D Shape : Type}
    (toShape : D → m Shape) (dims : List D) : m (List Shape) := dims.mapM toShape

/--
Julia source: base/abstractarray.jl:840-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_shape(i::Int) = i
```
-/
def toShapeInt (i : I64) : I64 := i

/--
Julia source: base/abstractarray.jl:841-841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_shape(i::Integer) = Int(i)
```
-/
def toShapeInteger {m : Type → Type} [Monad m] {I : Type}
    (toInt : I → m I64) (i : I) : m I64 := toInt i

/--
Julia source: base/abstractarray.jl:842-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_shape(r::AbstractOneTo) = _to_shape(last(r))
```
-/
def toShapeOneTo {m : Type → Type} [Monad m] {R I Shape : Type}
    (last : R → m I) (toShape : I → m Shape) (r : R) : m Shape := do toShape (← last r)

/--
Julia source: base/abstractarray.jl:843-843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_shape(x::Integer) = to_shape(x)
```
-/
def toShapeIntegerHelper {m : Type → Type} [Monad m] {I Shape : Type}
    (toShape : I → m Shape) (x : I) : m Shape := toShape x

/--
Julia source: base/abstractarray.jl:844-844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_shape(x) = Int(x)
```
-/
def toShapeOtherHelper {m : Type → Type} [Monad m] {I : Type}
    (toInt : I → m I64) (x : I) : m I64 := toInt x

/--
Julia source: base/abstractarray.jl:845-845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_shape(r::AbstractUnitRange) = r
```
-/
def toShapeUnitRange {R : Type} (r : R) : R := r

/--
Julia source: base/abstractarray.jl:869-869 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{T}, dims::DimOrInd...) where {T<:AbstractArray} = similar(T, dims)
```
-/
def similarStorageVarargs {m : Type → Type} [Monad m] {D B : Type}
    (similar : Type → D → m B) (t : Type) (dims : D) : m B := similar t dims

/--
Julia source: base/abstractarray.jl:870-870 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{T}, shape::Tuple{Union{Integer, AbstractOneTo}, Vararg{Union{Integer, AbstractOneTo}}}) where {T<:AbstractArray} = similar(T, to_shape(shape))
```
-/
def similarStorageOneTo {m : Type → Type} [Monad m] {D Shape B : Type}
    (toShape : D → m Shape) (similar : Type → Shape → m B)
    (t : Type) (shape : D) : m B := do
  similar t (← toShape shape)

/--
Julia source: base/abstractarray.jl:872-872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{T}, shape::Tuple{Union{Integer, OneTo}, Vararg{Union{Integer, OneTo}}}) where {T<:AbstractArray} = similar(T, to_shape(shape))
```
-/
def similarStorageLegacyOneTo {m : Type → Type} [Monad m] {D Shape B : Type}
    (toShape : D → m Shape) (similar : Type → Shape → m B)
    (t : Type) (shape : D) : m B := do
  similar t (← toShape shape)

/--
Julia source: base/abstractarray.jl:873-873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{T}, dims::Dims) where {T<:AbstractArray} = T(undef, dims)
```
-/
def similarStorageDims {m : Type → Type} [Monad m] {B : Type}
    (constructUndef : Type → List I64 → m B)
    (t : Type) (dims : List I64) : m B := constructUndef t dims

/--
Julia source: base/abstractarray.jl:892-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(a::AbstractVector{T}, ::Type{U}=T) where {T,U} = similar(a, U, 0)
```
-/
def emptyVector {m : Type → Type} [Monad m] {A B : Type}
    (similar : A → Type → I64 → m B) (a : A) (t : Type) : m B := similar a t (int 0)

/--
Julia source: base/abstractarray.jl:895-895 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
emptymutable(a::AbstractVector{T}, ::Type{U}=T) where {T,U} = Vector{U}()
```
-/
def emptyMutableVector {m : Type → Type} [Monad m] {A B : Type}
    (vectorEmpty : Type → m B) (_a : A) (t : Type) : m B := vectorEmpty t

/--
Julia source: base/abstractarray.jl:896-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
emptymutable(itr, ::Type{U}) where {U} = Vector{U}()
```
-/
def emptyMutableIterator {m : Type → Type} [Monad m] {A B : Type}
    (vectorEmpty : Type → m B) (_a : A) (t : Type) : m B := vectorEmpty t

/--
Julia source: base/abstractarray.jl:920-927 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy!(dst::AbstractVector, src::AbstractVector)
    firstindex(dst) == firstindex(src) || throw(ArgumentError(
        "vectors must have the same offset for copy! (consider using `copyto!`)"))
    if length(dst) != length(src)
        resize!(dst, length(src))
    end
    copyto!(dst, src)
end
```
-/
def copyBangVector {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S I : Type} (firstDest : D → m I) (firstSrc : S → m I)
    (eq : I → I → Bool) (lengthDest : D → m I64) (lengthSrc : S → m I64)
    (resize : D → I64 → m Unit) (copyto : D → S → m D) (dst : D) (src : S) : m D := do
  if !(eq (← firstDest dst) (← firstSrc src)) then
    throw (.julia (.argumentError
      "vectors must have the same offset for copy! (consider using `copyto!`)"))
  if (← lengthDest dst) != (← lengthSrc src) then resize dst (← lengthSrc src)
  copyto dst src

/--
Julia source: base/abstractarray.jl:929-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy!(dst::AbstractArray, src::AbstractArray)
    axes(dst) == axes(src) || throw(ArgumentError(
        "arrays must have the same axes for copy! (consider using `copyto!`)"))
    copyto!(dst, src)
end
```
-/
def copyBangArray {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S Ax : Type} (axesDest : D → m Ax) (axesSrc : S → m Ax)
    (eq : Ax → Ax → Bool) (copyto : D → S → m D) (dst : D) (src : S) : m D := do
  if !(eq (← axesDest dst) (← axesSrc src)) then
    throw (.julia (.argumentError
      "arrays must have the same axes for copy! (consider using `copyto!`)"))
  copyto dst src

/- UNTRANSLATED: Function declaration without a method body.
Julia source: base/abstractarray.jl:939-939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typeof(function copyto! end).name.max_methods = UInt8(1)
```
-/

/--
Julia source: base/abstractarray.jl:941-951 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::AbstractArray, src)
    destiter = eachindex(dest)
    y = iterate(destiter)
    for x in src
        y === nothing &&
            throw(ArgumentError("destination has fewer elements than required"))
        dest[y[1]] = x
        y = iterate(destiter, y[2])
    end
    return dest
end
```
-/
def copytoIterable {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D Src E Inds I St : Type} [ForIn m Src E]
    (eachindex : D → m Inds) (start : Inds → m (Option (I × St)))
    (next : Inds → St → m (Option (I × St)))
    (setindex : D → I → E → m Unit) (dest : D) (src : Src) : m D := do
  let destiter ← eachindex dest
  let mut y ← start destiter
  for x in src do
    match y with
    | none => throw (.julia (.argumentError "destination has fewer elements than required"))
    | some (i, st) =>
      setindex dest i x
      y ← next destiter st
  return dest

/--
Julia source: base/abstractarray.jl:953-971 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::AbstractArray, dstart::Integer, src)
    i = Int(dstart)
    if haslength(src) && length(dest) > 0
        n = length(src)
        n == 0 && return dest
        @boundscheck checkbounds(dest, i)
        @boundscheck n <= lastindex(dest) - i + 1 || throw(BoundsError(dest, i))
        for x in src
            @inbounds dest[i] = x
            i += 1
        end
    else
        for x in src
            dest[i] = x
            i += 1
        end
    end
    return dest
end
```
-/
def copytoIterableAt {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D Src E Start End Difference Span : Type} [ForIn m Src E]
    (toInt : Start → m I64) (haslength : Src → m Bool)
    (lengthDest : D → m I64) (lengthSrc : Src → m I64)
    (lastindex : D → m End) (checkbounds : D → I64 → m Unit)
    (sub : End → I64 → m Difference) (addOne : Difference → m Span)
    (le : I64 → Span → m Bool)
    (setindex : Bool → D → I64 → E → m Unit)
    (dest : D) (dstart : Start) (src : Src) : m D := do
  let mut i ← toInt dstart
  let hasLen ← haslength src
  let sized ← if hasLen then do
      let n ← lengthDest dest
      pure (decide (n.val > 0))
    else pure false
  if sized then
    let n ← lengthSrc src
    if n.val == 0 then return dest
    checkbounds dest i
    if !(← le n (← addOne (← sub (← lastindex dest) i))) then
      throw (.julia .boundsError)
    for x in src do
      setindex true dest i x
      i := i + int 1
  else
    for x in src do
      setindex false dest i x
      i := i + int 1
  return dest

/--
Julia source: base/abstractarray.jl:974-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::AbstractArray, dstart::Integer, src, sstart::Integer)
    if (sstart < 1)
        throw(ArgumentError(LazyString("source start offset (",sstart,") is < 1")))
    end
    y = iterate(src)
    for j = 1:(sstart-1)
        if y === nothing
            throw(ArgumentError(LazyString(
                "source has fewer elements than required, ",
                "expected at least ", sstart,", got ", j-1)))
        end
        y = iterate(src, y[2])
    end
    if y === nothing
        throw(ArgumentError(LazyString(
            "source has fewer elements than required, ",
            "expected at least ",sstart," got ", sstart-1)))
    end
    i = Int(dstart)
    while y !== nothing
        val, st = y
        dest[i] = val
        i += 1
        y = iterate(src, st)
    end
    return dest
end
```
-/
def copytoIterableFrom {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D Src E Start Offset PrefixOffset Prefix J St : Type} [ForIn m Prefix J]
    (lessOne : Offset → Bool) (subOne : Offset → PrefixOffset)
    (oneTo : PrefixOffset → m Prefix) (start : Src → m (Option (E × St)))
    (next : Src → St → m (Option (E × St))) (toInt : Start → m I64)
    (setindex : D → I64 → E → m Unit)
    (whileLoop : {β : Type} → β → (β → m (ForInStep β)) → m β)
    (dest : D) (dstart : Start) (src : Src) (sstart : Offset) : m D := do
  if lessOne sstart then
    throw (.julia (.argumentError "source start offset is < 1"))
  let mut y ← start src
  for _j in (← oneTo (subOne sstart)) do
    match y with
    | none => throw (.julia (.argumentError "source has fewer elements than required"))
    | some (_, st) => y ← next src st
  if y.isNone then
    throw (.julia (.argumentError "source has fewer elements than required"))
  let i ← toInt dstart
  let _ ← whileLoop (i, y) fun (i, y) => do
    match y with
    | none => return .done (i, y)
    | some (val, st) =>
      setindex dest i val
      let i := i + int 1
      let y ← next src st
      return .yield (i, y)
  return dest

/--
Julia source: base/abstractarray.jl:1003-1037 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::AbstractArray, dstart::Integer, src, sstart::Integer, n::Integer)
    n < 0 && throw(ArgumentError(LazyString("tried to copy n=",n,
        ", elements, but n should be non-negative")))
    n == 0 && return dest
    inds = LinearIndices(dest)
    sstart < 1 && throw(ArgumentError(LazyString("source start offset (",
        sstart,") is < 1")))
    (dstart ∈ inds && n <= last(inds) - dstart + 1) || throw(BoundsError(dest, dstart))
    dstart = Int(dstart)
    n = Int(n)
    dmax = dstart + n - 1
    y = iterate(src)
    for j = 1:(sstart-1)
        if y === nothing
            throw(ArgumentError(LazyString(
                "source has fewer elements than required, ",
                "expected at least ",sstart,", got ",j-1)))
        end
        y = iterate(src, y[2])
    end
    if y === nothing
        throw(ArgumentError(LazyString(
            "source has fewer elements than required, ",
            "expected at least ",sstart," got ", sstart-1)))
    end
    val, st = y
    i = dstart
    @inbounds dest[i] = val
    for val in Iterators.take(Iterators.rest(src, st), n-1)
        i += 1
        @inbounds dest[i] = val
    end
    i < dmax && throw(BoundsError(dest, i))
    return dest
end
```
-/
def copytoIterableN {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D Src E Start Offset PrefixOffset Count Inds End Difference Span Prefix J St Rest Taken : Type}
    [ForIn m Prefix J] [ForIn m Taken E]
    (negative : Count → Bool) (isZero : Count → Bool)
    (linearIndices : D → m Inds) (lessOne : Offset → Bool)
    (contains : Inds → Start → m Bool) (last : Inds → m End)
    (sub : End → Start → m Difference) (addOne : Difference → m Span)
    (le : Count → Span → m Bool)
    (toIntStart : Start → m I64) (toIntCount : Count → m I64)
    (start : Src → m (Option (E × St))) (subOne : Offset → PrefixOffset)
    (oneTo : PrefixOffset → m Prefix) (next : Src → St → m (Option (E × St)))
    (rest : Src → St → m Rest) (take : Rest → I64 → m Taken)
    (setindex : D → I64 → E → m Unit)
    (dest : D) (dstart : Start) (src : Src) (sstart : Offset) (n : Count) : m D := do
  if negative n then throw (.julia (.argumentError "n should be non-negative"))
  if isZero n then return dest
  let inds ← linearIndices dest
  if lessOne sstart then throw (.julia (.argumentError "source start offset is < 1"))
  if !(← contains inds dstart) then throw (.julia .boundsError)
  if !(← le n (← addOne (← sub (← last inds) dstart))) then throw (.julia .boundsError)
  let dstart ← toIntStart dstart
  let n ← toIntCount n
  let dmax := dstart + n - int 1
  let mut y ← start src
  for _j in (← oneTo (subOne sstart)) do
    match y with
    | none => throw (.julia (.argumentError "source has fewer elements than required"))
    | some (_, st) => y ← next src st
  match y with
  | none => throw (.julia (.argumentError "source has fewer elements than required"))
  | some (val, st) =>
    let mut i := dstart
    setindex dest i val
    for val in (← take (← rest src st) (n - int 1)) do
      i := i + int 1
      setindex dest i val
    if i.val < dmax.val then throw (.julia .boundsError)
    return dest

/--
Julia source: base/abstractarray.jl:1072-1080 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::AbstractArray, src::AbstractArray)
    isempty(src) && return dest
    if dest isa BitArray
        # avoid ambiguities with other copyto!(::AbstractArray, ::SourceArray) methods
        return _copyto_bitarray!(dest, src)
    end
    src′ = unalias(dest, src)
    copyto_unaliased!(IndexStyle(dest), dest, IndexStyle(src′), src′)
end
```
-/
def copytoArray {m : Type → Type} [Monad m] {D S Style : Type}
    (isempty : S → m Bool) (isBitArray : D → Bool) (copyBitArray : D → S → m D)
    (unalias : D → S → m S) (destStyle : D → m Style) (srcStyle : S → m Style)
    (copyUnaliased : Style → D → Style → S → m D) (dest : D) (src : S) : m D := do
  if ← isempty src then return dest
  if isBitArray dest then return ← copyBitArray dest src
  let src' ← unalias dest src
  copyUnaliased (← destStyle dest) dest (← srcStyle src') src'

/--
Julia source: base/abstractarray.jl:1082-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(deststyle::IndexStyle, dest::AbstractArray, srcstyle::IndexStyle, src::AbstractArray)
    isempty(src) && return dest
    src′ = unalias(dest, src)
    copyto_unaliased!(deststyle, dest, srcstyle, src′)
end
```
-/
def copytoStyles {m : Type → Type} [Monad m] {D S Style : Type}
    (isempty : S → m Bool) (unalias : D → S → m S)
    (copyUnaliased : Style → D → Style → S → m D)
    (deststyle : Style) (dest : D) (srcstyle : Style) (src : S) : m D := do
  if ← isempty src then return dest
  let src' ← unalias dest src
  copyUnaliased deststyle dest srcstyle src'

/--
Julia source: base/abstractarray.jl:1088-1123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto_unaliased!(deststyle::IndexStyle, dest::AbstractArray, srcstyle::IndexStyle, src::AbstractArray)
    isempty(src) && return dest
    destinds, srcinds = LinearIndices(dest), LinearIndices(src)
    idf, isf = first(destinds), first(srcinds)
    Δi = idf - isf
    (checkbounds(Bool, destinds, isf+Δi) & checkbounds(Bool, destinds, last(srcinds)+Δi)) ||
        throw(BoundsError(dest, srcinds))
    if deststyle isa IndexLinear
        if srcstyle isa IndexLinear
            # Single-index implementation
            @inbounds for i in srcinds
                dest[i + Δi] = src[i]
            end
        else
            # Dual-index implementation
            i = idf - 1
            @inbounds for a in src
                dest[i+=1] = a
            end
        end
    else
        iterdest, itersrc = eachindex(dest), eachindex(src)
        if iterdest == itersrc
            # Shared-iterator implementation
            for I in iterdest
                @inbounds dest[I] = src[I]
            end
        else
            # Dual-iterator implementation
            for (Idest, Isrc) in zip(iterdest, itersrc)
                @inbounds dest[Idest] = src[Isrc]
            end
        end
    end
    return dest
end
```
-/
def copytoUnaliased {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S Style LinD LinS ID IS Delta Counter E IndsD IndsS DI SI Zipped : Type}
    [ForIn m LinS IS] [ForIn m S E] [ForIn m IndsD DI] [ForIn m Zipped (DI × SI)]
    (isempty : S → m Bool) (linearDest : D → m LinD) (linearSrc : S → m LinS)
    (firstDest : LinD → m ID) (firstSrc lastSrc : LinS → m IS)
    (sub : ID → IS → m Delta) (add : IS → Delta → m ID)
    (checkbounds : LinD → ID → m Bool)
    (isLinear : Style → Bool) (getLinear : S → IS → m E)
    (setLinear : D → ID → E → m Unit)
    (subOne : ID → m Counter) (increment : Counter → m Counter)
    (setCounter : D → Counter → E → m Unit)
    (eachDest : D → m IndsD) (eachSrc : S → m IndsS)
    (eqIndices : IndsD → IndsS → Bool) (zipIndices : IndsD → IndsS → m Zipped)
    (getShared : S → DI → m E) (getindex : S → SI → m E)
    (setindex : D → DI → E → m Unit)
    (deststyle : Style) (dest : D) (srcstyle : Style) (src : S) : m D := do
  if ← isempty src then return dest
  let destinds ← linearDest dest
  let srcinds ← linearSrc src
  let idf ← firstDest destinds
  let isf ← firstSrc srcinds
  let delta ← sub idf isf
  let left ← checkbounds destinds (← add isf delta)
  let right ← checkbounds destinds (← add (← lastSrc srcinds) delta)
  if !(left && right) then throw (.julia .boundsError)
  if isLinear deststyle then
    if isLinear srcstyle then
      for i in srcinds do
        let a ← getLinear src i
        setLinear dest (← add i delta) a
    else
      let mut i ← subOne idf
      for a in src do
        i ← increment i
        setCounter dest i a
  else
    let iterdest ← eachDest dest
    let itersrc ← eachSrc src
    if eqIndices iterdest itersrc then
      for i in iterdest do setindex dest i (← getShared src i)
    else
      for (idest, isrc) in (← zipIndices iterdest itersrc) do
        setindex dest idest (← getindex src isrc)
  return dest

/--
Julia source: base/abstractarray.jl:1125-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray)
    copyto!(dest, dstart, src, first(LinearIndices(src)), length(src))
end
```
-/
def copytoArrayAt {m : Type → Type} [Monad m] {D S Start Lin Index : Type}
    (linearIndices : S → m Lin) (first : Lin → m Index) (length : S → m I64)
    (copyto : D → Start → S → Index → I64 → m D)
    (dest : D) (dstart : Start) (src : S) : m D := do
  copyto dest dstart src (← first (← linearIndices src)) (← length src)

/--
Julia source: base/abstractarray.jl:1129-1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray, sstart::Integer)
    srcinds = LinearIndices(src)
    checkbounds(Bool, srcinds, sstart) || throw(BoundsError(src, sstart))
    copyto!(dest, dstart, src, sstart, last(srcinds)-sstart+1)
end
```
-/
def copytoArrayFrom {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S Start Offset Count Lin End Difference : Type}
    (linearIndices : S → m Lin) (checkbounds : Lin → Offset → m Bool)
    (last : Lin → m End) (sub : End → Offset → m Difference) (addOne : Difference → m Count)
    (copyto : D → Start → S → Offset → Count → m D)
    (dest : D) (dstart : Start) (src : S) (sstart : Offset) : m D := do
  let srcinds ← linearIndices src
  if !(← checkbounds srcinds sstart) then throw (.julia .boundsError)
  copyto dest dstart src sstart (← addOne (← sub (← last srcinds) sstart))

/--
Julia source: base/abstractarray.jl:1135-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::AbstractArray, dstart::Integer,
                 src::AbstractArray, sstart::Integer,
                 n::Integer)
    n == 0 && return dest
    n < 0 && throw(ArgumentError(LazyString("tried to copy n=",
        n," elements, but n should be non-negative")))
    destinds, srcinds = LinearIndices(dest), LinearIndices(src)
    (checkbounds(Bool, destinds, dstart) && n <= last(destinds) - dstart + 1) || throw(BoundsError(dest, dstart))
    (checkbounds(Bool, srcinds, sstart)  && n <= last(srcinds) - sstart + 1)  || throw(BoundsError(src, sstart))
    dstart = Int(dstart)
    sstart = Int(sstart)
    n = Int(n)
    src′ = unalias(dest, src)
    @inbounds for i = 0:n-1
        dest[dstart+i] = src′[sstart+i]
    end
    return dest
end
```
-/
def copytoArrayN {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S E Start Offset Count Lin End DiffD DiffS SpanD SpanS : Type}
    (isZero : Count → Bool) (negative : Count → Bool)
    (linearDest : D → m Lin) (linearSrc : S → m Lin)
    (checkDest : Lin → Start → m Bool) (checkSrc : Lin → Offset → m Bool)
    (last : Lin → m End) (subDest : End → Start → m DiffD) (addOneDest : DiffD → m SpanD)
    (leDest : Count → SpanD → m Bool)
    (subSrc : End → Offset → m DiffS) (addOneSrc : DiffS → m SpanS)
    (leSrc : Count → SpanS → m Bool)
    (toIntDest : Start → m I64) (toIntSrc : Offset → m I64) (toIntCount : Count → m I64)
    (unalias : D → S → m S) (getindex : S → I64 → m E)
    (setindex : D → I64 → E → m Unit)
    (dest : D) (dstart : Start) (src : S) (sstart : Offset) (n : Count) : m D := do
  if isZero n then return dest
  if negative n then throw (.julia (.argumentError "n should be non-negative"))
  let destinds ← linearDest dest
  let srcinds ← linearSrc src
  if !(← checkDest destinds dstart) then throw (.julia .boundsError)
  if !(← leDest n (← addOneDest (← subDest (← last destinds) dstart))) then
    throw (.julia .boundsError)
  if !(← checkSrc srcinds sstart) then throw (.julia .boundsError)
  if !(← leSrc n (← addOneSrc (← subSrc (← last srcinds) sstart))) then
    throw (.julia .boundsError)
  let dstart ← toIntDest dstart
  let sstart ← toIntSrc sstart
  let n ← toIntCount n
  let src' ← unalias dest src
  for j in List.range ((n - int 1).val + 1).toNat do
    let i := int j
    setindex dest (dstart + i) (← getindex src' (sstart + i))
  return dest

/--
Julia source: base/abstractarray.jl:1154-1157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy(a::AbstractArray)
    @_propagate_inbounds_meta
    copymutable(a)
end
```
-/
def copyArray {m : Type → Type} [Monad m] {A B : Type}
    (copymutable : A → m B) (a : A) : m B := copymutable a

/--
Julia source: base/abstractarray.jl:1159-1182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(B::AbstractVecOrMat{R}, ir_dest::AbstractRange{Int}, jr_dest::AbstractRange{Int},
               A::AbstractVecOrMat{S}, ir_src::AbstractRange{Int}, jr_src::AbstractRange{Int}) where {R,S}
    if length(ir_dest) != length(ir_src)
        throw(ArgumentError(LazyString("source and destination must have same size (got ",
            length(ir_src)," and ",length(ir_dest),")")))
    end
    if length(jr_dest) != length(jr_src)
        throw(ArgumentError(LazyString("source and destination must have same size (got ",
            length(jr_src)," and ",length(jr_dest),")")))
    end
    @boundscheck checkbounds(B, ir_dest, jr_dest)
    @boundscheck checkbounds(A, ir_src, jr_src)
    A′ = unalias(B, A)
    jdest = first(jr_dest)
    for jsrc in jr_src
        idest = first(ir_dest)
        for isrc in ir_src
            @inbounds B[idest,jdest] = A′[isrc,jsrc]
            idest += step(ir_dest)
        end
        jdest += step(jr_dest)
    end
    return B
end
```
-/
def copytoBlock {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S R E : Type} [ForIn m R I64]
    (length : R → m I64) (checkDest : D → R → R → m Unit)
    (checkSrc : S → R → R → m Unit) (unalias : D → S → m S)
    (first : R → m I64) (step : R → m I64) (getindex : S → I64 → I64 → m E)
    (setindex : D → I64 → I64 → E → m Unit)
    (dest : D) (irDest jrDest : R) (src : S) (irSrc jrSrc : R) : m D := do
  if (← length irDest) != (← length irSrc) then
    throw (.julia (.argumentError "source and destination must have same size"))
  if (← length jrDest) != (← length jrSrc) then
    throw (.julia (.argumentError "source and destination must have same size"))
  checkDest dest irDest jrDest
  checkSrc src irSrc jrSrc
  let src' ← unalias dest src
  let mut jdest ← first jrDest
  for jsrc in jrSrc do
    let mut idest ← first irDest
    for isrc in irSrc do
      setindex dest idest jdest (← getindex src' isrc jsrc)
      idest := idest + (← step irDest)
    jdest := jdest + (← step jrDest)
  return dest

/--
Julia source: base/abstractarray.jl:1184-1184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _checkaxs(axd, axs) = axd == axs || throw(DimensionMismatch("axes must agree, got $axd and $axs"))
```
-/
def checkAxes {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {Ax : Type}
    (eq : Ax → Ax → Bool) (showAxes : Ax → String) (axd axs : Ax) : m Bool := do
  if eq axd axs then return true
  throw (.dimensionMismatch ("axes must agree, got " ++ showAxes axd ++ " and " ++ showAxes axs))

/--
Julia source: base/abstractarray.jl:1186-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto_axcheck!(dest, src)
    _checkaxs(axes(dest), axes(src))
    copyto!(dest, src)
end
```
-/
def copytoAxesCheck {m : Type → Type} [Monad m] {D S Ax : Type}
    (axesDest : D → m Ax) (axesSrc : S → m Ax) (checkAxes : Ax → Ax → m Bool)
    (copyto : D → S → m D) (dest : D) (src : S) : m D := do
  let _ ← checkAxes (← axesDest dest) (← axesSrc src)
  copyto dest src

/--
Julia source: base/abstractarray.jl:1211-1214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copymutable(a::AbstractArray)
    @_propagate_inbounds_meta
    copyto!(similar(a), a)
end
```
-/
def copyMutableArray {m : Type → Type} [Monad m] {A B : Type}
    (similar : A → m B) (copyto : B → A → m B) (a : A) : m B := do
  copyto (← similar a) a

/--
Julia source: base/abstractarray.jl:1215-1215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copymutable(itr) = collect(itr)
```
-/
def copyMutableIterator {m : Type → Type} {A B : Type}
    (collect : A → m B) (a : A) : m B := collect a

/--
Julia source: base/abstractarray.jl:1216-1216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copymutable(a::Array) = copy(a)
```
-/
def copyMutableDense {m : Type → Type} {A B : Type}
    (copy : A → m B) (a : A) : m B := copy a

/--
Julia source: base/abstractarray.jl:1218-1218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zero(x::AbstractArray{T}) where {T<:Number} = fill!(similar(x, typeof(zero(T))), zero(T))
```
-/
def zeroNumericArray {m : Type → Type} [Monad m] {A B E Ty : Type}
    (zero : Ty → m E) (typeof : E → Ty) (similar : A → Ty → m B)
    (fill : B → E → m B) (t : Ty) (x : A) : m B := do
  let z ← zero t
  let dest ← similar x (typeof z)
  fill dest (← zero t)

/--
Julia source: base/abstractarray.jl:1219-1219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zero(x::AbstractArray{S}) where {S<:Union{Missing, Number}} = fill!(similar(x, typeof(zero(S))), zero(S))
```
-/
def zeroMissingArray {m : Type → Type} [Monad m] {A B E Ty : Type}
    (zero : Ty → m E) (typeof : E → Ty) (similar : A → Ty → m B)
    (fill : B → E → m B) (t : Ty) (x : A) : m B := do
  let z ← zero t
  let dest ← similar x (typeof z)
  fill dest (← zero t)

/--
Julia source: base/abstractarray.jl:1220-1220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zero(x::AbstractArray) = map(zero, x)
```
-/
def zeroArray {m : Type → Type} {A B E F : Type}
    (zero : E → m F) (map : (E → m F) → A → m B) (x : A) : m B := map zero x

/--
Julia source: base/abstractarray.jl:1222-1234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _one(unit::T, mat::AbstractMatrix) where {T}
    (rows, cols) = axes(mat)
    (length(rows) == length(cols)) ||
      throw(DimensionMismatch("multiplicative identity defined only for square matrices"))
    zer = zero(unit)::T
    require_one_based_indexing(mat)
    I = similar(mat, T)
    fill!(I, zer)
    for i ∈ rows
        I[i, i] = unit
    end
    I
end
```
-/
def oneMatrix {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B E Ax : Type} [ForIn m Ax I64]
    (axes : A → m (Ax × Ax)) (length : Ax → m I64) (zero : E → m E)
    (requireOneBased : A → m Unit) (similar : A → m B)
    (fill : B → E → m Unit) (setindex : B → I64 → I64 → E → m Unit)
    (unit : E) (mat : A) : m B := do
  let (rows, cols) ← axes mat
  if (← length rows) != (← length cols) then
    throw (.dimensionMismatch "multiplicative identity defined only for square matrices")
  let zer ← zero unit
  requireOneBased mat
  let ident ← similar mat
  fill ident zer
  for i in rows do setindex ident i i unit
  return ident

/--
Julia source: base/abstractarray.jl:1236-1236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
one(x::AbstractMatrix{T}) where {T} = _one(one(T), x)
```
-/
def oneArray {m : Type → Type} [Monad m] {A B E Ty : Type}
    (one : Ty → m E) (oneMatrix : E → A → m B) (t : Ty) (x : A) : m B := do
  oneMatrix (← one t) x

/--
Julia source: base/abstractarray.jl:1237-1237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oneunit(x::AbstractMatrix{T}) where {T} = _one(oneunit(T), x)
```
-/
def oneunitArray {m : Type → Type} [Monad m] {A B E Ty : Type}
    (oneunit : Ty → m E) (oneMatrix : E → A → m B) (t : Ty) (x : A) : m B := do
  oneMatrix (← oneunit t) x

/--
Julia source: base/abstractarray.jl:1245-1245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate_starting_state(A) = iterate_starting_state(A, IndexStyle(A))
```
-/
def iterateStartingState {A Style St : Type}
    (indexStyle : A → Result Style) (startingState : A → Style → Result St)
    (a : A) : Result St := do startingState a (← indexStyle a)

/--
Julia source: base/abstractarray.jl:1246-1246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate_starting_state(A, ::IndexLinear) = firstindex(A)
```
-/
def iterateStartingLinear {A I : Type} (firstindex : A → Result I) (a : A) : Result I :=
  firstindex a

/--
Julia source: base/abstractarray.jl:1247-1247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate_starting_state(A, ::IndexStyle) = (eachindex(A),)
```
-/
def iterateStartingCartesian {A Inds : Type} (eachindex : A → Result Inds)
    (a : A) : Result (Inds × Unit) := do return (← eachindex a, ())

/--
Julia source: base/abstractarray.jl:1250-1250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline iterate(A::AbstractArray, state = iterate_starting_state(A)) = _iterate_abstractarray(A, state)
```
-/
def iterateArray {A St E Next : Type}
    (iterate : A → St → Result (Option (E × Next))) (a : A) (state : St) :
    Result (Option (E × Next)) := iterate a state

/--
Julia source: base/abstractarray.jl:1251-1255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _iterate_abstractarray(A::AbstractArray, state::Tuple)
    y = iterate(state...)::Union{Nothing,Tuple}
    y === nothing && return nothing
    A[y[1]], (state[1], tail(y)...)
end
```
-/
def iterateCartesian {A Inds St Next I E : Type}
    (iterate : Inds → St → Result (Option (I × Next))) (getindex : A → I → Result E)
    (a : A) (state : Inds × St) : Result (Option (E × (Inds × Next))) := do
  let y ← iterate state.1 state.2
  match y with
  | none => return none
  | some (i, st) => return some (← getindex a i, (state.1, st))

/--
Julia source: base/abstractarray.jl:1256-1259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _iterate_abstractarray(A::AbstractArray, state::Integer)
    checkbounds(Bool, A, state) || return nothing
    A[state], state + one(state)
end
```
-/
def iterateInteger {A I E : Type} (checkbounds : A → I → Result Bool)
    (getindex : A → I → Result E) (one : I → Result I) (add : I → I → Result I)
    (a : A) (state : I) : Result (Option (E × I)) := do
  if !(← checkbounds a state) then return none
  let x ← getindex a state
  return some (x, ← add state (← one state))

/--
Julia source: base/abstractarray.jl:1262-1262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(a::AbstractArray) = (length(a) == 0)
```
-/
def isemptyArray {m : Type → Type} [Monad m] {A : Type}
    (length : A → m I64) (a : A) : m Bool := do
  return (← length a).val == 0

/--
Julia source: base/abstractarray.jl:1267-1267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(::Type{T}, r::StepRange) where {T<:Real} = T(r.start):T(r.step):T(last(r))
```
-/
def mapStepRange {A Start Step End F R : Type} (start : A → Start) (step : A → Step)
    (last : A → Result End) (convertStart : Start → Result F)
    (convertStep : Step → Result F) (convertEnd : End → Result F)
    (range : F → F → F → Result R) (r : A) : Result R := do
  let first ← convertStart (start r)
  let stride ← convertStep (step r)
  range first stride (← convertEnd (← last r))

/--
Julia source: base/abstractarray.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(::Type{T}, r::UnitRange) where {T<:Real} = T(r.start):T(last(r))
```
-/
def mapUnitRange {A E F R : Type} (start : A → E) (last : A → Result E)
    (convert : E → Result F) (range : F → F → Result R) (r : A) : Result R := do
  let first ← convert (start r)
  range first (← convert (← last r))

/--
Julia source: base/abstractarray.jl:1269-1269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(::Type{T}, r::StepRangeLen) where {T<:AbstractFloat} = convert(StepRangeLen{T}, r)
```
-/
def mapStepRangeLen {A B : Type} (convert : A → Result B) (r : A) : Result B := convert r

/--
Julia source: base/abstractarray.jl:1270-1272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map(::Type{T}, r::LinRange) where T<:AbstractFloat
    LinRange(T(r.start), T(r.stop), length(r))
end
```
-/
def mapLinRange {A E F R : Type} (start stop : A → E) (convert : E → Result F)
    (length : A → Result I64) (linRange : F → F → I64 → Result R) (r : A) : Result R := do
  let first ← convert (start r)
  let last ← convert (stop r)
  linRange first last (← length r)

/--
Julia source: base/abstractarray.jl:1279-1279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(x::AbstractArray{T}) where {T} = unsafe_convert(Ptr{T}, cconvert(Ptr{T}, x))
```
-/
def pointerArray {A C Ptr : Type} (cconvert : A → Result C)
    (unsafeConvert : C → Result Ptr) (x : A) : Result Ptr := do
  unsafeConvert (← cconvert x)

/--
Julia source: base/abstractarray.jl:1280-1283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pointer(x::AbstractArray{T}, i::Integer) where T
    @inline
    pointer(x) + Int(_memory_offset(x, i))::Int
end
```
-/
def pointerIndex {A I Offset Ptr : Type} (pointer : A → Result Ptr)
    (memoryOffset : A → I → Result Offset) (toInt : Offset → Result I64)
    (add : Ptr → I64 → Result Ptr) (x : A) (i : I) : Result Ptr := do
  let p ← pointer x
  add p (← toInt (← memoryOffset x i))

/--
Julia source: base/abstractarray.jl:1286-1286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_memory_offset(x::DenseArray, I::Vararg{Any,N}) where {N} = (_to_linear_index(x, I...) - first(LinearIndices(x)))*elsize(x)
```
-/
def memoryOffsetDense {A Is Lin Index Origin Difference Offset : Type}
    (toLinearIndex : A → Is → Result Index)
    (linearIndices : A → Result Lin) (first : Lin → Result Origin)
    (sub : Index → Origin → Result Difference)
    (elsize : A → Result I64) (mul : Difference → I64 → Result Offset)
    (x : A) (is : Is) : Result Offset := do
  let i ← toLinearIndex x is
  let origin ← first (← linearIndices x)
  let difference ← sub i origin
  mul difference (← elsize x)

/--
Julia source: base/abstractarray.jl:1287-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _memory_offset(x::AbstractArray, I::Vararg{Any,N}) where {N}
    J = _to_subscript_indices(x, I...)
    return sum(map((i, s, o)->s*(i-o), J, strides(x), Tuple(first(CartesianIndices(x)))))*elsize(x)
end
```
-/
def memoryOffsetArray {A Is J Strides Origins Products Index Stride Origin Difference Product Sum Offset : Type}
    (toSubscripts : A → Is → Result J) (strides : A → Result Strides)
    (firstCartesian : A → Result Origins)
    (sub : Index → Origin → Result Difference) (mul : Stride → Difference → Result Product)
    (map : (Index → Stride → Origin → Result Product) → J → Strides → Origins → Result Products)
    (sum : Products → Result Sum) (elsize : A → Result I64)
    (mulTotal : Sum → I64 → Result Offset) (x : A) (is : Is) : Result Offset := do
  let js ← toSubscripts x is
  let ss ← strides x
  let origins ← firstCartesian x
  let total ← sum (← map (fun i s o => do mul s (← sub i o)) js ss origins)
  mulTotal total (← elsize x)

/- UNTRANSLATED: Compiler metadata assignment, with no callable method body.
Julia source: base/abstractarray.jl:1293-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typename(typeof(function getindex end)).constprop_heuristic = Core.ARRAY_INDEX_HEURISTIC
```
-/

/- UNTRANSLATED: Compiler metadata assignment, with no callable method body.
Julia source: base/abstractarray.jl:1294-1294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typename(typeof(function setindex! end)).constprop_heuristic = Core.ARRAY_INDEX_HEURISTIC
```
-/

/--
Julia source: base/abstractarray.jl:1363-1367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::AbstractArray, I...)
    @_propagate_inbounds_meta
    error_if_canonical_getindex(IndexStyle(A), A, I...)
    _getindex(IndexStyle(A), A, to_indices(A, I)...)
end
```
-/
def getindexArray {A I J Style E : Type}
    (indexStyle : A → Result Style) (canonicalCheck : Style → A → I → Result Unit)
    (toIndices : A → I → Result J) (get : Style → A → J → Result E)
    (a : A) (is : I) : Result E := do
  canonicalCheck (← indexStyle a) a is
  let style ← indexStyle a
  get style a (← toIndices a is)

/--
Julia source: base/abstractarray.jl:1369-1369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds getindex(A::Array, i1::Integer, I::Integer...) = A[to_indices(A, (i1, I...))...]
```
-/
def getindexIntegerArray {A I Rest J E : Type}
    (toIndices : A → I × Rest → Result J) (get : A → J → Result E)
    (a : A) (i : I) (is : Rest) : Result E := do
  get a (← toIndices a (i, is))

/--
Julia source: base/abstractarray.jl:1371-1371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline unsafe_getindex(A::AbstractArray, I...) = @inbounds getindex(A, I...)
```
-/
def unsafeGetindex {A I E : Type} (get : A → I → Result E)
    (a : A) (is : I) : Result E := get a is

/--
Julia source: base/abstractarray.jl:1376-1376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CanonicalIndexError(func::String, @nospecialize(type)) = new(func, type)
```
-/
def canonicalIndexError {Ty : Type} (functionName : String) (typeToken : Ty) :
    CanonicalError Ty := ⟨functionName, typeToken⟩

/--
Julia source: base/abstractarray.jl:1379-1380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_if_canonical_getindex(::IndexLinear, A::AbstractArray, ::Int) =
    throw(CanonicalIndexError("getindex", typeof(A)))
```
-/
def errorCanonicalGetindexLinear {A : Type} (typeof : A → String)
    (a : A) (_i : I64) : Result Unit :=
  throw (canonicalError (canonicalIndexError "getindex" (typeof a)))

/--
Julia source: base/abstractarray.jl:1381-1382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_if_canonical_getindex(::IndexCartesian, A::AbstractArray{T,N}, ::Vararg{Int,N}) where {T,N} =
    throw(CanonicalIndexError("getindex", typeof(A)))
```
-/
def errorCanonicalGetindexCartesian {A : Type} {n : Nat} (typeof : A → String)
    (a : A) (_is : Fin n → I64) : Result Unit :=
  throw (canonicalError (canonicalIndexError "getindex" (typeof a)))

/--
Julia source: base/abstractarray.jl:1383-1383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_if_canonical_getindex(::IndexStyle, ::AbstractArray, ::Any...) = nothing
```
-/
def errorCanonicalGetindexOther {Style A I : Type}
    (_style : Style) (_a : A) (_is : I) : Result Unit := pure ()

/--
Julia source: base/abstractarray.jl:1386-1387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_getindex(::IndexStyle, A::AbstractArray, I...) =
    error("getindex for $(typeof(A)) with types $(typeof(I)) is not supported")
```
-/
def getindexUnsupported {Style A I E : Type}
    (typeofA : A → String) (typeofI : I → String)
    (_style : Style) (a : A) (is : I) : Result E :=
  throw (.errorException ("getindex for " ++ typeofA a ++ " with types " ++ typeofI is ++
    " is not supported"))

/--
Julia source: base/abstractarray.jl:1390-1390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_getindex(::IndexLinear, A::AbstractVector, i::Int) = (@_propagate_inbounds_meta; getindex(A, i))  # ambiguity resolution in case packages specialize this (to be avoided if at all possible, but see Interpolations.jl)
```
-/
def getindexLinearVector {A E : Type} (get : A → I64 → Result E)
    (a : A) (i : I64) : Result E := get a i

/--
Julia source: base/abstractarray.jl:1391-1391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_getindex(::IndexLinear, A::AbstractArray, i::Int) = (@_propagate_inbounds_meta; getindex(A, i))
```
-/
def getindexLinearScalar {A E : Type} (get : A → I64 → Result E)
    (a : A) (i : I64) : Result E := get a i

/--
Julia source: base/abstractarray.jl:1392-1397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(::IndexLinear, A::AbstractArray, I::Vararg{Int,M}) where M
    @inline
    @boundscheck checkbounds(A, I...) # generally _to_linear_index requires bounds checking
    @inbounds r = getindex(A, _to_linear_index(A, I...))
    r
end
```
-/
def getindexLinear {A E : Type} (checkbounds : A → List I64 → Result Unit)
    (toLinear : A → List I64 → Result I64) (get : A → I64 → Result E)
    (a : A) (is : List I64) : Result E := do
  checkbounds a is
  let r ← get a (← toLinear a is)
  return r

/--
Julia source: base/abstractarray.jl:1398-1398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_linear_index(A::AbstractArray, i::Integer) = i
```
-/
def toLinearScalar {A : Type} {t : IntTy} (_a : A) (i : JInt t) : JInt t := i

/--
Julia source: base/abstractarray.jl:1399-1399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_linear_index(A::AbstractVector, i::Integer, I::Integer...) = i
```
-/
def toLinearVector {A Rest : Type} {t : IntTy}
    (_a : A) (i : JInt t) (_is : Rest) : JInt t := i

/--
Julia source: base/abstractarray.jl:1400-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_linear_index(A::AbstractArray) = first(LinearIndices(A))
```
-/
def toLinearEmpty {A Indices I : Type}
    (linearIndices : A → Result Indices) (first : Indices → Result I)
    (a : A) : Result I := do first (← linearIndices a)

/--
Julia source: base/abstractarray.jl:1401-1401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_linear_index(A::AbstractArray, I::Integer...) = (@inline; _sub2ind(A, I...))
```
-/
def toLinearMany {A I J : Type} (sub2ind : A → I → Result J)
    (a : A) (is : I) : Result J := sub2ind a is

/--
Julia source: base/abstractarray.jl:1404-1409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(::IndexCartesian, A::AbstractArray, I::Vararg{Int,M}) where M
    @inline
    @boundscheck checkbounds(A, I...) # generally _to_subscript_indices requires bounds checking
    @inbounds r = getindex(A, _to_subscript_indices(A, I...)...)
    r
end
```
-/
def getindexCartesian {A J E : Type} (checkbounds : A → List I64 → Result Unit)
    (toSubscripts : A → List I64 → Result J) (get : A → J → Result E)
    (a : A) (is : List I64) : Result E := do
  checkbounds a is
  let r ← get a (← toSubscripts a is)
  return r

/--
Julia source: base/abstractarray.jl:1410-1413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(::IndexCartesian, A::AbstractArray{T,N}, I::Vararg{Int, N}) where {T,N}
    @_propagate_inbounds_meta
    getindex(A, I...)
end
```
-/
def getindexCartesianExact {A E : Type} {n : Nat}
    (get : A → (Fin n → I64) → Result E) (a : A) (is : Fin n → I64) : Result E :=
  get a is

/--
Julia source: base/abstractarray.jl:1414-1414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray, i::Integer) = (@inline; _unsafe_ind2sub(A, i))
```
-/

def toSubscriptsScalar {A I J : Type}
    (unsafeInd2sub : A → I → Result J) (a : A) (i : I) : Result J :=
  unsafeInd2sub a i
/--
Julia source: base/abstractarray.jl:1415-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,N}) where {T,N} = (@inline; map(first, axes(A)))
```
-/

def toSubscriptsEmpty {A Axis I : Type}
    (axes : A → Result (List Axis)) (first : Axis → Result I)
    (a : A) : Result (List I) := do (← axes a).mapM first
/--
Julia source: base/abstractarray.jl:1416-1416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,0}) where {T} = ()
```
-/

def toSubscriptsZero {A : Type} (_a : A) : Unit := ()
/--
Julia source: base/abstractarray.jl:1417-1417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,0}, i::Integer) where {T} = ()
```
-/
def toSubscriptsZeroScalar {A I : Type} (_a : A) (_i : I) : Unit := ()

/--
Julia source: base/abstractarray.jl:1418-1418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,0}, I::Integer...) where {T} = ()
```
-/
def toSubscriptsZeroMany {A I : Type} (_a : A) (_is : I) : Unit := ()

/--
Julia source: base/abstractarray.jl:1419-1423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _to_subscript_indices(A::AbstractArray{T,N}, I::Integer...) where {T,N}
    @inline
    J, Jrem = IteratorsMD.split(I, Val(N))
    _to_subscript_indices(A, J, Jrem)
end
```
-/
def toSubscriptsSplit {A I J Rem Out : Type} (n : Nat)
    (split : I → Nat → Result (J × Rem))
    (convert : A → J → Rem → Result Out) (a : A) (is : I) : Result Out := do
  let (j, remainder) ← split is n
  convert a j remainder

/--
Julia source: base/abstractarray.jl:1424-1425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray, J::Tuple, Jrem::Tuple{}) =
    __to_subscript_indices(A, axes(A), J, Jrem)
```
-/
def toSubscriptsNoRemainder {A Ax J Out : Type} (axes : A → Result Ax)
    (convert : A → Ax → J → Unit → Result Out) (a : A) (j : J) : Result Out := do
  convert a (← axes a) j ()

/--
Julia source: base/abstractarray.jl:1426-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __to_subscript_indices(A::AbstractArray,
        ::Tuple{AbstractUnitRange,Vararg{AbstractUnitRange}}, J::Tuple, Jrem::Tuple{})
    @inline
    (J..., map(first, tail(_remaining_size(J, axes(A))))...)
end
```
-/
def toSubscriptsFill {A Axis I : Type} (axes : A → Result (List Axis))
    (remainingSize : List I → List Axis → Result (List Axis))
    (tail : List Axis → Result (List Axis)) (first : Axis → Result I)
    (a : A) (_dispatchAxes : Axis × List Axis) (j : List I) : Result (List I) := do
  let remainder ← remainingSize j (← axes a)
  let trailing ← (← tail remainder).mapM first
  return j ++ trailing

/--
Julia source: base/abstractarray.jl:1431-1431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A, J::Tuple, Jrem::Tuple) = J # already bounds-checked, safe to drop
```
-/
def toSubscriptsDropRemainder {A J Rem : Type} (_a : A) (j : J) (_remainder : Rem) : J := j

/--
Julia source: base/abstractarray.jl:1432-1432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,N}, I::Vararg{Int,N}) where {T,N} = I
```
-/
def toSubscriptsExact {A : Type} {n : Nat} (_a : A) (is : Fin n → I64) : Fin n → I64 := is

/--
Julia source: base/abstractarray.jl:1433-1433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_remaining_size(::Tuple{Any}, t::Tuple) = t
```
-/
def remainingSizeSingle {I Axis : Type} (_h : I) (axes : List Axis) : List Axis := axes

/--
Julia source: base/abstractarray.jl:1434-1434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_remaining_size(h::Tuple, t::Tuple) = (@inline; _remaining_size(tail(h), tail(t)))
```
-/
def remainingSizeMany {H T HRest TRest Out : Type}
    (tailH : H → Result HRest) (tailT : T → Result TRest)
    (recurse : HRest → TRest → Result Out) (h : H) (t : T) : Result Out := do
  let hs ← tailH h
  let ts ← tailT t
  recurse hs ts

/--
Julia source: base/abstractarray.jl:1435-1435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unsafe_ind2sub(::Tuple{}, i) = () # _ind2sub may throw(BoundsError()) in this case
```
-/
def unsafeInd2subEmpty {I : Type} (_i : I) : Unit := ()

/--
Julia source: base/abstractarray.jl:1436-1436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unsafe_ind2sub(sz, i) = (@inline; _ind2sub(sz, i))
```
-/
def unsafeInd2sub {Shape I Out : Type} (ind2sub : Shape → I → Result Out)
    (shape : Shape) (i : I) : Result Out := ind2sub shape i

/--
Julia source: base/abstractarray.jl:1464-1468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::AbstractArray, v, I...)
    @_propagate_inbounds_meta
    error_if_canonical_setindex(IndexStyle(A), A, I...)
    _setindex!(IndexStyle(A), A, v, to_indices(A, I)...)
end
```
-/
def setindexArray {m : Type → Type} [Monad m] {A V I J Style R : Type}
    (indexStyle : A → m Style) (canonicalCheck : Style → A → I → m Unit)
    (toIndices : A → I → m J) (set : Style → A → V → J → m R)
    (a : A) (v : V) (is : I) : m R := do
  canonicalCheck (← indexStyle a) a is
  let style ← indexStyle a
  set style a v (← toIndices a is)

/--
Julia source: base/abstractarray.jl:1469-1473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_setindex!(A::AbstractArray, v, I...)
    @inline
    @inbounds r = setindex!(A, v, I...)
    r
end
```
-/
def unsafeSetindex {m : Type → Type} [Monad m] {A V I R : Type}
    (set : A → V → I → m R) (a : A) (v : V) (is : I) : m R := do
  let r ← set a v is
  return r

/--
Julia source: base/abstractarray.jl:1475-1476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_if_canonical_setindex(::IndexLinear, A::AbstractArray, ::Int) =
    throw(CanonicalIndexError("setindex!", typeof(A)))
```
-/
def errorCanonicalSetindexLinear {A : Type} (typeof : A → String)
    (a : A) (_i : I64) : Result Unit :=
  throw (canonicalError (canonicalIndexError "setindex!" (typeof a)))

/--
Julia source: base/abstractarray.jl:1477-1478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_if_canonical_setindex(::IndexCartesian, A::AbstractArray{T,N}, ::Vararg{Int,N}) where {T,N} =
    throw(CanonicalIndexError("setindex!", typeof(A)))
```
-/
def errorCanonicalSetindexCartesian {A : Type} {n : Nat} (typeof : A → String)
    (a : A) (_is : Fin n → I64) : Result Unit :=
  throw (canonicalError (canonicalIndexError "setindex!" (typeof a)))

/--
Julia source: base/abstractarray.jl:1479-1479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_if_canonical_setindex(::IndexStyle, ::AbstractArray, ::Any...) = nothing
```
-/
def errorCanonicalSetindexOther {Style A I : Type}
    (_style : Style) (_a : A) (_is : I) : Result Unit := pure ()

/--
Julia source: base/abstractarray.jl:1482-1483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_setindex!(::IndexStyle, A::AbstractArray, v, I...) =
    error("setindex! for $(typeof(A)) with types $(typeof(I)) is not supported")
```
-/
def setindexUnsupported {Style A V I R : Type}
    (typeofA : A → String) (typeofI : I → String)
    (_style : Style) (a : A) (_v : V) (is : I) : Result R :=
  throw (.errorException ("setindex! for " ++ typeofA a ++ " with types " ++ typeofI is ++
    " is not supported"))

/--
Julia source: base/abstractarray.jl:1486-1486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_setindex!(::IndexLinear, A::AbstractArray, v, i::Int) = (@_propagate_inbounds_meta; setindex!(A, v, i))
```
-/
def setindexLinearScalar {m : Type → Type} [Monad m] {A V R : Type}
    (set : A → V → I64 → m R) (a : A) (v : V) (i : I64) : m R := set a v i

/--
Julia source: base/abstractarray.jl:1487-1492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(::IndexLinear, A::AbstractArray, v, I::Vararg{Int,M}) where M
    @inline
    @boundscheck checkbounds(A, I...)
    @inbounds r = setindex!(A, v, _to_linear_index(A, I...))
    r
end
```
-/
def setindexLinear {m : Type → Type} [Monad m] {A V R : Type}
    (checkbounds : A → List I64 → m Unit) (toLinear : A → List I64 → m I64)
    (set : A → V → I64 → m R) (a : A) (v : V) (is : List I64) : m R := do
  checkbounds a is
  let r ← set a v (← toLinear a is)
  return r

/--
Julia source: base/abstractarray.jl:1495-1498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(::IndexCartesian, A::AbstractArray{T,N}, v, I::Vararg{Int, N}) where {T,N}
    @_propagate_inbounds_meta
    setindex!(A, v, I...)
end
```
-/
def setindexCartesianExact {m : Type → Type} [Monad m] {A V R : Type} {n : Nat}
    (set : A → V → (Fin n → I64) → m R)
    (a : A) (v : V) (is : Fin n → I64) : m R := set a v is

/--
Julia source: base/abstractarray.jl:1499-1504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(::IndexCartesian, A::AbstractArray, v, I::Vararg{Int,M}) where M
    @inline
    @boundscheck checkbounds(A, I...)
    @inbounds r = setindex!(A, v, _to_subscript_indices(A, I...)...)
    r
end
```
-/
def setindexCartesian {m : Type → Type} [Monad m] {A V J R : Type}
    (checkbounds : A → List I64 → m Unit) (toSubscripts : A → List I64 → m J)
    (set : A → V → J → m R) (a : A) (v : V) (is : List I64) : m R := do
  checkbounds a is
  let r ← set a v (← toSubscripts a is)
  return r

/- UNTRANSLATED: Function declaration without a method body.
Julia source: base/abstractarray.jl:1518-1518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsetindex! end
```
-/

/- UNTRANSLATED: Function declaration without a method body.
Julia source: base/abstractarray.jl:1546-1546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parent end
```
-/

/--
Julia source: base/abstractarray.jl:1548-1548 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parent(a::AbstractArray) = a
```
-/
def parentArray {A : Type} (a : A) : A := a

/--
Julia source: base/abstractarray.jl:1566-1566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unalias(dest, A::AbstractArray) = mightalias(dest, A) ? unaliascopy(A) : A
```
-/
def unaliasArray {m : Type → Type} [Monad m] {D A : Type}
    (mightalias : D → A → m Bool) (unaliascopy : A → m A) (dest : D) (a : A) : m A := do
  if ← mightalias dest a then unaliascopy a else pure a

/--
Julia source: base/abstractarray.jl:1567-1567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unalias(dest, A::AbstractRange) = A
```
-/
def unaliasRange {D A : Type} (_dest : D) (a : A) : A := a

/--
Julia source: base/abstractarray.jl:1568-1568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unalias(dest, A) = A
```
-/
def unaliasOther {D A : Type} (_dest : D) (a : A) : A := a

/--
Julia source: base/abstractarray.jl:1582-1582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unaliascopy(A::Array) = copy(A)
```
-/
def unaliascopyDense {m : Type → Type} [Monad m] {A : Type}
    (copy : A → m A) (a : A) : m A := copy a

/--
Julia source: base/abstractarray.jl:1583-1583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unaliascopy(A::AbstractArray)::typeof(A) = (@noinline; _unaliascopy(A, copy(A)))
```
-/
def unaliascopyArray {m : Type → Type} [Monad m] {A C R : Type}
    (copy : A → m C) (unaliascopy : A → C → m R) (assertType : R → m A)
    (a : A) : m A := do
  let c ← copy a
  assertType (← unaliascopy a c)

/--
Julia source: base/abstractarray.jl:1584-1584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unaliascopy(A::T, C::T) where {T} = C
```
-/
def unaliascopySame {A : Type} (_a : A) (c : A) : A := c

/--
Julia source: base/abstractarray.jl:1585-1592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _unaliascopy(A, C)
    Aw = typename(typeof(A)).wrapper
    throw(ArgumentError(LazyString("an array of type `", Aw, "` shares memory with another argument ",
    "and must make a preventative copy of itself in order to maintain consistent semantics, ",
    "but `copy(::", typeof(A), ")` returns a new array of type `", typeof(C), "`.\n",
    """To fix, implement:
        `Base.unaliascopy(A::""", Aw, ")::typeof(A)`")))
end
```
-/
def unaliascopyMismatch {A C : Type} (typeofA : A → String) (typeofC : C → String)
    (wrapper : String → String) (lazyString : List String → Result String)
    (a : A) (c : C) : Result A := do
  let aw := wrapper (typeofA a)
  let message ← lazyString [
    "an array of type `", aw, "` shares memory with another argument ",
    "and must make a preventative copy of itself in order to maintain consistent semantics, ",
    "but `copy(::", typeofA a, ")` returns a new array of type `", typeofC c, "`.\n",
    "To fix, implement:\n        `Base.unaliascopy(A::", aw, ")::typeof(A)`"]
  throw (.julia (.argumentError message))

/--
Julia source: base/abstractarray.jl:1593-1593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unaliascopy(A) = A
```
-/
def unaliascopyOther {A : Type} (a : A) : A := a

/--
Julia source: base/abstractarray.jl:1603-1603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mightalias(A::AbstractArray, B::AbstractArray) = !isbits(A) && !isbits(B) && !isempty(A) && !isempty(B) && !_isdisjoint(dataids(A), dataids(B))
```
-/
def mightaliasArray {m : Type → Type} [Monad m] {A B IDsA IDsB : Type}
    (isbitsA : A → m Bool) (isbitsB : B → m Bool)
    (isemptyA : A → m Bool) (isemptyB : B → m Bool)
    (dataidsA : A → m IDsA) (dataidsB : B → m IDsB)
    (isdisjoint : IDsA → IDsB → m Bool) (a : A) (b : B) : m Bool := do
  if ← isbitsA a then return false
  if ← isbitsB b then return false
  if ← isemptyA a then return false
  if ← isemptyB b then return false
  let as ← dataidsA a
  let bs ← dataidsB b
  return !(← isdisjoint as bs)

/--
Julia source: base/abstractarray.jl:1604-1604 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mightalias(x, y) = false
```
-/
def mightaliasOther {A B : Type} (_a : A) (_b : B) : Bool := false

/--
Julia source: base/abstractarray.jl:1606-1606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isdisjoint(as::Tuple{}, bs::Tuple{}) = true
```
-/
def isdisjointEmptyEmpty : Bool := true

/--
Julia source: base/abstractarray.jl:1607-1607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isdisjoint(as::Tuple{}, bs::Tuple{UInt}) = true
```
-/
def isdisjointEmptyOne (_b : JInt .u64) : Bool := true

/--
Julia source: base/abstractarray.jl:1608-1608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isdisjoint(as::Tuple{}, bs::Tuple) = true
```
-/
def isdisjointEmptyMany {B : Type} (_bs : List B) : Bool := true

/--
Julia source: base/abstractarray.jl:1609-1609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isdisjoint(as::Tuple{UInt}, bs::Tuple{}) = true
```
-/
def isdisjointOneEmpty (_a : JInt .u64) : Bool := true

/--
Julia source: base/abstractarray.jl:1610-1610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isdisjoint(as::Tuple{UInt}, bs::Tuple{UInt}) = as[1] != bs[1]
```
-/
def isdisjointOneOne (a b : JInt .u64) : Bool := decide (a ≠ b)

/--
Julia source: base/abstractarray.jl:1611-1611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isdisjoint(as::Tuple{UInt}, bs::Tuple) = !(as[1] in bs)
```
-/
def isdisjointOneMany {B : Type} (contains : JInt .u64 → List B → Bool)
    (a : JInt .u64) (bs : List B) : Bool := !(contains a bs)

/--
Julia source: base/abstractarray.jl:1612-1612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isdisjoint(as::Tuple, bs::Tuple{}) = true
```
-/
def isdisjointManyEmpty {A : Type} (_as : List A) : Bool := true

/--
Julia source: base/abstractarray.jl:1613-1613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isdisjoint(as::Tuple, bs::Tuple{UInt}) = !(bs[1] in as)
```
-/
def isdisjointManyOne {A : Type} (contains : JInt .u64 → List A → Bool)
    (as : List A) (b : JInt .u64) : Bool := !(contains b as)

/--
Julia source: base/abstractarray.jl:1614-1614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isdisjoint(as::Tuple, bs::Tuple) = !(as[1] in bs) && _isdisjoint(tail(as), bs)
```
-/
def isdisjointMany {A B : Type} (contains : A → List B → Bool)
    (recurse : List A → List B → Bool) (as : A × List A) (bs : List B) : Bool :=
  !(contains as.1 bs) && recurse as.2 bs

/--
Julia source: base/abstractarray.jl:1626-1626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(A::AbstractArray) = (objectid(A),)
```
-/
def dataidsArray {A : Type} (objectid : A → JInt .u64) (a : A) : List (JInt .u64) :=
  [objectid a]

/--
Julia source: base/abstractarray.jl:1627-1627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(A::Memory) = (UInt(A.ptr),)
```
-/
def dataidsMemory {m : Type → Type} [Monad m] {M Ptr : Type}
    (ptr : M → Ptr) (toUInt : Ptr → m (JInt .u64))
    (a : M) : m (List (JInt .u64)) := do return [← toUInt (ptr a)]

/--
Julia source: base/abstractarray.jl:1628-1628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(A::Array) = dataids(A.ref.mem)
```
-/
def dataidsDense {m : Type → Type} {A Ref Memory IDs : Type}
    (ref : A → Ref) (mem : Ref → Memory)
    (dataids : Memory → m IDs) (a : A) : m IDs := dataids (mem (ref a))

/--
Julia source: base/abstractarray.jl:1629-1629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(::AbstractRange) = ()
```
-/
def dataidsRange {A : Type} (_a : A) : List (JInt .u64) := []

/--
Julia source: base/abstractarray.jl:1630-1630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(x) = ()
```
-/
def dataidsOther {A : Type} (_a : A) : List (JInt .u64) := []

/--
Julia source: base/abstractarray.jl:1637-1637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(A::AbstractArray, i::Integer, default) = checkbounds(Bool, A, i) ? A[i] : default
```
-/
def getDefaultScalar {m : Type → Type} [Monad m] {A I E : Type}
    (checkbounds : A → I → m Bool) (get : A → I → m E)
    (a : A) (i : I) (default : E) : m E := do
  if ← checkbounds a i then get a i else pure default

/--
Julia source: base/abstractarray.jl:1638-1638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(A::AbstractArray, I::Tuple{}, default) = checkbounds(Bool, A) ? A[] : default
```
-/
def getDefaultEmpty {m : Type → Type} [Monad m] {A E : Type}
    (checkbounds : A → m Bool) (get : A → m E) (a : A) (default : E) : m E := do
  if ← checkbounds a then get a else pure default

/--
Julia source: base/abstractarray.jl:1639-1639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(A::AbstractArray, I::Dims, default) = checkbounds(Bool, A, I...) ? A[I...] : default
```
-/
def getDefaultDims {m : Type → Type} [Monad m] {A E : Type}
    (checkbounds : A → List I64 → m Bool) (get : A → List I64 → m E)
    (a : A) (is : List I64) (default : E) : m E := do
  if ← checkbounds a is then get a is else pure default

/--
Julia source: base/abstractarray.jl:1640-1640 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Callable, A::AbstractArray, i::Integer) = checkbounds(Bool, A, i) ? A[i] : f()
```
-/
def getLazyScalar {m : Type → Type} [Monad m] {A I E : Type}
    (checkbounds : A → I → m Bool) (get : A → I → m E)
    (f : Unit → m E) (a : A) (i : I) : m E := do
  if ← checkbounds a i then get a i else f ()

/--
Julia source: base/abstractarray.jl:1641-1641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Callable, A::AbstractArray, I::Tuple{}) = checkbounds(Bool, A) ? A[] : f()
```
-/
def getLazyEmpty {m : Type → Type} [Monad m] {A E : Type}
    (checkbounds : A → m Bool) (get : A → m E)
    (f : Unit → m E) (a : A) : m E := do
  if ← checkbounds a then get a else f ()

/--
Julia source: base/abstractarray.jl:1642-1642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Callable, A::AbstractArray, I::Dims) = checkbounds(Bool, A, I...) ? A[I...] : f()
```
-/
def getLazyDims {m : Type → Type} [Monad m] {A E : Type}
    (checkbounds : A → List I64 → m Bool) (get : A → List I64 → m E)
    (f : Unit → m E) (a : A) (is : List I64) : m E := do
  if ← checkbounds a is then get a is else f ()

/--
Julia source: base/abstractarray.jl:1644-1652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(X::AbstractVector{T}, A::AbstractVector, I::Union{AbstractRange,AbstractVector{Int}}, default::T) where T
    # 1d is not linear indexing
    ind = findall(in(axes1(A)), I)
    X[ind] = A[I[ind]]
    Xind = axes1(X)
    X[first(Xind):first(ind)-1] = default
    X[last(ind)+1:last(Xind)] = default
    X
end
```
-/
def getVectorRange {m : Type → Type} [Monad m] {X A I Index Ax Pos Selected Values Span E : Type}
    (axes1A : A → m Ax) (contains : Ax → Index → m Bool)
    (findall : (Index → m Bool) → I → m Pos) (selectI : I → Pos → m Selected)
    (get : A → Selected → m Values) (set : X → Pos → Values → m Unit)
    (axes1X : X → m Ax) (firstAxis lastAxis : Ax → m I64)
    (firstPos lastPos : Pos → m I64) (span : I64 → I64 → m Span)
    (setDefault : X → Span → E → m Unit)
    (x : X) (a : A) (is : I) (default : E) : m X := do
  let ax ← axes1A a
  let ind ← findall (contains ax) is
  set x ind (← get a (← selectI is ind))
  let xind ← axes1X x
  setDefault x (← span (← firstAxis xind) ((← firstPos ind) - int 1)) default
  setDefault x (← span ((← lastPos ind) + int 1) (← lastAxis xind)) default
  return x

/--
Julia source: base/abstractarray.jl:1653-1660 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(X::AbstractArray{T}, A::AbstractArray, I::Union{AbstractRange,AbstractVector{Int}}, default::T) where T
    # Linear indexing
    ind = findall(in(1:length(A)), I)
    X[ind] = A[I[ind]]
    fill!(view(X, 1:first(ind)-1), default)
    fill!(view(X, last(ind)+1:length(X)), default)
    X
end
```
-/
def getArrayRange {m : Type → Type} [Monad m] {X A I Index Range Pos Selected Values View E : Type}
    (lengthA : A → m I64) (range : I64 → I64 → m Range)
    (contains : Range → Index → m Bool) (findall : (Index → m Bool) → I → m Pos)
    (selectI : I → Pos → m Selected) (get : A → Selected → m Values)
    (set : X → Pos → Values → m Unit) (firstPos lastPos : Pos → m I64)
    (lengthX : X → m I64) (view : X → Range → m View) (fill : View → E → m Unit)
    (x : X) (a : A) (is : I) (default : E) : m X := do
  let ax ← range (int 1) (← lengthA a)
  let ind ← findall (contains ax) is
  set x ind (← get a (← selectI is ind))
  fill (← view x (← range (int 1) ((← firstPos ind) - int 1))) default
  fill (← view x (← range ((← lastPos ind) + int 1) (← lengthX x))) default
  return x

/--
Julia source: base/abstractarray.jl:1662-1662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(A::AbstractArray, I::AbstractRange, default) = get!(similar(A, typeof(default), index_shape(I)), A, I, default)
```
-/
def getRangeDefault {m : Type → Type} [Monad m] {A I E Ty Shape X : Type}
    (typeof : E → Ty) (indexShape : I → m Shape)
    (similar : A → Ty → Shape → m X) (get : X → A → I → E → m X)
    (a : A) (is : I) (default : E) : m X := do
  let x ← similar a (typeof default) (← indexShape is)
  get x a is default

/--
Julia source: base/abstractarray.jl:1664-1669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(X::AbstractArray{T}, A::AbstractArray, I::RangeVecIntList, default::T) where T
    fill!(X, default)
    dst, src = indcopy(size(A), I)
    X[dst...] = A[src...]
    X
end
```
-/
def getIndexList {m : Type → Type} [Monad m] {X A I E Shape Dst Src Values : Type}
    (fill : X → E → m Unit) (size : A → m Shape)
    (indcopy : Shape → I → m (Dst × Src)) (get : A → Src → m Values)
    (set : X → Dst → Values → m Unit) (x : X) (a : A) (is : I) (default : E) : m X := do
  fill x default
  let (dst, src) ← indcopy (← size a) is
  set x dst (← get a src)
  return x

/--
Julia source: base/abstractarray.jl:1671-1672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(A::AbstractArray, I::RangeVecIntList, default) =
    get!(similar(A, typeof(default), index_shape(I...)), A, I, default)
```
-/
def getIndexListDefault {m : Type → Type} [Monad m] {A I E Ty Shape X : Type}
    (typeof : E → Ty) (indexShape : I → m Shape)
    (similar : A → Ty → Shape → m X) (get : X → A → I → E → m X)
    (a : A) (is : I) (default : E) : m X := do
  let x ← similar a (typeof default) (← indexShape is)
  get x a is default

/--
Julia source: base/abstractarray.jl:1675-1675 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace_in_print_matrix(A::AbstractMatrix,i::Integer,j::Integer,s::AbstractString) = s
```
-/
def replacePrintMatrix {A I J S : Type} (_a : A) (_i : I) (_j : J) (s : S) : S := s

/--
Julia source: base/abstractarray.jl:1676-1676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace_in_print_matrix(A::AbstractVector,i::Integer,j::Integer,s::AbstractString) = s
```
-/
def replacePrintVector {A I J S : Type} (_a : A) (_i : I) (_j : J) (s : S) : S := s

/--
Julia source: base/abstractarray.jl:1679-1679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltypeof(x) = typeof(x)
```
-/
def eltypeofOther {A Ty : Type} (typeof : A → Ty) (x : A) : Ty := typeof x

/--
Julia source: base/abstractarray.jl:1680-1680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltypeof(x::AbstractArray) = eltype(x)
```
-/
def eltypeofArray {A Ty : Type} (eltype : A → Ty) (x : A) : Ty := eltype x

/--
Julia source: base/abstractarray.jl:1682-1682 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltypeof() = error()
```
-/

def promoteEltypeofEmpty {Ty : Type} : Result Ty := throw (.errorException "")
/--
Julia source: base/abstractarray.jl:1683-1683 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltypeof(v1) = eltypeof(v1)
```
-/
def promoteEltypeofOne {A Ty : Type} (eltypeof : A → Result Ty) (v : A) : Result Ty :=
  eltypeof v

/--
Julia source: base/abstractarray.jl:1684-1684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltypeof(v1, v2) = promote_type(eltypeof(v1), eltypeof(v2))
```
-/

def promoteEltypeofTwo {m : Type → Type} [Monad m] {A B Ty : Type}
    (eltypeofA : A → m Ty) (eltypeofB : B → m Ty) (promote : Ty → Ty → m Ty)
    (a : A) (b : B) : m Ty := do
  let ta ← eltypeofA a
  promote ta (← eltypeofB b)
/--
Julia source: base/abstractarray.jl:1685-1685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltypeof(v1, v2, vs...) = (@inline; afoldl(((::Type{T}, y) where {T}) -> promote_type(T, eltypeof(y)), promote_eltypeof(v1, v2), vs...))
```
-/

def promoteEltypeofMany {m : Type → Type} [Monad m] {A B V Rest Ty : Type}
    (eltypeof : V → m Ty) (promote : Ty → Ty → m Ty)
    (two : A → B → m Ty)
    (afoldl : (Ty → V → m Ty) → Ty → Rest → m Ty)
    (a : A) (b : B) (vs : Rest) : m Ty := do
  afoldl (fun t y => do promote t (← eltypeof y)) (← two a b) vs
/--
Julia source: base/abstractarray.jl:1686-1686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltypeof(v1::T, vs::T...) where {T} = eltypeof(v1)
```
-/

def promoteEltypeofSame {A Rest Ty : Type} (eltypeof : A → Result Ty)
    (a : A) (_vs : Rest) : Result Ty := eltypeof a
/--
Julia source: base/abstractarray.jl:1687-1687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltypeof(v1::AbstractArray{T}, vs::AbstractArray{T}...) where {T} = T
```
-/

def promoteEltypeofArrays {A Rest Ty : Type} (elementType : Ty)
    (_a : A) (_vs : Rest) : Ty := elementType
/--
Julia source: base/abstractarray.jl:1689-1689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltype() = error()
```
-/

def promoteEltypeEmpty {Ty : Type} : Result Ty := throw (.errorException "")
/--
Julia source: base/abstractarray.jl:1690-1690 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltype(v1) = eltype(v1)
```
-/

def promoteEltypeOne {A Ty : Type} (eltype : A → Result Ty) (v : A) : Result Ty := eltype v
/--
Julia source: base/abstractarray.jl:1691-1691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltype(v1, v2) = promote_type(eltype(v1), eltype(v2))
```
-/

def promoteEltypeTwo {m : Type → Type} [Monad m] {A B Ty : Type}
    (eltypeA : A → m Ty) (eltypeB : B → m Ty) (promote : Ty → Ty → m Ty)
    (a : A) (b : B) : m Ty := do
  let ta ← eltypeA a
  promote ta (← eltypeB b)
/--
Julia source: base/abstractarray.jl:1692-1692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltype(v1, v2, vs...) = (@inline; afoldl(((::Type{T}, y) where {T}) -> promote_type(T, eltype(y)), promote_eltype(v1, v2), vs...))
```
-/

def promoteEltypeMany {m : Type → Type} [Monad m] {A B V Rest Ty : Type}
    (eltype : V → m Ty) (promote : Ty → Ty → m Ty)
    (two : A → B → m Ty)
    (afoldl : (Ty → V → m Ty) → Ty → Rest → m Ty)
    (a : A) (b : B) (vs : Rest) : m Ty := do
  afoldl (fun t y => do promote t (← eltype y)) (← two a b) vs
/--
Julia source: base/abstractarray.jl:1693-1693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltype(v1::T, vs::T...) where {T} = eltype(T)
```
-/

def promoteEltypeSame {A Rest Ty : Type} (eltype : Ty → Result Ty) (typeToken : Ty)
    (_a : A) (_vs : Rest) : Result Ty := eltype typeToken
/--
Julia source: base/abstractarray.jl:1694-1694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_eltype(v1::AbstractArray{T}, vs::AbstractArray{T}...) where {T} = T
```
-/

def promoteEltypeArrays {A Rest Ty : Type} (elementType : Ty)
    (_a : A) (_vs : Rest) : Ty := elementType
/--
Julia source: base/abstractarray.jl:1697-1697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cat(catdim::Int) = Vector{Any}()
```
-/

def catEmpty {A Ty : Type} (vector : Ty → Result A) (anyType : Ty) (_dim : I64) : Result A :=
  vector anyType
/--
Julia source: base/abstractarray.jl:1699-1699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_vcat(::Type{T}) where {T} = Vector{T}()
```
-/
def typedVcatEmpty {A Ty : Type} (vector : Ty → Result A) (t : Ty) : Result A :=
  vector t

/--
Julia source: base/abstractarray.jl:1700-1700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hcat(::Type{T}) where {T} = Vector{T}()
```
-/
def typedHcatEmpty {A Ty : Type} (vector : Ty → Result A) (t : Ty) : Result A :=
  vector t

/--
Julia source: base/abstractarray.jl:1703-1703 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(X::T...) where {T}         = T[ X[i] for i=eachindex(X) ]
```
-/
def vcatSame {X E A Ty : Type} (eachindex : X → Result (List I64))
    (get : X → I64 → Result E) (vector : Ty → List E → Result A)
    (t : Ty) (xs : X) : Result A := do
  let values ← (← eachindex xs).mapM (get xs)
  vector t values

/--
Julia source: base/abstractarray.jl:1704-1704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(X::T...) where {T<:Number} = T[ X[i] for i=eachindex(X) ]
```
-/
def vcatSameNumbers {X E A Ty : Type} (eachindex : X → Result (List I64))
    (get : X → I64 → Result E) (vector : Ty → List E → Result A)
    (t : Ty) (xs : X) : Result A := do
  let values ← (← eachindex xs).mapM (get xs)
  vector t values

/--
Julia source: base/abstractarray.jl:1705-1705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(X::T...) where {T}         = T[ X[j] for _=1:1, j=eachindex(X) ]
```
-/
def hcatSame {X E A Ty : Type} (eachindex : X → Result (List I64))
    (get : X → I64 → Result E) (matrix : Ty → I64 → List E → Result A)
    (t : Ty) (xs : X) : Result A := do
  let values ← (← eachindex xs).mapM (get xs)
  matrix t (int 1) values

/--
Julia source: base/abstractarray.jl:1706-1706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(X::T...) where {T<:Number} = T[ X[j] for _=1:1, j=eachindex(X) ]
```
-/
def hcatSameNumbers {X E A Ty : Type} (eachindex : X → Result (List I64))
    (get : X → I64 → Result E) (matrix : Ty → I64 → List E → Result A)
    (t : Ty) (xs : X) : Result A := do
  let values ← (← eachindex xs).mapM (get xs)
  matrix t (int 1) values

/--
Julia source: base/abstractarray.jl:1708-1712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function vcat(X::Number...)
    a = Vector{promote_typeof(X...)}(undef, length(X))
    hvncat_fill!(a, false, X)
    return a
end
```
-/
def vcatNumbers {m : Type → Type} [Monad m] {X A Ty : Type}
    (promoteTypeof : X → m Ty) (length : X → m I64)
    (vector : Ty → I64 → m A) (fill : A → Bool → X → m Unit) (xs : X) : m A := do
  let t ← promoteTypeof xs
  let a ← vector t (← length xs)
  fill a false xs
  return a

/--
Julia source: base/abstractarray.jl:1714-1718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hcat(X::Number...)
    a = Matrix{promote_typeof(X...)}(undef, 1, length(X))
    hvncat_fill!(a, false, X)
    return a
end
```
-/
def hcatNumbers {m : Type → Type} [Monad m] {X A Ty : Type}
    (promoteTypeof : X → m Ty) (length : X → m I64)
    (matrix : Ty → I64 → I64 → m A) (fill : A → Bool → X → m Unit)
    (xs : X) : m A := do
  let t ← promoteTypeof xs
  let a ← matrix t (int 1) (← length xs)
  fill a false xs
  return a

/--
Julia source: base/abstractarray.jl:1720-1724 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typed_vcat(::Type{T}, X::Number...) where {T}
    a = Vector{T}(undef, length(X))
    hvncat_fill!(a, false, X)
    return a
end
```
-/
def typedVcatNumbers {m : Type → Type} [Monad m] {X A Ty : Type}
    (length : X → m I64) (vector : Ty → I64 → m A)
    (fill : A → Bool → X → m Unit) (t : Ty) (xs : X) : m A := do
  let a ← vector t (← length xs)
  fill a false xs
  return a

/--
Julia source: base/abstractarray.jl:1726-1730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typed_hcat(::Type{T}, X::Number...) where {T}
    a = Matrix{T}(undef, 1, length(X))
    hvncat_fill!(a, false, X)
    return a
end
```
-/
def typedHcatNumbers {m : Type → Type} [Monad m] {X A Ty : Type}
    (length : X → m I64) (matrix : Ty → I64 → I64 → m A)
    (fill : A → Bool → X → m Unit) (t : Ty) (xs : X) : m A := do
  let a ← matrix t (int 1) (← length xs)
  fill a false xs
  return a

/--
Julia source: base/abstractarray.jl:1732-1732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(V::AbstractVector...) = typed_vcat(promote_eltype(V...), V...)
```
-/
def vcatVectors {m : Type → Type} [Monad m] {V A Ty : Type}
    (promoteEltype : V → m Ty) (typedVcat : Ty → V → m A) (vs : V) : m A := do
  typedVcat (← promoteEltype vs) vs

/--
Julia source: base/abstractarray.jl:1733-1733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(V::AbstractVector{T}...) where {T} = typed_vcat(T, V...)
```
-/
def vcatVectorsSame {m : Type → Type} [Monad m] {V A Ty : Type}
    (typedVcat : Ty → V → m A) (t : Ty) (vs : V) : m A := typedVcat t vs

/--
Julia source: base/abstractarray.jl:1740-1740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_vcat_similar(V, ::Type{T}, n) where T = similar(V[1], T, n)
```
-/
def typedVcatSimilar {m : Type → Type} [Monad m] {V A B Ty N : Type}
    (get : V → I64 → m A) (similar : A → Ty → N → m B)
    (vs : V) (t : Ty) (n : N) : m B := do
  similar (← get vs (int 1)) t n

/--
Julia source: base/abstractarray.jl:1741-1742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_vcat(::Type{T}, V::AbstractVecOrTuple{AbstractVector}) where T =
    _typed_vcat!(_typed_vcat_similar(V, T, sum(map(length, V))), V)
```
-/

def typedVcatVectors {m : Type → Type} [Monad m] {V A B Ty N Sizes : Type}
    (length : A → m N) (map : (A → m N) → V → m Sizes)
    (sum : Sizes → m N) (similar : V → Ty → N → m B)
    (fill : B → V → m B) (t : Ty) (vs : V) : m B := do
  fill (← similar vs t (← sum (← map length vs))) vs
/--
Julia source: base/abstractarray.jl:1744-1753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_vcat!(a::AbstractVector{T}, V::AbstractVecOrTuple{AbstractVector}) where T
    pos = 1
    for k=1:Int(length(V))::Int
        Vk = V[k]
        p1 = pos + Int(length(Vk))::Int - 1
        a[pos:p1] = Vk
        pos = p1+1
    end
    a
end
```
-/
def typedVcatFill {m : Type → Type} [Monad m] {V A B R : Type}
    (lengthV : V → m I64) (range : I64 → I64 → m (List I64))
    (get : V → I64 → m A) (lengthA : A → m I64)
    (slice : I64 → I64 → m R) (set : B → R → A → m Unit)
    (a : B) (vs : V) : m B := do
  let mut pos := int 1
  for k in (← range (int 1) (← lengthV vs)) do
    let vk ← get vs k
    let p1 := pos + (← lengthA vk) - int 1
    set a (← slice pos p1) vk
    pos := p1 + int 1
  return a

/--
Julia source: base/abstractarray.jl:1755-1755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hcat(::Type{T}, A::AbstractVecOrMat...) where {T} = _typed_hcat(T, A)
```
-/
def typedHcatArrays {m : Type → Type} [Monad m] {V A Ty : Type}
    (typedHcat : Ty → V → m A) (t : Ty) (vs : V) : m A := typedHcat t vs

/--
Julia source: base/abstractarray.jl:1759-1762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hcat(::AbstractArray, other...) = throw(ArgumentError("It is unclear whether you \
    intend to perform an indexing operation or typed concatenation. If you intend to \
    perform indexing (v[1 + 2]), adjust spacing or insert missing operator to clarify. \
    If you intend to perform typed concatenation (T[1 2]), ensure that T is a type."))
```
-/
def typedHcatNotType {A Other B : Type} (_a : A) (_other : Other) : Result B :=
  throw (.julia (.argumentError "It is unclear whether you intend to perform an indexing operation or typed concatenation. If you intend to perform indexing (v[1 + 2]), adjust spacing or insert missing operator to clarify. If you intend to perform typed concatenation (T[1 2]), ensure that T is a type."))

/--
Julia source: base/abstractarray.jl:1765-1765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(A::AbstractVecOrMat...) = typed_hcat(promote_eltype(A...), A...)
```
-/
def hcatArrays {m : Type → Type} [Monad m] {V A Ty : Type}
    (promoteEltype : V → m Ty) (typedHcat : Ty → V → m A) (vs : V) : m A := do
  typedHcat (← promoteEltype vs) vs

/--
Julia source: base/abstractarray.jl:1766-1766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(A::AbstractVecOrMat{T}...) where {T} = typed_hcat(T, A...)
```
-/
def hcatArraysSame {m : Type → Type} [Monad m] {V A Ty : Type}
    (typedHcat : Ty → V → m A) (t : Ty) (vs : V) : m A := typedHcat t vs

/--
Julia source: base/abstractarray.jl:1768-1800 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hcat(::Type{T}, A::AbstractVecOrTuple{AbstractVecOrMat}) where T
    nargs = length(A)
    nrows = size(A[1], 1)
    ncols = 0
    dense = true
    for j = 1:nargs
        Aj = A[j]
        if size(Aj, 1) != nrows
            throw(DimensionMismatch("number of rows of each array must match (got $(map(x->size(x,1), A)))"))
        end
        dense &= isa(Aj,Array)
        nd = ndims(Aj)
        ncols += (nd==2 ? size(Aj,2) : 1)
    end
    B = similar(A[1], T, nrows, ncols)
    pos = 1
    if dense
        for k=1:nargs
            Ak = A[k]
            n = length(Ak)
            copyto!(B, pos, Ak, 1, n)
            pos += n
        end
    else
        for k=1:nargs
            Ak = A[k]
            p1 = pos+(isa(Ak,AbstractMatrix) ? size(Ak, 2) : 1)-1
            B[:, pos:p1] = Ak
            pos = p1+1
        end
    end
    return B
end
```
-/
def typedHcat {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {V A B Ty R : Type}
    (lengthV : V → m I64) (get : V → I64 → m A)
    (size : A → I64 → m I64) (ndims : A → m I64) (isArray isMatrix : A → Bool)
    (range : I64 → I64 → m (List I64)) (showRows : V → m String)
    (similar : A → Ty → I64 → I64 → m B) (lengthA : A → m I64)
    (copyto : B → I64 → A → I64 → I64 → m B)
    (slice : I64 → I64 → m R) (set : B → R → A → m Unit)
    (t : Ty) (as : V) : m B := do
  let nargs ← lengthV as
  let nrows ← size (← get as (int 1)) (int 1)
  let mut ncols := int 0
  let mut dense := true
  for j in (← range (int 1) nargs) do
    let aj ← get as j
    if (← size aj (int 1)).val != nrows.val then
      throw (.dimensionMismatch ("number of rows of each array must match (got " ++
        (← showRows as) ++ ")"))
    dense := dense && isArray aj
    let nd ← ndims aj
    ncols := ncols + (← if nd.val == 2 then size aj (int 2) else pure (int 1))
  let b ← similar (← get as (int 1)) t nrows ncols
  let mut pos := int 1
  if dense then
    for k in (← range (int 1) nargs) do
      let ak ← get as k
      let n ← lengthA ak
      let _ ← copyto b pos ak (int 1) n
      pos := pos + n
  else
    for k in (← range (int 1) nargs) do
      let ak ← get as k
      let n ← if isMatrix ak then size ak (int 2) else pure (int 1)
      let p1 := pos + n - int 1
      set b (← slice pos p1) ak
      pos := p1 + int 1
  return b

/--
Julia source: base/abstractarray.jl:1802-1802 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(A::AbstractVecOrMat...) = typed_vcat(promote_eltype(A...), A...)
```
-/
def vcatArrays {m : Type → Type} [Monad m] {V A Ty : Type}
    (promoteEltype : V → m Ty) (typedVcat : Ty → V → m A) (as : V) : m A := do
  typedVcat (← promoteEltype as) as

/--
Julia source: base/abstractarray.jl:1803-1803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(A::AbstractVecOrMat{T}...) where {T} = typed_vcat(T, A...)
```
-/
def vcatArraysSame {m : Type → Type} [Monad m] {V A Ty : Type}
    (typedVcat : Ty → V → m A) (t : Ty) (as : V) : m A := typedVcat t as

/--
Julia source: base/abstractarray.jl:1805-1823 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_vcat(::Type{T}, A::AbstractVecOrTuple{AbstractVecOrMat}) where T
    nargs = length(A)
    nrows = sum(a->size(a, 1), A)::Int
    ncols = size(A[1], 2)
    for j = 2:nargs
        if size(A[j], 2) != ncols
            throw(DimensionMismatch("number of columns of each array must match (got $(map(x->size(x,2), A)))"))
        end
    end
    B = similar(A[1], T, nrows, ncols)
    pos = 1
    for k=1:nargs
        Ak = A[k]
        p1 = pos+size(Ak,1)::Int-1
        B[pos:p1, :] = Ak
        pos = p1+1
    end
    return B
end
```
-/
def typedVcat {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {V A B Ty R : Type} (lengthV : V → m I64) (get : V → I64 → m A)
    (size : A → I64 → m I64) (sum : (A → m I64) → V → m I64)
    (range : I64 → I64 → m (List I64)) (showCols : V → m String)
    (similar : A → Ty → I64 → I64 → m B)
    (slice : I64 → I64 → m R) (set : B → R → A → m Unit)
    (t : Ty) (as : V) : m B := do
  let nargs ← lengthV as
  let nrows ← sum (fun a => size a (int 1)) as
  let ncols ← size (← get as (int 1)) (int 2)
  for j in (← range (int 2) nargs) do
    if (← size (← get as j) (int 2)).val != ncols.val then
      throw (.dimensionMismatch ("number of columns of each array must match (got " ++
        (← showCols as) ++ ")"))
  let b ← similar (← get as (int 1)) t nrows ncols
  let mut pos := int 1
  for k in (← range (int 1) nargs) do
    let ak ← get as k
    let p1 := pos + (← size ak (int 1)) - int 1
    set b (← slice pos p1) ak
    pos := p1 + int 1
  return b

/--
Julia source: base/abstractarray.jl:1825-1825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_vcat(::Type{T}, A::AbstractVecOrMat...) where {T} = _typed_vcat(T, A)
```
-/
def typedVcatArrays {m : Type → Type} [Monad m] {V A Ty : Type}
    (typedVcat : Ty → V → m A) (t : Ty) (as : V) : m A := typedVcat t as

/--
Julia source: base/abstractarray.jl:1827-1828 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce(::typeof(vcat), A::AbstractVector{<:AbstractVecOrMat}) =
    _typed_vcat(mapreduce(eltype, promote_type, A), A)
```
-/
def reduceVcat {m : Type → Type} [Monad m] {V A B Ty : Type}
    (eltype : A → m Ty) (promote : Ty → Ty → m Ty)
    (mapreduce : (A → m Ty) → (Ty → Ty → m Ty) → V → m Ty)
    (typedVcat : Ty → V → m B) (as : V) : m B := do
  typedVcat (← mapreduce eltype promote as) as

/--
Julia source: base/abstractarray.jl:1830-1831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce(::typeof(hcat), A::AbstractVector{<:AbstractVecOrMat}) =
    _typed_hcat(mapreduce(eltype, promote_type, A), A)
```
-/
def reduceHcat {m : Type → Type} [Monad m] {V A B Ty : Type}
    (eltype : A → m Ty) (promote : Ty → Ty → m Ty)
    (mapreduce : (A → m Ty) → (Ty → Ty → m Ty) → V → m Ty)
    (typedHcat : Ty → V → m B) (as : V) : m B := do
  typedHcat (← mapreduce eltype promote as) as

/--
Julia source: base/abstractarray.jl:1836-1836 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_size(A) = (1,)
```
-/
def catSizeScalar (_a : A) : List I64 := [int 1]

/--
Julia source: base/abstractarray.jl:1837-1837 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_size(A::AbstractArray) = size(A)
```
-/
def catSizeArray {Shape : Type} (size : A → Result Shape) (a : A) : Result Shape := size a

/--
Julia source: base/abstractarray.jl:1838-1838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_size(A, d) = 1
```
-/
def catSizeDimScalar (_a : A) (_d : D) : I64 := int 1

/--
Julia source: base/abstractarray.jl:1839-1839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_size(A::AbstractArray, d) = size(A, d)
```
-/
def catSizeDimArray (size : A → D → Result I64) (a : A) (d : D) : Result I64 := size a d

/--
Julia source: base/abstractarray.jl:1841-1841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_length(::Any) = 1
```
-/
def catLengthScalar (_a : A) : I64 := int 1

/--
Julia source: base/abstractarray.jl:1842-1842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_length(a::AbstractArray) = length(a)
```
-/
def catLengthArray (length : A → Result I64) (a : A) : Result I64 := length a

/--
Julia source: base/abstractarray.jl:1844-1844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_ndims(a) = 0
```
-/
def catNdimsScalar (_a : A) : I64 := int 0

/--
Julia source: base/abstractarray.jl:1845-1845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_ndims(a::AbstractArray) = ndims(a)
```
-/
def catNdimsArray (ndims : A → Result I64) (a : A) : Result I64 := ndims a

/--
Julia source: base/abstractarray.jl:1847-1847 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_indices(A, d) = OneTo(1)
```
-/
def catIndicesScalar {Axis : Type} (oneTo : I64 → Result Axis)
    (_a : A) (_d : D) : Result Axis := oneTo (int 1)

/--
Julia source: base/abstractarray.jl:1848-1848 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_indices(A::AbstractArray, d) = axes(A, d)
```
-/
def catIndicesArray {Axis : Type} (axes : A → D → Result Axis)
    (a : A) (d : D) : Result Axis := axes a d

/--
Julia source: base/abstractarray.jl:1850-1850 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_similar(A, ::Type{T}, shape::Tuple) where T = Array{T}(undef, shape)
```
-/
def catSimilarTuple {Ty Shape B : Type} (array : Ty → Shape → Result B)
    (_a : A) (t : Ty) (shape : Shape) : Result B := array t shape

/--
Julia source: base/abstractarray.jl:1851-1851 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_similar(A, ::Type{T}, shape::Vector) where T = Array{T}(undef, shape...)
```
-/
def catSimilarVector {Ty Shape B : Type} (arrayVarargs : Ty → Shape → Result B)
    (_a : A) (t : Ty) (shape : Shape) : Result B := arrayVarargs t shape

/--
Julia source: base/abstractarray.jl:1852-1852 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_similar(A::Array, ::Type{T}, shape::Tuple) where T = Array{T}(undef, shape)
```
-/
def catSimilarArrayTuple {Ty Shape B : Type} (array : Ty → Shape → Result B)
    (_a : A) (t : Ty) (shape : Shape) : Result B := array t shape

/--
Julia source: base/abstractarray.jl:1853-1853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_similar(A::Array, ::Type{T}, shape::Vector) where T = Array{T}(undef, shape...)
```
-/
def catSimilarArrayVector {Ty Shape B : Type} (arrayVarargs : Ty → Shape → Result B)
    (_a : A) (t : Ty) (shape : Shape) : Result B := arrayVarargs t shape

/--
Julia source: base/abstractarray.jl:1854-1854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_similar(A::AbstractArray, T::Type, shape::Tuple) = similar(A, T, shape)
```
-/
def catSimilarAbstractTuple {Ty : Type u} {Shape B : Type} (similar : A → Ty → Shape → Result B)
    (a : A) (t : Ty) (shape : Shape) : Result B := similar a t shape

/--
Julia source: base/abstractarray.jl:1855-1855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_similar(A::AbstractArray, T::Type, shape::Vector) = similar(A, T, shape...)
```
-/
def catSimilarAbstractVector {Shape B : Type} (similarVarargs : A → Type → Shape → Result B)
    (a : A) (t : Type) (shape : Shape) : Result B := similarVarargs a t shape

/--
Julia source: base/abstractarray.jl:1858-1858 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_shape(dims, shape::Tuple{Vararg{Int}}) = shape
```
-/
def catShapeInt (_dims : D) (shape : List I64) : List I64 := shape

/--
Julia source: base/abstractarray.jl:1859-1865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cat_shape(dims, shapes::Tuple)
    out_shape = ()
    for s in shapes
        out_shape = _cshp(1, dims, out_shape, s)
    end
    return out_shape
end
```
-/
def catShape (combine : I64 → List Bool → List I64 → List I64 → Result (List I64))
    (dims : List Bool) (shapes : List (List I64)) : Result (List I64) := do
  let mut out := []
  for s in shapes do out ← combine (int 1) dims out s
  return out

/--
Julia source: base/abstractarray.jl:1867-1867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_size_shape(dims) = ntuple(Returns(0), Val(length(dims)))
```
-/
def catSizeShapeEmpty (dims : List Bool) : List I64 := List.replicate dims.length (int 0)

/--
Julia source: base/abstractarray.jl:1868-1868 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline cat_size_shape(dims, X, tail...) = _cat_size_shape(dims, _cshp(1, dims, (), cat_size(X)), tail...)
```
-/
def catSizeShape {X Rest : Type} (catSize : X → Result (List I64))
    (combine : I64 → List Bool → List I64 → List I64 → Result (List I64))
    (recurse : List Bool → List I64 → Rest → Result (List I64))
    (dims : List Bool) (x : X) (tail : Rest) : Result (List I64) := do
  recurse dims (← combine (int 1) dims [] (← catSize x)) tail

/--
Julia source: base/abstractarray.jl:1869-1869 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cat_size_shape(dims, shape) = shape
```
-/
def catSizeShapeDone (_dims : List Bool) (shape : List I64) : List I64 := shape

/--
Julia source: base/abstractarray.jl:1870-1870 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _cat_size_shape(dims, shape, X, tail...) = _cat_size_shape(dims, _cshp(1, dims, shape, cat_size(X)), tail...)
```
-/
def catSizeShapeMore {X Rest : Type} (catSize : X → Result (List I64))
    (combine : I64 → List Bool → List I64 → List I64 → Result (List I64))
    (recurse : List Bool → List I64 → Rest → Result (List I64))
    (dims : List Bool) (shape : List I64) (x : X) (tail : Rest) : Result (List I64) := do
  recurse dims (← combine (int 1) dims shape (← catSize x)) tail

/--
Julia source: base/abstractarray.jl:1872-1872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cshp(ndim::Int, ::Tuple{}, ::Tuple{}, ::Tuple{}) = ()
```
-/
def cshpEmpty (_ndim : I64) : List I64 := []

/--
Julia source: base/abstractarray.jl:1873-1873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cshp(ndim::Int, ::Tuple{}, ::Tuple{}, nshape) = nshape
```
-/
def cshpInitial (_ndim : I64) (nshape : List I64) : List I64 := nshape

/--
Julia source: base/abstractarray.jl:1874-1874 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cshp(ndim::Int, dims, ::Tuple{}, ::Tuple{}) = ntuple(Returns(1), Val(length(dims)))
```
-/
def cshpPad (_ndim : I64) (dims : List Bool) : List I64 :=
  List.replicate dims.length (int 1)

/--
Julia source: base/abstractarray.jl:1875-1876 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _cshp(ndim::Int, dims, shape, ::Tuple{}) =
    (shape[1] + dims[1], _cshp(ndim + 1, tail(dims), tail(shape), ())...)
```
-/
def cshpTrailing
    (recurse : I64 → List Bool → List I64 → List I64 → Result (List I64))
    (ndim : I64) (dims : Bool × List Bool) (shape : I64 × List I64) : Result (List I64) := do
  let first := shape.1 + int (if dims.1 then 1 else 0)
  return first :: (← recurse (ndim + int 1) dims.2 shape.2 [])

/--
Julia source: base/abstractarray.jl:1877-1878 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _cshp(ndim::Int, dims, ::Tuple{}, nshape) =
    (nshape[1], _cshp(ndim + 1, tail(dims), (), tail(nshape))...)
```
-/
def cshpLeading
    (recurse : I64 → List Bool → List I64 → List I64 → Result (List I64))
    (ndim : I64) (dims : Bool × List Bool) (nshape : I64 × List I64) : Result (List I64) := do
  return nshape.1 :: (← recurse (ndim + int 1) dims.2 [] nshape.2)

/--
Julia source: base/abstractarray.jl:1879-1882 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _cshp(ndim::Int, ::Tuple{}, shape, ::Tuple{})
    _cs(ndim, shape[1], 1)
    (1, _cshp(ndim + 1, (), tail(shape), ())...)
end
```
-/
def cshpMissing
    (check : I64 → I64 → I64 → Result I64)
    (recurse : I64 → List Bool → List I64 → List I64 → Result (List I64))
    (ndim : I64) (shape : I64 × List I64) : Result (List I64) := do
  let _ ← check ndim shape.1 (int 1)
  return int 1 :: (← recurse (ndim + int 1) [] shape.2 [])

/--
Julia source: base/abstractarray.jl:1883-1886 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _cshp(ndim::Int, ::Tuple{}, shape, nshape)
    next = _cs(ndim, shape[1], nshape[1])
    (next, _cshp(ndim + 1, (), tail(shape), tail(nshape))...)
end
```
-/
def cshpEqual
    (check : I64 → I64 → I64 → Result I64)
    (recurse : I64 → List Bool → List I64 → List I64 → Result (List I64))
    (ndim : I64) (shape nshape : I64 × List I64) : Result (List I64) := do
  let next ← check ndim shape.1 nshape.1
  return next :: (← recurse (ndim + int 1) [] shape.2 nshape.2)

/--
Julia source: base/abstractarray.jl:1887-1892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _cshp(ndim::Int, dims, shape, nshape)
    a = shape[1]
    b = nshape[1]
    next = dims[1] ? a + b : _cs(ndim, a, b)
    (next, _cshp(ndim + 1, tail(dims), tail(shape), tail(nshape))...)
end
```
-/
def cshpMerge
    (check : I64 → I64 → I64 → Result I64)
    (recurse : I64 → List Bool → List I64 → List I64 → Result (List I64))
    (ndim : I64) (dims : Bool × List Bool) (shape nshape : I64 × List I64) :
    Result (List I64) := do
  let a := shape.1
  let b := nshape.1
  let next ← if dims.1 then pure (a + b) else check ndim a b
  return next :: (← recurse (ndim + int 1) dims.2 shape.2 nshape.2)

/--
Julia source: base/abstractarray.jl:1894-1895 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cs(d, a, b) = (a == b ? a : throw(DimensionMismatch(
    "mismatch in dimension $d (expected $a got $b)")))
```
-/
def catCheckDim (d a b : I64) : Result I64 :=
  if a.val = b.val then pure a
  else throw (.dimensionMismatch ("mismatch in dimension " ++ toString d.val ++
    " (expected " ++ toString a.val ++ " got " ++ toString b.val ++ ")"))

/--
Julia source: base/abstractarray.jl:1897-1897 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dims2cat(::Val{dims}) where dims = dims2cat(dims)
```
-/
def dimsToCatVal {D : Type} (dimsToCat : D → Result (List Bool)) (dims : D) :
    Result (List Bool) := dimsToCat dims

/--
Julia source: base/abstractarray.jl:1898-1903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dims2cat(dims)
    if any(≤(0), dims)
        throw(ArgumentError("All cat dimensions must be positive integers, but got $dims"))
    end
    ntuple(in(dims), maximum(dims))
end
```
-/
def dimsToCat {D : Type} (any : (I64 → Bool) → D → Result Bool)
    (maximum : D → Result I64) (contains : I64 → D → Bool)
    (ntuple : (I64 → Bool) → I64 → Result (List Bool)) (showDims : D → String)
    (dims : D) : Result (List Bool) := do
  if ← any (fun d => decide (d.val ≤ 0)) dims then
    throw (.julia (.argumentError
      ("All cat dimensions must be positive integers, but got " ++ showDims dims)))
  ntuple (fun i => contains i dims) (← maximum dims)

/--
Julia source: base/abstractarray.jl:1905-1905 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cat(dims, X...) = _cat_t(dims, promote_eltypeof(X...), X...)
```
-/
def catPromote {m : Type → Type} [Monad m] {D Ty X A : Type}
    (promoteEltypeof : X → m Ty) (catT : D → Ty → X → m A)
    (dims : D) (xs : X) : m A := do
  catT dims (← promoteEltypeof xs) xs

/--
Julia source: base/abstractarray.jl:1907-1915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _cat_t(dims, ::Type{T}, X...) where {T}
    catdims = dims2cat(dims)
    shape = cat_size_shape(catdims, X...)
    A = cat_similar(X[1], T, shape)
    if count(!iszero, catdims)::Int > 1
        fill!(A, zero(T))
    end
    return __cat(A, shape, catdims, X...)
end
```
-/
def catTyped {m : Type → Type} [Monad m] {D Ty X E A B : Type}
    (dimsToCat : D → m (List Bool)) (sizeShape : List Bool → X → m (List I64))
    (first : X → m E) (similar : E → Ty → List I64 → m A)
    (count : (Bool → Bool) → List Bool → m I64)
    (zero : Ty → m B) (fill : A → B → m Unit)
    (cat : A → List I64 → List Bool → X → m A)
    (dims : D) (t : Ty) (xs : X) : m A := do
  let catdims ← dimsToCat dims
  let shape ← sizeShape catdims xs
  let a ← similar (← first xs) t shape
  if (← count (fun b => b) catdims).val > 1 then
    fill a (← zero t)
  cat a shape catdims xs

/--
Julia source: base/abstractarray.jl:1918-1918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline cat_t(::Type{T}, X...; dims) where {T} = _cat_t(dims, T, X...)
```
-/
def catTypedKeyword {m : Type → Type} [Monad m] {D Ty X A : Type}
    (catT : D → Ty → X → m A) (t : Ty) (xs : X) (dims : D) : m A :=
  catT dims t xs

/--
Julia source: base/abstractarray.jl:1921-1921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__cat(A, shape, catdims, X...) = __cat_offset!(A, shape, catdims, ntuple(Returns(0), length(shape)), X...)
```
-/
def catInner {m : Type → Type} [Monad m] {A X : Type}
    (offset : A → List I64 → List Bool → List I64 → X → m A)
    (a : A) (shape : List I64) (dims : List Bool) (xs : X) : m A :=
  offset a shape dims (List.replicate shape.length (int 0)) xs

/--
Julia source: base/abstractarray.jl:1923-1927 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __cat_offset!(A, shape, catdims, offsets, x, X...)
    # splitting the "work" on x from X... may reduce latency (fewer costly specializations)
    newoffsets = __cat_offset1!(A, shape, catdims, offsets, x)
    return __cat_offset!(A, shape, catdims, newoffsets, X...)
end
```
-/
def catOffsetMore {m : Type → Type} [Monad m] {A X Rest : Type}
    (one : A → List I64 → List Bool → List I64 → X → m (List I64))
    (recurse : A → List I64 → List Bool → List I64 → Rest → m A)
    (a : A) (shape : List I64) (dims : List Bool) (offsets : List I64)
    (x : X) (xs : Rest) : m A := do
  let newoffsets ← one a shape dims offsets x
  recurse a shape dims newoffsets xs

/--
Julia source: base/abstractarray.jl:1928-1928 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__cat_offset!(A, shape, catdims, offsets) = A
```
-/
def catOffsetDone {A : Type} (a : A) (_shape : List I64)
    (_dims : List Bool) (_offsets : List I64) : A := a

/--
Julia source: base/abstractarray.jl:1930-1939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __cat_offset1!(A, shape, catdims, offsets, x)
    inds = ntuple(length(offsets)) do i
        (i <= length(catdims) && catdims[i]) ? offsets[i] .+ cat_indices(x, i) : 1:shape[i]
    end
    _copy_or_fill!(A, inds, x)
    newoffsets = ntuple(length(offsets)) do i
        (i <= length(catdims) && catdims[i]) ? offsets[i] + cat_size(x, i) : offsets[i]
    end
    return newoffsets
end
```
-/
def catOffsetOne {m : Type → Type} [Monad m] {A X Axis R : Type}
    (getBool : List Bool → I64 → m Bool) (getInt : List I64 → I64 → m I64)
    (ntupleR : (I64 → m R) → Nat → m (List R))
    (ntupleI : (I64 → m I64) → Nat → m (List I64))
    (indices : X → I64 → m Axis) (shift : I64 → Axis → m R)
    (range : I64 → I64 → m R) (size : X → I64 → m I64)
    (copyOrFill : A → List R → X → m Unit)
    (a : A) (shape : List I64) (dims : List Bool) (offsets : List I64) (x : X) :
    m (List I64) := do
  let inds ← ntupleR (fun i => do
    let catdim ← if i.val ≤ (dims.length : Int) then getBool dims i else pure false
    if catdim then shift (← getInt offsets i) (← indices x i)
    else range (int 1) (← getInt shape i)) offsets.length
  copyOrFill a inds x
  let newoffsets ← ntupleI (fun i => do
    let catdim ← if i.val ≤ (dims.length : Int) then getBool dims i else pure false
    if catdim then return (← getInt offsets i) + (← size x i)
    else getInt offsets i) offsets.length
  return newoffsets

/--
Julia source: base/abstractarray.jl:1941-1941 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_copy_or_fill!(A, inds, x) = fill!(view(A, inds...), x)
```
-/
def copyOrFillScalar {m : Type → Type} [Monad m] {A I X V : Type}
    (view : A → I → m V) (fill : V → X → m Unit) (a : A) (inds : I) (x : X) :
    m Unit := do
  fill (← view a inds) x

/--
Julia source: base/abstractarray.jl:1942-1942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_copy_or_fill!(A, inds, x::AbstractArray) = (A[inds...] = x)
```
-/
def copyOrFillArray {m : Type → Type} [Monad m] {A I X : Type}
    (set : A → I → X → m Unit) (a : A) (inds : I) (x : X) : m Unit :=
  set a inds x

/--
Julia source: base/abstractarray.jl:2003-2003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(X...) = cat(X...; dims=Val(1))
```
-/
def vcatAny {m : Type → Type} [Monad m] {X A : Type}
    (cat : X → I64 → m A) (xs : X) : m A := cat xs (int 1)

/--
Julia source: base/abstractarray.jl:2053-2053 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(X...) = cat(X...; dims=Val(2))
```
-/
def hcatAny {m : Type → Type} [Monad m] {X A : Type}
    (cat : X → I64 → m A) (xs : X) : m A := cat xs (int 2)

/--
Julia source: base/abstractarray.jl:2055-2055 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_vcat(::Type{T}, X...) where T = _cat_t(Val(1), T, X...)
```
-/
def typedVcatAny {m : Type → Type} [Monad m] {Ty X A : Type}
    (catT : I64 → Ty → X → m A) (t : Ty) (xs : X) : m A := catT (int 1) t xs

/--
Julia source: base/abstractarray.jl:2056-2056 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hcat(::Type{T}, X...) where T = _cat_t(Val(2), T, X...)
```
-/
def typedHcatAny {m : Type → Type} [Monad m] {Ty X A : Type}
    (catT : I64 → Ty → X → m A) (t : Ty) (xs : X) : m A := catT (int 2) t xs

/--
Julia source: base/abstractarray.jl:2169-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline cat(A...; dims) = _cat(dims, A...)
```
-/
def catKeyword {m : Type → Type} [Monad m] {D X A : Type}
    (cat : D → X → m A) (xs : X) (dims : D) : m A := cat dims xs

/--
Julia source: base/abstractarray.jl:2171-2171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive _cat(catdims, A::AbstractArray{T}...) where {T} = _cat_t(catdims, T, A...)
```
-/
def catSameArrays {m : Type → Type} [Monad m] {D Ty X A : Type}
    (catT : D → Ty → X → m A) (dims : D) (t : Ty) (xs : X) : m A := catT dims t xs

/--
Julia source: base/abstractarray.jl:2175-2175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(A::AbstractArray) = cat(A; dims=Val(1))
```
-/
def vcatOneArray {m : Type → Type} [Monad m] {A B : Type}
    (cat : List A → I64 → m B) (a : A) : m B := cat [a] (int 1)

/--
Julia source: base/abstractarray.jl:2176-2176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(A::AbstractArray, B::AbstractArray) = cat(A, B; dims=Val(1))
```
-/
def vcatTwoArrays {m : Type → Type} [Monad m] {A B C : Type}
    (cat : A × B → I64 → m C) (a : A) (b : B) : m C := cat (a, b) (int 1)

/--
Julia source: base/abstractarray.jl:2177-2177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(A::AbstractArray...) = cat(A...; dims=Val(1))
```
-/
def vcatArrayVarargs {m : Type → Type} [Monad m] {X A : Type}
    (cat : X → I64 → m A) (xs : X) : m A := cat xs (int 1)

/--
Julia source: base/abstractarray.jl:2178-2178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(A::Union{AbstractArray,Number}...) = cat(A...; dims=Val(1))
```
-/
def vcatMixed {m : Type → Type} [Monad m] {X A : Type}
    (cat : X → I64 → m A) (xs : X) : m A := cat xs (int 1)

/--
Julia source: base/abstractarray.jl:2179-2179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(A::AbstractArray) = cat(A; dims=Val(2))
```
-/
def hcatOneArray {m : Type → Type} [Monad m] {A B : Type}
    (cat : List A → I64 → m B) (a : A) : m B := cat [a] (int 2)

/--
Julia source: base/abstractarray.jl:2180-2180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(A::AbstractArray, B::AbstractArray) = cat(A, B; dims=Val(2))
```
-/
def hcatTwoArrays {m : Type → Type} [Monad m] {A B C : Type}
    (cat : A × B → I64 → m C) (a : A) (b : B) : m C := cat (a, b) (int 2)

/--
Julia source: base/abstractarray.jl:2181-2181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(A::AbstractArray...) = cat(A...; dims=Val(2))
```
-/
def hcatArrayVarargs {m : Type → Type} [Monad m] {X A : Type}
    (cat : X → I64 → m A) (xs : X) : m A := cat xs (int 2)

/--
Julia source: base/abstractarray.jl:2182-2182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(A::Union{AbstractArray,Number}...) = cat(A...; dims=Val(2))
```
-/
def hcatMixed {m : Type → Type} [Monad m] {X A : Type}
    (cat : X → I64 → m A) (xs : X) : m A := cat xs (int 2)

/--
Julia source: base/abstractarray.jl:2184-2184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_vcat(T::Type, A::AbstractArray) = _cat_t(Val(1), T, A)
```
-/
def typedVcatOneArray {m : Type → Type} [Monad m] {Ty A B : Type}
    (catT : I64 → Ty → List A → m B) (t : Ty) (a : A) : m B := catT (int 1) t [a]

/--
Julia source: base/abstractarray.jl:2185-2185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_vcat(T::Type, A::AbstractArray, B::AbstractArray) = _cat_t(Val(1), T, A, B)
```
-/
def typedVcatTwoArrays {m : Type → Type} [Monad m] {Ty A B C : Type}
    (catT : I64 → Ty → A × B → m C) (t : Ty) (a : A) (b : B) : m C :=
  catT (int 1) t (a, b)

/--
Julia source: base/abstractarray.jl:2186-2186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_vcat(T::Type, A::AbstractArray...) = _cat_t(Val(1), T, A...)
```
-/
def typedVcatArrayVarargs {m : Type → Type} [Monad m] {Ty X A : Type}
    (catT : I64 → Ty → X → m A) (t : Ty) (xs : X) : m A := catT (int 1) t xs

/--
Julia source: base/abstractarray.jl:2187-2187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hcat(T::Type, A::AbstractArray) = _cat_t(Val(2), T, A)
```
-/
def typedHcatOneArray {m : Type → Type} [Monad m] {Ty A B : Type}
    (catT : I64 → Ty → List A → m B) (t : Ty) (a : A) : m B := catT (int 2) t [a]

/--
Julia source: base/abstractarray.jl:2188-2188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hcat(T::Type, A::AbstractArray, B::AbstractArray) = _cat_t(Val(2), T, A, B)
```
-/
def typedHcatTwoArrays {m : Type → Type} [Monad m] {Ty A B C : Type}
    (catT : I64 → Ty → A × B → m C) (t : Ty) (a : A) (b : B) : m C :=
  catT (int 2) t (a, b)

/--
Julia source: base/abstractarray.jl:2189-2189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hcat(T::Type, A::AbstractArray...) = _cat_t(Val(2), T, A...)
```
-/
def typedHcatArrayVarargs {m : Type → Type} [Monad m] {Ty X A : Type}
    (catT : I64 → Ty → X → m A) (t : Ty) (xs : X) : m A := catT (int 2) t xs

/--
Julia source: base/abstractarray.jl:2194-2194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hvcat_rows(rows::Tuple...) = hvcat(map(length, rows), (rows...)...)
```
-/
def hvcatRows {m : Type → Type} [Monad m] {Rows Shape X A : Type}
    (mapLengths : Rows → m Shape) (flatten : Rows → m X)
    (hvcat : Shape → X → m A) (rows : Rows) : m A := do
  hvcat (← mapLengths rows) (← flatten rows)

/--
Julia source: base/abstractarray.jl:2195-2195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hvcat_rows(T::Type, rows::Tuple...) = typed_hvcat(T, map(length, rows), (rows...)...)
```
-/
def typedHvcatRows {m : Type → Type} [Monad m] {Ty Rows Shape X A : Type}
    (mapLengths : Rows → m Shape) (flatten : Rows → m X)
    (hvcat : Ty → Shape → X → m A) (t : Ty) (rows : Rows) : m A := do
  hvcat t (← mapLengths rows) (← flatten rows)

/--
Julia source: base/abstractarray.jl:2197-2204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hvcat(nbc::Int, as...)
    # nbc = # of block columns
    n = length(as)
    mod(n,nbc) != 0 &&
        throw(ArgumentError("number of arrays $n is not a multiple of the requested number of block columns $nbc"))
    nbr = div(n,nbc)
    hvcat(ntuple(Returns(nbc), nbr), as...)
end
```
-/
def hvcatColumns {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {X A : Type}
    (length : X → m I64) (mod div : I64 → I64 → m I64)
    (ntuple : I64 → I64 → m (List I64)) (hvcat : List I64 → X → m A)
    (nbc : I64) (xs : X) : m A := do
  let n ← length xs
  if (← mod n nbc).val != 0 then
    throw (.julia (.argumentError ("number of arrays " ++ toString n.val ++
      " is not a multiple of the requested number of block columns " ++ toString nbc.val)))
  let nbr ← div n nbc
  hvcat (← ntuple nbc nbr) xs

/--
Julia source: base/abstractarray.jl:2244-2244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hvcat(rows::Tuple{Vararg{Int}}, xs::AbstractArray...) = typed_hvcat(promote_eltype(xs...), rows, xs...)
```
-/
def hvcatArrays {m : Type → Type} [Monad m] {Ty Rows X A : Type}
    (promoteEltype : X → m Ty) (hvcat : Ty → Rows → X → m A)
    (rows : Rows) (xs : X) : m A := do
  hvcat (← promoteEltype xs) rows xs

/--
Julia source: base/abstractarray.jl:2245-2245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hvcat(rows::Tuple{Vararg{Int}}, xs::AbstractArray{T}...) where {T} = typed_hvcat(T, rows, xs...)
```
-/
def hvcatSameArrays {m : Type → Type} [Monad m] {Ty Rows X A : Type}
    (hvcat : Ty → Rows → X → m A) (t : Ty) (rows : Rows) (xs : X) : m A :=
  hvcat t rows xs

/--
Julia source: base/abstractarray.jl:2247-2247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rows_to_dimshape(rows::Tuple{Vararg{Int}}) = all(==(rows[1]), rows) ? (length(rows), rows[1]) : (rows, (sum(rows),))
```
-/
def rowsToDimshape (get : List I64 → I64 → Result I64)
    (sum : List I64 → Result I64) (rows : List I64) :
    Result (Sum (I64 × I64) (List I64 × List I64)) := do
  let first ← get rows (int 1)
  if rows.all (fun n => n.val == first.val) then
    return .inl (int rows.length, ← get rows (int 1))
  else return .inr (rows, [← sum rows])

/--
Julia source: base/abstractarray.jl:2248-2248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hvcat(::Type{T}, rows::Tuple{Vararg{Int}}, as::AbstractVecOrMat...) where T = typed_hvncat(T, rows_to_dimshape(rows), true, as...)
```
-/
def typedHvcatArrays {m : Type → Type} [Monad m] {Ty Rows Shape X A : Type}
    (rowsToShape : Rows → m Shape) (hvncat : Ty → Shape → Bool → X → m A)
    (t : Ty) (rows : Rows) (xs : X) : m A := do
  hvncat t (← rowsToShape rows) true xs

/--
Julia source: base/abstractarray.jl:2250-2250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hvcat(rows::Tuple{Vararg{Int}}) = []
```
-/
def hvcatEmpty {Rows A : Type} (vectorAny : Result A) (_rows : Rows) : Result A :=
  vectorAny

/--
Julia source: base/abstractarray.jl:2251-2251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hvcat(::Type{T}, rows::Tuple{Vararg{Int}}) where {T} = Vector{T}()
```
-/
def typedHvcatEmpty {Ty Rows A : Type} (vector : Ty → Result A)
    (t : Ty) (_rows : Rows) : Result A := vector t

/--
Julia source: base/abstractarray.jl:2253-2272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hvcat(rows::Tuple{Vararg{Int}}, xs::T...) where T<:Number
    nr = length(rows)
    nc = rows[1]

    a = Matrix{T}(undef, nr, nc)
    if length(a) != length(xs)
        throw(ArgumentError("argument count does not match specified shape (expected $(length(a)), got $(length(xs)))"))
    end
    k = 1
    @inbounds for i=1:nr
        if nc != rows[i]
            throw(DimensionMismatch("row $(i) has mismatched number of columns (expected $nc, got $(rows[i]))"))
        end
        for j=1:nc
            a[i,j] = xs[k]
            k += 1
        end
    end
    a
end
```
-/
def hvcatSameNumbers {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Rows X Ty E A : Type} (lengthRows : Rows → m I64) (getRow : Rows → I64 → m I64)
    (matrix : Ty → I64 → I64 → m A) (lengthA : A → m I64) (lengthX : X → m I64)
    (range : I64 → I64 → m (List I64)) (get : X → I64 → m E)
    (set : A → I64 → I64 → E → m Unit)
    (t : Ty) (rows : Rows) (xs : X) : m A := do
  let nr ← lengthRows rows
  let nc ← getRow rows (int 1)
  let a ← matrix t nr nc
  if (← lengthA a).val != (← lengthX xs).val then
    throw (.julia (.argumentError ("argument count does not match specified shape (expected " ++
      toString (← lengthA a).val ++ ", got " ++ toString (← lengthX xs).val ++ ")")))
  let mut k := int 1
  for i in (← range (int 1) nr) do
    if nc.val != (← getRow rows i).val then
      throw (.dimensionMismatch ("row " ++ toString i.val ++
        " has mismatched number of columns (expected " ++ toString nc.val ++
        ", got " ++ toString (← getRow rows i).val ++ ")"))
    for j in (← range (int 1) nc) do
      set a i j (← get xs k)
      k := k + int 1
  return a

/--
Julia source: base/abstractarray.jl:2274-2274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hvcat(rows::Tuple{Vararg{Int}}, xs::Number...) = typed_hvcat(promote_typeof(xs...), rows, xs...)
```
-/
def hvcatNumbers {m : Type → Type} [Monad m] {Ty Rows X A : Type}
    (promoteTypeof : X → m Ty) (hvcat : Ty → Rows → X → m A)
    (rows : Rows) (xs : X) : m A := do
  hvcat (← promoteTypeof xs) rows xs

/--
Julia source: base/abstractarray.jl:2275-2275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hvcat(rows::Tuple{Vararg{Int}}, xs...) = typed_hvcat(promote_eltypeof(xs...), rows, xs...)
```
-/
def hvcatAny {m : Type → Type} [Monad m] {Ty Rows X A : Type}
    (promoteEltypeof : X → m Ty) (hvcat : Ty → Rows → X → m A)
    (rows : Rows) (xs : X) : m A := do
  hvcat (← promoteEltypeof xs) rows xs

/--
Julia source: base/abstractarray.jl:2277-2277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hvcat(rows::Tuple{Vararg{Int}}, xs::Union{AbstractArray,Number}...) = typed_hvcat(promote_eltypeof(xs...), rows, xs...)
```
-/
def hvcatMixed {m : Type → Type} [Monad m] {Ty Rows X A : Type}
    (promoteEltypeof : X → m Ty) (hvcat : Ty → Rows → X → m A)
    (rows : Rows) (xs : X) : m A := do
  hvcat (← promoteEltypeof xs) rows xs

/--
Julia source: base/abstractarray.jl:2279-2290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typed_hvcat(::Type{T}, rows::Tuple{Vararg{Int}}, xs::Number...) where T
    nr = length(rows)
    nc = rows[1]
    for i = 2:nr
        if nc != rows[i]
            throw(DimensionMismatch("row $(i) has mismatched number of columns (expected $nc, got $(rows[i]))"))
        end
    end
    a = Matrix{T}(undef, nr, nc)
    hvncat_fill!(a, true, xs)
    return a
end
```
-/
def typedHvcatNumbers {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Rows X Ty A : Type} (lengthRows : Rows → m I64) (getRow : Rows → I64 → m I64)
    (range : I64 → I64 → m (List I64)) (matrix : Ty → I64 → I64 → m A)
    (fill : A → Bool → X → m Unit) (t : Ty) (rows : Rows) (xs : X) : m A := do
  let nr ← lengthRows rows
  let nc ← getRow rows (int 1)
  for i in (← range (int 2) nr) do
    if nc.val != (← getRow rows i).val then
      throw (.dimensionMismatch ("row " ++ toString i.val ++
        " has mismatched number of columns (expected " ++ toString nc.val ++
        ", got " ++ toString (← getRow rows i).val ++ ")"))
  let a ← matrix t nr nc
  fill a true xs
  return a

/--
Julia source: base/abstractarray.jl:2292-2292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hvcat(::Type{T}, rows::Tuple{Vararg{Int}}, as...) where T = typed_hvncat(T, rows_to_dimshape(rows), true, as...)
```
-/
def typedHvcatAny {m : Type → Type} [Monad m] {Ty Rows Shape X A : Type}
    (rowsToShape : Rows → m Shape) (hvncat : Ty → Shape → Bool → X → m A)
    (t : Ty) (rows : Rows) (xs : X) : m A := do
  hvncat t (← rowsToShape rows) true xs

/--
Julia source: base/abstractarray.jl:2381-2381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hvncat(dimsshape::Tuple, row_first::Bool, xs...) = _hvncat(dimsshape, row_first, xs...)
```
-/
def hvncatTuple {m : Type → Type} {Shape X A : Type}
    (hvncat : Shape → Bool → X → m A) (shape : Shape) (rowFirst : Bool) (xs : X) : m A :=
  hvncat shape rowFirst xs

/--
Julia source: base/abstractarray.jl:2382-2382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hvncat(dim::Int, xs...) = _hvncat(dim, true, xs...)
```
-/
def hvncatDim {m : Type → Type} {X A : Type}
    (hvncat : I64 → Bool → X → m A) (dim : I64) (xs : X) : m A :=
  hvncat dim true xs

/--
Julia source: base/abstractarray.jl:2384-2384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool) = _typed_hvncat(Any, dimsshape, row_first)
```
-/
def hvncatEmpty {m : Type → Type} {Ty Shape A : Type}
    (typed : Ty → Shape → Bool → m A) (anyType : Ty) (shape : Shape) (rowFirst : Bool) :
    m A := typed anyType shape rowFirst

/--
Julia source: base/abstractarray.jl:2385-2385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool, xs...) = _typed_hvncat(promote_eltypeof(xs...), dimsshape, row_first, xs...)
```
-/
def hvncatPromote {m : Type → Type} [Monad m] {Ty Shape X A : Type}
    (promoteEltypeof : X → m Ty) (typed : Ty → Shape → Bool → X → m A)
    (shape : Shape) (rowFirst : Bool) (xs : X) : m A := do
  typed (← promoteEltypeof xs) shape rowFirst xs

/--
Julia source: base/abstractarray.jl:2386-2386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool, xs::T...) where T<:Number = _typed_hvncat(T, dimsshape, row_first, xs...)
```
-/
def hvncatSameNumbers {m : Type → Type} {Ty Shape X A : Type}
    (typed : Ty → Shape → Bool → X → m A)
    (t : Ty) (shape : Shape) (rowFirst : Bool) (xs : X) : m A :=
  typed t shape rowFirst xs

/--
Julia source: base/abstractarray.jl:2387-2387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool, xs::Number...) = _typed_hvncat(promote_typeof(xs...), dimsshape, row_first, xs...)
```
-/
def hvncatNumbers {m : Type → Type} [Monad m] {Ty Shape X A : Type}
    (promoteTypeof : X → m Ty) (typed : Ty → Shape → Bool → X → m A)
    (shape : Shape) (rowFirst : Bool) (xs : X) : m A := do
  typed (← promoteTypeof xs) shape rowFirst xs

/--
Julia source: base/abstractarray.jl:2388-2388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool, xs::AbstractArray...) = _typed_hvncat(promote_eltype(xs...), dimsshape, row_first, xs...)
```
-/
def hvncatArrays {m : Type → Type} [Monad m] {Ty Shape X A : Type}
    (promoteEltype : X → m Ty) (typed : Ty → Shape → Bool → X → m A)
    (shape : Shape) (rowFirst : Bool) (xs : X) : m A := do
  typed (← promoteEltype xs) shape rowFirst xs

/--
Julia source: base/abstractarray.jl:2389-2389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool, xs::AbstractArray{T}...) where T = _typed_hvncat(T, dimsshape, row_first, xs...)
```
-/
def hvncatSameArrays {m : Type → Type} {Ty Shape X A : Type}
    (typed : Ty → Shape → Bool → X → m A)
    (t : Ty) (shape : Shape) (rowFirst : Bool) (xs : X) : m A :=
  typed t shape rowFirst xs

/--
Julia source: base/abstractarray.jl:2392-2392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hvncat(T::Type, dimsshape::Tuple, row_first::Bool, xs...) = _typed_hvncat(T, dimsshape, row_first, xs...)
```
-/
def typedHvncatTuple {m : Type → Type} {Ty Shape X A : Type}
    (typed : Ty → Shape → Bool → X → m A)
    (t : Ty) (shape : Shape) (rowFirst : Bool) (xs : X) : m A :=
  typed t shape rowFirst xs

/--
Julia source: base/abstractarray.jl:2393-2393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typed_hvncat(T::Type, dim::Int, xs...) = _typed_hvncat(T, Val(dim), xs...)
```
-/
def typedHvncatDim {m : Type → Type} {Ty X A : Type}
    (typed : Ty → I64 → X → m A) (t : Ty) (dim : I64) (xs : X) : m A :=
  typed t dim xs

/--
Julia source: base/abstractarray.jl:2397-2397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(::Type, ::Val{0}) = _typed_hvncat_0d_only_one()
```
-/
def typedHvncatZeroEmpty {Ty A : Type} (onlyOne : Result A) (_t : Ty) : Result A :=
  onlyOne

/--
Julia source: base/abstractarray.jl:2398-2398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(T::Type, ::Val{0}, x) = fill(convert(T, x))
```
-/
def typedHvncatZeroScalar {m : Type → Type} [Monad m] {Ty X E A : Type}
    (convert : Ty → X → m E) (fill : E → m A) (t : Ty) (x : X) : m A := do
  fill (← convert t x)

/--
Julia source: base/abstractarray.jl:2399-2399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(T::Type, ::Val{0}, x::Number) = fill(convert(T, x))
```
-/
def typedHvncatZeroNumber {m : Type → Type} [Monad m] {Ty X E A : Type}
    (convert : Ty → X → m E) (fill : E → m A) (t : Ty) (x : X) : m A := do
  fill (← convert t x)

/--
Julia source: base/abstractarray.jl:2400-2400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(T::Type, ::Val{0}, x::AbstractArray) = convert.(T, x)
```
-/
def typedHvncatZeroArray {m : Type → Type} {Ty X A : Type}
    (broadcastConvert : Ty → X → m A) (t : Ty) (x : X) : m A := broadcastConvert t x

/--
Julia source: base/abstractarray.jl:2401-2401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(::Type, ::Val{0}, ::Any...) = _typed_hvncat_0d_only_one()
```
-/
def typedHvncatZeroAnyMany {Ty X A : Type} (onlyOne : Result A) (_t : Ty) (_xs : X) :
    Result A := onlyOne

/--
Julia source: base/abstractarray.jl:2402-2402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(::Type, ::Val{0}, ::Number...) = _typed_hvncat_0d_only_one()
```
-/
def typedHvncatZeroNumbersMany {Ty X A : Type} (onlyOne : Result A) (_t : Ty) (_xs : X) :
    Result A := onlyOne

/--
Julia source: base/abstractarray.jl:2403-2403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(::Type, ::Val{0}, ::AbstractArray...) = _typed_hvncat_0d_only_one()
```
-/
def typedHvncatZeroArraysMany {Ty X A : Type} (onlyOne : Result A) (_t : Ty) (_xs : X) :
    Result A := onlyOne

/--
Julia source: base/abstractarray.jl:2405-2406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat_0d_only_one() =
    throw(ArgumentError("a 0-dimensional array may only contain exactly one element"))
```
-/
def typedHvncatZeroOnlyOne {A : Type} : Result A :=
  throw (.julia (.argumentError "a 0-dimensional array may only contain exactly one element"))

/--
Julia source: base/abstractarray.jl:2409-2409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive _typed_hvncat(T::Type, dim::Int, ::Bool, xs...) = _typed_hvncat(T, Val(dim), xs...) # catches from _hvncat type promoters
```
-/
def typedHvncatDimFlag {m : Type → Type} {Ty X A : Type}
    (typed : Ty → I64 → X → m A) (t : Ty) (dim : I64) (_rowFirst : Bool) (xs : X) :
    m A := typed t dim xs

/--
Julia source: base/abstractarray.jl:2411-2415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat(::Type{T}, ::Val{N}) where {T, N}
    N < 0 &&
        throw(ArgumentError("concatenation dimension must be non-negative"))
    return Array{T, N}(undef, ntuple(Returns(0), Val(N)))
end
```
-/
def typedHvncatEmptyVal {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty N Shape A : Type} (negative : N → m Bool) (zeros : N → m Shape)
    (array : Ty → N → Shape → m A) (t : Ty) (n : N) : m A := do
  if ← negative n then
    throw (.julia (.argumentError "concatenation dimension must be non-negative"))
  array t n (← zeros n)

/--
Julia source: base/abstractarray.jl:2417-2421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat(T::Type, ::Val{N}, xs::Number...) where N
    N < 0 &&
        throw(ArgumentError("concatenation dimension must be non-negative"))
    return reshape(T[xs...], (ntuple(Returns(1), Val(N - 1))..., length(xs)))
end
```
-/
def typedHvncatNumbersVal {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty N Count X V A : Type} (negative : N → m Bool) (subOne : N → m Count)
    (ones : Count → m (List I64)) (length : X → m I64)
    (vector : Ty → X → m V) (reshape : V → List I64 → m A)
    (t : Ty) (n : N) (xs : X) : m A := do
  if ← negative n then
    throw (.julia (.argumentError "concatenation dimension must be non-negative"))
  let values ← vector t xs
  let shape ← ones (← subOne n)
  reshape values (shape ++ [← length xs])

/--
Julia source: base/abstractarray.jl:2423-2456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat(::Type{T}, ::Val{N}, as::AbstractArray...) where {T, N}
    # optimization for arrays that can be concatenated by copying them linearly into the destination
    # conditions: the elements must all have 1-length dimensions above N
    length(as) > 0 ||
        throw(ArgumentError("must have at least one element"))
    N < 0 &&
        throw(ArgumentError("concatenation dimension must be non-negative"))
    for a ∈ as
        ndims(a) <= N || all(x -> size(a, x) == 1, (N + 1):ndims(a)) ||
            return _typed_hvncat(T, (ntuple(Returns(1), Val(N - 1))..., length(as), 1), false, as...)
            # the extra 1 is to avoid an infinite cycle
    end

    nd = N

    Ndim = 0
    for i ∈ eachindex(as)
        Ndim += cat_size(as[i], N)
        nd = max(nd, cat_ndims(as[i]))
        for d ∈ 1:N - 1
            cat_size(as[1], d) == cat_size(as[i], d) || throw(DimensionMismatch("mismatched size along axis $d in element $i"))
        end
    end

    A = cat_similar(as[1], T, (ntuple(d -> size(as[1], d), N - 1)..., Ndim, ntuple(Returns(1), nd - N)...))
    k = 1
    for a ∈ as
        for i ∈ eachindex(a)
            A[k] = a[i]
            k += 1
        end
    end
    return A
end
```
-/
def typedHvncatArraysVal {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty N P A B I E : Type} (negative : N → m Bool)
    (le : I64 → N → m Bool) (addOne subOne : N → m P)
    (sub : Sum N P → N → m P) (maxRank : Sum N P → I64 → m P)
    (showDim : P → String)
    (rangeAfter : P → I64 → m (List P)) (rangeBefore : I64 → P → m (List P))
    (all : (P → m Bool) → List P → m Bool)
    (ndims catNdims : A → m I64)
    (sizeOther catSizeOther : A → P → m I64)
    (size : A → I64 → m I64) (catSize : A → N → m I64)
    (ones : P → m (List I64)) (ntuple : (I64 → m I64) → P → m (List I64))
    (typed : Ty → List I64 → Bool → List A → m B)
    (tupleIndices : List A → m (List I64)) (tupleGet : List A → I64 → m A)
    (similar : A → Ty → List I64 → m B)
    (eachindex : A → m (List I)) (get : A → I → m E)
    (set : B → I64 → E → m Unit) (t : Ty) (n : N) (as : List A) : m B := do
  if as.isEmpty then
    throw (.julia (.argumentError "must have at least one element"))
  if ← negative n then
    throw (.julia (.argumentError "concatenation dimension must be non-negative"))
  for a in as do
    if !(← le (← ndims a) n) then
      if !(← all (fun d => do return (← sizeOther a d).val == 1)
          (← rangeAfter (← addOne n) (← ndims a))) then
        return ← typed t ((← ones (← subOne n)) ++ [int as.length, int 1]) false as
  let mut nd : Sum N P := .inl n
  let mut ndim := int 0
  for i in (← tupleIndices as) do
    ndim := ndim + (← catSize (← tupleGet as i) n)
    nd := .inr (← maxRank nd (← catNdims (← tupleGet as i)))
    for d in (← rangeBefore (int 1) (← subOne n)) do
      if (← catSizeOther (← tupleGet as (int 1)) d).val !=
          (← catSizeOther (← tupleGet as i) d).val then
        throw (.dimensionMismatch ("mismatched size along axis " ++ showDim d ++
          " in element " ++ toString i.val))
  let a ← similar (← tupleGet as (int 1)) t
    ((← ntuple (fun d => do size (← tupleGet as (int 1)) d) (← subOne n)) ++
      [ndim] ++ (← ones (← sub nd n)))
  let mut k := int 1
  for source in as do
    for i in (← eachindex source) do
      set a k (← get source i)
      k := k + int 1
  return a

/--
Julia source: base/abstractarray.jl:2458-2488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat(::Type{T}, ::Val{N}, as...) where {T, N}
    length(as) > 0 ||
        throw(ArgumentError("must have at least one element"))
    N < 0 &&
        throw(ArgumentError("concatenation dimension must be non-negative"))
    nd = N
    Ndim = 0
    for i ∈ eachindex(as)
        Ndim += cat_size(as[i], N)
        nd = max(nd, cat_ndims(as[i]))
        for d ∈ 1:N-1
            cat_size(as[i], d) == 1 ||
                throw(DimensionMismatch("all dimensions of element $i other than $N must be of length 1"))
        end
    end

    A = Array{T, nd}(undef, ntuple(Returns(1), Val(N - 1))..., Ndim, ntuple(Returns(1), nd - N)...)

    k = 1
    for a ∈ as
        if a isa AbstractArray
            lena = length(a)
            copyto!(A, k, a, 1, lena)
            k += lena
        else
            A[k] = a
            k += 1
        end
    end
    return A
end
```
-/
def typedHvncatMixedVal {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty N P X A : Type} (negative : N → m Bool)
    (subOne : N → m P) (sub : Sum N P → N → m P)
    (maxRank : Sum N P → I64 → m P) (showDim : N → String)
    (range : I64 → P → m (List P)) (ones : P → m (List I64))
    (tupleIndices : List X → m (List I64)) (tupleGet : List X → I64 → m X)
    (catSize : X → N → m I64) (catSizeOther : X → P → m I64)
    (catNdims : X → m I64)
    (array : Ty → Sum N P → List I64 → m A) (isArray : X → Bool)
    (length : X → m I64) (copyto : A → I64 → X → I64 → I64 → m A)
    (set : A → I64 → X → m Unit) (t : Ty) (n : N) (as : List X) : m A := do
  if as.isEmpty then
    throw (.julia (.argumentError "must have at least one element"))
  if ← negative n then
    throw (.julia (.argumentError "concatenation dimension must be non-negative"))
  let mut nd : Sum N P := .inl n
  let mut ndim := int 0
  for i in (← tupleIndices as) do
    ndim := ndim + (← catSize (← tupleGet as i) n)
    nd := .inr (← maxRank nd (← catNdims (← tupleGet as i)))
    for d in (← range (int 1) (← subOne n)) do
      if (← catSizeOther (← tupleGet as i) d).val != 1 then
        throw (.dimensionMismatch ("all dimensions of element " ++ toString i.val ++
          " other than " ++ showDim n ++ " must be of length 1"))
  let a ← array t nd ((← ones (← subOne n)) ++ [ndim] ++ (← ones (← sub nd n)))
  let mut k := int 1
  for source in as do
    if isArray source then
      let len ← length source
      let _ ← copyto a k source (int 1) len
      k := k + len
    else
      set a k source
      k := k + int 1
  return a

/--
Julia source: base/abstractarray.jl:2492-2492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(T::Type, ::Tuple{}, ::Bool, x...) = _typed_hvncat(T, Val(0), x...)
```
-/
def typedHvncatEmptyShape {m : Type → Type} [Monad m] {Ty X A : Type}
    (typed : Ty → I64 → X → m A) (t : Ty) (_rowFirst : Bool) (xs : X) : m A :=
  typed t (int 0) xs

/--
Julia source: base/abstractarray.jl:2493-2493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(T::Type, ::Tuple{}, ::Bool, x::Number...) = _typed_hvncat(T, Val(0), x...)
```
-/
def typedHvncatEmptyShapeNumbers {m : Type → Type} [Monad m] {Ty X A : Type}
    (typed : Ty → I64 → X → m A) (t : Ty) (_rowFirst : Bool) (xs : X) : m A :=
  typed t (int 0) xs

/--
Julia source: base/abstractarray.jl:2498-2498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(T::Type, dims::Tuple{Int}, ::Bool, as...) = _typed_hvncat_1d(T, dims[1], Val(false), as...)
```
-/
def typedHvncatOneShape {m : Type → Type} [Monad m] {Ty X A : Type}
    (get : List I64 → I64 → m I64) (typed : Ty → I64 → Bool → X → m A)
    (t : Ty) (dims : List I64) (_rowFirst : Bool) (xs : X) : m A := do
  typed t (← get dims (int 1)) false xs

/--
Julia source: base/abstractarray.jl:2499-2499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_hvncat(T::Type, dims::Tuple{Int}, ::Bool, as::Number...) = _typed_hvncat_1d(T, dims[1], Val(false), as...)
```
-/
def typedHvncatOneShapeNumbers {m : Type → Type} [Monad m] {Ty X A : Type}
    (get : List I64 → I64 → m I64) (typed : Ty → I64 → Bool → X → m A)
    (t : Ty) (dims : List I64) (_rowFirst : Bool) (xs : X) : m A := do
  typed t (← get dims (int 1)) false xs

/--
Julia source: base/abstractarray.jl:2501-2512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat_1d(::Type{T}, ds::Int, ::Val{row_first}, as...) where {T, row_first}
    lengthas = length(as)
    ds > 0 ||
        throw(ArgumentError("`dimsshape` argument must consist of positive integers"))
    lengthas == ds ||
        throw(ArgumentError("number of elements does not match `dimshape` argument; expected $ds, got $lengthas"))
    if row_first
        return _typed_hvncat(T, Val(2), as...)
    else
        return _typed_hvncat(T, Val(1), as...)
    end
end
```
-/
def typedHvncatOneDim {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty X A : Type} (length : X → m I64) (typed : Ty → I64 → X → m A)
    (t : Ty) (ds : I64) (rowFirst : Bool) (xs : X) : m A := do
  let len ← length xs
  if ds.val ≤ 0 then
    throw (.julia (.argumentError "`dimsshape` argument must consist of positive integers"))
  if len.val != ds.val then
    throw (.julia (.argumentError ("number of elements does not match `dimshape` argument; expected " ++
      toString ds.val ++ ", got " ++ toString len.val)))
  if rowFirst then return ← typed t (int 2) xs
  else return ← typed t (int 1) xs

/--
Julia source: base/abstractarray.jl:2514-2525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat(::Type{T}, dims::NTuple{N, Int}, row_first::Bool, xs::Number...) where {T, N}
    all(>(0), dims) ||
        throw(ArgumentError("`dims` argument must contain positive integers"))
    A = Array{T, N}(undef, dims...)
    lengtha = length(A)  # Necessary to store result because throw blocks are being deoptimized right now, which leads to excessive allocations
    lengthx = length(xs) # Cuts from 3 allocations to 1.
    if lengtha != lengthx
       throw(ArgumentError("argument count does not match specified shape (expected $lengtha, got $lengthx)"))
    end
    hvncat_fill!(A, row_first, xs)
    return A
end
```
-/
def typedHvncatNumbersDims {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty X A : Type} (array : Ty → Nat → List I64 → m A)
    (lengthArray : A → m I64) (lengthArgs : X → m I64)
    (fill : A → Bool → X → m Unit)
    (t : Ty) (dims : List I64) (rowFirst : Bool) (xs : X) : m A := do
  if !(dims.all fun d => decide (0 < d.val)) then
    throw (.julia (.argumentError "`dims` argument must contain positive integers"))
  let a ← array t dims.length dims
  let lengtha ← lengthArray a
  let lengthx ← lengthArgs xs
  if lengtha.val != lengthx.val then
    throw (.julia (.argumentError ("argument count does not match specified shape (expected " ++
      toString lengtha.val ++ ", got " ++ toString lengthx.val ++ ")")))
  fill a rowFirst xs
  return a

/--
Julia source: base/abstractarray.jl:2527-2554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hvncat_fill_loop!(A::Array, row_first::Bool, xs::Tuple)
    nr, nc = size(A, 1), size(A, 2)
    na = prod(size(A)[3:end])
    len = length(xs)
    nrc = nr * nc
    if nrc * na != len
        throw(ArgumentError("argument count $(len) does not match specified shape $(size(A))"))
    end
    # putting these in separate functions leads to unnecessary allocations
    if row_first
        k = 1
        for d ∈ 1:na
            dd = nrc * (d - 1)
            for i ∈ 1:nr
                Ai = dd + i
                for _ ∈ 1:nc
                    @inbounds A[Ai] = xs[k]
                    k += 1
                    Ai += nr
                end
            end
        end
    else
        for k ∈ eachindex(xs)
            @inbounds A[k] = xs[k]
        end
    end
end
```
-/
def hvncatFillLoop {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A X E : Type} (size : A → I64 → m I64) (tailProduct : A → m I64)
    (length : X → m I64) (showShape : A → m String)
    (range : I64 → I64 → m (List I64)) (eachindex : X → m (List I64))
    (get : X → I64 → m E) (set : A → I64 → E → m Unit)
    (a : A) (rowFirst : Bool) (xs : X) : m Unit := do
  let nr ← size a (int 1)
  let nc ← size a (int 2)
  let na ← tailProduct a
  let len ← length xs
  let nrc := nr * nc
  if (nrc * na).val != len.val then
    throw (.julia (.argumentError ("argument count " ++ toString len.val ++
      " does not match specified shape " ++ (← showShape a))))
  if rowFirst then
    let mut k := int 1
    for d in (← range (int 1) na) do
      let dd := nrc * (d - int 1)
      for i in (← range (int 1) nr) do
        let mut ai := dd + i
        for _ in (← range (int 1) nc) do
          set a ai (← get xs k)
          k := k + int 1
          ai := ai + nr
  else
    for k in (← eachindex xs) do
      set a k (← get xs k)

/--
Julia source: base/abstractarray.jl:2556-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hvncat_fill!(A::Array, row_first::Bool, xs::Tuple)
    if @generated
        N = fieldcount(xs)
        N > 32 && return :(return _hvncat_fill_loop!(A, row_first, xs))
        nd = ndims(A)
        if nd <= 2
            return quote
                nr = size(A, 1)
                nc = size(A, 2)
                if nr*nc != $N
                    throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
                end
                if row_first
                    i::Int = 1
                    j::Int = 1
                    @nexprs $N k -> begin
                        @inbounds A[i, j] = xs[k]
                        j += 1
                        if j > nc
                            i += 1
                            j = 1
                        end
                    end
                else
                    @nexprs $N k -> begin
                        @inbounds A[k] = xs[k]
                    end
                end
                nothing
            end
        else
            return quote
                nr = size(A, 1)
                nc = size(A, 2)
                nrc = nr * nc
                na = prod(size(A)[3:end])
                if nrc * na != $N
                    throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
                end
                if row_first
                    d::Int = 1
                    i::Int = 1
                    dd::Int = 0
                    Ai::Int = dd + i
                    j::Int = 1
                    @nexprs $N k -> begin
                        @inbounds A[Ai] = xs[k]
                        j += 1
                        Ai += nr
                        if j > nc
                            j = 1
                            i += 1
                            if i > nr
                                i = 1
                                d += 1
                                dd = nrc * (d - 1)
                            end
                            Ai = dd + i
                        end
                    end
                else
                    @nexprs $N k -> begin
                        @inbounds A[k] = xs[k]
                    end
                end
                nothing
            end
        end
    else
        _hvncat_fill_loop!(A, row_first, xs)
    end
end
```
-/
def hvncatFill {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A X E : Type} (generated : Bool) (fieldcount rank : Nat)
    (size : A → I64 → m I64) (tailProduct : A → m I64)
    (showShape : A → m String) (get : X → I64 → m E)
    (set : A → I64 → E → m Unit) (set2 : A → I64 → I64 → E → m Unit)
    (loop : A → Bool → X → m Unit) (a : A) (rowFirst : Bool) (xs : X) : m Unit := do
  if !generated then return ← loop a rowFirst xs
  if fieldcount > 32 then return ← loop a rowFirst xs
  let nr ← size a (int 1)
  let nc ← size a (int 2)
  if rank ≤ 2 then
    if (nr * nc).val != (fieldcount : Int) then
      throw (.julia (.argumentError ("argument count " ++ toString fieldcount ++
        " does not match specified shape " ++ (← showShape a))))
    if rowFirst then
      let mut i := int 1
      let mut j := int 1
      for k in List.range fieldcount do
        set2 a i j (← get xs (int ((k : Int) + 1)))
        j := j + int 1
        if j.val > nc.val then
          i := i + int 1
          j := int 1
    else
      for k in List.range fieldcount do
        set a (int ((k : Int) + 1)) (← get xs (int ((k : Int) + 1)))
  else
    let nrc := nr * nc
    let na ← tailProduct a
    if (nrc * na).val != (fieldcount : Int) then
      throw (.julia (.argumentError ("argument count " ++ toString fieldcount ++
        " does not match specified shape " ++ (← showShape a))))
    if rowFirst then
      let mut d := int 1
      let mut i := int 1
      let mut dd := int 0
      let mut ai := dd + i
      let mut j := int 1
      for k in List.range fieldcount do
        set a ai (← get xs (int ((k : Int) + 1)))
        j := j + int 1
        ai := ai + nr
        if j.val > nc.val then
          j := int 1
          i := i + int 1
          if i.val > nr.val then
            i := int 1
            d := d + int 1
            dd := nrc * (d - int 1)
          ai := dd + i
    else
      for k in List.range fieldcount do
        set a (int ((k : Int) + 1)) (← get xs (int ((k : Int) + 1)))

/--
Julia source: base/abstractarray.jl:2629-2633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat(T::Type, dims::NTuple{N, Int}, row_first::Bool, as...) where {N}
    # function barrier after calculating the max is necessary for high performance
    nd = max(maximum(cat_ndims(a) for a ∈ as), N)
    return _typed_hvncat_dims(T, (dims..., ntuple(Returns(1), nd - N)...), row_first, as)
end
```
-/
def typedHvncatMixedDims {m : Type → Type} [Monad m] {Ty X A : Type}
    (catNdims : X → m I64) (maximum : (X → m I64) → List X → m I64)
    (ones : I64 → m (List I64))
    (typed : Ty → List I64 → Bool → List X → m A)
    (t : Ty) (dims : List I64) (rowFirst : Bool) (as : List X) : m A := do
  let nd := int (max (← maximum catNdims as).val (dims.length : Int))
  typed t (dims ++ (← ones (nd - int dims.length))) rowFirst as

/--
Julia source: base/abstractarray.jl:2635-2727 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat_dims(::Type{T}, dims::NTuple{N, Int}, row_first::Bool, as::Tuple) where {T, N}
    length(as) > 0 ||
        throw(ArgumentError("must have at least one element"))
    all(>(0), dims) ||
        throw(ArgumentError("`dims` argument must contain positive integers"))

    d1 = row_first ? 2 : 1
    d2 = row_first ? 1 : 2

    outdims = zeros(Int, N)

    # validate shapes for lowest level of concatenation
    d = findfirst(>(1), dims)
    if d !== nothing # all dims are 1
        if row_first && d < 3
            d = d == 1 ? 2 : 1
        end
        nblocks = length(as) ÷ dims[d]
        for b ∈ 1:nblocks
            offset = ((b - 1) * dims[d])
            startelementi = offset + 1
            for i ∈ offset .+ (2:dims[d])
                for dd ∈ 1:N
                    dd == d && continue
                    if cat_size(as[startelementi], dd) != cat_size(as[i], dd)
                        throw(DimensionMismatch("incompatible shape in element $i"))
                    end
                end
            end
        end
    end

    # discover number of rows or columns
    # d1 dimension is increased by 1 to appropriately handle 0-length arrays
    for i ∈ 1:dims[d1]
        outdims[d1] = checked_add(outdims[d1], cat_size(as[i], d1))
    end

    # adjustment to handle 0-length arrays
    first_dim_zero = outdims[d1] == 0
    if first_dim_zero
        outdims[d1] = dims[d1]
    end

    currentdims = zeros(Int, N)
    blockcount = 0
    elementcount = 0
    for i ∈ eachindex(as)
        elementcount = checked_add(elementcount, cat_length(as[i]))
        currentdims[d1] = checked_add(currentdims[d1], first_dim_zero ? 1 : cat_size(as[i], d1))
        if currentdims[d1] == outdims[d1]
            currentdims[d1] = 0
            for d ∈ (d2, 3:N...)
                currentdims[d] = checked_add(currentdims[d], cat_size(as[i], d))
                if outdims[d] == 0 # unfixed dimension
                    blockcount += 1
                    if blockcount == dims[d]
                        outdims[d] = currentdims[d]
                        currentdims[d] = 0
                        blockcount = 0
                    else
                        break
                    end
                else # fixed dimension
                    if currentdims[d] == outdims[d] # end of dimension
                        currentdims[d] = 0
                    elseif currentdims[d] < outdims[d] # dimension in progress
                        break
                    else # exceeded dimension
                        throw(DimensionMismatch("argument $i has too many elements along axis $d"))
                    end
                end
            end
        elseif currentdims[d1] > outdims[d1] # exceeded dimension
            throw(DimensionMismatch("argument $i has too many elements along axis $d1"))
        end
    end
    # restore 0-length adjustment
    if first_dim_zero
        outdims[d1] = 0
    end

    outlen = Core.checked_dims(ntuple(i -> outdims[i], Val(N))...)
    elementcount == outlen ||
        throw(DimensionMismatch("mismatched number of elements; expected $(outlen), got $(elementcount)"))

    # copy into final array
    A = cat_similar(as[1], T, ntuple(i -> outdims[i], N))
    # @assert all(==(0), currentdims)
    outdims .= 0
    hvncat_fill!(A, currentdims, outdims, d1, d2, as)
    return A
end
```
-/
def typedHvncatDims {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty X V A : Type}
    (range : I64 → I64 → m (List I64)) (div : I64 → I64 → m I64)
    (getDim : List I64 → I64 → m I64) (findFirst : List I64 → m (Option I64))
    (zeros : Nat → m V) (get : V → I64 → m I64) (set : V → I64 → I64 → m Unit)
    (tupleIndices : List X → m (List I64)) (tupleGet : List X → I64 → m X)
    (catSize : X → I64 → m I64) (catLength : X → m I64)
    (checkedAdd : I64 → I64 → m I64)
    (ntuple : (I64 → m I64) → Nat → m (List I64))
    (checkedDims : List I64 → m I64) (similar : X → Ty → List I64 → m A)
    (zero : V → m Unit) (fill : A → V → V → I64 → I64 → List X → m Unit)
    (t : Ty) (dims : List I64) (rowFirst : Bool) (as : List X) : m A := do
  if as.isEmpty then
    throw (.julia (.argumentError "must have at least one element"))
  if !(dims.all fun d => decide (0 < d.val)) then
    throw (.julia (.argumentError "`dims` argument must contain positive integers"))
  let d1 := if rowFirst then int 2 else int 1
  let d2 := if rowFirst then int 1 else int 2
  let outdims ← zeros dims.length
  if let some found ← findFirst dims then
    let d := if rowFirst && decide (found.val < 3) then
      (if found.val = 1 then int 2 else int 1) else found
    let nblocks ← div (int as.length) (← getDim dims d)
    for b in (← range (int 1) nblocks) do
      let offset := (b - int 1) * (← getDim dims d)
      let start := offset + int 1
      for i in ((← range (int 2) (← getDim dims d)).map (offset + ·)) do
        for dd in (← range (int 1) (int dims.length)) do
          if dd.val != d.val then
            if (← catSize (← tupleGet as start) dd).val !=
                (← catSize (← tupleGet as i) dd).val then
              throw (.dimensionMismatch ("incompatible shape in element " ++ toString i.val))
  for i in (← range (int 1) (← getDim dims d1)) do
    set outdims d1 (← checkedAdd (← get outdims d1) (← catSize (← tupleGet as i) d1))
  let firstDimZero := (← get outdims d1).val == 0
  if firstDimZero then set outdims d1 (← getDim dims d1)
  let currentdims ← zeros dims.length
  let mut blockcount := int 0
  let mut elementcount := int 0
  for i in (← tupleIndices as) do
    elementcount ← checkedAdd elementcount (← catLength (← tupleGet as i))
    set currentdims d1 (← checkedAdd (← get currentdims d1)
      (← if firstDimZero then pure (int 1) else catSize (← tupleGet as i) d1))
    if (← get currentdims d1).val == (← get outdims d1).val then
      set currentdims d1 (int 0)
      for d in (d2 :: (← range (int 3) (int dims.length))) do
        set currentdims d (← checkedAdd (← get currentdims d) (← catSize (← tupleGet as i) d))
        if (← get outdims d).val = 0 then
          blockcount := blockcount + int 1
          if blockcount.val == (← getDim dims d).val then
            set outdims d (← get currentdims d)
            set currentdims d (int 0)
            blockcount := int 0
          else break
        else
          if (← get currentdims d).val == (← get outdims d).val then
            set currentdims d (int 0)
          else if (← get currentdims d).val < (← get outdims d).val then break
          else throw (.dimensionMismatch ("argument " ++ toString i.val ++
            " has too many elements along axis " ++ toString d.val))
    else if (← get currentdims d1).val > (← get outdims d1).val then
      throw (.dimensionMismatch ("argument " ++ toString i.val ++
        " has too many elements along axis " ++ toString d1.val))
  if firstDimZero then set outdims d1 (int 0)
  let outlen ← checkedDims (← ntuple (get outdims) dims.length)
  if elementcount.val != outlen.val then
    throw (.dimensionMismatch ("mismatched number of elements; expected " ++
      toString outlen.val ++ ", got " ++ toString elementcount.val))
  let a ← similar (← tupleGet as (int 1)) t (← ntuple (get outdims) dims.length)
  zero outdims
  fill a currentdims outdims d1 d2 as
  return a

/--
Julia source: base/abstractarray.jl:2732-2736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat(T::Type, shape::Tuple{Tuple}, row_first::Bool, xs...)
    length(shape[1]) > 0 ||
        throw(ArgumentError("each level of `shape` argument must have at least one value"))
    return _typed_hvncat_1d(T, shape[1][1], Val(row_first), xs...)
end
```
-/
def typedHvncatOneLevel {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty X A : Type} (getShape : List (List I64) → I64 → m (List I64))
    (get : List I64 → I64 → m I64) (typed : Ty → I64 → Bool → X → m A)
    (t : Ty) (shape : List (List I64)) (rowFirst : Bool) (xs : X) : m A := do
  if (← getShape shape (int 1)).isEmpty then
    throw (.julia (.argumentError "each level of `shape` argument must have at least one value"))
  typed t (← get (← getShape shape (int 1)) (int 1)) rowFirst xs

/--
Julia source: base/abstractarray.jl:2738-2742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat(T::Type, shape::NTuple{N, Tuple}, row_first::Bool, as...) where {N}
    # function barrier after calculating the max is necessary for high performance
    nd = max(maximum(cat_ndims(a) for a ∈ as), N)
    return _typed_hvncat_shape(T, (shape..., ntuple(Returns(shape[end]), nd - N)...), row_first, as)
end
```
-/
def typedHvncatMixedShape {m : Type → Type} [Monad m] {Ty X A : Type}
    (catNdims : X → m I64) (maximum : (X → m I64) → List X → m I64)
    (last : List (List I64) → m (List I64))
    (replicate : List I64 → I64 → m (List (List I64)))
    (typed : Ty → List (List I64) → Bool → List X → m A)
    (t : Ty) (shape : List (List I64)) (rowFirst : Bool) (as : List X) : m A := do
  let nd := int (max (← maximum catNdims as).val (shape.length : Int))
  let tail ← replicate (← last shape) (nd - int shape.length)
  typed t (shape ++ tail) rowFirst as

/--
Julia source: base/abstractarray.jl:2744-2821 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_hvncat_shape(::Type{T}, shape::NTuple{N, Tuple}, row_first, as::Tuple) where {T, N}
    length(as) > 0 ||
        throw(ArgumentError("must have at least one element"))
    all(>(0), tuple((shape...)...)) ||
        throw(ArgumentError("`shape` argument must consist of positive integers"))

    d1 = row_first ? 2 : 1
    d2 = row_first ? 1 : 2

    shapev = collect(shape) # saves allocations later
    all(!isempty, shapev) ||
        throw(ArgumentError("each level of `shape` argument must have at least one value"))
    length(shapev[end]) == 1 ||
        throw(ArgumentError("last level of shape must contain only one integer"))
    shapelength = shapev[end][1]
    lengthas = length(as)
    shapelength == lengthas || throw(ArgumentError("number of elements does not match shape; expected $(shapelength), got $lengthas)"))
    # discover dimensions
    nd = max(N, cat_ndims(as[1]))
    outdims = fill(-1, nd)
    currentdims = zeros(Int, nd)
    blockcounts = zeros(Int, nd)
    shapepos = ones(Int, nd)

    elementcount = 0
    for i ∈ eachindex(as)
        elementcount = checked_add(elementcount, cat_length(as[i]))
        wasstartblock = false
        for d ∈ 1:N
            ad = (d < 3 && row_first) ? (d == 1 ? 2 : 1) : d
            dsize = cat_size(as[i], ad)
            blockcounts[d] += 1

            if d == 1 || i == 1 || wasstartblock
                currentdims[d] = checked_add(currentdims[d], dsize)
            elseif dsize != cat_size(as[i - 1], ad)
                throw(DimensionMismatch("argument $i has a mismatched number of elements along axis $ad; \
                                         expected $(cat_size(as[i - 1], ad)), got $dsize"))
            end

            wasstartblock = blockcounts[d] == 1 # remember for next dimension

            isendblock = blockcounts[d] == shapev[d][shapepos[d]]
            if isendblock
                if outdims[d] == -1
                    outdims[d] = currentdims[d]
                elseif outdims[d] != currentdims[d]
                    throw(DimensionMismatch("argument $i has a mismatched number of elements along axis $ad; \
                                             expected $(abs(outdims[d] - (currentdims[d] - dsize))), got $dsize"))
                end
                currentdims[d] = 0
                blockcounts[d] = 0
                shapepos[d] += 1
                d > 1 && (blockcounts[d - 1] == 0 ||
                    throw(DimensionMismatch("shape in level $d is inconsistent; level counts must nest \
                                             evenly into each other")))
            end
        end
    end

    outlen = Core.checked_dims(ntuple(i -> outdims[i], Val(N))...)
    elementcount == outlen ||
        throw(ArgumentError("mismatched number of elements; expected $(outlen), got $(elementcount)"))

    if row_first
        outdims[1], outdims[2] = outdims[2], outdims[1]
    end

    # @assert all(==(0), currentdims)
    # @assert all(==(0), blockcounts)

    # copy into final array
    A = cat_similar(as[1], T, ntuple(i -> outdims[i], nd))
    if !any(iszero, outdims)
        hvncat_fill!(A, currentdims, blockcounts, d1, d2, as)
    end
    return A
end
```
-/
def typedHvncatShape {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty X V A : Type} (collect : List (List I64) → m (List (List I64)))
    (last : List (List I64) → m (List I64))
    (getShape : List (List I64) → I64 → m (List I64))
    (getDim : List I64 → I64 → m I64)
    (range : I64 → I64 → m (List I64))
    (tupleIndices : List X → m (List I64)) (tupleGet : List X → I64 → m X)
    (catNdims : X → m I64) (catSize : X → I64 → m I64) (catLength : X → m I64)
    (filled : I64 → I64 → m V) (zeros ones : I64 → m V)
    (get : V → I64 → m I64) (set : V → I64 → I64 → m Unit)
    (checkedAdd : I64 → I64 → m I64) (abs : I64 → m I64)
    (ntuple : (I64 → m I64) → Nat → m (List I64))
    (checkedDims : List I64 → m I64) (anyZero : V → m Bool)
    (similar : X → Ty → List I64 → m A)
    (fill : A → V → V → I64 → I64 → List X → m Unit)
    (t : Ty) (shape : List (List I64)) (rowFirst : Bool) (as : List X) : m A := do
  if as.isEmpty then
    throw (.julia (.argumentError "must have at least one element"))
  if !(shape.flatten.all fun d => decide (0 < d.val)) then
    throw (.julia (.argumentError "`shape` argument must consist of positive integers"))
  let d1 := if rowFirst then int 2 else int 1
  let d2 := if rowFirst then int 1 else int 2
  let shapev ← collect shape
  if !(shapev.all fun ds => !ds.isEmpty) then
    throw (.julia (.argumentError "each level of `shape` argument must have at least one value"))
  if (← last shapev).length != 1 then
    throw (.julia (.argumentError "last level of shape must contain only one integer"))
  let shapelength ← getDim (← last shapev) (int 1)
  let lengthas := int as.length
  if shapelength.val != lengthas.val then
    throw (.julia (.argumentError ("number of elements does not match shape; expected " ++
      toString shapelength.val ++ ", got " ++ toString lengthas.val ++ ")")))
  let nd := int (max (shape.length : Int) (← catNdims (← tupleGet as (int 1))).val)
  let outdims ← filled (int (-1)) nd
  let currentdims ← zeros nd
  let blockcounts ← zeros nd
  let shapepos ← ones nd
  let mut elementcount := int 0
  for i in (← tupleIndices as) do
    elementcount ← checkedAdd elementcount (← catLength (← tupleGet as i))
    let mut wasStartBlock := false
    for d in (← range (int 1) (int shape.length)) do
      let ad := if decide (d.val < 3) && rowFirst then
        (if d.val = 1 then int 2 else int 1) else d
      let dsize ← catSize (← tupleGet as i) ad
      set blockcounts d ((← get blockcounts d) + int 1)
      if d.val = 1 || i.val = 1 || wasStartBlock then
        set currentdims d (← checkedAdd (← get currentdims d) dsize)
      else if dsize.val != (← catSize (← tupleGet as (i - int 1)) ad).val then
        throw (.dimensionMismatch ("argument " ++ toString i.val ++
          " has a mismatched number of elements along axis " ++ toString ad.val ++
          "; expected " ++ toString (← catSize (← tupleGet as (i - int 1)) ad).val ++
          ", got " ++ toString dsize.val))
      wasStartBlock := (← get blockcounts d).val == 1
      let isEndBlock := (← get blockcounts d).val ==
        (← getDim (← getShape shapev d) (← get shapepos d)).val
      if isEndBlock then
        if (← get outdims d).val = -1 then
          set outdims d (← get currentdims d)
        else if (← get outdims d).val != (← get currentdims d).val then
          throw (.dimensionMismatch ("argument " ++ toString i.val ++
            " has a mismatched number of elements along axis " ++ toString ad.val ++
            "; expected " ++ toString (← abs ((← get outdims d) -
              ((← get currentdims d) - dsize))).val ++ ", got " ++ toString dsize.val))
        set currentdims d (int 0)
        set blockcounts d (int 0)
        set shapepos d ((← get shapepos d) + int 1)
        if d.val > 1 then
          if (← get blockcounts (d - int 1)).val != 0 then
            throw (.dimensionMismatch ("shape in level " ++ toString d.val ++
              " is inconsistent; level counts must nest evenly into each other"))
  let outlen ← checkedDims (← ntuple (get outdims) shape.length)
  if elementcount.val != outlen.val then
    throw (.julia (.argumentError ("mismatched number of elements; expected " ++
      toString outlen.val ++ ", got " ++ toString elementcount.val)))
  if rowFirst then
    let second ← get outdims (int 2)
    let first ← get outdims (int 1)
    set outdims (int 1) second
    set outdims (int 2) first
  let a ← similar (← tupleGet as (int 1)) t
    (← ntuple (get outdims) nd.val.toNat)
  if !(← anyZero outdims) then fill a currentdims blockcounts d1 d2 as
  return a

/--
Julia source: base/abstractarray.jl:2823-2863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hvncat_fill!(A::AbstractArray{T, N}, scratch1::Vector{Int}, scratch2::Vector{Int}, d1::Int, d2::Int, as::Tuple) where {T, N}
    N > 1 || throw(ArgumentError("dimensions of the destination array must be at least 2"))
    length(scratch1) == length(scratch2) == N ||
        throw(ArgumentError("scratch vectors must have as many elements as the destination array has dimensions"))
    0 < d1 < 3 &&
    0 < d2 < 3 &&
    d1 != d2 ||
        throw(ArgumentError("d1 and d2 must be either 1 or 2, exclusive."))
    outdimsprod = cumprod(size(A))
    offsets = scratch1
    inneroffsets = scratch2
    for a ∈ as
        startindex = CartesianIndex(ntuple(i -> offsets[i] + 1, Val(N)))
        if isa(a, AbstractArray)
            if !isempty(a)
                if length(a) > 4
                    endindex = CartesianIndex(ntuple(i -> offsets[i] + cat_size(a, i), Val(N)))
                    @inbounds A[startindex:endindex] = a
                else
                    for ai ∈ a
                        @inbounds Ai = hvncat_calcindex(offsets, inneroffsets, outdimsprod, N)
                        @inbounds A[Ai] = ai
                        @inbounds for j ∈ 1:N
                            inneroffsets[j] += 1
                            inneroffsets[j] < cat_size(a, j) && break
                            inneroffsets[j] = 0
                        end
                    end
                end
            end
        else
            @inbounds A[startindex] = a
        end

        @inbounds for i ∈ (d1, d2, 3:N...)
            offsets[i] += cat_size(a, i)
            offsets[i] < cat_size(A, i) && break
            offsets[i] = 0
        end
    end
end
```
-/
def hvncatFillArrays {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A X V C E : Type}
    (length : V → m I64) (size : A → m (List I64)) (cumprod : List I64 → m (List I64))
    (get : V → I64 → m I64) (set : V → I64 → I64 → m Unit)
    (range : I64 → I64 → m (List I64))
    (ntuple : (I64 → m I64) → Nat → m (List I64))
    (cartesian : List I64 → m C) (isArray : X → Bool) (isempty : X → m Bool)
    (lengthArg : X → m I64) (catSizeArg : X → I64 → m I64)
    (catSizeDest : A → I64 → m I64)
    (calcIndex : V → V → List I64 → I64 → m I64)
    (values : X → m (List E))
    (setBlock : A → C → C → X → m Unit) (setElement : A → I64 → E → m Unit)
    (setScalar : A → C → X → m Unit)
    (rank : Nat) (a : A) (scratch1 scratch2 : V) (d1 d2 : I64) (as : List X) : m Unit := do
  if rank ≤ 1 then
    throw (.julia (.argumentError "dimensions of the destination array must be at least 2"))
  let length1 ← length scratch1
  let length2 ← length scratch2
  if !(length1.val = length2.val ∧ length2.val = (rank : Int)) then
    throw (.julia (.argumentError "scratch vectors must have as many elements as the destination array has dimensions"))
  if !(0 < d1.val ∧ d1.val < 3 ∧ 0 < d2.val ∧ d2.val < 3 ∧ d1.val ≠ d2.val) then
    throw (.julia (.argumentError "d1 and d2 must be either 1 or 2, exclusive."))
  let outdimsprod ← cumprod (← size a)
  let offsets := scratch1
  let inneroffsets := scratch2
  for x in as do
    let start ← cartesian (← ntuple (fun i => do return (← get offsets i) + int 1) rank)
    if isArray x then
      if !(← isempty x) then
        if (← lengthArg x).val > 4 then
          let finish ← cartesian (← ntuple (fun i => do
            return (← get offsets i) + (← catSizeArg x i)) rank)
          setBlock a start finish x
        else
          for value in (← values x) do
            let ai ← calcIndex offsets inneroffsets outdimsprod (int rank)
            setElement a ai value
            for j in (← range (int 1) (int rank)) do
              set inneroffsets j ((← get inneroffsets j) + int 1)
              if (← get inneroffsets j).val < (← catSizeArg x j).val then break
              set inneroffsets j (int 0)
    else setScalar a start x
    for i in (d1 :: d2 :: (← range (int 3) (int rank))) do
      set offsets i ((← get offsets i) + (← catSizeArg x i))
      if (← get offsets i).val < (← catSizeDest a i).val then break
      set offsets i (int 0)

/--
Julia source: base/abstractarray.jl:2865-2874 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function hvncat_calcindex(offsets::Vector{Int}, inneroffsets::Vector{Int},
                                                outdimsprod::NTuple{N, Int}, nd::Int) where {N}
    Ai = inneroffsets[1] + offsets[1] + 1
    for j ∈ 2:nd
        increment = inneroffsets[j] + offsets[j]
        increment *= outdimsprod[j - 1]
        Ai += increment
    end
    Ai
end
```
-/
def hvncatCalcIndex {m : Type → Type} [Monad m] {V : Type}
    (get : V → I64 → m I64) (getProduct : List I64 → I64 → m I64)
    (range : I64 → I64 → m (List I64))
    (offsets inneroffsets : V) (outdimsprod : List I64) (nd : I64) : m I64 := do
  let mut ai := (← get inneroffsets (int 1)) + (← get offsets (int 1)) + int 1
  for j in (← range (int 2) nd) do
    let mut increment := (← get inneroffsets j) + (← get offsets j)
    increment := increment * (← getProduct outdimsprod (j - int 1))
    ai := ai + increment
  return ai

/--
Julia source: base/abstractarray.jl:2967-2967 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stack(iter; dims::D=:) where {D} = _stack(dims, iter)
```
-/
def stack {m : Type → Type} [Monad m] {D It A : Type}
    (stack : D → It → m A) (dims : D) (iter : It) : m A := stack dims iter

/--
Julia source: base/abstractarray.jl:2996-2996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stack(f, iter; dims::D=:) where {D} = _stack(dims, f(x) for x in iter)
```
-/
def stackMap {m : Type → Type} [Monad m] {D It X E G A : Type}
    (generator : (X → m E) → It → m G) (stack : D → G → m A)
    (f : X → m E) (iter : It) (dims : D) : m A := do
  stack dims (← generator f iter)

/--
Julia source: base/abstractarray.jl:2997-2997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stack(f, xs, yzs...; dims::D=:) where {D} = _stack(dims, f(xy...) for xy in zip(xs, yzs...))
```
-/
def stackZipMap {m : Type → Type} [Monad m] {D It Rest Z X E G A : Type}
    (zip : It → Rest → m Z) (generator : (X → m E) → Z → m G)
    (stack : D → G → m A) (f : X → m E) (xs : It) (yzs : Rest) (dims : D) : m A := do
  stack dims (← generator f (← zip xs yzs))

/--
Julia source: base/abstractarray.jl:2999-2999 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_stack(dims::D, iter) where {D<:Union{Integer, Colon}} = _stack(dims, IteratorSize(iter), iter)
```
-/
def stackIterator {m : Type → Type} [Monad m] {D It Sz A : Type}
    (iteratorSize : It → m Sz) (stack : D → Sz → It → m A)
    (dims : D) (iter : It) : m A := do
  stack dims (← iteratorSize iter) iter

/--
Julia source: base/abstractarray.jl:3001-3001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_stack(dims::D, ::IteratorSize, iter) where {D} = _stack(dims, collect(iter))
```
-/
def stackCollect {m : Type → Type} [Monad m] {D It C A : Type}
    (collect : It → m C) (stack : D → C → m A) (dims : D) (iter : It) : m A := do
  stack dims (← collect iter)

/--
Julia source: base/abstractarray.jl:3003-3014 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _stack(dims::D, ::Union{HasShape, HasLength}, iter) where {D}
    S = @default_eltype iter
    T = S != Union{} ? eltype(S) : Any  # Union{} occurs for e.g. stack(1,2), postpone the error
    if isconcretetype(T)
        _typed_stack(dims, T, S, iter)
    else  # Need to look inside, but shouldn't run an expensive iterator twice:
        array = iter isa Union{Tuple, AbstractArray} ? iter : collect(iter)
        isempty(array) && return _empty_stack(dims, T, S, iter)
        T2 = mapreduce(eltype, promote_type, array)
        _typed_stack(dims, T2, eltype(array), array)
    end
end
```
-/
def stackKnownSize {m : Type → Type} [Monad m] {D It C Ty A : Type}
    (anyType : Ty) (defaultEltype : It → m Ty) (isBottom : Ty → Bool)
    (eltype : Ty → m Ty) (isConcrete : Ty → m Bool)
    (typed : D → Ty → Ty → It → m A)
    (isTupleOrArray : It → Bool) (reuse : It → C) (collect : It → m C)
    (isempty : C → m Bool) (empty : D → Ty → Ty → It → m A)
    (promoteEltypes : C → m Ty) (collectionEltype : C → m Ty)
    (typedCollection : D → Ty → Ty → C → m A)
    (dims : D) (iter : It) : m A := do
  let s ← defaultEltype iter
  let t ← if !isBottom s then eltype s else pure anyType
  if ← isConcrete t then return ← typed dims t s iter
  else
    let array ← if isTupleOrArray iter then pure (reuse iter) else collect iter
    if ← isempty array then return ← empty dims t s iter
    let t2 ← promoteEltypes array
    typedCollection dims t2 (← collectionEltype array) array

/--
Julia source: base/abstractarray.jl:3016-3032 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_stack(::Colon, ::Type{T}, ::Type{S}, A, Aax=_iterator_axes(A)) where {T, S}
    xit = iterate(A)
    nothing === xit && return _empty_stack(:, T, S, A)
    x1, _ = xit
    ax1 = _iterator_axes(x1)
    B = similar(_ensure_array(x1), T, ax1..., Aax...)
    off = firstindex(B)
    len = length(x1)
    while xit !== nothing
        x, state = xit
        _stack_size_check(x, ax1)
        copyto!(B, off, x)
        off += len
        xit = iterate(A, state)
    end
    B
end
```
-/
def typedStackColon {m : Type → Type} [Monad m] {It X Storage St Ty Ax B D : Type}
    (colon : D) (start : It → m (Option (X × St)))
    (next : It → St → m (Option (X × St)))
    (empty : D → Ty → Ty → It → m B) (iteratorAxes : X → m (List Ax))
    (ensureArray : X → m Storage) (similar : Storage → Ty → List Ax → m B)
    (firstindex : B → m I64) (length : X → m I64)
    (sizeCheck : X → List Ax → m Unit) (copyto : B → I64 → X → m B)
    (whileLoop : {β : Type} → β → (β → m (ForInStep β)) → m β)
    (t s : Ty) (a : It) (aax : List Ax) : m B := do
  let xit ← start a
  match xit with
  | none => empty colon t s a
  | some (x1, _) =>
    let ax1 ← iteratorAxes x1
    let b ← similar (← ensureArray x1) t (ax1 ++ aax)
    let off ← firstindex b
    let len ← length x1
    let _ ← whileLoop (off, xit) fun (off, xit) => do
      match xit with
      | none => pure (.done (off, xit))
      | some (x, state) =>
        sizeCheck x ax1
        let _ ← copyto b off x
        let off := off + len
        let xit ← next a state
        pure (.yield (off, xit))
    return b

/--
Julia source: base/abstractarray.jl:3034-3034 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_iterator_axes(x) = _iterator_axes(x, IteratorSize(x))
```
-/
def iteratorAxes {m : Type → Type} [Monad m] {X Sz Ax : Type}
    (iteratorSize : X → m Sz) (axes : X → Sz → m Ax) (x : X) : m Ax := do
  axes x (← iteratorSize x)

/--
Julia source: base/abstractarray.jl:3035-3035 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_iterator_axes(x, ::HasLength) = (OneTo(length(x)),)
```
-/
def iteratorAxesLength {m : Type → Type} [Monad m] {X N Ax : Type}
    (length : X → m N) (oneTo : N → m Ax) (x : X) : m (List Ax) := do
  return [← oneTo (← length x)]

/--
Julia source: base/abstractarray.jl:3036-3036 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_iterator_axes(x, ::IteratorSize) = axes(x)
```
-/
def iteratorAxesShape {m : Type → Type} [Monad m] {X Ax : Type}
    (axes : X → m Ax) (x : X) : m Ax := axes x

/--
Julia source: base/abstractarray.jl:3039-3040 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_stack(dims::Integer, ::Type{T}, ::Type{S}, A) where {T,S} =
    _typed_stack(dims, T, S, IteratorSize(S), A)
```
-/
def typedStackInteger {m : Type → Type} [Monad m] {D Ty It Sz A : Type}
    (iteratorSize : Ty → m Sz) (typed : D → Ty → Ty → Sz → It → m A)
    (dims : D) (t s : Ty) (a : It) : m A := do
  typed dims t s (← iteratorSize s) a

/--
Julia source: base/abstractarray.jl:3041-3047 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typed_stack(dims::Integer, ::Type{T}, ::Type{S}, ::HasShape{N}, A) where {T,S,N}
    if dims == N+1
        _typed_stack(:, T, S, A, (_vec_axis(A),))
    else
        _dim_stack(dims, T, S, A)
    end
end
```
-/
def typedStackShape {m : Type → Type} [Monad m] {D Ty It Ax A : Type}
    (isLast : D → Nat → m Bool) (vecAxis : It → m Ax)
    (colonStack : Ty → Ty → It → List Ax → m A)
    (dimStack : D → Ty → Ty → It → m A)
    (rank : Nat) (dims : D) (t s : Ty) (a : It) : m A := do
  if ← isLast dims (rank + 1) then
    colonStack t s a [← vecAxis a]
  else dimStack dims t s a

/--
Julia source: base/abstractarray.jl:3048-3049 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typed_stack(dims::Integer, ::Type{T}, ::Type{S}, ::IteratorSize, A) where {T,S} =
    _dim_stack(dims, T, S, A)
```
-/
def typedStackOther {m : Type → Type} [Monad m] {D Ty It A : Type}
    (dimStack : D → Ty → Ty → It → m A)
    (dims : D) (t s : Ty) (a : It) : m A := dimStack dims t s a

/--
Julia source: base/abstractarray.jl:3051-3051 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_vec_axis(A, ax=_iterator_axes(A)) = length(ax) == 1 ? only(ax) : OneTo(prod(length, ax; init=1))
```
-/
def vecAxis {m : Type → Type} [Monad m] {Ax N : Type}
    (only : List Ax → m Ax) (productLengths : List Ax → m N) (oneTo : N → m Ax)
    (axes : List Ax) : m Ax := do
  if axes.length = 1 then only axes
  else oneTo (← productLengths axes)

/--
Julia source: base/abstractarray.jl:3053-3073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function _dim_stack(dims::Integer, ::Type{T}, ::Type{S}, A) where {T,S}
    xit = Iterators.peel(A)
    nothing === xit && return _empty_stack(dims, T, S, A)
    x1, xrest = xit
    ax1 = _iterator_axes(x1)
    N1 = length(ax1)+1
    dims in 1:N1 || throw(ArgumentError(LazyString("cannot stack slices ndims(x) = ", N1-1, " along dims = ", dims)))

    newaxis = _vec_axis(A)
    outax = ntuple(d -> d==dims ? newaxis : ax1[d - (d>dims)], N1)
    B = similar(_ensure_array(x1), T, outax...)

    if dims == 1
        _dim_stack!(Val(1), B, x1, xrest)
    elseif dims == 2
        _dim_stack!(Val(2), B, x1, xrest)
    else
        _dim_stack!(Val(dims), B, x1, xrest)
    end
    B
end
```
-/
def dimStack {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D Ty It X Storage Rest Ax A : Type}
    (peel : It → m (Option (X × Rest))) (empty : D → Ty → Ty → It → m A)
    (iteratorAxes : X → m (List Ax)) (within : D → Nat → m Bool)
    (showDim : D → String) (eqDim : D → Nat → Bool) (greaterDim : Nat → D → Bool)
    (vecAxis : It → m Ax) (getAxis : List Ax → Nat → m Ax)
    (ntuple : (Nat → m Ax) → Nat → m (List Ax))
    (ensureArray : X → m Storage) (similar : Storage → Ty → List Ax → m A)
    (fillOne fillTwo : A → X → Rest → m Unit)
    (fillOther : D → A → X → Rest → m Unit)
    (dims : D) (t s : Ty) (a : It) : m A := do
  match ← peel a with
  | none => empty dims t s a
  | some (x1, rest) =>
    let ax1 ← iteratorAxes x1
    let n1 := ax1.length + 1
    if !(← within dims n1) then
      throw (.julia (.argumentError ("cannot stack slices ndims(x) = " ++
        toString (n1 - 1) ++ " along dims = " ++ showDim dims)))
    let newaxis ← vecAxis a
    let outax ← ntuple (fun d =>
      if eqDim dims d then pure newaxis
      else getAxis ax1 (d - if greaterDim d dims then 1 else 0)) n1
    let b ← similar (← ensureArray x1) t outax
    if eqDim dims 1 then fillOne b x1 rest
    else if eqDim dims 2 then fillTwo b x1 rest
    else fillOther dims b x1 rest
    return b

/--
Julia source: base/abstractarray.jl:3075-3087 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _dim_stack!(::Val{dims}, B::AbstractArray, x1, xrest) where {dims}
    before = ntuple(Returns(Colon()), dims - 1)
    after = ntuple(Returns(Colon()), ndims(B) - dims)

    i = firstindex(B, dims)
    copyto!(view(B, before..., i, after...), x1)

    for x in xrest
        _stack_size_check(x, _iterator_axes(x1))
        i += 1
        @inbounds copyto!(view(B, before..., i, after...), x)
    end
end
```
-/
def dimStackFill {m : Type → Type} [Monad m]
    {A X Rest Col View Ax : Type} [ForIn m Rest X]
    (colons : I64 → m (List Col)) (ndims : A → m I64)
    (firstindex : A → I64 → m I64)
    (view : A → List Col → I64 → List Col → m View)
    (copyto : View → X → m Unit) (iteratorAxes : X → m Ax)
    (sizeCheck : X → Ax → m Unit)
    (dims : I64) (b : A) (x1 : X) (rest : Rest) : m Unit := do
  let before ← colons (dims - int 1)
  let after ← colons ((← ndims b) - dims)
  let mut i ← firstindex b dims
  copyto (← view b before i after) x1
  for x in rest do
    sizeCheck x (← iteratorAxes x1)
    i := i + int 1
    copyto (← view b before i after) x

/--
Julia source: base/abstractarray.jl:3089-3096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _stack_size_check(x, ax1::Tuple)
    if _iterator_axes(x) != ax1
        uax1 = map(UnitRange, ax1)
        uaxN = map(UnitRange, _iterator_axes(x))
        throw(DimensionMismatch(
            LazyString("stack expects uniform slices, got axes(x) == ", uaxN, " while first had ", uax1)))
    end
end
```
-/
def stackSizeCheck {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {X Ax Range : Type} [DecidableEq Ax]
    (iteratorAxes : X → m (List Ax)) (unitRange : Ax → m Range)
    (showAxes : List Range → String) (x : X) (ax1 : List Ax) : m Unit := do
  if (← iteratorAxes x) != ax1 then
    let uax1 ← ax1.mapM unitRange
    let uaxn ← (← iteratorAxes x).mapM unitRange
    throw (.dimensionMismatch ("stack expects uniform slices, got axes(x) == " ++
      showAxes uaxn ++ " while first had " ++ showAxes uax1))

/--
Julia source: base/abstractarray.jl:3098-3098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ensure_array(x::AbstractArray) = x
```
-/
def ensureArray (x : A) : A := x

/--
Julia source: base/abstractarray.jl:3099-3099 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ensure_array(x) = 1:0  # passed to similar, makes stack's output an Array
```
-/
def ensureArrayOther {m : Type → Type} [Monad m] {A R : Type}
    (range : I64 → I64 → m R) (_x : A) : m R := range (int 1) (int 0)

/--
Julia source: base/abstractarray.jl:3101-3101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_empty_stack(_...) = throw(ArgumentError("`stack` on an empty collection is not allowed"))
```
-/
def emptyStack {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Args A : Type} (_args : Args) : m A :=
  throw (.julia (.argumentError "`stack` on an empty collection is not allowed"))

/--
Julia source: base/abstractarray.jl:3106-3117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isequal(A::AbstractArray, B::AbstractArray)
    if A === B return true end
    if axes(A) != axes(B)
        return false
    end
    for (a, b) in zip(A, B)
        if !isequal(a, b)
            return false
        end
    end
    return true
end
```
-/
def arrayIsequal {m : Type → Type} [Monad m]
    {A B Ax E F Z : Type} [DecidableEq Ax] [ForIn m Z (E × F)]
    (identical : A → B → Bool) (axesA : A → m Ax) (axesB : B → m Ax)
    (zip : A → B → m Z) (isequal : E → F → m Bool) (a : A) (b : B) : m Bool := do
  if identical a b then return true
  if (← axesA a) != (← axesB b) then return false
  for (x, y) in (← zip a b) do
    if !(← isequal x y) then return false
  return true

/--
Julia source: base/abstractarray.jl:3119-3128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cmp(A::AbstractVector, B::AbstractVector)
    ai1, bi1 = firstindex(A), firstindex(B)
    isequal(ai1, bi1) || return cmp(ai1, bi1)
    for (a, b) in zip(A, B)
        if !isequal(a, b)
            return isless(a, b) ? -1 : 1
        end
    end
    return cmp(length(A), length(B))
end
```
-/

def vectorCmp {m : Type → Type} [Monad m]
    {A B IA IB E F Z : Type} [ForIn m Z (E × F)]
    (firstA : A → m IA) (firstB : B → m IB)
    (equalFirst : IA → IB → m Bool) (cmpFirst : IA → IB → m I64)
    (zip : A → B → m Z) (isequal isless : E → F → m Bool)
    (lengthA : A → m I64) (lengthB : B → m I64)
    (cmpLength : I64 → I64 → m I64) (a : A) (b : B) : m I64 := do
  let ai ← firstA a
  let bi ← firstB b
  if !(← equalFirst ai bi) then return ← cmpFirst ai bi
  for (x, y) in (← zip a b) do
    if !(← isequal x y) then
      return if ← isless x y then int (-1) else int 1
  cmpLength (← lengthA a) (← lengthB b)
/--
Julia source: base/abstractarray.jl:3135-3137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isless(A::AbstractArray{<:Any,0}, B::AbstractArray{<:Any,0})
    isless(only(A), only(B))
end
```
-/
def arrayIslessZeroDim {m : Type → Type} [Monad m] {A B E F : Type}
    (onlyA : A → m E) (onlyB : B → m F) (isless : E → F → m Bool)
    (a : A) (b : B) : m Bool := do
  isless (← onlyA a) (← onlyB b)

/--
Julia source: base/abstractarray.jl:3145-3145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(A::AbstractVector, B::AbstractVector) = cmp(A, B) < 0
```
-/
def vectorIsless {m : Type → Type} [Monad m] {A B : Type}
    (cmp : A → B → m I64) (a : A) (b : B) : m Bool := do
  return decide ((← cmp a b).val < 0)

/--
Julia source: base/abstractarray.jl:3147-3147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OrderStyle(::Type{<:AbstractVector{T}}) where {T} = OrderStyle(T)
```
-/
def vectorOrderStyle {Ty Style : Type} (orderStyle : Ty → Style) (elementType : Ty) :
    Style := orderStyle elementType

/--
Julia source: base/abstractarray.jl:3149-3163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (==)(A::AbstractArray, B::AbstractArray)
    if axes(A) != axes(B)
        return false
    end
    anymissing = false
    for (a, b) in zip(A, B)
        eq = (a == b)
        if ismissing(eq)
            anymissing = true
        elseif !eq
            return false
        end
    end
    return anymissing ? missing : true
end
```
-/
def arrayEqual {m : Type → Type} [Monad m]
    {A B Ax E F Eq Z : Type} [DecidableEq Ax] [ForIn m Z (E × F)]
    (axesA : A → m Ax) (axesB : B → m Ax) (zip : A → B → m Z)
    (equal : E → F → m Eq) (isMissing : Eq → Bool) (notEqual : Eq → m Bool)
    (a : A) (b : B) : m (Option Bool) := do
  if (← axesA a) != (← axesB b) then return some false
  let mut anyMissing := false
  for (x, y) in (← zip a b) do
    let eq ← equal x y
    if isMissing eq then anyMissing := true
    else if ← notEqual eq then return some false
  return if anyMissing then none else some true

/--
Julia source: base/abstractarray.jl:3167-3170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sub2ind(A::AbstractArray, I...)
    @inline
    _sub2ind(axes(A), I...)
end
```
-/
def sub2indArray {A Ax I R : Type} (axes : A → Result Ax)
    (sub2ind : Ax → I → Result R) (a : A) (is : I) : Result R := do
  sub2ind (← axes a) is

/--
Julia source: base/abstractarray.jl:3172-3175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ind2sub(A::AbstractArray, ind)
    @inline
    _ind2sub(axes(A), ind)
end
```
-/
def ind2subArray {A Ax I R : Type} (axes : A → Result Ax)
    (ind2sub : Ax → I → Result R) (a : A) (i : I) : Result R := do
  ind2sub (← axes a) i

/--
Julia source: base/abstractarray.jl:3178-3178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(::Tuple{}) = 1
```
-/
def sub2indEmpty : I64 := int 1

/--
Julia source: base/abstractarray.jl:3179-3179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(::DimsInteger) = 1
```
-/
def sub2indDimsNoIndices {D : Type} (_dims : D) : I64 := int 1

/--
Julia source: base/abstractarray.jl:3180-3180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(::Indices) = 1
```
-/
def sub2indAxesNoIndices {Ax : Type} (_axes : Ax) : I64 := int 1

/--
Julia source: base/abstractarray.jl:3181-3181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(::Tuple{}, I::Integer...) = (@inline; _sub2ind_recurse((), 1, 1, I...))
```
-/
def sub2indEmptyIndices {I R : Type}
    (recurse : Unit → I64 → I64 → I → Result R) (is : I) : Result R :=
  recurse () (int 1) (int 1) is

/--
Julia source: base/abstractarray.jl:3184-3184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(dims::DimsInteger, I::Integer...) = (@inline; _sub2ind_recurse(dims, 1, 1, I...))
```
-/
def sub2indDims {D I R : Type}
    (recurse : D → I64 → I64 → I → Result R) (dims : D) (is : I) : Result R :=
  recurse dims (int 1) (int 1) is

/--
Julia source: base/abstractarray.jl:3185-3185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Indices, I::Integer...) = (@inline; _sub2ind_recurse(inds, 1, 1, I...))
```
-/
def sub2indAxes {Ax I R : Type}
    (recurse : Ax → I64 → I64 → I → Result R) (axes : Ax) (is : I) : Result R :=
  recurse axes (int 1) (int 1) is

/--
Julia source: base/abstractarray.jl:3188-3189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Indices{1}, I::Integer...) =
    throw(ArgumentError("Linear indexing is not defined for one-dimensional arrays"))
```
-/
def sub2indAmbiguousOneDim {Ax I R : Type} (_axes : Ax) (_is : I) : Result R :=
  throw (.julia (.argumentError "Linear indexing is not defined for one-dimensional arrays"))

/--
Julia source: base/abstractarray.jl:3190-3190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Tuple{OneTo}, I::Integer...) = (@inline; _sub2ind_recurse(inds, 1, 1, I...)) # only OneTo is safe
```
-/
def sub2indOneTo {Ax I R : Type}
    (recurse : Ax → I64 → I64 → I → Result R) (axes : Ax) (is : I) : Result R :=
  recurse axes (int 1) (int 1) is

/--
Julia source: base/abstractarray.jl:3191-3191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Tuple{OneTo}, i::Integer)    = i
```
-/
def sub2indOneToScalar {Ax : Type} {t : IntTy} (_axes : Ax) (i : JInt t) : JInt t := i

/--
Julia source: base/abstractarray.jl:3193-3193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind_recurse(::Any, L, ind) = ind
```
-/
def sub2indRecurseDone {Ax L Ind : Type} (_axes : Ax) (_stride : L) (ind : Ind) :
    Ind := ind

/--
Julia source: base/abstractarray.jl:3194-3197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sub2ind_recurse(::Tuple{}, L, ind, i::Integer, I::Integer...)
    @inline
    _sub2ind_recurse((), L, ind+(i-1)*L, I...)
end
```
-/
def sub2indRecurseEmpty {L Ind I Off Prod Rest R : Type}
    (sub : I → I64 → Result Off) (mul : Off → L → Result Prod)
    (add : Ind → Prod → Result Ind)
    (recurse : Unit → L → Ind → Rest → Result R)
    (stride : L) (ind : Ind) (i : I) (is : Rest) : Result R := do
  recurse () stride (← add ind (← mul (← sub i (int 1)) stride)) is

/--
Julia source: base/abstractarray.jl:3198-3202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sub2ind_recurse(inds, L, ind, i::Integer, I::Integer...)
    @inline
    r1 = inds[1]
    _sub2ind_recurse(tail(inds), nextL(L, r1), ind+offsetin(i, r1)*L, I...)
end
```
-/
def sub2indRecurse {Ax Axis L Ind I Off Prod Rest R : Type}
    (first : Ax → Result Axis) (tail : Ax → Result Ax)
    (nextL : L → Axis → Result L) (offsetin : I → Axis → Result Off)
    (mul : Off → L → Result Prod) (add : Ind → Prod → Result Ind)
    (recurse : Ax → L → Ind → Rest → Result R)
    (axes : Ax) (stride : L) (ind : Ind) (i : I) (is : Rest) : Result R := do
  let r1 ← first axes
  let rest ← tail axes
  let next ← nextL stride r1
  let index ← add ind (← mul (← offsetin i r1) stride)
  recurse rest next index is

/--
Julia source: base/abstractarray.jl:3204-3204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextL(L, l::Integer) = L*l
```
-/
def nextLInteger {L I R : Type} (mul : L → I → Result R) (stride : L) (n : I) :
    Result R := mul stride n

/--
Julia source: base/abstractarray.jl:3205-3205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextL(L, r::AbstractUnitRange) = L*length(r)
```
-/
def nextLRange {L Axis N R : Type} (length : Axis → Result N)
    (mul : L → N → Result R) (stride : L) (r : Axis) : Result R := do
  mul stride (← length r)

/--
Julia source: base/abstractarray.jl:3206-3206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextL(L, r::Slice) = L*length(r.indices)
```
-/
def nextLSlice {L Slice Axis N R : Type} (indices : Slice → Axis)
    (length : Axis → Result N) (mul : L → N → Result R)
    (stride : L) (r : Slice) : Result R := do
  mul stride (← length (indices r))

/--
Julia source: base/abstractarray.jl:3207-3207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
offsetin(i, l::Integer) = i-1
```
-/
def offsetinInteger {I N R : Type} (sub : I → I64 → Result R) (i : I) (_n : N) :
    Result R := sub i (int 1)

/--
Julia source: base/abstractarray.jl:3208-3208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
offsetin(i, r::AbstractUnitRange) = i-first(r)
```
-/
def offsetinRange {I Axis First R : Type} (first : Axis → Result First)
    (sub : I → First → Result R) (i : I) (r : Axis) : Result R := do
  sub i (← first r)

/--
Julia source: base/abstractarray.jl:3210-3210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(::Tuple{}, ind::Integer) = (@inline; ind == 1 ? () : throw(BoundsError()))
```
-/
def ind2subEmpty {I : Type} (isOne : I → Bool) (ind : I) : Result (List I) :=
  if isOne ind then pure [] else throw (.julia .boundsError)

/--
Julia source: base/abstractarray.jl:3211-3211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(dims::DimsInteger, ind::Integer) = (@inline; _ind2sub_recurse(dims, ind-1))
```
-/
def ind2subDims {D I Off R : Type} (subOne : I → Result Off)
    (recurse : D → Off → Result R) (dims : D) (ind : I) : Result R := do
  recurse dims (← subOne ind)

/--
Julia source: base/abstractarray.jl:3212-3212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(inds::Indices, ind::Integer)     = (@inline; _ind2sub_recurse(inds, ind-1))
```
-/
def ind2subAxes {Ax I Off R : Type} (subOne : I → Result Off)
    (recurse : Ax → Off → Result R) (axes : Ax) (ind : I) : Result R := do
  recurse axes (← subOne ind)

/--
Julia source: base/abstractarray.jl:3213-3214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(inds::Indices{1}, ind::Integer) =
    throw(ArgumentError("Linear indexing is not defined for one-dimensional arrays"))
```
-/

def ind2subAmbiguousOneDim {Ax I R : Type} (_axes : Ax) (_ind : I) : Result R :=
  throw (.julia (.argumentError "Linear indexing is not defined for one-dimensional arrays"))
/--
Julia source: base/abstractarray.jl:3215-3215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(inds::Tuple{OneTo}, ind::Integer) = (ind,)
```
-/

def ind2subOneTo {Ax I : Type} (_axes : Ax) (ind : I) : List I := [ind]
/--
Julia source: base/abstractarray.jl:3217-3217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub_recurse(::Tuple{}, ind) = (ind+1,)
```
-/

def ind2subRecurseEmpty {I R : Type} (addOne : I → Result R) (ind : I) :
    Result (List R) := do
  return [← addOne ind]
/--
Julia source: base/abstractarray.jl:3218-3221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ind2sub_recurse(indslast::NTuple{1}, ind)
    @inline
    (_lookup(ind, indslast[1]),)
end
```
-/

def ind2subRecurseLast {Ax Axis I R : Type} (first : Ax → Result Axis)
    (lookup : I → Axis → Result R) (axes : Ax) (ind : I) : Result (List R) := do
  return [← lookup ind (← first axes)]
/--
Julia source: base/abstractarray.jl:3222-3227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ind2sub_recurse(inds, ind)
    @inline
    r1 = inds[1]
    indnext, indsub = divrem(ind, _indexlength(r1))
    (_lookup(indsub, r1), _ind2sub_recurse(tail(inds), indnext)...)
end
```
-/

def ind2subRecurse {Ax Axis I Len R : Type} (first : Ax → Result Axis)
    (indexLength : Axis → Result Len) (divrem : I → Len → Result (I × I))
    (lookup : I → Axis → Result R) (tail : Ax → Result Ax)
    (recurse : Ax → I → Result (List R)) (axes : Ax) (ind : I) : Result (List R) := do
  let r1 ← first axes
  let (next, sub) ← divrem ind (← indexLength r1)
  let coordinate ← lookup sub r1
  return coordinate :: (← recurse (← tail axes) next)
/--
Julia source: base/abstractarray.jl:3229-3229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indexlength(d::Integer) = d
```
-/

def indexLengthInteger (d : I) : I := d
/--
Julia source: base/abstractarray.jl:3230-3230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indexlength(r::AbstractUnitRange) = length(r)
```
-/

def indexLengthRange {Axis I : Type} (length : Axis → Result I) (r : Axis) :
    Result I := length r
/--
Julia source: base/abstractarray.jl:3231-3231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_lookup(ind, d::Integer) = ind+1
```
-/

def lookupInteger {I D R : Type} (addOne : I → Result R) (ind : I) (_d : D) :
    Result R := addOne ind
/--
Julia source: base/abstractarray.jl:3232-3232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_lookup(ind, r::AbstractUnitRange) = ind+first(r)
```
-/

def lookupRange {I Axis First R : Type} (first : Axis → Result First)
    (add : I → First → Result R) (ind : I) (r : Axis) : Result R := do
  add ind (← first r)
/--
Julia source: base/abstractarray.jl:3235-3237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sub2ind(inds::Indices{1}, I1::AbstractVector{T}, I::AbstractVector{T}...) where T<:Integer
    throw(ArgumentError("Linear indexing is not defined for one-dimensional arrays"))
end
```
-/
def sub2indVectorsAmbiguous {Ax V R : Type} (_axes : Ax) (_first : V) (_rest : List V) :
    Result R :=
  throw (.julia (.argumentError "Linear indexing is not defined for one-dimensional arrays"))

/--
Julia source: base/abstractarray.jl:3238-3239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Tuple{OneTo}, I1::AbstractVector{T}, I::AbstractVector{T}...) where {T<:Integer} =
    _sub2ind_vecs(inds, I1, I...)
```
-/
def sub2indVectorsOneTo {m : Type → Type} [Monad m] {Ax V Out : Type}
    (vectors : Ax → List V → m Out) (axes : Ax) (first : V) (rest : List V) : m Out :=
  vectors axes (first :: rest)

/--
Julia source: base/abstractarray.jl:3240-3241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Union{DimsInteger,Indices}, I1::AbstractVector{T}, I::AbstractVector{T}...) where {T<:Integer} =
    _sub2ind_vecs(inds, I1, I...)
```
-/
def sub2indVectors {m : Type → Type} [Monad m] {Ax V Out : Type}
    (vectors : Ax → List V → m Out) (axes : Ax) (first : V) (rest : List V) : m Out :=
  vectors axes (first :: rest)

/--
Julia source: base/abstractarray.jl:3242-3251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sub2ind_vecs(inds, I::AbstractVector...)
    I1 = I[1]
    Iinds = axes1(I1)
    for j = 2:length(I)
        axes1(I[j]) == Iinds || throw(DimensionMismatch("indices of I[1] ($(Iinds)) does not match indices of I[$j] ($(axes1(I[j])))"))
    end
    Iout = similar(I1)
    _sub2ind!(Iout, inds, Iinds, I)
    Iout
end
```
-/
def sub2indVecs {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ax V Axis Out : Type} [DecidableEq Axis]
    (get : List V → I64 → m V) (axes1 : V → m Axis) (showAxis : Axis → String)
    (range : I64 → I64 → m (List I64)) (similar : V → m Out)
    (fill : Out → Ax → Axis → List V → m Out)
    (axes : Ax) (vectors : List V) : m Out := do
  let first ← get vectors (int 1)
  let inds ← axes1 first
  for j in (← range (int 2) (int vectors.length)) do
    if (← axes1 (← get vectors j)) != inds then
      throw (.dimensionMismatch ("indices of I[1] (" ++ showAxis inds ++
        ") does not match indices of I[" ++ toString j.val ++ "] (" ++
        showAxis (← axes1 (← get vectors j)) ++ ")"))
  let out ← similar first
  let _ ← fill out axes inds vectors
  return out

/--
Julia source: base/abstractarray.jl:3253-3260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sub2ind!(Iout, inds, Iinds, I)
    @noinline
    for i in Iinds
        # Iout[i] = _sub2ind(inds, map(Ij -> Ij[i], I)...)
        Iout[i] = sub2ind_vec(inds, i, I)
    end
    Iout
end
```
-/
def sub2indFill {m : Type → Type} [Monad m]
    {Out Ax Axis V I E : Type} [ForIn m Axis I]
    (sub2indVec : Ax → I → List V → m E) (set : Out → I → E → m Unit)
    (out : Out) (axes : Ax) (indices : Axis) (vectors : List V) : m Out := do
  for i in indices do set out i (← sub2indVec axes i vectors)
  return out

/--
Julia source: base/abstractarray.jl:3262-3262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sub2ind_vec(inds, i, I) = (@inline; _sub2ind(inds, _sub2ind_vec(i, I...)...))
```
-/
def sub2indVec {m : Type → Type} [Monad m] {Ax I V C Out : Type}
    (coordinates : I → List V → m C) (sub2ind : Ax → C → m Out)
    (axes : Ax) (i : I) (vectors : List V) : m Out := do
  sub2ind axes (← coordinates i vectors)

/--
Julia source: base/abstractarray.jl:3263-3263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind_vec(i, I1, I...) = (@inline; (I1[i], _sub2ind_vec(i, I...)...))
```
-/
def sub2indVecMore {m : Type → Type} [Monad m] {I V E : Type}
    (get : V → I → m E) (recurse : I → List V → m (List E))
    (i : I) (first : V) (rest : List V) : m (List E) := do
  let value ← get first i
  return value :: (← recurse i rest)

/--
Julia source: base/abstractarray.jl:3264-3264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind_vec(i) = ()
```
-/
def sub2indVecEmpty {I E : Type} (_i : I) : List E := []

/--
Julia source: base/abstractarray.jl:3266-3275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ind2sub(inds::Union{DimsInteger{N},Indices{N}}, ind::AbstractVector{<:Integer}) where N
    t = ntuple(_->similar(ind),Val(N))
    for (i,idx) in pairs(IndexLinear(), ind)
        sub = _ind2sub(inds, idx)
        for j = 1:N
            t[j][i] = sub[j]
        end
    end
    t
end
```
-/
def ind2subVectors {m : Type → Type} [Monad m]
    {Ax V Out I E C Coordinate Pairs : Type} [ForIn m Pairs (I × E)]
    (similar : V → m Out) (ntuple : (Nat → m Out) → Nat → m (List Out))
    (pairs : V → m Pairs) (ind2sub : Ax → E → m C)
    (range : I64 → I64 → m (List I64)) (getOutput : List Out → I64 → m Out)
    (getCoordinate : C → I64 → m Coordinate) (set : Out → I → Coordinate → m Unit)
    (rank : Nat) (axes : Ax) (ind : V) : m (List Out) := do
  let outputs ← ntuple (fun _ => similar ind) rank
  for (i, idx) in (← pairs ind) do
    let sub ← ind2sub axes idx
    for j in (← range (int 1) (int rank)) do
      set (← getOutput outputs j) i (← getCoordinate sub j)
  return outputs

/--
Julia source: base/abstractarray.jl:3307-3307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
foreach(f, itr) = (for x in itr; f(x); end; nothing)
```
-/
def foreach {m : Type → Type} [Monad m] {It E R : Type} [ForIn m It E]
    (f : E → m R) (iter : It) : m Unit := do
  for x in iter do let _ ← f x

/--
Julia source: base/abstractarray.jl:3308-3308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
foreach(f, itr, itrs...) = (for z in zip(itr, itrs...); f(z...); end; nothing)
```
-/
def foreachZip {m : Type → Type} [Monad m] {It Rest Z E R : Type} [ForIn m Z E]
    (zip : It → Rest → m Z) (f : E → m R) (iter : It) (iters : Rest) : m Unit := do
  for args in (← zip iter iters) do let _ ← f args

/--
Julia source: base/abstractarray.jl:3385-3448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function mapslices(f, A::AbstractArray; dims)
    isempty(dims) && return map(f, A)

    for d in dims
        d isa Integer || throw(ArgumentError("mapslices: dimension must be an integer, got $d"))
        d >= 1 || throw(ArgumentError("mapslices: dimension must be ≥ 1, got $d"))
        # Indexing a matrix M[:,1,:] produces a 1-column matrix, but dims=(1,3) here
        # would otherwise ignore 3, and slice M[:,i]. Previously this gave error:
        # BoundsError: attempt to access 2-element Vector{Any} at index [3]
        d > ndims(A) && throw(ArgumentError("mapslices does not accept dimensions > ndims(A) = $(ndims(A)), got $d"))
    end
    dim_mask = ntuple(d -> d in dims, ndims(A))

    # Apply the function to the first slice in order to determine the next steps
    idx1 = ntuple(d -> d in dims ? (:) : firstindex(A,d), ndims(A))
    Aslice = A[idx1...]
    r1 = f(Aslice)

    res1 = if r1 isa AbstractArray && ndims(r1) > 0
        n = sum(dim_mask)
        if ndims(r1) > n && any(ntuple(d -> size(r1,d+n)>1, ndims(r1)-n))
            s = size(r1)[1:n]
            throw(DimensionMismatch("mapslices cannot assign slice f(x) of size $(size(r1)) into output of size $s"))
        end
        r1
    else
        # If the result of f on a single slice is a scalar then we add singleton
        # dimensions. When adding the dimensions, we have to respect the
        # index type of the input array (e.g. in the case of OffsetArrays)
        _res1 = similar(Aslice, typeof(r1), reduced_indices(Aslice, 1:ndims(Aslice)))
        _res1[begin] = r1
        _res1
    end

    # Determine result size and allocate. We always pad ndims(res1) out to length(dims):
    din = Ref(0)
    Rsize = ntuple(ndims(A)) do d
        if d in dims
            axes(res1, din[] += 1)
        else
            axes(A,d)
        end
    end
    R = similar(res1, Rsize)

    # Determine iteration space. It will be convenient in the loop to mask N-dimensional
    # CartesianIndices, with some trivial dimensions:
    itershape = ntuple(d -> d in dims ? Base.OneTo(1) : axes(A,d), ndims(A))
    indices = Iterators.drop(CartesianIndices(itershape), 1)

    # That skips the first element, which we already have:
    ridx = ntuple(d -> d in dims ? Slice(axes(R,d)) : firstindex(A,d), ndims(A))
    concatenate_setindex!(R, res1, ridx...)

    # In some cases, we can re-use the first slice for a dramatic performance
    # increase. The slice itself must be mutable and the result cannot contain
    # any mutable containers. The following errs on the side of being overly
    # strict (#18570 & #21123).
    safe_for_reuse = isa(Aslice, StridedArray) &&
                     (isa(r1, Number) || (isa(r1, AbstractArray) && eltype(r1) <: Number))

    _inner_mapslices!(R, indices, f, A, dim_mask, Aslice, safe_for_reuse)
    return R
end
```
-/
def mapslices {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {F A X Y Res R D Ax Ix Ty Indices : Type}
    (map : F → A → m R) (isInteger belowOne : D → Bool)
    (aboveRank : D → I64 → Bool) (showDim : D → String)
    (ndims : A → m I64) (contains : I64 → List D → Bool)
    (ntupleBool : (I64 → m Bool) → I64 → m (List Bool))
    (ntupleIndex : (I64 → m Ix) → I64 → m (List Ix))
    (ntupleAxes : (I64 → m Ax) → I64 → m (List Ax))
    (colon : Ix) (firstindex : A → I64 → m Ix) (getSlice : A → List Ix → m X)
    (apply : F → X → m Y) (isArray isNumber : Y → Bool)
    (ndimsResult : Y → m I64) (sizeResult : Y → m (List I64))
    (sizeResultDim : Y → I64 → m I64) (showShape : List I64 → String)
    (arrayResult : Y → Res) (typeof : Y → Ty)
    (ndimsSlice : X → m I64) (range : I64 → I64 → m (List I64))
    (reducedIndices : X → List I64 → m (List Ax))
    (similarSlice : X → Ty → List Ax → m Res)
    (firstResult : Res → m Ix) (setResult : Res → Ix → Y → m Unit)
    (axisResult : Res → I64 → m Ax) (axisInput : A → I64 → m Ax)
    (similar : Res → List Ax → m R) (oneTo : I64 → m Ax)
    (cartesianDropFirst : List Ax → m Indices) (axisOutput : R → I64 → m Ax)
    (slice : Ax → m Ix) (concatenateSet : R → Res → List Ix → m Res)
    (isStrided : X → Bool) (eltype : Y → m Ty) (isNumberType : Ty → Bool)
    (inner : R → Indices → F → A → List Bool → X → Bool → m Unit)
    (f : F) (a : A) (dims : List D) : m R := do
  if dims.isEmpty then return ← map f a
  for d in dims do
    if !isInteger d then
      throw (.julia (.argumentError ("mapslices: dimension must be an integer, got " ++ showDim d)))
    if belowOne d then
      throw (.julia (.argumentError ("mapslices: dimension must be ≥ 1, got " ++ showDim d)))
    if aboveRank d (← ndims a) then
      throw (.julia (.argumentError ("mapslices does not accept dimensions > ndims(A) = " ++
        toString (← ndims a).val ++ ", got " ++ showDim d)))
  let mask ← ntupleBool (fun d => pure (contains d dims)) (← ndims a)
  let idx1 ← ntupleIndex (fun d =>
    if contains d dims then pure colon else firstindex a d) (← ndims a)
  let aslice ← getSlice a idx1
  let r1 ← apply f aslice
  let positiveArray ← if isArray r1 then
      (fun rank => decide (0 < rank.val)) <$> ndimsResult r1
    else pure false
  let res1 ← if positiveArray then do
      let n := int (mask.count true)
      if (← ndimsResult r1).val > n.val then
        let large ← ntupleBool (fun d => do
          return decide (1 < (← sizeResultDim r1 (d + n)).val)) ((← ndimsResult r1) - n)
        if large.any id then
          let s := (← sizeResult r1).take n.val.toNat
          throw (.dimensionMismatch ("mapslices cannot assign slice f(x) of size " ++
            showShape (← sizeResult r1) ++ " into output of size " ++ showShape s))
      pure (arrayResult r1)
    else do
      let r ← similarSlice aslice (typeof r1)
        (← reducedIndices aslice (← range (int 1) (← ndimsSlice aslice)))
      setResult r (← firstResult r) r1
      pure r
  let mut din := int 0
  let mut rsize : List Ax := []
  for d in (← range (int 1) (← ndims a)) do
    if contains d dims then
      din := din + int 1
      let ax ← axisResult res1 din
      rsize := ax :: rsize
    else
      let ax ← axisInput a d
      rsize := ax :: rsize
  let r ← similar res1 rsize.reverse
  let iterShape ← ntupleAxes (fun d =>
    if contains d dims then oneTo (int 1) else axisInput a d) (← ndims a)
  let indices ← cartesianDropFirst iterShape
  let ridx ← ntupleIndex (fun d => do
    if contains d dims then slice (← axisOutput r d) else firstindex a d) (← ndims a)
  let _ ← concatenateSet r res1 ridx
  let safe ← if isStrided aslice then
      if isNumber r1 then pure true
      else if isArray r1 then isNumberType <$> eltype r1
      else pure false
    else pure false
  inner r indices f a mask aslice safe
  return r

/--
Julia source: base/abstractarray.jl:3450-3475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _inner_mapslices!(R, indices, f, A, dim_mask, Aslice, safe_for_reuse)
    must_extend = any(dim_mask .& size(R) .> 1)
    if safe_for_reuse
        # when f returns an array, R[ridx...] = f(Aslice) line copies elements,
        # so we can reuse Aslice
        for I in indices
            idx = ifelse.(dim_mask, Slice.(axes(A)), Tuple(I))
            _unsafe_getindex!(Aslice, A, idx...)
            r = f(Aslice)
            if r isa AbstractArray || must_extend
                ridx = ifelse.(dim_mask, Slice.(axes(R)), Tuple(I))
                R[ridx...] = r
            else
                ridx = ifelse.(dim_mask, first.(axes(R)), Tuple(I))
                R[ridx...] = r
            end
        end
    else
        # we can't guarantee safety (#18524), so allocate new storage for each slice
        for I in indices
            idx = ifelse.(dim_mask, Slice.(axes(A)), Tuple(I))
            ridx = ifelse.(dim_mask, Slice.(axes(R)), Tuple(I))
            concatenate_setindex!(R, f(A[idx...]), ridx...)
        end
    end
end
```
-/
def innerMapslices {m : Type → Type} [Monad m]
    {R A X Y F Ax Ix C Indices Ret : Type} [ForIn m Indices C]
    (size : R → m (List I64)) (extendMask : List Bool → List I64 → m (List Bool))
    (axesInput : A → m (List Ax)) (axesOutput : R → m (List Ax))
    (slice first : Ax → m Ix) (coordinates : C → m (List Ix))
    (select : List Bool → List Ix → List Ix → m (List Ix))
    (unsafeGet : X → A → List Ix → m Unit) (apply : F → X → m Y)
    (isArray : Y → Bool) (set : R → Y → List Ix → m Unit)
    (getSlice : A → List Ix → m X) (concatenateSet : R → Y → List Ix → m Ret)
    (r : R) (indices : Indices) (f : F) (a : A)
    (mask : List Bool) (aslice : X) (safeForReuse : Bool) : m Unit := do
  let mustExtend := (← extendMask mask (← size r)).any id
  if safeForReuse then
    for i in indices do
      let idx ← select mask (← (← axesInput a).mapM slice) (← coordinates i)
      unsafeGet aslice a idx
      let value ← apply f aslice
      if isArray value || mustExtend then
        let ridx ← select mask (← (← axesOutput r).mapM slice) (← coordinates i)
        set r value ridx
      else
        let ridx ← select mask (← (← axesOutput r).mapM first) (← coordinates i)
        set r value ridx
  else
    for i in indices do
      let idx ← select mask (← (← axesInput a).mapM slice) (← coordinates i)
      let ridx ← select mask (← (← axesOutput r).mapM slice) (← coordinates i)
      let _ ← concatenateSet r (← apply f (← getSlice a idx)) ridx

/--
Julia source: base/abstractarray.jl:3477-3477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
concatenate_setindex!(R, v, I...) = (R[I...] .= (v,); R)
```
-/
def concatenateSetScalar {m : Type → Type} [Monad m] {R E I View : Type}
    (view : R → I → m View) (broadcast : View → List E → m Unit)
    (r : R) (value : E) (indices : I) : m R := do
  broadcast (← view r indices) [value]
  return r

/--
Julia source: base/abstractarray.jl:3478-3478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
concatenate_setindex!(R, X::AbstractArray, I...) = (R[I...] = X)
```
-/
def concatenateSetArray {m : Type → Type} [Monad m] {R A I Ret : Type}
    (set : R → A → I → m Ret) (r : R) (a : A) (indices : I) : m A := do
  let _ ← set r a indices
  return a

/--
Julia source: base/abstractarray.jl:3482-3488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map!(f::F, dest::AbstractArray, A::AbstractArray) where F
    for (i,j) in zip(eachindex(dest),eachindex(A))
        val = f(@inbounds A[j])
        @inbounds dest[i] = val
    end
    return dest
end
```
-/
def mapInplaceOne {m : Type → Type} [Monad m]
    {D A E F ID IA IndD IndA Z : Type} [ForIn m Z (ID × IA)]
    (eachDest : D → m IndD) (eachSrc : A → m IndA) (zip : IndD → IndA → m Z)
    (get : A → IA → m E) (set : D → ID → F → m Unit)
    (f : E → m F) (dest : D) (a : A) : m D := do
  for (i, j) in (← zip (← eachDest dest) (← eachSrc a)) do
    let value ← f (← get a j)
    set dest i value
  return dest

/--
Julia source: base/abstractarray.jl:3491-3491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, A::AbstractArray) = collect_similar(A, Generator(f,A))
```
-/
def mapArray {m : Type → Type} [Monad m] {A E F G R : Type}
    (generator : (E → m F) → A → m G) (collectSimilar : A → G → m R)
    (f : E → m F) (a : A) : m R := do
  collectSimilar a (← generator f a)

/--
Julia source: base/abstractarray.jl:3493-3493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapany(f, A::AbstractArray) = map!(f, Vector{Any}(undef, length(A)), A)
```
-/
def mapAnyArray {m : Type → Type} [Monad m] {A E F D : Type}
    (length : A → m I64) (allocateAny : I64 → m D)
    (map : (E → m F) → D → A → m D) (f : E → m F) (a : A) : m D := do
  map f (← allocateAny (← length a)) a

/--
Julia source: base/abstractarray.jl:3494-3494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapany(f, itr) = Any[f(x) for x in itr]
```
-/
def mapAnyIterator {m : Type → Type} [Monad m] {It E F G A : Type}
    (generator : (E → m F) → It → m G) (collectAny : G → m A)
    (f : E → m F) (iter : It) : m A := do
  collectAny (← generator f iter)

/--
Julia source: base/abstractarray.jl:3521-3521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, A) = collect(Generator(f,A)) # default to returning an Array for `map` on general iterators
```
-/
def mapIterator {m : Type → Type} [Monad m] {It E F G A : Type}
    (generator : (E → m F) → It → m G) (collect : G → m A)
    (f : E → m F) (iter : It) : m A := do
  collect (← generator f iter)

/--
Julia source: base/abstractarray.jl:3523-3523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, ::AbstractDict) = error("map is not defined on dictionaries")
```
-/
def mapDictionary {F D R : Type} (_f : F) (_dict : D) : Result R :=
  throw (.errorException "map is not defined on dictionaries")

/--
Julia source: base/abstractarray.jl:3524-3524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, ::AbstractSet) = error("map is not defined on sets")
```
-/
def mapSet {F S R : Type} (_f : F) (_set : S) : Result R :=
  throw (.errorException "map is not defined on sets")

/--
Julia source: base/abstractarray.jl:3527-3534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map!(f::F, dest::AbstractArray, A::AbstractArray, B::AbstractArray) where F
    for (i, j, k) in zip(eachindex(dest), eachindex(A), eachindex(B))
        @inbounds a, b = A[j], B[k]
        val = f(a, b)
        @inbounds dest[i] = val
    end
    return dest
end
```
-/
def mapInplaceTwo {m : Type → Type} [Monad m]
    {D A B E F G ID IA IB IndD IndA IndB Z : Type} [ForIn m Z (ID × IA × IB)]
    (eachDest : D → m IndD) (eachA : A → m IndA) (eachB : B → m IndB)
    (zip : IndD → IndA → IndB → m Z) (getA : A → IA → m E) (getB : B → IB → m F)
    (set : D → ID → G → m Unit) (f : E → F → m G)
    (dest : D) (a : A) (b : B) : m D := do
  for (i, j, k) in (← zip (← eachDest dest) (← eachA a) (← eachB b)) do
    let av ← getA a j
    let bv ← getB b k
    let value ← f av bv
    set dest i value
  return dest

/--
Julia source: base/abstractarray.jl:3538-3538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline ith_all(i, ::Tuple{}) = ()
```
-/

def ithAllEmpty {I E : Type} (_i : I) : List E := []
/--
Julia source: base/abstractarray.jl:3539-3542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ith_all(i, as)
    @_propagate_inbounds_meta
    return (as[1][i], ith_all(i, tail(as))...)
end
```
-/
def ithAll {m : Type → Type} [Monad m] {I As A E : Type}
    (first : As → m A) (get : A → I → m E) (tail : As → m As)
    (recurse : I → As → m (List E)) (i : I) (as : As) : m (List E) := do
  let value ← get (← first as) i
  return value :: (← recurse i (← tail as))

/--
Julia source: base/abstractarray.jl:3544-3560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map_n!(f::F, dest::AbstractArray, As) where F
    idxs = LinearIndices(dest)
    if all(x -> LinearIndices(x) == idxs, As)
        for i in idxs
            @inbounds as = ith_all(i, As)
            val = f(as...)
            @inbounds dest[i] = val
        end
    else
        for (i, Is...) in zip(eachindex(dest), map(eachindex, As)...)
            as = ntuple(j->getindex(As[j], Is[j]), length(As))
            val = f(as...)
            dest[i] = val
        end
    end
    return dest
end
```
-/
def mapNInplace {m : Type → Type} [Monad m]
    {D A Input Output Args Lin I ID J IndD IndA Z : Type}
    [ForIn m Lin I] [ForIn m Z (ID × List J)]
    (linearDest : D → m Lin) (linearSrc : A → m Lin)
    (equalIndices : Lin → Lin → m Bool)
    (all : (A → m Bool) → List A → m Bool)
    (ithAll : I → List A → m Args) (setLinear : D → I → Output → m Unit)
    (eachDest : D → m IndD) (eachSrc : A → m IndA)
    (mapIndices : (A → m IndA) → List A → m (List IndA))
    (zip : IndD → List IndA → m Z)
    (getArray : List A → I64 → m A) (getIndex : List J → I64 → m J)
    (get : A → J → m Input)
    (ntuple : (I64 → m Input) → Nat → m Args)
    (setDest : D → ID → Output → m Unit)
    (f : Args → m Output) (dest : D) (as : List A) : m D := do
  let indices ← linearDest dest
  if ← all (fun a => do equalIndices (← linearSrc a) indices) as then
    for i in indices do
      let args ← ithAll i as
      let value ← f args
      setLinear dest i value
  else
    for (i, is) in (← zip (← eachDest dest) (← mapIndices eachSrc as)) do
      let args ← ntuple (fun j => do get (← getArray as j) (← getIndex is j)) as.length
      let value ← f args
      setDest dest i value
  return dest

/--
Julia source: base/abstractarray.jl:3593-3596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map!(f::F, dest::AbstractArray, As::AbstractArray...) where {F}
    @assert !isempty(As) "should dispatch to map!(f, A)"
    map_n!(f, dest, As)
end
```
-/
def mapInplaceMany {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D A Args E : Type} (map : (Args → m E) → D → List A → m D)
    (f : Args → m E) (dest : D) (as : List A) : m D := do
  if as.isEmpty then throw (.assertionError "should dispatch to map!(f, A)")
  map f dest as

/--
Julia source: base/abstractarray.jl:3618-3618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map!(f::F, inout::AbstractArray) where F = map!(f, inout, inout)
```
-/
def mapInplace {m : Type → Type} [Monad m] {A E F : Type}
    (map : (E → m F) → A → A → m A) (f : E → m F) (a : A) : m A :=
  map f a a

/--
Julia source: base/abstractarray.jl:3645-3645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, it, iters...) = collect(Generator(f, it, iters...))
```
-/
def mapMany {m : Type → Type} [Monad m] {It Rest Args E G A : Type}
    (generator : (Args → m E) → It → Rest → m G) (collect : G → m A)
    (f : Args → m E) (iter : It) (iters : Rest) : m A := do
  collect (← generator f iter iters)

/--
Julia source: base/abstractarray.jl:3649-3656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(a::AbstractVector{T}, item) where T
    # convert first so we don't grow the array if the assignment won't work
    itemT = item isa T ? item : convert(T, item)::T
    new_length = length(a) + 1
    resize!(a, new_length)
    a[end] = itemT
    return a
end
```
-/
def pushOne {m : Type → Type} [Monad m] {A Raw Converted E Ret : Type}
    (isTarget : Raw → Bool) (asTarget : Raw → E)
    (convert : Raw → m Converted) (assertType : Converted → m E)
    (length : A → m I64) (resize : A → I64 → m Ret)
    (lastindex : A → m I64) (set : A → I64 → E → m Unit)
    (a : A) (item : Raw) : m A := do
  let itemT ← if isTarget item then pure (asTarget item) else do assertType (← convert item)
  let newLength := (← length a) + int 1
  let _ ← resize a newLength
  set a (← lastindex a) itemT
  return a

/--
Julia source: base/abstractarray.jl:3659-3664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(a::AbstractVector{Any}, @nospecialize x)
    new_length = length(a) + 1
    resize!(a, new_length)
    a[end] = x
    return a
end
```
-/
def pushOneAny {m : Type → Type} [Monad m] {A E Ret : Type}
    (length : A → m I64) (resize : A → I64 → m Ret)
    (lastindex : A → m I64) (set : A → I64 → E → m Unit)
    (a : A) (item : E) : m A := do
  let newLength := (← length a) + int 1
  let _ ← resize a newLength
  set a (← lastindex a) item
  return a

/--
Julia source: base/abstractarray.jl:3665-3675 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(a::AbstractVector{Any}, @nospecialize x...)
    @_terminates_locally_meta
    na = length(a)
    nx = length(x)
    resize!(a, na + nx)
    e = lastindex(a) - nx
    for i = 1:nx
        a[e+i] = x[i]
    end
    return a
end
```
-/
def pushManyAny {m : Type → Type} [Monad m] {A E Ret : Type}
    (length : A → m I64) (resize : A → I64 → m Ret) (lastindex : A → m I64)
    (range : I64 → I64 → m (List I64)) (get : List E → I64 → m E)
    (set : A → I64 → E → m Unit) (a : A) (items : List E) : m A := do
  let na ← length a
  let nx := int items.length
  let _ ← resize a (na + nx)
  let e := (← lastindex a) - nx
  for i in (← range (int 1) nx) do set a (e + i) (← get items i)
  return a

/--
Julia source: base/abstractarray.jl:3679-3679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(A, a, b) = push!(push!(A, a), b)
```
-/
def pushTwo {m : Type → Type} [Monad m] {A B R X Y : Type}
    (pushX : A → X → m B) (pushY : B → Y → m R)
    (a : A) (x : X) (y : Y) : m R := do
  pushY (← pushX a x) y

/--
Julia source: base/abstractarray.jl:3680-3680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(A, a, b, c...) = push!(push!(A, a, b), c...)
```
-/
def pushMany {m : Type → Type} [Monad m] {A B R X Y Rest : Type}
    (pushTwo : A → X → Y → m B) (pushRest : B → Rest → m R)
    (a : A) (x : X) (y : Y) (rest : Rest) : m R := do
  pushRest (← pushTwo a x y) rest

/--
Julia source: base/abstractarray.jl:3681-3681 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pushfirst!(A, a, b) = pushfirst!(pushfirst!(A, b), a)
```
-/
def pushfirstTwo {m : Type → Type} [Monad m] {A B R X Y : Type}
    (pushY : A → Y → m B) (pushX : B → X → m R)
    (a : A) (x : X) (y : Y) : m R := do
  pushX (← pushY a y) x

/--
Julia source: base/abstractarray.jl:3682-3682 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pushfirst!(A, a, b, c...) = pushfirst!(pushfirst!(A, c...), a, b)
```
-/
def pushfirstMany {m : Type → Type} [Monad m] {A B R X Y Rest : Type}
    (pushRest : A → Rest → m B) (pushTwo : B → X → Y → m R)
    (a : A) (x : X) (y : Y) (rest : Rest) : m R := do
  pushTwo (← pushRest a rest) x y

/--
Julia source: base/abstractarray.jl:3685-3685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizehint!(a::AbstractVector, _) = a
```
-/
def sizeHint {A Hint : Type} (a : A) (_hint : Hint) : A := a

/--
Julia source: base/abstractarray.jl:3688-3693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rest(a::AbstractArray{T}, state...) where {T}
    v = Vector{T}(undef, 0)
    # assume only very few items are taken from the front
    sizehint!(v, length(a))
    return foldl(push!, Iterators.rest(a, state...), init=v)
end
```
-/
def restArray {m : Type → Type} [Monad m] {A Ty State V It E Ret : Type}
    (vector : Ty → I64 → m V) (length : A → m I64) (sizehint : V → I64 → m Ret)
    (rest : A → State → m It)
    (foldl : (V → E → m V) → It → V → m V) (push : V → E → m V)
    (elementType : Ty) (a : A) (state : State) : m V := do
  let v ← vector elementType (int 0)
  let _ ← sizehint v (← length a)
  foldl push (← rest a state) v

/--
Julia source: base/abstractarray.jl:3699-3715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _keepat!(a::AbstractVector, inds)
    local prev
    i = firstindex(a)
    for k in inds
        if @isdefined(prev)
            prev < k || throw(ArgumentError("indices must be unique and sorted"))
        end
        ak = a[k] # must happen even when i==k for bounds checking
        if i != k
            @inbounds a[i] = ak # k > i, so a[i] is inbounds
        end
        prev = k
        i = nextind(a, i)
    end
    deleteat!(a, i:lastindex(a))
    return a
end
```
-/
def keepAtIndices {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Indices I K E Range Ret : Type} [ForIn m Indices K]
    (firstindex lastindex : A → m I) (less : K → K → m Bool)
    (same : I → K → m Bool) (get : A → K → m E) (set : A → I → E → m Unit)
    (nextind : A → I → m I) (range : I → I → m Range)
    (delete : A → Range → m Ret) (a : A) (indices : Indices) : m A := do
  let mut prev : Option K := none
  let mut i ← firstindex a
  for k in indices do
    if let some previous := prev then
      if !(← less previous k) then
        throw (.julia (.argumentError "indices must be unique and sorted"))
    let value ← get a k
    if !(← same i k) then set a i value
    prev := some k
    i ← nextind a i
  let _ ← delete a (← range i (← lastindex a))
  return a

/--
Julia source: base/abstractarray.jl:3717-3729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _keepat!(a::AbstractVector, m::AbstractVector{Bool})
    length(m) == length(a) || throw(BoundsError(a, m))
    j = firstindex(a)
    for i in eachindex(a, m)
        @inbounds begin
            if m[i]
                i == j || (a[j] = a[i])
                j = nextind(a, j)
            end
        end
    end
    deleteat!(a, j:lastindex(a))
end
```
-/
def keepAtMask {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Mask I E Indices Range Ret : Type} [ForIn m Indices I] [DecidableEq I]
    (lengthMask : Mask → m I64) (lengthArray : A → m I64)
    (firstindex lastindex : A → m I) (eachindex : A → Mask → m Indices)
    (getMask : Mask → I → m Bool) (get : A → I → m E)
    (set : A → I → E → m Unit) (nextind : A → I → m I)
    (range : I → I → m Range) (delete : A → Range → m Ret)
    (a : A) (mask : Mask) : m Ret := do
  if (← lengthMask mask).val != (← lengthArray a).val then
    throw (.julia .boundsError)
  let mut j ← firstindex a
  for i in (← eachindex a mask) do
    if ← getMask mask i then
      if i != j then set a j (← get a i)
      j ← nextind a j
  delete a (← range j (← lastindex a))

/--
Julia source: base/abstractarray.jl:3756-3766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function circshift!(a::AbstractVector, shift::Integer)
    n = length(a)
    n == 0 && return a
    shift = mod(shift, n)
    shift == 0 && return a
    l = lastindex(a)
    reverse!(a, firstindex(a), l-shift)
    reverse!(a, l-shift+1, lastindex(a))
    reverse!(a)
    return a
end
```
-/
def circshiftInplace {m : Type → Type} [Monad m]
    {A Shift Reduced Len I Ret : Type}
    (length : A → m Len) (zeroLength : Len → Bool)
    (mod : Shift → Len → m Reduced) (zeroShift : Reduced → Bool)
    (firstindex lastindex : A → m I) (sub : I → Reduced → m I)
    (addOne : I → m I) (reverseRange : A → I → I → m Ret)
    (reverse : A → m Ret) (a : A) (shift : Shift) : m A := do
  let n ← length a
  if zeroLength n then return a
  let shift ← mod shift n
  if zeroShift shift then return a
  let last ← lastindex a
  let _ ← reverseRange a (← firstindex a) (← sub last shift)
  let _ ← reverseRange a (← addOne (← sub last shift)) (← lastindex a)
  let _ ← reverse a
  return a

end JuliaLean.base.abstractarray

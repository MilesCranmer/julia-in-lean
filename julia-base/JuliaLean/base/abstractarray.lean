import JuliaLean.base.operators
import JuliaLean.base.generator
import JuliaLean.base.range
import JuliaLean.base.indices
import JuliaLean.Core
import JuliaLean.Runtime.Strings
import JuliaLean.base.essentials

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
  | showError (error : JuliaLean.Strings.ShowErrorKind)
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
def hasOffsetVector {m : Type → Type} [Monad m] {A I : Type} (firstindex : A → m I)
    (toInt : I → m I64) (a : A) : m Bool := do
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
def requireOneBased {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Args : Type} (hasOffset : Args → m Bool) (as : Args) : m Bool := do
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
def firstindexArray {m : Type → Type} [Monad m] {A R I : Type}
    (eachindexLinear : A → m R) (first : R → m I) (a : A) : m I := do first (← eachindexLinear a)

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
def iterateStartingState {m : Type → Type} [Monad m] {A Style St : Type}
    (indexStyle : A → m Style) (startingState : A → Style → m St)
    (a : A) : m St := do startingState a (← indexStyle a)

/--
Julia source: base/abstractarray.jl:1246-1246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate_starting_state(A, ::IndexLinear) = firstindex(A)
```
-/
def iterateStartingLinear {m : Type → Type} [Monad m] {A I : Type}
    (firstindex : A → m I) (a : A) : m I :=
  firstindex a

/--
Julia source: base/abstractarray.jl:1247-1247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate_starting_state(A, ::IndexStyle) = (eachindex(A),)
```
-/
def iterateStartingCartesian {m : Type → Type} [Monad m] {A Inds : Type}
    (eachindex : A → m Inds) (a : A) : m (Inds × Unit) := do return (← eachindex a, ())

/--
Julia source: base/abstractarray.jl:1250-1250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline iterate(A::AbstractArray, state = iterate_starting_state(A)) = _iterate_abstractarray(A, state)
```
-/
def iterateArray {m : Type → Type} [Monad m] {A St E Next : Type}
    (iterate : A → St → m (Option (E × Next))) (a : A) (state : St) :
    m (Option (E × Next)) := iterate a state

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
def iterateCartesian {m : Type → Type} [Monad m] {A Inds St Next I E : Type}
    (iterate : Inds → St → m (Option (I × Next))) (getindex : A → I → m E)
    (a : A) (state : Inds × St) : m (Option (E × (Inds × Next))) := do
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
def iterateInteger {m : Type → Type} [Monad m] {A I E : Type}
    (checkbounds : A → I → m Bool) (getindex : A → I → m E) (one : I → m I)
    (add : I → I → m I) (a : A) (state : I) : m (Option (E × I)) := do
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

/-- `dim_mask .& size(R) .> 1` from `_inner_mapslices!` (base/abstractarray.jl:3451).
`.&` binds tighter than `.>`, so each mask entry is promoted to `Int` and
bitwise-anded with the size before the comparison. Both tuples have `ndims(A)`
entries. -/
def mapslicesExtendMask (mask : List Bool) (sz : List I64) : List Bool :=
  List.zipWith (fun b s =>
    decide (1 < (JuliaLean.base.int.band (JuliaLean.base.int.ofBool .i64 b) s).val)) mask sz

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
    (size : R → m (List I64))
    (axesInput : A → m (List Ax)) (axesOutput : R → m (List Ax))
    (slice first : Ax → m Ix) (coordinates : C → m (List Ix))
    (select : List Bool → List Ix → List Ix → m (List Ix))
    (unsafeGet : X → A → List Ix → m Unit) (apply : F → X → m Y)
    (isArray : Y → Bool) (set : R → Y → List Ix → m Unit)
    (getSlice : A → List Ix → m X) (concatenateSet : R → Y → List Ix → m Ret)
    (r : R) (indices : Indices) (f : F) (a : A)
    (mask : List Bool) (aslice : X) (safeForReuse : Bool) : m Unit := do
  let mustExtend := (mapslicesExtendMask mask (← size r)).any id
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

namespace JuliaLean.base.abstractarray.Models1Group4

open JuliaLean JuliaLean.base.abstractarray

/-- Exact iteration values for the unit-step Int64 rank ranges used below.
Source: base/range.jl:711,935-942. The natural recursion index is the mathematical
number of remaining iterator advances, not a Julia arithmetic result or a fuel
limit. Each actual iterator advance uses wrapping JInt addition and the source
end check precedes the advance. No source element effects are precomputed. -/
-- Source: base/range.jl:711-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(r::AbstractUnitRange) = first(r) > last(r)
-- /Source
-- Source: base/range.jl:935-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(r::OrdinalRange) = isempty(r) ? nothing : (first(r), first(r))
-- 
-- function iterate(r::OrdinalRange{T}, i) where {T}
--     @inline
--     i == last(r) && return nothing
--     next = convert(T, i + step(r))
--     (next, next)
-- end
-- /Source
def hvncatIntRange (lo hi : I64) : List I64 :=
  if lo.val > hi.val then [] else
    let rec tail : Nat → I64 → List I64
      | 0, _ => []
      | n + 1, current =>
          if current.val == hi.val then [] else
            let next := current + int 1
            next :: tail n next
    lo :: tail (hi.val - lo.val).toNat lo

/-- Int64 specialization of `ntuple(f, Val(N))`, base/ntuple.jl:65-72.
The N::Int type assertion is represented by n's type. The generated path
executes the unrolled f(1), ..., f(N) calls in tuple field order; the fallback
uses the actual unit-range values. Both preserve every effect and exception
of f, including partial effects before a later component fails. -/
-- Source: base/ntuple.jl:65-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function ntuple(f::F, ::Val{N}) where {F,N}
--     (N::Int >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", N)))
--     if @generated
--         :(@ntuple $N i -> f(i))
--     else
--         Tuple(f(i) for i = 1:(N::Int))
--     end
-- end
-- /Source
def hvncatNtupleVal {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {E : Type} (generated : Bool) (f : I64 → m E) (n : I64) : m (List E) := do
  if n.val < 0 then
    throw (.julia (.argumentError ("tuple length should be ≥ 0, got " ++ toString n.val)))
  if generated then
    (List.range n.val.toNat).mapM (fun (k : Nat) => f (int (k : Int) + int 1))
  else
    (hvncatIntRange (int 1) n).mapM f

/-- Closed product of a native Julia size tuple, base/tuple.jl:688,693.
The zero-, one-, two- and variadic-argument multiplication cases retain their
source dispatch. The variadic case's afoldl is specialized to total, wrapping
I64 multiplication, consuming every remaining value in source order. -/
-- Source: base/tuple.jl:688-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- prod(x::Tuple{}) = 1
-- # This is consistent with the regular prod because there is no need for size promotion
-- # if all elements in the tuple are of system size.
-- # It is defined here separately in order to support bootstrap, because it's needed earlier
-- # than the general prod definition is available.
-- prod(x::Tuple{Int, Vararg{Int}}) = *(x...)
-- /Source
-- Source: base/operators.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::Number) = x
-- /Source
-- Source: base/operators.jl:666-676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for op in (:+, :(+%), :*, :(*%), :&, :|, :xor, :min, :max, :kron)
--     @eval begin
--         # note: these definitions must not cause a dispatch loop when +(a,b) is
--         # not defined, and must only try to call 2-argument definitions, so
--         # that defining +(a,b) is sufficient for full functionality.
--         ($op)(a, b, c, xs...) = (@inline; afoldl($op, ($op)(($op)(a,b),c), xs...))
--         # a further concern is that it's easy for a type like (Int,Int...)
--         # to match many definitions, so we need to keep the number of
--         # definitions down to avoid losing type information.
--     end
-- end
-- /Source
-- Source: base/int.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (*)(x::T, y::T) where {T<:BitInteger} = mul_int(x, y)
-- /Source
def hvncatProdDims : List I64 → I64
  | [] => int 1
  | [x] => x
  | [x, y] => x * y
  | x :: y :: z :: rest => rest.foldl (· * ·) ((x * y) * z)

/-- Closed reduction in `prod(size(A)[3:end])`, base/abstractarray.jl:2529.
The sole callback is the existing raw shape observation. The shape tuple is
read once, then its valid suffix is selected and multiplied concretely.
Dropping its first two fields is the immutable tuple indexing specialization
for the actual range 3:length(shape), which may be empty. -/
-- Source: base/abstractarray.jl:2529-2529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     na = prod(size(A)[3:end])
-- /Source
-- Source: base/tuple.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(t::Tuple, r::AbstractArray{<:Any,1}) = (eltype(t)[t[ri] for ri in r]...,)
-- /Source
def hvncatTailProduct {m : Type → Type} [Monad m] {A : Type}
    (sizeAll : A → m (List I64)) (a : A) : m I64 := do
  return hvncatProdDims ((← sizeAll a).drop 2)

/-- Native-Int specialization of base/abstractarray.jl:2417-2421.
Reuses the existing ordered vector-construction/reshape model. N-1 wraps as
Julia Int, and negative ntuple counts raise the actual argument error. Vector
construction/conversion, tuple length observation and reshape retain the existing
array runtime boundary. The N=0 overload selection belongs to the dispatcher;
this definition is the selected generic method body, not a replacement of it.
Non-Int Val parameters remain outside this partial specialization. -/
-- Source: base/abstractarray.jl:2417-2421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(T::Type, ::Val{N}, xs::Number...) where N
--     N < 0 &&
--         throw(ArgumentError("concatenation dimension must be non-negative"))
--     return reshape(T[xs...], (ntuple(Returns(1), Val(N - 1))..., length(xs)))
-- end
-- /Source
def typedHvncatNumbersValNative {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty X V A : Type} (generated : Bool)
    (length : X → m I64) (vector : Ty → X → m V)
    (reshape : V → List I64 → m A) (t : Ty) (n : I64) (xs : X) : m A :=
  typedHvncatNumbersVal (fun d : I64 => pure (decide (d.val < 0)))
    (fun d : I64 => pure (d - int 1))
    (fun d => hvncatNtupleVal generated (fun _ => pure (int 1)) d)
    length vector reshape t n xs

/-- Zero-rank Number tuple dispatch required by assigned
base/abstractarray.jl:2493. This closes dispatch to the existing scalar conversion
and fill model for one argument and the existing error model for any other count.
X represents Number values; the argument list represents an immutable Julia tuple.
Conversion and zero-dimensional fill retain their existing runtime allocation
boundary. The helper introduces no correctness premise for either operation.
The source block includes surrounding overloads solely to identify dispatch;
no additional unassigned method is replaced or claimed translated. -/
-- Source: base/abstractarray.jl:2397-2406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(::Type, ::Val{0}) = _typed_hvncat_0d_only_one()
-- _typed_hvncat(T::Type, ::Val{0}, x) = fill(convert(T, x))
-- _typed_hvncat(T::Type, ::Val{0}, x::Number) = fill(convert(T, x))
-- _typed_hvncat(T::Type, ::Val{0}, x::AbstractArray) = convert.(T, x)
-- _typed_hvncat(::Type, ::Val{0}, ::Any...) = _typed_hvncat_0d_only_one()
-- _typed_hvncat(::Type, ::Val{0}, ::Number...) = _typed_hvncat_0d_only_one()
-- _typed_hvncat(::Type, ::Val{0}, ::AbstractArray...) = _typed_hvncat_0d_only_one()
-- 
-- _typed_hvncat_0d_only_one() =
--     throw(ArgumentError("a 0-dimensional array may only contain exactly one element"))
-- /Source
def typedHvncatZeroNumbersDispatch {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {Ty X E A : Type}
    (convert : Ty → X → m E) (fill : E → m A)
    (t : Ty) (xs : List X) : m A :=
  match xs with
  | [x] => typedHvncatZeroNumber convert fill t x
  | _ =>
    match typedHvncatZeroOnlyOne (A := A) with
    | .ok value => pure value
    | .error error => throw error

/-- Callee-closed numeric empty-shape method at
base/abstractarray.jl:2493. The existing forwarding model is instantiated with
actual zero-rank overload dispatch, preserving all tuple cardinalities. The
Number/Type payloads and conversion/fill effects are the existing runtime
boundary; the boolean argument is ignored exactly as in Julia. -/
-- Source: base/abstractarray.jl:2493-2493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(T::Type, ::Tuple{}, ::Bool, x::Number...) = _typed_hvncat(T, Val(0), x...)
-- /Source
def typedHvncatEmptyShapeNumbersLinked {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {Ty X E A : Type}
    (convert : Ty → X → m E) (fill : E → m A)
    (t : Ty) (rowFirst : Bool) (xs : List X) : m A :=
  typedHvncatEmptyShapeNumbers
    (fun t _ values => typedHvncatZeroNumbersDispatch convert fill t values)
    t rowFirst xs

/-- Number-argument instance of base/abstractarray.jl:2501-2512.
This closes the selected numeric branches at dimensions 1 and 2, using the
existing check ordering. The positive-count check excludes the zero-argument
_typed_hvncat overload before the numeric callee is reached. Generic array and
heterogeneous arguments of the original method remain outside this instance. -/
-- Source: base/abstractarray.jl:2501-2512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat_1d(::Type{T}, ds::Int, ::Val{row_first}, as...) where {T, row_first}
--     lengthas = length(as)
--     ds > 0 ||
--         throw(ArgumentError("`dimsshape` argument must consist of positive integers"))
--     lengthas == ds ||
--         throw(ArgumentError("number of elements does not match `dimshape` argument; expected $ds, got $lengthas"))
--     if row_first
--         return _typed_hvncat(T, Val(2), as...)
--     else
--         return _typed_hvncat(T, Val(1), as...)
--     end
-- end
-- /Source
def typedHvncatOneDimNumbersLinked {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {Ty X V A : Type}
    (generated : Bool) (length : X → m I64) (vector : Ty → X → m V)
    (reshape : V → List I64 → m A)
    (t : Ty) (ds : I64) (rowFirst : Bool) (xs : X) : m A :=
  typedHvncatOneDim length
    (typedHvncatNumbersValNative generated length vector reshape)
    t ds rowFirst xs

/-- Selected numeric singleton-shape method at base/abstractarray.jl:2499.
`dimension` represents the only field of the source Tuple{Int}; tuple lookup
is concrete. The ignored row-first flag and both native count checks are kept.
The required `_typed_hvncat_1d` numeric branches invoke actual existing bodies,
not a supplied typed-hvncat callback. Arguments X denote the actual Number
argument tuple, whose native length is supplied by the existing tuple interface. -/
-- Source: base/abstractarray.jl:2499-2499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(T::Type, dims::Tuple{Int}, ::Bool, as::Number...) = _typed_hvncat_1d(T, dims[1], Val(false), as...)
-- /Source
def typedHvncatOneShapeNumbersLinked {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {Ty X V A : Type}
    (generated : Bool) (length : X → m I64) (vector : Ty → X → m V)
    (reshape : V → List I64 → m A)
    (t : Ty) (dimension : I64) (rowFirst : Bool) (xs : X) : m A :=
  typedHvncatOneShapeNumbers
    (fun dims i => match tupleGet dims i with
      | .ok value => pure value
      | .error error => throw error)
    (typedHvncatOneDimNumbersLinked generated length vector reshape)
    t [dimension] rowFirst xs

/-- Source method base/abstractarray.jl:2527-2554 with its suffix product
and native ranges implemented. A is the actual native Array and X the immutable
argument tuple; raw size, length, index enumeration, access and mutation retain
the original explicit runtime boundary. The source loop body is reused rather
than duplicated, and shared effects preserve errors and partial writes. -/
-- Source: base/abstractarray.jl:2527-2554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _hvncat_fill_loop!(A::Array, row_first::Bool, xs::Tuple)
--     nr, nc = size(A, 1), size(A, 2)
--     na = prod(size(A)[3:end])
--     len = length(xs)
--     nrc = nr * nc
--     if nrc * na != len
--         throw(ArgumentError("argument count $(len) does not match specified shape $(size(A))"))
--     end
--     # putting these in separate functions leads to unnecessary allocations
--     if row_first
--         k = 1
--         for d ∈ 1:na
--             dd = nrc * (d - 1)
--             for i ∈ 1:nr
--                 Ai = dd + i
--                 for _ ∈ 1:nc
--                     @inbounds A[Ai] = xs[k]
--                     k += 1
--                     Ai += nr
--                 end
--             end
--         end
--     else
--         for k ∈ eachindex(xs)
--             @inbounds A[k] = xs[k]
--         end
--     end
-- end
-- /Source
def hvncatFillLoopLinked {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A X E : Type}
    (size : A → I64 → m I64) (sizeAll : A → m (List I64))
    (length : X → m I64) (showShape : A → m String)
    (eachindex : X → m (List I64)) (get : X → I64 → m E)
    (set : A → I64 → E → m Unit)
    (a : A) (rowFirst : Bool) (xs : X) : m Unit :=
  hvncatFillLoop size (hvncatTailProduct sizeAll) length showShape
    (fun lo hi => pure (hvncatIntRange lo hi)) eachindex get set a rowFirst xs

/-- Callee-closed generated/fallback fill at
base/abstractarray.jl:2556-2627. The frozen generated model is reused, and its
non-generated/large-tuple branch invokes the existing hvncatFillLoop body.
Both paths use the same current-store array and tuple primitives. The runtime
fieldcount is the actual immutable tuple arity and rank is the actual Array
type rank; both are representation metadata, not arbitrary performance hints.
The range input of the loop is the closed native range model. The
shape suffix and native tuple product are implemented by hvncatTailProduct;
only raw shape observation remains at that boundary. -/
-- Source: base/abstractarray.jl:2556-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function hvncat_fill!(A::Array, row_first::Bool, xs::Tuple)
--     if @generated
--         N = fieldcount(xs)
--         N > 32 && return :(return _hvncat_fill_loop!(A, row_first, xs))
--         nd = ndims(A)
--         if nd <= 2
--             return quote
--                 nr = size(A, 1)
--                 nc = size(A, 2)
--                 if nr*nc != $N
--                     throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
--                 end
--                 if row_first
--                     i::Int = 1
--                     j::Int = 1
--                     @nexprs $N k -> begin
--                         @inbounds A[i, j] = xs[k]
--                         j += 1
--                         if j > nc
--                             i += 1
--                             j = 1
--                         end
--                     end
--                 else
--                     @nexprs $N k -> begin
--                         @inbounds A[k] = xs[k]
--                     end
--                 end
--                 nothing
--             end
--         else
--             return quote
--                 nr = size(A, 1)
--                 nc = size(A, 2)
--                 nrc = nr * nc
--                 na = prod(size(A)[3:end])
--                 if nrc * na != $N
--                     throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
--                 end
--                 if row_first
--                     d::Int = 1
--                     i::Int = 1
--                     dd::Int = 0
--                     Ai::Int = dd + i
--                     j::Int = 1
--                     @nexprs $N k -> begin
--                         @inbounds A[Ai] = xs[k]
--                         j += 1
--                         Ai += nr
--                         if j > nc
--                             j = 1
--                             i += 1
--                             if i > nr
--                                 i = 1
--                                 d += 1
--                                 dd = nrc * (d - 1)
--                             end
--                             Ai = dd + i
--                         end
--                     end
--                 else
--                     @nexprs $N k -> begin
--                         @inbounds A[k] = xs[k]
--                     end
--                 end
--                 nothing
--             end
--         end
--     else
--         _hvncat_fill_loop!(A, row_first, xs)
--     end
-- end
-- /Source
def hvncatFillUsingLoop {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A X E : Type} (generated : Bool) (fieldcount rank : Nat)
    (size : A → I64 → m I64) (sizeAll : A → m (List I64))
    (length : X → m I64) (showShape : A → m String)
    (eachindex : X → m (List I64)) (get : X → I64 → m E)
    (set : A → I64 → E → m Unit) (set2 : A → I64 → I64 → E → m Unit)
    (a : A) (rowFirst : Bool) (xs : X) : m Unit :=
  hvncatFill generated fieldcount rank size (hvncatTailProduct sizeAll) showShape get set set2
    (hvncatFillLoopLinked size sizeAll length showShape eachindex get set)
    a rowFirst xs

/-- Callee-closed numeric shape concatenation at
base/abstractarray.jl:2514-2525. The positivity, allocation and argument-count
checks are the existing source model. Its fill invokes both concrete generated
and fallback bodies above. Allocation and current-store observations/writes are
the frozen array runtime boundary. fieldcount is the actual tuple type arity;
dims is the native-sized dimension tuple for rank dims.length. This is an
internal method-body model; it does not claim implementation of array allocation. -/
-- Source: base/abstractarray.jl:2514-2525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(::Type{T}, dims::NTuple{N, Int}, row_first::Bool, xs::Number...) where {T, N}
--     all(>(0), dims) ||
--         throw(ArgumentError("`dims` argument must contain positive integers"))
--     A = Array{T, N}(undef, dims...)
--     lengtha = length(A)  # Necessary to store result because throw blocks are being deoptimized right now, which leads to excessive allocations
--     lengthx = length(xs) # Cuts from 3 allocations to 1.
--     if lengtha != lengthx
--        throw(ArgumentError("argument count does not match specified shape (expected $lengtha, got $lengthx)"))
--     end
--     hvncat_fill!(A, row_first, xs)
--     return A
-- end
-- /Source
def typedHvncatNumbersDimsUsingFill {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {Ty X A E : Type}
    (generated : Bool) (fieldcount : Nat)
    (array : Ty → Nat → List I64 → m A)
    (lengthArray : A → m I64) (lengthArgs : X → m I64)
    (size : A → I64 → m I64) (sizeAll : A → m (List I64))
    (showShape : A → m String) (eachindex : X → m (List I64))
    (get : X → I64 → m E) (set : A → I64 → E → m Unit)
    (set2 : A → I64 → I64 → E → m Unit)
    (t : Ty) (dims : List I64) (rowFirst : Bool) (xs : X) : m A :=
  typedHvncatNumbersDims array lengthArray lengthArgs
    (hvncatFillUsingLoop generated fieldcount dims.length size sizeAll
      lengthArgs showShape eachindex get set set2)
    t dims rowFirst xs

/-- Dispatch information from the existing `IteratorSize` runtime boundary,
base/generator.jl:63-67. The four documented traits are represented separately.
`Rank` retains the HasShape type parameter without converting it to machine Int
or using it arithmetically. `other` represents any additional subtype of the
abstract IteratorSize type, which selects the same pinned generic overload.
No length, axes, reflection, or trait-classification behavior is invented here.
-/
-- Source: base/generator.jl:63-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abstract type IteratorSize end
-- struct SizeUnknown <: IteratorSize end
-- struct HasLength <: IteratorSize end
-- struct HasShape{N} <: IteratorSize end
-- struct IsInfinite <: IteratorSize end
-- /Source
inductive IteratorSizeTag (Rank : Type) where
  | sizeUnknown
  | hasLength
  | hasShape (rank : Rank)
  | isInfinite
  | other

/-- Close `_iterator_axes(x)` at base/abstractarray.jl:3034 by dispatching to
its existing source methods at 3035 and 3036. The trait classifier is evaluated
once. HasLength obtains length, constructs OneTo, and packages the singleton
axis tuple; every other IteratorSize subtype invokes the existing axes method.
The HasShape rank is not read, checked, or used to recompute axes.

The only supplied operations are the already-explicit runtime trait classifier,
length observation, axes observation, and OneTo construction. Their actual
results, effects, and errors propagate through the original method bodies.
LengthValue is deliberately generic, preserving the original length/OneTo
intermediate type boundary rather than silently narrowing it to I64.
This is a complete composition of the pinned `_iterator_axes` overload set at
that runtime boundary; it does not claim to implement those primitives or any
later user-defined specialization of the internal `_iterator_axes` function.
-/
-- Source: base/abstractarray.jl:3034-3036 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _iterator_axes(x) = _iterator_axes(x, IteratorSize(x))
-- _iterator_axes(x, ::HasLength) = (OneTo(length(x)),)
-- _iterator_axes(x, ::IteratorSize) = axes(x)
-- /Source
def iteratorAxesLinked {m : Type → Type} [Monad m]
    {X Rank LengthValue Axis : Type}
    (iteratorSize : X → m (IteratorSizeTag Rank))
    (length : X → m LengthValue) (oneTo : LengthValue → m Axis)
    (axes : X → m (List Axis)) (x : X) : m (List Axis) :=
  iteratorAxes iteratorSize (fun object trait =>
    match trait with
    | .hasLength => iteratorAxesLength length oneTo object
    | .hasShape _ => iteratorAxesShape axes object
    | .isInfinite => iteratorAxesShape axes object
    | .sizeUnknown => iteratorAxesShape axes object
    | .other => iteratorAxesShape axes object) x

/-- Close the generic only/_only composition at base/iterators.jl:1659-1671
for the typed iterator boundary used by zero-dimensional AbstractArray handles.
The initial and next iterator actions share m; their states, mutations and
exceptions are retained. Option(element × state) is the existing iterator
protocol representation, which makes the source NTuple{2,Any} assertion a
representation invariant rather than an assumed iterator-correctness law.
The call at base/abstractarray.jl:3136 has no @inbounds suppression, so both
source bounds checks execute. Empty and multiple-element iterators throw at
the source points. The next yielded value is inspected only for presence.

This local dependency specializes the unchanged iterators.onlyModel and
sourceMethod1661 bodies because their prebuilt import is unavailable. It is
not a new assigned-method coverage claim for iterators.jl. -/
-- Source: base/iterators.jl:1659-1671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @propagate_inbounds only(x) = _only(x, iterate)
-- 
-- @propagate_inbounds function _only(x, ::typeof(iterate))
--     i = iterate(x)
--     @boundscheck if i === nothing
--         throw(ArgumentError("Collection is empty, must contain exactly 1 element"))
--     end
--     (ret, state) = i::NTuple{2,Any}
--     @boundscheck if iterate(x, state) !== nothing
--         throw(ArgumentError("Collection has multiple elements, must contain exactly 1 element"))
--     end
--     return ret
-- end
-- /Source
def onlyIterateAtArrayBoundary {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {A E S : Type}
    (first : A → m (Option (E × S)))
    (next : A → S → m (Option (E × S))) (a : A) : m E := do
  let initial ← first a
  match initial with
  | none =>
      throw (.julia (.argumentError
        "Collection is empty, must contain exactly 1 element"))
  | some (value, state) =>
      if (← next a state).isSome then
        throw (.julia (.argumentError
          "Collection has multiple elements, must contain exactly 1 element"))
      return value

/-- Close only(A) and only(B) in the existing zero-dimensional array isless
model at base/abstractarray.jl:3135-3137. The two arrays may share storage or
iterator state through m. FirstA, nextA, firstB, nextB and the element-order
operation execute in that order, stopping immediately at an exception.
The iterator and element comparison primitives are the established typed
runtime boundary; no entire only implementation or correctness law is supplied.
No rank check is invented: A and B denote the source's AbstractArray{<:Any,0}
handles. This models the selected pinned method, without replacing methods
for other ranks or future user-defined specializations of only. -/
-- Source: base/abstractarray.jl:3135-3137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isless(A::AbstractArray{<:Any,0}, B::AbstractArray{<:Any,0})
--     isless(only(A), only(B))
-- end
-- /Source
def arrayIslessZeroDimLinked {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {A B E F SA SB : Type}
    (firstA : A → m (Option (E × SA)))
    (nextA : A → SA → m (Option (E × SA)))
    (firstB : B → m (Option (F × SB)))
    (nextB : B → SB → m (Option (F × SB)))
    (isless : E → F → m Bool) (a : A) (b : B) : m Bool :=
  arrayIslessZeroDim (onlyIterateAtArrayBoundary firstA nextA)
    (onlyIterateAtArrayBoundary firstB nextB) isless a b

/-- `_sub2ind(inds::Tuple{OneTo},i::Integer)` at base/abstractarray.jl:3191.
The Julia method performs no arithmetic or conversion and returns the original
integer object. `IntegerValue` is the existing abstract value boundary, so the
identity covers BigInt and custom Integer payloads as well as every JInt type.
The caller has selected the Tuple{OneTo} overload; this declaration does not
replace the ambiguous general one-dimensional Indices overload. The existing
BitInteger-only `sub2indOneToScalar` remains unchanged. -/
-- Source: base/abstractarray.jl:3191-3191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind(inds::Tuple{OneTo}, i::Integer)    = i
-- /Source
def sub2indOneToScalarAny {Axis IntegerValue : Type} (_axes : Axis)
    (index : IntegerValue) : IntegerValue := index

/-- Close the recursive `_sub2ind_vec(i,I1,I...)` method at
base/abstractarray.jl:3263 using the existing `sub2indVecMore` and
`sub2indVecEmpty` bodies, including the terminating source method at 3264.

Index, Handle, and Value are arbitrary typed runtime payloads. In particular,
Index is not restricted to native Int, and handles may refer to shared mutable
objects. The only foreign operation is the already-explicit scalar/indexing
primitive `read`; its actual result, exception, and state effects are preserved.
Each read finishes before recursion starts, so repeated aliases are read again
from the current store. No values are eagerly snapshotted, no integer conversion
is inserted, and no supplied recursive implementation or correctness law remains.

The tuple-size argument is solely the representation invariant that the complete
returned argument tuple, including I1, fits native Int length. It is neither a
bounds check performed by Julia nor a success premise for the indexing operation.
The proof-module `sourceVectorCoordinates` only handles native I64 indices and
Result; this generic shared-monad composition cannot be obtained by importing
that proof module into the model and preserves its existing declaration.
-/
-- Source: base/abstractarray.jl:3263-3264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind_vec(i, I1, I...) = (@inline; (I1[i], _sub2ind_vec(i, I...)...))
-- _sub2ind_vec(i) = ()
-- /Source
def sub2indVecMoreLinked {m : Type → Type} [Monad m]
    {Index Handle Value : Type}
    (read : Handle → Index → m Value)
    (index : Index) (first : Handle) (rest : List Handle)
    (_tupleFits : (rest.length : Int) + 1 ≤ IntTy.i64.max) : m (List Value) :=
  let rec coordinates : List Handle → m (List Value)
    | [] => pure (sub2indVecEmpty index)
    | handle :: handles =>
        sub2indVecMore read (fun _ _ => coordinates handles) index handle handles
  sub2indVecMore read (fun _ handles => coordinates handles) index first rest

/-- `base/abstractarray.jl:3493`: close the one-source map! call using
the existing implementation. D denotes the allocated Vector{Any} handle, so
the pinned BitArray-destination specializations cannot apply. No more-specific
one-source map! method for a Vector{Any} destination exists in pinned Base.
Later user-defined internal-method extensions are outside the pinned overload set. Allocation, generic length, index iteration,
zip, scalar reads and scalar writes retain exactly the existing runtime boundary.
Handles and effects remain generic, so input/destination aliases are representable.
LengthValue preserves non-native length results, including OneTo{UInt64} and
OneTo{BigInt}; any dimension conversion/error occurs at allocateAny, as in source.
The existing native-only mapAnyArray wrapper is preserved unchanged.
This is a callee composition, not a claim that the supplied runtime primitives
have been implemented by this definition. -/
-- Source: base/abstractarray.jl:3493-3493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapany(f, A::AbstractArray) = map!(f, Vector{Any}(undef, length(A)), A)
-- /Source
def mapAnyArrayLinked {m : Type → Type} [Monad m]
    {A E F D LengthValue ID IA IndD IndA Z : Type} [ForIn m Z (ID × IA)]
    (length : A → m LengthValue) (allocateAny : LengthValue → m D)
    (eachDest : D → m IndD) (eachSrc : A → m IndA)
    (zip : IndD → IndA → m Z)
    (read : A → IA → m E) (write : D → ID → F → m Unit)
    (f : E → m F) (a : A) : m D := do
  let len ← length a
  let dest ← allocateAny len
  mapInplaceOne eachDest eachSrc zip read write f dest a

end JuliaLean.base.abstractarray.Models1Group4


/-!
## Runtime-typed array interfaces

These declarations refine the existing explicit runtime/interface boundary.
They do not implement arbitrary user constructors, type dispatch, or array
storage. Runtime outcomes carry their actual type-membership tag; there is
no assumed correctness law. A monad such as ExceptT ArrayError (StateM World)
preserves effects even when a later source check throws.
-/
namespace JuliaLean.base.abstractarray.Models1Group1

open JuliaLean

/-- An observation of an already evaluated Julia value at a type assertion.
`accepted` contains a value belonging to the asserted Julia type; `rejected`
contains a value outside it. The constructor is part of runtime type metadata,
not an independently supplied correctness Boolean. Different Julia types can
use the same Lean carrier, so the tag, not that carrier, records membership.
Julia source: base/abstractarray.jl:17-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:17-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{AbstractArray{T}}, a::AbstractArray) where {T} = AbstractArray{T}(a)::AbstractArray{T}
-- convert(::Type{AbstractArray{T,N}}, a::AbstractArray{<:Any,N}) where {T,N} = AbstractArray{T,N}(a)::AbstractArray{T,N}
-- /Source
inductive TypeAssertion (Expected Other : Type) where
  | accepted (value : Expected)
  | rejected (value : Other)

/-- The type-assertion primitive required by these assigned bodies.
The existing error carrier's historically named `showError .typeError` denotes
the TypeError class; no shared error enum is changed. The caller has already
evaluated the value, so any earlier effects remain in the effect monad.
Julia source: base/abstractarray.jl:17-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:17-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{AbstractArray{T}}, a::AbstractArray) where {T} = AbstractArray{T}(a)::AbstractArray{T}
-- convert(::Type{AbstractArray{T,N}}, a::AbstractArray{<:Any,N}) where {T,N} = AbstractArray{T,N}(a)::AbstractArray{T,N}
-- /Source
def assertType {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Expected Other : Type} : TypeAssertion Expected Other → m Expected
  | .accepted value => pure value
  | .rejected _ => throw (.showError .typeError)

/-- A finite Julia argument/axes tuple, with a native-Int representable arity.
This is tuple representation data, not an array model. Nat is used only for
the representation bound and Lean structural recursion, never for Julia
machine arithmetic. Element payloads retain their selected Julia types.
Julia source: base/abstractarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
-- /Source
structure Tuple (α : Type) where
  values : List α
  nativeArity : values.length ≤ 2 ^ 63 - 1

/-- Conversion followed by the source's explicit AbstractArray{T} assertion.
The selected constructor is the pre-existing runtime boundary; its result
partition now includes values that fail the assertion. Constructor effects and
exceptions precede the assertion, and an accepted value is returned unchanged.
Julia source: base/abstractarray.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{AbstractArray{T}}, a::AbstractArray) where {T} = AbstractArray{T}(a)::AbstractArray{T}
-- /Source
def convertAbstract {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B Other : Type} (construct : A → m (TypeAssertion B Other)) (a : A) : m B := do
  assertType (← construct a)

/-- Rank-preserving conversion followed by the AbstractArray{T,N} assertion.
Here the accepted tag means membership in that complete target type, including
the statically selected N. This does not assume the constructor's correctness.
Julia source: base/abstractarray.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{AbstractArray{T,N}}, a::AbstractArray{<:Any,N}) where {T,N} = AbstractArray{T,N}(a)::AbstractArray{T,N}
-- /Source
def convertAbstractN {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B Other : Type} (construct : A → m (TypeAssertion B Other)) (a : A) : m B := do
  assertType (← construct a)

open JuliaLean

/-- A Julia size component with its actual native-Int/non-native runtime
classification. `other` retains the original runtime payload, including wider
integers. These tags describe the value itself; they are not correctness flags
supplied for a conversion or an assertion. The native constructor lets the
source's literal trailing dimension 1 retain its exact Julia Int64 type.
Julia source: base/abstractarray.jl:42-46; base/range.jl:706
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function size(t::AbstractArray, dim)
--     d = Int(dim)::Int
--     s = size(t)
--     d <= length(s) ? s[d] : 1
-- end
-- /Source
inductive SizeValue (Other : Type) where
  | native (value : I64)
  | other (value : Other)

/-- Preserve the explicit native-Int assertion after dimension conversion,
then obtain size before either indexing or returning a trailing singleton.
The size tuple can retain non-native components, as for wide-integer ranges.
The actual tuple arity is encoded as Julia Int before native comparison;
Tuple.nativeArity ensures that encoding is representable. Existing tupleGet
implements the pure native tuple access and its BoundsError. In particular,
nonpositive d is rejected only after size returns successfully.

The selected conversion and size methods remain the existing runtime boundary.
No new callee implementation, dispatch callback, or correctness law is added.
Julia source: base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function size(t::AbstractArray, dim)
--     d = Int(dim)::Int
--     s = size(t)
--     d <= length(s) ? s[d] : 1
-- end
-- /Source
def sizeDim {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A D Other NotInt : Type}
    (toInt : D → m (TypeAssertion I64 NotInt))
    (size : A → m (Tuple (SizeValue Other))) (array : A) (dimension : D) :
    m (SizeValue Other) := do
  let d ← assertType (← toInt dimension)
  let sizes ← size array
  let arity : I64 := int (sizes.values.length : Int)
  if d.val ≤ arity.val then
    match JuliaLean.base.abstractarray.tupleGet sizes.values d with
    | .ok value => pure value
    | .error error => throw error
  else
    pure (.native (int 1))

/-- Assert the original dimension is Integer, compare it with the actual
static rank parameter, and only then select axes or the trailing singleton.
The integer representation is passed unchanged to tuple indexing, including
non-native integers. A non-Bool comparison result raises TypeError at the
conditional. Comparison and array/indexing calls retain their existing
runtime-dispatch boundary; no rank-positivity assumption is imposed.
Julia source: base/abstractarray.jl:79-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:79-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A::AbstractArray{T,N}, d) where {T,N}
--     @inline
--     d::Integer <= N ? axes(A)[d] : OneTo(1)
-- end
-- /Source
def axesDim {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A D NotInteger N Ax R NotBool : Type}
    (leN : D → N → m (TypeAssertion Bool NotBool))
    (axes : A → m Ax) (get : Ax → D → m R) (oneTo : I64 → R)
    (n : N) (a : A) (dimension : TypeAssertion D NotInteger) : m R := do
  let d ← assertType dimension
  let condition ← assertType (← leN d n)
  if condition then get (← axes a) d else pure (oneTo (int 1))

/-- Preserve all size-component runtime types and each selected unchecked_oneto
result/error/effect. A heterogeneous tuple may use a tagged Size carrier;
there is no coercion to native Int. Size executes before the left-to-right map.
The input tuple has native-representable arity and successful mapping preserves
its length. This retains the baseline tuple-map representation abstraction;
the temporary allocation in tuple.jl:394-401 and arbitrary selected range
constructors are not implemented by this outer body.
Julia source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source
def axesDefault {m : Type → Type} [Monad m] {A Size Axis : Type}
    (size : A → m (Tuple Size)) (uncheckedOneTo : Size → m Axis)
    (array : A) : m (List Axis) := do
  let sizes ← size array
  sizes.values.mapM uncheckedOneTo

/-- Selected unary has_offset_axes dispatch cases. `fallback` denotes an
argument using the generic axes method, `vector` its vector specialization,
`dense` the Array specialization, and `custom` a user-selected specialization.
The payloads may be tagged universal Julia values, so heterogeneous argument
tuples are not coerced to a homogeneous Julia element type.
Julia source: base/abstractarray.jl:115-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:115-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
-- has_offset_axes(A::AbstractVector) = Int(firstindex(A))::Int != 1 # improve performance of a common case (ranges)
-- has_offset_axes(::Colon) = false
-- has_offset_axes(::Array) = false
-- /Source
inductive OffsetArgument (A V Dense Custom : Type) where
  | fallback (value : A)
  | vector (value : V)
  | colon
  | dense (value : Dense)
  | custom (value : Custom)

/-- The existing axes/first/firstindex/Int-conversion and user-dispatch
boundaries, collected for the concrete recursive composition below. Native
conversion now exposes its explicit ::Int assertion. The custom case is only
selected user code; known Base branches below call their real models.
Julia source: base/abstractarray.jl:115-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:115-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
-- has_offset_axes(A::AbstractVector) = Int(firstindex(A))::Int != 1 # improve performance of a common case (ranges)
-- has_offset_axes(::Colon) = false
-- has_offset_axes(::Array) = false
-- # note: this could call `any` directly if the compiler can infer it. We don't use _any_tuple
-- # here because it stops full elision in some cases (#49332) and we don't need handling of
-- # `missing` (has_offset_axes(A) always returns a Bool)
-- has_offset_axes(A, As...) = has_offset_axes(A) || has_offset_axes(As...)
-- /Source
structure OffsetOps (m : Type → Type) (A V Custom R I NotInt : Type) where
  axes : A → m (Tuple R)
  first : R → m I
  toInt : I → m (TypeAssertion I64 NotInt)
  firstindex : V → m I
  custom : Custom → m Bool

/-- The _any_tuple dependency specialized to the actual has_offset_axes
predicate. This predicate always returns Bool or throws: its result is native
Int != 1. Consequently anymissing remains false. The traversal preserves
left-to-right effects, errors, and the first true short circuit. This is the
effect-polymorphic counterpart of the baseline's anyTupleM, not a callback
standing for the recursive call.
Julia source: base/anyall.jl:159-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/anyall.jl:159-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _any_tuple(f, anymissing::Bool, x, rest...)
--     v = f(x)
--     if ismissing(v)
--         anymissing = true
--     elseif v
--         return true
--     end
--     return _any_tuple(f, anymissing, rest...)
-- end
-- @inline _any_tuple(_, anymissing::Bool) = anymissing ? missing : false
-- /Source
def anyOffsetAxis {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A V Custom R I NotInt : Type}
    (ops : OffsetOps m A V Custom R I NotInt) : List R → m Bool
  | [] => pure false
  | axis :: rest => do
      let first ← ops.first axis
      let native ← assertType (← ops.toInt first)
      if native.val != 1 then pure true else anyOffsetAxis ops rest

/-- The generic unary offset check with its original conversion/assertion
and short-circuit tuple traversal. All array-interface effects are retained;
the helper's recursion is defined locally rather than supplied by a caller.
Julia source: base/abstractarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
-- /Source
def hasOffset {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A V Custom R I NotInt : Type}
    (ops : OffsetOps m A V Custom R I NotInt) (a : A) : m Bool := do
  anyOffsetAxis ops (← ops.axes a).values

/-- Dispatch known unary branches to their callable models. Dense arrays
and Colon do not inspect axes. A custom selected method remains the existing
explicit unary-dispatch boundary, without any assumed correctness law.
Julia source: base/abstractarray.jl:115-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:115-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
-- has_offset_axes(A::AbstractVector) = Int(firstindex(A))::Int != 1 # improve performance of a common case (ranges)
-- has_offset_axes(::Colon) = false
-- has_offset_axes(::Array) = false
-- # note: this could call `any` directly if the compiler can infer it. We don't use _any_tuple
-- # here because it stops full elision in some cases (#49332) and we don't need handling of
-- # `missing` (has_offset_axes(A) always returns a Bool)
-- has_offset_axes(A, As...) = has_offset_axes(A) || has_offset_axes(As...)
-- /Source
def hasOffsetArgument {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A V Dense Custom R I NotInt : Type}
    (ops : OffsetOps m A V Custom R I NotInt) : OffsetArgument A V Dense Custom → m Bool
  | .fallback a => hasOffset ops a
  | .vector v => JuliaLean.base.abstractarray.hasOffsetVector ops.firstindex
      (fun i => do assertType (← ops.toInt i)) v
  | .colon => pure JuliaLean.base.abstractarray.hasOffsetColon
  | .dense a => pure (JuliaLean.base.abstractarray.hasOffsetArray a)
  | .custom a => ops.custom a

/-- Closed dispatch and recursion for a tuple of has_offset_axes arguments.
The one-argument case selects the unary method; the multi-argument case tests
the first argument and recursively dispatches the tail only after false.
The empty case reuses hasOffsetNone. The exported input has a native arity.
Julia source: base/abstractarray.jl:114-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:114-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes() = false
-- has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
-- has_offset_axes(A::AbstractVector) = Int(firstindex(A))::Int != 1 # improve performance of a common case (ranges)
-- has_offset_axes(::Colon) = false
-- has_offset_axes(::Array) = false
-- # note: this could call `any` directly if the compiler can infer it. We don't use _any_tuple
-- # here because it stops full elision in some cases (#49332) and we don't need handling of
-- # `missing` (has_offset_axes(A) always returns a Bool)
-- has_offset_axes(A, As...) = has_offset_axes(A) || has_offset_axes(As...)
-- /Source
def hasOffsetArguments {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A V Dense Custom R I NotInt : Type}
    (ops : OffsetOps m A V Custom R I NotInt) : List (OffsetArgument A V Dense Custom) → m Bool
  | [] => pure JuliaLean.base.abstractarray.hasOffsetNone
  | [a] => hasOffsetArgument ops a
  | a :: b :: rest => do
      if ← hasOffsetArgument ops a then pure true
      else hasOffsetArguments ops (b :: rest)

/-- The assigned varargs method, using the closed recursive dispatcher.
The input tuple must be nonempty because A is a required source argument.
Its representation proof is not a hypothesis about method correctness.
Julia source: base/abstractarray.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes(A, As...) = has_offset_axes(A) || has_offset_axes(As...)
-- /Source
def hasOffsetMany {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A V Dense Custom R I NotInt : Type}
    (ops : OffsetOps m A V Custom R I NotInt)
    (args : Tuple (OffsetArgument A V Dense Custom))
    (_nonempty : args.values ≠ []) : m Bool :=
  hasOffsetArguments ops args.values

/-- Reuse the source error/return body with the actual closed varargs
offset implementation, including the zero-argument call. Success returns
true. The first earlier runtime exception is not replaced by ArgumentError.
Julia source: base/abstractarray.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- require_one_based_indexing(A...) = !has_offset_axes(A...) || throw(ArgumentError("offset arrays are not supported but got an array with index other than 1"))
-- /Source
def requireOneBased {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A V Dense Custom R I NotInt : Type}
    (ops : OffsetOps m A V Custom R I NotInt)
    (args : Tuple (OffsetArgument A V Dense Custom)) : m Bool :=
  JuliaLean.base.abstractarray.requireOneBased
    (fun xs : List (OffsetArgument A V Dense Custom) => hasOffsetArguments ops xs) args.values

/-- The iterator axes fallback retains the selected length's Julia type.
It calls the existing checked oneto interface after length, preserving both
operations' effects and exceptions. No native-Int narrowing is introduced.
Julia source: base/abstractarray.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes1(iter) = oneto(length(iter))
-- /Source
def axes1Iterator {m : Type → Type} [Monad m] {A Length Axis : Type}
    (length : A → m Length) (oneto : Length → m Axis) (iterator : A) : m Axis := do
  oneto (← length iterator)

/-- Close the existing keytype(Bottom) source mirror with the callable
eltypeBottom model. Runtime type tokens are Ty : Type; slurp arguments are
already evaluated on entry and ignored, as in the source.
Julia source: base/abstractarray.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keytype(::Type{Union{}}, slurp...) = eltype(Union{})
-- /Source
def keytypeBottom {Ty Args : Type} (_slurp : Args) : Result Ty :=
  JuliaLean.base.abstractarray.keytypeBottom
    (fun _ : Type => JuliaLean.base.abstractarray.eltypeBottom (α := Ty)) Empty

/-- The array-type key query evaluates the selected ndims method before the
existing CartesianIndex type-application boundary. Both boundaries are already
present in the baseline model; this refinement permits their real exceptions
and effects and retains the original runtime type/rank carriers. No assertion
that rank is native Int is added at this source line: the selected ndims body
and runtime type application determine their own results or failures.

The polymorphic effect monad can retain arbitrary Julia exceptions, including
an unbound-static-parameter exception from ndims. This method does not implement
the ndims type overload, dynamic type matching, or Core.apply_type. It does not
assume those callees' correctness and adds no new numeric/runtime callback.
Julia source: base/abstractarray.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keytype(A::Type{<:AbstractArray}) = CartesianIndex{ndims(A)}
-- /Source
def keytypeArray {m : Type → Type} [Monad m] {ArrayType Rank KeyType : Type}
    (ndims : ArrayType → m Rank) (cartesianIndexType : Rank → m KeyType)
    (arrayType : ArrayType) : m KeyType := do
  cartesianIndexType (← ndims arrayType)

/-- Close valtype(Bottom) with the same real eltypeBottom callee, retaining
its ArgumentError and ignoring already evaluated optional arguments.
Julia source: base/abstractarray.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- valtype(::Type{Union{}}, slurp...) = eltype(Union{})
-- /Source
def valtypeBottom {Ty Args : Type} (_slurp : Args) : Result Ty :=
  JuliaLean.base.abstractarray.valtypeBottom
    (fun _ : Type => JuliaLean.base.abstractarray.eltypeBottom (α := Ty)) Empty

/-- The selected array-type eltype method remains the existing explicit
dispatch boundary. Its result is a runtime value token: the Julia body adds
no return-type assertion. An effect monad retains its exceptions and state
effects instead of forcing a pure Lean Type result.

`ArrayType` is the carrier of already-dispatched Type{<:AbstractArray}
arguments. This definition does not implement a user-selected eltype method.
Julia source: base/abstractarray.jl:217-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:217-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- valtype(A::Type{<:AbstractArray}) = eltype(A)
-- /Source
def valtypeArray {m : Type → Type} {ArrayType Value : Type}
    (selectedEltype : ArrayType → m Value) (arrayType : ArrayType) : m Value :=
  selectedEltype arrayType

/-- The value convenience method obtains its runtime type and calls the
selected eltype method. The typeof primitive remains pure, as in the source;
the selected eltype operation can return any Julia value or raise an exception
and retains any effects through m. No new assertion that its result is a type
is introduced. These are the pre-existing typeof/dispatch boundaries.
Julia source: base/abstractarray.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltype(x) = eltype(typeof(x))
-- /Source
def eltypeValue {m : Type → Type} {A TypeToken Value : Type}
    (typeOf : A → TypeToken) (selectedEltype : TypeToken → m Value)
    (value : A) : m Value :=
  selectedEltype (typeOf value)

/-- Read the already-selected static E binding; only an unbound parameter
uses the Any token. The source contains no E::Type assertion. AbstractArray's
parameters are unconstrained (base/boot.jl:62), so a bound non-type parameter
must be returned as-is when admitted by Julia's type-parameter representation.

Value carries runtime values admissible in this already-validated static
binding (type objects and allowed plain-bits/value parameters). The model does
not accept an arbitrary runtime object as a legal type parameter, construct an
AbstractArray type, or implement type matching. `none` is an unbound static
variable, not a bound Julia nothing value; a bound nothing token is `some`.
Julia source: base/abstractarray.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltype(::Type{<:AbstractArray{E}}) where {E} = @isdefined(E) ? E : Any
-- /Source
def eltypeArray {Value : Type} (anyType : Value) (elementBinding : Option Value) : Value :=
  match elementBinding with
  | some parameter => parameter
  | none => anyType

/-- Assert the actual selected static rank parameter N is native Int.
Accepted metadata includes every Int64, including negative ranks; rejected
metadata includes other-width integers and other Julia type-parameter values.
The original model is reused after the assertion. No array contents are read.
Julia source: base/abstractarray.jl:278-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:278-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ndims(::AbstractArray{T,N}) where {T,N} = N::Int
-- /Source
def ndimsValue {A NotInt : Type} (rank : TypeAssertion I64 NotInt) (a : A) : Result I64 := do
  let n ← assertType rank
  pure (JuliaLean.base.abstractarray.ndimsValue n a)

end JuliaLean.base.abstractarray.Models1Group1

namespace JuliaLean.base.abstractarray.Models1Group1

/-- The IndexLinear fallback passes the original length value to checked
oneto. Length can be any Julia Integer carrier admitted by the existing array
interface; the selected calls preserve their state and exception channels.
Julia source: base/abstractarray.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::AbstractArray) = (@inline; oneto(length(A)))
-- /Source
def eachindexLinear {m : Type → Type} [Monad m] {A Length Axis : Type}
    (length : A → m Length) (oneto : Length → m Axis) (array : A) : m Axis := do
  oneto (← length array)

/-- The vector prefix method preserves the comparison's effects and Bool
assertion, then obtains the endpoint before checked_length and min. The
original requested integer, checked length, and min result retain independent
Julia carriers; no truncation or assumed numeric correctness is supplied.
Range construction and indexing remain the existing selected interfaces.
Julia source: base/abstractarray.jl:507-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:507-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function first(v::AbstractVector, n::Integer)
--     n < 0 && throw(ArgumentError("Number of elements must be non-negative"))
--     v[range(begin, length=min(n, checked_length(v)))]
-- end
-- /Source
def firstVectorN {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Requested Index Length Count Range Out NotBool : Type}
    (negative : Requested → m (TypeAssertion Bool NotBool))
    (firstindex : A → m Index) (checkedLength : A → m Length)
    (minimum : Requested → Length → m Count) (range : Index → Count → m Range)
    (getindex : A → Range → m Out) (vector : A) (requested : Requested) : m Out := do
  if ← assertType (← negative requested) then
    throw (.julia (.argumentError "Number of elements must be non-negative"))
  let start ← firstindex vector
  let count ← minimum requested (← checkedLength vector)
  getindex vector (← range start count)

/-- The generic suffix method calls reverse iterator, take, collect, and
reverse! in source order. Collected storage and the returned reverse! value
have distinct carriers, because the Julia body contains no same-type result
assertion. The effect monad preserves reverse!'s mutations even when it throws.
Julia source: base/abstractarray.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(itr, n::Integer) = reverse!(collect(Iterators.take(Iterators.reverse(itr), n)))
-- /Source
def lastN {m : Type → Type} [Monad m]
    {A Requested ReverseIterator Taken Collected Out : Type}
    (reverseIterator : A → m ReverseIterator)
    (take : ReverseIterator → Requested → m Taken)
    (collect : Taken → m Collected) (reverseBang : Collected → m Out)
    (iterator : A) (requested : Requested) : m Out := do
  reverseBang (← collect (← take (← reverseIterator iterator) requested))

/-- The vector suffix method retains the original n, checked length, and
min result without native narrowing. It checks the effectful negative test
and its Bool result before obtaining lastindex, then checked_length, min,
the stop-based range, and the indexed result, preserving all earlier effects.
Julia source: base/abstractarray.jl:557-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:557-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function last(v::AbstractVector, n::Integer)
--     n < 0 && throw(ArgumentError("Number of elements must be non-negative"))
--     v[range(stop=lastindex(v), length=min(n, checked_length(v)))]
-- end
-- /Source
def lastVectorN {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Requested Index Length Count Range Out NotBool : Type}
    (negative : Requested → m (TypeAssertion Bool NotBool))
    (lastindex : A → m Index) (checkedLength : A → m Length)
    (minimum : Requested → Length → m Count) (rangeStop : Index → Count → m Range)
    (getindex : A → Range → m Out) (vector : A) (requested : Requested) : m Out := do
  if ← assertType (← negative requested) then
    throw (.julia (.argumentError "Number of elements must be non-negative"))
  let stop ← lastindex vector
  let count ← minimum requested (← checkedLength vector)
  getindex vector (← rangeStop stop count)

end JuliaLean.base.abstractarray.Models1Group1

namespace JuliaLean.base.abstractarray.Models1Group1

open JuliaLean

/-- A value retaining its selected Julia runtime type. The multiplication
boundary can return a value whose tag differs from either input tag; no
homogeneous Julia element-type restriction is imposed by the Lean carrier.
Julia source: base/abstractarray.jl:609-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:609-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline size_to_strides(s, d, sz...) = (s, size_to_strides(s * d, sz...)...)
-- size_to_strides(s, d) = (s,)
-- size_to_strides(s) = ()
-- /Source
abbrev StrideValue (Ty : Type) (Payload : Ty → Type) := Σ t : Ty, Payload t

/-- Closed source-order recursion for size_to_strides. The [] and singleton
cases call the existing terminal models. In particular the singleton case
never evaluates multiplication. In the recursive case, multiplication can
change the value's Julia type; its effects/errors occur before recursion,
and the original s is prepended only after recursion succeeds.

`multiply` is the pre-existing multiplication-dispatch parameter of
JuliaLean.base.abstractarray.sizeToStrides, lifted to the caller's effect
monad so errors or state effects are not forced away. It is not a supplied
recursive implementation and no arithmetic correctness law is assumed.
The function does not itself implement generic Julia multiplication.
Internal lists implement structural recursion; the exported dispatcher below
requires a native-arity tuple containing every already-evaluated argument.
Julia source: base/abstractarray.jl:609-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:609-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline size_to_strides(s, d, sz...) = (s, size_to_strides(s * d, sz...)...)
-- size_to_strides(s, d) = (s,)
-- size_to_strides(s) = ()
-- /Source
def sizeToStridesValues {m : Type → Type} [Monad m]
    {Ty : Type} {Payload : Ty → Type}
    (multiply : StrideValue Ty Payload → StrideValue Ty Payload →
      m (StrideValue Ty Payload))
    (s : StrideValue Ty Payload) : List (StrideValue Ty Payload) →
      m (List (StrideValue Ty Payload))
  | [] => pure (JuliaLean.base.abstractarray.sizeToStridesEmpty s)
  | [d] => pure (JuliaLean.base.abstractarray.sizeToStridesLast s d)
  | d :: e :: rest => do
      let product ← multiply s d
      let following ← sizeToStridesValues multiply product (e :: rest)
      pure (s :: following)

/-- Dispatch all nonempty argument tuples of size_to_strides to the closed
recursive implementation. The first argument is s; all remaining arguments
are dimensions. A Julia call requires s, so nonempty is solely an arity
invariant, not a premise about correct behavior. The tuple bounds the entire
call's arity, including s. Existing sizeToStridesLast/Empty are reused for
the more specific terminal methods rather than evaluating a spurious final
multiplication. Result lists represent the output tuple, whose arity is one
less than the input arity on every successful branch.
Julia source: base/abstractarray.jl:609-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:609-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline size_to_strides(s, d, sz...) = (s, size_to_strides(s * d, sz...)...)
-- size_to_strides(s, d) = (s,)
-- size_to_strides(s) = ()
-- /Source
def sizeToStrides {m : Type → Type} [Monad m]
    {Ty : Type} {Payload : Ty → Type}
    (multiply : StrideValue Ty Payload → StrideValue Ty Payload →
      m (StrideValue Ty Payload))
    (args : Tuple (StrideValue Ty Payload))
    (nonempty : args.values ≠ []) : m (List (StrideValue Ty Payload)) :=
  match h : args.values with
  | [] => False.elim (nonempty h)
  | s :: dims => sizeToStridesValues multiply s dims

end JuliaLean.base.abstractarray.Models1Group1

namespace JuliaLean.base.abstractarray.Models1Group1

/-- Map every axis length before invoking the selected product, retaining
the Julia types of both intermediate lengths and the product result. Axis and
Length may be tagged runtime-value carriers, so heterogeneous tuples are not
coerced to a homogeneous Julia numeric type. The empty tuple still calls prod.
The input tuple's arity is native-representable; mapM preserves that arity.

This retains the baseline's tuple-map representation boundary. It preserves
left-to-right length calls and their exceptions, but does not implement the
temporary Vector{Any} allocation used by tuple.jl's >=32-element map method
(base/tuple.jl:394-401), nor the selected prod's numeric reduction semantics.
There is no new mapper, allocator, arithmetic callback, or callee law.
Julia source: base/abstractarray.jl:634-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/abstractarray.jl:634-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function trailingsize(inds::Indices)
--     @inline
--     prod(map(length, inds))
-- end
-- /Source
def trailingSizeAll {m : Type → Type} [Monad m] {Axis Length Product : Type}
    (length : Axis → m Length) (prod : List Length → m Product)
    (axes : Tuple Axis) : m Product := do
  prod (← axes.values.mapM length)

end JuliaLean.base.abstractarray.Models1Group1

namespace JuliaLean.base.abstractarray.Models1Group1

/-- Pure membership validation for the already constructed mapped tuple.
Accepted payloads are exactly Integer or AbstractUnitRange values, with their
original type tags retained by Shape. This is an interpretation of the one
tuple type assertion, not a sequence of calls to a user conversion function.
It runs only after the entire map has returned, so a later map exception takes
precedence over an earlier nonconforming successful element.
Julia source: base/abstractarray.jl:838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:838-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- to_shape(dims::DimsOrInds) = map(to_shape, dims)::DimsOrInds
-- /Source
def assertShapeTuple {Shape Other : Type} :
    List (TypeAssertion Shape Other) → Result (List Shape)
  | [] => pure []
  | x :: xs => do
      let head ← assertType x
      let tail ← assertShapeTuple xs
      pure (head :: tail)

/-- The mixed shape tuple fallback with its previously omitted final
::DimsOrInds assertion. Input D is the existing DimOrInd domain; Shape denotes
the actual runtime values in that same union, not just native Int. The map
reuses the existing callable model. Selected leaf to_shape dispatch remains
the existing interface boundary, and its correctness is never assumed.
Julia source: base/abstractarray.jl:838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:838-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- to_shape(dims::DimsOrInds) = map(to_shape, dims)::DimsOrInds
-- /Source
def toShapeMixed {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D Shape Other : Type}
    (toShape : D → m (TypeAssertion Shape Other)) (dims : Tuple D) : m (List Shape) := do
  let mapped ← JuliaLean.base.abstractarray.toShapeMixed toShape dims.values
  match assertShapeTuple mapped with
  | .ok values => pure values
  | .error error => throw error

end JuliaLean.base.abstractarray.Models1Group1

namespace JuliaLean.base.abstractarray.Models1Group2

open JuliaLean JuliaLean.base.abstractarray

/-- Effectful axes equality and interpolation, at the existing axes/show interface.
Julia source: base/abstractarray.jl:1184. The failed comparison is followed by
destination formatting, source formatting, and finally DimensionMismatch.
A failure in equality or either formatting action propagates without a later action.
-/
-- Source: base/abstractarray.jl:1184-1184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline _checkaxs(axd, axs) = axd == axs || throw(DimensionMismatch("axes must agree, got $axd and $axs"))
-- /Source
def checkAxesEffectful {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ax : Type} (eq : Ax → Ax → m Bool) (showAxes : Ax → m String)
    (axd axs : Ax) : m Bool := do
  if ← eq axd axs then return true
  let d ← showAxes axd
  let s ← showAxes axs
  throw (.dimensionMismatch ("axes must agree, got " ++ d ++ " and " ++ s))

/-- Close the same-file _checkaxs call rather than accepting an arbitrary guard.
Julia source: base/abstractarray.jl:1186-1189. Array axes and the selected
copyto! method retain the baseline explicit mutable-array interface; this
definition does not assert that an arbitrary copyto! implementation is correct.
-/
-- Source: base/abstractarray.jl:1186-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto_axcheck!(dest, src)
--     _checkaxs(axes(dest), axes(src))
--     copyto!(dest, src)
-- end
-- /Source
def copytoAxesCheckLinked {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S Ax : Type} (axesDest : D → m Ax) (axesSrc : S → m Ax)
    (eq : Ax → Ax → m Bool) (showAxes : Ax → m String)
    (copyto : D → S → m D) (dest : D) (src : S) : m D :=
  copytoAxesCheck axesDest axesSrc (checkAxesEffectful eq showAxes) copyto dest src

/-- Necessary dependency for _one at base/abstractarray.jl:1227.
This is the Boolean-predicate specialization of _any_tuple: the predicate
Int(first(axis)) != 1 cannot return missing. Predicate effects/errors and
short-circuit evaluation remain in the same monad as the array operations.
-/
-- Source: base/anyall.jl:159-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _any_tuple(f, anymissing::Bool, x, rest...)
--     v = f(x)
--     if ismissing(v)
--         anymissing = true
--     elseif v
--         return true
--     end
--     return _any_tuple(f, anymissing, rest...)
-- end
-- @inline _any_tuple(_, anymissing::Bool) = anymissing ? missing : false
-- /Source
def anyTupleBool {m : Type → Type} [Monad m] {A : Type}
    (predicate : A → m Bool) : List A → m Bool
  | [] => pure false
  | x :: xs => do
      if ← predicate x then return true
      anyTupleBool predicate xs

/-- Necessary effectful has_offset_axes dependency for _one.
Julia source: base/abstractarray.jl:115. first and checked Int conversion
are the existing axis/integer interfaces; no mathematical integer replaces
the resulting Julia machine Int.
-/
-- Source: base/abstractarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
-- /Source
def hasOffsetAxesEffectful {m : Type → Type} [Monad m] {A Ax I : Type}
    (axes : A → m (List Ax)) (first : Ax → m I) (toInt : I → m I64)
    (a : A) : m Bool := do
  anyTupleBool (fun axis => do return (← toInt (← first axis)).val != 1) (← axes a)

/-- The explicit zero(unit)::T assertion used by _one.
Julia source: base/abstractarray.jl:1226. At the existing numeric dispatch
boundary, some z denotes a result with the concrete type of unit, while
none denotes a result of a different type. The discarded wrong-typed value
is unobservable after this assertion. TypeError uses the already available
ArrayError.showError constructor; its historical wrapper name is not a
claim that a show method ran.
-/
-- Source: base/abstractarray.jl:1226-1226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     zer = zero(unit)::T
-- /Source
def assertZeroType {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {E : Type} : Option E → m E
  | some value => pure value
  | none => throw (.showError .typeError)


/-- The existing has_offset_axes dispatch boundary for an AbstractMatrix.
`array` selects base/abstractarray.jl:118, `fallback` selects :115, and
`specialized` is a method defined by another built-in array type or an external
subtype. In particular SubArray, ReinterpretArray, PermutedDimsArray, and
CartesianIndices have their own pinned methods. Those methods are not claimed
implemented by this local caller completion. -/
inductive OffsetAxesDispatch (m : Type → Type) (A : Type) where
  | array
  | fallback
  | specialized (method : A → m Bool)

/-- Full local _one body with its dynamic assertion and generic axis index type.
Julia source: base/abstractarray.jl:1222-1234. E represents the Julia
dispatch type T of unit, including dimensionless one(T) results whose type
differs from the original matrix element type. similar receives E explicitly.
The runtime method selection distinguishes concrete Array (not all
DenseArray), the default fallback, and a specialized external method.
For the generic AbstractMatrix fallback, the second axes query occurs
after zero and its assertion, inside the one-based check, so effects on
the matrix between queries are retained.
Allocation, fill!, scalar setindex!, axis iteration, and numeric zero
remain at the baseline explicit interfaces; no callee correctness law
is assumed. Shared-state monads preserve partial mutation on failure.
-/
-- Source: base/abstractarray.jl:1222-1234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _one(unit::T, mat::AbstractMatrix) where {T}
--     (rows, cols) = axes(mat)
--     (length(rows) == length(cols)) ||
--       throw(DimensionMismatch("multiplicative identity defined only for square matrices"))
--     zer = zero(unit)::T
--     require_one_based_indexing(mat)
--     I = similar(mat, T)
--     fill!(I, zer)
--     for i ∈ rows
--         I[i, i] = unit
--     end
--     I
-- end
-- /Source
def oneMatrixChecked {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B E Ax I : Type} [ForIn m Ax I]
    (offsetDispatch : OffsetAxesDispatch m A)
    (axes : A → m (Ax × Ax)) (length : Ax → m I64)
    (first : Ax → m I) (toInt : I → m I64)
    (zero : E → m (Option E)) (similar : A → Type → m B)
    (fill : B → E → m Unit) (setindex : B → I → I → E → m Unit)
    (unit : E) (mat : A) : m B := do
  let (rows, cols) ← axes mat
  if (← length rows) != (← length cols) then
    throw (.dimensionMismatch "multiplicative identity defined only for square matrices")
  let zer ← assertZeroType (← zero unit)
  let _ ← requireOneBased (fun a =>
    match offsetDispatch with
    | .array => pure (hasOffsetArray a)
    | .fallback => hasOffsetAxesEffectful (fun a => do
        let (rs, cs) ← axes a
        pure [rs, cs]) first toInt a
    | .specialized method => method a) mat
  let ident ← similar mat E
  fill ident zer
  for i in rows do setindex ident i i unit
  return ident

/-- Close the _one call using oneMatrixChecked.
Julia source: base/abstractarray.jl:1236. The original caller body is
reused, including evaluating the element-type identity before axes.
Ty is the original element-type token; E is the actual type of its identity.
-/
-- Source: base/abstractarray.jl:1236-1236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(x::AbstractMatrix{T}) where {T} = _one(one(T), x)
-- /Source
def oneArrayChecked {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B E Ax I Ty : Type} [ForIn m Ax I]
    (offsetDispatch : OffsetAxesDispatch m A)
    (identity : Ty → m E) (axes : A → m (Ax × Ax)) (length : Ax → m I64)
    (first : Ax → m I) (toInt : I → m I64)
    (zero : E → m (Option E)) (similar : A → Type → m B)
    (fill : B → E → m Unit) (setindex : B → I → I → E → m Unit)
    (elementType : Ty) (mat : A) : m B :=
  oneArray identity (oneMatrixChecked offsetDispatch axes length first toInt zero similar fill setindex)
    elementType mat

/-- Close the _one call using oneMatrixChecked.
Julia source: base/abstractarray.jl:1237. The original caller body is
reused, including evaluating the element-type identity before axes.
Ty is the original element-type token; E is the actual type of its identity.
-/
-- Source: base/abstractarray.jl:1237-1237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- oneunit(x::AbstractMatrix{T}) where {T} = _one(oneunit(T), x)
-- /Source
def oneunitArrayChecked {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B E Ax I Ty : Type} [ForIn m Ax I]
    (offsetDispatch : OffsetAxesDispatch m A)
    (identity : Ty → m E) (axes : A → m (Ax × Ax)) (length : Ax → m I64)
    (first : Ax → m I) (toInt : I → m I64)
    (zero : E → m (Option E)) (similar : A → Type → m B)
    (fill : B → E → m Unit) (setindex : B → I → I → E → m Unit)
    (elementType : Ty) (mat : A) : m B :=
  oneunitArray identity (oneMatrixChecked offsetDispatch axes length first toInt zero similar fill setindex)
    elementType mat


/-- A source iteration state at the existing well-formed iterator-protocol boundary.
`linear` carries any Julia Integer representation, not just machine Int. A
Cartesian initial state is the singleton tuple `(eachindex(A),)`; `none` encodes
its missing iterator-state argument, and `some` encodes a resumed state.
Julia source: base/abstractarray.jl:1245-1259. -/
inductive IterationState (I Inds St : Type) where
  | linear (index : I)
  | cartesian (indices : Inds) (state : Option St)

/-- Close starting-state dispatch using the existing two method bodies.
Julia source: base/abstractarray.jl:1245. isLinear is the existing IndexStyle
reflection boundary (true exactly for IndexLinear, false for the fallback).
-/
-- Source: base/abstractarray.jl:1245-1247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate_starting_state(A) = iterate_starting_state(A, IndexStyle(A))
-- iterate_starting_state(A, ::IndexLinear) = firstindex(A)
-- iterate_starting_state(A, ::IndexStyle) = (eachindex(A),)
-- /Source
def iterateStartingStateLinked {m : Type → Type} [Monad m] {A I Inds St : Type}
    (isLinear : A → m Bool) (firstindex : A → m I) (eachindex : A → m Inds)
    (a : A) : m (IterationState I Inds St) :=
  iterateStartingState isLinear (fun a linear => do
    if linear then
      return .linear (← iterateStartingLinear firstindex a)
    else
      let state ← iterateStartingCartesian eachindex a
      return .cartesian state.1 none) a

/-- Dispatch a well-formed source state to the existing helper bodies.
Julia source: base/abstractarray.jl:1251-1259. The iterator protocol boundary
returns nothing or (index,next_state); a dynamic carrier can represent
changing iterator-state types. This is not a claim about malformed tuples
or arbitrary user-defined iterate implementations.
-/
-- Source: base/abstractarray.jl:1251-1259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _iterate_abstractarray(A::AbstractArray, state::Tuple)
--     y = iterate(state...)::Union{Nothing,Tuple}
--     y === nothing && return nothing
--     A[y[1]], (state[1], tail(y)...)
-- end
-- @inline function _iterate_abstractarray(A::AbstractArray, state::Integer)
--     checkbounds(Bool, A, state) || return nothing
--     A[state], state + one(state)
-- end
-- /Source
def iterateStateLinked {m : Type → Type} [Monad m] {A I Inds St E : Type}
    (checkbounds : A → I → m Bool) (getindex : A → I → m E)
    (one : I → m I) (add : I → I → m I)
    (start : Inds → m (Option (I × St))) (next : Inds → St → m (Option (I × St)))
    (a : A) : IterationState I Inds St → m (Option (E × IterationState I Inds St))
  | .linear i => do
      let result ← iterateInteger checkbounds getindex one add a i
      return result.map (fun (value, state) => (value, .linear state))
  | .cartesian indices state => do
      let result ← iterateCartesian (fun inds st =>
        match st with
        | none => start inds
        | some s => next inds s) getindex a (indices, state)
      return result.map (fun (value, inds, st) => (value, .cartesian inds (some st)))

/-- The missing optional-argument entry point iterate(A), with actual local
starting-state and helper dispatch. Julia source: base/abstractarray.jl:1250.
The explicit-state forwarding body iterateArray is reused. Every primitive
failure and effect remains in m; arithmetic of machine Integer instances
must be supplied using the existing JInt operations, never Nat increments.
-/
-- Source: base/abstractarray.jl:1250-1250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline iterate(A::AbstractArray, state = iterate_starting_state(A)) = _iterate_abstractarray(A, state)
-- /Source
def iterateDefault {m : Type → Type} [Monad m] {A I Inds St E : Type}
    (isLinear : A → m Bool) (firstindex : A → m I) (eachindex : A → m Inds)
    (checkbounds : A → I → m Bool) (getindex : A → I → m E)
    (one : I → m I) (add : I → I → m I)
    (start : Inds → m (Option (I × St))) (next : Inds → St → m (Option (I × St)))
    (a : A) : m (Option (E × IterationState I Inds St)) := do
  let state ← iterateStartingStateLinked isLinear firstindex eachindex a
  iterateArray (iterateStateLinked checkbounds getindex one add start next) a state

/-- Effectful type-object interpolation before the unsupported-index ErrorException.
Julia source: base/abstractarray.jl:1386-1387. Pure typeof is the existing type
reflection boundary; rendering each observed type token may mutate shared state
or throw. Both tokens are captured before interpolation. Their rendering order
is array type, then index-tuple type. The original error body is reused only
after both renderings succeed, so no renderer failure is hidden. -/
-- Source: base/abstractarray.jl:1386-1387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _getindex(::IndexStyle, A::AbstractArray, I...) =
--     error("getindex for $(typeof(A)) with types $(typeof(I)) is not supported")
-- /Source
def getindexUnsupportedEffectful {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Style A I E Ty : Type} (typeofA : A → Ty) (typeofI : I → Ty)
    (render : Ty → m String) (style : Style) (a : A) (is : I) : m E := do
  let ta := typeofA a
  let ti := typeofI is
  let shownA ← render ta
  let shownI ← render ti
  match getindexUnsupported (fun _ : A => shownA) (fun _ : I => shownI) style a is with
  | .ok result => pure result
  | .error error => throw error

/-- All-Integer scalar identity, including Bool, BigInt and external Integer types.
Julia source: base/abstractarray.jl:1398. I is the represented Julia Integer
carrier; no arithmetic or narrowing conversion occurs. -/
-- Source: base/abstractarray.jl:1398-1398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _to_linear_index(A::AbstractArray, i::Integer) = i
-- /Source
def toLinearScalarInteger {A I : Type} (_a : A) (i : I) : I := i

/-- All-Integer vector projection. Julia source: base/abstractarray.jl:1399.
Every extra index is ignored by this method, with no conversion or arithmetic.
The Integer signature is a dispatch invariant; Rest may encode heterogeneous
Integer types without restricting them to BitInteger. -/
-- Source: base/abstractarray.jl:1399-1399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _to_linear_index(A::AbstractVector, i::Integer, I::Integer...) = i
-- /Source
def toLinearVectorInteger {A I Rest : Type} (_a : A) (i : I) (_rest : Rest) : I := i

/-- Required tuple dependency: extracting the varargs tail keeps all values and their represented types unchanged.
Julia source: base/essentials.jl:523-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/essentials.jl:523-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- argtail(_, rest...) = rest
-- /Source
def tupleArgtail {I : Type} (_head : I) (rest : List I) : List I := rest

/-- Required tuple dependency: dispatch on the empty tuple preserves its ArgumentError.
The list is a tuple spine, not array storage.
Julia source: base/essentials.jl:541-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/essentials.jl:541-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- tail(x::Tuple) = argtail(x...)
-- tail(::Tuple{}) = throw(ArgumentError("Cannot call tail on an empty tuple."))
-- /Source
def tupleTail {I : Type} : List I → Result (List I)
  | [] => .error (.julia (.argumentError "Cannot call tail on an empty tuple."))
  | i :: is => .ok (tupleArgtail i is)

/-- Complete recursive dispatch for _remaining_size. The singleton case is reused.
The recursive method uses the existing body with its two tuple-tail operations,
so tail(h) is evaluated before tail(t). An empty h fails at that first tail;
it cannot enter the recursive continuation. No dimension arithmetic is performed.
Julia source: base/abstractarray.jl:1433-1434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/abstractarray.jl:1433-1434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _remaining_size(::Tuple{Any}, t::Tuple) = t
-- _remaining_size(h::Tuple, t::Tuple) = (@inline; _remaining_size(tail(h), tail(t)))
-- /Source
def remainingSize {I Axis : Type} : List I → List Axis → Result (List Axis)
  | [], _ => .error (.julia (.argumentError "Cannot call tail on an empty tuple."))
  | [i], axes => .ok (remainingSizeSingle i axes)
  | i :: j :: is, axes =>
      remainingSizeMany tupleTail tupleTail
        (fun _ trailing => remainingSize (j :: is) trailing) (i :: j :: is) axes

/-- Required IteratorsMD.split dependency: the _split1 dispatch family.
Nonempty recursion copies one tuple component and advances both spines.
The adjacent _splitrest source is retained as dispatch context.
Julia source: base/multidimensional.jl:527-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/multidimensional.jl:527-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @inline _split1(t, ref) = (t[1], _split1(tail(t), tail(ref))...)
--     @inline _splitrest(t, ref) = _splitrest(tail(t), tail(ref))
--     # exit either when we've exhausted the input or reference tuple
--     _split1(::Tuple{}, ::Tuple{}) = ()
--     _split1(::Tuple{}, ref) = ()
--     _split1(t, ::Tuple{}) = ()
--     _splitrest(::Tuple{}, ::Tuple{}) = ()
--     _splitrest(t, ::Tuple{}) = t
--     _splitrest(::Tuple{}, ref) = ()
-- /Source
def splitHead {I : Type} : List I → List Bool → List I
  | [], [] => []
  | [], _ :: _ => []
  | _ :: _, [] => []
  | i :: is, _ :: refs => i :: splitHead is refs

/-- Required IteratorsMD.split dependency: the _splitrest dispatch family.
The exhausted reference tuple returns the entire residual input tuple.
Julia source: base/multidimensional.jl:528-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/multidimensional.jl:528-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @inline _splitrest(t, ref) = _splitrest(tail(t), tail(ref))
--     # exit either when we've exhausted the input or reference tuple
--     _split1(::Tuple{}, ::Tuple{}) = ()
--     _split1(::Tuple{}, ref) = ()
--     _split1(t, ::Tuple{}) = ()
--     _splitrest(::Tuple{}, ::Tuple{}) = ()
--     _splitrest(t, ::Tuple{}) = t
--     _splitrest(::Tuple{}, ref) = ()
-- /Source
def splitRest {I : Type} : List I → List Bool → List I
  | [], [] => []
  | is, [] => is
  | [], _ :: _ => []
  | _ :: is, _ :: refs => splitRest is refs

/-- Required IteratorsMD.split dependency. Rank is a nonnegative type-level
natural; the reference tuple is materialized as a list spine. The two
recursive source traversals remain distinct and in source evaluation order.
Julia source: base/multidimensional.jl:523-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/multidimensional.jl:523-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @inline function split(t, V::Val)
--         ref = ntuple(Returns(true), V)  # create a reference tuple of length N
--         _split1(t, ref), _splitrest(t, ref)
--     end
-- /Source
def splitTuple {I : Type} (is : List I) (n : Nat) : List I × List I :=
  let refs := List.replicate n true
  let head := splitHead is refs
  let rest := splitRest is refs
  (head, rest)

/-- Closes the existing body over actual _remaining_size recursion and tuple tail.
Axis observations remain at the existing AbstractArray interface. In particular,
the source re-reads axes(A), even after the earlier dispatch read.
Julia source: base/abstractarray.jl:1426-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/abstractarray.jl:1426-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function __to_subscript_indices(A::AbstractArray,
--         ::Tuple{AbstractUnitRange,Vararg{AbstractUnitRange}}, J::Tuple, Jrem::Tuple{})
--     @inline
--     (J..., map(first, tail(_remaining_size(J, axes(A))))...)
-- end
-- /Source
def toSubscriptsFillClosed {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Axis I : Type} (axes : A → m (List Axis)) (first : Axis → m I)
    (a : A) (_dispatchAxes : Axis × List Axis) (j : List I) : m (List I) := do
  let remaining ← match remainingSize j (← axes a) with
    | .ok result => pure result
    | .error error => throw error
  let tail ← match tupleTail remaining with
    | .ok result => pure result
    | .error error => throw error
  let trailing ← tail.mapM first
  return j ++ trailing

/-- Closes the empty-remainder dispatch with the existing method body.
An empty axes tuple has no __to_subscript_indices method in this source, so
this dispatch failure is a MethodError. An Axis represents an AbstractUnitRange.
Julia source: base/abstractarray.jl:1424-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/abstractarray.jl:1424-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _to_subscript_indices(A::AbstractArray, J::Tuple, Jrem::Tuple{}) =
--     __to_subscript_indices(A, axes(A), J, Jrem)
-- function __to_subscript_indices(A::AbstractArray,
--         ::Tuple{AbstractUnitRange,Vararg{AbstractUnitRange}}, J::Tuple, Jrem::Tuple{})
--     @inline
--     (J..., map(first, tail(_remaining_size(J, axes(A))))...)
-- end
-- /Source
def toSubscriptsNoRemainderClosed {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Axis I : Type} (axes : A → m (List Axis)) (first : Axis → m I)
    (a : A) (j : List I) : m (List I) := do
  let observed ← axes a
  match observed with
  | [] => throw (.julia (.methodError "__to_subscript_indices"))
  | ax :: rest => toSubscriptsFillClosed axes first a (ax, rest) j

/-- Internal Julia dispatch between the empty-remainder specialization and
the general remainder fallback. Extra coordinates are discarded only by
the source fallback; this helper does not add a new bounds check.
Julia source: base/abstractarray.jl:1424-1431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/abstractarray.jl:1424-1431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _to_subscript_indices(A::AbstractArray, J::Tuple, Jrem::Tuple{}) =
--     __to_subscript_indices(A, axes(A), J, Jrem)
-- function __to_subscript_indices(A::AbstractArray,
--         ::Tuple{AbstractUnitRange,Vararg{AbstractUnitRange}}, J::Tuple, Jrem::Tuple{})
--     @inline
--     (J..., map(first, tail(_remaining_size(J, axes(A))))...)
-- end
-- _to_subscript_indices(A, J::Tuple, Jrem::Tuple) = J # already bounds-checked, safe to drop
-- /Source
def toSubscriptsRemainderClosed {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Axis I : Type} (axes : A → m (List Axis)) (first : Axis → m I)
    (a : A) (j remainder : List I) : m (List I) :=
  match remainder with
  | [] => toSubscriptsNoRemainderClosed axes first a j
  | _ :: _ => pure (toSubscriptsDropRemainder a j remainder)

/-- Closes tuple splitting and local remainder dispatch of the general
Integer-varargs method. More-specific scalar, zero-dimensional, empty-input,
and exact-rank Int methods remain separate existing declarations. Input I
may encode arbitrary Integer subtypes because this method performs no
arithmetic or index conversion. No arbitrary algorithm callback remains.
Julia source: base/abstractarray.jl:1419-1423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/abstractarray.jl:1419-1423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _to_subscript_indices(A::AbstractArray{T,N}, I::Integer...) where {T,N}
--     @inline
--     J, Jrem = IteratorsMD.split(I, Val(N))
--     _to_subscript_indices(A, J, Jrem)
-- end
-- /Source
def toSubscriptsSplitClosed {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Axis I : Type} (axes : A → m (List Axis)) (first : Axis → m I)
    (n : Nat) (a : A) (is : List I) : m (List I) := do
  let (j, remainder) := splitTuple is n
  toSubscriptsRemainderClosed axes first a j remainder


/-- Effectful type-object interpolation before the unsupported-index ErrorException.
Julia source: base/abstractarray.jl:1482-1483. Pure typeof is the existing type
reflection boundary; rendering each observed type token may mutate shared state
or throw. Both tokens are captured before interpolation. Their rendering order
is array type, then index-tuple type. The original error body is reused only
after both renderings succeed, so no renderer failure is hidden. -/
-- Source: base/abstractarray.jl:1482-1483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _setindex!(::IndexStyle, A::AbstractArray, v, I...) =
--     error("setindex! for $(typeof(A)) with types $(typeof(I)) is not supported")
-- /Source
def setindexUnsupportedEffectful {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Style A V I E Ty : Type} (typeofA : A → Ty) (typeofI : I → Ty)
    (render : Ty → m String) (style : Style) (a : A) (value : V) (is : I) : m E := do
  let ta := typeofA a
  let ti := typeofI is
  let shownA ← render ta
  let shownI ← render ti
  match setindexUnsupported (fun _ : A => shownA) (fun _ : I => shownI) style a value is with
  | .ok result => pure result
  | .error error => throw error

open JuliaLean JuliaLean.base.abstractarray

/-- A captured LazyString used only as an ArgumentError payload at
base/abstractarray.jl:1587-1591. Literal strings and Julia type objects remain
separate. This local value representation deliberately has no rendering operation.
The source calls below build a fixed-size tuple; this list does not represent
an unbounded Julia array. Message contents are erased only at the existing error
channel, as permitted when no property concerns exception text. -/
structure UnaliasLazyMessage (Ty : Type) where
  parts : List (Sum String Ty)
  compact : Bool
  rendered : Option String

/-- The nonrendering constructor needed at base/abstractarray.jl:1587.
Julia source: base/strings/lazy.jl:36-43. The source's new(args, false, nothing)
stores the captured type tokens without invoking their show/print methods.
Only the fields needed before the immediately following throw are represented;
this is not a model of later LazyString rendering or heap identity. -/
-- Source: base/strings/lazy.jl:36-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct LazyString <: AbstractString
--     const parts::Tuple
--     const compact::Bool # compact & limited output
--     # Created on first access
--     @atomic str::Union{String,Nothing}
--     global _LazyString(parts, str) = new(parts, false, str)
--     LazyString(args...; compact::Bool=false) = new(args, compact, nothing)
-- end
-- /Source
def unaliasLazyString {Ty : Type} (parts : List (Sum String Ty)) : UnaliasLazyMessage Ty :=
  { parts := parts, compact := false, rendered := none }

/-- ArgumentError payload projection for base/abstractarray.jl:1587-1591.
Julia source: base/boot.jl:549-552. The constructor stores its AbstractString;
it does not force a LazyString. The existing ArrayError channel retains the
ArgumentError class but has a String payload, so the message is explicitly
erased here. The empty string is an abstraction, not Julia's actual diagnostic.
No property in this group concerns exception message text or later display. -/
-- Source: base/boot.jl:549-552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct ArgumentError <: Exception
--     msg::AbstractString
--     ArgumentError(msg::AbstractString) = new(msg)
-- end
-- /Source
def throwUnaliasArgumentError {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty R : Type} (_message : UnaliasLazyMessage Ty) : m R :=
  throw (.julia (.argumentError ""))

/-- The mismatched-copy branch, preserving the pre-display behavior.
Julia source: base/abstractarray.jl:1585-1592. typeof, typename and the wrapper
field are pure runtime type-reflection inputs, as in the baseline. The source
wrapper observation precedes capture of the two types in the deferred message.
Type tokens are never converted into strings and no renderer callback is supplied.
Only exception text is abstracted; the thrown class and its position are retained. -/
-- Source: base/abstractarray.jl:1585-1592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _unaliascopy(A, C)
--     Aw = typename(typeof(A)).wrapper
--     throw(ArgumentError(LazyString("an array of type `", Aw, "` shares memory with another argument ",
--     "and must make a preventative copy of itself in order to maintain consistent semantics, ",
--     "but `copy(::", typeof(A), ")` returns a new array of type `", typeof(C), "`.\n",
--     """To fix, implement:
--         `Base.unaliascopy(A::""", Aw, ")::typeof(A)`")))
-- end
-- /Source
def unaliascopyMismatchDeferred {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A C Ty Name : Type} (typeofA : A → Ty) (typeofC : C → Ty)
    (typename : Ty → Name) (wrapper : Name → Ty) (a : A) (c : C) : m A := do
  let aw := wrapper (typename (typeofA a))
  let message := unaliasLazyString [
    .inl "an array of type `", .inr aw, .inl "` shares memory with another argument ",
    .inl "and must make a preventative copy of itself in order to maintain consistent semantics, ",
    .inl "but `copy(::", .inr (typeofA a), .inl ")` returns a new array of type `",
    .inr (typeofC c), .inl "`.\n",
    .inl "To fix, implement:\n        `Base.unaliascopy(A::", .inr aw, .inl ")::typeof(A)`"]
  throwUnaliasArgumentError message

/-- Close the local _unaliascopy dispatch in the public fallback.
Julia source: base/abstractarray.jl:1583-1584. The copy runtime boundary returns
inl c exactly when c has the Julia type typeof(a), and inr c when it has another
type. This tag is a dynamic-type representation, not a correctness hypothesis
about copy's contents, storage, termination, effects, or errors. C can represent
any wrong-typed copy value, including a nonarray. A denotes the source array type.
The same-typed branch reuses unaliascopySame and the existing convertSame model
(base/abstractarray.jl:16); the return annotation therefore adds no conversion
effect on that branch. The mismatched branch throws before conversion. The
existing unaliascopyArray caller preserves copy's effects before either branch. -/
-- Source: base/abstractarray.jl:1583-1584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unaliascopy(A::AbstractArray)::typeof(A) = (@noinline; _unaliascopy(A, copy(A)))
-- _unaliascopy(A::T, C::T) where {T} = C
-- /Source
def unaliascopyArrayTagged {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A C Ty Name : Type} (copy : A → m (Sum A C))
    (typeofA : A → Ty) (typeofC : C → Ty)
    (typename : Ty → Name) (wrapper : Name → Ty) (a : A) : m A :=
  unaliascopyArray copy
    (fun original result => match result with
      | .inl copied => pure (unaliascopySame original copied)
      | .inr other => unaliascopyMismatchDeferred typeofA typeofC typename wrapper original other)
    (fun copied => pure (convertSame copied)) a

/-- Representation of a finite Julia tuple of UInt data-segment identities.
The bound is a tuple-size representation invariant, not a guarantee of allocation success.
No machine arithmetic is performed on the list length. -/
structure DataIdTuple where
  values : List (JInt .u64)
  machineSized : (values.length : Int) ≤ IntTy.i64.max

/-- UInt specialization of base/operators.jl:1463: the comparison has type Bool,
so the accumulated result is Boolean and cannot be missing. The UInt values remain JInt.u64. -/
-- Source: base/operators.jl:1463-1471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _in_tuple(x, @nospecialize(itr::Tuple), result = false)
--     @inline
--     isempty(itr) && return result
--     v = (itr[1] == x)
--     if v === true
--         return true
--     end
--     return _in_tuple(x, tail(itr), result | v)
-- end
-- /Source
def uintInTupleAux (needle : JInt .u64) : List (JInt .u64) → Bool → Bool
  | [], result => result
  | x :: xs, result =>
      let v := decide (x.val = needle.val)
      if v then true else uintInTupleAux needle xs (result || v)

/-- UInt equality specialization of the tuple `_any` loop at base/anyall.jl:120.
Each predicate result is a Bool, so `ismissing(v)` is statically false, the
anymissing flag stays false, and the final branch returns false. All comparisons
and the first-true early return are retained. Extra dependency of mightalias. -/
-- Source: base/anyall.jl:117-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for ItrT = (Tuple,Any)
--     # define a generic method and a specialized version for `Tuple`,
--     # whose method bodies are identical, while giving better effects to the later
--     @eval function _any(f, itr::$ItrT, ::Colon)
--         $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
--         anymissing = false
--         for x in itr
--             v = f(x)
--             if ismissing(v)
--                 anymissing = true
--             else
--                 v && return true
--             end
--         end
--         return anymissing ? missing : false
--     end
-- end
-- /Source
def uintAnyTuple (needle : JInt .u64) (xs : List (JInt .u64)) : Bool := Id.run do
  for x in xs do
    let v := decide (x.val = needle.val)
    if v then return true
  return false

/-- Complete membership dispatch for the documented UInt tuple domain of
base/abstractarray.jl:1618-1624. At 32 tuple fields Julia selects the Any32 fallback
(base/tuple.jl:364-368), which invokes generic `in`; `any` on a homogeneous UInt
tuple selects its loop (base/anyall.jl:152-157). The comparison on the tuple's
static arity below implements method selection, not Julia integer arithmetic. -/
-- Source: base/operators.jl:1455-1474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- in(x, itr::Any) = any(==(x), itr)
-- 
-- # Specialized variant of in for Tuple, which can generate typed comparisons for each element
-- # of the tuple, skipping values that are statically known to be != at compile time.
-- in(x, itr::Tuple) = _in_tuple(x, itr)
-- 
-- # This recursive function will be unrolled at compiletime, and will not generate separate
-- # llvm-compiled specializations for each step of the recursion.
-- function _in_tuple(x, @nospecialize(itr::Tuple), result = false)
--     @inline
--     isempty(itr) && return result
--     v = (itr[1] == x)
--     if v === true
--         return true
--     end
--     return _in_tuple(x, tail(itr), result | v)
-- end
-- 
-- # fallback to the loop implementation after some number of arguments to avoid inference blowup
-- in(x, itr::Any32) = invoke(in, Tuple{Any,Any}, x, itr)
-- /Source
def uintTupleContains (needle : JInt .u64) (xs : List (JInt .u64)) : Bool :=
  if 32 ≤ xs.length then uintAnyTuple needle xs
  else uintInTupleAux needle xs false

/-- Closed dispatch for `_isdisjoint` at base/abstractarray.jl:1606-1614 on the
UInt tuples promised by dataids. Existing leaf method models are reused. This
is not a claim about arbitrary heterogeneous Tuple values or custom equality.
The frozen proof helper `disjointCalls` gives equivalent UInt dispatch but cannot
be imported into the canonical model because that would create an import cycle. -/
-- Source: base/abstractarray.jl:1606-1614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _isdisjoint(as::Tuple{}, bs::Tuple{}) = true
-- _isdisjoint(as::Tuple{}, bs::Tuple{UInt}) = true
-- _isdisjoint(as::Tuple{}, bs::Tuple) = true
-- _isdisjoint(as::Tuple{UInt}, bs::Tuple{}) = true
-- _isdisjoint(as::Tuple{UInt}, bs::Tuple{UInt}) = as[1] != bs[1]
-- _isdisjoint(as::Tuple{UInt}, bs::Tuple) = !(as[1] in bs)
-- _isdisjoint(as::Tuple, bs::Tuple{}) = true
-- _isdisjoint(as::Tuple, bs::Tuple{UInt}) = !(bs[1] in as)
-- _isdisjoint(as::Tuple, bs::Tuple) = !(as[1] in bs) && _isdisjoint(tail(as), bs)
-- /Source
def uintDataIdsDisjoint : List (JInt .u64) → List (JInt .u64) → Bool
  | [], [] => isdisjointEmptyEmpty
  | [], [b] => isdisjointEmptyOne b
  | [], bs => isdisjointEmptyMany bs
  | [a], [] => isdisjointOneEmpty a
  | [a], [b] => isdisjointOneOne a b
  | [a], bs => isdisjointOneMany uintTupleContains a bs
  | as, [] => isdisjointManyEmpty as
  | as, [b] => isdisjointManyOne uintTupleContains as b
  | a :: as, bs => isdisjointMany uintTupleContains
      (fun _ _ => uintDataIdsDisjoint as bs) (a, as) bs

/-- base/abstractarray.jl:1603 with the local recursive disjoint callee wired.
isbits, isempty and dataids remain the baseline explicit AbstractArray/runtime
interface; custom isempty methods retain their own dispatch, errors and effects.
The monad retains all boundary mutation in source order. The dataids interface
supplies its documented machine-sized tuple of UInt identities. -/
-- Source: base/abstractarray.jl:1603-1603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mightalias(A::AbstractArray, B::AbstractArray) = !isbits(A) && !isbits(B) && !isempty(A) && !isempty(B) && !_isdisjoint(dataids(A), dataids(B))
-- /Source
def mightaliasDataIds {m : Type → Type} [Monad m] {A B : Type}
    (isbitsA : A → m Bool) (isbitsB : B → m Bool)
    (isemptyA : A → m Bool) (isemptyB : B → m Bool)
    (dataidsA : A → m DataIdTuple) (dataidsB : B → m DataIdTuple)
    (a : A) (b : B) : m Bool :=
  mightaliasArray isbitsA isbitsB isemptyA isemptyB
    dataidsA dataidsB (fun as bs => pure (uintDataIdsDisjoint as.values bs.values)) a b

/-- Default-isempty specialization of base/abstractarray.jl:1603, using the
actual default body from base/abstractarray.jl:1262. This helper is explicitly
the default dispatch path; mightaliasDataIds above also permits custom isempty
methods at the existing array interface boundary. -/
-- Source: base/abstractarray.jl:1603-1603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mightalias(A::AbstractArray, B::AbstractArray) = !isbits(A) && !isbits(B) && !isempty(A) && !isempty(B) && !_isdisjoint(dataids(A), dataids(B))
-- /Source
def mightaliasDefaultDataIds {m : Type → Type} [Monad m] {A B : Type}
    (isbitsA : A → m Bool) (isbitsB : B → m Bool)
    (lengthA : A → m I64) (lengthB : B → m I64)
    (dataidsA : A → m DataIdTuple) (dataidsB : B → m DataIdTuple)
    (a : A) (b : B) : m Bool :=
  mightaliasDataIds isbitsA isbitsB (isemptyArray lengthA) (isemptyArray lengthB)
    dataidsA dataidsB a b

/-- Close dataids(Array)'s call to the existing dataids(Memory) body.
Julia source: base/abstractarray.jl:1628, with callee at :1627.
The existing runtime field interface remains explicit: ref, mem and ptr are
field projections. ptr exposes the native pointer's 64 address bits as JInt.u64,
not a dereferenceable allocation. UInt(ptr) preserves exactly those bits by
base/boot.jl:1198, `UInt(x::Ptr) = bitcast(UInt, x)`, so no conversion callback
or correctness assumption is needed. Array shape, reference offsets, element
type and storage contents do not restrict this caller's domain. This does not
claim implementation of allocation, GC relocation or field-layout primitives.
-/
-- Source: base/abstractarray.jl:1628-1628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- dataids(A::Array) = dataids(A.ref.mem)
-- /Source
def dataidsDenseLinked {m : Type → Type} [Monad m] {A Ref Memory : Type}
    (ref : A → Ref) (mem : Ref → Memory) (ptr : Memory → JInt .u64)
    (a : A) : m (List (JInt .u64)) :=
  dataidsDense ref mem (dataidsMemory ptr (fun address => pure address)) a

open JuliaLean JuliaLean.base.abstractarray

/-- A constructible Julia argument tuple. Its arity is a Julia Int64, and the
stored list has exactly that arity. This representation invariant excludes
unrestricted Lean lists whose size is not a Julia machine integer. -/
structure PromotionArgs (Value : Type) where
  values : List Value
  size : I64
  sizeCorrect : size.val = (values.length : Int)

/-- One source `op(y, bs[i])` step from base/operators.jl:628-660. The
existing tupleGet model supplies checked one-based tuple lookup, retaining its
BoundsError instead of silently returning the accumulator. op is the source's
actual higher-order argument, not a replacement implementation of afoldl. -/
-- Source: base/operators.jl:628-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     i =  1; y = op(y, bs[i]); l == i && return y
-- /Source
def argumentFoldAt {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Acc Value : Type} (op : Acc → Value → m Acc) (y : Acc)
    (bs : PromotionArgs Value) (i : I64) : m Acc := do
  let value ← match tupleGet bs.values i with
    | .ok value => pure value
    | .error error => throw error
  op y value

/-- Lower the remainder `for i in (i + 1):l` at base/operators.jl:659-662.
All actual indices and the endpoint are JInt.i64; successor uses the existing
wrapping addition. OrdinalRange iteration stops at the endpoint before forming
another successor (base/range.jl:935-942), so typemax never wraps into another
iteration. The Nat fuel is an auxiliary structural termination count equal to the exact
number of remaining iterations; its equality proof is erased. Its equality proof prevents early truncation;
zero fuel is admitted only for an empty residual range. -/
-- Source: base/operators.jl:659-662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     for i in (i + 1):l
--         y = op(y, bs[i])
--     end
--     return y
-- /Source
-- Source: base/range.jl:935-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(r::OrdinalRange) = isempty(r) ? nothing : (first(r), first(r))
-- 
-- function iterate(r::OrdinalRange{T}, i) where {T}
--     @inline
--     i == last(r) && return nothing
--     next = convert(T, i + step(r))
--     (next, next)
-- end
-- /Source
def argumentFoldTail {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Acc Value : Type} (op : Acc → Value → m Acc) (bs : PromotionArgs Value)
    (stop : I64) : (fuel : Nat) → (i : I64) → 0 ≤ i.val →
      fuel = (stop.val - i.val + 1).toNat → Acc → m Acc
  | 0, _i, _nonnegative, _exactFuel, y => pure y
  | fuel + 1, i, nonnegative, exactFuel, y => do
      let y ← argumentFoldAt op y bs i
      if atEnd : i.val = stop.val then return y
      else
        have beforeEnd : i.val < stop.val := by omega
        have successorValue : (i + int 1).val = i.val + 1 := by
          change wrapInt .i64 (i.val + (int 1).val) = i.val + 1
          rw [show (int 1).val = 1 by decide]
          apply wrapInt_of_inRange
          constructor
          · have minimumNonpositive : IntTy.i64.min ≤ 0 := by decide
            omega
          · have stopMaximum := stop.property.2
            omega
        have successorNonnegative : 0 ≤ (i + int 1).val := by
          rw [successorValue]
          omega
        have successorFuel : fuel = (stop.val - (i + int 1).val + 1).toNat := by
          rw [successorValue]
          omega
        argumentFoldTail op bs stop fuel (i + int 1)
          successorNonnegative successorFuel y

/-- Empty-argument afoldl specialization at base/operators.jl:622.
It does not invoke the supplied source operator. -/
-- Source: base/operators.jl:622-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- afoldl(op, a) = a
-- /Source
def argumentFoldEmpty {m : Type → Type} [Monad m] {Acc Value : Type}
    (_op : Acc → Value → m Acc) (a : Acc) : m Acc := pure a

/-- Effectful machine-indexed source body at base/operators.jl:623-663.
The thirty-one source steps are individually retained, including tuple lookup,
operator call, and only then the end test. The final range starts with wrapping
Int64 addition, and its exact residual count is used solely for termination.
No operator error or tuple error is replaced by a default accumulator. -/
-- Source: base/operators.jl:623-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function afoldl(op, a, bs...)
--     @_terminates_locally_meta
--     l = length(bs)
--     i =  0; y = a;            l == i && return y
--     #@nexprs 31 i -> (y = op(y, bs[i]); l == i && return y)
--     i =  1; y = op(y, bs[i]); l == i && return y
--     i =  2; y = op(y, bs[i]); l == i && return y
--     i =  3; y = op(y, bs[i]); l == i && return y
--     i =  4; y = op(y, bs[i]); l == i && return y
--     i =  5; y = op(y, bs[i]); l == i && return y
--     i =  6; y = op(y, bs[i]); l == i && return y
--     i =  7; y = op(y, bs[i]); l == i && return y
--     i =  8; y = op(y, bs[i]); l == i && return y
--     i =  9; y = op(y, bs[i]); l == i && return y
--     i = 10; y = op(y, bs[i]); l == i && return y
--     i = 11; y = op(y, bs[i]); l == i && return y
--     i = 12; y = op(y, bs[i]); l == i && return y
--     i = 13; y = op(y, bs[i]); l == i && return y
--     i = 14; y = op(y, bs[i]); l == i && return y
--     i = 15; y = op(y, bs[i]); l == i && return y
--     i = 16; y = op(y, bs[i]); l == i && return y
--     i = 17; y = op(y, bs[i]); l == i && return y
--     i = 18; y = op(y, bs[i]); l == i && return y
--     i = 19; y = op(y, bs[i]); l == i && return y
--     i = 20; y = op(y, bs[i]); l == i && return y
--     i = 21; y = op(y, bs[i]); l == i && return y
--     i = 22; y = op(y, bs[i]); l == i && return y
--     i = 23; y = op(y, bs[i]); l == i && return y
--     i = 24; y = op(y, bs[i]); l == i && return y
--     i = 25; y = op(y, bs[i]); l == i && return y
--     i = 26; y = op(y, bs[i]); l == i && return y
--     i = 27; y = op(y, bs[i]); l == i && return y
--     i = 28; y = op(y, bs[i]); l == i && return y
--     i = 29; y = op(y, bs[i]); l == i && return y
--     i = 30; y = op(y, bs[i]); l == i && return y
--     i = 31; y = op(y, bs[i]); l == i && return y
--     for i in (i + 1):l
--         y = op(y, bs[i])
--     end
--     return y
-- end
-- /Source
def argumentFoldMany {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Acc Value : Type} (op : Acc → Value → m Acc) (a : Acc)
    (bs : PromotionArgs Value) : m Acc := do
  let l := bs.size
  let i := int 0
  let y := a
  if l.val == i.val then return y
  let i := int 1
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 2
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 3
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 4
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 5
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 6
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 7
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 8
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 9
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 10
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 11
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 12
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 13
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 14
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 15
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 16
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 17
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 18
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 19
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 20
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 21
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 22
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 23
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 24
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 25
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 26
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 27
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 28
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 29
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 30
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let i := int 31
  let y ← argumentFoldAt op y bs i
  if l.val == i.val then return y
  let start := i + int 1
  argumentFoldTail op bs l (l.val - start.val + 1).toNat start
    (by decide) rfl y

/-- Source dispatch between the zero-rest and varargs afoldl methods at
base/operators.jl:622-663. Tuple emptiness here selects a method; no Julia
arithmetic is replaced by an unbounded length calculation. -/
-- Source: base/operators.jl:622-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- afoldl(op, a) = a
-- function afoldl(op, a, bs...)
--     @_terminates_locally_meta
--     l = length(bs)
--     i =  0; y = a;            l == i && return y
-- /Source
def argumentFold {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Acc Value : Type} (op : Acc → Value → m Acc) (a : Acc)
    (bs : PromotionArgs Value) : m Acc :=
  match bs.values with
  | [] => argumentFoldEmpty op a
  | _ :: _ => argumentFoldMany op a bs

/-- Dispatch tag distinguishing nonarray and AbstractArray values for the two
eltypeof methods. The tags are runtime type membership, not a callee correctness
law; the carriers may encode heterogeneous concrete Julia types. -/
inductive EltypeofArg (Scalar Array : Type) where
  | scalar (value : Scalar)
  | array (value : Array)

/-- Close `eltypeof` dispatch at base/abstractarray.jl:1679-1680 using the existing
bodies. typeof is pure runtime reflection; eltype retains the existing array
interface and may have effects/errors. In the array branch the baseline forwarding
model's result carrier is the action m Ty, so that the action runs exactly once. -/
-- Source: base/abstractarray.jl:1679-1680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltypeof(x) = typeof(x)
-- eltypeof(x::AbstractArray) = eltype(x)
-- /Source
def eltypeofSelected {m : Type → Type} [Monad m] {Scalar Array Ty : Type}
    (typeof : Scalar → Ty) (eltype : Array → m Ty) : EltypeofArg Scalar Array → m Ty
  | .scalar value => pure (eltypeofOther typeof value)
  | .array value => eltypeofArray eltype value

/-- The runtime's selected method for a two-argument promotion query.
ordinary selects the generic pair body; sameConcrete records the diagonal
same-type method and its genuine Julia type object; arrayElement records the
more-specific shared array-element-type method and its parameter. These are
method-selection tags at the existing explicit runtime dispatch boundary, not
callbacks that implement a missing Base algorithm. The source argument types
must actually select the tagged method. In all declarations below, Ty denotes
genuine Julia Type objects, so the afoldl lambda's ::Type{T} parameter is a
representation invariant. Incorrect non-Type returns from overriding promotion
are outside this typed runtime boundary, not silently accepted as type objects. -/
inductive PromotionPairMethod (Ty : Type) where
  | ordinary
  | sameConcrete (typeToken : Ty)
  | arrayElement (elementType : Ty)

/-- Single-argument internal method at base/abstractarray.jl:1683 with the local
eltypeof dispatch closed. This monadic completion retains effects of a custom
array eltype query, which the original Result-only wrapper cannot express. -/
-- Source: base/abstractarray.jl:1683-1683 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltypeof(v1) = eltypeof(v1)
-- /Source
def promoteEltypeofOneSelected {m : Type → Type} [Monad m] {Scalar Array Ty : Type}
    (typeof : Scalar → Ty) (eltype : Array → m Ty)
    (a : EltypeofArg Scalar Array) : m Ty :=
  eltypeofSelected typeof eltype a

/-- Two-argument internal method body at base/abstractarray.jl:1684. Scalar/array
eltypeof dispatch is closed, and the existing promoteEltypeofTwo body preserves
left query, right query, then promotion. promote_type remains the pre-existing
external numeric-type dispatch boundary; no full promotion model is claimed. -/
-- Source: base/abstractarray.jl:1684-1684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltypeof(v1, v2) = promote_type(eltypeof(v1), eltypeof(v2))
-- /Source
def promoteEltypeofTwoSelected {m : Type → Type} [Monad m]
    {Scalar Array Ty : Type} (typeof : Scalar → Ty) (eltype : Array → m Ty)
    (promote : Ty → Ty → m Ty) (a b : EltypeofArg Scalar Array) : m Ty :=
  promoteEltypeofTwo (eltypeofSelected typeof eltype) (eltypeofSelected typeof eltype)
    promote a b

/-- Same-concrete-type internal method at base/abstractarray.jl:1686, with local
eltypeof selection closed and the original method's effects preserved. The
runtime method tag guarantees the same concrete Julia type T; no rest argument
is inspected. The shared array-element-type method is a separate dispatch case. -/
-- Source: base/abstractarray.jl:1686-1686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltypeof(v1::T, vs::T...) where {T} = eltypeof(v1)
-- /Source
def promoteEltypeofSameSelected {m : Type → Type} [Monad m]
    {Scalar Array Ty Rest : Type} (typeof : Scalar → Ty) (eltype : Array → m Ty)
    (a : EltypeofArg Scalar Array) (_rest : Rest) : m Ty :=
  eltypeofSelected typeof eltype a

/-- Close the inner two-argument call made by base/abstractarray.jl:1685.
The runtime selects among the generic pair, same-concrete-type, and shared
array-element-type methods. In particular, a mixed outer argument list can
have a same-type first pair: that pair must not make an extra promotion call.
The existing array-parameter leaf is reused and never calls eltype. -/
-- Source: base/abstractarray.jl:1684-1687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltypeof(v1, v2) = promote_type(eltypeof(v1), eltypeof(v2))
-- promote_eltypeof(v1, v2, vs...) = (@inline; afoldl(((::Type{T}, y) where {T}) -> promote_type(T, eltypeof(y)), promote_eltypeof(v1, v2), vs...))
-- promote_eltypeof(v1::T, vs::T...) where {T} = eltypeof(v1)
-- promote_eltypeof(v1::AbstractArray{T}, vs::AbstractArray{T}...) where {T} = T
-- /Source
def promoteEltypeofPairSelected {m : Type → Type} [Monad m]
    {Scalar Array Ty : Type} (typeof : Scalar → Ty) (eltype : Array → m Ty)
    (promote : Ty → Ty → m Ty) (method : PromotionPairMethod Ty)
    (a b : EltypeofArg Scalar Array) : m Ty :=
  match method with
  | .ordinary => promoteEltypeofTwoSelected typeof eltype promote a b
  | .sameConcrete _ => promoteEltypeofSameSelected typeof eltype a b
  | .arrayElement elementType => pure (promoteEltypeofArrays elementType a b)

/-- Internal varargs method at base/abstractarray.jl:1685 with concrete local
eltypeof selection, actual selected inner-pair method bodies, and machine-indexed
afoldl. The existing typed wrapper is reused. The pairMethod argument records
runtime method selection, not an assumed algorithm result. External eltype and
promote_type errors/effects propagate at their original source point. -/
-- Source: base/abstractarray.jl:1685-1685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltypeof(v1, v2, vs...) = (@inline; afoldl(((::Type{T}, y) where {T}) -> promote_type(T, eltypeof(y)), promote_eltypeof(v1, v2), vs...))
-- /Source
def promoteEltypeofManyClosed {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Scalar Array Ty : Type} (typeof : Scalar → Ty) (eltype : Array → m Ty)
    (promote : Ty → Ty → m Ty) (pairMethod : PromotionPairMethod Ty)
    (a b : EltypeofArg Scalar Array) (vs : PromotionArgs (EltypeofArg Scalar Array)) : m Ty :=
  promoteEltypeofMany (eltypeofSelected typeof eltype) promote
    (promoteEltypeofPairSelected typeof eltype promote pairMethod) argumentFold a b vs

/-- Same-concrete-type internal method at base/abstractarray.jl:1693. It queries
eltype on the shared type object T, not on the first value. This monadic
completion preserves custom type-level eltype effects beyond the baseline's
Result-only wrapper. The type token is supplied by runtime method selection. -/
-- Source: base/abstractarray.jl:1693-1693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltype(v1::T, vs::T...) where {T} = eltype(T)
-- /Source
def promoteEltypeSameEffectful {m : Type → Type} [Monad m]
    {A Rest Ty : Type} (eltypeType : Ty → m Ty) (typeToken : Ty)
    (_a : A) (_rest : Rest) : m Ty :=
  eltypeType typeToken

/-- Close the inner two-argument call of base/abstractarray.jl:1692, including
same-concrete-type and shared-array-element-type dispatch. The generic pair and
array-parameter bodies are reused unchanged; the 1694 declaration is an existing
out-of-queue callee dependency, not a newly translated method. -/
-- Source: base/abstractarray.jl:1691-1694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltype(v1, v2) = promote_type(eltype(v1), eltype(v2))
-- promote_eltype(v1, v2, vs...) = (@inline; afoldl(((::Type{T}, y) where {T}) -> promote_type(T, eltype(y)), promote_eltype(v1, v2), vs...))
-- promote_eltype(v1::T, vs::T...) where {T} = eltype(T)
-- promote_eltype(v1::AbstractArray{T}, vs::AbstractArray{T}...) where {T} = T
-- /Source
def promoteEltypePairSelected {m : Type → Type} [Monad m]
    {A B Ty : Type} (eltypeA : A → m Ty) (eltypeB : B → m Ty)
    (eltypeType : Ty → m Ty) (promote : Ty → Ty → m Ty)
    (method : PromotionPairMethod Ty) (a : A) (b : B) : m Ty :=
  match method with
  | .ordinary => promoteEltypeTwo eltypeA eltypeB promote a b
  | .sameConcrete typeToken => promoteEltypeSameEffectful eltypeType typeToken a b
  | .arrayElement elementType => pure (promoteEltypeArrays elementType a b)

/-- Internal varargs method at base/abstractarray.jl:1692. The exact selected
inner-pair method and the concrete machine-indexed argument fold replace the two
local algorithm callbacks. Value-level and type-level eltype queries are separate,
as Julia requires in the same-concrete-type pair method. Numeric type promotion
remains the baseline typed runtime boundary; no correctness law is supplied. -/
-- Source: base/abstractarray.jl:1692-1692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltype(v1, v2, vs...) = (@inline; afoldl(((::Type{T}, y) where {T}) -> promote_type(T, eltype(y)), promote_eltype(v1, v2), vs...))
-- /Source
def promoteEltypeManyClosed {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B Value Ty : Type} (eltypeA : A → m Ty) (eltypeB : B → m Ty)
    (eltype : Value → m Ty) (eltypeType : Ty → m Ty) (promote : Ty → Ty → m Ty)
    (pairMethod : PromotionPairMethod Ty) (a : A) (b : B)
    (vs : PromotionArgs Value) : m Ty :=
  promoteEltypeMany eltype promote
    (promoteEltypePairSelected eltypeA eltypeB eltypeType promote pairMethod)
    argumentFold a b vs

end JuliaLean.base.abstractarray.Models1Group2


namespace JuliaLean.base.abstractarray.Models1Group3

/-! Closed instances for the assigned homogeneous scalar comprehensions.
The payload type represents the Julia element type, including reference-valued
payloads. MachineTuple records the runtime length and its representation
invariant. DenseLiteral describes the freshly produced array's observable
shape and element sequence together with the returned allocation handle.
Constructor checks and resource failures stay at the pre-existing explicit
allocation boundary. No callee correctness law is an input.
-/

/-- A native tuple whose field count is an Int64. The equality is a representation
invariant, not a restriction selected for a property. Source: base/tuple.jl:28. -/
structure MachineTuple (E : Type) where
  values : List E
  count : I64
  count_eq : count.val = (values.length : Int)

/-- Value observation of a new dense array. Its element type is E; the shape
contains Julia Int64 dimensions. Elements are retained as values, so reference
payloads are copied without deep copying. Source: base/abstractarray.jl:1703-1706. -/
structure DenseLiteral (E Handle : Type) where
  storage : Handle
  shape : List I64
  values : List E

/-- Native tuple keys, base/tuple.jl:75. List.range enumerates the finite tuple
positions; addition on the returned Julia indices uses wrapping I64 arithmetic.
The MachineTuple invariant makes every enumerated index representable. -/
-- Source: base/tuple.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keys(@nospecialize t::Tuple) = OneTo(length(t))
-- /Source
def tupleKeys {E : Type} (xs : MachineTuple E) : Result (List I64) :=
  pure ((List.range xs.values.length).map fun (k : Nat) => int k + int 1)

/-- The tuple instance of eachindex, base/abstractarray.jl:322, through the
existing generic eachindex model and the concrete tuple keys above. -/
-- Source: base/abstractarray.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(itrs...) = keys(itrs...)
-- /Source
def tupleEachindex {E : Type} (xs : MachineTuple E) : Result (List I64) :=
  eachindexIterators tupleKeys xs

/-- Closed homogeneous vertical comprehension, base/abstractarray.jl:1703.
The iterator is formed, the array is allocated, then the source body reads
the tuple in order. The allocator receives the actual Int64 dimensions and
returns only a storage handle, never a supposed concatenation result.
Every constructor error is retained. E is the requested element type;
base/array.jl:1031-1045 makes same-type stores identity conversions. -/
-- Source: base/abstractarray.jl:1703-1703 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- vcat(X::T...) where {T}         = T[ X[i] for i=eachindex(X) ]
-- /Source
def homogeneousVcat {E Handle : Type}
    (allocate : I64 → Result Handle)
    (xs : MachineTuple E) : Result (DenseLiteral E Handle) := do
  let indices ← tupleEachindex xs
  let storage ← allocate xs.count
  JuliaLean.base.abstractarray.vcatSame (fun (_ : MachineTuple E) => pure indices)
    (fun ys i => tupleGet ys.values i)
    (fun (_ : Unit) values => pure ⟨storage, [xs.count], values⟩) () xs

/-- Closed homogeneous vertical comprehension, base/abstractarray.jl:1704.
The iterator is formed, the array is allocated, then the source body reads
the tuple in order. The allocator receives the actual Int64 dimensions and
returns only a storage handle, never a supposed concatenation result.
Every constructor error is retained. E is the requested element type;
base/array.jl:1031-1045 makes same-type stores identity conversions. -/
-- Source: base/abstractarray.jl:1704-1704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- vcat(X::T...) where {T<:Number} = T[ X[i] for i=eachindex(X) ]
-- /Source
def homogeneousNumberVcat {E Handle : Type}
    (allocate : I64 → Result Handle)
    (xs : MachineTuple E) : Result (DenseLiteral E Handle) := do
  let indices ← tupleEachindex xs
  let storage ← allocate xs.count
  JuliaLean.base.abstractarray.vcatSameNumbers (fun (_ : MachineTuple E) => pure indices)
    (fun ys i => tupleGet ys.values i)
    (fun (_ : Unit) values => pure ⟨storage, [xs.count], values⟩) () xs

/-- Closed homogeneous horizontal comprehension, base/abstractarray.jl:1705.
The iterator is formed, the array is allocated, then the source body reads
the tuple in order. The allocator receives the actual Int64 dimensions and
returns only a storage handle, never a supposed concatenation result.
Every constructor error is retained. E is the requested element type;
base/array.jl:1031-1045 makes same-type stores identity conversions. -/
-- Source: base/abstractarray.jl:1705-1705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hcat(X::T...) where {T}         = T[ X[j] for _=1:1, j=eachindex(X) ]
-- /Source
def homogeneousHcat {E Handle : Type}
    (allocate : I64 → I64 → Result Handle)
    (xs : MachineTuple E) : Result (DenseLiteral E Handle) := do
  let indices ← tupleEachindex xs
  let storage ← allocate (int 1) xs.count
  JuliaLean.base.abstractarray.hcatSame (fun (_ : MachineTuple E) => pure indices)
    (fun ys i => tupleGet ys.values i)
    (fun (_ : Unit) nrows values => pure ⟨storage, [nrows, xs.count], values⟩) () xs

/-- Closed homogeneous horizontal comprehension, base/abstractarray.jl:1706.
The iterator is formed, the array is allocated, then the source body reads
the tuple in order. The allocator receives the actual Int64 dimensions and
returns only a storage handle, never a supposed concatenation result.
Every constructor error is retained. E is the requested element type;
base/array.jl:1031-1045 makes same-type stores identity conversions. -/
-- Source: base/abstractarray.jl:1706-1706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hcat(X::T...) where {T<:Number} = T[ X[j] for _=1:1, j=eachindex(X) ]
-- /Source
def homogeneousNumberHcat {E Handle : Type}
    (allocate : I64 → I64 → Result Handle)
    (xs : MachineTuple E) : Result (DenseLiteral E Handle) := do
  let indices ← tupleEachindex xs
  let storage ← allocate (int 1) xs.count
  JuliaLean.base.abstractarray.hcatSameNumbers (fun (_ : MachineTuple E) => pure indices)
    (fun ys i => tupleGet ys.values i)
    (fun (_ : Unit) nrows values => pure ⟨storage, [nrows, xs.count], values⟩) () xs

end JuliaLean.base.abstractarray.Models1Group3

namespace JuliaLean.base.abstractarray.Models1Group3

/-- The pre-existing explicit Array runtime boundary used by numeric typed
concatenation. Allocation, shape observation, and primitive setindex! retain
all effects of m, including conversion errors and mutations before failure.
No fill, recursive concatenation, promotion, or callee-correctness operation
is supplied. Source: base/abstractarray.jl:1720-1730,2527-2627. -/
structure NumericArrayRuntime (m : Type → Type) (Ty A E : Type) where
  vector : Ty → I64 → m A
  matrix : Ty → I64 → I64 → m A
  size : A → I64 → m I64
  shape : A → m (MachineTuple I64)
  set : A → I64 → E → m Unit
  set2 : A → I64 → I64 → E → m Unit

/-- Embed a closed native-tuple observation in the existing effect monad;
its existing ArrayError is preserved. This is representation plumbing, not
an additional Julia method or runtime callback. -/
def numericFromResult {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {E : Type} : Result E → m E
  | .ok value => pure value
  | .error err => throw err

/-- Structural enumeration for the source's native `1:n` loops. Nat is only
iteration fuel; every produced Julia index uses JInt addition. Nonpositive
ends enumerate no indices. This helper is needed by the reused row-first
loop but is unreachable from both assigned callers, which pass false.
Source: base/abstractarray.jl:2538-2542. -/
-- Source: base/abstractarray.jl:2538-2542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         for d ∈ 1:na
--             dd = nrc * (d - 1)
--             for i ∈ 1:nr
--                 Ai = dd + i
--                 for _ ∈ 1:nc
-- /Source
def numericOneTo (last : I64) : List I64 :=
  (List.range last.val.toNat).map fun (k : Nat) => int k + int 1

/-- The product of the Int64 tuple after dropping its first two fields;
empty products are Int64 one and every multiplication wraps as Julia Int.
This closes the `tailProduct` input of the existing fill-loop mirror. The
source tuple specialization is base/tuple.jl:688,693; its existing wrapper
prodIntTuple only delegates the variadic multiplication it is passed.
Source: base/abstractarray.jl:2529. -/
-- Source: base/abstractarray.jl:2529-2529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     na = prod(size(A)[3:end])
-- /Source
def numericTailProduct {m : Type → Type} [Monad m] {Ty A E : Type}
    (runtime : NumericArrayRuntime m Ty A E) (a : A) : m I64 := do
  let sizes ← runtime.shape a
  return sizes.values.drop 2 |>.foldl (fun total size => total * size) (int 1)

/-- Render the native Int64 size tuple for the existing error branch. The
runtime shape read remains at the throw site; no formatter callback or
assumption is added. Error-message IO allocation failures are outside the
existing ArrayError message abstraction; the exception class is retained.
Source: base/abstractarray.jl:2533,2566,2593. -/
-- Source: base/abstractarray.jl:2533-2533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         throw(ArgumentError("argument count $(len) does not match specified shape $(size(A))"))
-- /Source
def numericShowShape {m : Type → Type} [Monad m] {Ty A E : Type}
    (runtime : NumericArrayRuntime m Ty A E) (a : A) : m String := do
  let sizes ← runtime.shape a
  let body := String.intercalate ", " (sizes.values.map fun size => toString size.val)
  return "(" ++ body ++ (if sizes.values.length = 1 then "," else "") ++ ")"

/-- Close both generated and interpreter branches of the existing fill
models. `generated` selects Julia's two compiler execution paths; `rank`
is the statically known rank of the Array constructor used by the caller.
Tuple length, eachindex and reads are closed; all native index arithmetic is
I64. No fill implementation or recursion callback is accepted as input.
The literal first endpoint supplied by hvncatFillLoop is always one, so the
local range closure is exactly the source's `1:n` ranges.
Source: base/abstractarray.jl:2527-2627. -/
-- Source: base/abstractarray.jl:2527-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _hvncat_fill_loop!(A::Array, row_first::Bool, xs::Tuple)
--     nr, nc = size(A, 1), size(A, 2)
--     na = prod(size(A)[3:end])
--     len = length(xs)
--     nrc = nr * nc
--     if nrc * na != len
--         throw(ArgumentError("argument count $(len) does not match specified shape $(size(A))"))
--     end
--     # putting these in separate functions leads to unnecessary allocations
--     if row_first
--         k = 1
--         for d ∈ 1:na
--             dd = nrc * (d - 1)
--             for i ∈ 1:nr
--                 Ai = dd + i
--                 for _ ∈ 1:nc
--                     @inbounds A[Ai] = xs[k]
--                     k += 1
--                     Ai += nr
--                 end
--             end
--         end
--     else
--         for k ∈ eachindex(xs)
--             @inbounds A[k] = xs[k]
--         end
--     end
-- end
--
-- function hvncat_fill!(A::Array, row_first::Bool, xs::Tuple)
--     if @generated
--         N = fieldcount(xs)
--         N > 32 && return :(return _hvncat_fill_loop!(A, row_first, xs))
--         nd = ndims(A)
--         if nd <= 2
--             return quote
--                 nr = size(A, 1)
--                 nc = size(A, 2)
--                 if nr*nc != $N
--                     throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
--                 end
--                 if row_first
--                     i::Int = 1
--                     j::Int = 1
--                     @nexprs $N k -> begin
--                         @inbounds A[i, j] = xs[k]
--                         j += 1
--                         if j > nc
--                             i += 1
--                             j = 1
--                         end
--                     end
--                 else
--                     @nexprs $N k -> begin
--                         @inbounds A[k] = xs[k]
--                     end
--                 end
--                 nothing
--             end
--         else
--             return quote
--                 nr = size(A, 1)
--                 nc = size(A, 2)
--                 nrc = nr * nc
--                 na = prod(size(A)[3:end])
--                 if nrc * na != $N
--                     throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
--                 end
--                 if row_first
--                     d::Int = 1
--                     i::Int = 1
--                     dd::Int = 0
--                     Ai::Int = dd + i
--                     j::Int = 1
--                     @nexprs $N k -> begin
--                         @inbounds A[Ai] = xs[k]
--                         j += 1
--                         Ai += nr
--                         if j > nc
--                             j = 1
--                             i += 1
--                             if i > nr
--                                 i = 1
--                                 d += 1
--                                 dd = nrc * (d - 1)
--                             end
--                             Ai = dd + i
--                         end
--                     end
--                 else
--                     @nexprs $N k -> begin
--                         @inbounds A[k] = xs[k]
--                     end
--                 end
--                 nothing
--             end
--         end
--     else
--         _hvncat_fill_loop!(A, row_first, xs)
--     end
-- end
-- /Source
def numericFill {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty A E : Type} (runtime : NumericArrayRuntime m Ty A E)
    (generated : Bool) (rank : Nat) (a : A) (rowFirst : Bool)
    (xs : MachineTuple E) : m Unit :=
  hvncatFill generated xs.values.length rank runtime.size
    (numericTailProduct runtime) (numericShowShape runtime)
    (fun ys i => numericFromResult (tupleGet ys.values i))
    runtime.set runtime.set2
    (fun target first ys =>
      hvncatFillLoop runtime.size (numericTailProduct runtime)
        (fun zs => pure zs.count) (numericShowShape runtime)
        (fun _ last => pure (numericOneTo last))
        (fun zs => numericFromResult (tupleEachindex zs))
        (fun zs i => numericFromResult (tupleGet zs.values i)) runtime.set
        target first ys)
    a rowFirst xs

/-- Typed scalar vertical concatenation composed from the existing source
mirror and the closed fill implementation. The constructor fixes rank one;
the explicit Array boundary retains allocation and setindex! conversion
errors, mutation and effects. This does not assert allocator correctness.
Source: base/abstractarray.jl:1720-1724. -/
-- Source: base/abstractarray.jl:1720-1724 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function typed_vcat(::Type{T}, X::Number...) where {T}
--     a = Vector{T}(undef, length(X))
--     hvncat_fill!(a, false, X)
--     return a
-- end
-- /Source
def typedNumericVcat {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty A E : Type} (runtime : NumericArrayRuntime m Ty A E)
    (generated : Bool) (t : Ty) (xs : MachineTuple E) : m A :=
  typedVcatNumbers (fun ys => pure ys.count) runtime.vector
    (numericFill runtime generated 1) t xs

/-- Typed scalar horizontal concatenation composed from the existing source
mirror and the closed fill implementation. The constructor fixes rank two;
the explicit Array boundary retains allocation and setindex! conversion
errors, mutation and effects. This does not assert allocator correctness.
Source: base/abstractarray.jl:1726-1730. -/
-- Source: base/abstractarray.jl:1726-1730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function typed_hcat(::Type{T}, X::Number...) where {T}
--     a = Matrix{T}(undef, 1, length(X))
--     hvncat_fill!(a, false, X)
--     return a
-- end
-- /Source
def typedNumericHcat {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty A E : Type} (runtime : NumericArrayRuntime m Ty A E)
    (generated : Bool) (t : Ty) (xs : MachineTuple E) : m A :=
  typedHcatNumbers (fun ys => pure ys.count) runtime.matrix
    (numericFill runtime generated 2) t xs

end JuliaLean.base.abstractarray.Models1Group3

namespace JuliaLean.base.abstractarray.Models1Group3

/-- The array RHS overload returns the RHS after assignment, independently
of the primitive setindex! return value. The indexed-store boundary is the
same one used by the frozen source mirror, now with its result correctly
observed. Effects and errors remain in m; no copy/conversion callback is
introduced. Source: base/abstractarray.jl:1942; assignment lowering is
specified at base/array.jl:1014-1016. -/
-- Source: base/abstractarray.jl:1942-1942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _copy_or_fill!(A, inds, x::AbstractArray) = (A[inds...] = x)
-- /Source
def copyArrayReturningRhs {m : Type → Type} [Monad m] {A I X Ret : Type}
    (set : A → I → X → m Ret) (a : A) (inds : I) (x : X) : m X := do
  copyOrFillArray (fun dest indices value => do
    let _ ← set dest indices value
    pure ()) a inds x
  return x

end JuliaLean.base.abstractarray.Models1Group3

namespace JuliaLean.base.abstractarray.Models1Group3

/-- Necessary closed Int64-tuple sum dependency for base/abstractarray.jl:2247.
The generic tuple sum maps identity, seeds reduce_first with the first Int64,
and adds the remaining fields left-to-right. Every addition is native and
wraps; no mathematical Int accumulator replaces it. Empty tuple eltype is
Union{}, so its reduction would throw the source's ArgumentError. The caller
never reaches that case because it first reads rows[1].
Source: base/reduce.jl:19,40-67,83-84,306,319-321,411-415,546,575. -/
-- Source: base/reduce.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- add_sum(x::Real, y::Real)::Real = x + y
-- /Source
-- Source: base/reduce.jl:40-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function mapfoldl_impl(f::F, op::OP, nt, itr) where {F,OP}
--     op′, itr′ = _xfadjoint(BottomRF(op), Generator(f, itr))
--     return foldl_impl(op′, nt, itr′)
-- end
--
-- function foldl_impl(op::OP, nt, itr) where {OP}
--     v = _foldl_impl(op, nt, itr)
--     v isa _InitialValue && return reduce_empty_iter(op, itr)
--     return v
-- end
--
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
--
-- function _foldl_impl(op, init, itr::Union{Tuple,NamedTuple})
--     length(itr) <= 32 && return afoldl(op, init, itr...)
--     @invoke _foldl_impl(op, init, itr::Any)
-- /Source
-- Source: base/reduce.jl:83-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::BottomRF)(::_InitialValue, x) = reduce_first(op.rf, x)
-- @inline (op::BottomRF)(acc, x) = op.rf(acc, x)
-- /Source
-- Source: base/reduce.jl:319-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(f, T) = _empty_reduce_error()
-- mapreduce_empty(f, op, T) = _empty_reduce_error()
-- reduce_empty(f, ::Type{Union{}}, splat...) = _empty_reduce_error()
-- /Source
-- Source: base/reduce.jl:411-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(op, x) = x
-- reduce_first(::typeof(+), x::Bool) = Int(x)
-- reduce_first(::typeof(*), x::AbstractChar) = string(x)
--
-- reduce_first(::typeof(add_sum), x) = reduce_first(+, x)
-- /Source
-- Source: base/reduce.jl:546-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(f, a; kw...) = mapreduce(f, add_sum, a; kw...)
-- /Source
-- Source: base/reduce.jl:575-575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(a; kw...) = sum(identity, a; kw...)
-- /Source
def rowWidthsSum : List I64 → Result I64
  | [] => .error (.julia (.argumentError
      "reducing over an empty collection is not allowed; consider supplying `init` to the reducer"))
  | first :: rest => pure (rest.foldl (fun total width => total + width) first)

/-- Close the existing row-shape model over every native Int tuple, including
empty tuples, negative widths and overflowing sums. Tuple reads use tupleGet,
and the sum uses rowWidthsSum. The MachineTuple invariant makes the returned
row count a constructible Int64, without adding a shape-validity premise.
Source: base/abstractarray.jl:2247. -/
-- Source: base/abstractarray.jl:2247-2247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rows_to_dimshape(rows::Tuple{Vararg{Int}}) = all(==(rows[1]), rows) ? (length(rows), rows[1]) : (rows, (sum(rows),))
-- /Source
def rowDimensions (rows : MachineTuple I64) :
    Result (Sum (I64 × I64) (List I64 × List I64)) :=
  rowsToDimshape tupleGet rowWidthsSum rows.values

end JuliaLean.base.abstractarray.Models1Group3

namespace JuliaLean.base.abstractarray.Models1Group3

/-- Native Matrix metadata is assigned by the constructor, never supplied by
an arbitrary length/size callback. Ref is the opaque allocation/reference
handle at the existing primitive boundary. The selected Julia element type
is represented by elementType; rows/columns are the stored native size tuple.
Only matrices produced by nativeMatrix below enter the assigned method.
Source: base/boot.jl:825-827; base/essentials.jl:12-13. -/
-- Source: base/boot.jl:825-827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
-- end))
-- /Source
structure NativeMatrix (Ty Ref : Type) where
  elementType : Ty
  reference : Ref
  rows : I64
  columns : I64

/-- The remaining primitive boundary allocates the memory/reference handle
for a selected type and validated element count, and performs homogeneous
Cartesian stores. It cannot select or change Matrix metadata. Its effects
and errors remain arbitrary; no allocation or store correctness law is an
input. Generic conversion is unnecessary for same-T stores at
base/array.jl:1042-1052. Source: base/boot.jl:779,825-827. -/
structure HvcatArrayRuntime (m : Type → Type) (Ty Ref E : Type) where
  allocateRef : Ty → I64 → m Ref
  set2 : NativeMatrix Ty Ref → I64 → I64 → E → m Unit

/-- Required local two-dimensional checked multiplication dependency. The
returned product is an actual wrapping JInt operation. Mathematical Int
arithmetic occurs only in the overflow bit's primitive semantic definition;
it never replaces a Julia result or intermediate. Unsigned remainder into
UInt64 preserves the operand bit pattern for the source's ule_int tests.
The native product, overflow bit, and two ordered flag combinations mirror
_checked_mul_dims exactly. The existing boot model cannot be imported with
the supplied prebuilt closure, so this necessary specialization stays local.
Source: base/boot.jl:784-791. -/
-- Source: base/boot.jl:784-791 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _checked_mul_dims(m::Int, n::Int)
--     b = Intrinsics.checked_smul_int(m, n)
--     a = getfield(b, 1)
--     ovflw = getfield(b, 2)
--     ovflw = Intrinsics.or_int(ovflw, Intrinsics.ule_int(typemax_Int, m))
--     ovflw = Intrinsics.or_int(ovflw, Intrinsics.ule_int(typemax_Int, n))
--     return a, ovflw
-- end
-- /Source
def matrixCheckedMulDimensions (nr nc : I64) : I64 × Bool :=
  let product := nr * nc
  let overflow := decide
    (nr.val * nc.val < JuliaLean.IntTy.i64.min ∨
      JuliaLean.IntTy.i64.max < nr.val * nc.val)
  let threshold := (JuliaLean.JInt.rem .u64 (JuliaLean.JInt.typemax .i64)).val
  let invalidRows := decide (threshold ≤ (JuliaLean.JInt.rem .u64 nr).val)
  let overflow := overflow || invalidRows
  let invalidColumns := decide (threshold ≤ (JuliaLean.JInt.rem .u64 nc).val)
  let overflow := overflow || invalidColumns
  (product, overflow)

/-- Required two-dimension checked_dims specialization: reject the exact
native invalid-dimension flag before any primitive allocation.
Source: base/boot.jl:814-818. -/
-- Source: base/boot.jl:814-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checked_dims(d::Int...)
--     b = _checked_mul_dims(d...)
--     getfield(b, 2) && throw(ArgumentError("invalid Array dimensions"))
--     return getfield(b, 1)
-- end
-- /Source
def matrixCheckedDimensions (nr nc : I64) : Result I64 := do
  let result := matrixCheckedMulDimensions nr nc
  if result.2 then throw (.julia (.argumentError "invalid Array dimensions"))
  return result.1

/-- Required native Matrix constructor specialization. Dimension validation
precedes raw allocation; successful allocation is followed by installation
of exactly the requested size tuple and selected type. The raw primitive
returns only an opaque reference handle, not a Matrix or metadata. This
closes the invalid-metadata path that would otherwise make @inbounds tuple
reads undefined rather than legitimate BoundsErrors.
Source: base/boot.jl:779,825-827. -/
-- Source: base/boot.jl:779-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- new_as_memoryref(self::Type{GenericMemoryRef{kind,T,addrspace}}, m::Int) where {T,kind,addrspace} = memoryref(fieldtype(self, :mem)(undef, m))
-- /Source
-- Source: base/boot.jl:825-827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
-- end))
-- /Source
def nativeMatrix {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref E : Type} (runtime : HvcatArrayRuntime m Ty Ref E)
    (t : Ty) (nr nc : I64) : m (NativeMatrix Ty Ref) := do
  let count ← numericFromResult (matrixCheckedDimensions nr nc)
  let reference ← runtime.allocateRef t count
  return ⟨t, reference, nr, nc⟩

/-- Required fixed Matrix length: size is its stored two-field tuple and
prod on the native Int64 pair is the native product. Each source call
recomputes this value; there is no mutable or arbitrary length callback.
Source: base/essentials.jl:12-13; base/tuple.jl:693. -/
-- Source: base/essentials.jl:12-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
-- Source: base/tuple.jl:693-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- prod(x::Tuple{Int, Vararg{Int}}) = *(x...)
-- /Source
def nativeMatrixLength {Ty Ref : Type} (a : NativeMatrix Ty Ref) : I64 :=
  a.rows * a.columns

/-- Close the selected homogeneous-number hvcat body over native tuples and native
Matrix construction/metadata. Empty rows fail before allocation. The reused
body retains both length evaluations in count-error diagnostics, repeated
row reads in width-error diagnostics, and row checks interleaved with stores.
All loop/index values remain JInt; Nat only enumerates finite ranges.
Constructor validation plus the closed argument-count check ensure every
subsequent source @inbounds tuple read is actually within the native tuple.
The public zero-argument call selects the separate method at2250; this
definition represents the explicitly selected homogeneous method body.
Source: base/abstractarray.jl:2253-2272. -/
-- Source: base/abstractarray.jl:2253-2272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function hvcat(rows::Tuple{Vararg{Int}}, xs::T...) where T<:Number
--     nr = length(rows)
--     nc = rows[1]
--
--     a = Matrix{T}(undef, nr, nc)
--     if length(a) != length(xs)
--         throw(ArgumentError("argument count does not match specified shape (expected $(length(a)), got $(length(xs)))"))
--     end
--     k = 1
--     @inbounds for i=1:nr
--         if nc != rows[i]
--             throw(DimensionMismatch("row $(i) has mismatched number of columns (expected $nc, got $(rows[i]))"))
--         end
--         for j=1:nc
--             a[i,j] = xs[k]
--             k += 1
--         end
--     end
--     a
-- end
-- /Source
def homogeneousNumericHvcat {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref E : Type} (runtime : HvcatArrayRuntime m Ty Ref E)
    (t : Ty) (rows : MachineTuple I64) (xs : MachineTuple E) :
    m (NativeMatrix Ty Ref) :=
  hvcatSameNumbers (fun rs => pure rs.count)
    (fun rs i => numericFromResult (tupleGet rs.values i))
    (nativeMatrix runtime) (fun a => pure (nativeMatrixLength a)) (fun ys => pure ys.count)
    (fun _ last => pure (numericOneTo last))
    (fun ys i => numericFromResult (tupleGet ys.values i)) runtime.set2
    t rows xs

end JuliaLean.base.abstractarray.Models1Group3

namespace JuliaLean.base.abstractarray.Models1Group3

/-- The typed numeric method permits a requested T different from argument
Number types. Both primitive setindex! forms therefore retain conversion,
store effects and failures at the existing Array runtime boundary. The two
primitives have their actual separate effects; no coherence law is assumed.
Raw allocation returns only a handle, never freely chosen Matrix metadata.
Source: base/abstractarray.jl:2279-2290; base/array.jl:1031-1052. -/
-- Source: base/abstractarray.jl:2279-2290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function typed_hvcat(::Type{T}, rows::Tuple{Vararg{Int}}, xs::Number...) where T
--     nr = length(rows)
--     nc = rows[1]
--     for i = 2:nr
--         if nc != rows[i]
--             throw(DimensionMismatch("row $(i) has mismatched number of columns (expected $nc, got $(rows[i]))"))
--         end
--     end
--     a = Matrix{T}(undef, nr, nc)
--     hvncat_fill!(a, true, xs)
--     return a
-- end
-- /Source
structure TypedHvcatArrayRuntime (m : Type → Type) (Ty Ref E : Type) where
  allocateRef : Ty → I64 → m Ref
  set : NativeMatrix Ty Ref → I64 → E → m Unit
  set2 : NativeMatrix Ty Ref → I64 → I64 → E → m Unit

/-- Native Matrix size metadata, with the exact two-field tuple invariant.
Source: base/essentials.jl:12. -/
-- Source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- /Source
def nativeMatrixShape {Ty Ref : Type} (a : NativeMatrix Ty Ref) : MachineTuple I64 :=
  ⟨[a.rows, a.columns], int 2, by change (int 2).val = 2; decide⟩

/-- The existing size(A,dim) source mirror applied to the Matrix's fixed
native size tuple. Native Int conversion is identity, trailing dimensions
are singleton, and nonpositive dimensions preserve tuple BoundsError.
Source: base/abstractarray.jl:42-46; base/essentials.jl:12. -/
-- Source: base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function size(t::AbstractArray, dim)
--     d = Int(dim)::Int
--     s = size(t)
--     d <= length(s) ? s[d] : 1
-- end
-- /Source
def nativeMatrixSize {Ty Ref : Type} (a : NativeMatrix Ty Ref) (dim : I64) : Result I64 :=
  sizeDim (fun d : I64 => pure d)
    (fun matrix : NativeMatrix Ty Ref => pure [matrix.rows, matrix.columns]) a dim

/-- Constructor projection: nativeMatrix uses only allocateRef. Its unused
homogeneous-store element type is Empty, so no such store can be called.
This does not identify typed conversion with homogeneous identity conversion.
Source: base/boot.jl:825-827. -/
-- Source: base/boot.jl:825-827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
-- end))
-- /Source
private def typedHvcatMatrix {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref E : Type} (runtime : TypedHvcatArrayRuntime m Ty Ref E)
    (t : Ty) (nr nc : I64) : m (NativeMatrix Ty Ref) :=
  nativeMatrix (E := Empty)
    { allocateRef := runtime.allocateRef
      set2 := fun _ _ _ impossible => nomatch impossible } t nr nc

/-- Fill-only projection of NumericArrayRuntime. Its unused allocator type
parameter is Empty, so vector/matrix fields are total uncallable functions,
not error stubs or claimed Vector implementations. numericFill observes
only the closed metadata and the actual typed setindex! primitives.
Source: base/abstractarray.jl:2556-2627 (the reused fill source mirror). -/
-- Source: base/abstractarray.jl:2556-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function hvncat_fill!(A::Array, row_first::Bool, xs::Tuple)
--     if @generated
--         N = fieldcount(xs)
--         N > 32 && return :(return _hvncat_fill_loop!(A, row_first, xs))
--         nd = ndims(A)
--         if nd <= 2
--             return quote
--                 nr = size(A, 1)
--                 nc = size(A, 2)
--                 if nr*nc != $N
--                     throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
--                 end
--                 if row_first
--                     i::Int = 1
--                     j::Int = 1
--                     @nexprs $N k -> begin
--                         @inbounds A[i, j] = xs[k]
--                         j += 1
--                         if j > nc
--                             i += 1
--                             j = 1
--                         end
--                     end
--                 else
--                     @nexprs $N k -> begin
--                         @inbounds A[k] = xs[k]
--                     end
--                 end
--                 nothing
--             end
--         else
--             return quote
--                 nr = size(A, 1)
--                 nc = size(A, 2)
--                 nrc = nr * nc
--                 na = prod(size(A)[3:end])
--                 if nrc * na != $N
--                     throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
--                 end
--                 if row_first
--                     d::Int = 1
--                     i::Int = 1
--                     dd::Int = 0
--                     Ai::Int = dd + i
--                     j::Int = 1
--                     @nexprs $N k -> begin
--                         @inbounds A[Ai] = xs[k]
--                         j += 1
--                         Ai += nr
--                         if j > nc
--                             j = 1
--                             i += 1
--                             if i > nr
--                                 i = 1
--                                 d += 1
--                                 dd = nrc * (d - 1)
--                             end
--                             Ai = dd + i
--                         end
--                     end
--                 else
--                     @nexprs $N k -> begin
--                         @inbounds A[k] = xs[k]
--                     end
--                 end
--                 nothing
--             end
--         end
--     else
--         _hvncat_fill_loop!(A, row_first, xs)
--     end
-- end
-- /Source
private def typedHvcatFillRuntime {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref E : Type} (runtime : TypedHvcatArrayRuntime m Ty Ref E) :
    NumericArrayRuntime m Empty (NativeMatrix Ty Ref) E where
  vector := fun impossible _ => nomatch impossible
  matrix := fun impossible _ _ => nomatch impossible
  size := fun a d => numericFromResult (nativeMatrixSize a d)
  shape := fun a => pure (nativeMatrixShape a)
  set := runtime.set
  set2 := runtime.set2

/-- Selected typed numeric hvcat body. The source's 2:nr row-validation
range is exactly numericOneTo(nr) with its first value dropped. All width
checks precede native constructor validation and raw allocation. The existing
numericFill supplies both generated and interpreter branches at rank two
and row_first=true, with closed native metadata preventing unchecked tuple
exhaustion. Primitive stores retain typed conversion and mutation failures.
Public typed_hvcat(T,rows) without values selects2251 instead; this definition
represents the explicitly selected2279 body, not complete generic dispatch.
Source: base/abstractarray.jl:2279-2290. -/
-- Source: base/abstractarray.jl:2279-2290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function typed_hvcat(::Type{T}, rows::Tuple{Vararg{Int}}, xs::Number...) where T
--     nr = length(rows)
--     nc = rows[1]
--     for i = 2:nr
--         if nc != rows[i]
--             throw(DimensionMismatch("row $(i) has mismatched number of columns (expected $nc, got $(rows[i]))"))
--         end
--     end
--     a = Matrix{T}(undef, nr, nc)
--     hvncat_fill!(a, true, xs)
--     return a
-- end
-- /Source
def typedNumericHvcat {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref E : Type} (runtime : TypedHvcatArrayRuntime m Ty Ref E)
    (generated : Bool) (t : Ty) (rows : MachineTuple I64) (xs : MachineTuple E) :
    m (NativeMatrix Ty Ref) :=
  typedHvcatNumbers (fun rs => pure rs.count)
    (fun rs i => numericFromResult (tupleGet rs.values i))
    (fun _ last => pure ((numericOneTo last).drop 1))
    (typedHvcatMatrix runtime) (numericFill (typedHvcatFillRuntime runtime) generated 2)
    t rows xs

end JuliaLean.base.abstractarray.Models1Group3

namespace JuliaLean.base.abstractarray.Models1Group3

/-- Observation of an arbitrary inner tuple member. Native Int64 values are
retained; every other Julia value is represented by other. Such values include
Bool, other integer widths, nested tuples, arrays, functions, types and custom
objects. The only inspection made by source2732 is dispatch of the first
inner member to _typed_hvncat_1d(::Type,::Int,...); that dispatch rejects all
other cases before their values can be evaluated. No input type is excluded.
Source: base/abstractarray.jl:2501,2732-2736. -/
-- Source: base/abstractarray.jl:2501-2501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat_1d(::Type{T}, ds::Int, ::Val{row_first}, as...) where {T, row_first}
-- /Source
-- Source: base/abstractarray.jl:2732-2736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(T::Type, shape::Tuple{Tuple}, row_first::Bool, xs...)
--     length(shape[1]) > 0 ||
--         throw(ArgumentError("each level of `shape` argument must have at least one value"))
--     return _typed_hvncat_1d(T, shape[1][1], Val(row_first), xs...)
-- end
-- /Source
inductive EmptyHvncatInnerValue where
  | nativeInt (value : I64)
  | other
  deriving Repr, DecidableEq

/-- Observation of any outer tuple field: native Int, an arbitrary inner
Tuple, or any remaining Julia value. Inner tuples are machine-sized and may
contain any mix of native and other values. This is an observation-based
representation of all values in the source Tuple domain, not a homogeneity
precondition. Source: base/abstractarray.jl:2384,2492-2499,2514,2732,2738. -/
-- Source: base/abstractarray.jl:2384-2384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool) = _typed_hvncat(Any, dimsshape, row_first)
-- /Source
-- Source: base/abstractarray.jl:2492-2499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(T::Type, ::Tuple{}, ::Bool, x...) = _typed_hvncat(T, Val(0), x...)
-- _typed_hvncat(T::Type, ::Tuple{}, ::Bool, x::Number...) = _typed_hvncat(T, Val(0), x...)
--
--
-- # balanced dimensions hvncat methods
--
-- _typed_hvncat(T::Type, dims::Tuple{Int}, ::Bool, as...) = _typed_hvncat_1d(T, dims[1], Val(false), as...)
-- _typed_hvncat(T::Type, dims::Tuple{Int}, ::Bool, as::Number...) = _typed_hvncat_1d(T, dims[1], Val(false), as...)
-- /Source
-- Source: base/abstractarray.jl:2514-2514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(::Type{T}, dims::NTuple{N, Int}, row_first::Bool, xs::Number...) where {T, N}
-- /Source
-- Source: base/abstractarray.jl:2732-2732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(T::Type, shape::Tuple{Tuple}, row_first::Bool, xs...)
-- /Source
-- Source: base/abstractarray.jl:2738-2738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(T::Type, shape::NTuple{N, Tuple}, row_first::Bool, as...) where {N}
-- /Source
inductive EmptyHvncatMember where
  | nativeInt (value : I64)
  | tuple (value : MachineTuple EmptyHvncatInnerValue)
  | other

/-- The complete Union{Tuple,Int} dimension domain for the no-value
overload. Tuple field counts carry the actual native representation invariant.
Source: base/abstractarray.jl:2384. -/
-- Source: base/abstractarray.jl:2384-2384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool) = _typed_hvncat(Any, dimsshape, row_first)
-- /Source
inductive EmptyHvncatDimensions where
  | nativeInt (rank : I64)
  | tuple (fields : MachineTuple EmptyHvncatMember)

/-- Native Array metadata installed by its constructor: selected element
type, opaque reference, and the exact machine-sized native dimension tuple.
The raw allocator cannot fabricate or mutate this metadata. Source:
base/boot.jl:831-833; base/essentials.jl:12-13. -/
-- Source: base/boot.jl:831-833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T, N}})(::UndefInitializer, d::Vararg{Int, N}) where {T, N}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(d...))), :d))
-- end))
-- /Source
-- Source: base/essentials.jl:12-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
structure EmptyHvncatArray (Ty Ref : Type) where
  elementType : Ty
  reference : Ref
  dimensions : MachineTuple I64

/-- The only remaining effectful primitive for empty hvncat: allocation
of a memory/reference handle for the selected type, exact dimension context
and checked native element count. Context permits rank/shape-sensitive
allocation effects and errors, including distinct zero-cell shapes; it does
not let the primitive choose returned Array metadata. Type formation and
physical dimension-tuple creation before validation remain structural
representations, with separate VM/resource failures outside the available
primitives; no runtime rank limit is invented. No concatenation, conversion,
fill, size, length or dispatch implementation is supplied. Source:
base/boot.jl:779,821-838. -/
-- Source: base/boot.jl:779-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- new_as_memoryref(self::Type{GenericMemoryRef{kind,T,addrspace}}, m::Int) where {T,kind,addrspace} = memoryref(fieldtype(self, :mem)(undef, m))
-- /Source
-- Source: base/boot.jl:821-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
-- end))
-- eval(Core, :(function (self::Type{Array{T,3}})(::UndefInitializer, m::Int, n::Int, o::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n, o))), :((m, n, o))))
-- end))
-- eval(Core, :(function (self::Type{Array{T, N}})(::UndefInitializer, d::Vararg{Int, N}) where {T, N}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(d...))), :d))
-- end))
-- # type and dimensionality specified, accepting dims as tuples of Ints
-- (self::Type{Array{T,1}})(::UndefInitializer, d::NTuple{1, Int}) where {T} = self(undef, getfield(d, 1))
-- (self::Type{Array{T,2}})(::UndefInitializer, d::NTuple{2, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2))
-- (self::Type{Array{T,3}})(::UndefInitializer, d::NTuple{3, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2), getfield(d, 3))
-- (self::Type{Array{T,N}})(::UndefInitializer, d::NTuple{N, Int}) where {T, N} = self(undef, d...)
-- /Source
structure EmptyHvncatRuntime (m : Type → Type) (Ty Ref : Type) where
  allocateRef : Ty → MachineTuple I64 → I64 → m Ref

/-- The actual empty value tuple passed by source2384. Empty is its value
type, so no value or store can be fabricated in an unreachable fill branch.
Source: base/abstractarray.jl:2384. -/
-- Source: base/abstractarray.jl:2384-2384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool) = _typed_hvncat(Any, dimsshape, row_first)
-- /Source
def emptyHvncatArguments : MachineTuple Empty :=
  ⟨[], int 0, by rfl⟩

/-- Closed bit-preserving unsigned comparison used by native dimension
validation. This rejects negatives and typemax(Int) itself. Source:
base/boot.jl:783,797,804. -/
-- Source: base/boot.jl:783-783 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _checked_mul_dims(m::Int) = m, Intrinsics.ule_int(typemax_Int, m) # equivalently: (m + 1) < 1
-- /Source
-- Source: base/boot.jl:797-797 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     neg = Intrinsics.ule_int(typemax_Int, m)
-- /Source
-- Source: base/boot.jl:804-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         neg = Intrinsics.or_int(neg, Intrinsics.ule_int(typemax_Int, di))
-- /Source
def emptyHvncatInvalidDimension (dimension : I64) : Bool :=
  decide ((JuliaLean.JInt.rem .u64 (JuliaLean.JInt.typemax .i64)).val ≤
    (JuliaLean.JInt.rem .u64 dimension).val)

/-- Required checked_smul_int specialization: the result is native JInt
multiplication; exact Int arithmetic only defines the intrinsic overflow bit.
It never replaces a Julia value or arithmetic intermediate. Source:
base/boot.jl:801. -/
-- Source: base/boot.jl:801-801 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         b = Intrinsics.checked_smul_int(a, di)
-- /Source
def emptyHvncatCheckedMultiply (a b : I64) : I64 × Bool :=
  (a * b, decide (a.val * b.val < JuliaLean.IntTy.i64.min ∨
    JuliaLean.IntTy.i64.max < a.val * b.val))

/-- Required local native checked-dimension loop. List recursion is finite
tuple iteration fuel; the source accumulator, index increment and all flags
remain native. Its only caller supplies the tail of a MachineTuple, whose
length is at most typemax(Int)-1, so the source loop index cannot wrap before
termination. Source: base/boot.jl:792-809. -/
-- Source: base/boot.jl:792-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _checked_mul_dims(m::Int, d::Int...)
--     @_foldable_meta # the compiler needs to know this loop terminates
--     a = m
--     i = 1
--     ovflw = false
--     neg = Intrinsics.ule_int(typemax_Int, m)
--     zero = false # if m==0 we won't have overflow since we go left to right
--     while Intrinsics.sle_int(i, nfields(d))
--         di = getfield(d, i)
--         b = Intrinsics.checked_smul_int(a, di)
--         zero = Intrinsics.or_int(zero, di === 0)
--         ovflw = Intrinsics.or_int(ovflw, getfield(b, 2))
--         neg = Intrinsics.or_int(neg, Intrinsics.ule_int(typemax_Int, di))
--         a = getfield(b, 1)
--         i = Intrinsics.add_int(i, 1)
--    end
--    return a, Intrinsics.or_int(neg, Intrinsics.and_int(ovflw, Intrinsics.not_int(zero)))
-- end
-- /Source
def emptyHvncatCheckedDimensionsLoop :
    I64 → I64 → Bool → Bool → Bool → List I64 → I64 × Bool × Bool × Bool
  | a, _index, overflow, negative, zero, [] => (a, overflow, negative, zero)
  | a, index, overflow, negative, zero, dimension :: rest =>
      let product := emptyHvncatCheckedMultiply a dimension
      let zero := zero || dimension.val == 0
      let overflow := overflow || product.2
      let negative := negative || emptyHvncatInvalidDimension dimension
      let a := product.1
      let index := index + int 1
      emptyHvncatCheckedDimensionsLoop a index overflow negative zero rest

/-- Concrete overload selection for native _checked_mul_dims. The
two-field branch reuses the already installed2253 helper. The general branch
preserves zero's suppression of overflow, but never suppresses invalid
dimensions. Existing boot models cannot be imported using the supplied
prebuilt closure, so this required dependency stays local. Source:
base/boot.jl:782-809. -/
-- Source: base/boot.jl:782-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _checked_mul_dims() = 1, false
-- _checked_mul_dims(m::Int) = m, Intrinsics.ule_int(typemax_Int, m) # equivalently: (m + 1) < 1
-- function _checked_mul_dims(m::Int, n::Int)
--     b = Intrinsics.checked_smul_int(m, n)
--     a = getfield(b, 1)
--     ovflw = getfield(b, 2)
--     ovflw = Intrinsics.or_int(ovflw, Intrinsics.ule_int(typemax_Int, m))
--     ovflw = Intrinsics.or_int(ovflw, Intrinsics.ule_int(typemax_Int, n))
--     return a, ovflw
-- end
-- function _checked_mul_dims(m::Int, d::Int...)
--     @_foldable_meta # the compiler needs to know this loop terminates
--     a = m
--     i = 1
--     ovflw = false
--     neg = Intrinsics.ule_int(typemax_Int, m)
--     zero = false # if m==0 we won't have overflow since we go left to right
--     while Intrinsics.sle_int(i, nfields(d))
--         di = getfield(d, i)
--         b = Intrinsics.checked_smul_int(a, di)
--         zero = Intrinsics.or_int(zero, di === 0)
--         ovflw = Intrinsics.or_int(ovflw, getfield(b, 2))
--         neg = Intrinsics.or_int(neg, Intrinsics.ule_int(typemax_Int, di))
--         a = getfield(b, 1)
--         i = Intrinsics.add_int(i, 1)
--    end
--    return a, Intrinsics.or_int(neg, Intrinsics.and_int(ovflw, Intrinsics.not_int(zero)))
-- end
-- /Source
def emptyHvncatCheckedDimensionsFlags (dimensions : MachineTuple I64) : I64 × Bool :=
  match dimensions.values with
  | [] => (int 1, false)
  | [dimension] => (dimension, emptyHvncatInvalidDimension dimension)
  | [rows, columns] => matrixCheckedMulDimensions rows columns
  | first :: rest =>
      let (product, overflow, negative, zero) :=
        emptyHvncatCheckedDimensionsLoop first (int 1) false
          (emptyHvncatInvalidDimension first) false rest
      (product, negative || (overflow && !zero))

/-- Concrete checked_dims dispatch. Its zero and one-argument overloads
do not call _checked_mul_dims: the one-dimensional validation is deferred to
Memory allocation. Two or more dimensions preserve the exact flag check
before any raw allocation. Source: base/boot.jl:812-818. -/
-- Source: base/boot.jl:812-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checked_dims() = 1
-- checked_dims(m::Int) = m # defer this check to Memory constructor instead
-- function checked_dims(d::Int...)
--     b = _checked_mul_dims(d...)
--     getfield(b, 2) && throw(ArgumentError("invalid Array dimensions"))
--     return getfield(b, 1)
-- end
-- /Source
def emptyHvncatCheckedDimensions (dimensions : MachineTuple I64) : Result I64 := do
  match dimensions.values with
  | [] => return int 1
  | [dimension] => return dimension
  | _ =>
      let checked := emptyHvncatCheckedDimensionsFlags dimensions
      if checked.2 then throw (.julia (.argumentError "invalid Array dimensions"))
      return checked.1

/-- Required native Array constructor. Concrete dimension validation
precedes raw allocation; after success the model installs exactly the type
and dimension tuple supplied by the Julia caller. The memory primitive
receives the exact dimension context but returns only a reference. The rank-one branch's checked_dims identity
preserves its direct-Memory constructor behavior. Source:
base/boot.jl:779,821-838. -/
-- Source: base/boot.jl:779-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- new_as_memoryref(self::Type{GenericMemoryRef{kind,T,addrspace}}, m::Int) where {T,kind,addrspace} = memoryref(fieldtype(self, :mem)(undef, m))
-- /Source
-- Source: base/boot.jl:821-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
-- end))
-- eval(Core, :(function (self::Type{Array{T,3}})(::UndefInitializer, m::Int, n::Int, o::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n, o))), :((m, n, o))))
-- end))
-- eval(Core, :(function (self::Type{Array{T, N}})(::UndefInitializer, d::Vararg{Int, N}) where {T, N}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(d...))), :d))
-- end))
-- # type and dimensionality specified, accepting dims as tuples of Ints
-- (self::Type{Array{T,1}})(::UndefInitializer, d::NTuple{1, Int}) where {T} = self(undef, getfield(d, 1))
-- (self::Type{Array{T,2}})(::UndefInitializer, d::NTuple{2, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2))
-- (self::Type{Array{T,3}})(::UndefInitializer, d::NTuple{3, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2), getfield(d, 3))
-- (self::Type{Array{T,N}})(::UndefInitializer, d::NTuple{N, Int}) where {T, N} = self(undef, d...)
-- /Source
def emptyHvncatAllocate {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref : Type} (runtime : EmptyHvncatRuntime m Ty Ref)
    (elementType : Ty) (dimensions : MachineTuple I64) : m (EmptyHvncatArray Ty Ref) := do
  let count ← numericFromResult (emptyHvncatCheckedDimensions dimensions)
  let reference ← runtime.allocateRef elementType dimensions count
  return ⟨elementType, reference, dimensions⟩

/-- Native Array length is recomputed from the stored size tuple. Empty
products are native1; nonempty products start with the first native value,
and each multiplication wraps. No metadata callback or allocator law is
used. Source: base/essentials.jl:12-13; base/tuple.jl:688-693. -/
-- Source: base/essentials.jl:12-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
-- Source: base/tuple.jl:688-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- prod(x::Tuple{}) = 1
-- # This is consistent with the regular prod because there is no need for size promotion
-- # if all elements in the tuple are of system size.
-- # It is defined here separately in order to support bootstrap, because it's needed earlier
-- # than the general prod definition is available.
-- prod(x::Tuple{Int, Vararg{Int}}) = *(x...)
-- /Source
def emptyHvncatArrayLength {Ty Ref : Type} (array : EmptyHvncatArray Ty Ref) : I64 :=
  match array.dimensions.values with
  | [] => int 1
  | first :: rest => rest.foldl (fun product dimension => product * dimension) first

/-- Closed native size(A,d), reusing the existing source mirror and
tuple indexing. Identity conversion is exact because every requested
dimension already is native Int64. Source: base/abstractarray.jl:42-46;
base/essentials.jl:12. -/
-- Source: base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function size(t::AbstractArray, dim)
--     d = Int(dim)::Int
--     s = size(t)
--     d <= length(s) ? s[d] : 1
-- end
-- /Source
-- Source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- /Source
def emptyHvncatArraySize {Ty Ref : Type} (array : EmptyHvncatArray Ty Ref)
    (dimension : I64) : Result I64 :=
  sizeDim pure (fun a => pure a.dimensions.values) array dimension

/-- Closed Array observations for the actual empty fill dependency.
Both the allocator type and stored value type are Empty: these operations
cannot be called, not supplied as arbitrary callbacks. Source array size
and shape are the installed descriptor's own metadata. Source:
base/abstractarray.jl:2527-2554; base/essentials.jl:12. -/
-- Source: base/abstractarray.jl:2527-2554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _hvncat_fill_loop!(A::Array, row_first::Bool, xs::Tuple)
--     nr, nc = size(A, 1), size(A, 2)
--     na = prod(size(A)[3:end])
--     len = length(xs)
--     nrc = nr * nc
--     if nrc * na != len
--         throw(ArgumentError("argument count $(len) does not match specified shape $(size(A))"))
--     end
--     # putting these in separate functions leads to unnecessary allocations
--     if row_first
--         k = 1
--         for d ∈ 1:na
--             dd = nrc * (d - 1)
--             for i ∈ 1:nr
--                 Ai = dd + i
--                 for _ ∈ 1:nc
--                     @inbounds A[Ai] = xs[k]
--                     k += 1
--                     Ai += nr
--                 end
--             end
--         end
--     else
--         for k ∈ eachindex(xs)
--             @inbounds A[k] = xs[k]
--         end
--     end
-- end
-- /Source
-- Source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- /Source
def emptyHvncatFillRuntime {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref : Type} : NumericArrayRuntime m Empty (EmptyHvncatArray Ty Ref) Empty where
  vector := fun impossible _ => nomatch impossible
  matrix := fun impossible _ _ => nomatch impossible
  size := fun a d => numericFromResult (emptyHvncatArraySize a d)
  shape := fun a => pure a.dimensions
  set := fun _ _ impossible => nomatch impossible
  set2 := fun _ _ _ impossible => nomatch impossible

/-- The source no-value continuation of hvncat_fill! uses the actual
closed numericFill implementation. No fill or store stub is introduced.
In the balanced positive-dimension branch the preceding constructor and
count checks prevent this continuation from being reached. Source:
base/abstractarray.jl:2514-2525,2556-2627. -/
-- Source: base/abstractarray.jl:2514-2525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(::Type{T}, dims::NTuple{N, Int}, row_first::Bool, xs::Number...) where {T, N}
--     all(>(0), dims) ||
--         throw(ArgumentError("`dims` argument must contain positive integers"))
--     A = Array{T, N}(undef, dims...)
--     lengtha = length(A)  # Necessary to store result because throw blocks are being deoptimized right now, which leads to excessive allocations
--     lengthx = length(xs) # Cuts from 3 allocations to 1.
--     if lengtha != lengthx
--        throw(ArgumentError("argument count does not match specified shape (expected $lengtha, got $lengthx)"))
--     end
--     hvncat_fill!(A, row_first, xs)
--     return A
-- end
-- /Source
-- Source: base/abstractarray.jl:2556-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function hvncat_fill!(A::Array, row_first::Bool, xs::Tuple)
--     if @generated
--         N = fieldcount(xs)
--         N > 32 && return :(return _hvncat_fill_loop!(A, row_first, xs))
--         nd = ndims(A)
--         if nd <= 2
--             return quote
--                 nr = size(A, 1)
--                 nc = size(A, 2)
--                 if nr*nc != $N
--                     throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
--                 end
--                 if row_first
--                     i::Int = 1
--                     j::Int = 1
--                     @nexprs $N k -> begin
--                         @inbounds A[i, j] = xs[k]
--                         j += 1
--                         if j > nc
--                             i += 1
--                             j = 1
--                         end
--                     end
--                 else
--                     @nexprs $N k -> begin
--                         @inbounds A[k] = xs[k]
--                     end
--                 end
--                 nothing
--             end
--         else
--             return quote
--                 nr = size(A, 1)
--                 nc = size(A, 2)
--                 nrc = nr * nc
--                 na = prod(size(A)[3:end])
--                 if nrc * na != $N
--                     throw(ArgumentError("argument count $($N) does not match specified shape $(size(A))"))
--                 end
--                 if row_first
--                     d::Int = 1
--                     i::Int = 1
--                     dd::Int = 0
--                     Ai::Int = dd + i
--                     j::Int = 1
--                     @nexprs $N k -> begin
--                         @inbounds A[Ai] = xs[k]
--                         j += 1
--                         Ai += nr
--                         if j > nc
--                             j = 1
--                             i += 1
--                             if i > nr
--                                 i = 1
--                                 d += 1
--                                 dd = nrc * (d - 1)
--                             end
--                             Ai = dd + i
--                         end
--                     end
--                 else
--                     @nexprs $N k -> begin
--                         @inbounds A[k] = xs[k]
--                     end
--                 end
--                 nothing
--             end
--         end
--     else
--         _hvncat_fill_loop!(A, row_first, xs)
--     end
-- end
-- /Source
def emptyHvncatFill {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref : Type} (generated : Bool) (array : EmptyHvncatArray Ty Ref)
    (rowFirst : Bool) : m Unit :=
  numericFill emptyHvncatFillRuntime generated array.dimensions.values.length
    array rowFirst emptyHvncatArguments

/-- Closed ntuple(Returns(0),Val(N)) dependency for native N. The source
Int assertion is a representation invariant; negative lengths retain its
ArgumentError. Both generated and interpreter paths produce exactly N
native zero fields. Nat only describes finite tuple construction. Source:
base/ntuple.jl:65-72. -/
-- Source: base/ntuple.jl:65-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function ntuple(f::F, ::Val{N}) where {F,N}
--     (N::Int >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", N)))
--     if @generated
--         :(@ntuple $N i -> f(i))
--     else
--         Tuple(f(i) for i = 1:(N::Int))
--     end
-- end
-- /Source
def emptyHvncatZeroDimensions (rank : I64) : Result (MachineTuple I64) := do
  if negative : rank.val < 0 then
    throw (.julia (.argumentError
      ("tuple length should be ≥ 0, got " ++ toString rank.val)))
  else
    return ⟨List.replicate rank.val.toNat (int 0), rank, by
      simp only [List.length_replicate]
      exact (Int.toNat_of_nonneg (by omega)).symm⟩

/-- Required no-value Val dispatch: the fixed Val0 method takes priority
and reuses the existing exact source error. Every other native Val uses the
existing empty-Val body with closed comparison, zero-tuple and constructor
dependencies. No value varargs algorithm is substituted. Source:
base/abstractarray.jl:2397,2405-2415. -/
-- Source: base/abstractarray.jl:2397-2397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(::Type, ::Val{0}) = _typed_hvncat_0d_only_one()
-- /Source
-- Source: base/abstractarray.jl:2405-2415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat_0d_only_one() =
--     throw(ArgumentError("a 0-dimensional array may only contain exactly one element"))
--
-- # `@constprop :aggressive` here to form constant `Val(dim)` type to get type stability
-- @constprop :aggressive _typed_hvncat(T::Type, dim::Int, ::Bool, xs...) = _typed_hvncat(T, Val(dim), xs...) # catches from _hvncat type promoters
--
-- function _typed_hvncat(::Type{T}, ::Val{N}) where {T, N}
--     N < 0 &&
--         throw(ArgumentError("concatenation dimension must be non-negative"))
--     return Array{T, N}(undef, ntuple(Returns(0), Val(N)))
-- end
-- /Source
def emptyHvncatVal {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref : Type} (runtime : EmptyHvncatRuntime m Ty Ref)
    (elementType : Ty) (rank : I64) : m (EmptyHvncatArray Ty Ref) :=
  if rank.val == 0 then numericFromResult typedHvncatZeroOnlyOne
  else typedHvncatEmptyVal (fun n => pure (decide (n.val < 0)))
    (fun n => numericFromResult (emptyHvncatZeroDimensions n))
    (fun t _ dimensions => emptyHvncatAllocate runtime t dimensions)
    elementType rank

/-- Close the one-dimensional no-value helper with actual native tuple
length and the real no-value Val continuation. Positive ds still fails the
zero-argument count check; nonpositive ds fails its preceding guard. Source:
base/abstractarray.jl:2501-2512. -/
-- Source: base/abstractarray.jl:2501-2512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat_1d(::Type{T}, ds::Int, ::Val{row_first}, as...) where {T, row_first}
--     lengthas = length(as)
--     ds > 0 ||
--         throw(ArgumentError("`dimsshape` argument must consist of positive integers"))
--     lengthas == ds ||
--         throw(ArgumentError("number of elements does not match `dimshape` argument; expected $ds, got $lengthas"))
--     if row_first
--         return _typed_hvncat(T, Val(2), as...)
--     else
--         return _typed_hvncat(T, Val(1), as...)
--     end
-- end
-- /Source
def emptyHvncatOneDimension {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref : Type} (runtime : EmptyHvncatRuntime m Ty Ref)
    (elementType : Ty) (dimension : I64) (rowFirst : Bool) : m (EmptyHvncatArray Ty Ref) :=
  typedHvncatOneDim (fun xs => pure xs.count)
    (fun t rank _ => emptyHvncatVal runtime t rank)
    elementType dimension rowFirst emptyHvncatArguments

/-- Closed no-value balanced native dimensions composition. Array
allocation captures the original MachineTuple because the frozen mirror
passes exactly its values and length; this preserves the representation
proof rather than constructing an unrestricted list-shaped Array. Native
length is closed, and the actual numeric fill remains the continuation.
Positive dimensions and successful native construction make that
continuation unreachable without an allocator correctness assumption.
Source: base/abstractarray.jl:2514-2525. -/
-- Source: base/abstractarray.jl:2514-2525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(::Type{T}, dims::NTuple{N, Int}, row_first::Bool, xs::Number...) where {T, N}
--     all(>(0), dims) ||
--         throw(ArgumentError("`dims` argument must contain positive integers"))
--     A = Array{T, N}(undef, dims...)
--     lengtha = length(A)  # Necessary to store result because throw blocks are being deoptimized right now, which leads to excessive allocations
--     lengthx = length(xs) # Cuts from 3 allocations to 1.
--     if lengtha != lengthx
--        throw(ArgumentError("argument count does not match specified shape (expected $lengtha, got $lengthx)"))
--     end
--     hvncat_fill!(A, row_first, xs)
--     return A
-- end
-- /Source
def emptyHvncatNativeDimensions {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref : Type} (runtime : EmptyHvncatRuntime m Ty Ref) (generated : Bool)
    (elementType : Ty) (dimensions : MachineTuple I64) (rowFirst : Bool) :
    m (EmptyHvncatArray Ty Ref) :=
  typedHvncatNumbersDims
    (fun t _ _ => emptyHvncatAllocate runtime t dimensions)
    (fun a => pure (emptyHvncatArrayLength a)) (fun xs => pure xs.count)
    (fun a first _ => emptyHvncatFill generated a first)
    elementType dimensions.values rowFirst emptyHvncatArguments

/-- Full arbitrary-inner-tuple specialization of the one-level method.
It retains the source's first length check and subsequent first-field read.
Non-native first members fail dispatch to _typed_hvncat_1d; later arbitrary
members are never inspected. The existing one-level frozen model restricts
all inner fields to I64, so it cannot represent this required domain.
Source: base/abstractarray.jl:2732-2736. -/
-- Source: base/abstractarray.jl:2732-2736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(T::Type, shape::Tuple{Tuple}, row_first::Bool, xs...)
--     length(shape[1]) > 0 ||
--         throw(ArgumentError("each level of `shape` argument must have at least one value"))
--     return _typed_hvncat_1d(T, shape[1][1], Val(row_first), xs...)
-- end
-- /Source
def emptyHvncatOneLevel {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref : Type} (runtime : EmptyHvncatRuntime m Ty Ref)
    (elementType : Ty) (inner : MachineTuple EmptyHvncatInnerValue) (rowFirst : Bool) :
    m (EmptyHvncatArray Ty Ref) := do
  let shape : List (MachineTuple EmptyHvncatInnerValue) := [inner]
  let firstLevel ← numericFromResult (tupleGet shape (int 1))
  if firstLevel.count.val ≤ 0 then
    throw (.julia (.argumentError "each level of `shape` argument must have at least one value"))
  let firstLevel ← numericFromResult (tupleGet shape (int 1))
  let first ← numericFromResult (tupleGet firstLevel.values (int 1))
  match first with
  | .nativeInt dimension => emptyHvncatOneDimension runtime elementType dimension rowFirst
  | .other => throw (.julia (.methodError "_typed_hvncat_1d"))

/-- Required maximum over the empty argument generator. mapreduce and
mapfoldl unwrap its generators to the empty Tuple; no cat_ndims call occurs.
The empty reduction's result type is Empty because its only outcome is the
source ArgumentError, not a default element or a fabricated callback result.
It uses the standard empty-Tuple error, not the unknown-element-type error.
Source: base/abstractarray.jl:2740; base/reduce.jl:40-67,146-155,173,306,
318-322,358-359,382-392,718; base/operators.jl:622. -/
-- Source: base/abstractarray.jl:2740-2740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     nd = max(maximum(cat_ndims(a) for a ∈ as), N)
-- /Source
-- Source: base/reduce.jl:40-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function mapfoldl_impl(f::F, op::OP, nt, itr) where {F,OP}
--     op′, itr′ = _xfadjoint(BottomRF(op), Generator(f, itr))
--     return foldl_impl(op′, nt, itr′)
-- end
--
-- function foldl_impl(op::OP, nt, itr) where {OP}
--     v = _foldl_impl(op, nt, itr)
--     v isa _InitialValue && return reduce_empty_iter(op, itr)
--     return v
-- end
--
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
--
-- function _foldl_impl(op, init, itr::Union{Tuple,NamedTuple})
--     length(itr) <= 32 && return afoldl(op, init, itr...)
--     @invoke _foldl_impl(op, init, itr::Any)
-- /Source
-- Source: base/reduce.jl:146-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _xfadjoint(op, itr)
--     itr′, wrap = _xfadjoint_unwrap(itr)
--     wrap(op), itr′
-- end
--
-- _xfadjoint_unwrap(itr) = itr, identity
-- function _xfadjoint_unwrap(itr::Generator)
--     itr′, wrap = _xfadjoint_unwrap(itr.iter)
--     itr.f === identity && return itr′, wrap
--     return itr′, wrap ∘ Fix1(MappingRF, itr.f)
-- /Source
-- Source: base/reduce.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapfoldl(f, op, itr; init=_InitialValue()) = mapfoldl_impl(f, op, init, itr)
-- /Source
-- Source: base/reduce.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce(f, op, itr; kw...) = mapfoldl(f, op, itr; kw...)
-- /Source
-- Source: base/reduce.jl:318-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _empty_reduce_error() = throw(ArgumentError("reducing over an empty collection is not allowed; consider supplying `init` to the reducer"))
-- reduce_empty(f, T) = _empty_reduce_error()
-- mapreduce_empty(f, op, T) = _empty_reduce_error()
-- reduce_empty(f, ::Type{Union{}}, splat...) = _empty_reduce_error()
-- mapreduce_empty(f, op, ::Type{Union{}}, splat...) = _empty_reduce_error()
-- /Source
-- Source: base/reduce.jl:358-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(op::BottomRF, ::Type{T}) where {T} = reduce_empty(op.rf, T)
-- reduce_empty(op::MappingRF, ::Type{T}) where {T} = mapreduce_empty(op.f, op.rf, T)
-- /Source
-- Source: base/reduce.jl:382-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline reduce_empty_iter(op, itr) = reduce_empty_iter(op, itr, IteratorEltype(itr))
-- @inline reduce_empty_iter(op::FlatteningRF, itr) = reduce_empty_iter(op.rf, Iterators.flatten(itr))
-- @inline reduce_empty_iter(op, itr, ::HasEltype) = reduce_empty(op, eltype(itr))
-- # a homogeneous tuple binds the element type as a static parameter, which stays
-- # precise for abstract `Tuple{Vararg{T}}` queries where `eltype` of the
-- # `@nospecialize`d tuple type does not (#61323). `T` is undefined only for the
-- # empty tuple (vacuous `Vararg` match), whose eltype is `Union{}`; the
-- # `@isdefined` guard keeps this method's intentional unbound sparam (see the
-- # `detect_unbound_args` allow-list in test/ambiguous.jl), like `_eltype_ntuple`.
-- @inline reduce_empty_iter(op, itr::Tuple{Vararg{T}}, ::HasEltype) where {T} =
--     reduce_empty(op, @isdefined(T) ? T : Union{})
-- /Source
-- Source: base/reduce.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- maximum(a; kw...) = mapreduce(identity, max, a; kw...)
-- /Source
-- Source: base/operators.jl:622-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- afoldl(op, a) = a
-- /Source
def emptyHvncatMaximum : Result Empty :=
  .error (.julia (.argumentError
    "reducing over an empty collection is not allowed; consider supplying `init` to the reducer"))

/-- No-value specialization of the many-level tuple path. The actual
empty maximum always throws before max, shape[end], repetition or recursive
concatenation. Eliminating its Empty result makes that source-unreachable
tail explicit; no fake callee callback is required. Arbitrary inner tuple
contents are unobserved. Source: base/abstractarray.jl:2738-2742. -/
-- Source: base/abstractarray.jl:2738-2742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(T::Type, shape::NTuple{N, Tuple}, row_first::Bool, as...) where {N}
--     # function barrier after calculating the max is necessary for high performance
--     nd = max(maximum(cat_ndims(a) for a ∈ as), N)
--     return _typed_hvncat_shape(T, (shape..., ntuple(Returns(shape[end]), nd - N)...), row_first, as)
-- end
-- /Source
def emptyHvncatManyLevels {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A : Type} : m A := do
  let impossible ← numericFromResult emptyHvncatMaximum
  nomatch impossible

/-- Concrete dispatch classifier for the native-Int tuple family. It
retains the exact number of fields and each native value. Non-native values
produce none, never a default dimension. This is finite tuple type
classification, not an extensible dispatch callback. Source:
base/abstractarray.jl:2514. -/
-- Source: base/abstractarray.jl:2514-2514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(::Type{T}, dims::NTuple{N, Int}, row_first::Bool, xs::Number...) where {T, N}
-- /Source
def emptyHvncatNativeFields : (fields : List EmptyHvncatMember) →
    Option { dimensions : List I64 // dimensions.length = fields.length }
  | [] => some ⟨[], rfl⟩
  | .nativeInt dimension :: rest => do
      let tail ← emptyHvncatNativeFields rest
      return ⟨dimension :: tail.val, by simp only [List.length_cons, tail.property]⟩
  | _ :: _ => none

/-- The concrete complete no-value _typed_hvncat dispatcher needed only
by assigned source2384. The explicit empty/singleton intersection overloads
take precedence, then native-Int tuples choose the vacuously applicable
Number-varargs method, all-Tuple shapes choose their shape method, and every
other tuple receives MethodError. Arbitrary inner values remain represented.
Source: base/abstractarray.jl:2397,2409,2492-2499,2514,2732,2738. -/
-- Source: base/abstractarray.jl:2397-2397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(::Type, ::Val{0}) = _typed_hvncat_0d_only_one()
-- /Source
-- Source: base/abstractarray.jl:2409-2409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @constprop :aggressive _typed_hvncat(T::Type, dim::Int, ::Bool, xs...) = _typed_hvncat(T, Val(dim), xs...) # catches from _hvncat type promoters
-- /Source
-- Source: base/abstractarray.jl:2492-2499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(T::Type, ::Tuple{}, ::Bool, x...) = _typed_hvncat(T, Val(0), x...)
-- _typed_hvncat(T::Type, ::Tuple{}, ::Bool, x::Number...) = _typed_hvncat(T, Val(0), x...)
--
--
-- # balanced dimensions hvncat methods
--
-- _typed_hvncat(T::Type, dims::Tuple{Int}, ::Bool, as...) = _typed_hvncat_1d(T, dims[1], Val(false), as...)
-- _typed_hvncat(T::Type, dims::Tuple{Int}, ::Bool, as::Number...) = _typed_hvncat_1d(T, dims[1], Val(false), as...)
-- /Source
-- Source: base/abstractarray.jl:2514-2514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(::Type{T}, dims::NTuple{N, Int}, row_first::Bool, xs::Number...) where {T, N}
-- /Source
-- Source: base/abstractarray.jl:2732-2732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(T::Type, shape::Tuple{Tuple}, row_first::Bool, xs...)
-- /Source
-- Source: base/abstractarray.jl:2738-2738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(T::Type, shape::NTuple{N, Tuple}, row_first::Bool, as...) where {N}
-- /Source
def emptyHvncatTyped {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref : Type} (runtime : EmptyHvncatRuntime m Ty Ref) (generated : Bool)
    (elementType : Ty) (dimensions : EmptyHvncatDimensions) (rowFirst : Bool) :
    m (EmptyHvncatArray Ty Ref) := do
  match dimensions with
  | .nativeInt rank =>
      typedHvncatDimFlag (fun t n (_ : MachineTuple Empty) => emptyHvncatVal runtime t n)
        elementType rank rowFirst emptyHvncatArguments
  | .tuple fields =>
      match fields.values with
      | [] =>
          typedHvncatEmptyShapeNumbers
            (fun t n (_ : MachineTuple Empty) => emptyHvncatVal runtime t n)
            elementType rowFirst emptyHvncatArguments
      | [.nativeInt dimension] =>
          typedHvncatOneShapeNumbers (fun ds i => numericFromResult (tupleGet ds i))
            (fun t d first (_ : MachineTuple Empty) =>
              emptyHvncatOneDimension runtime t d first)
            elementType [dimension] rowFirst emptyHvncatArguments
      | [.tuple inner] => emptyHvncatOneLevel runtime elementType inner rowFirst
      | _ =>
          match emptyHvncatNativeFields fields.values with
          | some native =>
              let machine : MachineTuple I64 := ⟨native.val, fields.count, by
                rw [native.property]
                exact fields.count_eq⟩
              emptyHvncatNativeDimensions runtime generated elementType machine rowFirst
          | none =>
              if fields.values.all (fun field => match field with
                  | .tuple _ => true | _ => false) then
                emptyHvncatManyLevels
              else throw (.julia (.methodError "_typed_hvncat"))

/-- The assigned empty _hvncat method, composed with the complete
closed no-value dispatcher. Any is a selected type token at the existing
raw-memory boundary, not a promotion operation. Every native Int and every
machine-sized Tuple of arbitrary values is represented. Effects and errors
of raw allocation are preserved; all dimension metadata and dispatch are
computed by the model. This does not model the nonempty public overloads.
Source: base/abstractarray.jl:2384. -/
-- Source: base/abstractarray.jl:2384-2384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool) = _typed_hvncat(Any, dimsshape, row_first)
-- /Source
def emptyHvncat {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty Ref : Type} (runtime : EmptyHvncatRuntime m Ty Ref) (generated : Bool)
    (anyType : Ty) (dimensions : EmptyHvncatDimensions) (rowFirst : Bool) :
    m (EmptyHvncatArray Ty Ref) :=
  hvncatEmpty (emptyHvncatTyped runtime generated) anyType dimensions rowFirst

end JuliaLean.base.abstractarray.Models1Group3



namespace JuliaLean.base.abstractarray.Models2Group6

open JuliaLean
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion)

/-- The existing array exception classes plus the runtime exception from an
unbound static parameter. World age is a Julia UInt. The existing
MonadExceptOf interface carries this local extension; canonical ArrayError
and JlError remain unchanged. Symbols are represented by their exact names.
Julia source: base/abstractarray.jl:279; base/boot.jl:500-506.
-/
-- Source: base/boot.jl:500-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UndefVarError <: Exception
--     var::Symbol
--     world::UInt
--     scope # a Module or Symbol or other object describing the context where this variable was looked for (e.g. Main or :local or :static_parameter)
--     UndefVarError(var::Symbol) = new(var, ccall(:jl_get_tls_world_age, UInt, ()))
--     UndefVarError(var::Symbol, @nospecialize scope) = new(var, ccall(:jl_get_tls_world_age, UInt, ()), scope)
-- end
-- /Source
inductive StaticRankError where
  | array (error : ArrayError)
  | undefVarError (varName : String) (world : JInt .u64) (scope : String)

/-- Read the selected static N binding before asserting native Int. The
binding is entry representation metadata, as in the installed eltypeArray
model: none denotes an unbound static parameter and differs from every bound
value. Other ranges over all Julia-admissible non-Int parameter values. Every
native Int64 rank is admitted, including negative ranks and both extrema.
The array type argument follows the original model's Type-token convention;
the source does not inspect it. The UInt world age is ambient runtime metadata
captured by an unbound-static-parameter exception. The installed assertion and
native-rank model are reused after the static read succeeds.
Julia source: base/abstractarray.jl:279.
-/
-- Source: base/abstractarray.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ndims(::Type{<:AbstractArray{<:Any,N}}) where {N} = N::Int
-- /Source
def ndimsType {m : Type → Type} [Monad m] [MonadExceptOf StaticRankError m]
    {Other : Type} (world : JInt .u64)
    (rankBinding : Option (TypeAssertion I64 Other)) (arrayType : Type) : m I64 := do
  let rank ← match rankBinding with
    | none => throw (.undefVarError "N" world "static_parameter")
    | some rank => pure rank
  let native ← match (Models1Group1.assertType rank : Result I64) with
    | .ok native => pure native
    | .error error => throw (.array error)
  pure (JuliaLean.base.abstractarray.ndimsType native arrayType)

end JuliaLean.base.abstractarray.Models2Group6

namespace JuliaLean.base.abstractarray.Models2Group6

open JuliaLean
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Runtime value payloads in base/abstractarray.jl:597-607. The left
branch is an actual Julia Int64; the right branch retains every other selected
Julia value and its runtime type, including wider/custom integers and arbitrary yielded indices. Promotion
can change the branch after each operation. No conversion is implicit. -/
-- Source: base/abstractarray.jl:597-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function stride(A::AbstractArray, k::Integer)
--     st = strides(A)
--     k ≤ ndims(A) && return st[k]
--     ndims(A) == 0 && return 1
--     sz = size(A)
--     s = st[1] * sz[1]
--     for i in 2:ndims(A)
--         s += st[i] * sz[i]
--     end
--     return s
-- end
-- /Source
abbrev RuntimeValue (Other : Type) := Sum I64 Other

/-- Open dispatch selected by the operands of base/abstractarray.jl:597-607.
K denotes any Julia Integer admitted by the signature. Rank, metadata and
iteration payloads retain their selected Julia types; in particular the
source imposes no Int assertion on ndims(A), strides(A), size(A), or products.
Each field is one selected call, not a callback for the loop or stride body.
Comparison results retain non-Bool values for the source condition assertion.
The source's ForIn boundary supplies Julia's language-level loop protocol;
its adapter can preserve custom iteration state, exceptions and divergence.
-/
-- Source: base/abstractarray.jl:597-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function stride(A::AbstractArray, k::Integer)
--     st = strides(A)
--     k ≤ ndims(A) && return st[k]
--     ndims(A) == 0 && return 1
--     sz = size(A)
--     s = st[1] * sz[1]
--     for i in 2:ndims(A)
--         s += st[i] * sz[i]
--     end
--     return s
-- end
-- /Source
structure StrideOps (m : Type → Type)
    (A K Rank Strides Sizes Range Index Other NotBool : Type) where
  strides : A → m Strides
  ndims : A → m Rank
  lessEqual : K → Rank → m (TypeAssertion Bool NotBool)
  getRequested : Strides → K → m (RuntimeValue Other)
  equalZero : Rank → I64 → m (TypeAssertion Bool NotBool)
  size : A → m Sizes
  getStride : Strides → RuntimeValue Index → m (RuntimeValue Other)
  getSize : Sizes → RuntimeValue Index → m (RuntimeValue Other)
  multiply : RuntimeValue Other → RuntimeValue Other → m (RuntimeValue Other)
  add : RuntimeValue Other → RuntimeValue Other → m (RuntimeValue Other)
  colon : I64 → Rank → m Range

/-- Full source body of stride at base/abstractarray.jl:597-607, with open
callee dispatch at the installed array-interface boundary. It observes rank
again at each source occurrence, including after the first product. Generic
indexing/arithmetic preserve original payloads, intermediate types, errors and
state effects. The loop is explicit and retains the source SUM of products;
it is not changed into a trailing-dimension product. Only source literals are
native Int64. ForIn is the existing language-level iteration boundary, not a
supplied stride, reduction, or source-recursion callback.
-/
-- Source: base/abstractarray.jl:597-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function stride(A::AbstractArray, k::Integer)
--     st = strides(A)
--     k ≤ ndims(A) && return st[k]
--     ndims(A) == 0 && return 1
--     sz = size(A)
--     s = st[1] * sz[1]
--     for i in 2:ndims(A)
--         s += st[i] * sz[i]
--     end
--     return s
-- end
-- /Source
def stride {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A K Rank Strides Sizes Range Index Other NotBool : Type}
    [ForIn m Range (RuntimeValue Index)]
    (ops : StrideOps m A K Rank Strides Sizes Range Index Other NotBool)
    (array : A) (requested : K) : m (RuntimeValue Other) := do
  let st ← ops.strides array
  let firstRank ← ops.ndims array
  if ← assertType (← ops.lessEqual requested firstRank) then
    return ← ops.getRequested st requested
  let secondRank ← ops.ndims array
  if ← assertType (← ops.equalZero secondRank (int 0)) then
    return .inl (int 1)
  let sz ← ops.size array
  let firstStride ← ops.getStride st (.inl (int 1))
  let firstSize ← ops.getSize sz (.inl (int 1))
  let mut accumulator ← ops.multiply firstStride firstSize
  let thirdRank ← ops.ndims array
  let indices ← ops.colon (int 2) thirdRank
  for index in indices do
    let strideValue ← ops.getStride st index
    let sizeValue ← ops.getSize sz index
    let product ← ops.multiply strideValue sizeValue
    accumulator ← ops.add accumulator product
  return accumulator

end JuliaLean.base.abstractarray.Models2Group6

namespace JuliaLean.base.abstractarray.Models2Group6

open JuliaLean
open JuliaLean.base.abstractarray.Models1Group1 (Tuple)

/-- The selected calls in base/abstractarray.jl:619-625. The method fixes
neither A nor n, so rank, range, index and size values retain their actual
runtime types. Each field denotes one dispatch-selected call. RuntimeValue
retains the native initial accumulator and every type-changing product.
ForIn is the already installed language-level loop interface; the source
loop and its accumulator update are explicit in trailingSize below. -/
-- Source: base/abstractarray.jl:619-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function trailingsize(A, n)
--     s = 1
--     for i=n:ndims(A)
--         s *= size(A,i)
--     end
--     return s
-- end
-- /Source
structure TrailingSizeOps (m : Type → Type)
    (A Start Rank Range Index Other : Type) where
  ndims : A → m Rank
  colon : Start → Rank → m Range
  size : A → RuntimeValue Index → m (RuntimeValue Other)
  multiply : RuntimeValue Other → RuntimeValue Other → m (RuntimeValue Other)

/-- Full body of base/abstractarray.jl:619-625. Native Int one is established
before the selected rank and colon calls. Each yielded index is passed
unchanged to size; each selected product becomes the next accumulator.
No size, requested start, yielded index or product is narrowed to native Int.
The effect monad preserves selected-call errors and all earlier mutations.
There is no supplied trailing-size, fold, or recursive-loop callback. -/
-- Source: base/abstractarray.jl:619-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function trailingsize(A, n)
--     s = 1
--     for i=n:ndims(A)
--         s *= size(A,i)
--     end
--     return s
-- end
-- /Source
def trailingSize {m : Type → Type} [Monad m]
    {A Start Rank Range Index Other : Type}
    [ForIn m Range (RuntimeValue Index)]
    (ops : TrailingSizeOps m A Start Rank Range Index Other)
    (array : A) (start : Start) : m (RuntimeValue Other) := do
  let mut accumulator : RuntimeValue Other := .inl (int 1)
  let rank ← ops.ndims array
  let indices ← ops.colon start rank
  for index in indices do
    let size ← ops.size array index
    accumulator ← ops.multiply accumulator size
  return accumulator

/-- The concrete Tuple length dependency of base/abstractarray.jl:626-632.
The existing Tuple representation bounds its field count by typemax(Int),
so the native nfields read is exact. Nat counts representation fields only;
the result passed to Julia colon is an actual JInt.i64, not a Lean Nat.
Julia source: base/tuple.jl:28. -/
-- Source: base/tuple.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(@nospecialize t::Tuple) = nfields(t)
-- /Source
def tupleFieldCount {Value : Type} (tuple : Tuple Value) : I64 :=
  int (tuple.values.length : Int)

/-- Dispatch leaves in base/abstractarray.jl:626-632. Axis represents the
actual AbstractUnitRange members of Indices. A yielded index has an open
runtime type, so its getindex dispatch and even the returned value's type are
retained explicitly; Got is not assumed to be one Axis. The concrete native
tuple length is implemented by tupleFieldCount and is never a callback.
Selected length and multiplication preserve wide/custom numeric values,
exceptions, and state effects with no callee-correctness law. -/
-- Source: base/abstractarray.jl:626-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function trailingsize(inds::Indices, n)
--     s = 1
--     for i=n:length(inds)
--         s *= length(inds[i])
--     end
--     return s
-- end
-- /Source
structure TrailingIndicesOps (m : Type → Type)
    (Axis Start Range Index Got Other : Type) where
  colon : Start → I64 → m Range
  getindex : Tuple Axis → RuntimeValue Index → m Got
  length : Got → m (RuntimeValue Other)
  multiply : RuntimeValue Other → RuntimeValue Other → m (RuntimeValue Other)

/-- Full Indices overload at base/abstractarray.jl:626-632. The argument
tuple has a constructible native arity; its original members and every
selected index are retained. Indexing precedes length, which precedes the
type-changing multiplication at each iteration. Empty iteration returns the
source literal Int one. The generic n parameter has no added Integer or
native-Int restriction. No range or product is precomputed mathematically. -/
-- Source: base/abstractarray.jl:626-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function trailingsize(inds::Indices, n)
--     s = 1
--     for i=n:length(inds)
--         s *= length(inds[i])
--     end
--     return s
-- end
-- /Source
def trailingSizeIndices {m : Type → Type} [Monad m]
    {Axis Start Range Index Got Other : Type}
    [ForIn m Range (RuntimeValue Index)]
    (ops : TrailingIndicesOps m Axis Start Range Index Got Other)
    (indices : Tuple Axis) (start : Start) : m (RuntimeValue Other) := do
  let mut accumulator : RuntimeValue Other := .inl (int 1)
  let range ← ops.colon start (tupleFieldCount indices)
  for index in range do
    let item ← ops.getindex indices index
    let length ← ops.length item
    accumulator ← ops.multiply accumulator length
  return accumulator

end JuliaLean.base.abstractarray.Models2Group6

namespace JuliaLean.base.abstractarray.Models2Group6.BoundsNil

open JuliaLean JuliaLean.base.abstractarray
open JuliaLean.base.abstractarray.Models1Group1 (Tuple TypeAssertion assertType)

/-- The possible normal results of tuple all. Missing is a distinct Julia
singleton, not an exception or a false Boolean.
Julia source: base/abstractarray.jl:728; base/anyall.jl:257.
-/
-- Source: base/anyall.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
-- /Source
inductive AllValue where
  | boolean (value : Bool)
  | missing
  deriving DecidableEq, Repr

/-- Actual runtime Bool-membership metadata for a comparison or ismissing
result. Other includes every non-Bool Julia value, including Missing. It is
not restricted to integers, ranges, or values obeying an interface law.
Julia source: base/abstractarray.jl:728; base/anyall.jl:245-257.
-/
-- Source: base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
abbrev Predicate (Other : Type) := TypeAssertion Bool Other

/-- Open selected dispatch at the exact call sites used by the omitted-index
predicate and tuple all. Length retains its Julia runtime type; no native
conversion is inserted. Equality receives native Int one. isMissing can
select custom methods on the actual comparison result, so its effects,
exceptions and even a non-Bool return are preserved. Both result membership
tags are the installed TypeAssertion runtime representation.
Julia source: base/abstractarray.jl:728; base/anyall.jl:245-257.
-/
-- Source: base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
-- Source: base/anyall.jl:245-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _all_tuple(f, anymissing::Bool, x, rest...)
--     v = f(x)
--     if ismissing(v)
--         anymissing = true
--     # this syntax allows throwing a TypeError for non-Bool, for consistency with any
--     elseif v
--         nothing
--     else
--         return false
--     end
--     return _all_tuple(f, anymissing, rest...)
-- end
-- @inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
-- /Source
structure Ops (m : Type → Type) (Axis Length Other : Type) where
  length : Axis → m Length
  equal : Length → I64 → m (Predicate Other)
  isMissing : Predicate Other → m (Predicate Other)

/-- The concrete terminal _all_tuple method, needed by the actual recursive
callee. It returns Julia Missing iff a prior predicate was recognized as
missing. Julia source: base/anyall.jl:257.
-/
-- Source: base/anyall.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
-- /Source
def allTupleDone (anyMissing : Bool) : AllValue :=
  if anyMissing then .missing else .boolean true

/-- Close _all_tuple's real recursion. Every call first evaluates f, then
selected ismissing, then its Bool condition. A false missing test checks the
original predicate value in Bool context; it is not converted to Bool.
A true missing test continues even if that original value is another type.
Effects and the earliest exception are retained in m.

The internal list represents the remaining fields of the bounded tuple
passed to allTuple below. It is not an allocated or unbounded Julia array.
Julia source: base/anyall.jl:245-257.
-/
-- Source: base/anyall.jl:245-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _all_tuple(f, anymissing::Bool, x, rest...)
--     v = f(x)
--     if ismissing(v)
--         anymissing = true
--     # this syntax allows throwing a TypeError for non-Bool, for consistency with any
--     elseif v
--         nothing
--     else
--         return false
--     end
--     return _all_tuple(f, anymissing, rest...)
-- end
-- @inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
-- /Source
def allTupleRecursive {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Axis Other : Type} (isMissing : Predicate Other → m (Predicate Other))
    (predicate : Axis → m (Predicate Other)) (anyMissing : Bool) :
    List Axis → m AllValue
  | [] => pure (allTupleDone anyMissing)
  | x :: rest => do
      let value ← predicate x
      let missing ← assertType (← isMissing value)
      if missing then
        allTupleRecursive isMissing predicate true rest
      else
        let condition ← assertType value
        if condition then
          allTupleRecursive isMissing predicate anyMissing rest
        else
          pure (.boolean false)

/-- The actual tuple _all loop. The anonymous length/equality function used
by row728 is not identity, so the distinct identity/Bool optimization at
anyall.jl:224 does not apply. Tuple field traversal is closed List iteration:
it follows the immutable field order from tuple.jl:69-73. There are no
selected iterator or loop-result callbacks. The native tuple's final iterator
state, including a wrapping increment at the largest representable arity,
is outside the 1:length guard and stops; structural traversal has the same
field schedule without exposing that otherwise unused state.

The explicit Boolean checks preserve ismissing and original-predicate
TypeError locations. Earlier effects survive failures. Internal fields are
always supplied by the bounded allTuple entry below.
Julia source: base/anyall.jl:204-220; base/tuple.jl:69-73.
-/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
-- Source: base/anyall.jl:204-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for ItrT = (Tuple,Any)
--     # define a generic method and a specialized version for `Tuple`,
--     # whose method bodies are identical, while giving better effects to the later
--     @eval function _all(f, itr::$ItrT, ::Colon)
--         $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
--         anymissing = false
--         for x in itr
--             v = f(x)
--             if ismissing(v)
--                 anymissing = true
--             else
--                 v || return false
--             end
--         end
--         return anymissing ? missing : true
--     end
-- end
-- /Source
def allTupleLoop {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Axis Other : Type} (isMissing : Predicate Other → m (Predicate Other))
    (predicate : Axis → m (Predicate Other)) (fields : List Axis) : m AllValue := do
  let mut anyMissing := false
  for x in fields do
    let value ← predicate x
    let missing ← assertType (← isMissing value)
    if missing then
      anyMissing := true
    else
      let condition ← assertType value
      if !condition then return .boolean false
  return if anyMissing then .missing else .boolean true

/-- Concrete all(f,Tuple) dispatch, retaining the NTuple-first short circuit
and native length comparison. isNTuple is the actual runtime tuple-type test,
not a predicate-correctness flag. Axis may itself be a tagged heterogeneous
runtime carrier. The installed Tuple bound makes the Int length constructible.
Both selected algorithms are implemented above, rather than supplied by the
caller. Julia source: base/anyall.jl:238-243.
-/
-- Source: base/anyall.jl:238-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function all(f, itr::Tuple)
--     if itr isa NTuple || length(itr) > 32
--         return _all(f, itr, :)
--     end
--     _all_tuple(f, false, itr...)
-- end
-- /Source
def allTuple {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Axis Other : Type} (isMissing : Predicate Other → m (Predicate Other))
    (predicate : Axis → m (Predicate Other)) (isNTuple : Bool)
    (fields : Tuple Axis) : m AllValue := do
  if isNTuple then
    allTupleLoop isMissing predicate fields.values
  else
    let count : I64 := int fields.values.length
    if (int 32).val < count.val then
      allTupleLoop isMissing predicate fields.values
    else
      allTupleRecursive isMissing predicate false fields.values

/-- Full omitted-index-tuple body over every constructible tuple, including
arbitrary non-range elements and non-native/custom length values. It constructs
the actual length-equality predicate and invokes the closed tuple-all callee.
Missing results and condition TypeErrors are retained, without a Bool return
assertion absent from this source. The three dispatch leaves are unconstrained
and retain their state, errors and possible divergence through m.
Julia source: base/abstractarray.jl:728.
-/
-- Source: base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
def checkboundsIndicesNil {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Axis Length Other : Type} (ops : Ops m Axis Length Other)
    (isNTuple : Bool) (inds : Tuple Axis) : m AllValue :=
  allTuple ops.isMissing
    (fun axis => do
      let count ← ops.length axis
      ops.equal count (int 1)) isNTuple inds

end JuliaLean.base.abstractarray.Models2Group6.BoundsNil

namespace JuliaLean.base.abstractarray.Models2Group6

open JuliaLean
open JuliaLean.base.abstractarray.Models1Group1 (Tuple)

/-- Global Julia bounds-check policy, retained rather than overridden by a source
`@inbounds` annotation. `always`, `never`, `automatic` denote
`--check-bounds=yes`, `no`, `auto`, respectively.
Representation for base/abstractarray.jl:1371,1469-1473;
doc/src/devdocs/boundscheck.md:123-126. No compiler policy is reimplemented. -/
-- Source: base/abstractarray.jl:1371-1371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline unsafe_getindex(A::AbstractArray, I...) = @inbounds getindex(A, I...)
-- /Source
inductive UnsafeCheckBounds where
  | always
  | never
  | automatic
  deriving DecidableEq, Repr

/-- The source annotation at the selected array call. This is a context request,
not a statement that every check in the callee has been removed.
Representation for base/abstractarray.jl:1371,1469-1473;
base/essentials.jl:981-988 and doc/src/devdocs/boundscheck.md:13-37,72-79. -/
-- Source: base/abstractarray.jl:1371-1371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline unsafe_getindex(A::AbstractArray, I...) = @inbounds getindex(A, I...)
-- /Source
inductive UnsafeBoundsAnnotation where
  | inherited
  | inbounds
  deriving DecidableEq, Repr

/-- The unchanged global policy and arbitrary incoming compiler/caller context.
`Caller` can retain inlining decisions, incoming bounds scopes and propagation
metadata; it is not restricted to one Boolean. This is metadata at the existing
selected-call interface, not a new Julia value or an array representation.
Representation for base/abstractarray.jl:1371,1469-1473. -/
-- Source: base/abstractarray.jl:1371-1371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline unsafe_getindex(A::AbstractArray, I...) = @inbounds getindex(A, I...)
-- /Source
structure UnsafeAmbientContext (Caller : Type) where
  checkBounds : UnsafeCheckBounds
  caller : Caller

/-- The source call's lexical `@inbounds` scope and wrapper `@inline` hint,
together with the unchanged ambient context. The selected leaf observes this
request and the global policy; no unconditional check-elision assumption is
made. Inlining and propagation within arbitrary selected user code are not this
wrapper's body. This is compiler metadata, not an extra Julia call argument.
Representation for base/abstractarray.jl:1371,1469-1473. -/
-- Source: base/abstractarray.jl:1371-1371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline unsafe_getindex(A::AbstractArray, I...) = @inbounds getindex(A, I...)
-- /Source
structure UnsafeIndexRequest (Caller : Type) where
  ambient : UnsafeAmbientContext Caller
  annotation : UnsafeBoundsAnnotation
  wrapperInlineHint : Bool

/-- Genuine selected `getindex` dispatch for an AbstractArray and its complete
index tuple, including its bounds context. `Index` is a carrier for arbitrary,
possibly heterogeneous Julia index values, not a restriction to scalar/native
indices. `m` retains effects, exceptions and nonreturning selected behavior.
No concrete storage type is fixed by base/abstractarray.jl:1371. -/
-- Source: base/abstractarray.jl:1371-1371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline unsafe_getindex(A::AbstractArray, I...) = @inbounds getindex(A, I...)
-- /Source
structure UnsafeReadOps (m : Type → Type) (Caller A Index R : Type) where
  getindex : UnsafeIndexRequest Caller → A → Tuple Index → m R

/-- Genuine selected `setindex!` dispatch, preserving its distinct argument-value
and returned-value domains. The selected call can share and mutate arbitrary
storage through `m`. No callee-correctness law is required.
No concrete storage type is fixed by base/abstractarray.jl:1469-1473. -/
-- Source: base/abstractarray.jl:1469-1473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_setindex!(A::AbstractArray, v, I...)
--     @inline
--     @inbounds r = setindex!(A, v, I...)
--     r
-- end
-- /Source
structure UnsafeWriteOps (m : Type → Type) (Caller A V Index R : Type) where
  setindex : UnsafeIndexRequest Caller → A → V → Tuple Index → m R

/-- Source-mirrored unsafe reader at base/abstractarray.jl:1371. The ordinary
getindex dispatch is called once with the original array and native-arity tuple
under the source's explicit `@inbounds` request. Global check-bounds policy and
incoming caller metadata are retained. `@inline` remains a hint, not an assumed
compiler outcome. Neither bounds success nor memory safety is assumed.
Julia documentation: doc/src/devdocs/boundscheck.md:13-37,72-79,123-126. -/
-- Source: base/abstractarray.jl:1371-1371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline unsafe_getindex(A::AbstractArray, I...) = @inbounds getindex(A, I...)
-- /Source
def unsafeGetindexContext {m : Type → Type} [Monad m]
    {Caller A Index R : Type} (ops : UnsafeReadOps m Caller A Index R)
    (ambient : UnsafeAmbientContext Caller) (a : A) (indices : Tuple Index) : m R :=
  ops.getindex
    { ambient := ambient, annotation := .inbounds, wrapperInlineHint := true }
    a indices

/-- Source-mirrored unsafe writer at base/abstractarray.jl:1469-1473. The source
binds the selected writer's result to `r` and returns precisely that result; it
does not force the return value to be the array. Its lexical bounds request,
global check-bounds setting, caller context, arguments and effects are explicit.
Julia documentation: doc/src/devdocs/boundscheck.md:13-37,72-79,123-126. -/
-- Source: base/abstractarray.jl:1469-1473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_setindex!(A::AbstractArray, v, I...)
--     @inline
--     @inbounds r = setindex!(A, v, I...)
--     r
-- end
-- /Source
def unsafeSetindexContext {m : Type → Type} [Monad m]
    {Caller A V Index R : Type} (ops : UnsafeWriteOps m Caller A V Index R)
    (ambient : UnsafeAmbientContext Caller) (a : A) (value : V)
    (indices : Tuple Index) : m R := do
  let r ← ops.setindex
    { ambient := ambient, annotation := .inbounds, wrapperInlineHint := true }
    a value indices
  return r

end JuliaLean.base.abstractarray.Models2Group6

namespace JuliaLean.base.abstractarray.Models2Group6

open JuliaLean
open JuliaLean.base.abstractarray.Models1Group1 (Tuple)

/-- Selected calls on the unfixed concrete array arguments of the splatted
concatenation frontends. Ty is the complete promotion-result carrier: it is
not restricted to valid Type objects. The selected typed concatenation may
therefore report a dispatch error, as well as arbitrary effects and results.
Julia source: base/abstractarray.jl:1732,1765,1802. -/
-- Source: base/abstractarray.jl:1732-1732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- vcat(V::AbstractVector...) = typed_vcat(promote_eltype(V...), V...)
-- /Source
-- Source: base/abstractarray.jl:1765-1765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hcat(A::AbstractVecOrMat...) = typed_hcat(promote_eltype(A...), A...)
-- /Source
-- Source: base/abstractarray.jl:1802-1802 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- vcat(A::AbstractVecOrMat...) = typed_vcat(promote_eltype(A...), A...)
-- /Source
structure ConcatDispatchOps (m : Type → Type) (E Ty A : Type) where
  promoteEltype : Tuple E → m Ty
  typedConcat : Ty → Tuple E → m A

/-- The empty argument tuple fixes the concrete no-argument Base method,
which throws before typed concatenation. Nonempty arguments retain their
unfixed selected promotion dispatch. Tuple inspection is representation
plumbing, and the installed empty method supplies the exact error class and
message. Julia source: base/abstractarray.jl:1689. -/
-- Source: base/abstractarray.jl:1689-1689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltype() = error()
-- /Source
def concatPromoteEltype {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {E Ty : Type} (selected : Tuple E → m Ty) (args : Tuple E) : m Ty :=
  match args.values with
  | [] => match (JuliaLean.base.abstractarray.promoteEltypeEmpty : Result Ty) with
      | .ok value => pure value
      | .error error => throw error
  | _ :: _ => selected args

/-- Complete composition of the installed vertical-vector frontend, with its
known zero-argument promotion branch closed. Every nonempty splatted selected
call keeps the original ordered, native-arity tuple and actual promoted value.
Julia source: base/abstractarray.jl:1732. -/
-- Source: base/abstractarray.jl:1732-1732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- vcat(V::AbstractVector...) = typed_vcat(promote_eltype(V...), V...)
-- /Source
def vcatVectorsSelected {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {E Ty A : Type} (ops : ConcatDispatchOps m E Ty A) (args : Tuple E) : m A :=
  JuliaLean.base.abstractarray.vcatVectors
    (concatPromoteEltype ops.promoteEltype) ops.typedConcat args

/-- Complete horizontal vector/matrix frontend at the permitted selected
dispatch boundary, including the concrete empty-promotion error before any
typed concatenation. Julia source: base/abstractarray.jl:1765. -/
-- Source: base/abstractarray.jl:1765-1765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hcat(A::AbstractVecOrMat...) = typed_hcat(promote_eltype(A...), A...)
-- /Source
def hcatArraysSelected {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {E Ty A : Type} (ops : ConcatDispatchOps m E Ty A) (args : Tuple E) : m A :=
  JuliaLean.base.abstractarray.hcatArrays
    (concatPromoteEltype ops.promoteEltype) ops.typedConcat args

/-- Complete vertical vector/matrix frontend. It reuses the installed source
body and preserves selected results, aliases, arbitrary errors and effects;
the known empty-promotion branch is implemented, not a dispatch callback.
Julia source: base/abstractarray.jl:1802. -/
-- Source: base/abstractarray.jl:1802-1802 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- vcat(A::AbstractVecOrMat...) = typed_vcat(promote_eltype(A...), A...)
-- /Source
def vcatArraysSelected {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {E Ty A : Type} (ops : ConcatDispatchOps m E Ty A) (args : Tuple E) : m A :=
  JuliaLean.base.abstractarray.vcatArrays
    (concatPromoteEltype ops.promoteEltype) ops.typedConcat args

end JuliaLean.base.abstractarray.Models2Group6

namespace JuliaLean.base.abstractarray.Models2Group6

open JuliaLean
open JuliaLean.base.abstractarray
open JuliaLean.base.abstractarray.Models1Group1 (Tuple TypeAssertion assertType)
open JuliaLean.base.abstractarray.Models1Group3 (numericFromResult numericOneTo)

/-- The concrete native UnitRange value passed to a selected slice setter.
Both fields are Julia Int64 values, including wrapped endpoints. This is the
two-field representation of base/range.jl:425-429, not an index list. -/
-- Source: base/range.jl:425-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UnitRange{T<:Real} <: AbstractUnitRange{T}
--     start::T
--     stop::T
--     UnitRange{T}(start::T, stop::T) where {T<:Real} = new(start, unitrange_last(start, stop))
-- end
-- /Source
structure NativeIntUnitRange where
  start : I64
  stop : I64

/-- Native Int specialization of colon and UnitRange construction. The
Integer normalization at base/range.jl:439-441 preserves stop when ordered;
otherwise it stores the wrapping value start-one. The intermediate
start-stop is native Int, whose oneunit is native one. -/
-- Source: base/range.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (:)(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
-- /Source
-- Source: base/range.jl:428-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     UnitRange{T}(start::T, stop::T) where {T<:Real} = new(start, unitrange_last(start, stop))
-- /Source
-- Source: base/range.jl:439-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unitrange_last(start::Integer, stop::Integer) =
--     stop >= start ? stop : convert(typeof(stop),
--         _range_wrapping_sub(start, oneunit(_range_wrapping_sub(start, stop))))
-- /Source
def nativeIntUnitRange (start stop : I64) : NativeIntUnitRange :=
  ⟨start, if start.val ≤ stop.val then stop else start - int 1⟩

/-- Actual source-container dispatch at base/abstractarray.jl:1738,1744.
Tuple fields have the source's AbstractVector element membership. A vector
container keeps its unfixed concrete type and selected length/getindex calls.
These tags are runtime representation data, not correctness assumptions. -/
-- Source: base/abstractarray.jl:1738-1738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- AbstractVecOrTuple{T} = Union{AbstractVector{<:T}, Tuple{Vararg{T}}}
-- /Source
-- Source: base/abstractarray.jl:1744-1744 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_vcat!(a::AbstractVector{T}, V::AbstractVecOrTuple{AbstractVector}) where T
-- /Source
inductive VcatFillInput (Container Element : Type) where
  | tuple (values : Tuple Element)
  | vector (value : Container)

/-- Native tuple getindex returns an original field. A custom container's
getindex may instead return any other Julia value; there is no source return
annotation that forces its result to equal the declared element type.
Source: base/abstractarray.jl:1747. -/
-- Source: base/abstractarray.jl:1747-1747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         Vk = V[k]
-- /Source
abbrev VcatFillItem (Element OtherItem : Type) := Sum Element OtherItem

/-- Selected leaves of base/abstractarray.jl:1744-1753. All nonnative length
values and conversion results are admitted, including a result rejected by
the explicit Int assertion. Setter results are unrestricted and discarded.
Tuple reads/length, native Int identity, ranges, loop, and position arithmetic
are closed below and are not supplied as callbacks. -/
-- Source: base/abstractarray.jl:1744-1753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_vcat!(a::AbstractVector{T}, V::AbstractVecOrTuple{AbstractVector}) where T
--     pos = 1
--     for k=1:Int(length(V))::Int
--         Vk = V[k]
--         p1 = pos + Int(length(Vk))::Int - 1
--         a[pos:p1] = Vk
--         pos = p1+1
--     end
--     a
-- end
-- /Source
structure VcatFillOps (m : Type → Type)
    (Container Element OtherItem OtherLength NotInt Target SetResult : Type) where
  lengthVector : Container → m (RuntimeValue OtherLength)
  getVector : Container → I64 → m (VcatFillItem Element OtherItem)
  lengthItem : VcatFillItem Element OtherItem → m (RuntimeValue OtherLength)
  toInt : OtherLength → m (TypeAssertion I64 NotInt)
  setindex : Target → VcatFillItem Element OtherItem → NativeIntUnitRange → m SetResult

/-- The two explicit Int conversion/assertion points in
base/abstractarray.jl:1746,1748. Native Int construction selects the identity
method at base/boot.jl:1195; other runtime types retain their selected Int
constructor and subsequent assertion, including state changes before failure. -/
-- Source: base/boot.jl:1195-1195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(x::T) where {T<:Number} = x
-- /Source
-- Source: base/abstractarray.jl:1746-1748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     for k=1:Int(length(V))::Int
--         Vk = V[k]
--         p1 = pos + Int(length(Vk))::Int - 1
-- /Source
def vcatFillInt {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {OtherLength NotInt : Type}
    (toInt : OtherLength → m (TypeAssertion I64 NotInt)) : RuntimeValue OtherLength → m I64
  | .inl native => pure native
  | .inr other => do assertType (← toInt other)

/-- Complete effectful composition of the installed source loop at
base/abstractarray.jl:1744-1753. The two native metadata callbacks are completed
with the actual conversion/assertion steps. Native tuple getindex/length and
Int identity are closed; custom vector reads and arbitrary returned items
retain dispatch. numericOneTo is the installed native 1:n enumeration.
The slice setter receives a normalized UnitRange value and its successful
return is discarded. The original target is returned only after the loop.
No source fuel, callee-correctness law, or fixed native metadata is assumed. -/
-- Source: base/abstractarray.jl:1744-1753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_vcat!(a::AbstractVector{T}, V::AbstractVecOrTuple{AbstractVector}) where T
--     pos = 1
--     for k=1:Int(length(V))::Int
--         Vk = V[k]
--         p1 = pos + Int(length(Vk))::Int - 1
--         a[pos:p1] = Vk
--         pos = p1+1
--     end
--     a
-- end
-- /Source
def typedVcatFillConverted {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Container Element OtherItem OtherLength NotInt Target SetResult : Type}
    (ops : VcatFillOps m Container Element OtherItem OtherLength NotInt Target SetResult)
    (target : Target) (input : VcatFillInput Container Element) : m Target :=
  JuliaLean.base.abstractarray.typedVcatFill
    (fun input => do
      let length ← match input with
        | .tuple values => pure (.inl (tupleFieldCount values))
        | .vector value => ops.lengthVector value
      vcatFillInt ops.toInt length)
    (fun _ last => pure (numericOneTo last))
    (fun input index => match input with
      | .tuple values => do
          return .inl (← numericFromResult (tupleGet values.values index))
      | .vector value => ops.getVector value index)
    (fun item => do vcatFillInt ops.toInt (← ops.lengthItem item))
    (fun start stop => pure (nativeIntUnitRange start stop))
    (fun array range item => do
      let _ ← ops.setindex array item range
      pure ())
    target input

end JuliaLean.base.abstractarray.Models2Group6


namespace JuliaLean.base.abstractarray.ArrayCallees

open JuliaLean JuliaLean.base.abstractarray

-- placed here to break an import cycle with array
/-- Native array copying, base/array.jl:391-399. Runtime field, allocation and memory operations retain their installed interface. -/
-- Source: base/array.jl:391-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @eval function copy(a::Array)
--     # `copy` only throws when the size exceeds the max allocation size,
--     # but since we're copying an existing array, we're guaranteed that this will not happen.
--     @_nothrow_meta
--     ref = a.ref
--     newmem = typeof(ref.mem)(undef, length(a))
--     @inbounds unsafe_copyto!(memoryref(newmem), ref, length(a))
--     return $(Expr(:new, :(typeof(a)), :(memoryref(newmem)), :(a.size)))
-- end
-- /Source
def copyArray {m : Type → Type} [Monad m] {A R Mem D : Type}
    (ref : A → m R) (length : A → m I64)
    (allocateMemory : R → I64 → m Mem) (memoryref : Mem → m R)
    (copy : R → R → I64 → m Unit) (size : A → m D) (newArray : R → D → m A)
    (a : A) : m A := do
  let ref ← ref a
  let newmem ← allocateMemory ref (← length a)
  copy (← memoryref newmem) ref (← length a)
  newArray (← memoryref newmem) (← size a)

end JuliaLean.base.abstractarray.ArrayCallees

namespace JuliaLean.base.abstractarray.Completion20261105

open JuliaLean JuliaLean.base.abstractarray

/-- Dense mutable copying invokes the installed native Array copy body, base/abstractarray.jl:1216. -/
-- Source: base/abstractarray.jl:1216-1216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copymutable(a::Array) = copy(a)
-- /Source
def copyMutableDense {m : Type → Type} [Monad m] {A R Mem D : Type}
    (ref : A → m R) (length : A → m I64)
    (allocateMemory : R → I64 → m Mem) (memoryref : Mem → m R)
    (copy : R → R → I64 → m Unit) (size : A → m D) (newArray : R → D → m A)
    (a : A) : m A :=
  ArrayCallees.copyArray ref length allocateMemory memoryref copy size newArray a

end JuliaLean.base.abstractarray.Completion20261105

namespace JuliaLean.base.abstractarray.Completion20261105

open JuliaLean JuliaLean.base.abstractarray
open JuliaLean.base.abstractarray.Models1Group1 (Tuple TypeAssertion assertType)
open JuliaLean.base.abstractarray.Models2Group6 (UnsafeCheckBounds UnsafeAmbientContext UnsafeIndexRequest)

/-- Dispatch leaves in base/abstractarray.jl:920-927. Comparison results retain their Bool assertion and counts their unfixed runtime types. -/
structure CopyVectorOps (m : Type → Type) (D S DI SI DL SL Other R ResizeResult : Type) where
  firstDest : D → m DI
  firstSrc : S → m SI
  equal : DI → SI → m (TypeAssertion Bool Other)
  lengthDest : D → m DL
  lengthSrc : S → m SL
  notEqual : DL → SL → m (TypeAssertion Bool Other)
  resize : D → SL → m ResizeResult
  copyto : D → S → m R

/-- Val's parameter is runtime type metadata; the Julia value has no data fields.
Source: base/essentials.jl:1199-1203. -/
-- Source: base/essentials.jl:1199-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Val{x}
--     Val{x}() where {x} = new()
-- end
--
-- Val(x) = Val{x}()
-- /Source
structure ValValue (Parameter : Type) where
  parameter : Parameter

/-- Base Val construction retains the actual type parameter, base/essentials.jl:1203. -/
def valValue {Parameter : Type} (parameter : Parameter) : ValValue Parameter := ⟨parameter⟩

/-- Runtime dispatch partition for Base.Generator(f, iter), including type objects.
The free-type-variable bit is type metadata from the runtime. Source: base/generator.jl:3-40. -/
inductive GeneratorFunction (Fn Ty : Type) where
  | ordinary (function : Fn)
  | typeObject (type : Ty) (hasFreeTypevars : Bool)

/-- Preserve the concrete Generator constructor's two result layouts. -/
inductive GeneratorValue (Iterator Fn Ty : Type) where
  | ordinary (generator : JuliaLean.base.generator.Generator Iterator Fn)
  | typeObject (generator : JuliaLean.base.generator.Generator Iterator
      (JuliaLean.base.generator.GeneratorTypeFunction Ty))

/-- Close the installed one-iterator constructor; there is no generator-result callback.
Source: base/generator.jl:3-40. -/
def constructGenerator {Iterator Fn Ty : Type} (function : GeneratorFunction Fn Ty)
    (iterator : Iterator) : GeneratorValue Iterator Fn Ty :=
  match function with
  | .ordinary f => .ordinary ⟨f, iterator⟩
  | .typeObject t hasFree => .typeObject
      (JuliaLean.base.generator.generatorFromType (fun _ => hasFree) t iterator)

/-- The generated lambda captures f and applies it to one iteration value.
Source: base/abstractarray.jl:2996. -/
structure ApplyClosure (Fn : Type) where
  function : Fn

def applyClosure {m : Type → Type} {Fn X R : Type}
    (apply : Fn → X → m R) (closure : ApplyClosure Fn) (x : X) : m R :=
  apply closure.function x

/-- The generated lambda captures f and splats its one iteration value.
Source: base/abstractarray.jl:2997. -/
structure SplatClosure (Fn : Type) where
  function : Fn

def applySplatClosure {m : Type → Type} {Fn Args R : Type}
    (apply : Fn → Args → m R) (closure : SplatClosure Fn) (args : Args) : m R :=
  apply closure.function args

/-- The installed Fix2 membership closure retains its operator tag and captured range. -/
abbrev InPredicate (m : Type → Type) (Value Predicate : Type) (collection : Value) :=
  JuliaLean.base.operators.Fix 2 (Value → Value → Unit → m Predicate) Value
    JuliaLean.base.operators.Fix2OpTag.inOp collection

/-- The global bounds policy resolves the caller/compiler's actual incoming check decision.
Metadata follows doc/src/devdocs/boundscheck.md:13-37,123-126. -/
def boundsActive (policy : UnsafeCheckBounds) (incoming : Bool) : Bool :=
  match policy with
  | .always => true
  | .never => false
  | .automatic => incoming

/-- Source-language effects retain arbitrary exceptions, worlds and nonreturning calls. -/
abbrev ArrayM (Error World : Type) := ExceptT Error (StateT World Option)

/-- Fuel-free source-language while control. No Julia callee or loop result is supplied. -/
def arrayLoopRaw {Error World S A : Type}
    (step : S → ArrayM Error World (Sum A S)) (state : S) (world : World) :
    Option (Except Error A × World) :=
  match (step state).run.run world with
  | none => none
  | some (.error error, after) => some (.error error, after)
  | some (.ok (.inl result), after) => some (.ok result, after)
  | some (.ok (.inr next), after) => arrayLoopRaw step next after
partial_fixpoint

def arrayLoop {Error World S A : Type} (step : S → ArrayM Error World (Sum A S))
    (initial : S) : ArrayM Error World A :=
  ExceptT.mk <| StateT.mk (arrayLoopRaw step initial)

/-- Native UInt and Symbol membership dispatch remain concrete. Other retains every
other Julia value and its runtime type through the selected-call interface. Symbol
strings are identity tokens, rather than rendered names. -/
inductive AliasAtom (Other : Type) where
  | word (value : JInt .u64)
  | symbol (identity : String)
  | other (value : Other)

/-- Bool membership is runtime type metadata, not a correctness assertion. -/
abbrev AliasTruth (Other : Type) := TypeAssertion Bool Other

structure DisjointOps (m : Type → Type) (Element Other : Type) where
  equal : AliasAtom Element → AliasAtom Element → m (AliasTruth Other)
  or : AliasTruth Other → AliasTruth Other → m (AliasTruth Other)
  not : Other → m (AliasTruth Other)

/-- Fixed equality on the concrete UInt/Symbol branches; selected equality otherwise. -/
def aliasEqual {m : Type → Type} [Monad m] {Element Other : Type}
    (ops : DisjointOps m Element Other) (left right : AliasAtom Element) : m (AliasTruth Other) :=
  match left, right with
  | .word a, .word b => pure (.accepted (a == b))
  | .symbol a, .symbol b => pure (.accepted (a == b))
  | .word _, .symbol _ | .symbol _, .word _ => pure (.accepted false)
  | _, _ => ops.equal left right

/-- Concrete Bool or, with both operands already evaluated, and selected non-Bool or. -/
def aliasOr {m : Type → Type} [Monad m] {Element Other : Type}
    (ops : DisjointOps m Element Other) (left right : AliasTruth Other) : m (AliasTruth Other) :=
  match left, right with
  | .accepted a, .accepted b => pure (.accepted (a || b))
  | _, _ => ops.or left right

def aliasNot {m : Type → Type} [Monad m] {Element Other : Type}
    (ops : DisjointOps m Element Other) : AliasTruth Other → m (AliasTruth Other)
  | .accepted b => pure (.accepted (!b))
  | .rejected other => ops.not other

/-- Close tuple membership without narrowing arbitrary equality/or results to Bool or Missing.
Unlike any, an accumulated true result does not stop later comparisons; only v === true does. -/
-- Source: base/operators.jl:1463-1471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _in_tuple(x, @nospecialize(itr::Tuple), result = false)
--     @inline
--     isempty(itr) && return result
--     v = (itr[1] == x)
--     if v === true
--         return true
--     end
--     return _in_tuple(x, tail(itr), result | v)
-- end
-- /Source
def aliasInTupleLoop {m : Type → Type} [Monad m] {Element Other : Type}
    (ops : DisjointOps m Element Other) (needle : AliasAtom Element)
    (result : AliasTruth Other) : List (AliasAtom Element) → m (AliasTruth Other)
  | [] => pure result
  | first :: rest => do
      let value ← aliasEqual ops first needle
      match value with
      | .accepted true => pure (.accepted true)
      | _ => aliasInTupleLoop ops needle (← aliasOr ops result value) rest

/-- Runtime Symbol-tuple classification is pure immutable type metadata. -/
def aliasSymbolFields : List (AliasAtom Element) → Option (List String)
  | [] => some []
  | .symbol name :: rest => (aliasSymbolFields rest).map (name :: ·)
  | _ => none

/-- Close both pinned tuple membership methods, including the Symbol specialization. -/
def aliasInTuple {m : Type → Type} [Monad m] {Element Other : Type}
    (ops : DisjointOps m Element Other) (needle : AliasAtom Element)
    (values : List (AliasAtom Element)) : m (AliasTruth Other) :=
  match needle with
  | .symbol name => match aliasSymbolFields values with
      | some symbols => pure (.accepted (JuliaLean.base.tuple.inSym name symbols))
      | none => aliasInTupleLoop ops needle (.accepted false) values
  | _ => aliasInTupleLoop ops needle (.accepted false) values

/-- Int literals retain their native type; Other retains all other runtime types,
including noninteger intermediate values returned by selected arithmetic. -/
inductive SubscriptValue (Other : Type) where
  | native (value : I64)
  | other (value : Other)

/-- Only native tuples have fixed head/tail operations. Other containers retain
selected indexing and tail dispatch, including effects and nontermination. -/
inductive SubscriptShape (Dimension Container : Type) where
  | tuple (values : Tuple Dimension)
  | container (value : Container)

structure SubscriptOps (m : Type → Type) (Other Dimension Container : Type) where
  subtract : SubscriptValue Other → SubscriptValue Other → m (SubscriptValue Other)
  multiply : SubscriptValue Other → SubscriptValue Other → m (SubscriptValue Other)
  add : SubscriptValue Other → SubscriptValue Other → m (SubscriptValue Other)
  getindex : Container → I64 → m Dimension
  tail : Container → m (SubscriptShape Dimension Container)
  nextL : SubscriptValue Other → Dimension → m (SubscriptValue Other)
  offsetin : SubscriptValue Other → Dimension → m (SubscriptValue Other)

def subscriptSubtract {m : Type → Type} [Monad m] {Other Dimension Container : Type}
    (ops : SubscriptOps m Other Dimension Container) (left right : SubscriptValue Other) :
    m (SubscriptValue Other) :=
  match left, right with
  | .native a, .native b => pure (.native (a - b))
  | _, _ => ops.subtract left right

def subscriptMultiply {m : Type → Type} [Monad m] {Other Dimension Container : Type}
    (ops : SubscriptOps m Other Dimension Container) (left right : SubscriptValue Other) :
    m (SubscriptValue Other) :=
  match left, right with
  | .native a, .native b => pure (.native (a * b))
  | _, _ => ops.multiply left right

def subscriptAdd {m : Type → Type} [Monad m] {Other Dimension Container : Type}
    (ops : SubscriptOps m Other Dimension Container) (left right : SubscriptValue Other) :
    m (SubscriptValue Other) :=
  match left, right with
  | .native a, .native b => pure (.native (a + b))
  | _, _ => ops.add left right

def subscriptHead {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Other Dimension Container : Type} (ops : SubscriptOps m Other Dimension Container) :
    SubscriptShape Dimension Container → m Dimension
  | .tuple values => match tupleGet values.values (int 1) with
      | .ok value => pure value
      | .error error => throw error
  | .container value => ops.getindex value (int 1)

def subscriptTail {m : Type → Type} [Monad m] {Other Dimension Container : Type}
    (ops : SubscriptOps m Other Dimension Container) :
    SubscriptShape Dimension Container → m (SubscriptShape Dimension Container)
  | .tuple values => pure (.tuple ⟨values.values.tail, by
      simpa only [List.length_tail] using Nat.le_trans (Nat.sub_le values.values.length 1) values.nativeArity⟩)
  | .container value => ops.tail value

/-- All recursive source calls are closed. The integer-coordinate tuple decreases;
the dimension container need not decrease or even remain a tuple. Runtime nextL
and offsetin selection remains on the unfixed type of each fetched dimension.
Source: base/abstractarray.jl:3193-3202. -/
-- Source: base/abstractarray.jl:3193-3202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind_recurse(::Any, L, ind) = ind
-- function _sub2ind_recurse(::Tuple{}, L, ind, i::Integer, I::Integer...)
--     @inline
--     _sub2ind_recurse((), L, ind+(i-1)*L, I...)
-- end
-- function _sub2ind_recurse(inds, L, ind, i::Integer, I::Integer...)
--     @inline
--     r1 = inds[1]
--     _sub2ind_recurse(tail(inds), nextL(L, r1), ind+offsetin(i, r1)*L, I...)
-- end
-- /Source
def subscriptLoop {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Other Dimension Container : Type} (ops : SubscriptOps m Other Dimension Container)
    (shape : SubscriptShape Dimension Container) (stride index : SubscriptValue Other) :
    List (SubscriptValue Other) → m (SubscriptValue Other)
  | [] => pure index
  | coordinate :: rest => do
      match shape with
      | .tuple ⟨[], _⟩ =>
          let offset ← subscriptSubtract ops coordinate (.native (int 1))
          let product ← subscriptMultiply ops offset stride
          subscriptLoop ops shape stride (← subscriptAdd ops index product) rest
      | _ =>
          let dimension ← subscriptHead ops shape
          let tail ← subscriptTail ops shape
          let next ← ops.nextL stride dimension
          let offset ← ops.offsetin coordinate dimension
          let product ← subscriptMultiply ops offset stride
          subscriptLoop ops tail next (← subscriptAdd ops index product) rest

/-- Zero-dimensional arrays have a singleton first axis, base/abstractarray.jl:140. -/
-- Source: base/abstractarray.jl:140-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes1(A::AbstractArray{<:Any,0}) = OneTo(1)
-- /Source
def axes1Zero {A : Type} (_ : A) :=
  JuliaLean.base.range.Models1Group7.oneToStopBits .i64 .i64 (int 1)

/-- Full source body with runtime-selected operations and unchanged error/effect order, base/abstractarray.jl:169-169. -/
-- Source: base/abstractarray.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keys(a::AbstractArray) = CartesianIndices(axes(a))
-- /Source
def keysArray {m : Type → Type} [Monad m] {A Axes R : Type}
    (axes : A → m Axes) (cartesianIndices : Axes → m R) (a : A) : m R := do
  cartesianIndices (← axes a)

/-- Full source body with runtime-selected operations and unchanged error/effect order, base/abstractarray.jl:170-170. -/
-- Source: base/abstractarray.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keys(a::AbstractVector) = LinearIndices(a)
-- /Source
def keysVector {m : Type → Type} {A R : Type}
    (linearIndices : A → m R) (a : A) : m R := linearIndices a

/-- Selected type metadata method, base/abstractarray.jl:192. typeof is runtime metadata. -/
-- Source: base/abstractarray.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keytype(a::AbstractArray) = keytype(typeof(a))
-- /Source
def keytypeValue {m : Type → Type} {A Ty R : Type}
    (typeof : A → Ty) (keytype : Ty → m R) (a : A) : m R := keytype (typeof a)

/-- Selected type metadata method, base/abstractarray.jl:198. -/
-- Source: base/abstractarray.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- valtype(a::AbstractArray) = valtype(typeof(a))
-- /Source
def valtypeValue {m : Type → Type} {A Ty R : Type}
    (typeof : A → Ty) (valtype : Ty → m R) (a : A) : m R := valtype (typeof a)

/-- Full source body with runtime-selected operations and unchanged error/effect order, base/abstractarray.jl:243-243. -/
-- Source: base/abstractarray.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltype(::Type) = Any
-- /Source
def eltypeDefault {Ty : Type} (_type : Ty) : JuliaLean.base.promotion.PType := .any

/-- Element storage metadata preserves the selected method's runtime result, base/abstractarray.jl:261. -/
-- Source: base/abstractarray.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- elsize(A::AbstractArray) = elsize(typeof(A))
-- /Source
def elsizeValue {m : Type → Type} {A Ty R : Type}
    (typeof : A → Ty) (elsize : Ty → m R) (a : A) : m R := elsize (typeof a)

/-- Both calls dispatch on the unfixed array tuple, base/abstractarray.jl:390-393. -/
-- Source: base/abstractarray.jl:390-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function eachindex(A::AbstractArray, B::AbstractArray...)
--     @inline
--     eachindex(IndexStyle(A,B...), A, B...)
-- end
-- /Source
def eachindexMany {m : Type → Type} [Monad m] {A B Style R : Type}
    (indexStyle : A → Tuple B → m Style) (eachindex : Style → A → Tuple B → m R)
    (a : A) (bs : Tuple B) : m R := do
  let style ← indexStyle a bs
  eachindex style a bs

/-- Style-directed keys preserve the original arrays, base/abstractarray.jl:407. -/
-- Source: base/abstractarray.jl:407-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keys(s::IndexStyle, A::AbstractArray, B::AbstractArray...) = eachindex(s, A, B...)
-- /Source
def keysStyle {m : Type → Type} {S A B R : Type}
    (eachindex : S → A → Tuple B → m R) (style : S) (a : A) (bs : Tuple B) : m R :=
  eachindex style a bs

/-- Obtain the axis before its final index, base/abstractarray.jl:430. -/
-- Source: base/abstractarray.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- lastindex(a, d) = (@inline; last(axes(a, d)))
-- /Source
def lastindexDim {m : Type → Type} [Monad m] {A D Axis R : Type}
    (axes : A → D → m Axis) (last : Axis → m R) (a : A) (d : D) : m R := do
  last (← axes a d)

/-- Obtain the axis before its first index, base/abstractarray.jl:453. -/
-- Source: base/abstractarray.jl:453-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- firstindex(a, d) = (@inline; first(axes(a, d)))
-- /Source
def firstindexDim {m : Type → Type} [Monad m] {A D Axis R : Type}
    (axes : A → D → m Axis) (first : Axis → m R) (a : A) (d : D) : m R := do
  first (← axes a d)

/-- IdentityUnitRange field access is concrete; checking its unfixed inner range is selected, base/abstractarray.jl:752. -/
-- Source: base/abstractarray.jl:752-752 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::IdentityUnitRange, i::Real) = checkindex(Bool, inds.indices, i)
-- /Source
def checkindexIdentity {m : Type → Type} {Axis I R : Type}
    (checkindex : Axis → I → m R) (inds : JuliaLean.base.indices.IdentityUnitRange Axis)
    (index : I) : m R := checkindex inds.indices index

/-- Int construction has no return assertion here; user-defined Integer methods can return any value, base/abstractarray.jl:841. -/
-- Source: base/abstractarray.jl:841-841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- to_shape(i::Integer) = Int(i)
-- /Source
def toShapeInteger {m : Type → Type} {Integer R : Type}
    (toInt : Integer → m R) (i : Integer) : m R := toInt i

/-- Preserve selected to_shape dispatch on the Integer argument, base/abstractarray.jl:843. -/
-- Source: base/abstractarray.jl:843-843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _to_shape(x::Integer) = to_shape(x)
-- /Source
def toShapeIntegerHelper {m : Type → Type} {Integer R : Type}
    (toShape : Integer → m R) (x : Integer) : m R := toShape x

/-- Preserve arbitrary Int-constructor results without an invented assertion, base/abstractarray.jl:844. -/
-- Source: base/abstractarray.jl:844-844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _to_shape(x) = Int(x)
-- /Source
def toShapeOtherHelper {m : Type → Type} {A R : Type}
    (toInt : A → m R) (x : A) : m R := toInt x

/-- The storage type is unfixed and its constructor remains selected, base/abstractarray.jl:873. -/
-- Source: base/abstractarray.jl:873-873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(::Type{T}, dims::Dims) where {T<:AbstractArray} = T(undef, dims)
-- /Source
def similarStorageDims {m : Type → Type} {Ty R : Type}
    (constructUndef : Ty → Tuple I64 → m R) (storage : Ty) (dims : Tuple I64) : m R :=
  constructUndef storage dims

/-- Offset checking precedes lengths; source length is evaluated again only when resizing, base/abstractarray.jl:920-927. -/
-- Source: base/abstractarray.jl:920-927 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copy!(dst::AbstractVector, src::AbstractVector)
--     firstindex(dst) == firstindex(src) || throw(ArgumentError(
--         "vectors must have the same offset for copy! (consider using `copyto!`)"))
--     if length(dst) != length(src)
--         resize!(dst, length(src))
--     end
--     copyto!(dst, src)
-- end
-- /Source
def copyBangVector {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S DI SI DL SL Other R ResizeResult : Type}
    (ops : CopyVectorOps m D S DI SI DL SL Other R ResizeResult) (dst : D) (src : S) : m R := do
  let di ← ops.firstDest dst
  let si ← ops.firstSrc src
  let same ← assertType (← ops.equal di si)
  if !same then
    throw (.julia (.argumentError
      "vectors must have the same offset for copy! (consider using `copyto!`)"))
  let dl ← ops.lengthDest dst
  let sl ← ops.lengthSrc src
  let different ← assertType (← ops.notEqual dl sl)
  if different then
    let n ← ops.lengthSrc src
    let _ ← ops.resize dst n
  ops.copyto dst src

/-- Full source ordering and runtime-selected dispatch, base/abstractarray.jl:953-971. -/
-- Source: base/abstractarray.jl:953-971 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto!(dest::AbstractArray, dstart::Integer, src)
--     i = Int(dstart)
--     if haslength(src) && length(dest) > 0
--         n = length(src)
--         n == 0 && return dest
--         @boundscheck checkbounds(dest, i)
--         @boundscheck n <= lastindex(dest) - i + 1 || throw(BoundsError(dest, i))
--         for x in src
--             @inbounds dest[i] = x
--             i += 1
--         end
--     else
--         for x in src
--             dest[i] = x
--             i += 1
--         end
--     end
--     return dest
-- end
-- /Source
def copytoIterableAt {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D Src E Start Value LengthD Count Last Difference Span Other CheckResult StoreResult Caller : Type}
    [ForIn m Src E]
    (toInt : Start → m Value) (haslength : Src → m (TypeAssertion Bool Other))
    (lengthDest : D → m LengthD) (positive : LengthD → I64 → m (TypeAssertion Bool Other))
    (lengthSrc : Src → m Count) (isZero : Count → I64 → m (TypeAssertion Bool Other))
    (checkbounds : D → Value → m CheckResult) (lastindex : D → m Last)
    (subtract : Last → Value → m Difference) (addSpan : Difference → I64 → m Span)
    (lessEqual : Count → Span → m (TypeAssertion Bool Other))
    (increment : Value → I64 → m Value)
    (setindex : UnsafeIndexRequest Caller → D → Value → E → m StoreResult)
    (ambient : UnsafeAmbientContext Caller) (incomingBounds : Bool)
    (dest : D) (start : Start) (src : Src) : m D := do
  let mut i ← toInt start
  let hasLen ← assertType (← haslength src)
  let sized ← if hasLen then do
      assertType (← positive (← lengthDest dest) (int 0))
    else pure false
  if sized then
    let n ← lengthSrc src
    if ← assertType (← isZero n (int 0)) then return dest
    if boundsActive ambient.checkBounds incomingBounds then
      let _ ← checkbounds dest i
      let span ← addSpan (← subtract (← lastindex dest) i) (int 1)
      if !(← assertType (← lessEqual n span)) then throw (.julia .boundsError)
    for value in src do
      let _ ← setindex { ambient := ambient, annotation := .inbounds, wrapperInlineHint := false }
        dest i value
      i ← increment i (int 1)
  else
    for value in src do
      let _ ← setindex { ambient := ambient, annotation := .inherited, wrapperInlineHint := false }
        dest i value
      i ← increment i (int 1)
  return dest

/-- Full offset-copy body, including both repeated error-path subtractions and the unasserted Int result, base/abstractarray.jl:974-1000. -/
-- Source: base/abstractarray.jl:974-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto!(dest::AbstractArray, dstart::Integer, src, sstart::Integer)
--     if (sstart < 1)
--         throw(ArgumentError(LazyString("source start offset (",sstart,") is < 1")))
--     end
--     y = iterate(src)
--     for j = 1:(sstart-1)
--         if y === nothing
--             throw(ArgumentError(LazyString(
--                 "source has fewer elements than required, ",
--                 "expected at least ", sstart,", got ", j-1)))
--         end
--         y = iterate(src, y[2])
--     end
--     if y === nothing
--         throw(ArgumentError(LazyString(
--             "source has fewer elements than required, ",
--             "expected at least ",sstart,", got ", sstart-1)))
--     end
--     i = Int(dstart)
--     while y !== nothing
--         val, st = y
--         dest[i] = val
--         i += 1
--         y = iterate(src, st)
--     end
--     return dest
-- end
-- /Source
def copytoIterableFrom {Error World D Src E Start Offset End Range J Index St Other StoreResult Caller : Type}
    [MonadExceptOf ArrayError (ArrayM Error World)] [ForIn (ArrayM Error World) Range J]
    (lessOne : Offset → I64 → ArrayM Error World (TypeAssertion Bool Other))
    (subtractOffset : Offset → I64 → ArrayM Error World End)
    (subtractLoop : J → I64 → ArrayM Error World End)
    (range : I64 → End → ArrayM Error World Range)
    (start : Src → ArrayM Error World (Option (E × St)))
    (next : Src → St → ArrayM Error World (Option (E × St)))
    (toInt : Start → ArrayM Error World Index) (increment : Index → I64 → ArrayM Error World Index)
    (setindex : UnsafeIndexRequest Caller → D → Index → E → ArrayM Error World StoreResult)
    (ambient : UnsafeAmbientContext Caller)
    (dest : D) (dstart : Start) (src : Src) (sstart : Offset) : ArrayM Error World D := do
  if ← assertType (← lessOne sstart (int 1)) then
    throw (.julia (.argumentError "source start offset is < 1"))
  let mut y ← start src
  let stop ← subtractOffset sstart (int 1)
  for j in (← range (int 1) stop) do
    match y with
    | none =>
        let _ ← subtractLoop j (int 1)
        throw (.julia (.argumentError "source has fewer elements than required"))
    | some (_, state) => y ← next src state
  if y.isNone then
    let _ ← subtractOffset sstart (int 1)
    throw (.julia (.argumentError "source has fewer elements than required"))
  let i ← toInt dstart
  let _ ← arrayLoop (fun (i, y) => do
    match y with
    | none => return .inl ()
    | some (value, state) =>
        let _ ← setindex { ambient := ambient, annotation := .inherited, wrapperInlineHint := false }
          dest i value
        let i ← increment i (int 1)
        let y ← next src state
        return .inr (i, y)) (i, y)
  return dest

/-- Bounded iterable copying with nonrendered exception payloads, base/abstractarray.jl:1003-1037. -/
-- Source: base/abstractarray.jl:1003-1037 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto!(dest::AbstractArray, dstart::Integer, src, sstart::Integer, n::Integer)
--     n < 0 && throw(ArgumentError(LazyString("tried to copy n=",n,
--         ", elements, but n should be non-negative")))
--     n == 0 && return dest
--     inds = LinearIndices(dest)
--     sstart < 1 && throw(ArgumentError(LazyString("source start offset (",
--         sstart,") is < 1")))
--     (dstart ∈ inds && n <= last(inds) - dstart + 1) || throw(BoundsError(dest, dstart))
--     dstart = Int(dstart)
--     n = Int(n)
--     dmax = dstart + n - 1
--     y = iterate(src)
--     for j = 1:(sstart-1)
--         if y === nothing
--             throw(ArgumentError(LazyString(
--                 "source has fewer elements than required, ",
--                 "expected at least ",sstart,", got ",j-1)))
--         end
--         y = iterate(src, y[2])
--     end
--     if y === nothing
--         throw(ArgumentError(LazyString(
--             "source has fewer elements than required, ",
--             "expected at least ",sstart," got ", sstart-1)))
--     end
--     val, st = y
--     i = dstart
--     @inbounds dest[i] = val
--     for val in Iterators.take(Iterators.rest(src, st), n-1)
--         i += 1
--         @inbounds dest[i] = val
--     end
--     i < dmax && throw(BoundsError(dest, i))
--     return dest
-- end
-- /Source
inductive CopytoLazyPart (Offset Count PrefixOffset ShortCount : Type) where
  | text (value : String)
  | count (value : Count)
  | offset (value : Offset)
  | prefixResult (value : PrefixOffset)
  | loopResult (value : ShortCount)

/-- LazyString stores its arguments without invoking their printers. -/
structure CopytoLazyMessage (Offset Count PrefixOffset ShortCount : Type) where
  parts : List (CopytoLazyPart Offset Count PrefixOffset ShortCount)
  compact : Bool := false
  cached : Option String := none

inductive CopytoIterableError (D Start Offset Count PrefixOffset ShortCount Other : Type) where
  | argument (message : CopytoLazyMessage Offset Count PrefixOffset ShortCount)
  | boundsOriginal (destination : D) (index : Start)
  | boundsFinal (destination : D) (index : I64)
  | typeError (functionName context expected : String) (actual : Other)

/-- Condition lowering calls jl_type_error("if", Bool, actual).
Source: src/interpreter.c:645; src/rtutils.c:jl_type_error. -/
def copytoAssertBool {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {D Start Offset Count PrefixOffset ShortCount Other : Type}
    (inject : CopytoIterableError D Start Offset Count PrefixOffset ShortCount Other → Error) :
    TypeAssertion Bool Other → m Bool
  | .accepted value => pure value
  | .rejected actual => throw (inject (.typeError "if" "" "Bool" actual))

/-- The identity injection retains every exception field. Other injections are
explicit projections for clients that observe only exception classes.
Source: base/abstractarray.jl:1003-1037 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027 -/
def copytoIterableN {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {D Src E Start Offset Count Linear Endpoint Difference Span PrefixOffset ShortCount
      Prefix J St Rest Taken Other StoreResult Caller : Type}
    [ForIn m Prefix J] [ForIn m Taken E]
    (inject : CopytoIterableError D Start Offset Count PrefixOffset ShortCount Other → Error)
    (negative isZero : Count → I64 → m (TypeAssertion Bool Other))
    (linearIndices : D → m Linear)
    (lessOne : Offset → I64 → m (TypeAssertion Bool Other))
    (contains : Start → Linear → m (TypeAssertion Bool Other)) (last : Linear → m Endpoint)
    (subtract : Endpoint → Start → m Difference) (addOne : Difference → I64 → m Span)
    (lessEqual : Count → Span → m (TypeAssertion Bool Other))
    (toIntStart : Start → m I64) (toIntCount : Count → m I64)
    (start : Src → m (Option (E × St))) (next : Src → St → m (Option (E × St)))
    (subtractOffset : Offset → I64 → m PrefixOffset)
    (subtractLoop : J → I64 → m ShortCount) (range : I64 → PrefixOffset → m Prefix)
    (rest : Src → St → m Rest) (take : Rest → I64 → m Taken)
    (setindex : UnsafeIndexRequest Caller → D → I64 → E → m StoreResult)
    (ambient : UnsafeAmbientContext Caller)
    (dest : D) (dstart : Start) (src : Src) (sstart : Offset) (n : Count) : m D := do
  if ← copytoAssertBool inject (← negative n (int 0)) then
    throw (inject (.argument ⟨[.text "tried to copy n=", .count n,
      .text ", elements, but n should be non-negative"], false, none⟩))
  if ← copytoAssertBool inject (← isZero n (int 0)) then return dest
  let inds ← linearIndices dest
  if ← copytoAssertBool inject (← lessOne sstart (int 1)) then
    throw (inject (.argument ⟨[.text "source start offset (", .offset sstart,
      .text ") is < 1"], false, none⟩))
  let allowed ← copytoAssertBool inject (← contains dstart inds)
  if !allowed then throw (inject (.boundsOriginal dest dstart))
  let span ← addOne (← subtract (← last inds) dstart) (int 1)
  if !(← copytoAssertBool inject (← lessEqual n span)) then
    throw (inject (.boundsOriginal dest dstart))
  let dstart ← toIntStart dstart
  let n ← toIntCount n
  let dmax := dstart + n - int 1
  let mut y ← start src
  let stop ← subtractOffset sstart (int 1)
  for j in (← range (int 1) stop) do
    match y with
    | none =>
        let got ← subtractLoop j (int 1)
        throw (inject (.argument ⟨[.text "source has fewer elements than required, ",
          .text "expected at least ", .offset sstart, .text ", got ", .loopResult got],
          false, none⟩))
    | some (_, state) => y ← next src state
  match y with
  | none =>
      let got ← subtractOffset sstart (int 1)
      throw (inject (.argument ⟨[.text "source has fewer elements than required, ",
        .text "expected at least ", .offset sstart, .text " got ", .prefixResult got],
        false, none⟩))
  | some (value, state) =>
      let mut i := dstart
      let request : UnsafeIndexRequest Caller :=
        { ambient := ambient, annotation := .inbounds, wrapperInlineHint := false }
      let _ ← setindex request dest i value
      let remaining ← rest src state
      let taken ← take remaining (n - int 1)
      for value in taken do
        i := i + int 1
        let _ ← setindex request dest i value
      if i.val < dmax.val then throw (inject (.boundsFinal dest i))
      return dest

/-- Full source ordering and runtime-selected dispatch, base/abstractarray.jl:1125-1127. -/
-- Source: base/abstractarray.jl:1125-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray)
--     copyto!(dest, dstart, src, first(LinearIndices(src)), length(src))
-- end
-- /Source
def copytoArrayAt {m : Type → Type} [Monad m] {D S Start Linear Index Count R : Type}
    (linearIndices : S → m Linear) (first : Linear → m Index) (length : S → m Count)
    (copyto : D → Start → S → Index → Count → m R)
    (dest : D) (start : Start) (src : S) : m R := do
  let linear ← linearIndices src
  let index ← first linear
  let count ← length src
  copyto dest start src index count

/-- Full source ordering and runtime-selected dispatch, base/abstractarray.jl:1135-1152. -/
-- Source: base/abstractarray.jl:1135-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto!(dest::AbstractArray, dstart::Integer,
--                  src::AbstractArray, sstart::Integer,
--                  n::Integer)
--     n == 0 && return dest
--     n < 0 && throw(ArgumentError(LazyString("tried to copy n=",
--         n," elements, but n should be non-negative")))
--     destinds, srcinds = LinearIndices(dest), LinearIndices(src)
--     (checkbounds(Bool, destinds, dstart) && n <= last(destinds) - dstart + 1) || throw(BoundsError(dest, dstart))
--     (checkbounds(Bool, srcinds, sstart)  && n <= last(srcinds) - sstart + 1)  || throw(BoundsError(src, sstart))
--     dstart = Int(dstart)
--     sstart = Int(sstart)
--     n = Int(n)
--     src′ = unalias(dest, src)
--     @inbounds for i = 0:n-1
--         dest[dstart+i] = src′[sstart+i]
--     end
--     return dest
-- end
-- /Source
def copytoArrayN {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S Value LinearD LinearS U E Range Yield Other StoreResult Caller : Type}
    [ForIn m Range Yield]
    (isZero negative : Value → I64 → m (TypeAssertion Bool Other))
    (linearDest : D → m LinearD) (linearSrc : S → m LinearS)
    (checkDest : LinearD → Value → m (TypeAssertion Bool Other))
    (checkSrc : LinearS → Value → m (TypeAssertion Bool Other))
    (lastDest : LinearD → m Value) (lastSrc : LinearS → m Value)
    (subtract : Value → Value → m Value)
    (addOne subtractOne : Value → I64 → m Value)
    (lessEqual : Value → Value → m (TypeAssertion Bool Other))
    (toInt : Value → m Value) (unalias : D → S → m U)
    (range : I64 → Value → m Range) (addIndex : Value → Yield → m Value)
    (getindex : UnsafeIndexRequest Caller → U → Value → m E)
    (setindex : UnsafeIndexRequest Caller → D → Value → E → m StoreResult)
    (ambient : UnsafeAmbientContext Caller)
    (dest : D) (dstart : Value) (src : S) (sstart n : Value) : m D := do
  if ← assertType (← isZero n (int 0)) then return dest
  if ← assertType (← negative n (int 0)) then
    throw (.julia (.argumentError "n should be non-negative"))
  let destinds ← linearDest dest
  let srcinds ← linearSrc src
  let destOK ← assertType (← checkDest destinds dstart)
  let destOK ← if destOK then do
      let span ← addOne (← subtract (← lastDest destinds) dstart) (int 1)
      assertType (← lessEqual n span)
    else pure false
  if !destOK then throw (.julia .boundsError)
  let srcOK ← assertType (← checkSrc srcinds sstart)
  let srcOK ← if srcOK then do
      let span ← addOne (← subtract (← lastSrc srcinds) sstart) (int 1)
      assertType (← lessEqual n span)
    else pure false
  if !srcOK then throw (.julia .boundsError)
  let dstart ← toInt dstart
  let sstart ← toInt sstart
  let n ← toInt n
  let srcUnaliased ← unalias dest src
  let stop ← subtractOne n (int 1)
  let indices ← range (int 0) stop
  let request : UnsafeIndexRequest Caller :=
    { ambient := ambient, annotation := .inbounds, wrapperInlineHint := false }
  for i in indices do
    let sourceIndex ← addIndex sstart i
    let value ← getindex request srcUnaliased sourceIndex
    let destIndex ← addIndex dstart i
    let _ ← setindex request dest destIndex value
  return dest

/-- Full selected-call composition and source order, base/abstractarray.jl:1159-1182. -/
-- Source: base/abstractarray.jl:1159-1182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto!(B::AbstractVecOrMat{R}, ir_dest::AbstractRange{Int}, jr_dest::AbstractRange{Int},
--                A::AbstractVecOrMat{S}, ir_src::AbstractRange{Int}, jr_src::AbstractRange{Int}) where {R,S}
--     if length(ir_dest) != length(ir_src)
--         throw(ArgumentError(LazyString("source and destination must have same size (got ",
--             length(ir_src)," and ",length(ir_dest),")")))
--     end
--     if length(jr_dest) != length(jr_src)
--         throw(ArgumentError(LazyString("source and destination must have same size (got ",
--             length(jr_src)," and ",length(jr_dest),")")))
--     end
--     @boundscheck checkbounds(B, ir_dest, jr_dest)
--     @boundscheck checkbounds(A, ir_src, jr_src)
--     A′ = unalias(B, A)
--     jdest = first(jr_dest)
--     for jsrc in jr_src
--         idest = first(ir_dest)
--         for isrc in ir_src
--             @inbounds B[idest,jdest] = A′[isrc,jsrc]
--             idest += step(ir_dest)
--         end
--         jdest += step(jr_dest)
--     end
--     return B
-- end
-- /Source
def copytoBlock {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D S U Range Value Step Other E CheckResult StoreResult Caller : Type}
    [ForIn m Range I64]
    (length : Range → m Value) (notEqual : Value → Value → m (TypeAssertion Bool Other))
    (checkDest : D → Range → Range → m CheckResult)
    (checkSrc : S → Range → Range → m CheckResult)
    (unalias : D → S → m U) (first : Range → m Value) (step : Range → m Step)
    (add : Value → Step → m Value)
    (getindex : UnsafeIndexRequest Caller → U → I64 → I64 → m E)
    (setindex : UnsafeIndexRequest Caller → D → Value → Value → E → m StoreResult)
    (ambient : UnsafeAmbientContext Caller) (incomingBounds : Bool)
    (dest : D) (irDest jrDest : Range) (src : S) (irSrc jrSrc : Range) : m D := do
  let destRows ← length irDest
  let srcRows ← length irSrc
  if ← assertType (← notEqual destRows srcRows) then
    let _ ← length irSrc
    let _ ← length irDest
    throw (.julia (.argumentError "source and destination must have same size"))
  let destCols ← length jrDest
  let srcCols ← length jrSrc
  if ← assertType (← notEqual destCols srcCols) then
    let _ ← length jrSrc
    let _ ← length jrDest
    throw (.julia (.argumentError "source and destination must have same size"))
  if boundsActive ambient.checkBounds incomingBounds then
    let _ ← checkDest dest irDest jrDest
    let _ ← checkSrc src irSrc jrSrc
  let source ← unalias dest src
  let mut jdest ← first jrDest
  let request : UnsafeIndexRequest Caller :=
    { ambient := ambient, annotation := .inbounds, wrapperInlineHint := false }
  for jsrc in jrSrc do
    let mut idest ← first irDest
    for isrc in irSrc do
      let value ← getindex request source isrc jsrc
      let _ ← setindex request dest idest jdest value
      idest ← add idest (← step irDest)
    jdest ← add jdest (← step jrDest)
  return dest

/-- Comparison dispatch retains arbitrary length and result types, base/abstractarray.jl:1262. -/
-- Source: base/abstractarray.jl:1262-1262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(a::AbstractArray) = (length(a) == 0)
-- /Source
def isemptyArray {m : Type → Type} [Monad m] {A Length R : Type}
    (length : A → m Length) (equal : Length → I64 → m R) (a : A) : m R := do
  let count ← length a
  equal count (int 0)

/-- Endpoint conversion precedes construction; LinRange length uses its installed field model.
The selected type constructor and the constructor selected on its unfixed results retain effects.
Source: base/abstractarray.jl:1270. -/
-- Source: base/abstractarray.jl:1270-1272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function map(::Type{T}, r::LinRange) where T<:AbstractFloat
--     LinRange(T(r.start), T(r.stop), length(r))
-- end
-- /Source
def mapLinRange {m : Type → Type} [Monad m] {Source Converted Length R : Type}
    (convert : Source → m Converted) (construct : Converted → Converted → Length → m R)
    (range : JuliaLean.base.range.LinRange Source Length) : m R := do
  let start ← convert range.start
  let stop ← convert range.stop
  construct start stop (JuliaLean.base.range.length_LinRange range)

/-- Full selected-call composition and source order, base/abstractarray.jl:1287-1290. -/
-- Source: base/abstractarray.jl:1287-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _memory_offset(x::AbstractArray, I::Vararg{Any,N}) where {N}
--     J = _to_subscript_indices(x, I...)
--     return sum(map((i, s, o)->s*(i-o), J, strides(x), Tuple(first(CartesianIndices(x)))))*elsize(x)
-- end
-- /Source
def memoryOffsetArray {m : Type → Type} [Monad m]
    {A Input J Strides Cartesian First Origins Index Stride Origin Difference Product Products Total Size Offset : Type}
    (toSubscripts : A → Tuple Input → m J) (strides : A → m Strides)
    (cartesianIndices : A → m Cartesian) (first : Cartesian → m First)
    (tuple : First → m Origins)
    (subtract : Index → Origin → m Difference) (multiply : Stride → Difference → m Product)
    (map : (Index → Stride → Origin → m Product) → J → Strides → Origins → m Products)
    (sum : Products → m Total) (elsize : A → m Size) (multiplyTotal : Total → Size → m Offset)
    (array : A) (indices : Tuple Input) : m Offset := do
  let coordinates ← toSubscripts array indices
  let storageStrides ← strides array
  let cartesian ← cartesianIndices array
  let originIndex ← first cartesian
  let origins ← tuple originIndex
  let products ← map (fun index stride origin => do multiply stride (← subtract index origin))
    coordinates storageStrides origins
  let total ← sum products
  let size ← elsize array
  multiplyTotal total size

/-- Scalar vector indexing selects the unfixed array's public getter, base/abstractarray.jl:1390. -/
-- Source: base/abstractarray.jl:1390-1390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _getindex(::IndexLinear, A::AbstractVector, i::Int) = (@_propagate_inbounds_meta; getindex(A, i))  # ambiguity resolution in case packages specialize this (to be avoided if at all possible, but see Interpolations.jl)
-- /Source
def getindexLinearVector {m : Type → Type} {A R : Type}
    (getindex : A → I64 → m R) (a : A) (i : I64) : m R := getindex a i

/-- Full source ordering and runtime-selected dispatch, base/abstractarray.jl:1392-1397. -/
-- Source: base/abstractarray.jl:1392-1397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _getindex(::IndexLinear, A::AbstractArray, I::Vararg{Int,M}) where M
--     @inline
--     @boundscheck checkbounds(A, I...) # generally _to_linear_index requires bounds checking
--     @inbounds r = getindex(A, _to_linear_index(A, I...))
--     r
-- end
-- /Source
def getindexLinearMany {m : Type → Type} [Monad m] {A Index R CheckResult Caller : Type}
    (checkbounds : A → Tuple I64 → m CheckResult)
    (toLinear : A → Tuple I64 → m Index)
    (getindex : UnsafeIndexRequest Caller → A → Index → m R)
    (ambient : UnsafeAmbientContext Caller) (incomingBounds : Bool)
    (array : A) (indices : Tuple I64) : m R := do
  if boundsActive ambient.checkBounds incomingBounds then
    let _ ← checkbounds array indices
  let index ← toLinear array indices
  getindex { ambient := ambient, annotation := .inbounds, wrapperInlineHint := true } array index

/-- The selected conversion receives the original array and integer, base/abstractarray.jl:1414. -/
-- Source: base/abstractarray.jl:1414-1414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _to_subscript_indices(A::AbstractArray, i::Integer) = (@inline; _unsafe_ind2sub(A, i))
-- /Source
def toSubscriptsScalar {m : Type → Type} {A I R : Type}
    (unsafeInd2sub : A → I → m R) (a : A) (i : I) : m R := unsafeInd2sub a i

/-- The shape and index types are unfixed dispatch arguments, base/abstractarray.jl:1436. -/
-- Source: base/abstractarray.jl:1436-1436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _unsafe_ind2sub(sz, i) = (@inline; _ind2sub(sz, i))
-- /Source
def unsafeInd2sub {m : Type → Type} {Shape I R : Type}
    (ind2sub : Shape → I → m R) (shape : Shape) (i : I) : m R := ind2sub shape i

/-- Full source ordering and runtime-selected dispatch, base/abstractarray.jl:1487-1492. -/
-- Source: base/abstractarray.jl:1487-1492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _setindex!(::IndexLinear, A::AbstractArray, v, I::Vararg{Int,M}) where M
--     @inline
--     @boundscheck checkbounds(A, I...)
--     @inbounds r = setindex!(A, v, _to_linear_index(A, I...))
--     r
-- end
-- /Source
def setindexLinearMany {m : Type → Type} [Monad m] {A E Index R CheckResult Caller : Type}
    (checkbounds : A → Tuple I64 → m CheckResult)
    (toLinear : A → Tuple I64 → m Index)
    (setindex : UnsafeIndexRequest Caller → A → E → Index → m R)
    (ambient : UnsafeAmbientContext Caller) (incomingBounds : Bool)
    (array : A) (value : E) (indices : Tuple I64) : m R := do
  if boundsActive ambient.checkBounds incomingBounds then
    let _ ← checkbounds array indices
  let index ← toLinear array indices
  setindex { ambient := ambient, annotation := .inbounds, wrapperInlineHint := true } array value index

/-- Close the full pinned _isdisjoint overload recursion over native tuple fields.
All tuple tails are structural; no recursive source-body callback is supplied. -/
-- Source: base/abstractarray.jl:1606-1614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _isdisjoint(as::Tuple{}, bs::Tuple{}) = true
-- _isdisjoint(as::Tuple{}, bs::Tuple{UInt}) = true
-- _isdisjoint(as::Tuple{}, bs::Tuple) = true
-- _isdisjoint(as::Tuple{UInt}, bs::Tuple{}) = true
-- _isdisjoint(as::Tuple{UInt}, bs::Tuple{UInt}) = as[1] != bs[1]
-- _isdisjoint(as::Tuple{UInt}, bs::Tuple) = !(as[1] in bs)
-- _isdisjoint(as::Tuple, bs::Tuple{}) = true
-- _isdisjoint(as::Tuple, bs::Tuple{UInt}) = !(bs[1] in as)
-- _isdisjoint(as::Tuple, bs::Tuple) = !(as[1] in bs) && _isdisjoint(tail(as), bs)
-- /Source
def aliasDisjointLoop {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Element Other : Type} (ops : DisjointOps m Element Other) :
    List (AliasAtom Element) → List (AliasAtom Element) → m (AliasTruth Other)
  | [], _ => pure (.accepted true)
  | _, [] => pure (.accepted true)
  | [.word a], [.word b] => pure (.accepted (a != b))
  | [.word a], right => do aliasNot ops (← aliasInTuple ops (.word a) right)
  | left, [.word b] => do aliasNot ops (← aliasInTuple ops (.word b) left)
  | first :: rest, right => do
      let condition ← assertType (← aliasNot ops (← aliasInTuple ops first right))
      if condition then aliasDisjointLoop ops rest right else pure (.accepted false)

/-- The sole UInt field of the left tuple is represented directly, base/abstractarray.jl:1611. -/
-- Source: base/abstractarray.jl:1611-1611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _isdisjoint(as::Tuple{UInt}, bs::Tuple) = !(as[1] in bs)
-- /Source
def disjointWordLeft {m : Type → Type} [Monad m] {Element Other : Type}
    (ops : DisjointOps m Element Other) (left : JInt .u64) (right : Tuple (AliasAtom Element)) :
    m (AliasTruth Other) := do aliasNot ops (← aliasInTuple ops (.word left) right.values)

/-- The sole UInt field of the right tuple is represented directly, base/abstractarray.jl:1613. -/
-- Source: base/abstractarray.jl:1613-1613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _isdisjoint(as::Tuple, bs::Tuple{UInt}) = !(bs[1] in as)
-- /Source
def disjointWordRight {m : Type → Type} [Monad m] {Element Other : Type}
    (ops : DisjointOps m Element Other) (left : Tuple (AliasAtom Element)) (right : JInt .u64) :
    m (AliasTruth Other) := do aliasNot ops (← aliasInTuple ops (.word right) left.values)

/-- General fallback with its checked head access and Bool-context check, base/abstractarray.jl:1614. -/
-- Source: base/abstractarray.jl:1614-1614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _isdisjoint(as::Tuple, bs::Tuple) = !(as[1] in bs) && _isdisjoint(tail(as), bs)
-- /Source
def disjointGeneral {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Element Other : Type} (ops : DisjointOps m Element Other)
    (left right : Tuple (AliasAtom Element)) : m (AliasTruth Other) := do
  let first ← match tupleGet left.values (int 1) with
    | .ok value => pure value
    | .error error => throw error
  let condition ← assertType (← aliasNot ops (← aliasInTuple ops first right.values))
  if condition then aliasDisjointLoop ops left.values.tail right.values else pure (.accepted false)

/-- Preserve the membership closure, every selected read/write and evaluation order, base/abstractarray.jl:1644-1652. -/
-- Source: base/abstractarray.jl:1644-1652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function get!(X::AbstractVector{T}, A::AbstractVector, I::Union{AbstractRange,AbstractVector{Int}}, default::T) where T
--     # 1d is not linear indexing
--     ind = findall(in(axes1(A)), I)
--     X[ind] = A[I[ind]]
--     Xind = axes1(X)
--     X[first(Xind):first(ind)-1] = default
--     X[last(ind)+1:last(Xind)] = default
--     X
-- end
-- /Source
def getVector {m : Type → Type} [Monad m] {X A I Value Predicate E StoreResult : Type}
    (axesSrc : A → m Value) (axesDest : X → m Value)
    (contains : Value → Value → m Predicate)
    (findall : {collection : Value} → InPredicate m Value Predicate collection → I → m Value)
    (getIndices : I → Value → m Value) (getSource : A → Value → m Value)
    (setData : X → Value → Value → m StoreResult)
    (first last : Value → m Value)
    (subtract add : Value → I64 → m Value) (range : Value → Value → m Value)
    (setDefault : X → Value → E → m StoreResult)
    (dest : X) (source : A) (indices : I) (default : E) : m X := do
  let axis ← axesSrc source
  let ind ← findall (JuliaLean.base.operators.inUnary contains axis) indices
  let selected ← getIndices indices ind
  let values ← getSource source selected
  let _ ← setData dest ind values
  let axisDest ← axesDest dest
  let start ← first axisDest
  let stop ← subtract (← first ind) (int 1)
  let _ ← setDefault dest (← range start stop) default
  let start ← add (← last ind) (int 1)
  let stop ← last axisDest
  let _ ← setDefault dest (← range start stop) default
  return dest

/-- Preserve the membership closure, every selected read/write and evaluation order, base/abstractarray.jl:1653-1660. -/
-- Source: base/abstractarray.jl:1653-1660 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function get!(X::AbstractArray{T}, A::AbstractArray, I::Union{AbstractRange,AbstractVector{Int}}, default::T) where T
--     # Linear indexing
--     ind = findall(in(1:length(A)), I)
--     X[ind] = A[I[ind]]
--     fill!(view(X, 1:first(ind)-1), default)
--     fill!(view(X, last(ind)+1:length(X)), default)
--     X
-- end
-- /Source
def getArray {m : Type → Type} [Monad m] {X A I Value Predicate E View StoreResult FillResult : Type}
    (lengthSrc : A → m Value) (lengthDest : X → m Value)
    (rangeFromOne : I64 → Value → m Value) (range : Value → Value → m Value)
    (contains : Value → Value → m Predicate)
    (findall : {collection : Value} → InPredicate m Value Predicate collection → I → m Value)
    (getIndices : I → Value → m Value) (getSource : A → Value → m Value)
    (setData : X → Value → Value → m StoreResult)
    (first last : Value → m Value) (subtract add : Value → I64 → m Value)
    (view : X → Value → m View) (fill : View → E → m FillResult)
    (dest : X) (source : A) (indices : I) (default : E) : m X := do
  let domain ← rangeFromOne (int 1) (← lengthSrc source)
  let ind ← findall (JuliaLean.base.operators.inUnary contains domain) indices
  let selected ← getIndices indices ind
  let values ← getSource source selected
  let _ ← setData dest ind values
  let stop ← subtract (← first ind) (int 1)
  let headRange ← rangeFromOne (int 1) stop
  let _ ← fill (← view dest headRange) default
  let start ← add (← last ind) (int 1)
  let stop ← lengthDest dest
  let suffix ← range start stop
  let _ ← fill (← view dest suffix) default
  return dest

/-- Preserve the membership closure, every selected read/write and evaluation order, base/abstractarray.jl:1671-1672. -/
-- Source: base/abstractarray.jl:1671-1672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- get(A::AbstractArray, I::RangeVecIntList, default) =
--     get!(similar(A, typeof(default), index_shape(I...)), A, I, default)
-- /Source
def getScattered {m : Type → Type} [Monad m] {A I E Ty Shape B R : Type}
    (typeof : E → Ty) (indexShape : I → m Shape)
    (similar : A → Ty → Shape → m B) (get : B → A → I → E → m R)
    (source : A) (indices : I) (default : E) : m R := do
  let type := typeof default
  let shape ← indexShape indices
  let dest ← similar source type shape
  get dest source indices default

/-- The concrete empty promote_eltypeof method precedes concatenation; nonempty calls remain selected on their unfixed arguments. -/
-- Source: base/abstractarray.jl:1682-1682 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltypeof() = error()
-- /Source
def concatPromoteEltypeof {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {X Ty : Type} (selected : Tuple X → m Ty) (xs : Tuple X) : m Ty :=
  match xs.values with
  | [] => match (promoteEltypeofEmpty : Result Ty) with
      | .ok ty => pure ty
      | .error error => throw error
  | _ :: _ => selected xs

/-- Preserve the selected value's element-type operation, base/abstractarray.jl:1690. -/
-- Source: base/abstractarray.jl:1690-1690 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_eltype(v1) = eltype(v1)
-- /Source
def promoteEltypeOne {m : Type → Type} {A R : Type}
    (eltype : A → m R) (value : A) : m R := eltype value

/-- Source-mirrored complete dispatch domain, base/abstractarray.jl:1839. -/
-- Source: base/abstractarray.jl:1839-1839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cat_size(A::AbstractArray, d) = size(A, d)
-- /Source
def catSizeDimArray {m : Type → Type} {A D R : Type}
    (size : A → D → m R) (a : A) (d : D) : m R := size a d

/-- Source-mirrored complete dispatch domain, base/abstractarray.jl:1842. -/
-- Source: base/abstractarray.jl:1842-1842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cat_length(a::AbstractArray) = length(a)
-- /Source
def catLengthArray {m : Type → Type} {A R : Type}
    (length : A → m R) (a : A) : m R := length a

/-- Source-mirrored complete dispatch domain, base/abstractarray.jl:1845. -/
-- Source: base/abstractarray.jl:1845-1845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cat_ndims(a::AbstractArray) = ndims(a)
-- /Source
def catNdimsArray {m : Type → Type} {A R : Type}
    (ndims : A → m R) (a : A) : m R := ndims a

/-- Source-mirrored complete dispatch domain, base/abstractarray.jl:1869. -/
-- Source: base/abstractarray.jl:1869-1869 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _cat_size_shape(dims, shape) = shape
-- /Source
def catSizeShapeDone {D Shape : Type} (_ : D) (shape : Shape) : Shape := shape

/-- Source-mirrored complete dispatch domain, base/abstractarray.jl:1873. -/
-- Source: base/abstractarray.jl:1873-1873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _cshp(ndim::Int, ::Tuple{}, ::Tuple{}, nshape) = nshape
-- /Source
def cshpInitial {Shape : Type} (_ : I64) (shape : Shape) : Shape := shape

/-- Full source body with runtime-selected operations and unchanged error/effect order, base/abstractarray.jl:1897-1897. -/
-- Source: base/abstractarray.jl:1897-1897 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- dims2cat(::Val{dims}) where dims = dims2cat(dims)
-- /Source
def dims2catVal {m : Type → Type} {D R : Type}
    (dims2cat : D → m R) (dims : ValValue D) : m R := dims2cat dims.parameter

/-- Full source body with runtime-selected operations and unchanged error/effect order, base/abstractarray.jl:1905-1905. -/
-- Source: base/abstractarray.jl:1905-1905 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _cat(dims, X...) = _cat_t(dims, promote_eltypeof(X...), X...)
-- /Source
def catAny {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {D X Ty R : Type}
    (promote : Tuple X → m Ty) (typed : D → Ty → Tuple X → m R)
    (dimensions : D) (xs : Tuple X) : m R := do
  let t ← match xs.values with
    | [] => match (promoteEltypeofEmpty : Result Ty) with
        | .ok t => pure t
        | .error error => throw error
    | _ :: _ => promote xs
  typed dimensions t xs

/-- Concrete tuple reads and Int assertions surround selected operations on the unfixed dimensions, elements, type objects and array result. -/
-- Source: base/abstractarray.jl:1907-1915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _cat_t(dims, ::Type{T}, X...) where {T}
--     catdims = dims2cat(dims)
--     shape = cat_size_shape(catdims, X...)
--     A = cat_similar(X[1], T, shape)
--     if count(!iszero, catdims)::Int > 1
--         fill!(A, zero(T))
--     end
--     return __cat(A, shape, catdims, X...)
-- end
-- /Source
def catTyped {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {D Ty X CatDims Shape A Element ZeroResult Predicate Other E FillResult R : Type}
    (dims2cat : D → m CatDims) (sizeShape : CatDims → Tuple X → m Shape)
    (similar : X → Ty → Shape → m A)
    (iszero : Element → m ZeroResult) (notZero : ZeroResult → m Predicate)
    (count : (Element → m Predicate) → CatDims → m (TypeAssertion I64 Other))
    (zero : Ty → m E) (fill : A → E → m FillResult)
    (cat : A → Shape → CatDims → Tuple X → m R)
    (dims : D) (t : Ty) (xs : Tuple X) : m R := do
  let catdims ← dims2cat dims
  let shape ← sizeShape catdims xs
  let first ← match tupleGet xs.values (int 1) with
    | .ok first => pure first
    | .error error => throw error
  let array ← similar first t shape
  let n ← assertType (← count (fun element => do notZero (← iszero element)) catdims)
  if n.val > (int 1).val then
    let z ← zero t
    let _ ← fill array z
  cat array shape catdims xs

/-- Typed concatenation retains the requested type and every source argument, base/abstractarray.jl:2055. -/
-- Source: base/abstractarray.jl:2055-2055 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_vcat(::Type{T}, X...) where T = _cat_t(Val(1), T, X...)
-- /Source
def typedVcatAny {m : Type → Type} {Ty X R : Type}
    (cat : ValValue I64 → Ty → Tuple X → m R) (type : Ty) (values : Tuple X) : m R :=
  cat (valValue (int 1)) type values

/-- Typed concatenation retains the requested type and every source argument, base/abstractarray.jl:2056. -/
-- Source: base/abstractarray.jl:2056-2056 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_hcat(::Type{T}, X...) where T = _cat_t(Val(2), T, X...)
-- /Source
def typedHcatAny {m : Type → Type} {Ty X R : Type}
    (cat : ValValue I64 → Ty → Tuple X → m R) (type : Ty) (values : Tuple X) : m R :=
  cat (valValue (int 2)) type values

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2175. -/
-- Source: base/abstractarray.jl:2175-2175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- vcat(A::AbstractArray) = cat(A; dims=Val(1))
-- /Source
def vcatOneArray {m : Type → Type} {A R : Type}
    (cat : A → ValValue I64 → m R) (a : A) : m R := cat a (valValue (int 1))

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2176. -/
-- Source: base/abstractarray.jl:2176-2176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- vcat(A::AbstractArray, B::AbstractArray) = cat(A, B; dims=Val(1))
-- /Source
def vcatTwoArrays {m : Type → Type} {A B R : Type}
    (cat : A → B → ValValue I64 → m R) (a : A) (b : B) : m R :=
  cat a b (valValue (int 1))

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2179. -/
-- Source: base/abstractarray.jl:2179-2179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hcat(A::AbstractArray) = cat(A; dims=Val(2))
-- /Source
def hcatOneArray {m : Type → Type} {A R : Type}
    (cat : A → ValValue I64 → m R) (a : A) : m R := cat a (valValue (int 2))

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2180. -/
-- Source: base/abstractarray.jl:2180-2180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hcat(A::AbstractArray, B::AbstractArray) = cat(A, B; dims=Val(2))
-- /Source
def hcatTwoArrays {m : Type → Type} {A B R : Type}
    (cat : A → B → ValValue I64 → m R) (a : A) (b : B) : m R :=
  cat a b (valValue (int 2))

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2184. -/
-- Source: base/abstractarray.jl:2184-2184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_vcat(T::Type, A::AbstractArray) = _cat_t(Val(1), T, A)
-- /Source
def typedVcatOneArray {m : Type → Type} {Ty A R : Type}
    (cat : ValValue I64 → Ty → A → m R) (t : Ty) (a : A) : m R :=
  cat (valValue (int 1)) t a

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2185. -/
-- Source: base/abstractarray.jl:2185-2185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_vcat(T::Type, A::AbstractArray, B::AbstractArray) = _cat_t(Val(1), T, A, B)
-- /Source
def typedVcatTwoArrays {m : Type → Type} {Ty A B R : Type}
    (cat : ValValue I64 → Ty → A → B → m R) (t : Ty) (a : A) (b : B) : m R :=
  cat (valValue (int 1)) t a b

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2186. -/
-- Source: base/abstractarray.jl:2186-2186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_vcat(T::Type, A::AbstractArray...) = _cat_t(Val(1), T, A...)
-- /Source
def typedVcatArrayVarargs {m : Type → Type} {Ty A R : Type}
    (cat : ValValue I64 → Ty → Tuple A → m R) (t : Ty) (arrays : Tuple A) : m R :=
  cat (valValue (int 1)) t arrays

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2187. -/
-- Source: base/abstractarray.jl:2187-2187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_hcat(T::Type, A::AbstractArray) = _cat_t(Val(2), T, A)
-- /Source
def typedHcatOneArray {m : Type → Type} {Ty A R : Type}
    (cat : ValValue I64 → Ty → A → m R) (t : Ty) (a : A) : m R :=
  cat (valValue (int 2)) t a

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2188. -/
-- Source: base/abstractarray.jl:2188-2188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_hcat(T::Type, A::AbstractArray, B::AbstractArray) = _cat_t(Val(2), T, A, B)
-- /Source
def typedHcatTwoArrays {m : Type → Type} {Ty A B R : Type}
    (cat : ValValue I64 → Ty → A → B → m R) (t : Ty) (a : A) (b : B) : m R :=
  cat (valValue (int 2)) t a b

/-- Concatenation retains the Val-tagged dimension and complete argument arity, base/abstractarray.jl:2189. -/
-- Source: base/abstractarray.jl:2189-2189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_hcat(T::Type, A::AbstractArray...) = _cat_t(Val(2), T, A...)
-- /Source
def typedHcatArrayVarargs {m : Type → Type} {Ty A R : Type}
    (cat : ValValue I64 → Ty → Tuple A → m R) (t : Ty) (arrays : Tuple A) : m R :=
  cat (valValue (int 2)) t arrays

/-- Close empty promotion and preserve every selected argument and result, base/abstractarray.jl:2244. -/
-- Source: base/abstractarray.jl:2244-2244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hvcat(rows::Tuple{Vararg{Int}}, xs::AbstractArray...) = typed_hvcat(promote_eltype(xs...), rows, xs...)
-- /Source
def hvcatArrays {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {X Ty R : Type}
    (promote : Tuple X → m Ty) (typed : Ty → Tuple I64 → Tuple X → m R)
    (rows : Tuple I64) (xs : Tuple X) : m R :=
  JuliaLean.base.abstractarray.hvcatArrays (Models2Group6.concatPromoteEltype promote) typed rows xs

/-- Close the native row-shape dependency before selected concatenation, base/abstractarray.jl:2248. -/
-- Source: base/abstractarray.jl:2248-2248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_hvcat(::Type{T}, rows::Tuple{Vararg{Int}}, as::AbstractVecOrMat...) where T = typed_hvncat(T, rows_to_dimshape(rows), true, as...)
-- /Source
def typedHvcatArrays {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {Ty X R : Type}
    (typed : Ty → Sum (I64 × I64) (List I64 × List I64) → Bool → Tuple X → m R)
    (t : Ty) (rows : Models1Group3.MachineTuple I64) (xs : Tuple X) : m R := do
  let shape ← match Models1Group3.rowDimensions rows with
    | .ok shape => pure shape
    | .error error => throw error
  typed t shape true xs

/-- Close empty promotion and preserve every selected argument and result, base/abstractarray.jl:2275. -/
-- Source: base/abstractarray.jl:2275-2275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hvcat(rows::Tuple{Vararg{Int}}, xs...) = typed_hvcat(promote_eltypeof(xs...), rows, xs...)
-- /Source
def hvcatAny {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {X Ty R : Type}
    (promote : Tuple X → m Ty) (typed : Ty → Tuple I64 → Tuple X → m R)
    (rows : Tuple I64) (xs : Tuple X) : m R :=
  JuliaLean.base.abstractarray.hvcatAny (concatPromoteEltypeof promote) typed rows xs

/-- Close empty promotion and preserve every selected argument and result, base/abstractarray.jl:2277. -/
-- Source: base/abstractarray.jl:2277-2277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hvcat(rows::Tuple{Vararg{Int}}, xs::Union{AbstractArray,Number}...) = typed_hvcat(promote_eltypeof(xs...), rows, xs...)
-- /Source
def hvcatMixed {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {X Ty R : Type}
    (promote : Tuple X → m Ty) (typed : Ty → Tuple I64 → Tuple X → m R)
    (rows : Tuple I64) (xs : Tuple X) : m R :=
  JuliaLean.base.abstractarray.hvcatMixed (concatPromoteEltypeof promote) typed rows xs

/-- Close the native row-shape dependency before selected concatenation, base/abstractarray.jl:2292. -/
-- Source: base/abstractarray.jl:2292-2292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_hvcat(::Type{T}, rows::Tuple{Vararg{Int}}, as...) where T = typed_hvncat(T, rows_to_dimshape(rows), true, as...)
-- /Source
def typedHvcatAny {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {Ty X R : Type}
    (typed : Ty → Sum (I64 × I64) (List I64 × List I64) → Bool → Tuple X → m R)
    (t : Ty) (rows : Models1Group3.MachineTuple I64) (xs : Tuple X) : m R := do
  let shape ← match Models1Group3.rowDimensions rows with
    | .ok shape => pure shape
    | .error error => throw error
  typed t shape true xs

/-- Close empty promotion and preserve every selected argument and result, base/abstractarray.jl:2385. -/
-- Source: base/abstractarray.jl:2385-2385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool, xs...) = _typed_hvncat(promote_eltypeof(xs...), dimsshape, row_first, xs...)
-- /Source
def hvncatPromote {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {D X Ty R : Type}
    (promote : Tuple X → m Ty) (typed : Ty → D → Bool → Tuple X → m R)
    (dimensions : D) (rowFirst : Bool) (xs : Tuple X) : m R :=
  JuliaLean.base.abstractarray.hvncatPromote (concatPromoteEltypeof promote) typed dimensions rowFirst xs

/-- Close empty promotion and preserve every selected argument and result, base/abstractarray.jl:2388. -/
-- Source: base/abstractarray.jl:2388-2388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _hvncat(dimsshape::Union{Tuple, Int}, row_first::Bool, xs::AbstractArray...) = _typed_hvncat(promote_eltype(xs...), dimsshape, row_first, xs...)
-- /Source
def hvncatArrays {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {D X Ty R : Type}
    (promote : Tuple X → m Ty) (typed : Ty → D → Bool → Tuple X → m R)
    (dimensions : D) (rowFirst : Bool) (xs : Tuple X) : m R :=
  JuliaLean.base.abstractarray.hvncatArrays (Models2Group6.concatPromoteEltype promote) typed dimensions rowFirst xs

/-- The frontend constructs a Val type token before selected concatenation, base/abstractarray.jl:2393. -/
-- Source: base/abstractarray.jl:2393-2393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typed_hvncat(T::Type, dim::Int, xs...) = _typed_hvncat(T, Val(dim), xs...)
-- /Source
def typedHvncatDim {m : Type → Type} {Ty X R : Type}
    (typed : Ty → ValValue I64 → Tuple X → m R)
    (t : Ty) (dimension : I64) (xs : Tuple X) : m R :=
  typed t (valValue dimension) xs

/-- The source's four rejecting 0-dimensional methods call the installed fixed error helper. -/
-- Source: base/abstractarray.jl:2397-2397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(::Type, ::Val{0}) = _typed_hvncat_0d_only_one()
-- /Source
def typedHvncatZeroEmpty {Ty R : Type} (_ : Ty) : Result R := typedHvncatZeroOnlyOne

/-- Fixed helper composition, base/abstractarray.jl:2401. -/
-- Source: base/abstractarray.jl:2401-2401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(::Type, ::Val{0}, ::Any...) = _typed_hvncat_0d_only_one()
-- /Source
def typedHvncatZeroAnyMany {Ty X R : Type} (_ : Ty) (_ : Tuple X) : Result R :=
  typedHvncatZeroOnlyOne

/-- Fixed helper composition, base/abstractarray.jl:2402. -/
-- Source: base/abstractarray.jl:2402-2402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(::Type, ::Val{0}, ::Number...) = _typed_hvncat_0d_only_one()
-- /Source
def typedHvncatZeroNumbersMany {Ty X R : Type} (_ : Ty) (_ : Tuple X) : Result R :=
  typedHvncatZeroOnlyOne

/-- Fixed helper composition, base/abstractarray.jl:2403. -/
-- Source: base/abstractarray.jl:2403-2403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(::Type, ::Val{0}, ::AbstractArray...) = _typed_hvncat_0d_only_one()
-- /Source
def typedHvncatZeroArraysMany {Ty X R : Type} (_ : Ty) (_ : Tuple X) : Result R :=
  typedHvncatZeroOnlyOne

/-- Row-first metadata is intentionally unused in this native-dimension overload, base/abstractarray.jl:2409. -/
-- Source: base/abstractarray.jl:2409-2409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @constprop :aggressive _typed_hvncat(T::Type, dim::Int, ::Bool, xs...) = _typed_hvncat(T, Val(dim), xs...) # catches from _hvncat type promoters
-- /Source
def typedHvncatDimFlag {m : Type → Type} {Ty X R : Type}
    (typed : Ty → ValValue I64 → Tuple X → m R)
    (t : Ty) (dimension : I64) (_rowFirst : Bool) (xs : Tuple X) : m R :=
  typed t (valValue dimension) xs

/-- Native tuple operations and source checks precede selected concatenation, base/abstractarray.jl:2492-2492. -/
-- Source: base/abstractarray.jl:2492-2492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(T::Type, ::Tuple{}, ::Bool, x...) = _typed_hvncat(T, Val(0), x...)
-- /Source
def typedHvncatEmptyShape {m : Type → Type} {Ty X R : Type}
    (typed : Ty → ValValue I64 → Tuple X → m R)
    (t : Ty) (_rowFirst : Bool) (xs : Tuple X) : m R := typed t (valValue (int 0)) xs

/-- Native tuple operations and source checks precede selected concatenation, base/abstractarray.jl:2498-2498. -/
-- Source: base/abstractarray.jl:2498-2498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typed_hvncat(T::Type, dims::Tuple{Int}, ::Bool, as...) = _typed_hvncat_1d(T, dims[1], Val(false), as...)
-- /Source
def typedHvncatOneDimension {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty X R : Type} (typed : Ty → I64 → ValValue Bool → Tuple X → m R)
    (t : Ty) (dimensions : {tuple : Tuple I64 // tuple.values.length = 1})
    (_rowFirst : Bool) (xs : Tuple X) : m R := do
  let dimension ← match tupleGet dimensions.val.values (int 1) with
    | .ok value => pure value
    | .error error => throw error
  typed t dimension (valValue false) xs

/-- Native tuple operations and source checks precede selected concatenation, base/abstractarray.jl:2501-2512. -/
-- Source: base/abstractarray.jl:2501-2512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat_1d(::Type{T}, ds::Int, ::Val{row_first}, as...) where {T, row_first}
--     lengthas = length(as)
--     ds > 0 ||
--         throw(ArgumentError("`dimsshape` argument must consist of positive integers"))
--     lengthas == ds ||
--         throw(ArgumentError("number of elements does not match `dimshape` argument; expected $ds, got $lengthas"))
--     if row_first
--         return _typed_hvncat(T, Val(2), as...)
--     else
--         return _typed_hvncat(T, Val(1), as...)
--     end
-- end
-- /Source
def typedHvncat1d {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty X R Other : Type} (typed : Ty → ValValue I64 → Tuple X → m R)
    (t : Ty) (dimension : I64) (rowFirst : TypeAssertion Bool Other) (xs : Tuple X) : m R := do
  let lengthas := Models2Group6.tupleFieldCount xs
  if !(dimension.val > (int 0).val) then
    throw (.julia (.argumentError "`dimsshape` argument must consist of positive integers"))
  if !(lengthas == dimension) then
    throw (.julia (.argumentError ("number of elements does not match `dimshape` argument; expected " ++
      toString dimension.val ++ ", got " ++ toString lengthas.val)))
  if ← assertType rowFirst then
    typed t (valValue (int 2)) xs
  else
    typed t (valValue (int 1)) xs

/-- Native tuple operations and source checks precede selected concatenation, base/abstractarray.jl:2732-2736. -/
-- Source: base/abstractarray.jl:2732-2736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _typed_hvncat(T::Type, shape::Tuple{Tuple}, row_first::Bool, xs...)
--     length(shape[1]) > 0 ||
--         throw(ArgumentError("each level of `shape` argument must have at least one value"))
--     return _typed_hvncat_1d(T, shape[1][1], Val(row_first), xs...)
-- end
-- /Source
def typedHvncatOneShape {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Ty D X R : Type} (typed : Ty → D → ValValue Bool → Tuple X → m R)
    (t : Ty) (shape : {tuple : Tuple (Tuple D) // tuple.values.length = 1})
    (rowFirst : Bool) (xs : Tuple X) : m R := do
  let firstShape ← match tupleGet shape.val.values (int 1) with
    | .ok value => pure value
    | .error error => throw error
  if !((Models2Group6.tupleFieldCount firstShape).val > (int 0).val) then
    throw (.julia (.argumentError "each level of `shape` argument must have at least one value"))
  let firstShape ← match tupleGet shape.val.values (int 1) with
    | .ok value => pure value
    | .error error => throw error
  let dimension ← match tupleGet firstShape.values (int 1) with
    | .ok value => pure value
    | .error error => throw error
  typed t dimension (valValue rowFirst) xs

/-- Construct the actual Generator representation before selected collection/stacking, base/abstractarray.jl:2996. -/
-- Source: base/abstractarray.jl:2996-2996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- stack(f, iter; dims::D=:) where {D} = _stack(dims, f(x) for x in iter)
-- /Source
def stackMap {m : Type → Type} {D Iterator Fn R : Type}
    (stack : D → JuliaLean.base.generator.Generator Iterator (ApplyClosure Fn) → m R)
    (dims : D) (f : Fn) (iterator : Iterator) : m R :=
  stack dims ⟨⟨f⟩, iterator⟩

/-- Construct the actual Generator representation before selected collection/stacking, base/abstractarray.jl:2997. -/
-- Source: base/abstractarray.jl:2997-2997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- stack(f, xs, yzs...; dims::D=:) where {D} = _stack(dims, f(xy...) for xy in zip(xs, yzs...))
-- /Source
def stackZipMap {m : Type → Type} [Monad m] {D Iterator Other Zipped Fn R : Type}
    (zip : Iterator → Tuple Other → m Zipped)
    (stack : D → JuliaLean.base.generator.Generator Zipped (SplatClosure Fn) → m R)
    (dims : D) (f : Fn) (iterator : Iterator) (others : Tuple Other) : m R := do
  let zipped ← zip iterator others
  stack dims ⟨⟨f⟩, zipped⟩

/-- Native range construction uses the installed wrapping UnitRange model, base/abstractarray.jl:3099. -/
-- Source: base/abstractarray.jl:3099-3099 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _ensure_array(x) = 1:0  # passed to similar, makes stack's output an Array
-- /Source
def ensureArrayOther {A : Type} (_ : A) : Models2Group6.NativeIntUnitRange :=
  Models2Group6.nativeIntUnitRange (int 1) (int 0)

/-- Full generic comparison body, preserving non-Bool type errors, selected effects and source evaluation order, base/abstractarray.jl:3106-3117. -/
-- Source: base/abstractarray.jl:3106-3117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isequal(A::AbstractArray, B::AbstractArray)
--     if A === B return true end
--     if axes(A) != axes(B)
--         return false
--     end
--     for (a, b) in zip(A, B)
--         if !isequal(a, b)
--             return false
--         end
--     end
--     return true
-- end
-- /Source
def arrayIsequal {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B AxA AxB E F Z Equal Other : Type} [ForIn m Z (E × F)]
    (identical : A → B → Bool) (axesA : A → m AxA) (axesB : B → m AxB)
    (notEqualAxes : AxA → AxB → m (TypeAssertion Bool Other))
    (zip : A → B → m Z) (isequal : E → F → m Equal)
    (notEqual : Equal → m (TypeAssertion Bool Other)) (a : A) (b : B) : m Bool := do
  if identical a b then return true
  let axisA ← axesA a
  let axisB ← axesB b
  if ← assertType (← notEqualAxes axisA axisB) then return false
  for (x, y) in (← zip a b) do
    if ← assertType (← notEqual (← isequal x y)) then return false
  return true

/-- Full generic comparison body, preserving non-Bool type errors, selected effects and source evaluation order, base/abstractarray.jl:3119-3128. -/
-- Source: base/abstractarray.jl:3119-3128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cmp(A::AbstractVector, B::AbstractVector)
--     ai1, bi1 = firstindex(A), firstindex(B)
--     isequal(ai1, bi1) || return cmp(ai1, bi1)
--     for (a, b) in zip(A, B)
--         if !isequal(a, b)
--             return isless(a, b) ? -1 : 1
--         end
--     end
--     return cmp(length(A), length(B))
-- end
-- /Source
def arrayCmp {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B FirstA FirstB E F Z Equal LengthA LengthB Other OtherCmp : Type}
    [ForIn m Z (E × F)]
    (firstA : A → m FirstA) (firstB : B → m FirstB)
    (equalFirst : FirstA → FirstB → m (TypeAssertion Bool Other))
    (cmpFirst : FirstA → FirstB → m (Models2Group6.RuntimeValue OtherCmp))
    (zip : A → B → m Z) (isequal : E → F → m Equal)
    (notEqual : Equal → m (TypeAssertion Bool Other))
    (isless : E → F → m (TypeAssertion Bool Other))
    (lengthA : A → m LengthA) (lengthB : B → m LengthB)
    (cmpLength : LengthA → LengthB → m (Models2Group6.RuntimeValue OtherCmp))
    (a : A) (b : B) : m (Models2Group6.RuntimeValue OtherCmp) := do
  let ai1 ← firstA a
  let bi1 ← firstB b
  if !(← assertType (← equalFirst ai1 bi1)) then return ← cmpFirst ai1 bi1
  for (x, y) in (← zip a b) do
    if ← assertType (← notEqual (← isequal x y)) then
      if ← assertType (← isless x y) then return .inl (int (-1)) else return .inl (int 1)
  let na ← lengthA a
  let nb ← lengthB b
  cmpLength na nb

/-- Full generic comparison body, preserving non-Bool type errors, selected effects and source evaluation order, base/abstractarray.jl:3145-3145. -/
-- Source: base/abstractarray.jl:3145-3145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isless(A::AbstractVector, B::AbstractVector) = cmp(A, B) < 0
-- /Source
def arrayIsless {m : Type → Type} [Monad m] {A B Cmp R : Type}
    (cmp : A → B → m Cmp) (less : Cmp → I64 → m R) (a : A) (b : B) : m R := do
  less (← cmp a b) (int 0)

/-- Runtime type parameters remain type objects in selected OrderStyle dispatch, base/abstractarray.jl:3147. -/
-- Source: base/abstractarray.jl:3147-3147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- OrderStyle(::Type{<:AbstractVector{T}}) where {T} = OrderStyle(T)
-- /Source
def orderStyleVector {m : Type → Type} {Ty R : Type}
    (orderStyle : Ty → m R) (elementType : Ty) : m R := orderStyle elementType

/-- Full generic comparison body, preserving non-Bool type errors, selected effects and source evaluation order, base/abstractarray.jl:3149-3163. -/
-- Source: base/abstractarray.jl:3149-3163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function (==)(A::AbstractArray, B::AbstractArray)
--     if axes(A) != axes(B)
--         return false
--     end
--     anymissing = false
--     for (a, b) in zip(A, B)
--         eq = (a == b)
--         if ismissing(eq)
--             anymissing = true
--         elseif !eq
--             return false
--         end
--     end
--     return anymissing ? missing : true
-- end
-- /Source
def arrayEqual {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A B AxA AxB E F Z Equal Other : Type} [ForIn m Z (E × F)]
    (axesA : A → m AxA) (axesB : B → m AxB)
    (notEqualAxes : AxA → AxB → m (TypeAssertion Bool Other))
    (zip : A → B → m Z) (equal : E → F → m Equal)
    (isMissing notEqual : Equal → m (TypeAssertion Bool Other))
    (a : A) (b : B) : m (Option Bool) := do
  let axisA ← axesA a
  let axisB ← axesB b
  if ← assertType (← notEqualAxes axisA axisB) then return some false
  let mut anyMissing := false
  for (x, y) in (← zip a b) do
    let eq ← equal x y
    if ← assertType (← isMissing eq) then
      anyMissing := true
    else if ← assertType (← notEqual eq) then
      return some false
  return if anyMissing then none else some true

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3167-3170. -/
-- Source: base/abstractarray.jl:3167-3170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _sub2ind(A::AbstractArray, I...)
--     @inline
--     _sub2ind(axes(A), I...)
-- end
-- /Source
def sub2indArray {m : Type → Type} [Monad m] {A Axis I R : Type}
    (axes : A → m Axis) (sub2ind : Axis → Tuple I → m R) (a : A) (indices : Tuple I) : m R := do
  sub2ind (← axes a) indices

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3172-3175. -/
-- Source: base/abstractarray.jl:3172-3175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _ind2sub(A::AbstractArray, ind)
--     @inline
--     _ind2sub(axes(A), ind)
-- end
-- /Source
def ind2subArray {m : Type → Type} [Monad m] {A Axis I R : Type}
    (axes : A → m Axis) (ind2sub : Axis → I → m R) (a : A) (index : I) : m R := do
  ind2sub (← axes a) index

/-- The empty-dimension entry initializes the native stride and index, base/abstractarray.jl:3181. -/
-- Source: base/abstractarray.jl:3181-3181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind(::Tuple{}, I::Integer...) = (@inline; _sub2ind_recurse((), 1, 1, I...))
-- /Source
def subscriptEmpty {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Other Dimension Container : Type} (ops : SubscriptOps m Other Dimension Container)
    (coordinates : Tuple (SubscriptValue Other)) : m (SubscriptValue Other) :=
  subscriptLoop ops (.tuple ⟨[], by simp⟩) (.native (int 1)) (.native (int 1)) coordinates.values

/-- Integer dimension tuples initialize native stride and index, base/abstractarray.jl:3184. -/
-- Source: base/abstractarray.jl:3184-3184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind(dims::DimsInteger, I::Integer...) = (@inline; _sub2ind_recurse(dims, 1, 1, I...))
-- /Source
def subscriptDimensions {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Other Dimension Container : Type} (ops : SubscriptOps m Other Dimension Container)
    (dimensions : Tuple Dimension) (coordinates : Tuple (SubscriptValue Other)) : m (SubscriptValue Other) :=
  subscriptLoop ops (.tuple dimensions) (.native (int 1)) (.native (int 1)) coordinates.values

/-- Axis tuples initialize native stride and index, base/abstractarray.jl:3185. -/
-- Source: base/abstractarray.jl:3185-3185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind(inds::Indices, I::Integer...) = (@inline; _sub2ind_recurse(inds, 1, 1, I...))
-- /Source
def subscriptAxes {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Other Dimension Container : Type} (ops : SubscriptOps m Other Dimension Container)
    (axes : Tuple Dimension) (coordinates : Tuple (SubscriptValue Other)) : m (SubscriptValue Other) :=
  subscriptLoop ops (.tuple axes) (.native (int 1)) (.native (int 1)) coordinates.values

/-- Empty dimensions consume every coordinate without a recursive callback, base/abstractarray.jl:3194. -/
-- Source: base/abstractarray.jl:3194-3197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _sub2ind_recurse(::Tuple{}, L, ind, i::Integer, I::Integer...)
--     @inline
--     _sub2ind_recurse((), L, ind+(i-1)*L, I...)
-- end
-- /Source
def subscriptRecurseEmpty {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Other Dimension Container : Type} (ops : SubscriptOps m Other Dimension Container)
    (stride index coordinate : SubscriptValue Other) (rest : Tuple (SubscriptValue Other)) :
    m (SubscriptValue Other) := do
  let offset ← subscriptSubtract ops coordinate (.native (int 1))
  let product ← subscriptMultiply ops offset stride
  subscriptLoop ops (.tuple ⟨[], by simp⟩) stride (← subscriptAdd ops index product) rest.values

/-- Head access precedes tail, stride and offset evaluation, base/abstractarray.jl:3198. -/
-- Source: base/abstractarray.jl:3198-3202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _sub2ind_recurse(inds, L, ind, i::Integer, I::Integer...)
--     @inline
--     r1 = inds[1]
--     _sub2ind_recurse(tail(inds), nextL(L, r1), ind+offsetin(i, r1)*L, I...)
-- end
-- /Source
def subscriptRecurse {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Other Dimension Container : Type} (ops : SubscriptOps m Other Dimension Container)
    (shape : SubscriptShape Dimension Container) (stride index coordinate : SubscriptValue Other)
    (rest : Tuple (SubscriptValue Other)) : m (SubscriptValue Other) := do
  let dimension ← subscriptHead ops shape
  let tail ← subscriptTail ops shape
  let next ← ops.nextL stride dimension
  let offset ← ops.offsetin coordinate dimension
  let product ← subscriptMultiply ops offset stride
  subscriptLoop ops tail next (← subscriptAdd ops index product) rest.values

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3204-3204. -/
-- Source: base/abstractarray.jl:3204-3204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- nextL(L, l::Integer) = L*l
-- /Source
def nextLInteger {m : Type → Type} {L I R : Type}
    (multiply : L → I → m R) (stride : L) (dimension : I) : m R := multiply stride dimension

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3205-3205. -/
-- Source: base/abstractarray.jl:3205-3205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- nextL(L, r::AbstractUnitRange) = L*length(r)
-- /Source
def nextLRange {m : Type → Type} [Monad m] {L Range Length R : Type}
    (length : Range → m Length) (multiply : L → Length → m R)
    (stride : L) (axis : Range) : m R := do multiply stride (← length axis)

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3206-3206. -/
-- Source: base/abstractarray.jl:3206-3206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- nextL(L, r::Slice) = L*length(r.indices)
-- /Source
def nextLSlice {m : Type → Type} [Monad m] {L Axis Length R : Type}
    (length : Axis → m Length) (multiply : L → Length → m R)
    (stride : L) (slice : JuliaLean.base.indices.Slice Axis) : m R := do
  multiply stride (← length slice.indices)

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3207-3207. -/
-- Source: base/abstractarray.jl:3207-3207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- offsetin(i, l::Integer) = i-1
-- /Source
def offsetinInteger {m : Type → Type} {I L R : Type}
    (subtract : I → I64 → m R) (index : I) (_length : L) : m R := subtract index (int 1)

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3208-3208. -/
-- Source: base/abstractarray.jl:3208-3208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- offsetin(i, r::AbstractUnitRange) = i-first(r)
-- /Source
def offsetinRange {m : Type → Type} [Monad m] {I Axis First R : Type}
    (first : Axis → m First) (subtract : I → First → m R) (index : I) (axis : Axis) : m R := do
  subtract index (← first axis)

/-- Full source ordering and runtime-selected dispatch, base/abstractarray.jl:3210-3210. -/
-- Source: base/abstractarray.jl:3210-3210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _ind2sub(::Tuple{}, ind::Integer) = (@inline; ind == 1 ? () : throw(BoundsError()))
-- /Source
def ind2subEmpty {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {I Other : Type}
    (equal : I → I64 → m (TypeAssertion Bool Other)) (index : I) : m Unit := do
  if ← assertType (← equal index (int 1)) then pure () else throw (.julia .boundsError)

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3217-3217. -/
-- Source: base/abstractarray.jl:3217-3217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _ind2sub_recurse(::Tuple{}, ind) = (ind+1,)
-- /Source
def ind2subRecurseEmpty {m : Type → Type} [Monad m] {I R : Type}
    (add : I → I64 → m R) (index : I) : m (List R) := do
  return [← add index (int 1)]

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3218-3221. -/
-- Source: base/abstractarray.jl:3218-3221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _ind2sub_recurse(indslast::NTuple{1}, ind)
--     @inline
--     (_lookup(ind, indslast[1]),)
-- end
-- /Source
def ind2subRecurseLast {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Axis I R : Type} (lookup : I → Axis → m R)
    (axes : {tuple : Tuple Axis // tuple.values.length = 1}) (index : I) : m (List R) := do
  let axis ← match tupleGet axes.val.values (int 1) with
    | .ok value => pure value
    | .error error => throw error
  return [← lookup index axis]

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3231-3231. -/
-- Source: base/abstractarray.jl:3231-3231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _lookup(ind, d::Integer) = ind+1
-- /Source
def lookupInteger {m : Type → Type} {I D R : Type}
    (add : I → I64 → m R) (index : I) (_dimension : D) : m R := add index (int 1)

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3232-3232. -/
-- Source: base/abstractarray.jl:3232-3232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _lookup(ind, r::AbstractUnitRange) = ind+first(r)
-- /Source
def lookupRange {m : Type → Type} [Monad m] {I Axis First R : Type}
    (first : Axis → m First) (add : I → First → m R) (index : I) (axis : Axis) : m R := do
  add index (← first axis)

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3238-3239. -/
-- Source: base/abstractarray.jl:3238-3239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind(inds::Tuple{OneTo}, I1::AbstractVector{T}, I::AbstractVector{T}...) where {T<:Integer} =
--     _sub2ind_vecs(inds, I1, I...)
-- /Source
def sub2indVectorsOneTo {m : Type → Type} {Axis V R : Type}
    (vectors : Axis → V → Tuple V → m R) (axes : Axis) (first : V) (rest : Tuple V) : m R :=
  vectors axes first rest

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3240-3241. -/
-- Source: base/abstractarray.jl:3240-3241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind(inds::Union{DimsInteger,Indices}, I1::AbstractVector{T}, I::AbstractVector{T}...) where {T<:Integer} =
--     _sub2ind_vecs(inds, I1, I...)
-- /Source
def sub2indVectors {m : Type → Type} {Axis V R : Type}
    (vectors : Axis → V → Tuple V → m R) (axes : Axis) (first : V) (rest : Tuple V) : m R :=
  vectors axes first rest

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3253-3260. -/
-- Source: base/abstractarray.jl:3253-3260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _sub2ind!(Iout, inds, Iinds, I)
--     @noinline
--     for i in Iinds
--         # Iout[i] = _sub2ind(inds, map(Ij -> Ij[i], I)...)
--         Iout[i] = sub2ind_vec(inds, i, I)
--     end
--     Iout
-- end
-- /Source
def sub2indFill {m : Type → Type} [Monad m] {Out Axes Indices I V E StoreResult : Type}
    [ForIn m Indices I] (sub2indVec : Axes → I → V → m E)
    (setindex : Out → I → E → m StoreResult)
    (out : Out) (axes : Axes) (indices : Indices) (vectors : V) : m Out := do
  for index in indices do
    let value ← sub2indVec axes index vectors
    let _ ← setindex out index value
  return out

/-- Construct the actual Generator representation before selected collection/stacking, base/abstractarray.jl:3491. -/
-- Source: base/abstractarray.jl:3491-3491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map(f, A::AbstractArray) = collect_similar(A, Generator(f,A))
-- /Source
def mapArray {m : Type → Type} {A Fn Ty R : Type}
    (collectSimilar : A → GeneratorValue A Fn Ty → m R)
    (function : GeneratorFunction Fn Ty) (array : A) : m R :=
  collectSimilar array (constructGenerator function array)

/-- Construct the actual Generator representation before selected collection/stacking, base/abstractarray.jl:3521. -/
-- Source: base/abstractarray.jl:3521-3521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map(f, A) = collect(Generator(f,A)) # default to returning an Array for `map` on general iterators
-- /Source
def mapIterator {m : Type → Type} {Iterator Fn Ty R : Type}
    (collect : GeneratorValue Iterator Fn Ty → m R)
    (function : GeneratorFunction Fn Ty) (iterator : Iterator) : m R :=
  collect (constructGenerator function iterator)

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3593-3596. -/
-- Source: base/abstractarray.jl:3593-3596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function map!(f::F, dest::AbstractArray, As::AbstractArray...) where {F}
--     @assert !isempty(As) "should dispatch to map!(f, A)"
--     map_n!(f, dest, As)
-- end
-- /Source
def mapInplaceMany {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {Fn A Source R : Type} (mapN : Fn → A → Tuple Source → m R)
    (f : Fn) (dest : A) (arrays : Tuple Source) : m R := do
  if arrays.values.isEmpty then
    throw (.assertionError "should dispatch to map!(f, A)")
  mapN f dest arrays

/-- Complete source body with selected operations on the unfixed runtime arguments, base/abstractarray.jl:3618-3618. -/
-- Source: base/abstractarray.jl:3618-3618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map!(f::F, inout::AbstractArray) where F = map!(f, inout, inout)
-- /Source
def mapInplaceSelf {m : Type → Type} {Fn A R : Type}
    (map : Fn → A → A → m R) (f : Fn) (array : A) : m R := map f array array

/-- Full source body with runtime-selected operations and unchanged error/effect order, base/abstractarray.jl:3649-3656. -/
-- Source: base/abstractarray.jl:3649-3656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function push!(a::AbstractVector{T}, item) where T
--     # convert first so we don't grow the array if the assignment won't work
--     itemT = item isa T ? item : convert(T, item)::T
--     new_length = length(a) + 1
--     resize!(a, new_length)
--     a[end] = itemT
--     return a
-- end
-- /Source
def pushOne {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Element Other Wrong Length NewLength Index ResizeResult StoreResult : Type}
    (convert : Other → m (TypeAssertion Element Wrong))
    (length : A → m Length) (add : Length → I64 → m NewLength)
    (resize : A → NewLength → m ResizeResult) (lastindex : A → m Index)
    (setindex : A → Index → Element → m StoreResult)
    (array : A) (item : TypeAssertion Element Other) : m A := do
  let itemT ← match item with
    | .accepted value => pure value
    | .rejected value => do assertType (← convert value)
  let newLength ← add (← length array) (int 1)
  let _ ← resize array newLength
  let index ← lastindex array
  let _ ← setindex array index itemT
  return array

/-- Full source body with runtime-selected operations and unchanged error/effect order, base/abstractarray.jl:3659-3664. -/
-- Source: base/abstractarray.jl:3659-3664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function push!(a::AbstractVector{Any}, @nospecialize x)
--     new_length = length(a) + 1
--     resize!(a, new_length)
--     a[end] = x
--     return a
-- end
-- /Source
def pushAny {m : Type → Type} [Monad m]
    {A Element Length NewLength Index ResizeResult StoreResult : Type}
    (length : A → m Length) (add : Length → I64 → m NewLength)
    (resize : A → NewLength → m ResizeResult) (lastindex : A → m Index)
    (setindex : A → Index → Element → m StoreResult) (array : A) (item : Element) : m A := do
  let newLength ← add (← length array) (int 1)
  let _ ← resize array newLength
  let index ← lastindex array
  let _ ← setindex array index item
  return array

/-- Full source body with runtime-selected operations and unchanged error/effect order, base/abstractarray.jl:3665-3675. -/
-- Source: base/abstractarray.jl:3665-3675 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function push!(a::AbstractVector{Any}, @nospecialize x...)
--     @_terminates_locally_meta
--     na = length(a)
--     nx = length(x)
--     resize!(a, na + nx)
--     e = lastindex(a) - nx
--     for i = 1:nx
--         a[e+i] = x[i]
--     end
--     return a
-- end
-- /Source
def pushManyAny {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Element Length NewLength Last End Index ResizeResult StoreResult : Type}
    (length : A → m Length) (addLength : Length → I64 → m NewLength)
    (resize : A → NewLength → m ResizeResult) (lastindex : A → m Last)
    (subtract : Last → I64 → m End) (addIndex : End → I64 → m Index)
    (setindex : A → Index → Element → m StoreResult) (array : A) (items : Tuple Element) : m A := do
  let na ← length array
  let nx := Models2Group6.tupleFieldCount items
  let _ ← resize array (← addLength na nx)
  let e ← subtract (← lastindex array) nx
  for i in Models1Group3.numericOneTo nx do
    let value ← match tupleGet items.values i with
      | .ok value => pure value
      | .error error => throw error
    let index ← addIndex e i
    let _ ← setindex array index value
  return array

/-- Full generic filtering body, including bounds annotations, arbitrary selected return types and the original check order, base/abstractarray.jl:3699-3715. -/
-- Source: base/abstractarray.jl:3699-3715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _keepat!(a::AbstractVector, inds)
--     local prev
--     i = firstindex(a)
--     for k in inds
--         if @isdefined(prev)
--             prev < k || throw(ArgumentError("indices must be unique and sorted"))
--         end
--         ak = a[k] # must happen even when i==k for bounds checking
--         if i != k
--             @inbounds a[i] = ak # k > i, so a[i] is inbounds
--         end
--         prev = k
--         i = nextind(a, i)
--     end
--     deleteat!(a, i:lastindex(a))
--     return a
-- end
-- /Source
def keepAtIndices {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Indices I K E Last Range Other StoreResult DeleteResult Caller : Type}
    [ForIn m Indices K]
    (firstindex : A → m I) (lastindex : A → m Last)
    (less : K → K → m (TypeAssertion Bool Other))
    (notEqual : I → K → m (TypeAssertion Bool Other)) (getindex : A → K → m E)
    (setindex : UnsafeIndexRequest Caller → A → I → E → m StoreResult)
    (nextind : A → I → m I) (range : I → Last → m Range)
    (deleteat : A → Range → m DeleteResult) (ambient : UnsafeAmbientContext Caller)
    (array : A) (indices : Indices) : m A := do
  let mut previous : Option K := none
  let mut i ← firstindex array
  for k in indices do
    if let some prev := previous then
      if !(← assertType (← less prev k)) then
        throw (.julia (.argumentError "indices must be unique and sorted"))
    let value ← getindex array k
    if ← assertType (← notEqual i k) then
      let _ ← setindex { ambient := ambient, annotation := .inbounds, wrapperInlineHint := false }
        array i value
    previous := some k
    i ← nextind array i
  let last ← lastindex array
  let tail ← range i last
  let _ ← deleteat array tail
  return array

/-- Full generic filtering body, including bounds annotations, arbitrary selected return types and the original check order, base/abstractarray.jl:3717-3729. -/
-- Source: base/abstractarray.jl:3717-3729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _keepat!(a::AbstractVector, m::AbstractVector{Bool})
--     length(m) == length(a) || throw(BoundsError(a, m))
--     j = firstindex(a)
--     for i in eachindex(a, m)
--         @inbounds begin
--             if m[i]
--                 i == j || (a[j] = a[i])
--                 j = nextind(a, j)
--             end
--         end
--     end
--     deleteat!(a, j:lastindex(a))
-- end
-- /Source
def keepAtMask {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Mask LengthM LengthA I K E Last Indices Range Other StoreResult DeleteResult Caller : Type}
    [ForIn m Indices K]
    (lengthMask : Mask → m LengthM) (lengthArray : A → m LengthA)
    (equalLength : LengthM → LengthA → m (TypeAssertion Bool Other))
    (firstindex : A → m I) (lastindex : A → m Last)
    (eachindex : A → Mask → m Indices)
    (getMask : UnsafeIndexRequest Caller → Mask → K → m (TypeAssertion Bool Other))
    (equalIndex : UnsafeIndexRequest Caller → K → I → m (TypeAssertion Bool Other))
    (getindex : UnsafeIndexRequest Caller → A → K → m E)
    (setindex : UnsafeIndexRequest Caller → A → I → E → m StoreResult)
    (nextind : UnsafeIndexRequest Caller → A → I → m I) (range : I → Last → m Range)
    (deleteat : A → Range → m DeleteResult) (ambient : UnsafeAmbientContext Caller)
    (array : A) (mask : Mask) : m DeleteResult := do
  let lm ← lengthMask mask
  let la ← lengthArray array
  if !(← assertType (← equalLength lm la)) then throw (.julia .boundsError)
  let mut j ← firstindex array
  let indices ← eachindex array mask
  let request : UnsafeIndexRequest Caller :=
    { ambient := ambient, annotation := .inbounds, wrapperInlineHint := false }
  for i in indices do
    if ← assertType (← getMask request mask i) then
      if !(← assertType (← equalIndex request i j)) then
        let value ← getindex request array i
        let _ ← setindex request array j value
      j ← nextind request array j
  let last ← lastindex array
  let tail ← range j last
  deleteat array tail

/-- Full source body with runtime-selected operations and unchanged error/effect order, base/abstractarray.jl:3756-3766. -/
-- Source: base/abstractarray.jl:3756-3766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function circshift!(a::AbstractVector, shift::Integer)
--     n = length(a)
--     n == 0 && return a
--     shift = mod(shift, n)
--     shift == 0 && return a
--     l = lastindex(a)
--     reverse!(a, firstindex(a), l-shift)
--     reverse!(a, l-shift+1, lastindex(a))
--     reverse!(a)
--     return a
-- end
-- /Source
def circshiftInplace {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {A Shift Length ModShift Last First Difference Start Other Reverse1 Reverse2 Reverse3 : Type}
    (length : A → m Length) (lengthZero : Length → I64 → m (TypeAssertion Bool Other))
    (mod : Shift → Length → m ModShift) (shiftZero : ModShift → I64 → m (TypeAssertion Bool Other))
    (lastindex : A → m Last) (firstindex : A → m First)
    (subtract : Last → ModShift → m Difference) (add : Difference → I64 → m Start)
    (reverseFirst : A → First → Difference → m Reverse1)
    (reverseSecond : A → Start → Last → m Reverse2) (reverseAll : A → m Reverse3)
    (array : A) (shift : Shift) : m A := do
  let n ← length array
  if ← assertType (← lengthZero n (int 0)) then return array
  let shift ← mod shift n
  if ← assertType (← shiftZero shift (int 0)) then return array
  let l ← lastindex array
  let first ← firstindex array
  let difference ← subtract l shift
  let _ ← reverseFirst array first difference
  let start ← add (← subtract l shift) (int 1)
  let last ← lastindex array
  let _ ← reverseSecond array start last
  let _ ← reverseAll array
  return array

end JuliaLean.base.abstractarray.Completion20261105

namespace JuliaLean.AbstractArrays

open JuliaLean

/-- `size(A, d)`, `base/abstractarray.jl:42-46`. -/
def sizeDim (sizes : List I64) (d : I64) : Jl I64 :=
  if d.val < 1 then .error .boundsError
  else if d.val ≤ sizes.length then
    .ok (sizes.getD (d.val - 1).toNat (i64 1))
  else .ok (i64 1)

/-- `size(A, dim)` for an arbitrary fixed-width `Integer`: the first source
line is `d = Int(dim)::Int`, so conversion can fail before the trailing
dimension branch. -/
def sizeDimInteger {t : IntTy} (sizes : List I64) (d : JInt t) : Jl I64 := do
  let d ← JInt.convert (IntTy.i64.name) .i64 d.val
  sizeDim sizes d

/-- `axes(A, d)`, `base/abstractarray.jl:79-82`, for one-based axes. -/
def axesDim (sizes : List I64) (d : I64) : Jl Axis :=
  if d.val < 1 then .error .boundsError
  else if d.val ≤ sizes.length then
    .ok (Axis.oneTo (sizes.getD (d.val - 1).toNat (i64 1)).val.toNat)
  else .ok (Axis.oneTo 1)

/-- `has_offset_axes`, `base/abstractarray.jl:114-122`. -/
def hasOffsetAxes (axes : List Axis) : Bool := axes.any (fun a => !a.isOneBased)

/-- `require_one_based_indexing`, `base/abstractarray.jl:125-135`. -/
def requireOneBased (axes : List Axis) : Jl Unit :=
  if hasOffsetAxes axes then .error (.argumentError "offset arrays are not supported") else .ok ()

/-- The vector fast path of `has_offset_axes`, `base/abstractarray.jl:116`,
for an axis whose first value has any fixed-width integer type. -/
def hasOffsetInteger {t : IntTy} (first : JInt t) : Jl Bool := do
  let first ← JInt.convert (IntTy.i64.name) .i64 first.val
  return first.val != 1

/-- `require_one_based_indexing` after the integer-axis fast path. -/
def requireOneBasedInteger {t : IntTy} (first : JInt t) : Jl Unit := do
  if ← hasOffsetInteger first then
    throw (.argumentError "offset arrays are not supported")
  return ()


/-- `checkindex(Bool, inds, i::Real)`, `base/abstractarray.jl:751-753`.
The implementation tests only the numeric value and ignores whether `to_index`
supports the scalar type. -/
def checkScalar (axis : Axis) (i : ScalarIndex) : Bool := axis.contains i.value


/-- `checkindex` for `Colon` and `AbstractRange`,
`base/abstractarray.jl:754-760`. -/
def checkRange (axis : Axis) (r : RangeIndex) : Bool :=
  r.empty || (axis.contains r.first && axis.contains r.last)

/-- Cartesian scalar checks performed one axis at a time by
`checkbounds_indices`, `base/abstractarray.jl:722-728`. Missing axes are
trailing singleton dimensions, and missing indices require every remaining
axis to be singleton. -/
def checkCoords : List Axis → List ScalarIndex → Bool
  | [], [] => true
  | axes, [] => axes.all (fun a => a.len == 1)
  | [], i :: is => checkScalar (Axis.oneTo 1) i && checkCoords [] is
  | a :: axes, i :: is => checkScalar a i && checkCoords axes is

/-- `checkbounds(Bool, A, i)` for one scalar index,
`base/abstractarray.jl:687-693`. Vectors retain their axis; other arrays use
`1:length(A)`. -/
def checkLinear (axes : List Axis) (i : ScalarIndex) : Bool :=
  match axes with
  | [a] => checkScalar a i
  | _ =>
    let n := axes.foldl (fun p a => p * i64 a.len) (i64 1)
    decide (1 ≤ i.value.val ∧ i.value.val ≤ n.val)

/-- A generic mutable vector with offset axis and possibly unassigned slots. -/
structure GVec (α : Type) where
  first : I64
  slots : List (Option α)
  deriving DecidableEq, Repr

namespace GVec

def axis (v : GVec α) : Axis := ⟨v.first, v.slots.length⟩

def eachIndex (v : GVec α) : List I64 :=
  (List.range v.slots.length).map fun k => i64 (v.first.val + Int.ofNat k)

def firstIndex (v : GVec α) : I64 := v.first

def lastIndex (v : GVec α) : I64 := v.axis.last

/-- Generic `copyto!(dest, src)` after `unalias`,
`base/abstractarray.jl:1072-1123`. Iteration order, rather than offset equality,
determines the corresponding elements. -/
def copyAll (dest src : GVec α) : Jl (GVec α) :=
  if src.slots.length ≤ dest.slots.length then
    .ok { dest with slots := src.slots ++ dest.slots.drop src.slots.length }
  else .error .boundsError

/-- Generic `similar(a, T, dims)` fallback, `base/abstractarray.jl:819-834`,
represented by an unassigned one-based vector. -/
def similar (n : Nat) : GVec α := ⟨i64 1, List.replicate n none⟩

/-- `isempty(a::AbstractArray)`, `base/abstractarray.jl:1262`. -/
def isEmpty (v : GVec α) : Bool := v.slots.length == 0

end GVec

/-- Mixed-element-type `vcat` after promotion,
`base/abstractarray.jl:1689-1753`. -/
def vcatPromote (f : α → γ) (g : β → γ) (xs : List α) (ys : List β) : List γ :=
  xs.map f ++ ys.map g

/-- Mixed-element-type `hcat`, `base/abstractarray.jl:1755-1800`, represented
as rows. -/
def hcatPromote (f : α → γ) (g : β → γ) (xs : List α) (ys : List β) : Jl (List (γ × γ)) :=
  if xs.length = ys.length then .ok ((xs.map f).zip (ys.map g))
  else .error (.argumentError "number of rows must match")

end JuliaLean.AbstractArrays

namespace JuliaLean.Multidim

/-- `isempty(a::AbstractArray) = (length(a) == 0)`, `base/abstractarray.jl:1262`. -/
def ciIsEmpty (lengthFn : List Rng → I64) (R : List Rng) : Bool := (lengthFn R).val == 0

/-- `checkbounds(Bool, A, I)` for a `CartesianIndex` `I` and an array with axes `ax`. -/
def inAxes (ax : List (Int × Int)) (J : List Int) : Bool :=
  J.length == ax.length && (ax.zip J).all fun ((lo, hi), j) => decide (lo ≤ j ∧ j ≤ hi)

/-- `checkindex(Bool, inds, i)` for one index and the axes it covers
(`base/abstractarray.jl:719-760`; a `Slice` is accepted unchecked, line 755). -/
def checkIdx : Idx → List Nat → Bool
  | .int v, [n] => decide (1 ≤ v ∧ v ≤ n)
  | .urange lo hi, [n] => decide (hi < lo ∨ (1 ≤ lo ∧ hi ≤ n))
  | .colon, _ => true
  | .slice _, _ => true
  | .cart vs, ns => vs.length == ns.length && (vs.zip ns).all fun (v, n) => decide (1 ≤ v ∧ v ≤ n)
  | _, _ => false

/-- A `cat` argument: a scalar (`cat_size = (1,)`) or an `Array` of the given size. -/
inductive CatArg where
  | scalar
  | array (sz : List Nat)
  deriving DecidableEq, Repr

/-- `cat_size(A)`, `base/abstractarray.jl:1836-1837`. -/
def CatArg.size : CatArg → List Nat
  | .scalar => [1]
  | .array sz => sz

/-- `cat_size(A, d)` (0-based `d`): `size(A, d+1)`, 1 beyond `ndims`; 1 for scalars. -/
def CatArg.sizeAt (x : CatArg) (d : Nat) : Nat :=
  match x with
  | .scalar => 1
  | .array sz => sz.getD d 1

/-- `_cs(d, a, b)`, `base/abstractarray.jl:1894-1895`. -/
def cs (a b : Nat) : R Nat := if a = b then .ok a else .error .dimensionMismatch

/-- `_cshp(ndim, (), shape, nshape)`, `base/abstractarray.jl:1872-1873, 1879-1886` (the
methods for an exhausted `dims`; `ndim` only appears in error messages). -/
def cshpNoDims : List Nat → List Nat → R (List Nat)
  | [], nshape => .ok nshape
  | a :: as, [] => do
    let _ ← cs a 1
    let rest ← cshpNoDims as []
    pure (1 :: rest)
  | a :: as, b :: bs => do
    let next ← cs a b
    let rest ← cshpNoDims as bs
    pure (next :: rest)

/-- `_cshp(ndim, dims, shape, nshape)`, `base/abstractarray.jl:1872-1892` (eight methods;
the empty/nonempty pattern of the arguments selects the most specific one). -/
def cshp : List Bool → List Nat → List Nat → R (List Nat)
  | [], shape, nshape => cshpNoDims shape nshape
  | dims, [], [] => .ok (dims.map fun _ => 1)
  | d :: ds, a :: as, [] => do
    let rest ← cshp ds as []
    pure ((a + if d then 1 else 0) :: rest)
  | _ :: ds, [], b :: bs => do
    let rest ← cshp ds [] bs
    pure (b :: rest)
  | d :: ds, a :: as, b :: bs => do
    let next ← if d then pure (a + b) else cs a b
    let rest ← cshp ds as bs
    pure (next :: rest)

/-- `cat_size_shape(dims, X...)`, `base/abstractarray.jl:1867-1870`. -/
def catSizeShape (dims : List Bool) : List CatArg → R (List Nat)
  | [] => .ok (dims.map fun _ => 0)
  | x :: xs => do
    let s0 ← cshp dims [] x.size
    xs.foldlM (fun s y => cshp dims s y.size) s0

/-- `dims2cat(dims)`, `base/abstractarray.jl:1898-1903`. -/
def dims2cat (dims : List Int) : R (List Bool) :=
  if dims.any (· ≤ 0) then .error .argumentError
  else match dims.max? with
    | none => .error .argumentError     -- maximum(()) throws
    | some m => .ok ((List.range m.toNat).map fun (i : Nat) => dims.contains ((i : Int) + 1))


/-- `cat(X...; dims)` = `_cat_t(dims, T, X...)`, `base/abstractarray.jl:1907-1942`:
the result size, after `__cat_offset1!` stores each argument (`fill!` of the block for a
scalar, `A[inds...] = x` with its shape check for an array). -/
def cat (dims : List Int) (xs : List CatArg) : R (List Nat) := do
  let catdims ← dims2cat dims
  let shape ← catSizeShape catdims xs
  for x in xs do
    match x with
    | .scalar => pure ()
    | .array sz =>
      let blk := (List.range shape.length).map fun (i : Nat) =>
        if catdims.getD i false then x.sizeAt i else shape.getD i 0
      if !setindexShapeCheck sz blk then throw .dimensionMismatch
  pure shape

/-! ## `hvcat` -/

/-- `hvcat(rows, xs::T...) where T<:Number`, `base/abstractarray.jl:2253-2272`, with `n`
values. -/
def hvcatSame (rows : List Nat) (n : Nat) : R (Nat × Nat) :=
  match rows with
  | [] => .error .boundsError                         -- rows[1]
  | nc :: _ =>
    let nr := rows.length
    if nr * nc ≠ n then .error .argumentError
    else if rows.any (· ≠ nc) then .error .dimensionMismatch
    else .ok (nr, nc)

/-- `typed_hvcat(T, rows, xs::Number...)`, `base/abstractarray.jl:2279-2290`, with the
count check of `hvncat_fill!` (lines 2556-2566). -/
def hvcatTyped (rows : List Nat) (n : Nat) : R (Nat × Nat) :=
  match rows with
  | [] => .error .boundsError
  | nc :: rest =>
    if rest.any (· ≠ nc) then .error .dimensionMismatch
    else if rows.length * nc ≠ n then .error .argumentError
    else .ok (rows.length, nc)

/-- `hvcat(nbc::Int, as...)`, `base/abstractarray.jl:2197-2204`, with `n` values of one
`Number` type; `hvcat(())` with no values returns `[]`. -/
def hvcatCols (nbc : I64) (n : Nat) : R (Nat × Nat) := do
  let nI := i64 n
  let m ← (JInt.mod nI nbc).mapError fun _ => Err.divideError
  if m.val ≠ 0 then throw .argumentError
  let nbr ← (JInt.div nI nbc).mapError fun _ => Err.divideError
  if nbr.val < 0 then throw .argumentError         -- ntuple with a negative length
  if nbr.val = 0 then return (0, 0)                -- hvcat(()) = []
  hvcatSame (List.replicate nbr.val.toNat nbc.val.toNat) n

end JuliaLean.Multidim

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- `size_to_strides(s, sz...)`, `base/abstractarray.jl:609-611`: `(s, s*sz[1], s*sz[1]*sz[2], ...)`
with one entry per dimension. -/
def sizeToStrides (s : I64) : List I64 → List I64
  | [] => []
  | [_] => [s]
  | d :: ds => s :: sizeToStrides (s * d) ds

end JuliaLean.BroadcastViews

/-!
Method-specific models for `base/abstractarray.jl:16-280` at `bbfa0ce4150`.
Each definition follows one Julia method body. Function arguments represent
the Julia methods called by that body; the model controls their call order,
branches, conversions, errors, and returned value.
-/

namespace JuliaLean.AbstractArrayCov.Rows.Basic

open JuliaLean
open JuliaLean.AbstractArrays

abbrev I64 := JInt .i64

def i64 (x : Int) : I64 := JInt.lit .i64 x

inductive TypeTag where
  | any | bottom | int | cartesian (rank : Nat) | element (id : Nat) | other (id : Nat)
  deriving Repr, DecidableEq

/-- One-based tuple indexing, including the BoundsError from `s[d]`. -/
def tupleGet (xs : List α) (i : I64) : Jl α :=
  if h : 1 ≤ i.val ∧ i.val ≤ xs.length then
    .ok (xs[(i.val - 1).toNat]'(by omega))
  else .error .boundsError

/-- `convert(::Type{T}, a::T)`, line 16. -/
def method16 (a : α) : α := a

/-- `convert(::Type{AbstractArray{T}}, a::AbstractArray)`, line 17. -/
def method17 (construct : α → β) (a : α) : β := construct a

/-- Rank-specialized `convert`, line 18. -/
def method18 (construct : α → β) (a : α) : β := construct a

/-- `size(t, dim)`, lines 42-46: convert `dim`, call `size(t)`, then index or return 1. -/
def method42 {t : IntTy} (size : Unit → List I64) (dim : JInt t) : Jl I64 := do
  let d ← JInt.convert (IntTy.i64.name) .i64 dim.val
  let s := size ()
  if d.val ≤ s.length then tupleGet s d else .ok (i64 1)

/-- `axes(A, d)`, lines 79-82: compare before indexing, with `OneTo(1)` past rank. -/
def method79 {t : IntTy} (rank : Nat) (axes : Unit → List Axis) (d : JInt t) : Jl Axis :=
  if d.val ≤ rank then do
    let i ← JInt.convert (IntTy.i64.name) .i64 d.val
    tupleGet (axes ()) i
  else .ok (Axis.oneTo 1)

/-- `axes(A)`, lines 100-103. -/
def method100 (size : α → List I64) (uncheckedOneTo : I64 → Axis) (a : α) : List Axis :=
  (size a).map uncheckedOneTo

/-- `has_offset_axes()`, line 114. -/
def method114 : Bool := false

/-- `_any_tuple(x -> Int(first(x)) != 1, false, axes(A)...)`, line 115. -/
def offsetAxesLoop (first : α → Int) : List α → Jl Bool
  | [] => .ok false
  | axis :: rest => do
      let i ← JInt.convert (IntTy.i64.name) .i64 (first axis)
      if i.val != 1 then .ok true else offsetAxesLoop first rest

def method115 (axes : β → List α) (first : α → Int) (a : β) : Jl Bool :=
  offsetAxesLoop first (axes a)

/-- Vector fast path of `has_offset_axes`, line 116. -/
def method116 (firstindex : α → Int) (a : α) : Jl Bool := do
  let i ← JInt.convert (IntTy.i64.name) .i64 (firstindex a)
  return i.val != 1

/-- `has_offset_axes(::Colon)`, line 117. -/
def method117 : Bool := false

/-- `has_offset_axes(::Array)`, line 118. -/
def method118 : Bool := false

/-- Vararg `has_offset_axes`, line 122, with source short-circuit order. -/
def method122 (hasOffset : α → Jl Bool) (a : α) (rest : List α) : Jl Bool := do
  if ← hasOffset a then return true
  for x in rest do
    if ← hasOffset x then return true
  return false

/-- `require_one_based_indexing`, line 135. -/
def method135 (hasOffset : List α → Jl Bool) (arrays : List α) : Jl Unit := do
  if ← hasOffset arrays then
    throw (.argumentError "offset arrays are not supported but got an array with index other than 1")
  return ()

/-- Zero-dimensional `axes1`, line 140. -/
def method140 : Axis := Axis.oneTo 1

/-- Array `axes1`, line 141. -/
def method141 (axes : α → List Axis) (a : α) : Jl Axis := tupleGet (axes a) (i64 1)

/-- Generic iterable `axes1`, line 142. -/
def method142 (length : α → Nat) (oneto : Nat → Axis) (iter : α) : Axis :=
  oneto (length iter)

/-- `keys(a::AbstractArray)`, line 169. -/
def method169 (axes : α → List Axis) (cartesianIndices : List Axis → β) (a : α) : β :=
  cartesianIndices (axes a)

/-- `keys(a::AbstractVector)`, line 170. -/
def method170 (linearIndices : α → β) (a : α) : β := linearIndices a

/-- `keytype(a) = keytype(typeof(a))`, line 192. -/
def method192 (typeof : α → TypeTag) (keytype : TypeTag → TypeTag) (a : α) : TypeTag :=
  keytype (typeof a)

/-- Bottom `keytype` delegates to Bottom `eltype`, line 193. -/
def method193 (eltype : TypeTag → Jl TypeTag) : Jl TypeTag := eltype .bottom

/-- Generic AbstractArray key type, line 195. -/
def method195 (ndims : TypeTag → Nat) (arrayType : TypeTag) : TypeTag :=
  .cartesian (ndims arrayType)

/-- AbstractVector key type, line 196. -/
def method196 : TypeTag := .int

/-- `valtype(a) = valtype(typeof(a))`, line 198. -/
def method198 (typeof : α → TypeTag) (valtype : TypeTag → TypeTag) (a : α) : TypeTag :=
  valtype (typeof a)

/-- Bottom `valtype` delegates to Bottom `eltype`, line 199. -/
def method199 (eltype : TypeTag → Jl TypeTag) : Jl TypeTag := eltype .bottom

/-- AbstractArray `valtype` delegates to `eltype`, line 217. -/
def method217 (eltype : TypeTag → TypeTag) (arrayType : TypeTag) : TypeTag :=
  eltype arrayType

/-- `prevind`, line 219. -/
def method219 (raw : Int) : Jl I64 := do
  let i ← JInt.convert (IntTy.i64.name) .i64 raw
  return i - i64 1

/-- `nextind`, line 220. -/
def method220 (raw : Int) : Jl I64 := do
  let i ← JInt.convert (IntTy.i64.name) .i64 raw
  return i + i64 1

/-- Default `eltype(::Type)`, line 243. -/
def method243 : TypeTag := .any

/-- Bottom `eltype`, line 244. -/
def method244 : Jl TypeTag := .error (.argumentError "Union{} does not have elements")

/-- Value `eltype` delegates through `typeof`, line 245. -/
def method245 (typeof : α → TypeTag) (eltype : TypeTag → TypeTag) (x : α) : TypeTag :=
  eltype (typeof x)

/-- AbstractArray element type branch, line 246. -/
def method246 (defined : Bool) (element : TypeTag) : TypeTag := if defined then element else .any

/-- `elsize(A) = elsize(typeof(A))`, line 261. -/
def method261 (typeof : α → TypeTag) (elsize : TypeTag → Nat) (a : α) : Nat :=
  elsize (typeof a)

/-- Value `ndims`, line 278. -/
def method278 (rank : I64) : I64 := rank

/-- Type `ndims`, line 279. -/
def method279 (rank : I64) : I64 := rank

/-- Bottom `ndims`, line 280. -/
def method280 : Jl I64 := .error (.argumentError "Union{} does not have elements")

end JuliaLean.AbstractArrayCov.Rows.Basic

namespace JuliaLean.ArrayOps

open JuliaLean

/-- Slots of a `Vector`; `none` is an unassigned slot. -/
abbrev Vec (α : Type) := List (Option α)

/-- Final contents of the mutated vector and the result or exception. -/
structure Out (α β : Type) where
  vec : Vec α
  res : Jl β

end JuliaLean.ArrayOps

/-!
Models of the generic `AbstractArray` methods of `base/abstractarray.jl` (master
`bbfa0ce4150`) used by the spec-first properties of this area.

An input `Arr α` stores Int64 axes and mutable column-major data. Its canonical
getter and setter follow the OffsetArrays convention. The model identifies a
vector's linear axis with its axis values, which is valid for identity-indexed
axes but does not represent `first(LinearIndices(A))` for a plain offset
`UnitRange`. The generic zero-index consumer is modelled separately in
`AbstractArraySpecs.Indexing`.

Arrays are values here, so `===`, `mightalias` and `unalias` never fire; the
properties are about distinct arrays.
-/

namespace JuliaLean.AbstractArraySpecs


/-! ## Axes -/



/-- Tuple `==` of axes: same length and elementwise `==`. -/
def axesEq : List Ax → List Ax → Bool
  | [], [] => true
  | r :: rs, s :: ss => axEq r s && axesEq rs ss
  | _, _ => false

/-! ## Input arrays -/

inductive Style where
  | linear
  | cartesian
  deriving DecidableEq, Repr

structure Arr (α : Type) where
  axes : List Ax
  style : Style
  /-- Elements in column-major order. -/
  data : List α
  deriving DecidableEq, Repr



/-! ## Reference semantics (independent of Base)

Column-major position of a Cartesian index list, following the manual
(doc/src/manual/arrays.md, "Omitted and extra indices"): indices beyond `ndims` must
be 1, and omitted trailing indices are allowed for length-one dimensions. -/
def refCartPos : List Ax → List Int → Option Nat
  | axs, [] => if axs.all (fun r => decide (r.len = 1)) then some 0 else none
  | [], i :: is => if i = 1 then refCartPos [] is else none
  | r :: rs, i :: is =>
      if r.lo.val ≤ i ∧ i ≤ r.hi.val then
        (refCartPos rs is).map (fun p => (i - r.lo.val).toNat + r.len.toNat * p)
      else none

/-- Position of a linear index: a vector's linear indices are its axis, every other
array's are `1:length(A)` (doc/src/manual/arrays.md, "Linear indexing";
base/abstractarray.jl:337-346). -/
def refLinPos {α : Type} (A : Arr α) (k : Int) : Option Nat :=
  match A.axes with
  | [r] => if r.lo.val ≤ k ∧ k ≤ r.hi.val then some (k - r.lo.val).toNat else none
  | axs => if 1 ≤ k ∧ k ≤ totalLen axs then some (k - 1).toNat else none

/-- The position an index list refers to: one index is linear, any other number is
Cartesian. -/
def refPos {α : Type} (A : Arr α) : List I64 → Option Nat
  | [k] => refLinPos A k.val
  | I => refCartPos A.axes (I.map (·.val))

/-! ## The array type's canonical methods -/

def elemAt {α : Type} (A : Arr α) (p : Option Nat) : R α :=
  match p with
  | some p => match A.data[p]? with
    | some x => .ok x
    | none => .error .boundsError
  | none => .error .boundsError

def storeAt {α : Type} (A : Arr α) (p : Option Nat) (v : α) : R (Arr α) :=
  match p with
  | some p => if p < A.data.length then .ok { A with data := A.data.set p v } else .error .boundsError
  | none => .error .boundsError

/-- `getindex(A, i::Int)` of an `IndexLinear` array type. -/
def canonGetL {α : Type} (A : Arr α) (i : I64) : R α := elemAt A (refLinPos A i.val)
/-- `getindex(A, I::Vararg{Int,N})` of an `IndexCartesian` array type. -/
def canonGetC {α : Type} (A : Arr α) (I : List I64) : R α :=
  if I.length = A.axes.length then elemAt A (refCartPos A.axes (I.map (·.val)))
  else .error .boundsError
def canonSetL {α : Type} (A : Arr α) (v : α) (i : I64) : R (Arr α) := storeAt A (refLinPos A i.val) v
def canonSetC {α : Type} (A : Arr α) (v : α) (I : List I64) : R (Arr α) :=
  if I.length = A.axes.length then storeAt A (refCartPos A.axes (I.map (·.val))) v
  else .error .boundsError

/-! ## Base: size, length, linear indices -/

/-- `size(A)` of the array type: the axis lengths. -/
def sizeA {α : Type} (A : Arr α) : List I64 := A.axes.map axLength

/-- `length(t::AbstractArray) = prod(size(t))`, wrapping `Int` products. -/
def prodI : List I64 → I64
  | [] => i64 1
  | x :: xs => x * prodI xs

def lengthA {α : Type} (A : Arr α) : I64 := prodI (sizeA A)

/-- `oneto(n)` / `unchecked_oneto(n)` for the nonnegative `length(A)`. -/
def onetoLen {α : Type} (A : Arr α) : Ax := oneTo (lengthA A)

/-- `axes1(A)` (base/abstractarray.jl:140-141): `OneTo(1)` for 0-d, else `axes(A)[1]`. -/
def axes1 {α : Type} (A : Arr α) : Ax :=
  match A.axes with
  | [] => oneTo (i64 1)
  | r :: _ => r

/-- `eachindex(::IndexLinear, A)` (base/abstractarray.jl:394-396): `axes1(A)` for a
vector, `oneto(length(A))` otherwise. For identity-indexed vector axes this also
represents `LinearIndices(A)`. -/
def linearAxis {α : Type} (A : Arr α) : Ax :=
  match A.axes with
  | [_] => axes1 A
  | _ => onetoLen A

/-! ## Base: bounds checking -/

/-- `unsigned(x)` of an `Int`. -/
def unsignedVal (x : I64) : Int := wrapInt .u64 x.val

/-- `checkindex(Bool, inds, i::Int)` (base/abstractarray.jl:751-753): the `OneTo{Int}`
method uses `unsigned(i -% one(i)) < unsigned(last(inds))`; other unit ranges
(including `IdentityUnitRange`, line 752) compare with both endpoints. -/
def checkindex (r : Ax) (i : I64) : Bool :=
  match r.kind with
  | .oneTo => decide (unsignedVal (i - i64 1) < unsignedVal r.hi)
  | .unit => decide (r.lo ≤ i) && decide (i ≤ r.hi)

/-- `checkbounds_indices(Bool, inds, I)` (base/abstractarray.jl:722-728), with
`get(inds, 1, OneTo(1))` and `safe_tail`. -/
def checkboundsIndices : List Ax → List I64 → Bool
  | inds, [] => inds.all (fun x => axLength x == i64 1)
  | inds, i :: I => checkindex (inds.headD (oneTo (i64 1))) i && checkboundsIndices inds.tail I

/-- `checkbounds(Bool, A, I...)` (base/abstractarray.jl:682-693): one index uses
`eachindex(IndexLinear(), A)`. -/
def checkboundsBool {α : Type} (A : Arr α) (I : List I64) : Bool :=
  match I with
  | [i] => checkindex (linearAxis A) i
  | _ => checkboundsIndices A.axes I

/-- `checkbounds(A, I...)`: `BoundsError` unless in bounds. -/
def checkbounds {α : Type} (A : Arr α) (I : List I64) : R Unit :=
  if checkboundsBool A I then .ok () else .error .boundsError

/-! ## Base: index conversion -/

/-- `_sub2ind_recurse` (base/abstractarray.jl:1193-1202) with `nextL` and
`offsetin` (lines 1204-1208). -/
def sub2indRecurse : List Ax → I64 → I64 → List I64 → I64
  | _, _, ind, [] => ind
  | [], L, ind, i :: I => sub2indRecurse [] L (ind + (i - i64 1) * L) I
  | r :: rs, L, ind, i :: I => sub2indRecurse rs (L * axLength r) (ind + (i - r.lo) * L) I

/-- `_sub2ind(inds, I::Integer...)` (base/abstractarray.jl:1178-1191) for a nonempty
index list. -/
def sub2ind (inds : List Ax) (I : List I64) : R I64 :=
  match inds, I with
  | [r], [i] => if r.kind = .oneTo then .ok i else .error .argumentError
  | [r], I => if r.kind = .oneTo then .ok (sub2indRecurse [r] (i64 1) (i64 1) I) else .error .argumentError
  | inds, I => .ok (sub2indRecurse inds (i64 1) (i64 1) I)

/-- `first(LinearIndices(A))`. -/
def firstLinear {α : Type} (A : Arr α) : I64 := (linearAxis A).lo

/-- `_to_linear_index(A, I...)` (base/abstractarray.jl:1398-1401). -/
def toLinearIndex {α : Type} (A : Arr α) (I : List I64) : R I64 :=
  match I with
  | [] => .ok (firstLinear A)
  | [i] => .ok i
  | i :: I' => if A.axes.length = 1 then .ok i else sub2ind A.axes (i :: I')

/-- `divrem(x, y)` for `Int` (truncating `div` and `rem`). -/
def divrem (x y : I64) : R (I64 × I64) :=
  if y.val = 0 then .error .divideError
  else if x.val = tmin ∧ y.val = -1 then .error .divideError
  else .ok (i64 (x.val.tdiv y.val), i64 (x.val.tmod y.val))

/-- `_ind2sub_recurse` (base/abstractarray.jl:1217-1227) with `_indexlength` and
`_lookup` (lines 1229-1232). -/
def ind2subRecurse : List Ax → I64 → R (List I64)
  | [], ind => .ok [ind + i64 1]
  | [r], ind => .ok [ind + r.lo]
  | r :: rs, ind => do
      let (indnext, indsub) ← divrem ind (axLength r)
      let rest ← ind2subRecurse rs indnext
      .ok ((indsub + r.lo) :: rest)

/-- `_ind2sub(inds, ind::Integer)` (base/abstractarray.jl:1210-1215). -/
def ind2sub (inds : List Ax) (ind : I64) : R (List I64) :=
  match inds with
  | [] => if ind = i64 1 then .ok [] else .error .boundsError
  | [r] => if r.kind = .oneTo then .ok [ind] else .error .argumentError
  | inds => ind2subRecurse inds (ind - i64 1)

/-- The zero-index conversion maps `first` over axes without converting the
axis element type (base/abstractarray.jl:1415). -/
def axisStarts {Axis : Type u} {Index : Type v} (first : Axis → Index) (axes : List Axis) : List Index :=
  axes.map first

/-- An axis stores its first index in the axis's own index type. -/
structure AxisFirst (Index : Type) where
  first : Index


/-- `_to_subscript_indices(A, I...)` (base/abstractarray.jl:1414-1432), for an index
count different from `ndims(A)`. -/
def toSubscriptIndices {α : Type} (A : Arr α) (I : List I64) : R (List I64) :=
  match A.axes, I with
  | [], _ => .ok []
  | axs, [] => .ok (axisStarts (·.lo) axs)
  | axs, [i] => ind2sub axs i
  | axs, I =>
      if I.length ≤ axs.length then .ok (I ++ (axs.drop I.length).map (·.lo))
      else .ok (I.take axs.length)

/-! ## Base: getindex and setindex! -/

/-- `getindex(A, I::Int...)` (base/abstractarray.jl:1363-1367) for integer indices:
the array type's canonical method when the signature matches, otherwise
`_getindex(IndexStyle(A), A, I...)` (lines 1392-1397 and 1404-1409). -/
def getindex {α : Type} (A : Arr α) (I : List I64) : R α :=
  match A.style with
  | .linear =>
      if I.length = 1 then canonGetL A (I.headD (i64 0))
      else do
        checkbounds A I
        let k ← toLinearIndex A I
        canonGetL A k
  | .cartesian =>
      if I.length = A.axes.length then canonGetC A I
      else do
        checkbounds A I
        let J ← toSubscriptIndices A I
        canonGetC A J

/-- `setindex!(A, v, I::Int...)` (base/abstractarray.jl:1464-1468, 1486-1504). -/
def setindex {α : Type} (A : Arr α) (v : α) (I : List I64) : R (Arr α) :=
  match A.style with
  | .linear =>
      if I.length = 1 then canonSetL A v (I.headD (i64 0))
      else do
        checkbounds A I
        let k ← toLinearIndex A I
        canonSetL A v k
  | .cartesian =>
      if I.length = A.axes.length then canonSetC A v I
      else do
        checkbounds A I
        let J ← toSubscriptIndices A I
        canonSetC A v J

/-- `get(A, I::Dims, default)` and `get(A, i::Integer, default)`
(base/abstractarray.jl:1637-1639). -/
def getDefault {α : Type} (A : Arr α) (I : List I64) (d : α) : R α :=
  if checkboundsBool A I then getindex A I else .ok d

/-! ## Base: first, last, size(A, d), axes(A, d), isempty -/

/-- `first(a::AbstractArray) = a[first(eachindex(a))]` (base/abstractarray.jl:455).
`eachindex(A)` is `eachindex(IndexLinear(), A)` for linear arrays and
`CartesianIndices(axes(A))` otherwise, whose first element is the tuple of axis
starts. -/
def firstA {α : Type} (A : Arr α) : R α :=
  match A.style with
  | .linear => getindex A [(linearAxis A).lo]
  | .cartesian => getindex A (A.axes.map (·.lo))

/-- `last(a) = a[end]`, `lastindex(a) = last(eachindex(IndexLinear(), a))`
(base/abstractarray.jl:429, 530). -/
def lastA {α : Type} (A : Arr α) : R α := getindex A [(linearAxis A).hi]

/-- `size(t::AbstractArray, dim)` (base/abstractarray.jl:42-46) for `dim::Int`:
`s[d]` on the size tuple throws `BoundsError` for `d < 1`. -/
def sizeD {α : Type} (A : Arr α) (d : I64) : R I64 :=
  if d.val ≤ (sizeA A).length then
    match (sizeA A)[d.val.toNat - 1]?, decide (1 ≤ d.val) with
    | some s, true => .ok s
    | _, _ => .error .boundsError
  else .ok (i64 1)

/-- `axes(A, d)` (base/abstractarray.jl:79-82) for `d::Int`. -/
def axesD {α : Type} (A : Arr α) (d : I64) : R Ax :=
  if d.val ≤ A.axes.length then
    match A.axes[d.val.toNat - 1]?, decide (1 ≤ d.val) with
    | some r, true => .ok r
    | _, _ => .error .boundsError
  else .ok (oneTo (i64 1))

/-- `isempty(a::AbstractArray) = (length(a) == 0)` (base/abstractarray.jl:1262). -/
def isemptyA {α : Type} (A : Arr α) : Bool := lengthA A == i64 0

/-! ## Base: eachindex with two arrays -/

/-- `IndexStyle(A, B)`: linear only when both are. -/
def styleOf2 {α β : Type} (A : Arr α) (B : Arr β) : Style :=
  if A.style = .linear ∧ B.style = .linear then .linear else .cartesian

/-- `eachindex(A, B)` (base/abstractarray.jl:386-404 for `IndexLinear`,
base/multidimensional.jl:`eachindex(::IndexCartesian, A, B...)` for the rest).
The result is the common index range (for the linear style) or axes. -/
def eachindex2 {α β : Type} (A : Arr α) (B : Arr β) : R (List Ax) :=
  match styleOf2 A B with
  | .linear =>
      if axEq (linearAxis B) (linearAxis A) then .ok [linearAxis A] else .error .dimensionMismatch
  | .cartesian =>
      if axesEq B.axes A.axes then .ok A.axes else .error .dimensionMismatch

end JuliaLean.AbstractArraySpecs

namespace JuliaLean.AbstractArraySpecs

/-! Generic Cartesian zero-index fallback. Axis starts retain their integer type
until the second call to `getindex`/`setindex!` converts them through `to_index`.
The canonical methods are supplied by the concrete array type. -/


def genericStarts (axes : List GenericAxis) : List ScalarIndex :=
  axisStarts GenericAxis.first axes


structure GenericCartesianArray (α σ : Type) where
  axes : List GenericAxis
  /-- Abstract element function, independent of the concrete getter. -/
  element : List Int → α
  canonicalGet : List Int → R α
  canonicalSet : Option (α → List Int → R σ)
  updated : α → List Int → σ


def singletonAxes (axes : List GenericAxis) : Bool :=
  axes.all (fun axis => axis.length == 1)

/-- Cartesian `_getindex` zero-index path (abstractarray.jl:1404-1416). -/
def genericZeroGet {α σ : Type} (A : GenericCartesianArray α σ) : R α :=
  if A.axes.isEmpty then A.canonicalGet []
  else if singletonAxes A.axes then do
    let I ← convertScalarIndices (genericStarts A.axes)
    A.canonicalGet I
  else .error .boundsError

/-- Cartesian `_setindex!` zero-index path (abstractarray.jl:1495-1503).
A missing canonical setter is Julia's CanonicalIndexError. -/
def genericZeroSet {α σ : Type} (A : GenericCartesianArray α σ) (v : α) : R σ :=
  let call := fun I => match A.canonicalSet with
    | some set => set v I
    | none => .error .canonicalIndexError
  if A.axes.isEmpty then call []
  else if singletonAxes A.axes then do
    let I ← convertScalarIndices (genericStarts A.axes)
    call I
  else .error .boundsError

def genericZeroDefault {α σ : Type} (A : GenericCartesianArray α σ) (d : α) : R α :=
  if singletonAxes A.axes then genericZeroGet A else .ok d




structure GenericLinearArray (α σ : Type) where
  axes : List GenericAxis
  element : Int → α
  canonicalGet : Int → R α
  canonicalSet : Option (α → Int → R σ)
  updated : α → Int → σ


def genericLinearZeroGet {α σ : Type} (A : GenericLinearArray α σ) : R α :=
  if singletonAxes A.axes then do
    let i ← genericLinearStart A.axes
    A.canonicalGet i
  else .error .boundsError

def genericLinearZeroSet {α σ : Type} (A : GenericLinearArray α σ) (v : α) : R σ :=
  if singletonAxes A.axes then do
    let i ← genericLinearStart A.axes
    match A.canonicalSet with
    | some set => set v i
    | none => .error .canonicalIndexError
  else .error .boundsError

def genericLinearZeroDefault {α σ : Type} (A : GenericLinearArray α σ) (d : α) : R α :=
  if singletonAxes A.axes then genericLinearZeroGet A else .ok d



end JuliaLean.AbstractArraySpecs

/-!
Models of array iteration (base/abstractarray.jl:1239-1260, with `CartesianIndices`
iteration from base/multidimensional.jl:445-486) and of the loops built on it:
`isequal` and `==` (base/abstractarray.jl:3106-3117, 3149-3163) over
`zip(A, B)`, and `map!(f, dest, A)` (lines 3482-3488) over
`zip(eachindex(dest), eachindex(A))`.
-/

namespace JuliaLean.AbstractArraySpecs

/-- Iteration states: the integer state of an `IndexLinear` array, or the tuple
state `(eachindex(A),)` / `(CartesianIndices, CartesianIndex)` of the other style;
a 0-d `CartesianIndices` uses a `done::Bool` state (multidimensional.jl:486). -/
inductive IterState where
  | lin (k : I64)
  | cartStart
  | cart (I : List I64)
  | cart0 (done : Bool)
  /-- Iteration of an `AbstractUnitRange` before the first element / after yielding `i`. -/
  | rngStart
  | rng (i : I64)
  deriving DecidableEq, Repr

/-- `iterate_starting_state(A)` (base/abstractarray.jl:1245-1247):
`firstindex(A)` for `IndexLinear`, `(eachindex(A),)` otherwise. -/
def iterStart {α : Type} (A : Arr α) : IterState :=
  match A.style with
  | .linear => .lin (linearAxis A).lo
  | .cartesian => .cartStart

/-- `i in r` for a unit range. -/
def inAx (i : I64) (r : Ax) : Bool := decide (r.lo ≤ i) && decide (i ≤ r.hi)

/-- `__inc(state, indices)` (base/multidimensional.jl:468-483) for unit ranges
(`step(rng) == 1`). -/
def ciInc : List I64 → List Ax → Bool × List I64
  | [s], [r] => (s != r.hi, [s + i64 1])
  | s :: s2 :: ss, r :: r2 :: rs =>
      if s != r.hi then (true, (s + i64 1) :: s2 :: ss)
      else
        let t := ciInc (s2 :: ss) (r2 :: rs)
        (t.1, r.lo :: t.2)
  | _, _ => (false, [])

/-- `iterate(A, state)` (base/abstractarray.jl:1250-1259). The `IndexLinear` method
checks `checkbounds(Bool, A, state)` and steps by one; the tuple method iterates
`CartesianIndices(axes(A))` and indexes `A` with the resulting `CartesianIndex`,
which `to_indices` splats into `ndims(A)` integer indices. -/
def iterateA {α : Type} (A : Arr α) : IterState → R (Option (α × IterState))
  | .lin k =>
      if checkboundsBool A [k] then do
        let x ← getindex A [k]
        .ok (some (x, .lin (k + i64 1)))
      else .ok none
  | .cartStart =>
      match A.axes with
      | [] => do
          let x ← getindex A []
          .ok (some (x, .cart0 true))
      | axs =>
          let f := axs.map (·.lo)
          if (f.zip axs).all (fun p => inAx p.1 p.2) then do
            let x ← getindex A f
            .ok (some (x, .cart f))
          else .ok none
  | .cart I =>
      let t := ciInc I A.axes
      if t.1 then do
        let x ← getindex A t.2
        .ok (some (x, .cart t.2))
      else .ok none
  | .cart0 done =>
      if done then .ok none
      else do
        let x ← getindex A []
        .ok (some (x, .cart0 true))
  | .rngStart => .ok none
  | .rng _ => .ok none

/-- `collect`-style consumption of `iterate(A)` with fuel. -/
def iterAll {α : Type} (A : Arr α) : Nat → IterState → R (List α)
  | 0, _ => .ok []
  | f + 1, st => do
      match ← iterateA A st with
      | none => .ok []
      | some (x, st') => do
          let rest ← iterAll A f st'
          .ok (x :: rest)

/-- `for (a, b) in zip(A, B)` with fuel: `zip` iterates `A` then `B` and stops when
either is exhausted. `step a b` returns `some r` to leave the loop early with `r`. -/
def zipLoop {α β γ : Type} (A : Arr α) (B : Arr β) (step : α → β → Option γ) (done : γ) :
    Nat → IterState → IterState → R γ
  | 0, _, _ => .ok done
  | f + 1, sa, sb => do
      match ← iterateA A sa with
      | none => .ok done
      | some (a, sa') =>
        match ← iterateA B sb with
        | none => .ok done
        | some (b, sb') =>
          match step a b with
          | some r => .ok r
          | none => zipLoop A B step done f sa' sb'

/-- Fuel for loops over the elements of `A`. -/
def fuelOf {α : Type} (A : Arr α) : Nat := A.data.length + 1

/-- `isequal(A, B)` (base/abstractarray.jl:3106-3117), with `iseq` the element
`isequal`; `A === B` cannot be observed on values. -/
def isequalA {α : Type} (iseq : α → α → Bool) (A B : Arr α) : R Bool :=
  if !axesEq A.axes B.axes then .ok false
  else zipLoop A B (fun a b => if !iseq a b then some false else none) true
    (fuelOf A) (iterStart A) (iterStart B)

/-- Three-valued element `==`: `some b` or `none` for `missing`. -/
abbrev Eq3 (α : Type) := α → α → Option Bool

/-- `==(A, B)` (base/abstractarray.jl:3149-3163): `false` at the first `false`,
otherwise `missing` if any comparison was `missing`, otherwise `true`. The running
`anymissing` flag is threaded through the loop state. -/
def eqLoop {α : Type} (A B : Arr α) (eq : Eq3 α) :
    Nat → Bool → IterState → IterState → R (Option Bool)
  | 0, m, _, _ => .ok (if m then none else some true)
  | f + 1, m, sa, sb => do
      match ← iterateA A sa with
      | none => .ok (if m then none else some true)
      | some (a, sa') =>
        match ← iterateA B sb with
        | none => .ok (if m then none else some true)
        | some (b, sb') =>
          match eq a b with
          | none => eqLoop A B eq f true sa' sb'
          | some false => .ok (some false)
          | some true => eqLoop A B eq f m sa' sb'

def eqA {α : Type} (eq : Eq3 α) (A B : Arr α) : R (Option Bool) :=
  if !axesEq A.axes B.axes then .ok (some false)
  else eqLoop A B eq (fuelOf A) false (iterStart A) (iterStart B)

/-- Whether `eachindex(A)` is a unit range of linear indices: `eachindex(A::AbstractVector)
= axes1(A)` for every vector, `eachindex(IndexLinear(), A) = oneto(length(A))` for other
`IndexLinear` arrays, and `CartesianIndices(axes(A))` otherwise
(base/abstractarray.jl:325, 384, 394-396; base/multidimensional.jl:435). -/
def eachRange {α : Type} (A : Arr α) : Bool :=
  match A.style, A.axes with
  | .linear, _ => true
  | .cartesian, [_] => true
  | .cartesian, _ => false

/-- Starting state of `eachindex(A)`. -/
def eachStart {α : Type} (A : Arr α) : IterState :=
  if eachRange A then .rngStart else .cartStart

/-- `eachindex(A)`'s iteration as index lists: `eachindex(IndexLinear(), A)` for
linear arrays, a unit range iterated by `iterate(r) = isempty(r) ? nothing :
(first(r), first(r))` and `iterate(r, i) = i == last(r) ? nothing : (i + 1, i + 1)`
(base/range.jl), and `CartesianIndices(axes(A))` otherwise. -/
def eachindexStep {α : Type} (A : Arr α) : IterState → Option (List I64 × IterState)
  | .rngStart =>
      let r := linearAxis A
      if axIsEmpty r then none else some ([r.lo], .rng r.lo)
  | .rng i =>
      let r := linearAxis A
      if i = r.hi then none else some ([i + i64 1], .rng (i + i64 1))
  | .lin _ => none
  | .cartStart =>
      match A.axes with
      | [] => some ([], .cart0 true)
      | axs =>
          let f := axs.map (·.lo)
          if (f.zip axs).all (fun p => inAx p.1 p.2) then some (f, .cart f) else none
  | .cart I =>
      let t := ciInc I A.axes
      if t.1 then some (t.2, .cart t.2) else none
  | .cart0 done => if done then none else some ([], .cart0 true)

/-- `map!(f, dest, A)` (base/abstractarray.jl:3482-3488):
`for (i, j) in zip(eachindex(dest), eachindex(A)); dest[i] = f(A[j]); end`. -/
def mapLoop {α : Type} (f : α → α) (A : Arr α) :
    Nat → Arr α → IterState → IterState → R (Arr α)
  | 0, dest, _, _ => .ok dest
  | n + 1, dest, si, sj =>
      match eachindexStep dest si with
      | none => .ok dest
      | some (i, si') =>
        match eachindexStep A sj with
        | none => .ok dest
        | some (j, sj') => do
            let a ← getindex A j
            let dest' ← setindex dest (f a) i
            mapLoop f A n dest' si' sj'

def mapBang {α : Type} (f : α → α) (dest A : Arr α) : R (Arr α) :=
  mapLoop f A (fuelOf dest) dest (eachStart dest) (eachStart A)

/-- `cmp(x::Int, y::Int)` (base/operators.jl:`cmp(x, y) = isless(x, y) ? -1 : ifelse(isless(y, x), 1, 0)`). -/
def cmpI (x y : I64) : Int := if x < y then -1 else if y < x then 1 else 0

/-- `cmp(A::AbstractVector, B::AbstractVector)` (base/abstractarray.jl:3119-3128) with
element `isequal` `iseq` and `isless` `lt`: `firstindex(v) = first(axes1(v))` for
vectors (lines 452, 140-141). -/
def cmpV {α : Type} (iseq lt : α → α → Bool) (A B : Arr α) : R Int :=
  let ai1 := (linearAxis A).lo
  let bi1 := (linearAxis B).lo
  if !(ai1 == bi1) then .ok (cmpI ai1 bi1)
  else zipLoop A B (fun a b => if !iseq a b then some (if lt a b then -1 else 1) else none)
    (cmpI (lengthA A) (lengthA B)) (fuelOf A) (iterStart A) (iterStart B)

/-- `isless(A::AbstractVector, B::AbstractVector) = cmp(A, B) < 0` (line 3145). -/
def islessV {α : Type} (iseq lt : α → α → Bool) (A B : Arr α) : R Bool := do
  let c ← cmpV iseq lt A B
  .ok (decide (c < 0))

end JuliaLean.AbstractArraySpecs

namespace JuliaLean.ArrayOps

/-- The loop of `_keepat!(a, inds)`, `base/abstractarray.jl:3699-3715`, after `prev`
is defined. Reading an unassigned slot is modelled as copying the slot. -/
def keepatLoop (copyItem : Vec α → Int → Int → Vec α)
    (a : Vec α) (i : Int) (prev : Option Int) : List JInt64 → Out α Int
  | [] => ⟨a, .ok i⟩
  | k :: rest =>
    if (match prev with | some p => decide (¬ p < k.val) | none => false) then
      ⟨a, .error (.argumentError "indices must be unique and sorted")⟩
    else if ¬ (1 ≤ k.val ∧ k.val ≤ a.length) then ⟨a, .error .boundsError⟩
    else
      let a := if i ≠ k.val then copyItem a i k.val else a
      keepatLoop copyItem a (i + 1) (some k.val) rest

end JuliaLean.ArrayOps

/-!
Model of the general `cat(A...; dims)` path of `base/abstractarray.jl` at
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`, lines 1833-1942, 2003-2056
and 2164-2189: `_cat_t`, `dims2cat`, `cat_size_shape`/`_cshp`, `cat_similar`,
`__cat`, `__cat_offset!`, `__cat_offset1!`, `_copy_or_fill!`, and the front ends
`cat`, `vcat`, `hcat`, `typed_vcat`, `typed_hcat`, `cat_t` and `_cat`.

An argument is an array or any other value (`Item`). The output's element type `T`
is reached through `conv : α → R β` (`convert(T, x)` inside `setindex!`/`fill!`);
`zero` is `zero(T)`. The callees outside this file are modelled from master:
`A[inds...] = X` on an `Array` (base/array.jl:1063-1076 for one index,
base/multidimensional.jl:1046-1076 `_setindex!`/`_unsafe_setindex!` otherwise, with
`setindex_shape_check` from base/indices.jl:214-225), `fill!(view(A, inds...), x)`
(the view's `checkbounds`, then `convert(T, x)` once and a store in every cell), and
`Array{T}(undef, dims)` (base/boot.jl:812-850: `ArgumentError` for a negative or
overflowing dimension list).

The output is a 1-based `Array`: its shape and its cells in column-major order,
`none` for an uninitialized cell.
The current model restricts inputs to one Lean element type, assumes the default
`similar` allocation, and models stores into a 1-based `Array`. It does not model
heterogeneous promotion or custom `similar` and destination indexing methods.
-/

namespace JuliaLean.AbstractArraySpecs

/-- A `cat` argument: an array, or any other value (a number, a string, ...). -/
inductive Item (α : Type) where
  | arr (a : Arr α)
  | val (x : α)
  deriving DecidableEq, Repr

/-- `dims2cat(dims)` (base/abstractarray.jl:1898-1903); `maximum` of an empty
collection throws. -/
def dims2cat (dims : List Int) : R (List Bool) :=
  if dims.any (· ≤ 0) then .error .argumentError
  else match dims with
    | [] => .error .argumentError
    | d :: ds => .ok ((List.range (ds.foldl max d).toNat).map (fun (k : Nat) => dims.contains ((k : Int) + 1)))

/-- `dims2cat(::Val{dims}) = dims2cat(dims)` (line 1897); the `Val` parameter is the
list of dimensions. -/
def dims2catVal (dims : List Int) : R (List Bool) := dims2cat dims

/-- `Int + Bool`. -/
def boolI (b : Bool) : I64 := if b then i64 1 else i64 0

/-- `_cs(d, a, b)` (base/abstractarray.jl:1894-1895). -/
def cs (a b : I64) : R I64 := if a = b then .ok a else .error .dimensionMismatch

/-- `_cshp(ndim, dims, shape, nshape)` (base/abstractarray.jl:1872-1892), with fuel
for the simultaneous recursion on three tuples. -/
def cshp : Nat → List Bool → List I64 → List I64 → R (List I64)
  | 0, _, _, _ => .ok []
  | _ + 1, [], [], [] => .ok []
  | _ + 1, [], [], n => .ok n
  | _ + 1, d, [], [] => .ok (List.replicate d.length (i64 1))
  | f + 1, d :: ds, s :: ss, [] => do
      let rest ← cshp f ds ss []
      .ok ((s + boolI d) :: rest)
  | f + 1, _ :: ds, [], n :: ns => do
      let rest ← cshp f ds [] ns
      .ok (n :: rest)
  | f + 1, [], s :: ss, [] => do
      let _ ← cs s (i64 1)
      let rest ← cshp f [] ss []
      .ok (i64 1 :: rest)
  | f + 1, [], s :: ss, n :: ns => do
      let next ← cs s n
      let rest ← cshp f [] ss ns
      .ok (next :: rest)
  | f + 1, d :: ds, s :: ss, n :: ns => do
      let next ← if d then .ok (s + n) else cs s n
      let rest ← cshp f ds ss ns
      .ok (next :: rest)

def cshp' (dims : List Bool) (shape nshape : List I64) : R (List I64) :=
  cshp (dims.length + shape.length + nshape.length + 1) dims shape nshape

/-- `cat_size(A)` (lines 1836-1837): `(1,)` for a value, `size(A)` for an array. -/
def catSizeAll {α : Type} : Item α → List I64
  | .arr a => sizeA a
  | .val _ => [i64 1]

/-- `cat_size(A, d)` (lines 1838-1839) for the 0-based dimension `d`: 1 for a value,
`size(A, d)` for an array (1 past `ndims`). -/
def catSize {α : Type} : Item α → Nat → I64
  | .arr a, d => ((sizeA a)[d]?).getD (i64 1)
  | .val _, _ => i64 1

/-- `size(A, dim)` (lines 42-46) for any Julia `Integer` value `dim`: convert to
`Int` first, read `size(A)`, then tuple-index when `d <= length(s)`, else return 1.
The conversion can throw even when the dimension is past the array's rank. -/
def sizeDimFallback {α : Type} (A : Arr α) (dim : Int) : R I64 :=
  if dim < tmin ∨ tmax < dim then .error .inexactError
  else
    let d := i64 dim
    let s := sizeA A
    if d.val ≤ s.length then
      if d.val < 1 then .error .boundsError
      else match s[(d.val - 1).toNat]? with
        | some n => .ok n
        | none => .error .boundsError
    else .ok (i64 1)

/-- `cat_size(A::AbstractArray, d) = size(A, d)` (line 1839), including the integer
conversion and error behavior of `size(A, d)`. -/
def catSizeIntegerDim {α : Type} (A : Arr α) (dim : Int) : R I64 := sizeDimFallback A dim

/-- `cat_length` (lines 1841-1842): 1 for a value, `length(a)` for an array. -/
def catLength {α : Type} : Item α → I64
  | .arr a => lengthA a
  | .val _ => i64 1

/-- `cat_ndims` (lines 1844-1845): 0 for a value, `ndims(a)` for an array. -/
def catNdims {α : Type} : Item α → Nat
  | .arr a => a.axes.length
  | .val _ => 0

/-- `cat_indices(A, d)` (lines 1847-1848) for the 0-based dimension `d`: `OneTo(1)`
for a value, `axes(A, d)` for an array (`OneTo(1)` past `ndims`). -/
def catIndices {α : Type} : Item α → Nat → Ax
  | .arr a, d => (a.axes[d]?).getD (oneTo (i64 1))
  | .val _, _ => oneTo (i64 1)

/-- `cat_shape(dims, shapes::Tuple)` (lines 1859-1865): fold `_cshp(1, dims, out_shape,
s)` over the shapes from `()`. -/
def catShape (dims : List Bool) (shapes : List (List I64)) : R (List I64) :=
  shapes.foldlM (fun out s => cshp' dims out s) []

/-- `_cat_size_shape(dims, shape, X...)` (lines 1869-1870). -/
def catSizeShapeFrom {α : Type} (dims : List Bool) : List I64 → List (Item α) → R (List I64)
  | shape, [] => .ok shape
  | shape, x :: xs => do
      let s ← cshp' dims shape (catSizeAll x)
      catSizeShapeFrom dims s xs

/-- `cat_size_shape(dims, X...)` (lines 1867-1868). -/
def catSizeShape {α : Type} (dims : List Bool) : List (Item α) → R (List I64)
  | [] => .ok (List.replicate dims.length (i64 0))
  | x :: xs => do
      let s ← cshp' dims [] (catSizeAll x)
      catSizeShapeFrom dims s xs

/-- The output array: its shape and cells, `none` when uninitialized. -/
structure CatOut (β : Type) where
  shape : List I64
  cells : List (Option β)
  deriving DecidableEq, Repr

/-- `Core.checked_dims(d...)` (base/boot.jl:790-817) and the `Memory` constructor
check: `ArgumentError` for a dimension that is negative or `typemax(Int)`, or for a
product that overflows with no zero dimension. -/
def dimsInvalid (shape : List I64) : Bool :=
  shape.any (fun s => decide (s.val < 0) || decide (s.val = tmax)) ||
    (decide (tmax < (shape.map (fun s => s.val)).foldl (· * ·) 1) && !shape.any (fun s => s.val == 0))

/-- `Array{T}(undef, shape)` (base/boot.jl:821-850). -/
def arrayUndef {β : Type} (shape : List I64) : R (CatOut β) :=
  if dimsInvalid shape then .error .argumentError
  else .ok ⟨shape, List.replicate ((shape.map (fun s => s.val.toNat)).foldl (· * ·) 1) none⟩

/-- `cat_similar(A, ::Type{T}, shape::Tuple) = Array{T}(undef, shape)` (line 1850). -/
def catSimilarTuple {α β : Type} (_A : Item α) (shape : List I64) : R (CatOut β) := arrayUndef shape
/-- `cat_similar(A, ::Type{T}, shape::Vector) = Array{T}(undef, shape...)` (line 1851). -/
def catSimilarVector {α β : Type} (_A : Item α) (shape : List I64) : R (CatOut β) := arrayUndef shape
/-- `cat_similar(A::Array, ::Type{T}, shape::Tuple) = Array{T}(undef, shape)` (line 1852). -/
def catSimilarArrayTuple {α β : Type} (_A : Arr α) (shape : List I64) : R (CatOut β) := arrayUndef shape
/-- `cat_similar(A::Array, ::Type{T}, shape::Vector) = Array{T}(undef, shape...)` (line 1853). -/
def catSimilarArrayVector {α β : Type} (_A : Arr α) (shape : List I64) : R (CatOut β) := arrayUndef shape

/-- `similar(a::AbstractArray, ::Type{T}, dims::Dims{N}) = Array{T,N}(undef, dims)`
(line 834), which `similar(a, T, dims::DimOrInd...)` (line 823) reaches for `Int`s. -/
def similarDims {α β : Type} (_a : Arr α) (dims : List I64) : R (CatOut β) := arrayUndef dims

/-- `similar(a, T)` (line 820) calls `similar(a, T, axes(a))`: `OneTo` axes are
converted to lengths (lines 829-834). Other unit axes need a type-specific method;
without one, dispatch throws `MethodError`. -/
def similarDefault {α β : Type} (a : Arr α) : R (CatOut β) :=
  if a.axes.all (fun r => r.kind == .oneTo) then similarDims a (sizeA a)
  else .error .methodError

/-- `cat_similar(A::AbstractArray, T::Type, shape::Tuple) = similar(A, T, shape)` (line 1854). -/
def catSimilarAbsTuple {α β : Type} (A : Arr α) (shape : List I64) : R (CatOut β) := similarDims A shape
/-- `cat_similar(A::AbstractArray, T::Type, shape::Vector) = similar(A, T, shape...)` (line 1855). -/
def catSimilarAbsVector {α β : Type} (A : Arr α) (shape : List I64) : R (CatOut β) :=
  if shape.isEmpty then similarDefault A else similarDims A shape

/-- `cat_similar(X[1], T, shape)` with a tuple shape, dispatching on the argument: an
array (an `Array` or another `AbstractArray`, both allocating `Array{T}(undef, shape)`)
or a value. -/
def catSimilar {α β : Type} (x : Item α) (shape : List I64) : R (CatOut β) :=
  match x with
  | .arr a => catSimilarAbsTuple a shape
  | .val _ => catSimilarTuple x shape

/-- Integers `lo:hi`. -/
def rangeVals (lo hi : I64) : List I64 :=
  (List.range (hi.val - lo.val + 1).toNat).map (fun (k : Nat) => i64 (lo.val + (k : Int)))

/-- Tuples of `CartesianIndices(ranges)` in iteration (column-major) order. -/
def cartProd : List (List I64) → List (List I64)
  | [] => [[]]
  | r :: rs => (cartProd rs).flatMap (fun t => r.map (· :: t))

/-- Column-major position of a 1-based index tuple in an `Array` of the given shape. -/
def outPos : List I64 → List I64 → Int
  | [], _ => 0
  | i :: is, s :: ss => (i.val - 1) + s.val * outPos is ss
  | i :: is, [] => (i.val - 1) + outPos is []


/-- `checkindex(Bool, OneTo(n), r::AbstractRange)` for a unit range `lo:hi`
(base/abstractarray.jl:756-757). -/
def checkindexRange (n : I64) (lo hi : I64) : Bool :=
  decide (hi < lo) || (checkindex (oneTo n) lo && checkindex (oneTo n) hi)

/-- `checkbounds(A, inds...)` for unit-range indices on the output `Array`. -/
def rangesInBounds {β : Type} (A : CatOut β) (inds : List (I64 × I64)) : Bool :=
  decide (inds.length = A.shape.length) && (inds.zip A.shape).all (fun p => checkindexRange p.2 p.1.1 p.1.2)

/-- Store `v` in the cell of every tuple. -/
def storeCells {β : Type} (A : CatOut β) (tuples : List (List I64)) (vs : List β) : List (Option β) :=
  (tuples.zip vs).foldl (fun cs tv => cs.set (outPos tv.1 A.shape).toNat (some tv.2)) A.cells

/-- `A[inds...] = x` on the `Array` output with unit-range indices: with one index,
base/array.jl:1063-1076 (`setindex_shape_check` before `checkbounds`); otherwise
base/multidimensional.jl `_setindex!` (`checkbounds`, then `setindex_shape_check`);
then `A[I] = x′[idx]` in `CartesianIndices(inds)` order along `x`'s iteration order,
each store converting with `convert(T, ·)`. -/
def setRanges {α β : Type} (conv : α → R β) (A : CatOut β) (inds : List (I64 × I64)) (x : Arr α) :
    R (CatOut β) := do
  let lens := inds.map (fun p => i64 1 + (p.2 - p.1))
  if inds.length = 1 then
    shapeCheck prodI (sizeA x) lens
    if !rangesInBounds A inds then .error .boundsError
  else
    if !rangesInBounds A inds then .error .boundsError
    shapeCheck prodI (sizeA x) lens
  let tuples := cartProd (inds.map (fun p => rangeVals p.1 p.2))
  let vs ← x.data.mapM conv
  .ok ⟨A.shape, storeCells A tuples vs⟩

/-- `fill!(view(A, inds...), x)`: the view's `checkbounds`, then `convert(T, x)` once
and a store in every cell of the box. -/
def fillRanges {α β : Type} (conv : α → R β) (A : CatOut β) (inds : List (I64 × I64)) (x : α) :
    R (CatOut β) := do
  if !rangesInBounds A inds then .error .boundsError
  let v ← conv x
  let tuples := cartProd (inds.map (fun p => rangeVals p.1 p.2))
  .ok ⟨A.shape, storeCells A tuples (tuples.map (fun _ => v))⟩

/-- `_copy_or_fill!(A, inds, x)` (lines 1941-1942): `fill!` for a value, `A[inds...] = x`
for an array. -/
def copyOrFill {α β : Type} (conv : α → R β) (A : CatOut β) (inds : List (I64 × I64)) : Item α → R (CatOut β)
  | .val x => fillRanges conv A inds x
  | .arr x => setRanges conv A inds x

/-- `__cat_offset1!(A, shape, catdims, offsets, x)` (base/abstractarray.jl:1930-1939). -/
def catOffset1 {α β : Type} (conv : α → R β) (A : CatOut β) (shape : List I64) (catdims : List Bool)
    (offsets : List I64) (x : Item α) : R (CatOut β × List I64) := do
  let isCat := fun (i : Nat) => catdims.getD i false
  let inds := (List.range offsets.length).map (fun i =>
    if isCat i then
      let r := catIndices x i
      (offsets.getD i (i64 0) + r.lo, offsets.getD i (i64 0) + r.hi)
    else (i64 1, shape.getD i (i64 0)))
  let A ← copyOrFill conv A inds x
  let newoffsets := (List.range offsets.length).map (fun i =>
    if isCat i then offsets.getD i (i64 0) + catSize x i else offsets.getD i (i64 0))
  .ok (A, newoffsets)

/-- `__cat_offset!(A, shape, catdims, offsets, x, X...)` and `__cat_offset!(A, shape,
catdims, offsets) = A` (lines 1923-1928). -/
def catOffset {α β : Type} (conv : α → R β) (A : CatOut β) (shape : List I64) (catdims : List Bool) :
    List I64 → List (Item α) → R (CatOut β)
  | _, [] => .ok A
  | offsets, x :: X => do
      let (A', newoffsets) ← catOffset1 conv A shape catdims offsets x
      catOffset conv A' shape catdims newoffsets X

/-- `__cat(A, shape, catdims, X...)` (line 1921). -/
def catInner {α β : Type} (conv : α → R β) (A : CatOut β) (shape : List I64) (catdims : List Bool)
    (X : List (Item α)) : R (CatOut β) :=
  catOffset conv A shape catdims (List.replicate shape.length (i64 0)) X

/-- `_cat_t(dims, T, X...)` (lines 1907-1915); `X[1]` throws `BoundsError` without
arguments. -/
def catT {α β : Type} (conv : α → R β) (zero : β) (dims : List Int) (X : List (Item α)) : R (CatOut β) := do
  let catdims ← dims2cat dims
  let shape ← catSizeShape catdims X
  let A ← match X with
    | [] => .error .boundsError
    | x :: _ => catSimilar x shape
  let A : CatOut β := if (catdims.filter id).length > 1 then { A with cells := A.cells.map (fun _ => some zero) } else A
  catInner conv A shape catdims X

/-- `cat_t(::Type{T}, X...; dims) = _cat_t(dims, T, X...)` (line 1918). -/
def catTKw {α β : Type} (conv : α → R β) (zero : β) (X : List (Item α)) (dims : List Int) : R (CatOut β) :=
  catT conv zero dims X

/-- `_cat(dims, X...) = _cat_t(dims, promote_eltypeof(X...), X...)` (line 1905): the
element type is the arguments' common type `α`, so stores need no conversion. -/
def catPromote {α : Type} (zero : α) (dims : List Int) (X : List (Item α)) : R (CatOut α) :=
  catT (fun x => .ok x) zero dims X

/-- `_cat(catdims, A::AbstractArray{T}...) = _cat_t(catdims, T, A...)` (line 2171). -/
def catSame {α : Type} (zero : α) (dims : List Int) (A : List (Arr α)) : R (CatOut α) :=
  catT (fun x => .ok x) zero dims (A.map .arr)

/-- `cat(A...; dims) = _cat(dims, A...)` (line 2169). -/
def catKw {α : Type} (zero : α) (X : List (Item α)) (dims : List Int) : R (CatOut α) := catPromote zero dims X

/-- `vcat(X...) = cat(X...; dims=Val(1))` (line 2003). -/
def vcatAny {α : Type} (zero : α) (X : List (Item α)) : R (CatOut α) := catKw zero X [1]
/-- `hcat(X...) = cat(X...; dims=Val(2))` (line 2053). -/
def hcatAny {α : Type} (zero : α) (X : List (Item α)) : R (CatOut α) := catKw zero X [2]
/-- `typed_vcat(::Type{T}, X...) = _cat_t(Val(1), T, X...)` (line 2055). -/
def typedVcatAny {α β : Type} (conv : α → R β) (zero : β) (X : List (Item α)) : R (CatOut β) := catT conv zero [1] X
/-- `typed_hcat(::Type{T}, X...) = _cat_t(Val(2), T, X...)` (line 2056). -/
def typedHcatAny {α β : Type} (conv : α → R β) (zero : β) (X : List (Item α)) : R (CatOut β) := catT conv zero [2] X

/-- `vcat(A::AbstractArray) = cat(A; dims=Val(1))` (line 2175). -/
def vcat1 {α : Type} (zero : α) (A : Arr α) : R (CatOut α) := catKw zero [.arr A] [1]
/-- `vcat(A::AbstractArray, B::AbstractArray) = cat(A, B; dims=Val(1))` (line 2176). -/
def vcat2 {α : Type} (zero : α) (A B : Arr α) : R (CatOut α) := catKw zero [.arr A, .arr B] [1]
/-- `vcat(A::AbstractArray...) = cat(A...; dims=Val(1))` (line 2177). -/
def vcatArrs {α : Type} (zero : α) (A : List (Arr α)) : R (CatOut α) := catKw zero (A.map .arr) [1]
/-- `vcat(A::Union{AbstractArray,Number}...) = cat(A...; dims=Val(1))` (line 2178). -/
def vcatMixed {α : Type} (zero : α) (A : List (Item α)) : R (CatOut α) := catKw zero A [1]
/-- `hcat(A::AbstractArray) = cat(A; dims=Val(2))` (line 2179). -/
def hcat1 {α : Type} (zero : α) (A : Arr α) : R (CatOut α) := catKw zero [.arr A] [2]
/-- `hcat(A::AbstractArray, B::AbstractArray) = cat(A, B; dims=Val(2))` (line 2180). -/
def hcat2 {α : Type} (zero : α) (A B : Arr α) : R (CatOut α) := catKw zero [.arr A, .arr B] [2]
/-- `hcat(A::AbstractArray...) = cat(A...; dims=Val(2))` (line 2181). -/
def hcatArrs {α : Type} (zero : α) (A : List (Arr α)) : R (CatOut α) := catKw zero (A.map .arr) [2]
/-- `hcat(A::Union{AbstractArray,Number}...) = cat(A...; dims=Val(2))` (line 2182). -/
def hcatMixed {α : Type} (zero : α) (A : List (Item α)) : R (CatOut α) := catKw zero A [2]

/-- `typed_vcat(T::Type, A::AbstractArray) = _cat_t(Val(1), T, A)` (line 2184). -/
def typedVcat1 {α β : Type} (conv : α → R β) (zero : β) (A : Arr α) : R (CatOut β) := catT conv zero [1] [.arr A]
/-- `typed_vcat(T::Type, A::AbstractArray, B::AbstractArray) = _cat_t(Val(1), T, A, B)` (line 2185). -/
def typedVcat2 {α β : Type} (conv : α → R β) (zero : β) (A B : Arr α) : R (CatOut β) :=
  catT conv zero [1] [.arr A, .arr B]
/-- `typed_vcat(T::Type, A::AbstractArray...) = _cat_t(Val(1), T, A...)` (line 2186). -/
def typedVcatArrs {α β : Type} (conv : α → R β) (zero : β) (A : List (Arr α)) : R (CatOut β) :=
  catT conv zero [1] (A.map .arr)
/-- `typed_hcat(T::Type, A::AbstractArray) = _cat_t(Val(2), T, A)` (line 2187). -/
def typedHcat1 {α β : Type} (conv : α → R β) (zero : β) (A : Arr α) : R (CatOut β) := catT conv zero [2] [.arr A]
/-- `typed_hcat(T::Type, A::AbstractArray, B::AbstractArray) = _cat_t(Val(2), T, A, B)` (line 2188). -/
def typedHcat2 {α β : Type} (conv : α → R β) (zero : β) (A B : Arr α) : R (CatOut β) :=
  catT conv zero [2] [.arr A, .arr B]
/-- `typed_hcat(T::Type, A::AbstractArray...) = _cat_t(Val(2), T, A...)` (line 2189). -/
def typedHcatArrs {α β : Type} (conv : α → R β) (zero : β) (A : List (Arr α)) : R (CatOut β) :=
  catT conv zero [2] (A.map .arr)

/-- The same array with every axis replaced by `OneTo(length)`. -/
def rebase {α : Type} (A : Arr α) : Arr α := { A with axes := A.axes.map (fun r => oneTo (axLength r)) }

end JuliaLean.AbstractArraySpecs

/-!
The generic concatenation kernel at Julia commit
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`, abstracting the dynamically
selected `similar`, range assignment, view and fill methods as operations. The
operations return the actual destination state and may throw. Array arguments
carry their own element type, including when the array is empty.
-/

namespace JuliaLean.AbstractArraySpecs.CatTyped

structure Universe where
  Ty : Type
  Val : Ty → Type

inductive Item (U : Universe) where
  | scalar (t : U.Ty) (value : U.Val t)
  | array (t : U.Ty) (value : Arr (U.Val t))

def eltype {U : Universe} : Item U → U.Ty
  | .scalar t _ => t
  | .array t _ => t

def sizeAll {U : Universe} : Item U → List I64
  | .scalar _ _ => [i64 1]
  | .array _ a => sizeA a

def sizeDim {U : Universe} : Item U → Nat → I64
  | .scalar _ _, _ => i64 1
  | .array _ a, d => ((sizeA a)[d]?).getD (i64 1)

def indices {U : Universe} : Item U → Nat → Ax
  | .scalar _ _, _ => oneTo (i64 1)
  | .array _ a, d => (a.axes[d]?).getD (oneTo (i64 1))

def shapeFrom {U : Universe} (dims : List Bool) : List I64 → List (Item U) → R (List I64)
  | s, [] => .ok s
  | s, x :: xs => do
      let s ← cshp' dims s (sizeAll x)
      shapeFrom dims s xs

def shape {U : Universe} (dims : List Bool) : List (Item U) → R (List I64)
  | [] => .ok (List.replicate dims.length (i64 0))
  | x :: xs => do
      let s ← cshp' dims [] (sizeAll x)
      shapeFrom dims s xs

/-- Operations dispatched on the source and destination array types. `Dest t`
contains the state of an array whose declared element type is `t`. `viewFill`
models `fill!(view(A, inds...), x)` as one operation, so its bounds and
conversion errors occur in the implementation's own order. `assign` models
`A[inds...] = x`. -/
structure Ops (U : Universe) where
  Dest : U.Ty → Type
  promote : List U.Ty → R U.Ty
  convert : (s t : U.Ty) → U.Val s → R (U.Val t)
  zero : (t : U.Ty) → R (U.Val t)
  similar : (t : U.Ty) → Item U → List I64 → R (Dest t)
  axes : {t : U.Ty} → Dest t → List Ax
  read : {t : U.Ty} → Dest t → List I64 → R (U.Val t)
  write : {s t : U.Ty} → Dest t → List I64 → U.Val s → R (Dest t)
  fillAll : {t : U.Ty} → Dest t → U.Val t → R (Dest t)
  viewFill : {s t : U.Ty} → Dest t → List (I64 × I64) → U.Val s → R (Dest t)
  assign : {s t : U.Ty} → Dest t → List (I64 × I64) → Arr (U.Val s) → R (Dest t)

def copyOrFill {U : Universe} (ops : Ops U) {t : U.Ty} (a : ops.Dest t)
    (inds : List (I64 × I64)) : Item U → R (ops.Dest t)
  | .scalar _ x => ops.viewFill a inds x
  | .array _ x => ops.assign a inds x

def offset1 {U : Universe} (ops : Ops U) {t : U.Ty} (a : ops.Dest t)
    (shape : List I64) (catdims : List Bool) (offsets : List I64) (x : Item U) :
    R (ops.Dest t × List I64) := do
  let inds := (List.range offsets.length).map (fun i =>
    if catdims.getD i false then
      let r := indices x i
      (offsets.getD i (i64 0) + r.lo, offsets.getD i (i64 0) + r.hi)
    else (i64 1, shape.getD i (i64 0)))
  let a ← copyOrFill ops a inds x
  let next := (List.range offsets.length).map (fun i =>
    if catdims.getD i false then offsets.getD i (i64 0) + sizeDim x i
    else offsets.getD i (i64 0))
  .ok (a, next)

def offset {U : Universe} (ops : Ops U) {t : U.Ty} (shape : List I64)
    (catdims : List Bool) : ops.Dest t → List I64 → List (Item U) → R (ops.Dest t)
  | a, _, [] => .ok a
  | a, offsets, x :: xs => do
      let (a, offsets) ← offset1 ops a shape catdims offsets x
      offset ops shape catdims a offsets xs

def catT {U : Universe} (ops : Ops U) (t : U.Ty) (dims : List Int)
    (xs : List (Item U)) : R (ops.Dest t) := do
  let catdims ← dims2cat dims
  let shape ← shape catdims xs
  let a ← match xs with
    | [] => .error .boundsError
    | x :: _ => ops.similar t x shape
  let a ← if (catdims.filter id).length > 1 then do
    let z ← ops.zero t
    ops.fillAll a z
  else .ok a
  offset ops shape catdims a (List.replicate shape.length (i64 0)) xs

/-- The result retains the selected type together with its dependent destination. -/
def catPromote {U : Universe} (ops : Ops U) (dims : List Int) (xs : List (Item U)) :
    R (Sigma ops.Dest) := do
  let t ← ops.promote (xs.map eltype)
  let a ← catT ops t dims xs
  .ok ⟨t, a⟩


/-- Dense `Array` allocation for a requested element type. The input is ignored
by the `cat_similar` fallback and `Array` methods. -/
def denseSimilar {U : Universe} (t : U.Ty) (_x : Item U) (shape : List I64) :
    R (CatOut (U.Val t)) := arrayUndef shape

/-- The dense destination's range assignment and scalar-view fill, including
conversion from each argument's own element type. -/
def denseCopy {U : Universe} (convert : (s t : U.Ty) → U.Val s → R (U.Val t))
    {t : U.Ty} (a : CatOut (U.Val t)) (inds : List (I64 × I64)) :
    Item U → R (CatOut (U.Val t))
  | .scalar s x => fillRanges (convert s t) a inds x
  | .array s x => setRanges (convert s t) a inds x


end JuliaLean.AbstractArraySpecs.CatTyped

namespace JuliaLean.Reduce

/-! ### `reduce(vcat, vs)`, `reduce(hcat, vs)` -/

namespace Cat
variable {α : Type}

/-- `reduce(vcat, A::AbstractVector{<:AbstractVector})`, `base/abstractarray.jl:1741-1753,
1827-1828`: `_typed_vcat!` copies each `V[k]` into `a[pos:p1]`; an empty `A` throws from
`mapreduce(eltype, promote_type, A)`. -/
def reduceVcat (vs : List (List α)) : R (List α) :=
  if vs = [] then .error .argumentError
  else .ok (vs.foldl (fun a v => a ++ v) [])

/-- `reduce(hcat, A::AbstractVector{<:AbstractVector})`, `base/abstractarray.jl:1768-1803,
1830-1831`: every column must have `size(A[1], 1)` rows (`DimensionMismatch`); dense
columns are copied in order. Returns `(nrows, ncols, column-major data)`. -/
def reduceHcat (vs : List (List α)) : R (Nat × Nat × List α) :=
  match vs with
  | [] => .error .argumentError
  | v1 :: _ =>
    if vs.all (fun v => v.length = v1.length) then
      .ok (v1.length, vs.length, vs.foldl (fun a v => a ++ v) [])
    else .error .dimensionMismatch

end Cat

end JuliaLean.Reduce

/-!
Scalar `hvncat` methods (master base/abstractarray.jl:2398-2399).

Types have nominal codes (`Nat`); a value records its concrete `typeof` code. This
keeps the distinction between a requested storage type such as `Any` and a value's
concrete type. `accepts T t` represents Julia's subtype relation `t <: T` and
constrains conversion results in the contracts. Payload types remain arbitrary.
`fill(x)` with no dimensions allocates one cell, with element type `typeof(x)`
(base/array.jl:583-587), which is independent of the static type at the call site.
-/

namespace JuliaLean.AbstractArraySpecs

/-- A value and the nominal code of its concrete Julia type. -/
structure TypedValue (α : Type) where
  typeCode : Nat
  payload : α
  deriving DecidableEq, Repr

/-- The result's storage element type, separately from its payload representation. -/
structure TypedCatOut (α : Type) where
  elementType : Nat
  storage : CatOut α
  deriving DecidableEq, Repr

/-- `_typed_hvncat(T::Type, ::Val{0}, x) = fill(convert(T, x))`
(base/abstractarray.jl:2398), for a non-array scalar. -/
def hvn0Value {α β : Type} (fillScalar : TypedValue β → TypedCatOut β)
    (conv : Nat → TypedValue α → R (TypedValue β)) (T : Nat)
    (x : TypedValue α) : R (TypedCatOut β) := do
  let y ← conv T x
  .ok (fillScalar y)

/-- `_typed_hvncat(T::Type, ::Val{0}, x::Number) = fill(convert(T, x))`
(base/abstractarray.jl:2399). -/
def hvn0Number {α β : Type} (fillScalar : TypedValue β → TypedCatOut β)
    (conv : Nat → TypedValue α → R (TypedValue β)) (T : Nat)
    (x : TypedValue α) : R (TypedCatOut β) := do
  let y ← conv T x
  .ok (fillScalar y)


/-- `_typed_hvncat(::Type{T}, ::Val{N})` (base/abstractarray.jl:2411-2415).
The `Val(0)` no-argument specialization is a separate method; this row is reached for
negative or positive N. -/
def hvnEmpty {α : Type} (T : Nat) (N : Int) : R (TypedCatOut α) := do
  if N < 0 then .error .argumentError
  let A ← arrayUndef (List.replicate N.toNat (i64 0))
  .ok ⟨T, A⟩

/-- `_typed_hvncat(T, ::Val{N}, xs::Number...)` (lines 2417-2421): negative N
is rejected before `T[xs...]`, then reshape to `(1, ..., 1, length(xs))`.
`mapM conv` is the element-converting stores of `T[xs...]`
(base/array.jl:445-470); the reshape preserves the cells. -/
def hvnNumbersDim {α β : Type} (conv : Nat → TypedValue α → R (TypedValue β)) (T : Nat)
    (N : Int) (xs : List (TypedValue α)) : R (TypedCatOut β) := do
  if N < 0 then .error .argumentError
  let ys ← xs.mapM (conv T)
  let shape := List.replicate (N - 1).toNat (i64 1) ++ [i64 xs.length]
  .ok ⟨T, ⟨shape, ys.map (fun y => some y.payload)⟩⟩

end JuliaLean.AbstractArraySpecs

/-!
Model of `copyto!(dest::AbstractArray, src::AbstractArray)` (base/abstractarray.jl:1072-1080),
`copyto!(deststyle, dest, srcstyle, src)` (lines 1082-1086) and `copyto_unaliased!`
(lines 1088-1123), including the `BitArray` destination path `_copyto_bitarray!`
(base/bitarray.jl:507-532) and `unalias` (lines 1566, 1582).
-/

namespace JuliaLean.AbstractArraySpecs

/-- Single-index implementation (lines 1095-1098):
`for i in srcinds; dest[i + Δi] = src[i]; end`. `srcinds = LinearIndices(src)` iterates
the unit range `linearAxis src` (the same range as `eachindex(IndexLinear(), src)`) for
either style of `src`; `eachindexStep` from `.rngStart` walks that range. -/
def copyLL {α : Type} (src : Arr α) (Δ : I64) : Nat → Arr α → IterState → R (Arr α)
  | 0, D, _ => .ok D
  | n + 1, D, st =>
    match eachindexStep src st with
    | none => .ok D
    | some (I, st') => do
        let v ← getindex src I
        let D' ← setindex D v (I.map (· + Δ))
        copyLL src Δ n D' st'

/-- Dual-index implementation (lines 1100-1104):
`i = idf - 1; for a in src; dest[i += 1] = a; end`. -/
def copyLC {α : Type} (src : Arr α) : Nat → Arr α → I64 → IterState → R (Arr α)
  | 0, D, _, _ => .ok D
  | n + 1, D, i, st => do
    match ← iterateA src st with
    | none => .ok D
    | some (a, st') =>
      let i' := i + i64 1
      let D' ← setindex D a [i']
      copyLC src n D' i' st'

/-- Shared-iterator implementation (lines 1109-1112):
`for I in iterdest; dest[I] = src[I]; end`. -/
def copyShared {α : Type} (src : Arr α) : Nat → Arr α → IterState → R (Arr α)
  | 0, D, _ => .ok D
  | n + 1, D, st =>
    match eachindexStep D st with
    | none => .ok D
    | some (I, st') => do
        let v ← getindex src I
        let D' ← setindex D v I
        copyShared src n D' st'

/-- `iterdest == itersrc` (line 1108) for `eachindex(dest)` and `eachindex(src)`: two
unit ranges compare with range `==` (base/range.jl:1141-1180); two `CartesianIndices`
compare as arrays, equal exactly when their index ranges are pairwise `==`
(base/abstractarray.jl:3149-3163); a unit range never equals a `CartesianIndices` of
another dimensionality (their axes differ). -/
def iterEq {α : Type} (dest src : Arr α) : Bool :=
  match eachRange dest, eachRange src with
  | true, true => axEq (linearAxis dest) (linearAxis src)
  | false, false => axesEq dest.axes src.axes
  | _, _ => false

/-- `copyto_unaliased!(deststyle, dest, srcstyle, src)` (lines 1088-1123) for the given
style arguments `ds` and `ss` (which `copyto!(deststyle, dest, srcstyle, src)` may pass
independently of `IndexStyle(dest)` and `IndexStyle(src)`). -/
def copytoUnaliasedS {α : Type} (ds ss : Style) (dest src : Arr α) : R (Arr α) :=
  if isemptyA src then .ok dest
  else
    let destinds := linearAxis dest
    let srcinds := linearAxis src
    let idf := destinds.lo
    let isf := srcinds.lo
    let Δ := idf - isf
    if !(checkindex destinds (isf + Δ) && checkindex destinds (srcinds.hi + Δ)) then
      .error .boundsError
    else
      match ds, ss with
      | .linear, .linear => copyLL src Δ (fuelOf src) dest .rngStart
      | .linear, .cartesian => copyLC src (fuelOf src) dest (idf - i64 1) (iterStart src)
      | .cartesian, _ =>
        if iterEq dest src then copyShared src (fuelOf dest) dest (eachStart dest)
        else mapLoop id src (fuelOf dest) dest (eachStart dest) (eachStart src)

/-- `copyto_unaliased!(IndexStyle(dest), dest, IndexStyle(src), src)`. -/
def copytoUnaliased {α : Type} (dest src : Arr α) : R (Arr α) :=
  copytoUnaliasedS dest.style src.style dest src

/-- `unalias(dest, A) = mightalias(dest, A) ? unaliascopy(A) : A` (line 1566) with
`unaliascopy(A) = copy(A)` (line 1582). Arrays are values here, so a copy of `src` has the
same contents as `src`; `aliased` is the outcome of `mightalias(dest, src)`. -/
def unaliasA {α : Type} (aliased : Bool) (src : Arr α) : Arr α :=
  if aliased then { src with data := src.data } else src


/-- `copyto!(dest::AbstractArray, src::AbstractArray)` (lines 1072-1080); `destBit` is
`dest isa BitArray`, `aliased` is `mightalias(dest, src)`. -/
def copytoA {α : Type} (copytoBitarray : Arr α → Arr α → R (Arr α))
    (destBit aliased : Bool) (dest src : Arr α) : R (Arr α) :=
  if isemptyA src then .ok dest
  else if destBit then copytoBitarray dest src
  else
    let src' := unaliasA aliased src
    copytoUnaliased dest src'

/-- `copyto!(deststyle::IndexStyle, dest, srcstyle::IndexStyle, src)` (lines 1082-1086). -/
def copytoStyles {α : Type} (ds ss : Style) (aliased : Bool) (dest src : Arr α) : R (Arr α) :=
  if isemptyA src then .ok dest
  else
    let src' := unaliasA aliased src
    copytoUnaliasedS ds ss dest src'

/-- `similar(a)` (base/abstractarray.jl:819-834) when every axis of `a` is a `Base.OneTo`:
`similar(a, T, axes(a))` converts the axes with `to_shape` (`last` of each `OneTo`) and
returns `Array{T,N}(undef, dims)`, an `IndexLinear` array with axes `OneTo.(dims)` whose
uninitialized contents are `junk`. For other axes Base defines no method; the array type
must provide its own `similar` (doc/src/manual/interfaces.md, "Abstract arrays"), so the
result is `none`. -/
def similarArr {α : Type} (a : Arr α) (junk : List α) : Option (Arr α) :=
  if a.axes.all (fun r => decide (r.kind = .oneTo)) then
    some ⟨a.axes.map (fun r => oneTo r.hi), .linear, junk⟩
  else none

/-- `copy(a::AbstractArray) = copymutable(a) = copyto!(similar(a), a)`
(base/abstractarray.jl:1154-1157, 1211-1214). -/
def copyA {α : Type} (copytoBitarray : Arr α → Arr α → R (Arr α))
    (a : Arr α) (junk : List α) : Option (R (Arr α)) :=
  (similarArr a junk).map (fun s => copytoA copytoBitarray false false s a)

end JuliaLean.AbstractArraySpecs

/-!
Models of the remaining `copyto!`, `copy!` and `copyto_axcheck!` methods of
`base/abstractarray.jl` (master `bbfa0ce4150`, lines 920-1189), built on the array
model of `Model.lean` and `Copy.lean`.

An iterable `src` (any collection, possibly without a length) is the list of the
elements `iterate(src)` yields, in order; `hasLen` is `haslength(src)`.
-/

namespace JuliaLean.AbstractArraySpecs

/-! ## From an iterable source -/

/-- The loop of `copyto!(dest::AbstractArray, src)` (lines 941-951): `y` is the current
`iterate(destiter)` result, `D` the array whose `eachindex` is `destiter`. -/
def copyIterLoop {α : Type} (D : Arr α) : Arr α → Option (List I64 × IterState) → List α → R (Arr α)
  | dest, _, [] => .ok dest
  | _, none, _ :: _ => .error .argumentError
  | dest, some (I, st), x :: xs => do
      let dest' ← setindex dest x I
      copyIterLoop D dest' (eachindexStep D st) xs

/-- `copyto!(dest::AbstractArray, src)` (lines 941-951). -/
def copytoIter {α : Type} (dest : Arr α) (src : List α) : R (Arr α) :=
  copyIterLoop dest dest (eachindexStep dest (eachStart dest)) src

/-- `for x in src; dest[i] = x; i += 1; end` (lines 960-968, 993-998). -/
def writeLinear {α : Type} : Arr α → I64 → List α → R (Arr α)
  | dest, _, [] => .ok dest
  | dest, i, x :: xs => do
      let dest' ← setindex dest x [i]
      writeLinear dest' (i + i64 1) xs

/-- `copyto!(dest::AbstractArray, dstart::Integer, src)` (lines 953-971) for an `Int`
`dstart`. -/
def copytoIterAt {α : Type} (hasLen : Bool) (dest : Arr α) (dstart : I64) (src : List α) :
    R (Arr α) :=
  let i := dstart
  if hasLen && decide (i64 0 < lengthA dest) then
    let n := i64 src.length
    if n == i64 0 then .ok dest
    else do
      checkbounds dest [i]
      if !decide (n ≤ (linearAxis dest).hi - i + i64 1) then .error .boundsError
      else writeLinear dest i src
  else writeLinear dest i src

/-- The skip loop `for j = 1:(sstart-1)` (lines 977-985 and 1013-1021): `ys` is the rest
of `src` starting at `y`; each step throws `ArgumentError` when `y === nothing`. -/
def skipSrc {α : Type} : Nat → List α → R (List α)
  | 0, ys => .ok ys
  | _ + 1, [] => .error .argumentError
  | k + 1, _ :: ys => skipSrc k ys

/-- `copyto!(dest::AbstractArray, dstart::Integer, src, sstart::Integer)` (lines 973-1000)
for `Int` arguments. -/
def copytoIterFrom {α : Type} (dest : Arr α) (dstart : I64) (src : List α) (sstart : I64) :
    R (Arr α) :=
  if sstart < i64 1 then .error .argumentError
  else do
    let ys ← skipSrc (sstart.val - 1).toNat src
    match ys with
    | [] => .error .argumentError
    | _ :: _ => writeLinear dest dstart ys

/-- `for val in Iterators.take(Iterators.rest(src, st), n-1); i += 1; dest[i] = val; end`
(lines 1031-1034), returning `dest` and the final `i`. -/
def takeLoop {α : Type} : Arr α → I64 → List α → R (Arr α × I64)
  | dest, i, [] => .ok (dest, i)
  | dest, i, x :: xs => do
      let dest' ← setindex dest x [i + i64 1]
      takeLoop dest' (i + i64 1) xs

/-- `copyto!(dest::AbstractArray, dstart::Integer, src, sstart::Integer, n::Integer)`
(lines 1003-1037) for `Int` arguments; `dstart ∈ inds` with `inds = LinearIndices(dest)`. -/
def copytoIterN {α : Type} (dest : Arr α) (dstart : I64) (src : List α) (sstart n : I64) :
    R (Arr α) :=
  if n < i64 0 then .error .argumentError
  else if n == i64 0 then .ok dest
  else
    let inds := linearAxis dest
    if sstart < i64 1 then .error .argumentError
    else if !(inAx dstart inds && decide (n ≤ inds.hi - dstart + i64 1)) then .error .boundsError
    else
      let dmax := dstart + n - i64 1
      do
        let ys ← skipSrc (sstart.val - 1).toNat src
        match ys with
        | [] => .error .argumentError
        | val :: rest =>
          let dest ← setindex dest val [dstart]
          let (dest, i) ← takeLoop dest dstart (rest.take (n.val - 1).toNat)
          if i < dmax then .error .boundsError else .ok dest

/-! ## Between arrays, with start indices -/

/-- `@inbounds for i = 0:n-1; dest[dstart+i] = src′[sstart+i]; end` (lines 1149-1151). -/
def copyNLoop {α : Type} (src : Arr α) (dstart sstart : I64) : Nat → Nat → Arr α → R (Arr α)
  | 0, _, D => .ok D
  | k + 1, i, D => do
      let v ← getindex src [sstart + i64 i]
      let D' ← setindex D v [dstart + i64 i]
      copyNLoop src dstart sstart k (i + 1) D'

/-- `copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray, sstart::Integer,
n::Integer)` (lines 1135-1153) for `Int` arguments; `aliased` is `mightalias(dest, src)`. -/
def copytoN {α : Type} (aliased : Bool) (dest : Arr α) (dstart : I64) (src : Arr α)
    (sstart n : I64) : R (Arr α) :=
  if n == i64 0 then .ok dest
  else if n < i64 0 then .error .argumentError
  else
    let destinds := linearAxis dest
    let srcinds := linearAxis src
    if !(checkindex destinds dstart && decide (n ≤ destinds.hi - dstart + i64 1)) then
      .error .boundsError
    else if !(checkindex srcinds sstart && decide (n ≤ srcinds.hi - sstart + i64 1)) then
      .error .boundsError
    else
      let src' := unaliasA aliased src
      copyNLoop src' dstart sstart n.val.toNat 0 dest

/-- `copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray)` (lines 1125-1127). -/
def copytoAt {α : Type} (aliased : Bool) (dest : Arr α) (dstart : I64) (src : Arr α) : R (Arr α) :=
  copytoN aliased dest dstart src (linearAxis src).lo (lengthA src)

/-- `copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray, sstart::Integer)`
(lines 1129-1133); `checkbounds(Bool, srcinds, sstart)` checks `sstart` against
`eachindex(IndexLinear(), LinearIndices(src))`, the range `linearAxis src`. -/
def copytoFrom {α : Type} (aliased : Bool) (dest : Arr α) (dstart : I64) (src : Arr α)
    (sstart : I64) : R (Arr α) :=
  let srcinds := linearAxis src
  if !checkindex srcinds sstart then .error .boundsError
  else copytoN aliased dest dstart src sstart (srcinds.hi - sstart + i64 1)

/-! ## Rectangular blocks -/



/-- `checkindex(Bool, inds, r::AbstractRange)` (base/abstractarray.jl:756-757):
`isempty(r) | (checkindex(Bool, inds, first(r)) & checkindex(Bool, inds, last(r)))`. -/
def checkindexRg (inds : Ax) (r : Rg) : Bool :=
  decide (r.len = 0) || (checkindex inds r.first && checkindex inds (r.at (r.len - 1)))

/-- `checkbounds_indices(Bool, inds, I)` (lines 722-728) for range indices. -/
def checkboundsRgs : List Ax → List Rg → Bool
  | inds, [] => inds.all (fun x => axLength x == i64 1)
  | inds, r :: I => checkindexRg (inds.headD (oneTo (i64 1))) r && checkboundsRgs inds.tail I

/-- The inner loop of lines 1171-1175: `idest = first(ir_dest); for isrc in ir_src;
B[idest,jdest] = A′[isrc,jsrc]; idest += step(ir_dest); end`. -/
def blockInner {α : Type} (A : Arr α) (stepI jdest jsrc : I64) : I64 → List I64 → Arr α → R (Arr α)
  | _, [], B => .ok B
  | idest, isrc :: is, B => do
      let v ← getindex A [isrc, jsrc]
      let B' ← setindex B v [idest, jdest]
      blockInner A stepI jdest jsrc (idest + stepI) is B'

/-- The outer loop of lines 1170-1177: `for jsrc in jr_src; ...; jdest += step(jr_dest); end`. -/
def blockOuter {α : Type} (A : Arr α) (ird : Rg) (stepJ : I64) (irs : List I64) :
    I64 → List I64 → Arr α → R (Arr α)
  | _, [], B => .ok B
  | jdest, jsrc :: js, B => do
      let B' ← blockInner A ird.step jdest jsrc ird.first irs B
      blockOuter A ird stepJ irs (jdest + stepJ) js B'

/-- `copyto!(B::AbstractVecOrMat, ir_dest, jr_dest, A::AbstractVecOrMat, ir_src, jr_src)`
(lines 1159-1181); `aliased` is `mightalias(B, A)`. -/
def copytoBlock {α : Type} (aliased : Bool) (B : Arr α) (ird jrd : Rg) (A : Arr α) (irs jrs : Rg) :
    R (Arr α) :=
  if i64 ird.len ≠ i64 irs.len then .error .argumentError
  else if i64 jrd.len ≠ i64 jrs.len then .error .argumentError
  else do
    if !checkboundsRgs B.axes [ird, jrd] then .error .boundsError
    if !checkboundsRgs A.axes [irs, jrs] then .error .boundsError
    let A' := unaliasA aliased A
    blockOuter A' ird jrd.step irs.elems jrd.first jrs.elems B

/-! ## With an axes check -/

/-- `_checkaxs(axd, axs) = axd == axs || throw(DimensionMismatch(...))` (line 1184). -/
def checkaxs (axd axs : List Ax) : R Bool :=
  if axesEq axd axs then .ok true else .error .dimensionMismatch

/-- `copyto_axcheck!(dest, src)` (lines 1186-1189). -/
def copytoAxcheck {α : Type} (copytoBitarray : Arr α → Arr α → R (Arr α))
    (destBit aliased : Bool) (dest src : Arr α) : R (Arr α) := do
  let _ ← checkaxs dest.axes src.axes
  copytoA copytoBitarray destBit aliased dest src

/-- `copy!(dst::AbstractArray, src::AbstractArray)` (lines 929-933). -/
def copyBangA {α : Type} (copytoBitarray : Arr α → Arr α → R (Arr α))
    (destBit aliased : Bool) (dst src : Arr α) : R (Arr α) :=
  if !axesEq dst.axes src.axes then .error .argumentError
  else copytoA copytoBitarray destBit aliased dst src

/-- `copy!(dst::AbstractVector, src::AbstractVector)` (lines 920-927); `resize` is the
`resize!` method of `dst`'s type. -/
def copyBangV {α : Type} (copytoBitarray : Arr α → Arr α → R (Arr α))
    (resize : Arr α → I64 → R (Arr α)) (destBit aliased : Bool)
    (dst src : Arr α) : R (Arr α) :=
  if !((linearAxis dst).lo == (linearAxis src).lo) then .error .argumentError
  else do
    let dst ← if lengthA dst ≠ lengthA src then resize dst (lengthA src) else .ok dst
    copytoA copytoBitarray destBit aliased dst src

end JuliaLean.AbstractArraySpecs

/-!
Models of `map!` with several sources, `push!`/`pushfirst!` and `circshift!` from
`base/abstractarray.jl` (master `bbfa0ce4150`, lines 3527-3618, 3649-3682, 3756-3766),
on the array model of `Model.lean`.

Methods of the vector's own type that these bodies call (`resize!`, the one-item `push!`
and `pushfirst!`) are parameters constrained by their documented contracts in
`MutRowsProps.lean`. `reverse!(v, start, stop)` (base/array.jl:2317-2333) is modelled
line by line, and `reverse!(v)` is `reverse!(v, firstindex(v), lastindex(v))`
(base/array.jl:2269-2279).
-/

namespace JuliaLean.AbstractArraySpecs

/-! ## `map!` with two sources -/

/-- `for (i, j, k) in zip(eachindex(dest), eachindex(A), eachindex(B)); a, b = A[j], B[k];
dest[i] = f(a, b); end` (lines 3528-3532). -/
def map2Loop {α : Type} (f : α → α → α) (A B : Arr α) :
    Nat → Arr α → IterState → IterState → IterState → R (Arr α)
  | 0, dest, _, _, _ => .ok dest
  | n + 1, dest, si, sj, sk =>
    match eachindexStep dest si with
    | none => .ok dest
    | some (i, si') =>
      match eachindexStep A sj with
      | none => .ok dest
      | some (j, sj') =>
        match eachindexStep B sk with
        | none => .ok dest
        | some (k, sk') => do
          let a ← getindex A j
          let b ← getindex B k
          let dest' ← setindex dest (f a b) i
          map2Loop f A B n dest' si' sj' sk'

/-- `map!(f, dest, A, B)` (lines 3527-3534). -/
def mapBang2 {α : Type} (f : α → α → α) (dest A B : Arr α) : R (Arr α) :=
  map2Loop f A B (fuelOf dest) dest (eachStart dest) (eachStart A) (eachStart B)

/-! ## `map!` with any number of sources -/

/-- `ith_all(i, as)` (lines 3538-3542): `(as[1][i], ith_all(i, tail(as))...)`. -/
def ithAll {α : Type} (i : I64) : List (Arr α) → R (List α)
  | [] => .ok []
  | a :: as => do
    let x ← getindex a [i]
    let rest ← ithAll i as
    .ok (x :: rest)

/-- `for i in idxs; as = ith_all(i, As); dest[i] = f(as...); end` (lines 3547-3551), with
`idxs = LinearIndices(dest)` iterating the range `linearAxis dest`. -/
def mapNLin {α : Type} (f : List α → α) (D0 : Arr α) (As : List (Arr α)) :
    Nat → Arr α → IterState → R (Arr α)
  | 0, dest, _ => .ok dest
  | n + 1, dest, st =>
    match eachindexStep D0 st with
    | none => .ok dest
    | some (I, st') => do
      let as ← ithAll (I.headD (i64 0)) As
      let dest' ← setindex dest (f as) I
      mapNLin f D0 As n dest' st'

/-- One step of `map(eachindex, As)` zipped: every source yields its next index, or the
zip is exhausted. -/
def stepAll {α : Type} : List (Arr α) → List IterState → Option (List (List I64) × List IterState)
  | [], _ => some ([], [])
  | a :: as, s :: ss =>
    match eachindexStep a s with
    | none => none
    | some (I, s') => (stepAll as ss).map (fun p => (I :: p.1, s' :: p.2))
  | _ :: _, [] => none

/-- `ntuple(j -> getindex(As[j], Is[j]), length(As))` (line 3554). -/
def getAll {α : Type} : List (Arr α) → List (List I64) → R (List α)
  | a :: as, I :: Is => do
    let x ← getindex a I
    let rest ← getAll as Is
    .ok (x :: rest)
  | _, _ => .ok []

/-- `for (i, Is...) in zip(eachindex(dest), map(eachindex, As)...); ...; dest[i] = val; end`
(lines 3553-3557). -/
def mapNZip {α : Type} (f : List α → α) (As : List (Arr α)) :
    Nat → Arr α → IterState → List IterState → R (Arr α)
  | 0, dest, _, _ => .ok dest
  | n + 1, dest, si, ss =>
    match eachindexStep dest si with
    | none => .ok dest
    | some (i, si') =>
      match stepAll As ss with
      | none => .ok dest
      | some (Is, ss') => do
        let as ← getAll As Is
        let dest' ← setindex dest (f as) i
        mapNZip f As n dest' si' ss'

/-- `LinearIndices(x) == LinearIndices(dest)`: two `LinearIndices` arrays are `==` when
their axes (those of `x` and `dest`) are `==`, since equal axes give equal values. -/
def linIdxEq {α : Type} (x dest : Arr α) : Bool := axesEq x.axes dest.axes

/-- `map_n!(f, dest, As)` (lines 3544-3560). -/
def mapN {α : Type} (f : List α → α) (dest : Arr α) (As : List (Arr α)) : R (Arr α) :=
  if As.all (fun x => linIdxEq x dest) then mapNLin f dest As (fuelOf dest) dest .rngStart
  else mapNZip f As (fuelOf dest) dest (eachStart dest) (As.map eachStart)

/-- `map!(f, dest, As...)` (lines 3593-3596). -/
def mapBangN {α : Type} (f : List α → α) (dest : Arr α) (As : List (Arr α)) : R (Arr α) :=
  if As.isEmpty then .error .assertionError else mapN f dest As

/-- `map!(f, inout) = map!(f, inout, inout)` (line 3618), the one-source `map!`. -/
def mapBangInplace {α : Type} (f : α → α) (inout : Arr α) : R (Arr α) := mapBang f inout inout

/-! ## `push!` and `pushfirst!` -/

/-- `push!(a::AbstractVector{T}, item)` (lines 3649-3656); `conv` is
`item isa T ? item : convert(T, item)::T` and `resize` is `resize!` of `a`'s type. -/
def pushOne {α β : Type} (conv : β → R α) (resize : Arr α → I64 → R (Arr α)) (a : Arr α) (item : β) :
    R (Arr α) := do
  let itemT ← conv item
  let newLength := lengthA a + i64 1
  let a ← resize a newLength
  setindex a itemT [(linearAxis a).hi]

/-- `push!(a::AbstractVector{Any}, x)` (lines 3659-3664). -/
def pushOneAny {α : Type} (resize : Arr α → I64 → R (Arr α)) (a : Arr α) (x : α) : R (Arr α) := do
  let newLength := lengthA a + i64 1
  let a ← resize a newLength
  setindex a x [(linearAxis a).hi]

/-- `for i = 1:nx; a[e+i] = x[i]; end` (lines 3671-3673). -/
def pushManyLoop {α : Type} (e : I64) : Nat → Arr α → List α → R (Arr α)
  | _, a, [] => .ok a
  | i, a, x :: xs => do
    let a' ← setindex a x [e + i64 (i : Int)]
    pushManyLoop e (i + 1) a' xs

/-- `push!(a::AbstractVector{Any}, x...)` (lines 3665-3675). -/
def pushManyAny {α : Type} (resize : Arr α → I64 → R (Arr α)) (a : Arr α) (x : List α) : R (Arr α) := do
  let na := lengthA a
  let nx := i64 x.length
  let a ← resize a (na + nx)
  let e := (linearAxis a).hi - nx
  pushManyLoop e 1 a x

/-- `push!(A, a, b) = push!(push!(A, a), b)` (line 3679) for a collection `A` of any type
`C` (an `AbstractVector` dispatches to `push!(a::AbstractVector, iter...)` in
base/array.jl instead); `push` is the one-item `push!` of `C`. -/
def push2 {C α : Type} (push : C → α → R C) (A : C) (a b : α) : R C := do
  let A' ← push A a
  push A' b

/-- `push!(A, a, b, c...) = push!(push!(A, a, b), c...)` (line 3680) for a nonempty `c`,
with the call `push!(X, c...)` dispatching on the number of items. -/
def pushVar {C α : Type} (push : C → α → R C) : C → α → α → α → List α → R C
  | A, a, b, c, [] => do
    let A' ← push2 push A a b
    push A' c
  | A, a, b, c, d :: [] => do
    let A' ← push2 push A a b
    push2 push A' c d
  | A, a, b, c, d :: e :: es => do
    let A' ← push2 push A a b
    pushVar push A' c d e es

/-- `pushfirst!(A, a, b) = pushfirst!(pushfirst!(A, b), a)` (line 3681) for a collection
`A` that is not an `AbstractVector`. -/
def pushfirst2 {C α : Type} (pushfirst : C → α → R C) (A : C) (a b : α) : R C := do
  let A' ← pushfirst A b
  pushfirst A' a

/-- `pushfirst!(A, a, b, c...) = pushfirst!(pushfirst!(A, c...), a, b)` (line 3682) for a
nonempty `c`, with `pushfirst!(X, c...)` dispatching on the number of items. -/
def pushfirstVar {C α : Type} (pushfirst : C → α → R C) : C → α → α → α → List α → R C
  | A, a, b, c, [] => do
    let A' ← pushfirst A c
    pushfirst2 pushfirst A' a b
  | A, a, b, c, d :: [] => do
    let A' ← pushfirst2 pushfirst A c d
    pushfirst2 pushfirst A' a b
  | A, a, b, c, d :: e :: es => do
    let A' ← pushfirstVar pushfirst A c d e es
    pushfirst2 pushfirst A' a b

/-! ## `circshift!` -/


/-- `mod(x, n)` for a positive `Int` `n`: the result in `0:n-1`. -/
def modI (x : Int) (n : I64) : I64 := i64 (x % n.val)

/-- `circshift!(a::AbstractVector, shift::Integer)` (lines 3756-3766); `shift` is the
value of any `Integer` (`mod(shift, n)` is exact and lies in `0:n-1`). -/
def circshiftBang {α : Type} (reverseRange : Arr α → I64 → I64 → R (Arr α))
    (a : Arr α) (shift : Int) : R (Arr α) :=
  let n := lengthA a
  if n == i64 0 then .ok a
  else
    let shift := modI shift n
    if shift == i64 0 then .ok a
    else do
      let l := (linearAxis a).hi
      let a ← reverseRange a (linearAxis a).lo (l - shift)
      let a ← reverseRange a (l - shift + i64 1) (linearAxis a).hi
      reverseRange a (linearAxis a).lo (linearAxis a).hi

end JuliaLean.AbstractArraySpecs


/-! Method-specific models for `base/abstractarray.jl:322-637`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Iteration

open JuliaLean
open JuliaLean.AbstractArrayCov.Rows.Basic

abbrev I64 := JInt .i64
abbrev R (α : Type) := Except String α

def i64 (x : Int) : I64 := JInt.lit .i64 x

def joinCommaAnd : List String → String
  | [] => ""
  | [x] => x
  | [x, y] => x ++ " and " ++ y
  | x :: rest => x ++ ", " ++ joinCommaAnd rest

def listFirst (xs : List α) : Jl α :=
  match xs with | x :: _ => .ok x | [] => .error .boundsError

def listLast (xs : List α) : Jl α :=
  match xs.getLast? with | some x => .ok x | none => .error .boundsError

/-- `eachindex(itrs...) = keys(itrs...)`, line 322. -/
def method322 (keys : List α → β) (itrs : List α) : β := keys itrs
/-- Vector `eachindex`, line 325. -/
def method325 (axes1 : α → β) (a : α) : β := axes1 a
/-- Two-item `_join_comma_and`, line 329. -/
def method329 (a b : String) : String := a ++ " and " ++ b
/-- Vararg `_join_comma_and`, line 330. -/
def method330 (a b : String) (rest : List String) : String :=
  a ++ ", " ++ joinCommaAnd (b :: rest)
/-- `throw_eachindex_mismatch_indices`, lines 331-335. -/
def method331 (indices a : String) (bs : List String) : R Unit :=
  .error ("all inputs to eachindex must have the same " ++ indices ++ ", got " ++
    joinCommaAnd (a :: bs))
/-- Single-array `eachindex`, line 384. -/
def method384 (style : α → σ) (each : σ → α → β) (a : α) : β :=
  each (style a) a
/-- Two-array `eachindex`, lines 386-389. -/
def method386 (style : α → β → σ) (each : σ → α → β → γ) (a : α) (b : β) : γ :=
  each (style a b) a b
/-- Vararg-array `eachindex`, lines 390-393. -/
def method390 (style : α → List α → σ) (each : σ → α → List α → β)
    (a : α) (bs : List α) : β :=
  each (style a bs) a bs
/-- Linear Array/Memory `eachindex`, line 394. -/
def method394 (length : α → Nat) (uncheckedOneTo : Nat → β) (a : α) : β :=
  uncheckedOneTo (length a)
/-- Linear AbstractArray `eachindex`, line 395. -/
def method395 (length : α → Nat) (oneto : Nat → β) (a : α) : β := oneto (length a)
/-- Linear AbstractVector `eachindex`, line 396. -/
def method396 (axes1 : α → β) (a : α) : β := axes1 a
/-- Multi-array linear `eachindex`, lines 397-404. -/
def method397 [Repr β] [BEq β] (each : α → β) (a : α) (bs : List α) : R β :=
  let ia := each a
  let ibs := bs.map each
  if ibs.all (· == ia) then .ok ia
  else .error ("all inputs to eachindex must have the same indices, got " ++
    joinCommaAnd (toString (repr ia) :: ibs.map (toString ∘ repr)))

/-- `keys(style, A, B...)`, line 407. -/
def method407 (eachindex : σ → α → List α → β) (style : σ) (a : α) (bs : List α) : β :=
  eachindex style a bs
/-- `lastindex(a::AbstractArray)`, line 429. -/
def method429 (eachindex : α → List β) (a : α) : Jl β := listLast (eachindex a)
/-- Dimensional `lastindex`, line 430. -/
def method430 (axes : α → β → List γ) (a : α) (d : β) : Jl γ := listLast (axes a d)
/-- `firstindex(a::AbstractArray)`, line 452. -/
def method452 (eachindex : α → List β) (a : α) : Jl β := listFirst (eachindex a)
/-- Dimensional `firstindex`, line 453. -/
def method453 (axes : α → β → List γ) (a : α) (d : β) : Jl γ := listFirst (axes a d)
/-- `first(a::AbstractArray)`, line 455. -/
def method455 (eachindex : α → List β) (getindex : α → β → Jl γ) (a : α) : Jl γ := do
  let i ← listFirst (eachindex a)
  getindex a i
/-- Generic `first(itr)`, lines 474-478. -/
def method474 (iterate : α → Option (β × σ)) (itr : α) : Jl β :=
  match iterate itr with
  | none => .error (.argumentError "collection must be non-empty")
  | some result => .ok result.1
/-- Generic `first(itr,n)`, line 505. -/
def method505 (take : α → Int → β) (collect : β → γ) (itr : α) (n : Int) : γ :=
  collect (take itr n)
/-- Vector `first(v,n)`, lines 507-510. -/
def method507 (checkedLength : α → Jl Int) (range : Int → β)
    (getindex : α → β → Jl γ) (v : α) (n : Int) : Jl γ := do
  if n < 0 then throw (.argumentError "Number of elements must be non-negative")
  let len ← checkedLength v
  getindex v (range (min n len))
/-- `last(a) = a[end]`, line 530. -/
def method530 (lastindex : α → β) (getindex : α → β → γ) (a : α) : γ :=
  getindex a (lastindex a)
/-- Generic `last(itr,n)`, line 555. -/
def method555 (reverse : α → β) (take : β → Int → γ) (collect : γ → δ)
    (reverseBang : δ → ε) (itr : α) (n : Int) : ε :=
  reverseBang (collect (take (reverse itr) n))
/-- Vector `last(v,n)`, lines 557-560. -/
def method557 (checkedLength : α → Jl Int) (lastindex : α → Int)
    (range : Int → Int → β) (getindex : α → β → Jl γ) (v : α) (n : Int) : Jl γ := do
  if n < 0 then throw (.argumentError "Number of elements must be non-negative")
  let len ← checkedLength v
  getindex v (range (lastindex v) (min n len))
def strideTail : List (I64 × I64) → I64 → I64
  | [], acc => acc
  | (st, sz) :: rest, acc => strideTail rest (acc + st * sz)

/-- Generic `stride(A,k)`, lines 597-607. -/
def method597 (strides size : α → List I64) (ndims : α → Nat) (a : α) (k : Int) : Jl I64 := do
  let st := strides a
  if k ≤ ndims a then
    tupleGet st (← JInt.convert (IntTy.i64.name) .i64 k)
  else if ndims a = 0 then .ok (i64 1)
  else do
    let sz := size a
    let firstSt ← tupleGet st (i64 1)
    let firstSz ← tupleGet sz (i64 1)
    .ok (strideTail ((st.drop 1).zip (sz.drop 1)) (firstSt * firstSz))

def sizeToStrides (s : I64) : List I64 → List I64
  | [] => []
  | d :: rest => s :: sizeToStrides (s * d) rest

/-- Variadic recursive `size_to_strides`, line 609. -/
def method609 (s d : I64) (rest : List I64) : List I64 :=
  s :: sizeToStrides (s * d) rest
/-- Two-argument `size_to_strides`, line 610. -/
def method610 (s _d : I64) : List I64 := [s]
/-- One-argument `size_to_strides`, line 611. -/
def method611 (_s : I64) : List I64 := []
/-- `isstored`, lines 613-616. -/
def method613 (checkbounds : α → List Int → Jl Unit) (a : α) (indices : List Int) : Jl Bool := do
  checkbounds a indices
  return true
def intRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map fun (n : Nat) => lo + (n : Int)

/-- Array `trailingsize(A,n)`, lines 619-625. -/
def method619 (ndims : α → Int) (size : α → Int → Jl I64) (a : α) (n : Int) : Jl I64 := do
  let mut s := i64 1
  for i in intRange n (ndims a) do
    s := s * (← size a i)
  return s
/-- Tuple `trailingsize(inds,n)`, lines 626-632. -/
def method626 (length : α → I64) (inds : List α) (n : Int) : Jl I64 := do
  let mut s := i64 1
  for i in intRange n inds.length do
    let axis ← tupleGet inds (← JInt.convert (IntTy.i64.name) .i64 i)
    s := s * length axis
  return s
/-- Type-stable tuple `trailingsize`, lines 634-637. -/
def method634 (length : α → I64) (inds : List α) : I64 :=
  (inds.map length).foldl (· * ·) (i64 1)
end JuliaLean.AbstractArrayCov.Rows.Iteration

/-! Method-specific models for `base/abstractarray.jl:682-896`. -/

namespace JuliaLean.AbstractArrayCov.Rows.BoundsShape

open JuliaLean
open JuliaLean.AbstractArrays
open JuliaLean.AbstractArrayCov.Rows.Basic

abbrev I64 := JInt .i64

def i64 (x : Int) : I64 := JInt.lit .i64 x

/-- `checkbounds(Bool,A,I...)`, lines 682-685. -/
def method682 (axes : α → β) (check : β → γ → Bool) (a : α) (indices : γ) : Bool :=
  check (axes a) indices
/-- Single-index `checkbounds`, lines 690-693. -/
def method690 (eachindex : α → β) (checkindex : β → γ → Bool) (a : α) (index : γ) : Bool :=
  checkindex (eachindex a) index
/-- Recursive nonempty `checkbounds_indices`, lines 722-726. -/
def method722 (default : α) (checkindex : α → β → Bool)
    (recurse : List α → List β → Bool) (inds : List α) (indices : β × List β) : Bool :=
  let firstOk := checkindex (inds.getD 0 default) indices.1
  firstOk && recurse inds.tail indices.2
/-- Empty-index `checkbounds_indices`, line 728. -/
def method728 (length : α → Nat) (inds : List α) : Bool := inds.all fun x => length x = 1
/-- Default `checkindex` error, line 750. -/
def method750 (typeofName : α → String) (index : α) : Jl Bool :=
  .error (.argumentError ("unable to check bounds for indices of type " ++ typeofName index))
/-- Unit-range real `checkindex`, line 751. Both comparisons are evaluated. -/
def method751 (first last : α → β) (le : β → γ → Bool) (le' : γ → β → Bool)
    (inds : α) (index : γ) : Bool :=
  let lower := le (first inds) index
  let upper := le' index (last inds)
  lower && upper
/-- IdentityUnitRange `checkindex`, line 752. -/
def method752 (indices : α → β) (checkindex : β → γ → Bool) (inds : α) (index : γ) : Bool :=
  checkindex (indices inds) index
def unsignedValue (t : IntTy) (x : JInt t) : Int :=
  if t.signed ∧ x.val < 0 then x.val + 2 ^ t.bits else x.val

/-- OneTo same-BitInteger `checkindex`, line 753. -/
def method753 {t : IntTy} (last : α → JInt t) (inds : α) (index : JInt t) : Bool :=
  decide (unsignedValue t (index - JInt.lit t 1) < unsignedValue t (last inds))
/-- Colon `checkindex`, line 754. -/
def method754 : Bool := true
/-- Slice `checkindex`, line 755. -/
def method755 : Bool := true
/-- AbstractRange `checkindex`, lines 756-757. All bitwise operands are evaluated. -/
def method756 (isempty : α → Bool) (first last : α → β)
    (checkindex : γ → β → Bool) (inds : γ) (index : α) : Bool :=
  let empty := isempty index
  let firstOk := checkindex inds (first index)
  let lastOk := checkindex inds (last index)
  empty || (firstOk && lastOk)
/-- LinearIndices `checkindex`, lines 759-760. -/
def method759 (isempty : α → Bool) (first last : α → β)
    (checkindex : γ → β → Bool) (inds : γ) (index : α) : Bool :=
  let empty := isempty index
  let firstOk := checkindex inds (first index)
  let lastOk := checkindex inds (last index)
  empty || (firstOk && lastOk)
/-- Array-of-indices `checkindex`, lines 762-769. -/
def method762 (checkindex : α → β → Jl Bool) (inds : α) (indices : List β) : Jl Bool := do
  let mut b := true
  for i in indices do
    b := b && (← checkindex inds i)
  return b
/-- `similar(a::AbstractArray{T})`, line 819. -/
def method819 (similar : α → τ → β) (a : α) (elementType : τ) : β := similar a elementType
/-- `similar(a, T)`, line 820. -/
def method820 (axes : α → γ) (similar : α → τ → γ → β) (a : α) (t : τ) : β :=
  similar a t (axes a)
/-- Tuple-dims `similar`, line 821. -/
def method821 (similar : α → τ → γ → β) (a : α) (t : τ) (dims : γ) : β :=
  similar a t dims
/-- Vararg-dims `similar(a,dims...)`, line 822. -/
def method822 (similar : α → τ → List γ → β) (a : α) (t : τ) (dims : List γ) : β :=
  similar a t dims
/-- Vararg-dims `similar(a,T,dims...)`, line 823. -/
def method823 (similar : α → τ → List γ → β) (a : α) (t : τ) (dims : List γ) : β :=
  similar a t dims
/-- Mixed Integer/AbstractOneTo dims `similar`, line 829. -/
def method829 (toShape : γ → δ) (similar : α → τ → δ → β)
    (a : α) (t : τ) (dims : γ) : β :=
  similar a t (toShape dims)
/-- Legacy Integer/OneTo dims `similar`, line 832. -/
def method832 (toShape : γ → δ) (similar : α → τ → δ → β)
    (a : α) (t : τ) (dims : γ) : β :=
  similar a t (toShape dims)
/-- Default Array allocation `similar`, line 834. -/
def method834 (array : τ → γ → β) (t : τ) (dims : γ) : β := array t dims
/-- Empty tuple `to_shape`, line 836. -/
def method836 : List α := []
/-- Dims `to_shape`, line 837. -/
def method837 (dims : α) : α := dims
/-- DimsOrInds `to_shape`, line 838. -/
def method838 (toShape : α → β) (dims : List α) : List β := dims.map toShape
/-- Int `to_shape`, line 840. -/
def method840 (i : I64) : I64 := i
/-- Integer `to_shape`, line 841. -/
def method841 (raw : Int) : Jl I64 := JInt.convert (IntTy.i64.name) .i64 raw
/-- AbstractOneTo `to_shape`, line 842. -/
def method842 (last : α → β) (toShapePrivate : β → γ) (range : α) : γ :=
  toShapePrivate (last range)
/-- Integer `_to_shape`, line 843. -/
def method843 (toShape : α → β) (x : α) : β := toShape x
/-- Fallback `_to_shape`, line 844. -/
def method844 (convertInt : α → Jl I64) (x : α) : Jl I64 := convertInt x
/-- AbstractUnitRange `to_shape`, line 845. -/
def method845 (range : α) : α := range
/-- Storage-type vararg `similar`, line 869. -/
def method869 (similar : τ → List α → β) (t : τ) (dims : List α) : β := similar t dims
/-- Storage-type mixed dims `similar`, line 870. -/
def method870 (toShape : α → β) (similar : τ → β → γ) (t : τ) (shape : α) : γ :=
  similar t (toShape shape)
/-- Storage-type legacy mixed dims `similar`, line 872. -/
def method872 (toShape : α → β) (similar : τ → β → γ) (t : τ) (shape : α) : γ :=
  similar t (toShape shape)
/-- Storage-type Dims allocation, line 873. -/
def method873 (construct : τ → α → β) (t : τ) (dims : α) : β := construct t dims
/-- `empty(v,U)`, line 892. -/
def method892 (similar : α → τ → Nat → β) (a : α) (t : τ) : β := similar a t 0
/-- Vector `emptymutable`, line 895. -/
def method895 : List α := []
/-- Generic iterable `emptymutable`, line 896. -/
def method896 : List α := []
end JuliaLean.AbstractArrayCov.Rows.BoundsShape

/-! Method-specific models for `base/abstractarray.jl:920-1272`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Copy

open JuliaLean

abbrev I64 := JInt .i64
def i64 (x : Int) : I64 := JInt.lit .i64 x

def writeSeq (set : δ → I64 → α → Jl δ) : δ → I64 → List α → Jl δ
  | dest, _, [] => .ok dest
  | dest, i, x :: xs => do writeSeq set (← set dest i x) (i + i64 1) xs

def writePairs (set : δ → ι → α → Jl δ) : δ → List (ι × α) → Jl δ
  | dest, [] => .ok dest
  | dest, (i, x) :: rest => do writePairs set (← set dest i x) rest

/-- Vector `copy!`, lines 920-927. -/
def method920 (firstindex : α → Int) (length : α → Nat)
    (resize : α → Nat → Jl α) (copyto : α → α → Jl α) (dst src : α) : Jl α := do
  if firstindex dst != firstindex src then
    throw (.argumentError "vectors must have the same offset for copy! (consider using `copyto!`)")
  let dst ← if length dst != length src then resize dst (length src) else .ok dst
  copyto dst src
/-- General-array `copy!`, lines 929-933. -/
def method929 [BEq β] (axes : α → β) (copyto : α → α → Jl α) (dst src : α) : Jl α := do
  if axes dst != axes src then
    throw (JlError.argumentError "arrays must have the same axes for copy! (consider using `copyto!`)")
  copyto dst src
/-- Iterable-to-array `copyto!`, lines 941-951. -/
def method941 (eachindex : δ → List ι) (set : δ → ι → α → Jl δ)
    (dest : δ) (src : List α) : Jl δ :=
  if src.length ≤ (eachindex dest).length then
    writePairs set dest ((eachindex dest).zip src)
  else .error (.argumentError "destination has fewer elements than required")
/-- Iterable `copyto!(dest,dstart,src)`, lines 953-971. -/
def method953 (hasLength : Bool) (destLength : Nat) (lastindex : I64)
    (checkbounds : I64 → Jl Unit) (set : δ → I64 → α → Jl δ)
    (dest : δ) (dstart : Int) (src : List α) : Jl δ := do
  let i ← JInt.convert (IntTy.i64.name) .i64 dstart
  if hasLength && destLength > 0 then
    if src.isEmpty then return dest
    checkbounds i
    if ¬((src.length : Int) ≤ lastindex.val - i.val + 1) then throw .boundsError
    writeSeq set dest i src
  else writeSeq set dest i src
/-- Iterable `copyto!(dest,dstart,src,sstart)`, lines 974-1000. -/
def method974 (set : δ → I64 → α → Jl δ) (dest : δ)
    (dstart sstart : Int) (src : List α) : Jl δ := do
  if sstart < 1 then throw (.argumentError "source start offset is < 1")
  if src.length < sstart.toNat then throw (.argumentError "source has fewer elements than required")
  let i ← JInt.convert (IntTy.i64.name) .i64 dstart
  writeSeq set dest i (src.drop (sstart - 1).toNat)
/-- Counted iterable `copyto!`, lines 1003-1037. -/
def method1003 (destContains : Int → Bool) (destLast : Int)
    (set : δ → I64 → α → Jl δ) (dest : δ) (dstart : Int)
    (src : List α) (sstart n : Int) : Jl δ := do
  if n < 0 then throw (.argumentError "elements to copy should be non-negative")
  if n = 0 then return dest
  if sstart < 1 then throw (.argumentError "source start offset is < 1")
  if !(destContains dstart && n ≤ destLast - dstart + 1) then throw .boundsError
  let d ← JInt.convert (IntTy.i64.name) .i64 dstart
  let n64 ← JInt.convert (IntTy.i64.name) .i64 n
  if src.length < sstart.toNat then throw (.argumentError "source has fewer elements than required")
  let values := (src.drop (sstart - 1).toNat).take n64.val.toNat
  let dest ← writeSeq set dest d values
  if values.length < n64.val.toNat then throw .boundsError
  return dest
/-- AbstractArray-to-array `copyto!`, lines 1072-1080. -/
def method1072 (isempty isBitArray : Bool) (bitcopy : δ → σ → Jl δ)
    (unalias : δ → σ → σ) (styleDest : δ → ι) (styleSrc : σ → κ)
    (copyUnaliased : ι → δ → κ → σ → Jl δ) (dest : δ) (src : σ) : Jl δ := do
  if isempty then return dest
  if isBitArray then return ← bitcopy dest src
  let src' := unalias dest src
  copyUnaliased (styleDest dest) dest (styleSrc src') src'
/-- Styled AbstractArray `copyto!`, lines 1082-1086. -/
def method1082 (isempty : Bool) (unalias : δ → σ → σ)
    (copyU : ι → δ → κ → σ → Jl δ) (ds : ι) (dest : δ) (ss : κ) (src : σ) : Jl δ := do
  if isempty then return dest
  let src' := unalias dest src
  copyU ds dest ss src'
/-- `copyto_unaliased!`, lines 1088-1123, with explicit source and destination iterators. -/
def method1088 (srcEmpty destLinear srcLinear sameIterator : Bool)
    (boundsFirst boundsLast : Bool) (linearPairs dualPairs sharedPairs cartPairs : List (ι × α))
    (set : δ → ι → α → Jl δ) (dest : δ) : Jl δ := do
  if srcEmpty then return dest
  let firstOk := boundsFirst
  let lastOk := boundsLast
  if !(firstOk && lastOk) then throw .boundsError
  if destLinear then
    if srcLinear then writePairs set dest linearPairs else writePairs set dest dualPairs
  else if sameIterator then writePairs set dest sharedPairs else writePairs set dest cartPairs
/-- Three-argument AbstractArray `copyto!`, lines 1125-1127. -/
def method1125 (linear : σ → List Int) (length : σ → Int)
    (copy : δ → Int → σ → Int → Int → Jl δ) (dest : δ) (dstart : Int) (src : σ) : Jl δ :=
  match linear src with
  | [] => copy dest dstart src 1 (length src)
  | first :: _ => copy dest dstart src first (length src)
/-- Four-argument AbstractArray `copyto!`, lines 1129-1133. -/
def method1129 (linear : σ → List Int) (check : List Int → Int → Bool)
    (copy : δ → Int → σ → Int → Int → Jl δ) (dest : δ) (dstart : Int)
    (src : σ) (sstart : Int) : Jl δ := do
  let inds := linear src
  if !check inds sstart then throw .boundsError
  let last := inds.getLast?.getD 0
  copy dest dstart src sstart (last - sstart + 1)
/-- Counted AbstractArray block `copyto!`, lines 1135-1152. -/
def method1135 (destBounds srcBounds : Int → Int → Bool) (destLast srcLast : Int)
    (unalias : δ → σ → σ) (read : σ → Int → Jl α) (set : δ → I64 → α → Jl δ)
    (dest : δ) (dstart : Int) (src : σ) (sstart n : Int) : Jl δ := do
  if n = 0 then return dest
  if n < 0 then throw (.argumentError "elements to copy should be non-negative")
  if !(destBounds dstart n && n ≤ destLast - dstart + 1) then throw .boundsError
  if !(srcBounds sstart n && n ≤ srcLast - sstart + 1) then throw .boundsError
  let d ← JInt.convert (IntTy.i64.name) .i64 dstart
  let src' := unalias dest src
  let values ← (List.range n.toNat).mapM fun (k : Nat) => read src' (sstart + (k : Int))
  writeSeq set dest d values
/-- `copy(a::AbstractArray)`, lines 1154-1157. -/
def method1154 (copymutable : α → β) (a : α) : β := copymutable a
/-- Matrix-region `copyto!`, lines 1159-1182. -/
def method1159 (checkDest checkSrc : Jl Unit) (unalias : δ → σ → σ)
    (read : σ → Int → Int → Jl α) (set : δ → Int → Int → α → Jl δ)
    (dest : δ) (destRows destCols : List Int) (src : σ) (srcRows srcCols : List Int) : Jl δ := do
  if destRows.length != srcRows.length then throw (.argumentError "row sizes differ")
  if destCols.length != srcCols.length then throw (.argumentError "column sizes differ")
  checkDest
  checkSrc
  let src' := unalias dest src
  let mut out := dest
  for (dc, sc) in destCols.zip srcCols do
    for (dr, sr) in destRows.zip srcRows do
      out ← set out dr dc (← read src' sr sc)
  return out
/-- `_checkaxs`, line 1184. -/
def method1184 [BEq α] (destAxes srcAxes : α) : Except String Unit :=
  if destAxes == srcAxes then .ok () else .error "axes must agree"
/-- `copyto_axcheck!`, lines 1186-1189. -/
def method1186 (axes : α → β) (check : β → β → Except String Unit)
    (copyto : α → α → Except String α) (dest src : α) : Except String α := do
  check (axes dest) (axes src)
  copyto dest src
/-- Array `copymutable`, lines 1211-1214. -/
def method1211 (similar : α → β) (copyto : β → α → γ) (a : α) : γ :=
  copyto (similar a) a
/-- Generic `copymutable`, line 1215. -/
def method1215 (collect : α → β) (itr : α) : β := collect itr
/-- Array-specialized `copymutable`, line 1216. -/
def method1216 (copy : α → β) (a : α) : β := copy a
/-- Numeric-array `zero`, line 1218. -/
def method1218 (zero : τ → α) (typeof : α → σ) (similar : δ → σ → β)
    (fill : β → α → γ) (t : τ) (x : δ) : γ :=
  let z := zero t
  fill (similar x (typeof z)) z
/-- Missing-or-number array `zero`, line 1219. -/
def method1219 (zero : τ → α) (typeof : α → σ) (similar : δ → σ → β)
    (fill : β → α → γ) (t : τ) (x : δ) : γ :=
  let z := zero t
  fill (similar x (typeof z)) z
/-- Generic array `zero`, line 1220. -/
def method1220 (zero : α → β) (map : (α → β) → γ → δ) (x : γ) : δ := map zero x
/-- `_one`, lines 1222-1234. -/
def method1222 (rows cols : List ι) (zero : α → α) (require : Jl Unit)
    (similar : α → Jl δ) (fill : δ → α → Jl δ) (set : δ → ι → ι → α → Jl δ)
    (unit : α) : Jl δ := do
  if rows.length != cols.length then throw (.argumentError "identity requires square matrix")
  let z := zero unit
  require
  let out ← fill (← similar unit) z
  let mut out := out
  for i in rows do out ← set out i i unit
  return out
/-- Matrix `one`, line 1236. -/
def method1236 (one : τ → α) (makeOne : α → δ → β) (t : τ) (x : δ) : β :=
  makeOne (one t) x
/-- Matrix `oneunit`, line 1237. -/
def method1237 (oneunit : τ → α) (makeOne : α → δ → β) (t : τ) (x : δ) : β :=
  makeOne (oneunit t) x
/-- `iterate_starting_state(A)`, line 1245. -/
def method1245 (style : α → σ) (start : α → σ → β) (a : α) : β := start a (style a)
/-- Linear iteration starting state, line 1246. -/
def method1246 (firstindex : α → β) (a : α) : β := firstindex a
/-- Cartesian iteration starting state, line 1247. -/
def method1247 (eachindex : α → β) (a : α) : β × Unit := (eachindex a, ())
/-- Array `iterate`, line 1250. -/
def method1250 (iterateArray : α → σ → β) (a : α) (state : σ) : β := iterateArray a state
/-- Tuple-state array iteration, lines 1251-1255. -/
def method1251 (iterate : σ → List ρ → Option (ι × List ρ)) (get : α → ι → β)
    (a : α) (state : σ × List ρ) : Option (β × (σ × List ρ)) :=
  match iterate state.1 state.2 with
  | none => none
  | some (i, next) => some (get a i, (state.1, next))
/-- Integer-state array iteration, lines 1256-1259. -/
def method1256 (check : α → I64 → Bool) (get : α → I64 → β)
    (a : α) (state : I64) : Option (β × I64) :=
  if check a state then some (get a state, state + i64 1) else none
/-- `isempty(::AbstractArray)`, line 1262. -/
def method1262 (length : α → Nat) (a : α) : Bool := length a = 0
structure StepRangeModel (α : Type) where
  start : α
  step : α
  stop : α

structure UnitRangeModel (α : Type) where
  start : α
  stop : α

structure LinRangeModel (α : Type) where
  start : α
  stop : α
  len : Nat

/-- Type-map of StepRange, line 1267. -/
def method1267 (convert : α → β) (r : StepRangeModel α) : StepRangeModel β :=
  ⟨convert r.start, convert r.step, convert r.stop⟩
/-- Type-map of UnitRange, line 1268. -/
def method1268 (convert : α → β) (r : UnitRangeModel α) : UnitRangeModel β :=
  ⟨convert r.start, convert r.stop⟩
/-- Type-map of StepRangeLen, line 1269. -/
def method1269 (convert : α → β) (r : α) : β := convert r
/-- Type-map of LinRange, lines 1270-1272. -/
def method1270 (convert : α → β) (r : LinRangeModel α) : LinRangeModel β :=
  ⟨convert r.start, convert r.stop, r.len⟩
end JuliaLean.AbstractArrayCov.Rows.Copy

/-! Method-specific models for `base/abstractarray.jl:1279-1504`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Index

open JuliaLean

abbrev I64 := JInt .i64
def i64 (x : Int) : I64 := JInt.lit .i64 x

structure CanonicalIndexErrorModel where
  func : String
  typeName : String
  deriving Repr, DecidableEq

/-- One-argument `pointer`, line 1279. -/
def method1279 (cconvert : α → β) (unsafeConvert : β → γ) (x : α) : γ :=
  unsafeConvert (cconvert x)
/-- Indexed `pointer`, lines 1280-1283. -/
def method1280 (pointer : α → I64) (offset : α → Int → Int) (x : α) (i : Int) : Jl I64 := do
  let off ← JInt.convert (IntTy.i64.name) .i64 (offset x i)
  return pointer x + off
/-- Dense-array `_memory_offset`, line 1286. -/
def method1286 (linear : α → List β → I64) (firstLinear : α → I64)
    (elsize : α → I64) (x : α) (indices : List β) : I64 :=
  (linear x indices - firstLinear x) * elsize x
def offsetTerms : List I64 → List I64 → List I64 → List I64
  | i :: is, s :: ss, o :: os => s * (i - o) :: offsetTerms is ss os
  | _, _, _ => []

/-- Generic-array `_memory_offset`, lines 1287-1290. -/
def method1287 (subscripts : α → List β → List I64) (strides origins : α → List I64)
    (elsize : α → I64) (x : α) (indices : List β) : I64 :=
  let js := subscripts x indices
  ((offsetTerms js (strides x) (origins x)).foldl (· + ·) (i64 0)) * elsize x
/-- Generic `getindex`, lines 1363-1367. -/
def method1363 (style : α → σ) (canonical : σ → α → List ι → Jl Unit)
    (toIndices : α → List ι → Jl (List κ)) (get : σ → α → List κ → Jl β)
    (a : α) (indices : List ι) : Jl β := do
  canonical (style a) a indices
  let js ← toIndices a indices
  get (style a) a js
/-- Integer-only Array `getindex`, line 1369. -/
def method1369 (toIndices : α → List ι → Jl (List κ))
    (get : α → List κ → Jl β) (a : α) (indices : List ι) : Jl β := do
  get a (← toIndices a indices)
/-- `unsafe_getindex`, line 1371. -/
def method1371 (getindex : α → List ι → β) (a : α) (indices : List ι) : β :=
  getindex a indices
/-- Inner `CanonicalIndexError` constructor, line 1376. -/
def method1376 (func typeName : String) : CanonicalIndexErrorModel := ⟨func, typeName⟩
/-- Linear canonical-get guard, lines 1379-1380. -/
def method1379 (typeName : String) : Except CanonicalIndexErrorModel Unit :=
  .error ⟨"getindex", typeName⟩
/-- Cartesian canonical-get guard, lines 1381-1382. -/
def method1381 (typeName : String) : Except CanonicalIndexErrorModel Unit :=
  .error ⟨"getindex", typeName⟩
/-- Noncanonical get guard, line 1383. -/
def method1383 : Unit := ()
/-- Unsupported `_getindex` fallback, lines 1386-1387. -/
def method1386 (arrayType indexTypes : String) : Except String β :=
  .error ("getindex for " ++ arrayType ++ " with types " ++ indexTypes ++ " is not supported")
/-- Linear vector scalar `_getindex`, line 1390. -/
def method1390 (getindex : α → Int → β) (a : α) (i : Int) : β := getindex a i
/-- Linear array scalar `_getindex`, line 1391. -/
def method1391 (getindex : α → Int → β) (a : α) (i : Int) : β := getindex a i
/-- Linear multi-index `_getindex`, lines 1392-1397. -/
def method1392 (checkbounds : α → List Int → Jl Unit)
    (linear : α → List Int → Int) (getindex : α → Int → Jl β)
    (a : α) (indices : List Int) : Jl β := do
  checkbounds a indices
  getindex a (linear a indices)
/-- Single-index `_to_linear_index`, line 1398. -/
def method1398 (i : Int) : Int := i
/-- Vector multi-index `_to_linear_index`, line 1399. -/
def method1399 (i : Int) (_rest : List Int) : Int := i
/-- Zero-index `_to_linear_index`, line 1400. -/
def method1400 (linearIndices : α → List Int) (a : α) : Jl Int :=
  match linearIndices a with | i :: _ => .ok i | [] => .error .boundsError
/-- Multi-index `_to_linear_index`, line 1401. -/
def method1401 (sub2ind : α → List Int → Int) (a : α) (indices : List Int) : Int :=
  sub2ind a indices
/-- Cartesian multi-index `_getindex`, lines 1404-1409. -/
def method1404 (checkbounds : α → List Int → Jl Unit)
    (subscripts : α → List Int → List Int) (getindex : α → List Int → Jl β)
    (a : α) (indices : List Int) : Jl β := do
  checkbounds a indices
  getindex a (subscripts a indices)
/-- Canonical Cartesian `_getindex`, lines 1410-1413. -/
def method1410 (getindex : α → List Int → β) (a : α) (indices : List Int) : β :=
  getindex a indices
/-- One-index `_to_subscript_indices`, line 1414. -/
def method1414 (ind2sub : α → Int → β) (a : α) (i : Int) : β := ind2sub a i
/-- Zero-index general-rank `_to_subscript_indices`, line 1415. -/
def method1415 (rank : Nat) : List Int := List.replicate rank 1
/-- Zero-rank zero-index `_to_subscript_indices`, line 1416. -/
def method1416 : List Int := []
/-- Zero-rank one-index `_to_subscript_indices`, line 1417. -/
def method1417 (_i : Int) : List Int := []
/-- Zero-rank vararg `_to_subscript_indices`, line 1418. -/
def method1418 (_indices : List Int) : List Int := []
/-- General integer `_to_subscript_indices`, lines 1419-1423. -/
def method1419 (split : List Int → Nat → List Int × List Int)
    (finish : α → List Int → List Int → β) (a : α) (rank : Nat) (indices : List Int) : β :=
  let parts := split indices rank
  finish a parts.1 parts.2
/-- Empty-remainder `_to_subscript_indices`, lines 1424-1425. -/
def method1424 (axes : α → β) (finish : α → β → γ → δ) (a : α) (j : γ) : δ :=
  finish a (axes a) j
/-- `__to_subscript_indices`, lines 1426-1430. -/
def method1426 (remaining : List Int → List α → List α)
    (first : α → Int) (axes : α → List α) (a : α) (j : List Int) : List Int :=
  j ++ ((remaining j (axes a)).drop 1).map first
/-- Nonempty-remainder `_to_subscript_indices`, line 1431. -/
def method1431 (j : α) (_remainder : β) : α := j
/-- Canonical-rank `_to_subscript_indices`, line 1432. -/
def method1432 (indices : α) : α := indices
/-- Singleton-head `_remaining_size`, line 1433. -/
def method1433 (_head : α) (tail : β) : β := tail
/-- Recursive `_remaining_size`, line 1434. -/
def method1434 (remaining : List α → List β → γ) (heads : List α) (tails : List β) : γ :=
  remaining heads.tail tails.tail
/-- Empty-shape `_unsafe_ind2sub`, line 1435. -/
def method1435 (_i : Int) : List Int := []
/-- Nonempty `_unsafe_ind2sub`, line 1436. -/
def method1436 (ind2sub : α → Int → β) (shape : α) (i : Int) : β := ind2sub shape i
/-- Generic `setindex!`, lines 1464-1468. -/
def method1464 (style : α → σ) (canonical : σ → α → List ι → Jl Unit)
    (toIndices : α → List ι → Jl (List κ)) (set : σ → α → β → List κ → Jl α)
    (a : α) (value : β) (indices : List ι) : Jl α := do
  canonical (style a) a indices
  let js ← toIndices a indices
  set (style a) a value js
/-- `unsafe_setindex!`, lines 1469-1473. -/
def method1469 (setindex : α → β → List ι → γ) (a : α) (value : β) (indices : List ι) : γ :=
  setindex a value indices
/-- Linear canonical-set guard, lines 1475-1476. -/
def method1475 (typeName : String) : Except CanonicalIndexErrorModel Unit :=
  .error ⟨"setindex!", typeName⟩
/-- Cartesian canonical-set guard, lines 1477-1478. -/
def method1477 (typeName : String) : Except CanonicalIndexErrorModel Unit :=
  .error ⟨"setindex!", typeName⟩
/-- Noncanonical set guard, line 1479. -/
def method1479 : Unit := ()
/-- Unsupported `_setindex!` fallback, lines 1482-1483. -/
def method1482 (arrayType indexTypes : String) : Except String β :=
  .error ("setindex! for " ++ arrayType ++ " with types " ++ indexTypes ++ " is not supported")
/-- Linear scalar `_setindex!`, line 1486. -/
def method1486 (setindex : α → β → Int → γ) (a : α) (value : β) (i : Int) : γ :=
  setindex a value i
/-- Linear multi-index `_setindex!`, lines 1487-1492. -/
def method1487 (checkbounds : α → List Int → Jl Unit) (linear : α → List Int → Int)
    (setindex : α → β → Int → Jl α) (a : α) (value : β) (indices : List Int) : Jl α := do
  checkbounds a indices
  setindex a value (linear a indices)
/-- Canonical Cartesian `_setindex!`, lines 1495-1498. -/
def method1495 (setindex : α → β → List Int → γ) (a : α) (value : β) (indices : List Int) : γ :=
  setindex a value indices
/-- Cartesian multi-index `_setindex!`, lines 1499-1504. -/
def method1499 (checkbounds : α → List Int → Jl Unit)
    (subscripts : α → List Int → List Int) (setindex : α → β → List Int → Jl α)
    (a : α) (value : β) (indices : List Int) : Jl α := do
  checkbounds a indices
  setindex a value (subscripts a indices)
end JuliaLean.AbstractArrayCov.Rows.Index

/-! Method-specific models for `base/abstractarray.jl:1548-1694`. -/

namespace JuliaLean.AbstractArrayCov.Rows.AliasGet

open JuliaLean

/-- `parent(a::AbstractArray)`, line 1548. -/
def method1548 (a : α) : α := a
/-- Array `unalias`, line 1566. -/
def method1566 (mightalias : δ → α → Bool) (copy : α → α) (dest : δ) (a : α) : α :=
  if mightalias dest a then copy a else a
/-- Range `unalias`, line 1567. -/
def method1567 (_dest : δ) (a : α) : α := a
/-- Generic `unalias`, line 1568. -/
def method1568 (_dest : δ) (a : α) : α := a
/-- Array `unaliascopy`, line 1582. -/
def method1582 (copy : α → β) (a : α) : β := copy a
/-- AbstractArray `unaliascopy`, line 1583. -/
def method1583 (copy : α → β) (finish : α → β → Jl α) (a : α) : Jl α :=
  finish a (copy a)
/-- Same-type `_unaliascopy`, line 1584. -/
def method1584 (_a : α) (copy : α) : α := copy
/-- Wrong-type `_unaliascopy`, lines 1585-1592. -/
def method1585 (arrayType copyType : String) : Jl α :=
  .error (.argumentError ("copy(::" ++ arrayType ++ ") returns " ++ copyType))
/-- Generic `unaliascopy`, line 1593. -/
def method1593 (a : α) : α := a
/-- Array `mightalias`, line 1603, preserving short-circuit order. -/
def method1603 (isbits : α → Bool) (isempty : α → Bool) (dataids : α → List Nat)
    (disjoint : List Nat → List Nat → Bool) (a b : α) : Bool :=
  !isbits a && !isbits b && !isempty a && !isempty b && !disjoint (dataids a) (dataids b)
/-- Generic `mightalias`, line 1604. -/
def method1604 : Bool := false
/-- Empty/empty `_isdisjoint`, line 1606. -/
def method1606 : Bool := true
/-- Empty/singleton `_isdisjoint`, line 1607. -/
def method1607 (_b : Nat) : Bool := true
/-- Empty/tuple `_isdisjoint`, line 1608. -/
def method1608 (_bs : List Nat) : Bool := true
/-- Singleton/empty `_isdisjoint`, line 1609. -/
def method1609 (_a : Nat) : Bool := true
/-- Singleton/singleton `_isdisjoint`, line 1610. -/
def method1610 (a b : Nat) : Bool := a != b
/-- Singleton/tuple `_isdisjoint`, line 1611. -/
def method1611 (a : Nat) (bs : List Nat) : Bool := !bs.contains a
/-- Tuple/empty `_isdisjoint`, line 1612. -/
def method1612 (_as : List Nat) : Bool := true
/-- Tuple/singleton `_isdisjoint`, line 1613. -/
def method1613 (as : List Nat) (b : Nat) : Bool := !as.contains b
/-- Tuple/tuple recursive `_isdisjoint`, line 1614. -/
def method1614 (recurse : List Nat → List Nat → Bool) (as bs : List Nat) : Bool :=
  match as with
  | [] => true
  | a :: rest => !bs.contains a && recurse rest bs
/-- AbstractArray `dataids`, line 1626. -/
def method1626 (objectid : α → Nat) (a : α) : List Nat := [objectid a]
/-- Memory `dataids`, line 1627. -/
def method1627 (pointer : α → Nat) (a : α) : List Nat := [pointer a]
/-- Array `dataids`, line 1628. -/
def method1628 (memory : α → β) (dataids : β → List Nat) (a : α) : List Nat :=
  dataids (memory a)
/-- Range `dataids`, line 1629. -/
def method1629 : List Nat := []
/-- Generic `dataids`, line 1630. -/
def method1630 : List Nat := []
def getDefault (check : Bool) (get : Unit → α) (default : Unit → α) : α :=
  if check then get () else default ()

/-- Scalar defaulted `get`, line 1637. -/
def method1637 (check : α → Int → Bool) (get : α → Int → β)
    (a : α) (i : Int) (default : β) : β :=
  if check a i then get a i else default
/-- Zero-index defaulted `get`, line 1638. -/
def method1638 (check : α → Bool) (get : α → β) (a : α) (default : β) : β :=
  if check a then get a else default
/-- Dim-tuple defaulted `get`, line 1639. -/
def method1639 (check : α → List Int → Bool) (get : α → List Int → β)
    (a : α) (indices : List Int) (default : β) : β :=
  if check a indices then get a indices else default
/-- Callable scalar default `get`, line 1640. -/
def method1640 (check : α → Int → Bool) (get : α → Int → β)
    (fallback : Unit → β) (a : α) (i : Int) : β :=
  if check a i then get a i else fallback ()
/-- Callable zero-index default `get`, line 1641. -/
def method1641 (check : α → Bool) (get : α → β) (fallback : Unit → β) (a : α) : β :=
  if check a then get a else fallback ()
/-- Callable dim-tuple default `get`, line 1642. -/
def method1642 (check : α → List Int → Bool) (get : α → List Int → β)
    (fallback : Unit → β) (a : α) (indices : List Int) : β :=
  if check a indices then get a indices else fallback ()
/-- Vector-index `get!`, lines 1644-1652. -/
def method1644 (findValid : β → List Int) (copySelected : δ → List Int → Jl δ)
    (fillRange : δ → Int → Int → α → Jl δ) (x : δ) (requested : β) (default : α)
    (firstX lastX : Int) : Jl δ := do
  let validPositions := findValid requested
  let x ← copySelected x validPositions
  let firstValid := validPositions.head?.getD (lastX + 1)
  let lastValid := validPositions.getLast?.getD (firstX - 1)
  let x ← fillRange x firstX (firstValid - 1) default
  fillRange x (lastValid + 1) lastX default
/-- Linear array `get!`, lines 1653-1660. -/
def method1653 (findValid : β → List Int) (copySelected : δ → List Int → Jl δ)
    (fillView : δ → Int → Int → α → Jl δ) (x : δ) (requested : β)
    (default : α) (lengthX : Int) : Jl δ := do
  let validPositions := findValid requested
  let x ← copySelected x validPositions
  let firstValid := validPositions.head?.getD (lengthX + 1)
  let lastValid := validPositions.getLast?.getD 0
  let x ← fillView x 1 (firstValid - 1) default
  fillView x (lastValid + 1) lengthX default
/-- Range defaulted `get`, line 1662. -/
def method1662 (typeof : α → τ) (shape : ι → σ) (similar : δ → τ → σ → β)
    (getBang : β → δ → ι → α → γ) (a : δ) (indices : ι) (default : α) : γ :=
  getBang (similar a (typeof default) (shape indices)) a indices default
/-- Multi-index-list `get!`, lines 1664-1669. -/
def method1664 (fill : δ → α → Jl δ) (indcopy : σ → ι → κ × κ)
    (size : β → σ) (copy : δ → β → κ → κ → Jl δ)
    (x : δ) (a : β) (indices : ι) (default : α) : Jl δ := do
  let x ← fill x default
  let pair := indcopy (size a) indices
  copy x a pair.1 pair.2
/-- Multi-index-list defaulted `get`, lines 1671-1672. -/
def method1671 (typeof : α → τ) (shape : ι → σ) (similar : δ → τ → σ → β)
    (getBang : β → δ → ι → α → γ) (a : δ) (indices : ι) (default : α) : γ :=
  getBang (similar a (typeof default) (shape indices)) a indices default
/-- Matrix printing replacement, line 1675. -/
def method1675 (_a : α) (_i _j : Int) (text : String) : String := text
/-- Vector printing replacement, line 1676. -/
def method1676 (_a : α) (_i _j : Int) (text : String) : String := text
/-- Generic `eltypeof`, line 1679. -/
def method1679 (typeof : α → β) (x : α) : β := typeof x
/-- Array `eltypeof`, line 1680. -/
def method1680 (eltype : α → β) (x : α) : β := eltype x
/-- Zero-argument `promote_eltypeof`, line 1682. -/
def method1682 : Except String α := .error "promotion requires an argument"
/-- Unary `promote_eltypeof`, line 1683. -/
def method1683 (eltypeof : α → τ) (v : α) : τ := eltypeof v
/-- Binary `promote_eltypeof`, line 1684. -/
def method1684 (eltypeof : α → τ) (promote : τ → τ → τ) (a b : α) : τ :=
  promote (eltypeof a) (eltypeof b)
/-- Vararg `promote_eltypeof`, line 1685. -/
def method1685 (eltypeof : α → τ) (promote : τ → τ → τ) (a b : α) (rest : List α) : τ :=
  rest.foldl (fun t x => promote t (eltypeof x)) (promote (eltypeof a) (eltypeof b))
/-- Same-type `promote_eltypeof`, line 1686. -/
def method1686 (eltypeof : α → τ) (first : α) (_rest : List α) : τ := eltypeof first
/-- Same-element-array `promote_eltypeof`, line 1687. -/
def method1687 (elementType : τ) (_arrays : List α) : τ := elementType
/-- Zero-argument `promote_eltype`, line 1689. -/
def method1689 : Except String α := .error "promotion requires an argument"
/-- Unary `promote_eltype`, line 1690. -/
def method1690 (eltype : α → τ) (v : α) : τ := eltype v
/-- Binary `promote_eltype`, line 1691. -/
def method1691 (eltype : α → τ) (promote : τ → τ → τ) (a b : α) : τ :=
  promote (eltype a) (eltype b)
/-- Vararg `promote_eltype`, line 1692. -/
def method1692 (eltype : α → τ) (promote : τ → τ → τ) (a b : α) (rest : List α) : τ :=
  rest.foldl (fun t x => promote t (eltype x)) (promote (eltype a) (eltype b))
/-- Same-type `promote_eltype`, line 1693. -/
def method1693 (eltypeType : τ → σ) (typeTag : τ) (_values : List α) : σ := eltypeType typeTag
/-- Same-element-array `promote_eltype`, line 1694. -/
def method1694 (elementType : τ) (_arrays : List α) : τ := elementType
end JuliaLean.AbstractArrayCov.Rows.AliasGet

/-! Thin, method-specific concatenation adapters in `base/abstractarray.jl:1697-2292`. -/

namespace JuliaLean.AbstractArrayCov.Rows.ConcatDirect

open JuliaLean

structure MatrixResult (α : Type) where
  rows : Nat
  cols : Nat
  values : List α
  deriving Repr, DecidableEq

def emptyVector : List α := []

def method1697 (_dim : Int) : List α := []
def method1699 (elementType : Type) : List elementType := []
def method1700 (elementType : Type) : List elementType := []
/-- Same-type scalar `vcat` comprehensions, lines 1703-1704. -/
def method1703 (values : List α) : List α := values
def method1704 (values : List α) : List α := values
/-- Same-type scalar `hcat` comprehensions, lines 1705-1706. -/
def method1705 (values : List α) : MatrixResult α := ⟨1, values.length, values⟩
def method1706 (values : List α) : MatrixResult α := ⟨1, values.length, values⟩
def allocateFill (allocate : Nat → β) (fill : β → Bool → List α → γ)
    (values : List α) : γ := fill (allocate values.length) false values

def method1708 (promote : List α → τ) (allocate : τ → Nat → β)
    (fill : β → Bool → List α → γ) (values : List α) : γ :=
  fill (allocate (promote values) values.length) false values
def method1714 (promote : List α → τ) (allocate : τ → Nat → Nat → β)
    (fill : β → Bool → List α → γ) (values : List α) : γ :=
  fill (allocate (promote values) 1 values.length) false values
def method1720 (allocate : τ → Nat → β) (fill : β → Bool → List α → γ)
    (t : τ) (values : List α) : γ :=
  fill (allocate t values.length) false values
def method1726 (allocate : τ → Nat → Nat → β) (fill : β → Bool → List α → γ)
    (t : τ) (values : List α) : γ :=
  fill (allocate t 1 values.length) false values
def promotedCall (promote : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (promote xs) xs

def typedCall (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs

def method1732 (promote : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (promote xs) xs
def method1733 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def method1740 (similar : α → τ → Nat → β) (vectors : List α) (t : τ) (n : Nat) : Option β :=
  vectors.head?.map fun first => similar first t n
def method1741 (length : α → Nat) (allocate : List α → τ → Nat → β)
    (fill : β → List α → γ) (t : τ) (vectors : List α) : γ :=
  fill (allocate vectors t ((vectors.map length).foldl (· + ·) 0)) vectors
def method1755 (call : τ → List α → β) (t : τ) (arrays : List α) : β := call t arrays
def method1759 : Jl α := .error (.argumentError "ambiguous indexing or typed concatenation")
def method1765 (promote : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (promote xs) xs
def method1766 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def method1802 (promote : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (promote xs) xs
def method1803 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def method1825 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def method1827 (mapreduce : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (mapreduce xs) xs
def method1830 (mapreduce : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (mapreduce xs) xs
def method1836 : List Nat := [1]
def method1837 (size : α → List Nat) (a : α) : List Nat := size a
def method1838 (_a : α) (_d : Int) : Nat := 1
def method1839 (size : α → Int → Nat) (a : α) (d : Int) : Nat := size a d
def method1841 (_a : α) : Nat := 1
def method1842 (length : α → Nat) (a : α) : Nat := length a
def method1844 (_a : α) : Nat := 0
def method1845 (ndims : α → Nat) (a : α) : Nat := ndims a
def method1847 (_a : α) (_d : Int) : List Nat := [1]
def method1848 (axes : α → Int → β) (a : α) (d : Int) : β := axes a d
def method1850 (allocate : τ → List Nat → β) (t : τ) (shape : List Nat) : β := allocate t shape
def method1851 (allocate : τ → List Nat → β) (t : τ) (shape : List Nat) : β := allocate t shape
def method1852 (allocate : τ → List Nat → β) (t : τ) (shape : List Nat) : β := allocate t shape
def method1853 (allocate : τ → List Nat → β) (t : τ) (shape : List Nat) : β := allocate t shape
def method1854 (similar : α → τ → List Nat → β) (a : α) (t : τ) (shape : List Nat) : β :=
  similar a t shape
def method1855 (similar : α → τ → List Nat → β) (a : α) (t : τ) (shape : List Nat) : β :=
  similar a t shape
def method1858 (_dims : List Bool) (shape : List Nat) : List Nat := shape
def method1867 (dims : List Bool) : List Nat := List.replicate dims.length 0
def method1869 (_dims : List Bool) (shape : List Nat) : List Nat := shape
def method1872 (_ndim : Int) : List Nat := []
def method1873 (_ndim : Int) (nshape : List Nat) : List Nat := nshape
def method1874 (_ndim : Int) (dims : List Bool) : List Nat := List.replicate dims.length 1
def method1894 (dim : Int) (a b : Nat) : Except String Nat :=
  if a = b then .ok a else .error s!"mismatch in dimension {dim} (expected {a} got {b})"
def method1897 (dims2cat : List Int → β) (dims : List Int) : β := dims2cat dims
def method1905 (promote : List α → τ) (cat : List Int → τ → List α → β)
    (dims : List Int) (xs : List α) : β := cat dims (promote xs) xs
def method1918 (cat : List Int → τ → List α → β) (t : τ) (xs : List α) (dims : List Int) : β :=
  cat dims t xs
def method1921 (offset : α → List Nat → List Bool → List Nat → List β → γ)
    (a : α) (shape : List Nat) (catdims : List Bool) (xs : List β) : γ :=
  offset a shape catdims (List.replicate shape.length 0) xs
def method1928 (a : α) (_shape : β) (_dims : γ) (_offsets : δ) : α := a
def method1941 (view : α → ι → β) (fill : β → γ → δ) (a : α) (inds : ι) (x : γ) : δ :=
  fill (view a inds) x
def method1942 (set : α → ι → β → γ) (a : α) (inds : ι) (x : β) : γ := set a inds x
def callDim (call : Nat → List α → β) (dim : Nat) (xs : List α) : β := call dim xs

def method2003 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def method2053 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def method2055 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def method2056 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs
def method2169 (cat : δ → List α → β) (dims : δ) (xs : List α) : β := cat dims xs
def method2171 (cat : δ → τ → List α → β) (dims : δ) (t : τ) (xs : List α) : β := cat dims t xs
def vcatRoute (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def hcatRoute (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def typedVcatRoute (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def typedHcatRoute (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs

def method2175 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def method2176 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def method2177 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def method2178 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def method2179 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def method2180 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def method2181 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def method2182 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def method2184 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def method2185 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def method2186 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def method2187 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs
def method2188 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs
def method2189 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs
def method2194 (length : α → Nat) (hvcat : List Nat → List α → β) (rows : List α) : β :=
  hvcat (rows.map length) rows
def method2195 (length : α → Nat) (hvcat : τ → List Nat → List α → β)
    (t : τ) (rows : List α) : β := hvcat t (rows.map length) rows
def method2197 (hvcat : List Nat → List α → β) (columns : Int) (values : List α) : Jl β := do
  if columns = 0 then throw .divideError
  if (values.length : Int) % columns != 0 then
    throw (.argumentError "number of arrays is not a multiple of block columns")
  let rows := (values.length : Int) / columns
  if rows < 0 then throw (.argumentError "tuple length must be nonnegative")
  return hvcat (List.replicate rows.toNat columns.toNat) values
def method2244 (promote : List α → τ) (call : τ → List Nat → List α → β)
    (rows : List Nat) (xs : List α) : β := call (promote xs) rows xs
def method2245 (call : τ → List Nat → List α → β) (t : τ) (rows : List Nat) (xs : List α) : β :=
  call t rows xs
def method2247 (rows : List Nat) : Sum (Nat × Nat) (List Nat × Nat) :=
  match rows with
  | [] => .inl (0, 0)
  | first :: _ => if rows.all (· == first) then .inl (rows.length, first)
    else .inr (rows, rows.foldl (· + ·) 0)
def method2248 (shape : List Nat → σ) (call : τ → σ → Bool → List α → β)
    (t : τ) (rows : List Nat) (xs : List α) : β := call t (shape rows) true xs
inductive JuliaAny

def method2250 (_rows : List Nat) : List JuliaAny := []
def method2251 (elementType : Type) (_rows : List Nat) : List elementType := []
def method2274 (promote : List α → τ) (call : τ → List Nat → List α → β)
    (rows : List Nat) (xs : List α) : β := call (promote xs) rows xs
def method2275 (promote : List α → τ) (call : τ → List Nat → List α → β)
    (rows : List Nat) (xs : List α) : β := call (promote xs) rows xs
def method2277 (promote : List α → τ) (call : τ → List Nat → List α → β)
    (rows : List Nat) (xs : List α) : β := call (promote xs) rows xs
def method2292 (shape : List Nat → σ) (call : τ → σ → Bool → List α → β)
    (t : τ) (rows : List Nat) (xs : List α) : β := call t (shape rows) true xs
end JuliaLean.AbstractArrayCov.Rows.ConcatDirect

/-! Loop and branch-heavy concatenation methods in `base/abstractarray.jl:1744-2279`. -/

namespace JuliaLean.AbstractArrayCov.Rows.ConcatComplex

open JuliaLean
open JuliaLean.AbstractArrayCov.Rows.ConcatDirect

def method1744 (vectors : List (List α)) : List α := vectors.flatten
structure Block (α : Type) where
  rows : Nat
  cols : Nat
  dense : Bool
  values : List α
  deriving Repr, DecidableEq

def sameRows (n : Nat) : List (Block α) → Bool
  | [] => true
  | b :: rest => b.rows = n && sameRows n rest

def method1768 (blocks : List (Block α)) : Except String (MatrixResult α) :=
  match blocks with
  | [] => .error "empty concatenation"
  | first :: _ =>
      if !sameRows first.rows blocks then .error "number of rows must match"
      else
        let cols := blocks.foldl (fun n b => n + if b.cols = 0 then 1 else b.cols) 0
        let dense := blocks.all (·.dense)
        if dense then .ok ⟨first.rows, cols, blocks.flatMap (·.values)⟩
        else .ok ⟨first.rows, cols, blocks.flatMap (·.values)⟩
def sameCols (n : Nat) : List (Block α) → Bool
  | [] => true
  | b :: rest => b.cols = n && sameCols n rest

def method1805 (blocks : List (Block α)) : Except String (MatrixResult α) :=
  match blocks with
  | [] => .error "empty concatenation"
  | first :: _ =>
      if !sameCols first.cols blocks then .error "number of columns must match"
      else
        let result := ⟨blocks.foldl (fun n b => n + b.rows) 0, first.cols,
          blocks.flatMap (·.values)⟩
        .ok result
def method1859 (combine : List Bool → List Nat → List Nat → Except String (List Nat))
    (dims : List Bool) (shapes : List (List Nat)) : Except String (List Nat) :=
  shapes.foldlM (fun out shape => combine dims out shape) []
def method1868 (catSize : α → List Nat)
    (combine : List Bool → List Nat → List Nat → Except String (List Nat))
    (recurse : List Bool → List Nat → List α → Except String (List Nat))
    (dims : List Bool) (x : α) (rest : List α) : Except String (List Nat) := do
  let shape ← combine dims [] (catSize x)
  recurse dims shape rest
def method1870 (catSize : α → List Nat)
    (combine : List Bool → List Nat → List Nat → Except String (List Nat))
    (recurse : List Bool → List Nat → List α → Except String (List Nat))
    (dims : List Bool) (shape : List Nat) (x : α) (rest : List α) : Except String (List Nat) := do
  let shape ← combine dims shape (catSize x)
  recurse dims shape rest
def method1875 (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (dims : List Bool) (shape : List Nat) : Except String (List Nat) :=
  match dims, shape with
  | d :: ds, a :: rest => do return (a + (if d then 1 else 0)) ::
      (← recurse (ndim + 1) ds rest [])
  | _, _ => .error "invalid recursive shape"
def method1877 (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (dims : List Bool) (nshape : List Nat) : Except String (List Nat) :=
  match dims, nshape with
  | _ :: ds, b :: rest => do return b :: (← recurse (ndim + 1) ds [] rest)
  | _, _ => .error "invalid recursive shape"
def method1879 (check : Int → Nat → Nat → Except String Nat)
    (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (shape : List Nat) : Except String (List Nat) :=
  match shape with
  | [] => .ok []
  | a :: rest => do
      let _ ← check ndim a 1
      return 1 :: (← recurse (ndim + 1) [] rest [])
def method1883 (check : Int → Nat → Nat → Except String Nat)
    (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (shape nshape : List Nat) : Except String (List Nat) :=
  match shape, nshape with
  | a :: as, b :: bs => do
      let next ← check ndim a b
      return next :: (← recurse (ndim + 1) [] as bs)
  | _, _ => .error "invalid recursive shape"
def method1887 (check : Int → Nat → Nat → Except String Nat)
    (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (dims : List Bool) (shape nshape : List Nat) : Except String (List Nat) :=
  match dims, shape, nshape with
  | d :: ds, a :: as, b :: bs => do
      let next ← if d then .ok (a + b) else check ndim a b
      return next :: (← recurse (ndim + 1) ds as bs)
  | _, _, _ => .error "invalid recursive shape"
def method1898 (dims : List Int) : Jl (List Bool) := do
  if dims.any (· ≤ 0) then throw (.argumentError "cat dimensions must be positive")
  match dims.max? with
  | none => throw (.argumentError "empty cat dimensions")
  | some maximum => return (List.range maximum.toNat).map fun (i : Nat) => dims.contains ((i : Int) + 1)
def method1907 (dims2cat : δ → Jl (List Bool)) (shape : List Bool → List α → Jl σ)
    (allocate : α → τ → σ → Jl β) (zero : τ → γ) (fill : β → γ → Jl β)
    (finish : β → σ → List Bool → List α → Jl β)
    (dims : δ) (t : τ) (xs : List α) : Jl β := do
  let catdims ← dims2cat dims
  let outShape ← shape catdims xs
  let first ← match xs with | x :: _ => .ok x | [] => throw (JlError.argumentError "empty cat")
  let out ← allocate first t outShape
  let out ← if catdims.count true > 1 then fill out (zero t) else .ok out
  finish out outShape catdims xs
def method1923 (one : α → σ → List Bool → List Nat → β → List β → Jl (List Nat))
    (recurse : α → σ → List Bool → List Nat → List β → Jl α)
    (a : α) (shape : σ) (dims : List Bool) (offsets : List Nat) (x : β) (xs : List β) : Jl α := do
  let offsets ← one a shape dims offsets x xs
  recurse a shape dims offsets xs
def method1930 (catSize : α → Nat → Nat) (copy : β → List (List Nat) → α → Jl Unit)
    (a : β) (shape : List Nat) (dims : List Bool) (offsets : List Nat) (x : α) : Jl (List Nat) := do
  let inds := (List.range offsets.length).map fun i =>
    if dims.getD i false then (List.range (catSize x i)).map (· + offsets.getD i 0)
    else List.range (shape.getD i 0)
  copy a inds x
  return (List.range offsets.length).map fun i =>
    if dims.getD i false then offsets.getD i 0 + catSize x i else offsets.getD i 0
def rowMajorToColumnMajor (rows cols : Nat) (values : List α) : List α :=
  (List.range cols).flatMap fun j => (List.range rows).filterMap fun i => values[i * cols + j]?

def method2253 (rows : List Nat) (values : List α) : Except String (MatrixResult α) :=
  match rows with
  | [] => .error "empty rows"
  | cols :: _ =>
      if rows.length * cols != values.length then .error "argument count mismatch"
      else if !rows.all (· == cols) then .error "row column mismatch"
      else .ok ⟨rows.length, cols, rowMajorToColumnMajor rows.length cols values⟩
def method2279 (allocate : τ → Nat → Nat → β) (fill : β → Bool → List α → γ)
    (t : τ) (rows : List Nat) (values : List α) : Except String γ :=
  match rows with
  | [] => .error "empty rows"
  | cols :: rest =>
      if !rest.all (· == cols) then .error "row column mismatch"
      else .ok (fill (allocate t rows.length cols) true values)
end JuliaLean.AbstractArrayCov.Rows.ConcatComplex

/-! Method-specific models for `base/abstractarray.jl:2381-2874`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Hvncat

open JuliaLean
open JuliaLean.AbstractArrayCov.Rows.ConcatComplex

def routeShape (call : σ → Bool → List α → β) (shape : σ) (rowFirst : Bool)
    (xs : List α) : β := call shape rowFirst xs

def method2381 (call : σ → Bool → List α → β) (shape : σ) (rowFirst : Bool) (xs : List α) : β :=
  call shape rowFirst xs
def method2382 (call : Int → Bool → List α → β) (dim : Int) (xs : List α) : β := call dim true xs
def method2384 (call : τ → σ → Bool → List α → β) (anyType : τ)
    (shape : σ) (rowFirst : Bool) : β := call anyType shape rowFirst []
def promoted (promote : List α → τ) (call : τ → σ → Bool → List α → β)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call (promote xs) shape rowFirst xs

def method2385 (promote : List α → τ) (call : τ → σ → Bool → List α → β)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call (promote xs) shape rowFirst xs
def method2386 (call : τ → σ → Bool → List α → β) (t : τ)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call t shape rowFirst xs
def method2387 (promote : List α → τ) (call : τ → σ → Bool → List α → β)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call (promote xs) shape rowFirst xs
def method2388 (promote : List α → τ) (call : τ → σ → Bool → List α → β)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call (promote xs) shape rowFirst xs
def method2389 (call : τ → σ → Bool → List α → β) (t : τ)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call t shape rowFirst xs
def method2392 (call : τ → σ → Bool → List α → β) (t : τ)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call t shape rowFirst xs
def method2393 (call : τ → Int → List α → β) (t : τ) (dim : Int) (xs : List α) : β :=
  call t dim xs
def onlyOneError : Jl α := .error (.argumentError "a 0-dimensional array may only contain exactly one element")

def method2397 : Jl α := onlyOneError
def method2398 (convert : τ → α → β) (fill : β → γ) (t : τ) (x : α) : γ := fill (convert t x)
def method2399 (convert : τ → α → β) (fill : β → γ) (t : τ) (x : α) : γ := fill (convert t x)
def method2400 (convert : τ → α → β) (t : τ) (xs : List α) : List β := xs.map (convert t)
def method2401 : Jl α := onlyOneError
def method2402 : Jl α := onlyOneError
def method2403 : Jl α := onlyOneError
def method2405 : Jl α := onlyOneError
def method2409 (call : τ → Int → List α → β) (t : τ) (dim : Int)
    (_rowFirst : Bool) (xs : List α) : β := call t dim xs
def method2411 (allocate : τ → Nat → List Nat → β) (t : τ) (rank : Int) : Jl β := do
  if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
  return allocate t rank.toNat (List.replicate rank.toNat 0)
def method2417 (convert : τ → α → β) (reshape : List β → List Nat → γ)
    (t : τ) (rank : Int) (xs : List α) : Jl γ := do
  if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
  return reshape (xs.map (convert t)) (List.replicate (rank - 1).toNat 1 ++ [xs.length])
structure CatMeta (α : Type) where
  dims : List Nat
  values : List α
  deriving Repr, DecidableEq

def method2423 (fallback : τ → Int → List (CatMeta α) → β)
    (linear : τ → Int → List (CatMeta α) → β) (t : τ) (rank : Int)
    (arrays : List (CatMeta α)) : Jl β := do
  if arrays.isEmpty then throw (.argumentError "must have at least one element")
  if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
  if arrays.any (fun a => (a.dims.drop rank.toNat).any (· != 1)) then
    return fallback t rank arrays
  return linear t rank arrays
def method2458 (build : τ → Int → List (CatMeta α) → β)
    (t : τ) (rank : Int) (values : List (CatMeta α)) : Jl β := do
  if values.isEmpty then throw (.argumentError "must have at least one element")
  if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
  if values.any (fun a => (a.dims.take (rank - 1).toNat).any (· != 1)) then
    throw (.argumentError "non-concatenated dimensions must have length 1")
  return build t rank values
def method2492 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def method2493 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def method2498 (call : τ → Int → Bool → List α → β) (t : τ)
    (dims : List Int) (_rowFirst : Bool) (xs : List α) : Option β :=
  dims.head?.map fun d => call t d false xs
def method2499 (call : τ → Int → Bool → List α → β) (t : τ)
    (dims : List Int) (_rowFirst : Bool) (xs : List α) : Option β :=
  dims.head?.map fun d => call t d false xs
def method2501 (call : τ → Int → List α → β) (t : τ) (size : Int)
    (rowFirst : Bool) (xs : List α) : Jl β := do
  if size ≤ 0 then throw (.argumentError "dimsshape must be positive")
  if xs.length != size.toNat then throw (.argumentError "element count mismatch")
  return call t (if rowFirst then 2 else 1) xs
def method2514 (allocate : τ → List Nat → β) (fill : β → Bool → List α → γ)
    (t : τ) (dims : List Int) (rowFirst : Bool) (xs : List α) : Jl γ := do
  if dims.any (· ≤ 0) then throw (.argumentError "dims must be positive")
  let shape := dims.map Int.toNat
  if shape.foldl (· * ·) 1 != xs.length then throw (.argumentError "argument count mismatch")
  return fill (allocate t shape) rowFirst xs
def rowFirstValues (rows cols : Nat) (values : List α) : List α :=
  (List.range cols).flatMap fun j => (List.range rows).filterMap fun i => values[i * cols + j]?

def method2527 (rows cols pages : Nat) (rowFirst : Bool) (values : List α) : Jl (List α) := do
  if rows * cols * pages != values.length then throw (.argumentError "argument count mismatch")
  if rowFirst then
    return (List.range pages).flatMap fun page =>
      rowFirstValues rows cols ((values.drop (page * rows * cols)).take (rows * cols))
  return values
def method2556 (generated : Bool) (small : β) (fallback : β) : β := if generated then small else fallback
def method2629 (rankOf : α → Nat) (build : τ → List Int → Bool → List α → β)
    (t : τ) (dims : List Int) (rowFirst : Bool) (values : List α) : β :=
  let rank := max ((values.map rankOf).max?.getD 0) dims.length
  build t (dims ++ List.replicate (rank - dims.length) 1) rowFirst values
def stagedBuilder (validate : List Int → List (CatMeta α) → Jl Unit)
    (discover : List Int → Bool → List (CatMeta α) → Jl (List Nat))
    (allocate : List Nat → Jl β) (fill : β → Bool → List (CatMeta α) → Jl β)
    (dims : List Int) (rowFirst : Bool) (values : List (CatMeta α)) : Jl β := do
  if values.isEmpty then throw (.argumentError "must have at least one element")
  if dims.any (· ≤ 0) then throw (.argumentError "dims must be positive")
  validate dims values
  let shape ← discover dims rowFirst values
  let out ← allocate shape
  fill out rowFirst values

def method2635 := @stagedBuilder
def method2732 (call : τ → Int → Bool → List α → β) (t : τ)
    (shape : List (List Int)) (rowFirst : Bool) (xs : List α) : Jl β :=
  match shape with
  | [level] => match level with
    | d :: _ => if d > 0 then .ok (call t d rowFirst xs) else .error (.argumentError "empty shape level")
    | [] => .error (.argumentError "empty shape level")
  | _ => .error (.argumentError "expected one shape level")
def method2738 (rankOf : α → Nat) (build : τ → List (List Int) → Bool → List α → β)
    (t : τ) (shape : List (List Int)) (rowFirst : Bool) (values : List α) : β :=
  let rank := max ((values.map rankOf).max?.getD 0) shape.length
  build t (shape ++ List.replicate (rank - shape.length) shape.getLast!) rowFirst values
def method2744 (validate : List (List Int) → List (CatMeta α) → Jl Unit)
    (discover : List (List Int) → Bool → List (CatMeta α) → Jl (List Nat))
    (allocate : List Nat → Jl β) (fill : β → Bool → List (CatMeta α) → Jl β)
    (shape : List (List Int)) (rowFirst : Bool) (values : List (CatMeta α)) : Jl β := do
  if values.isEmpty then throw (.argumentError "must have at least one element")
  if shape.flatten.any (· ≤ 0) then throw (.argumentError "shape values must be positive")
  if shape.any List.isEmpty then throw (.argumentError "shape levels must be nonempty")
  validate shape values
  let dims ← discover shape rowFirst values
  let out ← allocate dims
  fill out rowFirst values
def method2823 (rank d1 d2 : Nat) (scratch1 scratch2 : List Nat)
    (fill : List Nat → List Nat → Nat → Nat → List α → Jl β) (values : List α) : Jl β := do
  if rank ≤ 1 then throw (.argumentError "destination rank must be at least 2")
  if scratch1.length != rank || scratch2.length != rank then throw (.argumentError "scratch rank mismatch")
  if !(0 < d1 && d1 < 3 && 0 < d2 && d2 < 3 && d1 != d2) then throw (.argumentError "invalid d1/d2")
  fill scratch1 scratch2 d1 d2 values
def method2865 (offsets inner products : List Int) : Int :=
  match offsets, inner with
  | o :: os, i :: is =>
      ((os.zip is).zip products).foldl (fun out p => out + (p.1.1 + p.1.2) * p.2) (o + i + 1)
  | _, _ => 1
end JuliaLean.AbstractArrayCov.Rows.Hvncat

/-! Method-specific models for `base/abstractarray.jl:2967-3101`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Stack

open JuliaLean

def method2967 (stack : δ → α → β) (dims : δ) (iter : α) : β := stack dims iter
def method2996 (map : (α → β) → γ → δ) (stack : σ → δ → ε)
    (f : α → β) (iter : γ) (dims : σ) : ε := stack dims (map f iter)
def method2997 (zip : α → List β → γ) (map : (δ → ε) → γ → ζ)
    (stack : σ → ζ → η) (f : δ → ε) (xs : α) (rest : List β) (dims : σ) : η :=
  stack dims (map f (zip xs rest))
def method2999 (iteratorSize : α → σ) (stack : δ → σ → α → β)
    (dims : δ) (iter : α) : β := stack dims (iteratorSize iter) iter
def method3001 (collect : α → β) (stack : δ → β → γ) (dims : δ) (iter : α) : γ :=
  stack dims (collect iter)
def method3003 (defaultType : α → τ) (elementType : τ → σ) (concrete : σ → Bool)
    (typed : δ → σ → τ → α → β) (collect : α → α) (isempty : α → Bool)
    (empty : δ → σ → τ → α → β) (promote : α → σ)
    (dims : δ) (iter : α) : β :=
  let s := defaultType iter
  let t := elementType s
  if concrete t then typed dims t s iter
  else
    let array := collect iter
    if isempty array then empty dims t s iter else typed dims (promote array) (defaultType array) array
def method3016 (iterate : α → List β) (axes : β → List γ)
    (allocate : β → List γ → List γ → δ) (copy : δ → Nat → β → δ)
    (a : α) (containerAxes : List γ) : Except String δ :=
  match iterate a with
  | [] => .error "stack on empty"
  | first :: rest =>
      let sliceAxes := axes first
      let out := allocate first sliceAxes containerAxes
      .ok ((first :: rest).foldl (fun out x => copy out 0 x) out)
def method3034 (iteratorSize : α → σ) (axes : α → σ → β) (x : α) : β :=
  axes x (iteratorSize x)
def method3035 (length : α → Nat) (oneTo : Nat → β) (x : α) : List β := [oneTo (length x)]
def method3036 (axes : α → β) (x : α) : β := axes x
def method3039 (iteratorSize : τ → σ) (typed : Int → α → τ → σ → β)
    (dims : Int) (t : α) (s : τ) : β := typed dims t s (iteratorSize s)
def method3041 (colonStack dimStack : β) (dims rank : Nat) : β :=
  if dims = rank + 1 then colonStack else dimStack
def method3048 (dimStack : Int → τ → σ → α → β) (dims : Int) (t : τ) (s : σ) (a : α) : β :=
  dimStack dims t s a
def method3051 (length : α → Nat) (oneTo : Nat → α) (axes : List α) : Option α :=
  match axes with
  | [axis] => some axis
  | _ => some (oneTo ((axes.map length).foldl (· * ·) 1))
def method3053 (peel : α → Option (β × List β)) (axes : β → List γ)
    (newAxis : α → γ) (allocate : β → List γ → δ)
    (fill : Nat → δ → β → List β → δ) (dims : Nat) (a : α) : Except String δ :=
  match peel a with
  | none => .error "stack on empty"
  | some (first, rest) =>
      let sliceAxes := axes first
      if !(1 ≤ dims && dims ≤ sliceAxes.length + 1) then .error "invalid stack dimension"
      else
        let outAxes := sliceAxes.take (dims - 1) ++ [newAxis a] ++ sliceAxes.drop (dims - 1)
        .ok (fill dims (allocate first outAxes) first rest)
def method3075 (copy : δ → Nat → β → δ) (check : β → Jl Unit)
    (firstIndex : Nat) (out : δ) (first : β) (rest : List β) : Jl δ := do
  let mut out := copy out firstIndex first
  let mut i := firstIndex
  for x in rest do
    check x
    i := i + 1
    out := copy out i x
  return out
def method3089 [BEq α] (axes : β → List α) (x : β) (expected : List α) : Except String Unit :=
  if axes x == expected then .ok () else .error "stack expects uniform slices"
def method3098 (x : α) : α := x
def method3099 : List Nat := []
def method3101 : Jl α := .error (.argumentError "`stack` on an empty collection is not allowed")
end JuliaLean.AbstractArrayCov.Rows.Stack

/-! Method-specific models for `base/abstractarray.jl:3106-3275`. -/

namespace JuliaLean.AbstractArrayCov.Rows.OrderIndex

open JuliaLean
open JuliaLean.AbstractArrays

abbrev I64 := JInt .i64
def i64 (x : Int) : I64 := JInt.lit .i64 x

def method3106 [BEq β] (identical : α → α → Bool) (axes : α → β)
    (values : α → List γ) (equal : γ → γ → Bool) (a b : α) : Bool :=
  if identical a b then true
  else if axes a != axes b then false
  else ((values a).zip (values b)).all fun p => equal p.1 p.2
def lexCmp (equal : α → β → Bool) (less : α → β → Bool) : List (α × β) → Int
  | [] => 0
  | p :: rest => if equal p.1 p.2 then lexCmp equal less rest else if less p.1 p.2 then -1 else 1

def compareInt (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0
def compareNat (a b : Nat) : Int := if a < b then -1 else if b < a then 1 else 0

def method3119 (firstindex : α → Int) (values : α → List β)
    (equal less : β → β → Bool) (a b : α) : Int :=
  let firstCmp := compareInt (firstindex a) (firstindex b)
  let pairs := (values a).zip (values b)
  let lengthCmp := compareNat (values a).length (values b).length
  if firstCmp != 0 then firstCmp
  else let c := lexCmp equal less pairs; if c != 0 then c else lengthCmp
def method3135 (onlyA : α) (onlyB : β) (less : α → β → Bool) : Bool := less onlyA onlyB
def method3145 (cmp : α → α → Int) (a b : α) : Bool := decide (cmp a b < 0)
def method3147 (elementStyle : τ → σ) (t : τ) : σ := elementStyle t
inductive Tri where | false | missing | true
  deriving Repr, DecidableEq

def method3149 [BEq β] (axes : α → β) (compareValues : α → α → List Tri) (a b : α) : Tri :=
  if axes a != axes b then .false
  else let results := compareValues a b
    if results.contains .false then .false
    else if results.contains .missing then .missing else .true
def method3167 (axes : α → β) (sub2ind : β → List Int → γ) (a : α) (indices : List Int) : γ :=
  sub2ind (axes a) indices
def method3172 (axes : α → β) (ind2sub : β → Int → γ) (a : α) (index : Int) : γ :=
  ind2sub (axes a) index
def method3178 : Int := 1
def method3179 (_dims : α) : Int := 1
def method3180 (_inds : α) : Int := 1
def method3181 (recurse : List Int → I64 → I64 → List I64 → I64)
    (indices : List I64) : I64 := recurse [] (i64 1) (i64 1) indices
def method3184 (recurse : α → I64 → I64 → List I64 → I64)
    (dims : α) (indices : List I64) : I64 := recurse dims (i64 1) (i64 1) indices
def method3185 (recurse : α → I64 → I64 → List I64 → I64)
    (inds : α) (indices : List I64) : I64 := recurse inds (i64 1) (i64 1) indices
def method3188 : Jl I64 := .error (.argumentError "Linear indexing is not defined for one-dimensional arrays")
def method3190 (recurse : α → I64 → I64 → List I64 → I64)
    (inds : α) (indices : List I64) : I64 := recurse inds (i64 1) (i64 1) indices
def method3191 (i : I64) : I64 := i
def method3193 (_inds : α) (_stride : I64) (index : I64) : I64 := index
def method3194 (recurse : I64 → I64 → List I64 → I64)
    (stride index : I64) (indices : List I64) : I64 :=
  match indices with
  | [] => index
  | i :: rest => recurse stride (index + (i - i64 1) * stride) rest
def method3198 (nextStride : I64 → Axis → I64) (recurse : List Axis → I64 → I64 → List I64 → I64)
    (inds : List Axis) (stride index : I64) (indices : List I64) : I64 :=
  match inds, indices with
  | axis :: axes, i :: rest => recurse axes (nextStride stride axis)
      (index + (i - axis.first) * stride) rest
  | _, _ => index
def method3204 (stride length : I64) : I64 := stride * length
def method3205 (stride : I64) (axis : Axis) : I64 := stride * i64 axis.len
def method3206 (stride : I64) (slice : Axis) : I64 := stride * i64 slice.len
def method3207 (i _length : I64) : I64 := i - i64 1
def method3208 (i : I64) (axis : Axis) : I64 := i - axis.first
def method3210 (index : I64) : Jl (List I64) :=
  if index.val = 1 then .ok [] else .error .boundsError
def method3211 (recurse : α → I64 → β) (dims : α) (index : I64) : β :=
  recurse dims (index - i64 1)
def method3212 (recurse : α → I64 → β) (inds : α) (index : I64) : β :=
  recurse inds (index - i64 1)
def method3213 : Jl (List I64) := .error (.argumentError "Linear indexing is not defined for one-dimensional arrays")
def method3215 (index : I64) : List I64 := [index]
def method3217 (index : I64) : List I64 := [index + i64 1]
def method3218 (lookup : I64 → Axis → I64) (axis : Axis) (index : I64) : List I64 :=
  [lookup index axis]
def method3222 (recurse : List Axis → I64 → List I64) (inds : List Axis) (index : I64) : List I64 :=
  match inds with
  | [] => [index + i64 1]
  | axis :: rest =>
      let divisor := i64 axis.len
      let q := i64 (index.val / divisor.val)
      let r := i64 (index.val % divisor.val)
      (axis.first + r) :: recurse rest q
def method3229 (dimension : I64) : I64 := dimension
def method3230 (axis : Axis) : I64 := i64 axis.len
def method3231 (index _dimension : I64) : I64 := index + i64 1
def method3232 (index : I64) (axis : Axis) : I64 := index + axis.first
def method3235 : Jl (List I64) := .error (.argumentError "Linear indexing is not defined for one-dimensional arrays")
def method3238 (call : List Axis → List (List I64) → β) (inds : List Axis) (indices : List (List I64)) : β := call inds indices
def method3240 (call : List Axis → List (List I64) → β) (inds : List Axis) (indices : List (List I64)) : β := call inds indices
def method3242 (sameAxes : List (List I64) → Bool)
    (similar : List I64 → List I64) (fill : List I64 → List (List I64) → List I64)
    (indices : List (List I64)) : Except String (List I64) :=
  match indices with
  | [] => .error "missing index vector"
  | first :: _ => if !sameAxes indices then .error "index axes mismatch"
    else .ok (fill (similar first) indices)
def method3253 (sub2ind : List Axis → List I64 → I64)
    (inds : List Axis) (coordinates : List (List I64)) : List I64 :=
  match coordinates with
  | [] => []
  | first :: _ => (List.range first.length).map fun k =>
      sub2ind inds (coordinates.filterMap fun is => is[k]?)
def method3262 (sub2ind : List Axis → List I64 → I64) (inds : List Axis)
    (i : Nat) (vectors : List (List I64)) : I64 :=
  sub2ind inds (vectors.filterMap fun v => v[i]?)
def method3263 (i : Nat) (first : List I64) (rest : List (List I64)) : List I64 :=
  first[i]?.toList ++ rest.filterMap fun v => v[i]?
def method3264 (_i : Nat) : List I64 := []
def method3266 (ind2sub : List Axis → I64 → List I64)
    (inds : List Axis) (indices : List I64) : List (List I64) :=
  (List.range inds.length).map fun d => indices.filterMap fun index => (ind2sub inds index)[d]?
end JuliaLean.AbstractArrayCov.Rows.OrderIndex

/-! Method-specific models for `base/abstractarray.jl:3307-3766`. -/

namespace JuliaLean.AbstractArrayCov.Rows.MapMut

open JuliaLean

def method3307 (f : σ → α → σ) (state : σ) (values : List α) : σ × Unit :=
  (values.foldl f state, ())
def method3308 (f : σ → List α → σ) (state : σ) (zipped : List (List α)) : σ × Unit :=
  (zipped.foldl f state, ())
def method3385 (mapAll : Jl ε) (rank : Nat) (dims : List Int)
    (firstSlice : Jl α) (applyFirst : α → Jl γ)
    (prepareResult : α → γ → Jl δ) (allocate : δ → Jl ε)
    (placeFirst : ε → δ → Jl ε) (inner : ε → Jl ε) : Jl ε := do
  if dims.isEmpty then return ← mapAll
  for d in dims do
    if d < 1 then throw (.argumentError "mapslices dimension must be at least 1")
    if rank < d then throw (.argumentError "mapslices dimension exceeds rank")
  let slice ← firstSlice
  let firstResult ← applyFirst slice
  let prepared ← prepareResult slice firstResult
  let out ← allocate prepared
  let out ← placeFirst out prepared
  inner out
def foldIndices (step : δ → ι → Jl δ) : δ → List ι → Jl δ
  | out, [] => .ok out
  | out, i :: rest => do foldIndices step (← step out i) rest

def method3450 (safe : Bool) (reuseOne freshOne : δ → ι → Jl δ)
    (out : δ) (indices : List ι) : Jl δ :=
  if safe then foldIndices reuseOne out indices else foldIndices freshOne out indices
def method3477 (broadcastSet : δ → List ι → α → δ) (out : δ)
    (value : α) (indices : List ι) : δ := broadcastSet out indices value
def method3478 (set : δ → List ι → α → δ) (out : δ) (value : α) (indices : List ι) : δ :=
  set out indices value
def method3482 (f : α → β) (dest : List β) (source : List α) : List β :=
  let values := source.map f
  values ++ dest.drop values.length
def method3491 (generator : (α → β) → γ → δ) (collect : γ → δ → ε)
    (f : α → β) (a : γ) : ε := collect a (generator f a)
def method3493 (allocate : Nat → List β) (f : α → β) (source : List α) : List β :=
  method3482 f (allocate source.length) source
def method3494 (f : α → β) (source : List α) : List β := source.map f
def method3521 (generator : (α → β) → γ → δ) (collect : δ → ε)
    (f : α → β) (source : γ) : ε := collect (generator f source)
def method3523 : Except String α := .error "map is not defined on dictionaries"
def method3524 : Except String α := .error "map is not defined on sets"
def method3527 (f : α → β → γ) (dest : List γ) (as : List α) (bs : List β) : List γ :=
  let values := (as.zip bs).map fun p => f p.1 p.2
  values ++ dest.drop values.length
def method3538 (_i : Nat) : List α := []
def method3539 (i : Nat) (arrays : List (List α)) : List α := arrays.filterMap fun a => a[i]?
def method3544 (linearIndices : List α → List Nat) (linear cartesian : δ → List (List α) → δ)
    (destIndices : List Nat) (dest : δ) (arrays : List (List α)) : δ :=
  if arrays.all (fun a => linearIndices a == destIndices) then linear dest arrays else cartesian dest arrays
def method3593 (mapN : (List α → β) → δ → List (List α) → γ)
    (f : List α → β) (dest : δ) (arrays : List (List α)) : Except String γ :=
  if arrays.isEmpty then .error "should dispatch to unary map!" else .ok (mapN f dest arrays)
def method3618 (map : (α → α) → β → β → γ) (f : α → α) (array : β) : γ :=
  map f array array
def method3645 (generator : (List α → β) → List (List α) → γ)
    (collect : γ → δ) (f : List α → β) (iters : List (List α)) : δ :=
  collect (generator f iters)
def method3649 (convert : α → Jl β) (append : List β → β → List β)
    (a : List β) (item : α) : Jl (List β) := do
  let item ← convert item
  return append a item
def method3659 (a : List α) (x : α) : List α := a ++ [x]
def method3665 (a xs : List α) : List α := a ++ xs
def method3679 (push : α → β → α) (a : α) (x y : β) : α := push (push a x) y
def method3680 (push2 : α → β → β → α) (pushMany : α → List β → α)
    (a : α) (x y : β) (rest : List β) : α := pushMany (push2 a x y) rest
def method3681 (pushfirst : α → β → α) (a : α) (x y : β) : α :=
  pushfirst (pushfirst a y) x
def method3682 (pushMany : α → List β → α) (push2 : α → β → β → α)
    (a : α) (x y : β) (rest : List β) : α := push2 (pushMany a rest) x y
def method3685 (a : α) (_hint : β) : α := a
def method3688 (length : α → Nat) (rest : α → σ → List β)
    (a : α) (state : σ) : List β :=
  let out : List β := []
  let _hint := length a
  (rest a state).foldl (fun out x => out ++ [x]) out
def method3699
    (keepat : JuliaLean.ArrayOps.Vec α → List JuliaLean.JInt64 → JuliaLean.ArrayOps.Out α Unit)
    (values : JuliaLean.ArrayOps.Vec α)
    (indices : List JuliaLean.JInt64) : JuliaLean.ArrayOps.Out α Unit :=
  keepat values indices
def method3717 (values : List α) (mask : List Bool) : Except String (List α) :=
  if mask.length != values.length then .error "bounds"
  else .ok ((values.zip mask).filterMap fun p => if p.2 then some p.1 else none)
def method3756 (length : α → Nat) (modShift : Int → Nat → Int)
    (lastindex firstindex : α → Int) (reverseWindow : α → Int → Int → α)
    (reverseAll : α → α) (a : α) (shift : Int) : α :=
  let n := length a
  if n = 0 then a
  else let shift := modShift shift n
    if shift = 0 then a
    else let last := lastindex a
      reverseAll (reverseWindow (reverseWindow a (firstindex a) (last - shift))
        (last - shift + 1) (lastindex a))
end JuliaLean.AbstractArrayCov.Rows.MapMut

namespace JuliaLean.ArrayOps

open JuliaLean

variable {α β : Type}

/-- `v[i]` for a `Vector`: `getindex(A::Array, i1::Integer)` → `to_indices`
(base/abstractarray.jl:1369), then the `Int` method. -/
def getindex {t : IntTy} (a : List α) (i : JInt t) : Jl α := do
  getAt a (← toIndexArray i)

/-- `checkbounds(Bool, v, i)` for an integer index: `checkindex(Bool, OneTo(n), i::Real)`
(base/abstractarray.jl:751), `(first(inds) <= i) & (i <= last(inds))`, compared
exactly across integer types. -/
def checkboundsInt {t : IntTy} (a : List α) (i : JInt t) : Bool :=
  decide (1 ≤ i.val ∧ i.val ≤ a.length)

/-- `circshift!(a::AbstractVector, shift::Integer)`, `base/abstractarray.jl:3756-3766`:
three `reverse!`s. -/
def circshiftBang [Inhabited α]
    (reverseBang : {s t : IntTy} → List α → JInt s → JInt t → Jl (List α)) {t : IntTy} (a : List α) (shift : JInt t) : Jl (List α) := do
  let n := a.length
  if n = 0 then return a
  let s := modShift shift n
  if s = 0 then return a
  let l : JInt64 := JInt.wrap .i64 n
  let a ← reverseBang a (JInt.lit .i64 1) (JInt.wrap .i64 (l.val - s))
  let a ← reverseBang a (JInt.wrap .i64 (l.val - s + 1)) l
  reverseBang a (JInt.lit .i64 1) l

end JuliaLean.ArrayOps

namespace JuliaLean.ReduceCov.Indices


/-- `checkindex(Bool, inds, i)` for a unit range `inds` (`base/abstractarray.jl:751-760`,
`base/multidimensional.jl:916-917`): a real scalar is in `first(inds):last(inds)`; a
range is empty or has its first and last elements in bounds; a Bool range must
have `axes1(I) == inds`. -/
def checkIndex (inds : UR) (i : Ix) : Bool :=
  let inB (x : Int) : Bool := decide (inds.first ≤ x ∧ x ≤ inds.last)
  match i with
  | .int i => inB i.val
  | .integer _ i => inB i.val
  | .bool b => inB (bInt b)
  | .brange .. | .bsrange .. =>
    decide ((List.range i.elems.length).map (fun (k : Nat) => (k : Int) + 1) = inds.vals)
  | _ => match i.elems.head?, i.elems.getLast? with
    | some x, some y => inB x && inB y
    | _, _ => true

/-- `@boundscheck checkbounds(S, i)` for a one-dimensional `S`. -/
def checkbounds (S : UR) (i : Ix) : RJ Unit :=
  if checkIndex S.axes1 i then .ok () else .error boundsErr

end JuliaLean.ReduceCov.Indices

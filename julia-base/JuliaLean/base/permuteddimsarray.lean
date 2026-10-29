import JuliaLean.Core
import JuliaLean.base.array
import JuliaLean.base.abstractarray
import JuliaLean.base.indices
import JuliaLean.base.multidimensional

/-!
# Model of `base/permuteddimsarray.jl`

Typed model of the methods in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Abstract-array operations remain typed interfaces. Tuple dimensions and indices use `TupleN`;
mutating indexed writes run in the typed `MutationResult` stack over `array.MutationM`.
-/

namespace JuliaLean.base.permuteddimsarray

abbrev Index := JInt .i64
abbrev Axis := JuliaLean.base.multidimensional.Rng
abbrev CartesianIndex := JuliaLean.base.multidimensional.CI

def int (value : Int) : Index := JInt.wrap .i64 value

structure TupleN (α : Type) (N : Nat) where
  values : List α
  length_eq : values.length = N
  deriving Repr

structure PermutedDimsArray (T : Type) (A : Type) (N : Nat) where
  parent : A
  perm : TupleN Index N
  iperm : TupleN Index N

inductive Error where
  | errorException (message : String)
  | argumentError (message : String)
  | boundsError
  | methodError (message : String)
  deriving DecidableEq, Repr

abbrev Result (α : Type) := Except Error α
abbrev MutationResult (α : Type) := ExceptT Error (JuliaLean.base.array.MutationM α)

/-- Lift one array-heap operation into the constructor/indexing error layer. -/
def liftMutation {α β : Type} (operation : JuliaLean.base.array.MutationM α β) : MutationResult α β :=
  liftM operation

/-- The source's one-based inclusive ranges used by the two tiled assignment methods. -/
def indexRange (first last : Index) : List Index :=
  if first.val ≤ last.val then
    (List.range (last.val - first.val + 1).toNat).map fun offset => int (first.val + Int.ofNat offset)
  else []

def tileStarts (axis : Axis) : List Index :=
  (List.range ((axis.len + 7) / 8)).map fun block =>
    int (axis.start.val + Int.ofNat block * 8)

def minIndex (a b : Index) : Index := if a.val ≤ b.val then a else b

def tileEnd (start : Index) (axis : Axis) : Index :=
  minIndex (start + int 7) (JuliaLean.base.multidimensional.Rng.last axis)

/--
Julia source: base/permuteddimsarray.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline genperm(I::NTuple{N,Any}, perm::Dims{N}) where {N} = ntuple(d -> I[perm[d]], Val(N))
```
-/

def genpermTuple [Monad m] {α : Type} {N : Nat}
    (ntuple : (n : Nat) → (Index → m α) → m (TupleN α n))
    (getInput : TupleN α N → Index → m α) (getPerm : TupleN Index N → Index → m Index)
    (input : TupleN α N) (perm : TupleN Index N) : m (TupleN α N) := do
  ntuple N fun d => do
    let p ← getPerm perm d
    getInput input p

/--
Julia source: base/permuteddimsarray.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline genperm(I, perm::AbstractVector{Int}) = genperm(I, (perm...,))
```
-/

def genpermVector [Monad m] {α : Type} {N : Nat} {V : Type}
    (ntuple : (n : Nat) → (Index → m α) → m (TupleN α n))
    (getInput : TupleN α N → Index → m α) (getPerm : TupleN Index N → Index → m Index)
    (splat : V → m (TupleN Index N)) (input : TupleN α N) (perm : V) : m (TupleN α N) := do
  let tuple ← splat perm
  genpermTuple ntuple getInput getPerm input tuple

def toIntTuple {N : Nat} {t : IntTy} (xs : TupleN (JInt t) N) : TupleN Index N :=
  ⟨xs.values.map (fun x => JInt.wrap .i64 x.val), by simpa using xs.length_eq⟩

/--
Julia source: base/permuteddimsarray.jl:12-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function PermutedDimsArray{T,N,perm,iperm,AA}(data::AA) where {T,N,perm,iperm,AA<:AbstractArray}
        (isa(perm, NTuple{N,Int}) && isa(iperm, NTuple{N,Int})) || error("perm and iperm must both be NTuple{$N,Int}")
        isperm(perm) || throw(ArgumentError(string(perm, " is not a valid permutation of dimensions 1:", N)))
        all(d->iperm[perm[d]]==d, 1:N) || throw(ArgumentError(string(perm, " and ", iperm, " must be inverses")))
        new(data)
    end
```
-/

def innerConstructor [Monad m] [MonadExceptOf Error m] {T A : Type} {N : Nat}
    {t u : IntTy}
    (isperm : TupleN Index N → m Bool) (all : List Index → (Index → m Bool) → m Bool)
    (tupleGet : TupleN Index N → Index → m Index)
    (renderPerm : TupleN (JInt t) N → String) (renderIperm : TupleN (JInt u) N → String)
    (data : A) (perm : TupleN (JInt t) N) (iperm : TupleN (JInt u) N) : m (PermutedDimsArray T A N) := do
  if decide (t = .i64) && decide (u = .i64) then
    let permInt := toIntTuple perm
    let ipermInt := toIntTuple iperm
    if !(← isperm permInt) then
      throw (.argumentError (renderPerm perm ++ " is not a valid permutation of dimensions 1:" ++ toString N))
    let inverses ← all ((List.range N).map fun d => int (Int.ofNat d + 1)) fun d => do
      let p ← tupleGet permInt d
      let inverse ← tupleGet ipermInt p
      pure (inverse == d)
    if !inverses then
      throw (.argumentError (renderPerm perm ++ " and " ++ renderIperm iperm ++ " must be inverses"))
    pure ⟨data, permInt, ipermInt⟩
  else throw (.errorException ("perm and iperm must both be NTuple{" ++ toString N ++ ",Int}"))

/--
Julia source: base/permuteddimsarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@constprop :aggressive function PermutedDimsArray(data::AbstractArray{T,N}, perm) where {T,N}
    length(perm) == N || throw(ArgumentError(string(perm, " is not a valid permutation of dimensions 1:", N)))
    iperm = invperm(perm)
    PermutedDimsArray{T,N,(perm...,),(iperm...,),typeof(data)}(data)
end
```
-/

def constructPermutedDimsArray [Monad m] [MonadExceptOf Error m]
    {T A P IP : Type} {N : Nat} {t u : IntTy}
    (length : P → m Index) (invperm : P → m IP)
    (splatPerm : P → m (TupleN (JInt t) N))
    (splatIperm : IP → m (TupleN (JInt u) N))
    (isperm : TupleN Index N → m Bool) (all : List Index → (Index → m Bool) → m Bool)
    (tupleGet : TupleN Index N → Index → m Index)
    (showInput : P → String)
    (renderPerm : TupleN (JInt t) N → String) (renderIperm : TupleN (JInt u) N → String)
    (data : A) (perm : P) : m (PermutedDimsArray T A N) := do
  if (← length perm).val != (N : Int) then
    throw (.argumentError (showInput perm ++ " is not a valid permutation of dimensions 1:" ++ toString N))
  let inverse ← invperm perm
  let perm ← splatPerm perm
  let iperm ← splatIperm inverse
  innerConstructor isperm all tupleGet renderPerm renderIperm data perm iperm

/--
Julia source: base/permuteddimsarray.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.parent(A::PermutedDimsArray) = A.parent
```
-/

def parent {T A : Type} {N : Nat} (a : PermutedDimsArray T A N) : A := a.parent

/--
Julia source: base/permuteddimsarray.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.size(A::PermutedDimsArray{T,N,perm}) where {T,N,perm} = genperm(size(parent(A)), perm)
```
-/

def size [Monad m] {T A : Type} {N : Nat}
    (sizeParent : A → m (TupleN Index N))
    (ntuple : (n : Nat) → (Index → m Index) → m (TupleN Index n))
    (tupleGet : TupleN Index N → Index → m Index)
    (a : PermutedDimsArray T A N) : m (TupleN Index N) := do
  genpermTuple ntuple tupleGet tupleGet (← sizeParent a.parent) a.perm

/--
Julia source: base/permuteddimsarray.jl:50-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.axes(A::PermutedDimsArray{T,N,perm}) where {T,N,perm} = genperm(axes(parent(A)), perm)
```
-/

def axes [Monad m] {T A Ax : Type} {N : Nat}
    (axesParent : A → m (TupleN Ax N))
    (ntuple : (n : Nat) → (Index → m Ax) → m (TupleN Ax n))
    (tupleGet : TupleN Ax N → Index → m Ax) (permGet : TupleN Index N → Index → m Index)
    (a : PermutedDimsArray T A N) : m (TupleN Ax N) := do
  genpermTuple ntuple tupleGet permGet (← axesParent a.parent) a.perm

/--
Julia source: base/permuteddimsarray.jl:51-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.has_offset_axes(A::PermutedDimsArray) = Base.has_offset_axes(A.parent)
```
-/

def hasOffsetAxes [Monad m] {T A : Type} {N : Nat}
    (hasOffset : A → m Bool) (a : PermutedDimsArray T A N) : m Bool :=
  hasOffset a.parent

/--
Julia source: base/permuteddimsarray.jl:52-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.similar(A::PermutedDimsArray, T::Type, dims::Base.Dims) = similar(parent(A), T, dims)
```
-/

def similar [Monad m] {T A Ty D B : Type} {N : Nat}
    (similarParent : A → Ty → D → m B) (a : PermutedDimsArray T A N) (ty : Ty) (dims : D) : m B :=
  similarParent a.parent ty dims

/--
Julia source: base/permuteddimsarray.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.dataids(A::PermutedDimsArray) = Base.dataids(parent(A))
```
-/

def dataids [Monad m] {T A Ids : Type} {N : Nat}
    (dataidsParent : A → m Ids) (a : PermutedDimsArray T A N) : m Ids :=
  dataidsParent a.parent

/--
Julia source: base/permuteddimsarray.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.unaliascopy(A::PermutedDimsArray) = typeof(A)(Base.unaliascopy(parent(A)))
```
-/

def unaliascopy [Monad m] [MonadExceptOf Error m] {T A : Type} {N : Nat}
    (unaliasParent : A → m A)
    (isperm : TupleN Index N → m Bool) (all : List Index → (Index → m Bool) → m Bool)
    (tupleGet : TupleN Index N → Index → m Index) (renderTuple : TupleN Index N → String)
    (a : PermutedDimsArray T A N) : m (PermutedDimsArray T A N) := do
  let copiedParent ← unaliasParent a.parent
  innerConstructor isperm all tupleGet renderTuple renderTuple copiedParent a.perm a.iperm

structure Ptr (T : Type) where
  address : Nat

/--
Julia source: base/permuteddimsarray.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.cconvert(::Type{Ptr{T}}, A::PermutedDimsArray{T}) where {T} = Base.cconvert(Ptr{T}, parent(A))
```
-/

def cconvert [Monad m] {T A R : Type} {N : Nat}
    (convert : Type → A → m R) (a : PermutedDimsArray T A N) : m R :=
  convert (Ptr T) a.parent

/--
Julia source: base/permuteddimsarray.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.pointer(A::PermutedDimsArray, i::Integer) = throw(ArgumentError("pointer(A, i) is deliberately unsupported for PermutedDimsArray"))
```
-/

def pointer [Monad m] [MonadExceptOf Error m] {T A X R : Type} {N : Nat}
    (_a : PermutedDimsArray T A N) (_i : X) : m R :=
  throw (.argumentError "pointer(A, i) is deliberately unsupported for PermutedDimsArray")

/--
Julia source: base/permuteddimsarray.jl:64-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.strides(A::PermutedDimsArray{T,N,perm}) where {T,N,perm}
    s = strides(parent(A))
    ntuple(d->s[perm[d]], Val(N))
end
```
-/

def strides [Monad m] {T A : Type} {N : Nat}
    (stridesParent : A → m (TupleN Index N))
    (ntuple : (n : Nat) → (Index → m Index) → m (TupleN Index n))
    (tupleGet : TupleN Index N → Index → m Index)
    (a : PermutedDimsArray T A N) : m (TupleN Index N) := do
  let s ← stridesParent a.parent
  ntuple N fun d => do
    let p ← tupleGet a.perm d
    tupleGet s p

/--
Julia source: base/permuteddimsarray.jl:68-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.elsize(::Type{<:PermutedDimsArray{<:Any, <:Any, <:Any, <:Any, P}}) where {P} = Base.elsize(P)
```
-/

def elsize [Monad m] {T A R : Type} {N : Nat}
    (elsizeParent : Type → m R) (parentType : Type) (_a : PermutedDimsArray T A N) : m R :=
  elsizeParent parentType

/--
Julia source: base/permuteddimsarray.jl:70-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function Base.getindex(A::PermutedDimsArray{T,N,perm,iperm}, I::Vararg{Int,N}) where {T,N,perm,iperm}
    @boundscheck checkbounds(A, I...)
    @inbounds val = getindex(A.parent, genperm(I, iperm)...)
    val
end
```
-/

def getindex [Monad m] {T A V : Type} {N : Nat}
    (checkbounds : PermutedDimsArray T A N → TupleN Index N → m Unit)
    (getParent : A → TupleN Index N → m V)
    (ntuple : (n : Nat) → (Index → m Index) → m (TupleN Index n))
    (tupleGet : TupleN Index N → Index → m Index)
    (a : PermutedDimsArray T A N) (indices : TupleN Index N) : m V := do
  checkbounds a indices
  let parentIndices ← genpermTuple ntuple tupleGet tupleGet indices a.iperm
  let val ← getParent a.parent parentIndices
  pure val

/--
Julia source: base/permuteddimsarray.jl:75-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function Base.setindex!(A::PermutedDimsArray{T,N,perm,iperm}, val, I::Vararg{Int,N}) where {T,N,perm,iperm}
    @boundscheck checkbounds(A, I...)
    @inbounds setindex!(A.parent, val, genperm(I, iperm)...)
    val
end
```
-/

def setindex {T A V : Type} {N : Nat}
    (checkbounds : PermutedDimsArray T A N → TupleN Index N → MutationResult V Unit)
    (setParent : A → V → TupleN Index N → MutationResult V Unit)
    (ntuple : (n : Nat) → (Index → MutationResult V Index) → MutationResult V (TupleN Index n))
    (tupleGet : TupleN Index N → Index → MutationResult V Index)
    (a : PermutedDimsArray T A N) (value : V) (indices : TupleN Index N) : MutationResult V V := do
  checkbounds a indices
  let parentIndices ← genpermTuple ntuple tupleGet tupleGet indices a.iperm
  setParent a.parent value parentIndices
  pure value

/--
Julia source: base/permuteddimsarray.jl:81-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.isassigned(A::PermutedDimsArray{T,N,perm,iperm}, I::Vararg{Int,N}) where {T,N,perm,iperm}
    @boundscheck checkbounds(Bool, A, I...) || return false
    @inbounds x = isassigned(A.parent, genperm(I, iperm)...)
    x
end
```
-/

def isassigned [Monad m] {T A : Type} {N : Nat}
    (checkbounds : PermutedDimsArray T A N → TupleN Index N → m Bool)
    (isassignedParent : A → TupleN Index N → m Bool)
    (ntuple : (n : Nat) → (Index → m Index) → m (TupleN Index n))
    (tupleGet : TupleN Index N → Index → m Index)
    (a : PermutedDimsArray T A N) (indices : TupleN Index N) : m Bool := do
  if !(← checkbounds a indices) then return false
  let parentIndices ← genpermTuple ntuple tupleGet tupleGet indices a.iperm
  let x ← isassignedParent a.parent parentIndices
  pure x

/--
Julia source: base/permuteddimsarray.jl:198-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function permutedims(A::AbstractArray, perm)
    dest = similar(A, genperm(axes(A), perm))
    permutedims!(dest, A, perm)
end
```
-/

def permutedimsArray [Monad m] {A B P Ax D : Type} {N : Nat}
    (axes : A → m (TupleN Ax N))
    (genperm : TupleN Ax N → P → m D)
    (similar : A → D → m B) (permutedimsBang : B → A → P → m B)
    (a : A) (perm : P) : m B := do
  let dims ← genperm (← axes a) perm
  let dest ← similar a dims
  permutedimsBang dest a perm

/--
Julia source: base/permuteddimsarray.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
permutedims(A::AbstractMatrix) = permutedims(A, (2,1))
```
-/

def permutedimsMatrix [Monad m] {A B : Type}
    (permutedims : A → TupleN Index 2 → m B) (a : A) : m B := do
  let swap : TupleN Index 2 := ⟨[int 2, int 1], by decide⟩
  permutedims a swap

/--
Julia source: base/permuteddimsarray.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
permutedims(v::AbstractVector) = reshape(v, (1, length(v)))
```
-/

def permutedimsVector [Monad m] {A B : Type}
    (length : A → m Index) (reshape : A → TupleN Index 2 → m B) (v : A) : m B := do
  let n ← length v
  let row : TupleN Index 2 := ⟨[int 1, n], by simp⟩
  reshape v row

/--
Julia source: base/permuteddimsarray.jl:286-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function permutedims!(dest, src::AbstractArray, perm)
    Base.checkdims_perm(axes(dest), axes(src), perm)
    P = PermutedDimsArray(dest, invperm(perm))
    _copy!(P, src)
    return dest
end
```
-/

def permutedimsBang [Monad m] {D S P IP T Ax : Type} {N : Nat}
    (axesDest : D → m (TupleN Ax N)) (axesSrc : S → m (TupleN Ax N))
    (checkdimsPerm : TupleN Ax N → TupleN Ax N → P → m Unit)
    (invperm : P → m IP) (construct : D → IP → m (PermutedDimsArray T D N))
    (copy : PermutedDimsArray T D N → S → m (PermutedDimsArray T D N))
    (dest : D) (src : S) (perm : P) : m D := do
  let destinationAxes ← axesDest dest
  let sourceAxes ← axesSrc src
  checkdimsPerm destinationAxes sourceAxes perm
  let inverse ← invperm perm
  let target ← construct dest inverse
  let _ ← copy target src
  pure dest

/--
Julia source: base/permuteddimsarray.jl:293-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.copyto!(dest::PermutedDimsArray{<:Any,N}, src::AbstractArray{<:Any,N}) where {N}
    isempty(src) && return dest
    checkbounds(dest, axes(src)...)
    src′ = Base.unalias(dest, src)
    _copy!(dest, src′)
end
```
-/

def copytoPermuted [Monad m] {T D S Ax : Type} {N : Nat}
    (isempty : S → m Bool) (axesSrc : S → m (TupleN Ax N))
    (checkbounds : PermutedDimsArray T D N → TupleN Ax N → m Unit)
    (unalias : PermutedDimsArray T D N → S → m S)
    (copy : PermutedDimsArray T D N → S → m (PermutedDimsArray T D N))
    (dest : PermutedDimsArray T D N) (src : S) : m (PermutedDimsArray T D N) := do
  if ← isempty src then return dest
  checkbounds dest (← axesSrc src)
  let srcPrime ← unalias dest src
  copy dest srcPrime

def fixedPrefix [Monad m] {N : Nat}
    (tupleGet : TupleN Index N → Index → m Index) (perm : TupleN Index N)
    (limit : Nat) (d : Nat) : m Nat := do
  if h : d < limit then
    let p ← tupleGet perm (int ((d : Int) + 1))
    if p.val == (d : Int) + 1 then fixedPrefix tupleGet perm limit (d + 1) else pure d
  else pure d
termination_by limit - d
decreasing_by omega

/--
Julia source: base/permuteddimsarray.jl:300-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _copy!(P::PermutedDimsArray{T,N,perm}, src) where {T,N,perm}
    # If dest/src are "close to dense," then it pays to be cache-friendly.
    # Determine the first permuted dimension
    d = 0  # d+1 will hold the first permuted dimension of src
    while d < ndims(src) && perm[d+1] == d+1
        d += 1
    end
    if d == ndims(src)
        copyto!(parent(P), src) # it's not permuted
    else
        R1 = CartesianIndices(axes(src)[1:d])
        d1 = findfirst(isequal(d+1), perm)::Int  # first permuted dim of dest
        R2 = CartesianIndices(axes(src)[d+2:d1-1])
        R3 = CartesianIndices(axes(src)[d1+1:end])
        _permutedims!(P, src, R1, R2, R3, d+1, d1)
    end
    return P
end
```
-/

def copyView {T A S Ax : Type} {N : Nat}
    (rank : S → Nat) (tupleGet : TupleN Index N → Index → MutationResult T Index)
    (axes : S → MutationResult T (TupleN Ax N))
    (sliceAxes : TupleN Ax N → Index → Index → MutationResult T (List Ax))
    (cartesianIndices : List Ax → MutationResult T (List CartesianIndex))
    (findfirst : Index → TupleN Index N → MutationResult T Index)
    (copyParent : A → S → MutationResult T Unit)
    (kernelZero : PermutedDimsArray T A N → S → List CartesianIndex → List CartesianIndex → List CartesianIndex → Index → Index → MutationResult T (PermutedDimsArray T A N))
    (kernelGeneral : PermutedDimsArray T A N → S → List CartesianIndex → List CartesianIndex → List CartesianIndex → Index → Index → MutationResult T (PermutedDimsArray T A N))
    (a : PermutedDimsArray T A N) (src : S) : MutationResult T (PermutedDimsArray T A N) := do
  let d ← fixedPrefix tupleGet a.perm (rank src) 0
  if d == rank src then
    copyParent a.parent src
  else
    let axes1 ← axes src
    let r1Axes ← sliceAxes axes1 (int 1) (int (Int.ofNat d))
    let r1 ← cartesianIndices r1Axes
    let d1 ← findfirst (int ((d : Int) + 1)) a.perm
    let axes2 ← axes src
    let r2Axes ← sliceAxes axes2 (int ((d : Int) + 2)) (d1 - int 1)
    let r2 ← cartesianIndices r2Axes
    let axes3 ← axes src
    let r3Axes ← sliceAxes axes3 (d1 + int 1) (int (Int.ofNat (rank src)))
    let r3 ← cartesianIndices r3Axes
    if d == 0 then
      let _ ← kernelZero a src r1 r2 r3 (int 1) d1
      pure ()
    else
      let _ ← kernelGeneral a src r1 r2 r3 (int ((d : Int) + 1)) d1
      pure ()
  pure a

/-- The eight-wide loop starts used in both tiled copy kernels. -/
def tileStartsAxis (axis : Axis) : List Index := tileStarts axis

/-- The source range `start:min(start+7,last(axis))` used by both tiled kernels. -/
def tileValues (start : Index) (axis : Axis) : List Index :=
  indexRange start (tileEnd start axis)

/--
Julia source: base/permuteddimsarray.jl:319-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _permutedims!(P::PermutedDimsArray, src, R1::CartesianIndices{0}, R2, R3, ds, dp)
    ip, is = axes(src, dp), axes(src, ds)
    for jo in first(ip):8:last(ip), io in first(is):8:last(is)
        for I3 in R3, I2 in R2
            for j in jo:min(jo+7, last(ip))
                for i in io:min(io+7, last(is))
                    @inbounds P[i, I2, j, I3] = src[i, I2, j, I3]
                end
            end
        end
    end
    P
end
```
-/

def permutedimsZero {T A S V : Type} {N : Nat}
    (axesDim : S → Index → MutationResult T Axis)
    (getSource : S → TupleN Index N → MutationResult T V)
    (setTarget : PermutedDimsArray T A N → V → TupleN Index N → MutationResult T V)
    (tupleFromList : List Index → MutationResult T (TupleN Index N))
    (p : PermutedDimsArray T A N) (src : S) (_r1 : List CartesianIndex)
    (r2 r3 : List CartesianIndex) (ds dp : Index) : MutationResult T (PermutedDimsArray T A N) := do
  let ip ← axesDim src dp
  let is ← axesDim src ds
  for jo in tileStartsAxis ip do
    for io in tileStartsAxis is do
      for I3 in r3 do
        for I2 in r2 do
          for j in tileValues jo ip do
            for i in tileValues io is do
              let indices ← tupleFromList ([i] ++ I2 ++ [j] ++ I3)
              let value ← getSource src indices
              let _ ← setTarget p value indices
              pure ()
  pure p

/--
Julia source: base/permuteddimsarray.jl:333-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _permutedims!(P::PermutedDimsArray, src, R1, R2, R3, ds, dp)
    ip, is = axes(src, dp), axes(src, ds)
    for jo in first(ip):8:last(ip), io in first(is):8:last(is)
        for I3 in R3, I2 in R2
            for j in jo:min(jo+7, last(ip))
                for i in io:min(io+7, last(is))
                    for I1 in R1
                        @inbounds P[I1, i, I2, j, I3] = src[I1, i, I2, j, I3]
                    end
                end
            end
        end
    end
    P
end
```
-/

def permutedimsGeneral {T A S V : Type} {N : Nat}
    (axesDim : S → Index → MutationResult T Axis)
    (getSource : S → TupleN Index N → MutationResult T V)
    (setTarget : PermutedDimsArray T A N → V → TupleN Index N → MutationResult T V)
    (tupleFromList : List Index → MutationResult T (TupleN Index N))
    (p : PermutedDimsArray T A N) (src : S)
    (r1 r2 r3 : List CartesianIndex) (ds dp : Index) : MutationResult T (PermutedDimsArray T A N) := do
  let ip ← axesDim src dp
  let is ← axesDim src ds
  for jo in tileStartsAxis ip do
    for io in tileStartsAxis is do
      for I3 in r3 do
        for I2 in r2 do
          for j in tileValues jo ip do
            for i in tileValues io is do
              for I1 in r1 do
                let indices ← tupleFromList (I1 ++ [i] ++ I2 ++ [j] ++ I3)
                let value ← getSource src indices
                let _ ← setTarget p value indices
                pure ()
  pure p

class CommutativeOp (Op : Type) : Prop
class ProductOp (Op : Type) : Prop
class RealOrComplex (T : Type) : Prop

/--
Julia source: base/permuteddimsarray.jl:351-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base._mapreduce_dim(f, op::CommutativeOps, init::Base._InitialValue, A::PermutedDimsArray, dims::Colon)
    Base._mapreduce_dim(f, op, init, parent(A), dims)
end
```
-/

def mapreduceDimCommutative [Monad m]
    {T A F Op Init D R : Type} {N : Nat} [CommutativeOp Op]
    (mapreduceDim : F → Op → Init → A → D → m R)
    (f : F) (op : Op) (init : Init) (a : PermutedDimsArray T A N) (dims : D) : m R :=
  mapreduceDim f op init a.parent dims

/--
Julia source: base/permuteddimsarray.jl:354-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base._mapreduce_dim(f::typeof(identity), op::Union{typeof(Base.mul_prod),typeof(*)}, init::Base._InitialValue, A::PermutedDimsArray{<:Union{Real,Complex}}, dims::Colon)
    Base._mapreduce_dim(f, op, init, parent(A), dims)
end
```
-/

def mapreduceDimProduct [Monad m]
    {T A Op Init D R : Type} {N : Nat} [ProductOp Op] [RealOrComplex T]
    (mapreduceDim : (T → T) → Op → Init → A → D → m R)
    (f : T → T) (_identity : f = id) (op : Op) (init : Init)
    (a : PermutedDimsArray T A N) (dims : D) : m R :=
  mapreduceDim f op init a.parent dims

/--
Julia source: base/permuteddimsarray.jl:358-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.mapreducedim!(f, op::CommutativeOps, B::AbstractArray{T,N}, A::PermutedDimsArray{S,N,perm,iperm}) where {T,S,N,perm,iperm}
    C = PermutedDimsArray{T,N,iperm,perm,typeof(B)}(B) # make the inverse permutation for the output
    Base.mapreducedim!(f, op, C, parent(A))
    B
end
```
-/

def mapreducedimCommutative [Monad m] [MonadExceptOf Error m]
    {T A B F Op : Type} {N : Nat} [CommutativeOp Op]
    (isperm : TupleN Index N → m Bool) (all : List Index → (Index → m Bool) → m Bool)
    (tupleGet : TupleN Index N → Index → m Index) (renderTuple : TupleN Index N → String)
    (mapreducedim : F → Op → PermutedDimsArray T B N → A → m Unit)
    (f : F) (op : Op) (b : B) (a : PermutedDimsArray T A N) : m B := do
  let c ← innerConstructor isperm all tupleGet renderTuple renderTuple b a.iperm a.perm
  let _ ← mapreducedim f op c (parent a)
  pure b

/--
Julia source: base/permuteddimsarray.jl:363-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.mapreducedim!(f::typeof(identity), op::Union{typeof(Base.mul_prod),typeof(*)}, B::AbstractArray{T,N}, A::PermutedDimsArray{<:Union{Real,Complex},N,perm,iperm}) where {T,N,perm,iperm}
    C = PermutedDimsArray{T,N,iperm,perm,typeof(B)}(B) # make the inverse permutation for the output
    Base.mapreducedim!(f, op, C, parent(A))
    B
end
```
-/

def mapreducedimProduct [Monad m] [MonadExceptOf Error m]
    {T A B Op : Type} {N : Nat} [ProductOp Op] [RealOrComplex T]
    (isperm : TupleN Index N → m Bool) (all : List Index → (Index → m Bool) → m Bool)
    (tupleGet : TupleN Index N → Index → m Index) (renderTuple : TupleN Index N → String)
    (mapreducedim : (T → T) → Op → PermutedDimsArray T B N → A → m Unit)
    (f : T → T) (_identity : f = id) (op : Op) (b : B) (a : PermutedDimsArray T A N) : m B := do
  let c ← innerConstructor isperm all tupleGet renderTuple renderTuple b a.iperm a.perm
  let _ ← mapreducedim f op c (parent a)
  pure b

/--
Julia source: base/permuteddimsarray.jl:369-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.showarg(io::IO, A::PermutedDimsArray{T,N,perm}, toplevel) where {T,N,perm}
    print(io, "PermutedDimsArray(")
    Base.showarg(io, parent(A), false)
    print(io, ", ", perm, ')')
    toplevel && print(io, " with eltype ", eltype(A))
    return nothing
end
```
-/

def showarg [Monad m] {T A IO : Type} {N : Nat}
    (print : IO → String → m IO) (showParent : IO → A → Bool → m IO)
    (renderPerm : TupleN Index N → String)
    (showEltype : IO → PermutedDimsArray T A N → m IO)
    (io : IO) (a : PermutedDimsArray T A N) (toplevel : Bool) : m Unit := do
  let io ← print io "PermutedDimsArray("
  let io ← showParent io a.parent false
  let io ← print io (", " ++ renderPerm a.perm ++ ")")
  if toplevel then
    let io ← print io " with eltype "
    let _ ← showEltype io a
    pure ()
  else pure ()

end JuliaLean.base.permuteddimsarray

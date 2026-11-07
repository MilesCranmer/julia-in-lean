import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.reduce

/-!
# Model of `base/combinatorics.jl`

Typed models for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform
(`Int === Int64`). Each translated method's docstring carries its verbatim source, and each body
follows its source checks, loop order, and error behavior.

* Fixed-width integer values are `JInt t`; factorial tables retain their Julia integer types.
* Collection access, mutation, indexing, and mixed-number arithmetic use explicit interfaces
  that preserve Julia dispatch and conversion behavior.
-/

namespace JuliaLean.base.combinatorics

open JuliaLean

inductive CombinatoricsError where
  | assertionError (message : String)
  deriving Repr, DecidableEq

structure FactorialOps (N F : Type) where
  toInt : N → Jl (JInt .i64)
  one : N → N
  oftype : N → F → Jl N

structure FactorialNarrowOps (N : Type) where
  toInt64 : N → Jl (JInt .i64)

structure PermutationOps (A T : Type) where
  length : A → Nat
  elements : A → List T
  inRange : T → Nat → Bool
  index : T → Nat

structure InverseVectorOps (A T : Type) where
  requireOneBased : A → Jl Unit
  length : A → Nat
  elements : A → List T
  zero : T
  isZero : T → Bool
  validPosition : T → Nat → Bool
  position : T → Nat
  fromIndex : Nat → Jl T
  rebuild : A → List T → Jl A

structure InPlacePermuteOps (A P : Type) where
  gather : A → P → A
  broadcastAssign : A → A → A
  indexedAssign : A → P → A → A

structure MatrixMutationOps (A I E : Type) where
  rows : A → List I
  columns : A → List I
  hasRow : List I → I → Bool
  hasColumn : List I → I → Bool
  equalIndex : I → I → Bool
  get : A → I → I → Jl E
  set : A → I → I → E → Jl A

structure PermutationBufferOps (P N I : Type) where
  length : P → Nat
  get : P → Nat → Jl N
  set : P → Nat → N → Jl P
  zero : N
  isZero : N → Bool
  asIndex : N → Jl I
  asMachineIndex : Nat → Jl I
  vectorIndex : N → Jl Nat
  equalToNat : N → Nat → Bool
  negate : N → Jl N
  isPositive : N → Bool
  isNegative : N → Bool
  findNextNonzero : (N → Bool) → P → Nat → Jl Nat
  negateAll : P → Jl P

inductive NextprodPhase where
  | check
  | carry
  | grow
  deriving DecidableEq

structure NextprodState (A X M I W : Type) where
  factors : A
  target : X
  powers : M
  size : Nat
  counters : List I
  product : W
  best : W
  carry : Nat
  phase : NextprodPhase

structure NextprodOps (A X F M I W : Type) where
  exceedsIntMax : X → Bool
  length : A → Nat
  showTarget : X → String
  mapNextPow : A → X → Jl M
  powerAt : M → Nat → Jl I
  powerLastIndex : M → Jl Nat
  factorAt : A → Nat → Jl F
  oneCounter : I
  storePower : I → Jl I
  toWide : I → Jl W
  divideWide : W → I → Jl W
  multiplyWideFactor : W → F → Jl W
  multiplyCounterFactor : I → F → Jl I
  counterLT : I → I → Bool
  counterGT : I → I → Bool
  counterLessWide : I → W → Bool
  wideLT : W → W → Bool
  wideGEReal : W → X → Bool
  wideLTReal : W → X → Bool
  wideToInt : W → Jl (JInt .i64)
  counterToInt : I → Jl (JInt .i64)

private def vectorGet {I : Type} (values : List I) (index : Nat) : Jl I :=
  match values, index with
  | [], _ => .error .boundsError
  | value :: _, 1 => .ok value
  | _ :: rest, Nat.succ i => vectorGet rest i
  | _, 0 => .error .boundsError
termination_by values.length

private def vectorSet {I : Type} (values : List I) (index : Nat) (value : I) : Jl (List I) :=
  match values, index with
  | [], _ => .error .boundsError
  | _ :: rest, 1 => .ok (value :: rest)
  | current :: rest, Nat.succ i => do
      let rest ← vectorSet rest i value
      pure (current :: rest)
  | _, 0 => .error .boundsError
termination_by values.length

private def factorialTable {t : IntTy} (size : Nat) : List (JInt t) :=
  if size == 0 then [] else
    let seed := JInt.lit t 1
    let (_, reversed) := List.foldl (fun (state : JInt t × List (JInt t)) index =>
      let next := state.1 * JInt.lit t (Int.ofNat (index + 2))
      (next, next :: state.2)) (seed, [seed]) (List.range (size - 1))
    reversed.reverse

private def listGetD {α : Type} (values : List α) (index : Nat) (default : α) : α :=
  match values, index with
  | [], _ => default
  | value :: _, 0 => value
  | _ :: rest, Nat.succ i => listGetD rest i default
termination_by values.length

private def listSet {α : Type} (values : List α) (index : Nat) (value : α) : List α :=
  match values, index with
  | [], _ => []
  | _ :: rest, 0 => value :: rest
  | current :: rest, Nat.succ i => current :: listSet rest i value
termination_by values.length

private def factorialField {F : Type} : List F → Nat → Option F
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, Nat.succ i => factorialField rest i

private def ispermLoop {T : Type} (inRange : T → Nat → Bool) (index : T → Nat)
    (n : Nat) : List T → List Bool → Bool
  | [], _ => true
  | value :: rest, used =>
      if inRange value n then
        let slot := index value - 1
        if listGetD used slot false then false
        else ispermLoop inRange index n rest (listSet used slot true)
      else false
termination_by values => values.length

/--
Julia source: base/combinatorics.jl:1-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

# Factorials

const _fact_table64 = let _fact_table64 = Vector{Int64}(undef, 20)
    _fact_table64[1] = 1
    for n in 2:20
        _fact_table64[n] = _fact_table64[n-1] * n
    end
    Tuple(_fact_table64)
end
```
-/
def factorial_table64 : List (JInt .i64) := factorialTable 20

/--
Julia source: base/combinatorics.jl:12-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

const _fact_table128 = let _fact_table128 = Vector{UInt128}(undef, 34)
    _fact_table128[1] = 1
    for n in 2:34
        _fact_table128[n] = _fact_table128[n-1] * n
    end
    Tuple(_fact_table128)
end
```
-/
def factorial_table128 : List (JInt .u128) := factorialTable 34

/--
Julia source: base/combinatorics.jl:20-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function factorial_lookup(
    n::Union{Checked.SignedInt,Checked.UnsignedInt},
    table::Union{NTuple{20,Int64},NTuple{34,UInt128}}, lim::Int)
    idx = Int(n)
    idx < 0 && throw(DomainError(n, "`n` must not be negative."))
    idx > lim && throw(OverflowError(lazy"$n is too large to look up in the table; consider using `factorial(big($n))` instead"))
    idx == 0 && return one(n)
    f = getfield(table, idx)
    return oftype(n, f)
end
```
-/
def factorial_lookup {N F : Type} (ops : FactorialOps N F) (n : N)
    (table : List F) (limit : Nat) : Jl N := do
  let index ← ops.toInt n
  if index.val < 0 then throw (.domainError "`n` must not be negative.")
  if index.val > Int.ofNat limit then throw (.overflowError "factorial input exceeds lookup limit")
  if index.val == 0 then return ops.one n
  match factorialField table (index.val.toNat - 1) with
  | none => throw .boundsError
  | some value => ops.oftype n value

/--
Julia source: base/combinatorics.jl:31-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

factorial(n::Int128) = factorial_lookup(n, _fact_table128, 33)
```
-/
def factorial_Int128 (ops : FactorialOps (JInt .i128) (JInt .u128))
    (n : JInt .i128) : Jl (JInt .i128) :=
  factorial_lookup ops n factorial_table128 33

/--
Julia source: base/combinatorics.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
factorial(n::UInt128) = factorial_lookup(n, _fact_table128, 34)
```
-/
def factorial_UInt128 (ops : FactorialOps (JInt .u128) (JInt .u128))
    (n : JInt .u128) : Jl (JInt .u128) :=
  factorial_lookup ops n factorial_table128 34

/--
Julia source: base/combinatorics.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
factorial(n::Union{Int64,UInt64}) = factorial_lookup(n, _fact_table64, 20)
```
-/
def factorial_Int64OrUInt64 {t : IntTy} (_ht : t = .i64 ∨ t = .u64)
    (ops : FactorialOps (JInt t) (JInt .i64)) (n : JInt t) : Jl (JInt t) :=
  factorial_lookup ops n factorial_table64 20

/--
Julia source: base/combinatorics.jl:35-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

if Int === Int32
    factorial(n::Union{Int8,UInt8,Int16,UInt16}) = factorial(Int32(n))
    factorial(n::Union{Int32,UInt32}) = factorial_lookup(n, _fact_table64, 12)
else
    factorial(n::Union{Int8,UInt8,Int16,UInt16,Int32,UInt32}) = factorial(Int64(n))
end
```
-/
def factorial_small_64bit {t : IntTy} (ops : FactorialNarrowOps (JInt t))
    (factorialInt64 : JInt .i64 → Jl (JInt .i64)) (n : JInt t) : Jl (JInt .i64) := do
  let widened ← ops.toInt64 n
  factorialInt64 widened

/--
Julia source: base/combinatorics.jl:42-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia


# Basic functions for working with permutations

@inline function _foldoneto(op, acc, ::Val{N}) where N
    @assert N::Integer > 0 "N must be positive"
    if @generated
        quote
            acc_0 = acc
            Base.Cartesian.@nexprs $N i -> acc_{i} = op(acc_{i-1}, i)
            return $(Symbol(:acc_, N))
        end
    else
        for i in 1:N
            acc = op(acc, i)
        end
        return acc
    end
end
```
-/
def _foldoneto {A : Type} (op : A → Nat → A) (acc : A) (count : Int) :
    Except CombinatoricsError A :=
  if count ≤ 0 then .error (.assertionError "N must be positive")
  else .ok (List.foldl (fun value i => op value (i + 1)) acc (List.range count.toNat))

/--
Julia source: base/combinatorics.jl:77-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function _isperm(A)
    n = length(A)
    used = falses(n)
    for a in A
        (0 < a <= n) && (used[a] ⊻= true) || return false
    end
    true
end
```
-/
def _isperm {A T : Type} (ops : PermutationOps A T) (a : A) : Bool :=
  let n := ops.length a
  ispermLoop ops.inRange ops.index n (ops.elements a) (List.replicate n false)

/--
Julia source: base/combinatorics.jl:61-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    isperm(v)::Bool

Return `true` if `v` is a valid permutation.

# Examples
```jldoctest
julia> isperm([1; 2])
true

julia> isperm([1; 3])
false
```
"""
isperm(A) = _isperm(A)
````
-/
def isperm {A T : Type} (ops : PermutationOps A T) (a : A) : Bool :=
  _isperm ops a

/--
Julia source: base/combinatorics.jl:86-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

isperm(p::Tuple{}) = true
```
-/
def isperm_Tuple0 : Bool := true

/--
Julia source: base/combinatorics.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isperm(p::Tuple{Int}) = p[1] == 1
```
-/
def isperm_Tuple1 (value : JInt .i64) : Bool := value.val == 1

/--
Julia source: base/combinatorics.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isperm(p::Tuple{Int,Int}) = ((p[1] == 1) & (p[2] == 2)) | ((p[1] == 2) & (p[2] == 1))
```
-/
def isperm_Tuple2 (first second : JInt .i64) : Bool :=
  ((first.val == 1) && (second.val == 2)) || ((first.val == 2) && (second.val == 1))

/--
Julia source: base/combinatorics.jl:90-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function isperm(P::Tuple)
    valn = Val(length(P))
    _foldoneto(true, valn) do b,i
        s = _foldoneto(false, valn) do s, j
            s || P[j]==i
        end
        b&s
    end
end
```
-/
def isperm_Tuple {T : Type} (equalTo : T → Nat → Bool) (values : List T) : Bool :=
  List.foldl (fun all index => all && values.any (fun value => equalTo value (index + 1)))
    true (List.range values.length)

/--
Julia source: base/combinatorics.jl:100-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

isperm(P::Any32) = _isperm(P)
```
-/
def isperm_Any32 {A T : Type} (ops : PermutationOps A T) (values : A) : Bool :=
  _isperm ops values

inductive PermuteColumnsState (A P N I : Type) where
  | outer (array : A) (permutation : P) (count start : Nat)
  | cycle (array : A) (permutation : P) (count start ptrVector : Nat)
      (ptr : I) (next : N) (nextVector : Nat)

private def permuteColumnsStep {A P N I : Type} (ops : PermutationBufferOps P N I)
    (swapColumns : A → I → I → Jl A) (size : Nat)
    (state : PermuteColumnsState A P N I) : Jl (Sum (A × P) (PermuteColumnsState A P N I)) := do
  match state with
  | .outer array permutation count start =>
      if count ≥ size then return .inl (array, permutation)
      let ptrVector ← ops.findNextNonzero (fun value => !ops.isZero value) permutation (start + 1)
      let next ← ops.get permutation ptrVector
      let nextVector ← ops.vectorIndex next
      let ptr ← ops.asMachineIndex ptrVector
      return .inr (.cycle array permutation (count + 1) ptrVector ptrVector ptr next nextVector)
  | .cycle array permutation count start ptrVector ptr next nextVector =>
      if ops.equalToNat next start then
        let permutation ← ops.set permutation ptrVector ops.zero
        return .inr (.outer array permutation count start)
      let nextArg ← ops.asIndex next
      let array ← swapColumns array ptr nextArg
      let permutation ← ops.set permutation ptrVector ops.zero
      let following ← ops.get permutation nextVector
      let followingVector ← ops.vectorIndex following
      return .inr (.cycle array permutation (count + 1) start nextVector nextArg following followingVector)

inductive PermuteVectorState (A P N I : Type) where
  | outer (array : A) (permutation : P) (i : Nat)
  | cycle (array : A) (permutation : P) (i vectorIndex : Nat) (current j : I)

private def permuteVectorStep {A P N I : Type} (ops : PermutationBufferOps P N I)
    (swap : A → I → I → Jl A) (size : Nat) (state : PermuteVectorState A P N I) :
    Jl (Sum (A × P) (PermuteVectorState A P N I)) := do
  match state with
  | .outer array permutation i =>
      if i > size then return .inl (array, permutation)
      let value ← ops.get permutation i
      if ops.isPositive value then return .inr (.outer array permutation (i + 1))
      let negated ← ops.negate value
      let permutation ← ops.set permutation i negated
      let vectorIndex ← ops.vectorIndex negated
      let current ← ops.asIndex negated
      let j ← ops.asMachineIndex i
      return .inr (.cycle array permutation i vectorIndex current j)
  | .cycle array permutation i vectorIndex current j =>
      let value ← ops.get permutation vectorIndex
      if !ops.isNegative value then return .inr (.outer array permutation (i + 1))
      let array ← swap array current j
      let value ← ops.get permutation vectorIndex
      let negated ← ops.negate value
      let permutation ← ops.set permutation vectorIndex negated
      let nextVector ← ops.vectorIndex negated
      let nextCurrent ← ops.asIndex negated
      return .inr (.cycle array permutation i nextVector nextCurrent current)

inductive InvPermuteVectorState (A P N I : Type) where
  | outer (array : A) (permutation : P) (i : Nat)
  | cycle (array : A) (permutation : P) (i vectorIndex : Nat) (value : N) (j : I)

private def invPermuteVectorStep {A P N I : Type} (ops : PermutationBufferOps P N I)
    (swap : A → I → I → Jl A) (size : Nat) (state : InvPermuteVectorState A P N I) :
    Jl (Sum (A × P) (InvPermuteVectorState A P N I)) := do
  match state with
  | .outer array permutation i =>
      if i > size then return .inl (array, permutation)
      let value ← ops.get permutation i
      if ops.isPositive value then return .inr (.outer array permutation (i + 1))
      let negated ← ops.negate value
      let permutation ← ops.set permutation i negated
      let vectorIndex ← ops.vectorIndex negated
      let j ← ops.asIndex negated
      return .inr (.cycle array permutation i vectorIndex negated j)
  | .cycle array permutation i vectorIndex value j =>
      if ops.equalToNat value i then return .inr (.outer array permutation (i + 1))
      let machineI ← ops.asMachineIndex i
      let array ← swap array j machineI
      let current ← ops.get permutation vectorIndex
      let negated ← ops.negate current
      let permutation ← ops.set permutation vectorIndex negated
      let nextVector ← ops.vectorIndex negated
      let nextArg ← ops.asIndex negated
      return .inr (.cycle array permutation i nextVector negated nextArg)

/--
Julia source: base/combinatorics.jl:102-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# swap columns i and j of a, in-place
function swapcols!(a::AbstractMatrix, i, j)
    i == j && return
    cols = axes(a,2)
    @boundscheck i in cols || throw(BoundsError(a, (:,i)))
    @boundscheck j in cols || throw(BoundsError(a, (:,j)))
    for k in axes(a,1)
        @inbounds a[k,i],a[k,j] = a[k,j],a[k,i]
    end
end
```
-/
def swapcols! {A I E : Type} (ops : MatrixMutationOps A I E)
    (a : A) (i j : I) : Jl A := do
  if ops.equalIndex i j then return a
  let columns := ops.columns a
  if !ops.hasColumn columns i then throw .boundsError
  if !ops.hasColumn columns j then throw .boundsError
  (ops.rows a).foldlM (fun matrix row => do
    let right ← ops.get matrix row j
    let left ← ops.get matrix row i
    let matrix ← ops.set matrix row i right
    ops.set matrix row j left) a

/--
Julia source: base/combinatorics.jl:113-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# swap rows i and j of a, in-place
function swaprows!(a::AbstractMatrix, i, j)
    i == j && return
    rows = axes(a,1)
    @boundscheck i in rows || throw(BoundsError(a, (:,i)))
    @boundscheck j in rows || throw(BoundsError(a, (:,j)))
    for k in axes(a,2)
        @inbounds a[i,k],a[j,k] = a[j,k],a[i,k]
    end
end
```
-/
def swaprows! {A I E : Type} (ops : MatrixMutationOps A I E)
    (a : A) (i j : I) : Jl A := do
  if ops.equalIndex i j then return a
  let rows := ops.rows a
  if !ops.hasRow rows i then throw .boundsError
  if !ops.hasRow rows j then throw .boundsError
  (ops.columns a).foldlM (fun matrix column => do
    let right ← ops.get matrix j column
    let left ← ops.get matrix i column
    let matrix ← ops.set matrix i column right
    ops.set matrix j column left) a

/--
Julia source: base/combinatorics.jl:124-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# like permute!! applied to each column of a, in-place in a (overwriting p).
function permutecols!!(a::AbstractMatrix, p::AbstractVector{<:Integer})
    require_one_based_indexing(a, p)
    count = 0
    start = 0
    while count < length(p)
        ptr = start = findnext(!iszero, p, start+1)::Int
        next = p[start]
        count += 1
        while next != start
            swapcols!(a, ptr, next)
            p[ptr] = 0
            ptr = next
            next = p[next]
            count += 1
        end
        p[ptr] = 0
    end
    a
end
```
-/
def permutecols!! {A P N I : Type} (ops : PermutationBufferOps P N I)
    (requireOneBased : A → P → Jl Unit) (swapColumns : A → I → I → Jl A)
    (a : A) (p : P) : Option (Jl (A × P)) :=
  match requireOneBased a p with
  | .error e => some (.error e)
  | .ok _ =>
      let state := PermuteColumnsState.outer a p 0 0
      JuliaLean.base.reduce.whileLoop (permuteColumnsStep ops swapColumns (ops.length p)) state

/--
Julia source: base/combinatorics.jl:151-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _permute!(a::AbstractMatrix, p::AbstractVector{<:Integer}, swapfun!::F) where {F}
    require_one_based_indexing(a, p)
    p .= .-p
    for i in 1:length(p)
        p[i] > 0 && continue
        j = i
        in = p[j] = -p[j]
        while p[in] < 0
            swapfun!(a, in, j)
            j = in
            in = p[in] = -p[in]
        end
    end
    a
end
```
-/
def _permute! {A P N I : Type} (ops : PermutationBufferOps P N I)
    (requireOneBased : A → P → Jl Unit) (swap : A → I → I → Jl A)
    (a : A) (p : P) : Option (Jl (A × P)) :=
  match requireOneBased a p with
  | .error e => some (.error e)
  | .ok _ =>
      match ops.negateAll p with
      | .error e => some (.error e)
      | .ok p =>
          JuliaLean.base.reduce.whileLoop (permuteVectorStep ops swap (ops.length p))
            (.outer a p 1)

/--
Julia source: base/combinatorics.jl:145-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Row and column permutations for AbstractMatrix
permutecols!(a::AbstractMatrix, p::AbstractVector{<:Integer}) =
    _permute!(a, p, Base.swapcols!)
```
-/
def permutecols! {A P N I : Type} (ops : PermutationBufferOps P N I)
    (requireOneBased : A → P → Jl Unit) (swapColumns : A → I → I → Jl A)
    (a : A) (p : P) : Option (Jl (A × P)) :=
  _permute! ops requireOneBased swapColumns a p

/--
Julia source: base/combinatorics.jl:149-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
permuterows!(a::AbstractMatrix, p::AbstractVector{<:Integer}) =
    _permute!(a, p, Base.swaprows!)
```
-/
def permuterows! {A P N I : Type} (ops : PermutationBufferOps P N I)
    (requireOneBased : A → P → Jl Unit) (swapRows : A → I → I → Jl A)
    (a : A) (p : P) : Option (Jl (A × P)) :=
  _permute! ops requireOneBased swapRows a p

/--
Julia source: base/combinatorics.jl:170-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _invpermute!(a::AbstractMatrix, p::AbstractVector{<:Integer}, swapfun!::F) where {F}
    require_one_based_indexing(a, p)
    p .= .-p
    for i in 1:length(p)
        p[i] > 0 && continue
        j = p[i] = -p[i]
        while j != i
           swapfun!(a, j, i)
           j = p[j] = -p[j]
        end
     end
    a
end
```
-/
def _invpermute! {A P N I : Type} (ops : PermutationBufferOps P N I)
    (requireOneBased : A → P → Jl Unit) (swap : A → I → I → Jl A)
    (a : A) (p : P) : Option (Jl (A × P)) :=
  match requireOneBased a p with
  | .error e => some (.error e)
  | .ok _ =>
      match ops.negateAll p with
      | .error e => some (.error e)
      | .ok p =>
          JuliaLean.base.reduce.whileLoop (invPermuteVectorStep ops swap (ops.length p))
            (.outer a p 1)

/--
Julia source: base/combinatorics.jl:166-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
invpermutecols!(a::AbstractMatrix, p::AbstractVector{<:Integer}) =
    _invpermute!(a, p, Base.swapcols!)
```
-/
def invpermutecols! {A P N I : Type} (ops : PermutationBufferOps P N I)
    (requireOneBased : A → P → Jl Unit) (swapColumns : A → I → I → Jl A)
    (a : A) (p : P) : Option (Jl (A × P)) :=
  _invpermute! ops requireOneBased swapColumns a p

/--
Julia source: base/combinatorics.jl:168-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
invpermuterows!(a::AbstractMatrix, p::AbstractVector{<:Integer}) =
    _invpermute!(a, p, Base.swaprows!)
```
-/
def invpermuterows! {A P N I : Type} (ops : PermutationBufferOps P N I)
    (requireOneBased : A → P → Jl Unit) (swapRows : A → I → I → Jl A)
    (a : A) (p : P) : Option (Jl (A × P)) :=
  _invpermute! ops requireOneBased swapRows a p

/--
Julia source: base/combinatorics.jl:183-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    permute!(v, p)

Permute vector `v` according to permutation `p`, storing the result back into `v`.
No checking is done to verify that `p` is a permutation.

To return a new permutation, use `v[p]`. This is generally faster than `permute!(v, p)`;
it is even faster to write into a pre-allocated output array with `u .= @view v[p]`.
(Even though `permute!` overwrites `v` in-place, it internally requires some allocation.)

$(_DOCS_ALIASING_WARNING)

See also [`invpermute!`](@ref).

# Examples
```jldoctest
julia> A = [1, 1, 3, 4];

julia> perm = [2, 4, 3, 1];

julia> permute!(A, perm);

julia> A
4-element Vector{Int64}:
 1
 4
 3
 1
```
"""
permute!(v, p::AbstractVector) = (v .= v[p])
````
-/
def permute! {A P : Type} (ops : InPlacePermuteOps A P) (v : A) (p : P) : A :=
  ops.broadcastAssign v (ops.gather v p)

/--
Julia source: base/combinatorics.jl:215-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    invpermute!(v, p)

Like [`permute!`](@ref), but the inverse of the given permutation is applied.

Note that if you have a pre-allocated output array (e.g. `u = similar(v)`),
it is quicker to instead employ `u[p] = v`.  (`invpermute!` internally
allocates a copy of the data.)

$(_DOCS_ALIASING_WARNING)

# Examples
```jldoctest
julia> A = [1, 1, 3, 4];

julia> perm = [2, 4, 3, 1];

julia> invpermute!(A, perm);

julia> A
4-element Vector{Int64}:
 4
 1
 3
 1
```
"""
invpermute!(v, p::AbstractVector) = (v[p] = v; v)
````
-/
def invpermute! {A P : Type} (ops : InPlacePermuteOps A P) (v : A) (p : P) : A :=
  ops.indexedAssign v p v

/--
Julia source: base/combinatorics.jl:244-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    invperm(v)

Return the inverse permutation of `v`.
If `B = A[v]`, then `A == B[invperm(v)]`.

See also [`sortperm`](@ref), [`invpermute!`](@ref), [`isperm`](@ref), [`permutedims`](@ref).

# Examples
```jldoctest
julia> p = (2, 3, 1);

julia> invperm(p)
(3, 1, 2)

julia> v = [2; 4; 3; 1];

julia> invperm(v)
4-element Vector{Int64}:
 4
 1
 3
 2

julia> A = ['a','b','c','d'];

julia> B = A[v]
4-element Vector{Char}:
 'b': ASCII/Unicode U+0062 (category Ll: Letter, lowercase)
 'd': ASCII/Unicode U+0064 (category Ll: Letter, lowercase)
 'c': ASCII/Unicode U+0063 (category Ll: Letter, lowercase)
 'a': ASCII/Unicode U+0061 (category Ll: Letter, lowercase)

julia> B[invperm(v)]
4-element Vector{Char}:
 'a': ASCII/Unicode U+0061 (category Ll: Letter, lowercase)
 'b': ASCII/Unicode U+0062 (category Ll: Letter, lowercase)
 'c': ASCII/Unicode U+0063 (category Ll: Letter, lowercase)
 'd': ASCII/Unicode U+0064 (category Ll: Letter, lowercase)
```
"""
function invperm(a::AbstractVector)
    require_one_based_indexing(a)
    b = fill!(similar(a), zero(eltype(a))) # mutable vector of zeros
    n = length(a)
    @inbounds for (i, j) in enumerate(a)
        ((1 <= j <= n) && b[j] == 0) ||
            throw(ArgumentError("argument is not a permutation"))
        b[j] = i
    end
    b
end
````
-/
def invperm_vector_loop {A T : Type} (ops : InverseVectorOps A T) (n : Nat) :
    List T → Nat → List T → Jl (List T)
  | [], _, inverse => pure inverse
  | value :: rest, index, inverse => do
      if !ops.validPosition value n then throw (.argumentError "argument is not a permutation")
      let slot := ops.position value - 1
      if !ops.isZero (listGetD inverse slot ops.zero) then
        throw (.argumentError "argument is not a permutation")
      let converted ← ops.fromIndex index
      invperm_vector_loop ops n rest (index + 1) (listSet inverse slot converted)
termination_by values => values.length

def invperm_vector {A T : Type} (ops : InverseVectorOps A T) (a : A) : Jl A := do
  let _ ← ops.requireOneBased a
  let n := ops.length a
  let inverse ← invperm_vector_loop ops n (ops.elements a) 1 (List.replicate n ops.zero)
  ops.rebuild a inverse

/--
Julia source: base/combinatorics.jl:297-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function invperm(p::Union{Tuple{},Tuple{Int},Tuple{Int,Int}})
    isperm(p) || throw(ArgumentError("argument is not a permutation"))
    p  # in dimensions 0-2, every permutation is its own inverse
end

```
-/
def invperm_small {A : Type} (isperm : A → Bool) (p : A) : Jl A :=
  if isperm p then .ok p else .error (.argumentError "argument is not a permutation")

/--
Julia source: base/combinatorics.jl:303-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invperm(P::Tuple)
    valn = Val(length(P))
    ntuple(valn) do i
        s = _foldoneto(nothing, valn) do s, j
            s !== nothing && return s
            P[j]==i && return j
            nothing
        end
        s === nothing && throw(ArgumentError("argument is not a permutation"))
        s
    end
end

```
-/
private def tuplePosition {T : Type} (equalTo : T → Nat → Bool) (target position : Nat)
    (values : List T) : Option Nat :=
  match values with
  | [] => none
  | value :: rest =>
      if equalTo value target then some position
      else tuplePosition equalTo target (position + 1) rest
termination_by values.length

def invperm_tuple_loop {T : Type} (equalTo : T → Nat → Bool) (values : List T)
    (target remaining : Nat) : Jl (List Nat) :=
  match remaining with
  | 0 => .ok []
  | Nat.succ rest => do
      let index ← match tuplePosition equalTo target 1 values with
        | none => throw (.argumentError "argument is not a permutation")
        | some index => pure index
      let suffix ← invperm_tuple_loop equalTo values (target + 1) rest
      pure (index :: suffix)
termination_by remaining

def invperm_Tuple {T : Type} (equalTo : T → Nat → Bool) (values : List T) : Jl (List Nat) :=
  invperm_tuple_loop equalTo values 1 values.length

/--
Julia source: base/combinatorics.jl:316-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
invperm(P::Any32) = Tuple(invperm(collect(P)))

```
-/
def invperm_Any32 {A C R : Type} (collect : A → C) (inverse : C → Jl C)
    (toTuple : C → R) (values : A) : Jl R := do
  let collected := collect values
  let result ← inverse collected
  pure (toTuple result)

private def nextprodStep {A X F M I W : Type} (ops : NextprodOps A X F M I W)
    (state : NextprodState A X M I W) : Jl (Sum (JInt .i64) (NextprodState A X M I W)) := do
  match state.phase with
  | .check => do
      let finalCounter ← vectorGet state.counters state.size
      let lastPowerIndex ← ops.powerLastIndex state.powers
      let finalPower ← ops.powerAt state.powers lastPowerIndex
      if ops.counterLT finalCounter finalPower then
        if ops.wideGEReal state.product state.target then
          let best := if ops.wideLT state.product state.best then state.product else state.best
          return .inr {state with best := best, phase := .carry}
        else return .inr {state with phase := .grow}
      let lastPowerIndex ← ops.powerLastIndex state.powers
      let finalPower ← ops.powerAt state.powers lastPowerIndex
      if ops.counterLessWide finalPower state.best then
        return .inl (← ops.counterToInt finalPower)
      else return .inl (← ops.wideToInt state.best)
  | .carry => do
      let divisor ← vectorGet state.counters state.carry
      let product ← ops.divideWide state.product divisor
      let counters ← vectorSet state.counters state.carry ops.oneCounter
      let carry := state.carry + 1
      let factor ← ops.factorAt state.factors carry
      let product ← ops.multiplyWideFactor product factor
      let counter ← vectorGet counters carry
      let counter ← ops.multiplyCounterFactor counter factor
      let counters ← vectorSet counters carry counter
      let power ← ops.powerAt state.powers carry
      if ops.counterGT counter power && carry < state.size then
        return .inr (NextprodState.mk state.factors state.target state.powers state.size
          counters product state.best carry .carry)
      let carry := if ops.wideLTReal product state.target then 1 else carry
      return .inr (NextprodState.mk state.factors state.target state.powers state.size
        counters product state.best carry .check)
  | .grow => do
      let factor ← ops.factorAt state.factors 1
      let product ← ops.multiplyWideFactor state.product factor
      let counter ← vectorGet state.counters 1
      let counter ← ops.multiplyCounterFactor counter factor
      let counters ← vectorSet state.counters 1 counter
      let phase := if ops.wideLTReal product state.target then .grow else .check
      return .inr (NextprodState.mk state.factors state.target state.powers state.size
        counters product state.best state.carry phase)

/--
Julia source: base/combinatorics.jl:318-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
#XXX This function should be moved to Combinatorics.jl but is currently used by Base.DSP.
"""
    nextprod(factors::Union{Tuple,AbstractVector}, n)

Next integer greater than or equal to `n` that can be written as ``\\prod k_i^{p_i}`` for integers
``p_1``, ``p_2``, etcetera, for factors ``k_i`` in `factors`.

# Examples
```jldoctest
julia> nextprod((2, 3), 105)
108

julia> 2^2 * 3^3
108
```

!!! compat "Julia 1.6"
    The method that accepts a tuple requires Julia 1.6 or later.
"""
function nextprod(a::Union{Tuple{Vararg{Integer}},AbstractVector{<:Integer}}, x::Real)
    if x > typemax(Int)
        throw(ArgumentError("unsafe for x > typemax(Int), got $x"))
    end
    k = length(a)
    v = fill(1, k)                    # current value of each counter
    mx = map(a -> nextpow(a,x), a)   # maximum value of each counter
    v[1] = mx[1]                      # start at first case that is >= x
    p::widen(Int) = mx[1]             # initial value of product in this case
    best = p
    icarry = 1

    while v[end] < mx[end]
        if p >= x
            best = p < best ? p : best  # keep the best found yet
            carrytest = true
            while carrytest
                p = div(p, v[icarry])
                v[icarry] = 1
                icarry += 1
                p *= a[icarry]
                v[icarry] *= a[icarry]
                carrytest = v[icarry] > mx[icarry] && icarry < k
            end
            if p < x
                icarry = 1
            end
        else
            while p < x
                p *= a[1]
                v[1] *= a[1]
            end
        end
    end
    # might overflow, but want predictable return type
    return mx[end] < best ? Int(mx[end]) : Int(best)
end
````
-/
def nextprod {A X F M I W : Type} (ops : NextprodOps A X F M I W)
    (a : A) (x : X) : Option (Jl (JInt .i64)) :=
  if ops.exceedsIntMax x then
    some (.error (.argumentError ("unsafe for x > typemax(Int), got " ++ ops.showTarget x)))
  else
    let setup : Jl (NextprodState A X M I W) := do
      let size := ops.length a
      let counters := List.replicate size ops.oneCounter
      let powers ← ops.mapNextPow a x
      let firstPower ← ops.powerAt powers 1
      let firstCounter ← ops.storePower firstPower
      let counters ← vectorSet counters 1 firstCounter
      let product ← ops.toWide firstPower
      pure (NextprodState.mk a x powers size counters product product 1 .check)
    match setup with
    | .error e => some (.error e)
    | .ok state => JuliaLean.base.reduce.whileLoop (nextprodStep ops) state

end JuliaLean.base.combinatorics

namespace JuliaLean.Combinatorics

open JuliaLean

structure FixedInteger where
  ty : IntTy
  val : Int
  deriving Repr, DecidableEq

def factorialNat : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialNat n

def factorialResultType : IntTy → IntTy
  | .i8 | .u8 | .i16 | .u16 | .i32 | .u32 => .i64
  | t => t

def factorialLimit : IntTy → Int
  | .i128 => 33
  | .u128 => 34
  | _ => 20

/-- `factorial_lookup`, `base/combinatorics.jl:21-30`, including its eager
conversion to machine `Int` before the sign and table-limit checks. -/
def factorialFixed (t : IntTy) (n : JInt t) : Jl FixedInteger := do
  let idx ← JInt.convert (IntTy.i64.name) .i64 n.val
  if idx.val < 0 then
    .error (.domainError "n must not be negative")
  else if idx.val > factorialLimit t then
    .error (.overflowError "too large for factorial table")
  else
    .ok ⟨factorialResultType t, factorialNat idx.val.toNat⟩

end JuliaLean.Combinatorics

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- `invperm(a::AbstractVector)`, `base/combinatorics.jl:286-296`. -/
def invperm (a : List Int) : Jl (List Int) :=
  let n := a.length
  (a.zipIdx 1).foldlM (fun (b : List Int) (p : Int × Nat) =>
    let (j, i) := p
    if 1 ≤ j ∧ j ≤ n ∧ b.getD (j - 1).toNat 0 = 0 then .ok (b.set (j - 1).toNat i)
    else .error (.argumentError "argument is not a permutation")) (List.replicate n 0)

/-- `isperm(p)`, `base/combinatorics.jl:59-101`: every value `1:n` occurs exactly once. -/
def isperm (p : List Int) : Bool :=
  (List.range p.length).all (fun k => p.count ((k : Int) + 1) = 1)

end JuliaLean.ReinterpretArrays

namespace JuliaLean.IntFuncsCov.Combinatorics

open JuliaLean JuliaLean.IntFuncsCov

/-! ### `factorial` methods -/

/-- `factorial_lookup(n, table, lim)`, `base/combinatorics.jl:21-30`: `Int(n)`, the sign and
limit checks, `one(n)` for zero, and `oftype(n, table[idx])`; the tables hold `idx!`. -/
def factorialLookup {t : IntTy} (n : JInt t) (lim : Int) : Jl (JInt t) := do
  let idx ← JInt.convert (IntTy.i64.name) .i64 n.val
  if idx.val < 0 then .error (.domainError "n must not be negative")
  else if idx.val > lim then .error (.overflowError "too large for factorial table")
  else if idx.val = 0 then .ok (JInt.lit t 1)
  else JInt.convert (t.name) t (JuliaLean.Combinatorics.factorialNat idx.val.toNat)

/-- The fixed-width `factorial` methods, `base/combinatorics.jl:32-40` on a 64-bit
platform: `Int128` (limit 33), `UInt128` (34), `Int64`/`UInt64` (20), and the narrower
types, which convert to `Int64` first. -/
def factorialMethod (t : IntTy) (n : JInt t) : Jl ((s : IntTy) × JInt s) :=
  match t with
  | .i128 => (⟨.i128, ·⟩) <$> factorialLookup n 33
  | .u128 => (⟨.u128, ·⟩) <$> factorialLookup n 34
  | .i64 => (⟨.i64, ·⟩) <$> factorialLookup n 20
  | .u64 => (⟨.u64, ·⟩) <$> factorialLookup n 20
  | _ => do
    let m ← JInt.convert (IntTy.i64.name) .i64 n.val
    (⟨.i64, ·⟩) <$> factorialLookup m 20

/-! ### `_foldoneto` -/

/-- `_foldoneto(op, acc, Val(N))`, `base/combinatorics.jl:46-60`: the `@assert N > 0`
followed by `for i in 1:N; acc = op(acc, i); end` (the `@generated` branch unrolls the same
loop). `op` may itself throw. -/
def foldoneto {α : Type} (op : α → Nat → Jl α) (acc : α) (N : Nat) : Jl α :=
  if N > 0 then (List.range' 1 N).foldlM op acc
  else .error (.argumentError "AssertionError: N must be positive")

/-! ### `isperm` and `invperm` -/

inductive Kind where
  | int | float | bool
  deriving DecidableEq, Repr

/-- A permutation element: its kind and twice its numeric value. -/
structure Elem where
  kind : Kind
  half : Int
  deriving DecidableEq, Repr

def Elem.ofInt (v : Int) : Elem := ⟨.int, 2 * v⟩

/-- `to_index(a)` for a scalar index (`base/indices.jl`): an `Integer` indexes, a `Bool` or
a non-integer real throws `ArgumentError("invalid index ...")`. -/
def toIndex (a : Elem) : Jl Int :=
  match a.kind with
  | .int => .ok (a.half / 2)
  | _ => .error (.argumentError "invalid index")

/-- The loop of `_isperm(A)`, `base/combinatorics.jl:78-85`:
`(0 < a <= n) && (used[a] ⊻= true) || return false`. -/
def ispermLoop (n : Nat) : List Bool → List Elem → Jl Bool
  | _, [] => .ok true
  | used, a :: as =>
    if 0 < a.half ∧ a.half ≤ 2 * n then do
      let k ← toIndex a
      let i := k.toNat - 1
      let new := xor (used.getD i false) true
      if new then ispermLoop n (used.set i new) as else .ok false
    else .ok false

/-- `_isperm(A)`: `used = falses(length(A))` and the loop. -/
def ispermVec (A : List Elem) : Jl Bool := ispermLoop A.length (List.replicate A.length false) A

/-- `isperm(A)`, `base/combinatorics.jl:76`, for an array argument. -/
def ispermArray (A : List Elem) : Jl Bool := ispermVec A

/-- `isperm(p::Tuple{}) = true`, `:87`. -/
def ispermEmpty : Bool := true

/-- `isperm(p::Tuple{Int}) = p[1] == 1`, `:88`. -/
def isperm1 (a : Elem) : Bool := a.half == 2

/-- `isperm(p::Tuple{Int,Int})`, `:89`. -/
def isperm2 (a b : Elem) : Bool :=
  (a.half == 2 && b.half == 4) || (a.half == 4 && b.half == 2)

/-- `isperm(P::Tuple)`, `:91-99`: for each `i`, an inner `_foldoneto` ors `P[j] == i` over
`j`, and the outer one ands the results. -/
def ispermTuple (P : List Elem) : Jl Bool :=
  let n := P.length
  foldoneto (fun b i => do
    let s ← foldoneto (fun s j => .ok (s || (P.getD (j - 1) ⟨.int, 0⟩).half == 2 * (i : Int))) false n
    .ok (b && s)) true n

/-- `isperm(P::Any32) = _isperm(P)`, `:101`, for tuples of length at least 32. -/
def ispermAny32 (P : List Elem) : Jl Bool := ispermVec P

/-- Method selection for a tuple argument. -/
def ispermTupleDispatch : List Elem → Jl Bool
  | [] => .ok ispermEmpty
  | [a] => if a.kind = .int then .ok (isperm1 a) else ispermTuple [a]
  | [a, b] => if a.kind = .int ∧ b.kind = .int then .ok (isperm2 a b) else ispermTuple [a, b]
  | P => if 32 ≤ P.length then ispermAny32 P else ispermTuple P

/-- `invperm(a::AbstractVector)`, `base/combinatorics.jl:286-296`, on the element model:
`((1 <= j <= n) && b[j] == 0) || throw(ArgumentError)`, then `b[j] = i`. -/
def invpermVecLoop (n : Nat) : Nat → List Int → List Elem → Jl (List Int)
  | _, b, [] => .ok b
  | i, b, j :: js =>
    if 2 ≤ j.half ∧ j.half ≤ 2 * n then do
      let k ← toIndex j
      if b.getD (k.toNat - 1) 0 = 0 then invpermVecLoop n (i + 1) (b.set (k.toNat - 1) i) js
      else .error (.argumentError "argument is not a permutation")
    else .error (.argumentError "argument is not a permutation")

def invpermVec (A : List Elem) : Jl (List Int) :=
  invpermVecLoop A.length 1 (List.replicate A.length 0) A

/-- `invperm(p::Union{Tuple{},Tuple{Int},Tuple{Int,Int}})`, `:298-301`: check, then return
`p` itself. -/
def invpermSmall (p : List Elem) : Jl (List Int) := do
  let ok ← ispermTupleDispatch p
  if ok then .ok (p.map (·.half / 2)) else .error (.argumentError "argument is not a permutation")

/-- `invperm(P::Tuple)`, `:303-314`: entry `i` is the first `j` with `P[j] == i`, found by a
`_foldoneto` over `j`; a missing `i` throws. -/
def invpermTuple (P : List Elem) : Jl (List Int) :=
  let n := P.length
  (List.range' 1 n).mapM fun (i : Nat) => do
    let s ← foldoneto (fun (s : Option Nat) j => .ok (if s.isSome then s
      else if (P.getD (j - 1) ⟨.int, 0⟩).half == 2 * (i : Int) then some j else none)) none n
    match s with
    | none => .error (.argumentError "argument is not a permutation")
    | some j => .ok (j : Int)

/-- `invperm(P::Any32) = Tuple(invperm(collect(P)))`, `:316`. -/
def invpermAny32 (P : List Elem) : Jl (List Int) := invpermVec P

/-- Method selection for a tuple argument of `invperm`. -/
def invpermTupleDispatch : List Elem → Jl (List Int)
  | [] => invpermSmall []
  | [a] => if a.kind = .int then invpermSmall [a] else invpermTuple [a]
  | [a, b] => if a.kind = .int ∧ b.kind = .int then invpermSmall [a, b] else invpermTuple [a, b]
  | P => if 32 ≤ P.length then invpermAny32 P else invpermTuple P

/-! ### Empty vectors with abstract element type -/

inductive EmptyEltype where
  | integer
  | any
  | bottom
  deriving DecidableEq

/-- The entry of `invperm(a::AbstractVector)` at `base/combinatorics.jl:286-296` before
the empty loop: `fill!(similar(a), zero(eltype(a)))`. `zero(Any)` and `zero(Union{})`
throw, while a concrete integer element type supplies zero. -/
def invpermEmpty : EmptyEltype → Jl (List Int)
  | .integer => .ok []
  | .any => .error (.methodError "zero")
  | .bottom => .error (.methodError "zero")

end JuliaLean.IntFuncsCov.Combinatorics

namespace JuliaLean.Combinatorics

open JuliaLean

abbrev isperm := JuliaLean.ReinterpretArrays.isperm
abbrev invperm := JuliaLean.ReinterpretArrays.invperm

def ispermTyped {t : IntTy} (p : List (JInt t)) : Bool :=
  isperm (p.map (·.val))

/-- `require_one_based_indexing(a)`, `base/combinatorics.jl:287`, before the
value-level `invperm` model. -/
def invpermWithFirstIndex (first : Int) (p : List Int) : Jl (List Int) :=
  if first = 1 then invperm p
  else .error (.argumentError "offset arrays are not supported")

inductive PermuteError where
  | bounds
  | dimensionMismatch
  deriving Repr, DecidableEq

abbrev PermuteResult (α : Type) := Except PermuteError α

def gathered (v : List Int) (p : List Int) : PermuteResult (List Int) :=
  if p.all (fun i => 1 ≤ i ∧ i ≤ v.length) then
    .ok (p.map fun i => v.getD (i - 1).toNat 0)
  else .error .bounds

/-- `permute!(v,p) = (v .= v[p])`, `base/combinatorics.jl:184-214`.
The indexed right-hand side is completed before the destination shape check. -/
def permuteBang (v p : List Int) : PermuteResult (List Int) := do
  let rhs ← gathered v p
  if rhs.length = v.length then .ok rhs else .error .dimensionMismatch

private def scatterPairs (out : List Int) : List (Int × Int) → List Int
  | [] => out
  | (i, x) :: rest => scatterPairs (out.set (i - 1).toNat x) rest

def scattered (v p : List Int) : PermuteResult (List Int) :=
  if p.length ≠ v.length then .error .dimensionMismatch
  else if p.all (fun i => 1 ≤ i ∧ i ≤ v.length) then
    .ok (scatterPairs v (p.zip v))
  else .error .bounds

/-- `invpermute!(v,p) = (v[p] = v; v)`, `base/combinatorics.jl:216-243`. -/
def invpermuteBang (v p : List Int) : PermuteResult (List Int) := scattered v p

def permuteFin {n : Nat} (v : Fin n → Int) (p : Fin n → Fin n) : Fin n → Int :=
  fun i => v (p i)

def invpermuteFin {n : Nat} (v : Fin n → Int) (pinv : Fin n → Fin n) : Fin n → Int :=
  fun i => v (pinv i)

private instance {t : IntTy} : Inhabited (JInt t) := ⟨JInt.lit t 0⟩

def swapAxis (axisLength i j : Int) : Jl Unit :=
  if i = j then .ok ()
  else if 1 ≤ i ∧ i ≤ axisLength ∧ 1 ≤ j ∧ j ≤ axisLength then .ok ()
  else .error .boundsError

def get1 {α : Type} [Inhabited α] (xs : List α) (i : Int) : α :=
  xs.getD (i - 1).toNat default

private def set1 {α : Type} (xs : List α) (i : Int) (x : α) : List α :=
  xs.set (i - 1).toNat x

private def swap1 {α : Type} [Inhabited α] (xs : List α) (i j : Int) : List α :=
  let xi := get1 xs i
  let xj := get1 xs j
  set1 (set1 xs i xj) j xi

private def cycleStep {t : IntTy} : Nat → List Int × List (JInt t) × Int × Int →
    Jl (List Int × List (JInt t) × Int × Int)
  | 0, _ => .error (.argumentError "cycle did not terminate")
  | fuel + 1, (cols, p, j, incoming) =>
      if (get1 p incoming).val < 0 then
        let cols' := swap1 cols incoming j
        let next := -(get1 p incoming)
        let p' := set1 p incoming next
        cycleStep fuel (cols', p', incoming, next.val)
      else .ok (cols, p, j, incoming)

private def permuteFor {t : IntTy} (n : Nat) : List Nat → List Int × List (JInt t) →
    Jl (List Int × List (JInt t))
  | [], state => .ok state
  | z :: rest, (cols, p) =>
      let i : Int := z + 1
      if (get1 p i).val > 0 then permuteFor n rest (cols, p)
      else do
        let incoming := -(get1 p i)
        let p' := set1 p i incoming
        let (cols', p'', _, _) ← cycleStep n (cols, p', i, incoming.val)
        permuteFor n rest (cols', p'')

/-- `_permute!`, `base/combinatorics.jl:151-165`, with columns represented by
their labels and the permutation vector mutated as the source mutates it. -/
def permuteCols {t : IntTy} (cols : List Int) (p : List (JInt t)) :
    Jl (List Int × List (JInt t)) :=
  let negated := p.map (fun x => -x)
  permuteFor p.length (List.range p.length) (cols, negated)

private def invCycle {t : IntTy} (i : Int) : Nat →
    List Int × List (JInt t) × Int → Jl (List Int × List (JInt t) × Int)
  | 0, _ => .error (.argumentError "inverse cycle did not terminate")
  | fuel + 1, (cols, p, j) =>
      if j = i then .ok (cols, p, j)
      else
        let cols' := swap1 cols j i
        let next := -(get1 p j)
        let p' := set1 p j next
        invCycle i fuel (cols', p', next.val)

private def invPermuteFor {t : IntTy} (n : Nat) : List Nat →
    List Int × List (JInt t) → Jl (List Int × List (JInt t))
  | [], state => .ok state
  | z :: rest, (cols, p) =>
      let i : Int := z + 1
      if (get1 p i).val > 0 then invPermuteFor n rest (cols, p)
      else do
        let j := -(get1 p i)
        let p' := set1 p i j
        let (cols', p'', _) ← invCycle i n (cols, p', j.val)
        invPermuteFor n rest (cols', p'')

/-- `_invpermute!`, `base/combinatorics.jl:170-182`. -/
def invPermuteCols {t : IntTy} (cols : List Int) (p : List (JInt t)) :
    Jl (List Int × List (JInt t)) :=
  let negated := p.map (fun x => -x)
  invPermuteFor p.length (List.range p.length) (cols, negated)

private def findNextNonzero {t : IntTy} : List (JInt t) → Nat → Option Nat
  | [], _ => none
  | x :: xs, 0 => if x.val ≠ 0 then some 0 else (findNextNonzero xs 0).map (· + 1)
  | _ :: xs, start + 1 => (findNextNonzero xs start).map (· + 1)

private def bangCycle {t : IntTy} (zero : JInt t) (start : Int) : Nat →
    List Int × List (JInt t) × Int × Int × Nat →
    Jl (List Int × List (JInt t) × Nat)
  | 0, _ => .error (.argumentError "destructive cycle did not terminate")
  | fuel + 1, (cols, p, ptr, next, count) =>
      if next = start then .ok (cols, set1 p ptr zero, count)
      else
        let cols' := swap1 cols ptr next
        let p' := set1 p ptr zero
        bangCycle zero start fuel (cols', p', next, (get1 p' next).val, count + 1)

private def bangOuter {t : IntTy} (zero : JInt t) (n : Nat) : Nat →
    List Int × List (JInt t) × Nat × Nat → Jl (List Int × List (JInt t))
  | 0, _ => .error (.argumentError "destructive permutation did not terminate")
  | fuel + 1, (cols, p, count, cursor) =>
      if count < n then
        match findNextNonzero p cursor with
        | none => .error (.argumentError "invalid permutation")
        | some z => do
            let start : Int := z + 1
            let next := (get1 p start).val
            let (cols', p', count') ← bangCycle zero start (n + 1)
              (cols, p, start, next, count + 1)
            bangOuter zero n fuel (cols', p', count', start.toNat)
      else .ok (cols, p)

/-- `permutecols!!`, `base/combinatorics.jl:125-144`. -/
def permuteColsBangBang {t : IntTy} (cols : List Int) (p : List (JInt t)) :
    Jl (List Int × List (JInt t)) :=
  bangOuter (JInt.lit t 0) p.length (p.length + 1) (cols, p, 0, 0)

def typedIsperm {t : IntTy} (p : List (JInt t)) : Bool :=
  JuliaLean.ReinterpretArrays.isperm (p.map (·.val))

def gatherCols {t : IntTy} (cols : List Int) (p : List (JInt t)) : List Int :=
  p.map (fun i => get1 cols i.val)

private def nextPowerLoop (a x p : Nat) : Nat → Nat
  | 0 => p
  | fuel + 1 => if x ≤ p then p else nextPowerLoop a x (p * a) fuel

def nextPower (a x : Nat) : Jl Nat :=
  if x = 0 then .error (.domainError "x must be positive")
  else if a ≤ 1 then .error (.domainError "a must exceed one")
  else .ok (nextPowerLoop a x 1 128)

private partial def carry (a mx : List Nat) (p : Nat) (v : List Nat) (icarry : Nat) :
    Jl (Nat × List Nat × Nat) := do
  let vi := v.getD icarry 0
  if vi = 0 then .error .divideError else
  let p := p / vi
  let v := v.set icarry 1
  let icarry := icarry + 1
  let factor := a.getD icarry 0
  let p := p * factor
  let v := v.set icarry (v.getD icarry 0 * factor)
  if v.getD icarry 0 > mx.getD icarry 0 ∧ icarry + 1 < a.length then
    carry a mx p v icarry
  else .ok (p, v, icarry)

private partial def nextprodLoop (a mx : List Nat) (x p best icarry : Nat) (v : List Nat) : Nat :=
  if v.getLastD 0 < mx.getLastD 0 then
    if x ≤ p then
      let best := min p best
      match carry a mx p v icarry with
      | .error _ => best
      | .ok (p, v, icarry) =>
          nextprodLoop a mx x p best (if p < x then 0 else icarry) v
    else
      nextprodLoop a mx x (p * a.getD 0 0) best icarry
        (v.set 0 (v.getD 0 0 * a.getD 0 0))
  else min (mx.getLastD 0) best

/-- Source control flow for positive machine-`Int` inputs. Empty factors reach
the same first-element `BoundsError` as lines 344-345. -/
def nextprod (a : List Nat) (x : Nat) : Jl Nat := do
  let mx ← a.mapM (fun factor => nextPower factor x)
  match a, mx with
  | [], _ => .error .boundsError
  | _, [] => .error .boundsError
  | _, first :: _ =>
      let v := (List.replicate a.length 1).set 0 first
      .ok (nextprodLoop a mx x first first 0 v)

end JuliaLean.Combinatorics

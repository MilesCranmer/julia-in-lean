import JuliaLean.base.boot
import JuliaLean.base.ntuple
import JuliaLean.Core
import JuliaLean.Runtime.Strings
import JuliaLean.base.abstractarray
import JuliaLean.base.operators
import JuliaLean.base.generator
import JuliaLean.base.iterators
import JuliaLean.base.int
import JuliaLean.src.genericmemory_c

/-!
# Model of `base/array.jl`

Julia revision `f755f49a9e41380d7da126b3c1db9fe7f83dd027`, on a 64-bit platform.
Integer values carry their Julia widths. Array handles, memory references, element types,
and mutable stores are typed parameters. The monad records allocation, mutation, and errors
in source order; in particular, an exception need not undo earlier writes. Calls into
`abstractarray.jl` and other later-loaded or user-extensible functions are typed parameters.
-/

namespace JuliaLean.base.array

open JuliaLean
open JuliaLean.src.genericmemory_c (DictLayout unsetCell)

inductive Error where
  | argument (message : String)
  | bounds
  | inexact
  | overflow
  | divide
  | typeError (context : String)
  | dimensionMismatch (message : String)
  | method (name : String)
  | assertion (message : String)
  | concurrency (message : String)
  | thrownNothing
  | undefinedReference
  | showError (error : JuliaLean.Strings.ShowErrorKind)
  deriving Repr, DecidableEq

structure DimensionMismatch where
  message : String
  deriving Repr, DecidableEq

abbrev I := JInt .i64

def zero : I := JInt.wrap .i64 0
def one : I := JInt.wrap .i64 1

/-- The counter and writes of a Julia `for i = 1:length(xs)` loop. Tuple reads
are total; the supplied store operation is Julia's typed `setindex!` call. -/
def writeValues [Monad m] (set : A → α → I → m A) (a : A) (xs : List α) : m A := do
  let (_, a) ← xs.foldlM (fun (i, a) x => do
    let a ← set a x i
    pure (i + one, a)) (one, a)
  pure a

/-- A Julia range loop with representable `Int` endpoints. The list contains its
actual iteration values, rather than an artificial evaluation limit. -/
def intRange (lo hi : I) : List I :=
  (List.range ((hi.val - lo.val + 1).toNat)).map (fun (k : Nat) => JInt.wrap .i64 (lo.val + (k : Int)))

/-- Syntax tree distinguished by `_safeindex`; other Julia expression heads remain opaque. -/
inductive Expr (Atom : Type) where
  | atom (value : Atom)
  | node (head : String) (args : List (Expr Atom))
  | ref (array : (Expr Atom)) (indices : List (Expr Atom))
  | assign (left right : (Expr Atom))
  | safeGet (array : (Expr Atom)) (indices : List (Expr Atom))
  | safeSet (array value : (Expr Atom)) (indices : List (Expr Atom))
  | escape (body : (Expr Atom))
  deriving Repr

/-- The typed field, memory, and checked-arithmetic operations used by vector resizing.
`checkedAdd`/`checkedMul` belong to checked.jl, which loads later. -/
structure Storage (m : Type → Type) (A Mem R : Type) where
  ref : A → m R
  memory : R → Mem
  offset : R → I
  length : A → m I
  memLength : Mem → m I
  sameRef : R → R → Bool
  sameMem : Mem → Mem → Bool
  setRef : A → R → m Unit
  setSize : A → I → m Unit
  memoryref : Mem → I → m R
  shiftref : R → I → m R
  allocate : Mem → I → m Mem
  copyMemory : Mem → I → Mem → I → I → m Unit
  copyRef : R → R → I → m Unit
  unsetMemory : Mem → I → m Unit
  unsetArray : A → I → m Unit
  checkedAdd : I → I → m I
  checkedMul : I → I → m I
  divide : I → I → m I
  overallocation : I → m I

/-- Finite iterator protocol: `rank` counts remaining iteration steps.
The decreasing witness is a termination invariant of a finite iterator, not evaluation fuel. -/
structure FiniteIterator (m : Type → Type) (α St : Type) where
  rank : St → Nat
  first : m (Option (α × St))
  next : (st : St) → m (Option (α × { st' : St // rank st' < rank st }))

/-- DataType layout fields read by `jl_stored_inline` in src/datatype.c. -/
structure Layout where
  name : Nat
  isbits : Bool
  mayInline : Bool
  ptrs : Bool
  undefPtrs : Bool
  size : Nat
  align : Nat

def Layout.WF (d : Layout) : Prop :=
  d.isbits = (d.mayInline && !d.ptrs) ∧ (∃ k, d.align = 2 ^ k) ∧ d.align ∣ d.size

inductive StoredType where
  | any
  | bottom
  | abstractDT (name : Nat)
  | dt (layout : Layout)
  | union (members : List Layout)

def inlineAlloc (d : Layout) (pointerfree : Bool) : Bool :=
  d.mayInline && (!d.ptrs || (!pointerfree && !d.undefPtrs))

def unionInlineCount : StoredType → Bool → Nat
  | .dt d, pf => if inlineAlloc d pf then 1 else 0
  | .union ms, _ => if ms.all (fun d => inlineAlloc d true) then ms.length else 0
  | _, _ => 0

def storedInline (t : StoredType) : JInt .i32 :=
  let count := unionInlineCount t false
  JInt.wrap .i32 (if 0 < count ∧ count < 127 then 1 else 0)

def unionType : StoredType → Bool
  | .union _ => true
  | _ => false

/--
Julia source: base/array.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
DimensionMismatch() = DimensionMismatch("")
```
-/
def dimensionMismatch : DimensionMismatch := ⟨""⟩

/--
Julia source: base/array.jl:132-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _safeindex(ex)
    return esc(_safeindex(ex))
end
```
-/
def safeindexMacro (rewrite : (Expr Atom) → (Expr Atom)) (ex : (Expr Atom)) : (Expr Atom) := .escape (rewrite ex)

/--
Julia source: base/array.jl:135-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _safeindex(ex)
    isa(ex, Expr) || return ex
    if ex.head === :(=)
        lhs = ex.args[1]
        if isa(lhs, Expr) && lhs.head === :ref # xs[i] = x
            rhs = ex.args[2]
            xs = lhs.args[1]
            args = Vector{Any}(undef, length(lhs.args)-1)
            for i = 2:length(lhs.args)
                args[i-1] = _safeindex(lhs.args[i])
            end
            return Expr(:call, GlobalRef(@__MODULE__, :__safe_setindex!), xs, _safeindex(rhs), args...)
        end
    elseif ex.head === :ref # xs[i]
        return Expr(:call, GlobalRef(@__MODULE__, :__safe_getindex), ex.args...)
    end
    args = Vector{Any}(undef, length(ex.args))
    for i = 1:length(ex.args)
        args[i] = _safeindex(ex.args[i])
    end
    return Expr(ex.head, args...)
end
```
-/
def safeindex : Expr Atom → Expr Atom
  | .atom x => .atom x
  | .assign (.ref xs args) rhs => .safeSet xs (safeindex rhs) (args.map safeindex)
  | .ref xs args => .safeGet xs args
  | .assign lhs rhs => .assign (safeindex lhs) (safeindex rhs)
  | .node h args => .node h (args.map safeindex)
  | .safeGet xs args => .safeGet (safeindex xs) (args.map safeindex)
  | .safeSet xs x args => .safeSet (safeindex xs) (safeindex x) (args.map safeindex)
  | .escape x => .escape (safeindex x)
termination_by e => sizeOf e

/--
Julia source: base/array.jl:158-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vect() = Vector{Any}()
```
-/
def vectEmpty [Monad m] (allocate : I → m A) : m A := allocate zero

/--
Julia source: base/array.jl:159-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function vect(X::T...) where T
    @_terminates_locally_meta
    vec = Vector{T}(undef, length(X))
    @_safeindex for i = 1:length(X)
        vec[i] = X[i]
    end
    return vec
end
```
-/
def vectTyped [Monad m] (allocate : I → m A) (set : A → α → I → m A)
    (xs : List α) : m A := do
  let vec ← allocate (JInt.wrap .i64 xs.length)
  writeValues set vec xs

/--
Julia source: base/array.jl:183-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function vect(X...)
    T = promote_typeof(X...)
    return T[X...]
end
```
-/
def vectPromoted [Monad m] (promoteTypeof : List α → m T)
    (literal : T → List α → m A) (xs : List α) : m A := do
  let t ← promoteTypeof xs
  literal t xs

/--
Julia source: base/array.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
asize_from(a::Array, n) = n > ndims(a) ? () : (size(a,n), asize_from(a, n+1)...)
```
-/
def asizeFrom [Monad m] (value : Z → Int) (toInt : Z → m I)
    (ndims : A → I) (size : A → I → m I) (a : A) (n : Z) : m (List I) := do
  if value n > (ndims a).val then return []
  let first ← toInt n
  (intRange first (ndims a)).mapM (size a)

/--
Julia source: base/array.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allocatedinline(@nospecialize T::Type) = (@_total_meta; ccall(:jl_stored_inline, Cint, (Any,), T) != Cint(0))
```
-/
def allocatedinline (storedInline : T → JInt .i32) (t : T) : Bool :=
  storedInline t != JInt.wrap .i32 0

/--
Julia source: base/array.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isbitsunion(u::Type) = u isa Union && allocatedinline(u)
```
-/
def isbitsunion (isUnion : T → Bool) (storedInline : T → JInt .i32)
    (u : T) : Bool := isUnion u && allocatedinline storedInline u

/--
Julia source: base/array.jl:208-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsetindex!(A::Array, i::Integer) = unsetindex!(A, to_index(i))
```
-/
def unsetindexInteger [Monad m] (toIndex : Z → m I)
    (unset : A → I → m A) (a : A) (i : Z) : m A := do
  unset a (← toIndex i)

/--
Julia source: base/array.jl:209-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsetindex!(A::Array, i::Int)
    @inline
    @boundscheck checkbounds(A, i)
    @inbounds unsetindex!(memoryref(A.ref, i))
    return A
end
```
-/
def unsetindexInt [Monad m] (checkbounds : A → I → m Unit)
    (memoryref : A → I → m R) (unset : R → m Unit) (a : A) (i : I) : m A := do
  checkbounds a i
  unset (← memoryref a i)
  pure a

/--
Julia source: base/array.jl:218-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
elsize(::Type{A}) where {T,A<:Array{T}} = aligned_sizeof(T)
```
-/
def elsizeArray (alignedSizeof : T → I) (t : T) : I := alignedSizeof t

/--
Julia source: base/array.jl:219-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function elsize(::Type{Ptr{T}}) where T
    # this only must return something valid for values which satisfy is_valid_intrinsic_elptr(T),
    # which includes Any and most concrete datatypes
    T === Any && return sizeof(Ptr{Any})
    T isa DataType || sizeof(Any) # throws
    return LLT_ALIGN(Core.sizeof(T), datatype_alignment(T))
end
```
-/
def elsizePtr [Monad m] (isAny isDataType : T → Bool)
    (sizeofAny : m I) (sizeofPtrAny : I) (coreSize alignment : T → m I)
    (align : I → I → I) (t : T) : m I := do
  if isAny t then return sizeofPtrAny
  if !isDataType t then let _ ← sizeofAny
  return align (← coreSize t) (← alignment t)

/--
Julia source: base/array.jl:226-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
elsize(::Type{Union{}}) = 0
```
-/
def elsizeBottom : I := zero

/--
Julia source: base/array.jl:227-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
elsize(::Type{Union{}}, slurp...) = throw(MethodError(elsize, (Union{}, slurp...)))
```
-/
def elsizeBottomArgs [Monad m] [MonadExceptOf Error m]
    (_args : List α) : m I := throw (.method "elsize")

/--
Julia source: base/array.jl:229-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeof(a::Array) = length(a) * elsize(typeof(a)) # n.b. this ignores bitsunion bytes, as a historical fact
```
-/
def sizeofArray (length : A → I) (elementSize : A → I) (a : A) : I :=
  length a * elementSize a

/--
Julia source: base/array.jl:231-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(a::Array, i::Int...)
    @inline
    @_noub_if_noinbounds_meta
    @boundscheck checkbounds(Bool, a, i...) || return false
    ii = _sub2ind(size(a), i...)
    return @inbounds isassigned(memoryrefnew(a.ref, ii, false))
end
```
-/
def isassignedArray [Monad m] (bounds : A → List I → m Bool)
    (size : A → m D) (sub2ind : D → List I → m I)
    (memoryrefnew : A → I → Bool → m R) (assigned : R → m Bool)
    (a : A) (indices : List I) : m Bool := do
  if !(← bounds a indices) then return false
  let ii ← sub2ind (← size a) indices
  assigned (← memoryrefnew a ii false)

/--
Julia source: base/array.jl:239-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(a::Vector, i::Int) # slight compiler simplification for the most common case
    @inline
    @_noub_if_noinbounds_meta
    @boundscheck checkbounds(Bool, a, i) || return false
    return @inbounds isassigned(memoryrefnew(a.ref, i, false))
end
```
-/
def isassignedVector [Monad m] (bounds : A → I → m Bool)
    (memoryrefnew : A → I → Bool → m R) (assigned : R → m Bool)
    (a : A) (i : I) : m Bool := do
  if !(← bounds a i) then return false
  assigned (← memoryrefnew a i false)

/--
Julia source: base/array.jl:259-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_copyto!(dest::Ptr{T}, src::Ptr{T}, n) where T
    # Do not use this to copy data between pointer arrays.
    # It can't be made safe no matter how carefully you checked.
    memmove(dest, src, n * aligned_sizeof(T))
    return dest
end
```
-/
def unsafeCopyPtr [Monad m] (alignedSizeof : I) (multiply : N → I → Bytes)
    (memmove : P → P → Bytes → m Unit) (dest src : P) (n : N) : m P := do
  memmove dest src (multiply n alignedSizeof)
  pure dest

/--
Julia source: base/array.jl:276-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_copyto!(dest::Array, doffs, src::Array, soffs, n)
    n == 0 && return dest
    unsafe_copyto!(memoryref(dest.ref, doffs), memoryref(src.ref, soffs), n)
    return dest
end
```
-/
def unsafeCopyArray [Monad m] (isZero : N → Bool)
    (destMemoryref : D → OffsetD → m R) (srcMemoryref : S → OffsetS → m R)
    (copy : R → R → N → m Unit) (dest : D) (doffs : OffsetD)
    (src : S) (soffs : OffsetS) (n : N) : m D := do
  if isZero n then return dest
  copy (← destMemoryref dest doffs) (← srcMemoryref src soffs) n
  pure dest

/--
Julia source: base/array.jl:288-289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array, doffs::Integer, src::Array, soffs::Integer, n::Integer) =
    (@_propagate_inbounds_meta; _copyto_impl!(dest, doffs, src, soffs, n))
```
-/
def copyto288 [Monad m] 
    (copyImpl : D → OffsetD → S → OffsetS → Count → m D)
    (dest : D) (doffs : OffsetD) (src : S) (soffs : OffsetS) (n : Count) : m D :=
  copyImpl dest doffs src soffs n

/--
Julia source: base/array.jl:290-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array, doffs::Integer, src::Memory, soffs::Integer, n::Integer) =
    (@_propagate_inbounds_meta; _copyto_impl!(dest, doffs, src, soffs, n))
```
-/
def copyto290 [Monad m] 
    (copyImpl : D → OffsetD → S → OffsetS → Count → m D)
    (dest : D) (doffs : OffsetD) (src : S) (soffs : OffsetS) (n : Count) : m D :=
  copyImpl dest doffs src soffs n

/--
Julia source: base/array.jl:292-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Memory, doffs::Integer, src::Array, soffs::Integer, n::Integer) =
    (@_propagate_inbounds_meta; _copyto_impl!(dest, doffs, src, soffs, n))
```
-/
def copyto292 [Monad m] 
    (copyImpl : D → OffsetD → S → OffsetS → Count → m D)
    (dest : D) (doffs : OffsetD) (src : S) (soffs : OffsetS) (n : Count) : m D :=
  copyImpl dest doffs src soffs n

/--
Julia source: base/array.jl:296-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array{T}, doffs::Integer, src::Array{T}, soffs::Integer, n::Integer) where {T} =
    (@_propagate_inbounds_meta; _copyto_impl!(dest, doffs, src, soffs, n))
```
-/
def copyto296 [Monad m] 
    (copyImpl : D → OffsetD → S → OffsetS → Count → m D)
    (dest : D) (doffs : OffsetD) (src : S) (soffs : OffsetS) (n : Count) : m D :=
  copyImpl dest doffs src soffs n

mutual

/--
Julia source: base/array.jl:299-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _copyto_impl!(dest::Union{Array,Memory}, doffs::Integer, src::Union{Array,Memory}, soffs::Integer, n::Integer)
    @inline
    n == 0 && return dest
    n > 0 || _throw_argerror("Number of elements to copy must be non-negative.")
    @boundscheck checkbounds(dest, doffs)
    @boundscheck n <= length(dest) - doffs + 1 || throw(BoundsError(dest, length(dest) + 1))
    @boundscheck checkbounds(src, soffs)
    @boundscheck n <= length(src) - soffs + 1 || throw(BoundsError(src, length(src) + 1))
    doffs = Int(doffs)
    soffs = Int(soffs)
    n = Int(n)
    @inbounds let dest = memoryref(dest isa Array ? getfield(dest, :ref) : dest, doffs),
                  src = memoryref(src isa Array ? getfield(src, :ref) : src, soffs)
        unsafe_copyto!(dest, src, n)
    end
    return dest
end
```
-/
def copytoImpl {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {Count D S OffsetD OffsetS DifferenceD DifferenceS RemainingD RemainingS Ref : Type}
    (isZero positive : Count → m Bool)
    (destLength : D → m I) (srcLength : S → m I)
    (destBounds : D → OffsetD → m Unit) (srcBounds : S → OffsetS → m Unit)
    (destSub : I → OffsetD → m DifferenceD) (srcSub : I → OffsetS → m DifferenceS)
    (destAdd : DifferenceD → I → m RemainingD)
    (srcAdd : DifferenceS → I → m RemainingS)
    (fitsDest : Count → RemainingD → m Bool) (fitsSrc : Count → RemainingS → m Bool)
    (throwDestBounds : D → I → m Empty) (throwSrcBounds : S → I → m Empty)
    (toDestInt : OffsetD → m I) (toSrcInt : OffsetS → m I)
    (toCountInt : Count → m I) (destRef : D → I → m Ref)
    (srcRef : S → I → m Ref) (copy : Ref → Ref → I → m Unit)
    (dest : D) (doffs : OffsetD) (src : S) (soffs : OffsetS) (n : Count) : m D := do
  if ← isZero n then return dest
  if !(← positive n) then
    throwArgument "Number of elements to copy must be non-negative."
  destBounds dest doffs
  let remaining ← destAdd (← destSub (← destLength dest) doffs) one
  if !(← fitsDest n remaining) then
    return Empty.elim (← throwDestBounds dest
      (JuliaLean.base.int.add (← destLength dest) one))
  srcBounds src soffs
  let remaining ← srcAdd (← srcSub (← srcLength src) soffs) one
  if !(← fitsSrc n remaining) then
    return Empty.elim (← throwSrcBounds src
      (JuliaLean.base.int.add (← srcLength src) one))
  let doffs ← toDestInt doffs
  let soffs ← toSrcInt soffs
  let count ← toCountInt n
  copy (← destRef dest doffs) (← srcRef src soffs) count
  pure dest

/--
Julia source: base/array.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_throw_argerror(s) = (@noinline; throw(ArgumentError(s)))
```
-/
-- Source: base/array.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def throwArgument {m : Type → Type} [Monad m] [MonadExceptOf Error m] {α : Type} (s : String) : m α :=
  throw (.argument s)

end

/--
Julia source: base/array.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_copyto2arg!(dest, src) = copyto!(dest, firstindex(dest), src, firstindex(src), length(src))
```
-/
def copyto2arg [Monad m] (firstDest : D → m I) (firstSrc : S → m I)
    (length : S → m I) (copy : D → I → S → I → I → m D) (dest : D) (src : S) : m D := do
  copy dest (← firstDest dest) src (← firstSrc src) (← length src)

/--
Julia source: base/array.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array, src::Array) = _copyto2arg!(dest, src)
```
-/
def copyto325 [Monad m] (firstDest : D → m I) (firstSrc : S → m I)
    (length : S → m I) (copy : D → I → S → I → I → m D) (dest : D) (src : S) : m D :=
  copyto2arg firstDest firstSrc length copy dest src

/--
Julia source: base/array.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array, src::Memory) = _copyto2arg!(dest, src)
```
-/
def copyto326 [Monad m] (firstDest : D → m I) (firstSrc : S → m I)
    (length : S → m I) (copy : D → I → S → I → I → m D) (dest : D) (src : S) : m D :=
  copyto2arg firstDest firstSrc length copy dest src

/--
Julia source: base/array.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Memory, src::Array) = _copyto2arg!(dest, src)
```
-/
def copyto327 [Monad m] (firstDest : D → m I) (firstSrc : S → m I)
    (length : S → m I) (copy : D → I → S → I → I → m D) (dest : D) (src : S) : m D :=
  copyto2arg firstDest firstSrc length copy dest src

/--
Julia source: base/array.jl:330-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array{T}, src::Array{T}) where {T} = _copyto2arg!(dest, src)
```
-/
def copyto330 [Monad m] (firstDest : D → m I) (firstSrc : S → m I)
    (length : S → m I) (copy : D → I → S → I → I → m D) (dest : D) (src : S) : m D :=
  copyto2arg firstDest firstSrc length copy dest src

/--
Julia source: base/array.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array{T}, src::Memory{T}) where {T} = _copyto2arg!(dest, src)
```
-/
def copyto331 [Monad m] (firstDest : D → m I) (firstSrc : S → m I)
    (length : S → m I) (copy : D → I → S → I → I → m D) (dest : D) (src : S) : m D :=
  copyto2arg firstDest firstSrc length copy dest src

/--
Julia source: base/array.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Memory{T}, src::Array{T}) where {T} = _copyto2arg!(dest, src)
```
-/
def copyto332 [Monad m] (firstDest : D → m I) (firstSrc : S → m I)
    (length : S → m I) (copy : D → I → S → I → I → m D) (dest : D) (src : S) : m D :=
  copyto2arg firstDest firstSrc length copy dest src

/--
Julia source: base/array.jl:368-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill!(A::AbstractArray{T}, x) where T
    @inline
    xT = x isa T ? x : convert(T, x)::T
    return _fill!(A, xT)
end
```
-/
def fillBang [Monad m] (alreadyTyped : α → Bool) (asTyped : α → β)
    (convert : α → m β) (fillTyped : A → β → m A) (a : A) (x : α) : m A := do
  let xT ← if alreadyTyped x then pure (asTyped x) else convert x
  fillTyped a xT

/--
Julia source: base/array.jl:373-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fill!(A::AbstractArray{T}, x::T) where T
    for i in eachindex(A)
        A[i] = x
    end
    return A
end
```
-/
-- Source: base/array.jl:373-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def fillTyped [Monad m] [ForIn m Keys K] (eachindex : A → m Keys)
    (set : A → E → K → m Unit) (a : A) (value : E) : m A := do
  for key in (← eachindex a) do
    set a value key
  pure a

/--
Julia source: base/array.jl:402-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _take!(dst::Array{T,N}, src::Array{T,N}) where {T,N}
    if getfield(dst, :ref) !== getfield(src, :ref)
        setfield!(dst, :ref, getfield(src, :ref))
    end
    if getfield(dst, :size) !== getfield(src, :size)
        setfield!(dst, :size, getfield(src, :size))
    end
    return dst
end
```
-/
def takeBang [Monad m] (getRef : A → m R) (sameRef : R → R → Bool)
    (setRef : A → R → m Unit) (getSize : A → m D) (sameSize : D → D → Bool)
    (setSize : A → D → m Unit) (dst src : A) : m A := do
  if !(sameRef (← getRef dst) (← getRef src)) then setRef dst (← getRef src)
  if !(sameSize (← getSize dst) (← getSize src)) then setSize dst (← getSize src)
  pure dst

/--
Julia source: base/array.jl:414-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::Vector{T}) where {T}                    = Vector{T}(undef, size(a,1))
```
-/
def similar414 [Monad m] (size : A → I → m I) (allocate : I → m B) (a : A) : m B := do
  allocate (← size a one)

/--
Julia source: base/array.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::Matrix{T}) where {T}                    = Matrix{T}(undef, size(a,1), size(a,2))
```
-/
def similar415 [Monad m] (size : A → I → m I) (allocate : I → I → m B) (a : A) : m B := do
  allocate (← size a one) (← size a (JInt.wrap .i64 2))

/--
Julia source: base/array.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::Vector{T}, S::Type) where {T}           = Vector{S}(undef, size(a,1))
```
-/
def similar416 [Monad m] (size : A → I → m I) (allocate : I → m B) (a : A) : m B := do
  allocate (← size a one)

/--
Julia source: base/array.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::Matrix{T}, S::Type) where {T}           = Matrix{S}(undef, size(a,1), size(a,2))
```
-/
def similar417 [Monad m] (size : A → I → m I) (allocate : I → I → m B) (a : A) : m B := do
  allocate (← size a one) (← size a (JInt.wrap .i64 2))

/--
Julia source: base/array.jl:418-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::Array{T}, m::Int) where {T}              = Vector{T}(undef, m)
```
-/
def similar418 [Monad m] (allocate : I → m B) (_a : A) (n : I) : m B := allocate n

/--
Julia source: base/array.jl:419-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::Array, T::Type, dims::Dims{N}) where {N} = Array{T,N}(undef, dims)
```
-/
def similar419 [Monad m] (allocate : D → m B) (_a : A) (dims : D) : m B := allocate dims

/--
Julia source: base/array.jl:420-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::Array{T}, dims::Dims{N}) where {T,N}     = Array{T,N}(undef, dims)
```
-/
def similar420 [Monad m] (allocate : D → m B) (_a : A) (dims : D) : m B := allocate dims

/--
Julia source: base/array.jl:421-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{Array{T,N}}, dims::Dims) where {T,N} = similar(Array{T}, dims)
```
-/
def similar421 [Monad m] (similar : D → m A) (dims : D) : m A := similar dims

/--
Julia source: base/array.jl:445-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(::Type{T}, vals...) where T
    @inline
    @_effect_free_terminates_locally_meta
    a = Vector{T}(undef, length(vals))
    if vals isa NTuple
        @_safeindex for i in 1:length(vals)
            a[i] = vals[i]
        end
    else
        # use afoldl to avoid type instability inside loop
        afoldl(1, vals...) do i, v
            @inbounds a[i] = v
            return i + 1
        end
    end
    return a
end
```
-/
def typedLiteral [Monad m] (allocate : I → m A) (set : A → α → I → m A)
    (homogeneous : Bool) (vals : List α) : m A := do
  let a ← allocate (JInt.wrap .i64 vals.length)
  if homogeneous then
    writeValues set a vals
  else
    let (_, a) ← vals.foldlM (fun (i, a) v => do
      let a ← set a v i
      pure (i + one, a)) (one, a)
    pure a

/--
Julia source: base/array.jl:463-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(::Type{Any}, @nospecialize vals...)
    @_effect_free_terminates_locally_meta
    a = Vector{Any}(undef, length(vals))
    @_safeindex for i = 1:length(vals)
        a[i] = vals[i]
    end
    return a
end
```
-/
def anyLiteral [Monad m] (allocate : I → m A) (set : A → α → I → m A)
    (vals : List α) : m A := do
  let a ← allocate (JInt.wrap .i64 vals.length)
  writeValues set a vals

/--
Julia source: base/array.jl:471-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(::Type{Any}) = Vector{Any}()
```
-/
def anyLiteralEmpty [Monad m] (allocate : I → m A) : m A := allocate zero

/--
Julia source: base/array.jl:473-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill!(a::Union{Array{UInt8}, Array{Int8}}, x::Integer)
    ref = a.ref
    t = @_gc_preserve_begin ref
    p = unsafe_convert(Ptr{Cvoid}, ref)
    memset(p, x isa eltype(a) ? x : convert(eltype(a), x), length(a) % UInt)
    @_gc_preserve_end t
    return a
end
```
-/
def fillBytes [Monad m]  (ref : A → m R)
    (preserve : R → m Token) (pointer : R → m P) (isElement : Z → Bool)
    (asElement : Z → β) (convert : Z → m β) (length : A → m I)
    (memset : P → β → JInt .u64 → m Unit) (endPreserve : Token → m Unit)
    (a : A) (x : Z) : m A := do
  let ref ← ref a
  let token ← preserve ref
  let p ← pointer ref
  let byte ← if isElement x then pure (asElement x) else convert x
  memset p byte (JInt.rem .u64 (← length a))
  endPreserve token
  pure a

/--
Julia source: base/array.jl:482-482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_dim(d::Integer) = d
```
-/
def toDimInteger (d : Z) : Z := d

/--
Julia source: base/array.jl:483-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_dim(d::OneTo) = last(d)
```
-/
def toDimOneTo (last : R → Z) (d : R) : Z := last d

-- Declaration without a method body.
-- Source: base/array.jl:581-581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill end
-- /Source

/--
Julia source: base/array.jl:583-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill(v, dims::DimOrInd...) = fill(v, dims)
```
-/
def fillVarargs [Monad m] (fill : α → List D → m A) (v : α) (dims : List D) : m A :=
  fill v dims

/--
Julia source: base/array.jl:584-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill(v, dims::NTuple{N, Union{Integer, OneTo}}) where {N} = fill(v, map(to_dim, dims))
```
-/
def fillMixedDims [Monad m] (toDim : D → Z) (fill : α → List Z → m A)
    (v : α) (dims : List D) : m A := fill v (dims.map toDim)

/--
Julia source: base/array.jl:585-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill(v, dims::NTuple{N, Integer}) where {N} = (a=Array{typeof(v),N}(undef, dims); fill!(a, v); a)
```
-/
def fill585 [Monad m] (allocate : List D → m A) (fill : A → α → m A)
    (v : α) (dims : List D) : m A := do
  let a ← allocate dims
  let _ ← fill a v
  pure a

/--
Julia source: base/array.jl:586-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill(v, dims::NTuple{N, DimOrInd}) where {N} = (a=similar(Array{typeof(v),N}, dims); fill!(a, v); a)
```
-/
def fill586 [Monad m] (allocate : List D → m A) (fill : A → α → m A)
    (v : α) (dims : List D) : m A := do
  let a ← allocate dims
  let _ ← fill a v
  pure a

/--
Julia source: base/array.jl:587-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill(v, dims::Tuple{}) = (a=Array{typeof(v),0}(undef, dims); fill!(a, v); a)
```
-/
def fill587 [Monad m] (allocate : List D → m A) (fill : A → α → m A)
    (v : α) (dims : List D) : m A := do
  let a ← allocate dims
  let _ ← fill a v
  pure a

-- Declaration without a method body.
-- Source: base/array.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function zeros end
-- /Source

-- Declaration without a method body.
-- Source: base/array.jl:629-629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ones end
-- /Source

/--
Julia source: base/array.jl:633-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $fname(dims::DimOrInd...) = $fname(dims)
```
-/
def constantVarargs [Monad m] (constant : List D → m A) (dims : List D) : m A :=
  constant dims

/--
Julia source: base/array.jl:634-634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $fname(::Type{T}, dims::DimOrInd...) where {T} = $fname(T, dims)
```
-/
def constantTypedVarargs [Monad m] (constant : T → List D → m A)
    (t : T) (dims : List D) : m A := constant t dims

/--
Julia source: base/array.jl:635-635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $fname(dims::Tuple{Vararg{DimOrInd}}) = $fname(Float64, dims)
```
-/
def constantDefaultType [Monad m] (float64 : T) (constant : T → D → m A)
    (dims : D) : m A := constant float64 dims

/--
Julia source: base/array.jl:636-636 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $fname(::Type{T}, dims::NTuple{N, Union{Integer, OneTo}}) where {T,N} = $fname(T, map(to_dim, dims))
```
-/
def constantMixedDims [Monad m] (toDim : D → Z) (constant : T → List Z → m A)
    (t : T) (dims : List D) : m A := constant t (dims.map toDim)

/--
Julia source: base/array.jl:637-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function $fname(::Type{T}, dims::NTuple{N, Integer}) where {T,N}
            a = Array{T,N}(undef, dims)
            fill!(a, $felt(T))
            return a
        end
```
-/
def constant637 [Monad m] (allocate : List D → m A) (element : m α)
    (fill : A → α → m A) (dims : List D) : m A := do
  let a ← allocate dims
  let _ ← fill a (← element)
  pure a

/--
Julia source: base/array.jl:642-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function $fname(::Type{T}, dims::Tuple{}) where {T}
            a = Array{T}(undef)
            fill!(a, $felt(T))
            return a
        end
```
-/
def constant642 [Monad m] (allocate : List D → m A) (element : m α)
    (fill : A → α → m A) (dims : List D) : m A := do
  let a ← allocate dims
  let _ ← fill a (← element)
  pure a

/--
Julia source: base/array.jl:647-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function $fname(::Type{T}, dims::NTuple{N, DimOrInd}) where {T,N}
            a = similar(Array{T,N}, dims)
            fill!(a, $felt(T))
            return a
        end
```
-/
def constant647 [Monad m] (allocate : List D → m A) (element : m α)
    (fill : A → α → m A) (dims : List D) : m A := do
  let a ← allocate dims
  let _ ← fill a (← element)
  pure a

/--
Julia source: base/array.jl:657-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, a::AbstractArray) where {T<:Array} = a isa T ? a : T(a)::T
```
-/
def convertArray [Monad m] (alreadyTyped : A → Bool) (asTyped : A → B)
    (constructor : A → m V) (typeassert : V → m B) (a : A) : m B :=
  if alreadyTyped a then pure (asTyped a) else do typeassert (← constructor a)

/--
Julia source: base/array.jl:659-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{Array{T,n}}, b::Type{Array{S,n}}) where {T,n,S} = el_same(promote_type(T,S), a, b)
```
-/
def promoteArrayRule (promoteType : T → T → T) (elSame : T → A → A → A)
    (t s : T) (a b : A) : A := elSame (promoteType t s) a b

/--
Julia source: base/array.jl:664-664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Array{T,N}(x::AbstractArray{S,N})         where {T,N,S} = copyto_axcheck!(Array{T,N}(undef, size(x)), x)
```
-/
def arrayConstructor [Monad m] (size : S → m D) (allocate : D → m A)
    (copyAxcheck : A → S → m A) (x : S) : m A := do
  copyAxcheck (← allocate (← size x)) x

/--
Julia source: base/array.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AbstractArray{T,N}(A::AbstractArray{S,N}) where {T,N,S} = copyto_axcheck!(similar(A,T), A)
```
-/
def abstractArrayConstructor [Monad m] (similar : S → m A)
    (copyAxcheck : A → S → m A) (a : S) : m A := do
  copyAxcheck (← similar a) a

/--
Julia source: base/array.jl:684-684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
collect(::Type{T}, itr) where {T} = _collect(T, itr, IteratorSize(itr))
```
-/
def collectTyped [Monad m] (iteratorSize : X → Size)
    (collect : T → X → Size → m A) (t : T) (itr : X) : m A :=
  collect t itr (iteratorSize itr)

/--
Julia source: base/array.jl:686-687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_collect(::Type{T}, itr, isz::Union{HasLength,HasShape}) where {T} =
    copyto!(_array_for_inner(T, isz, _similar_shape(itr, isz)), itr)
```
-/
def collectSized [Monad m] (similarShape : X → Size → m Shape)
    (arrayForInner : T → Size → Shape → m A) (copyto : A → X → m A)
    (t : T) (itr : X) (isz : Size) : m A := do
  copyto (← arrayForInner t isz (← similarShape itr isz)) itr

/--
Julia source: base/array.jl:688-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _collect(::Type{T}, itr, isz::SizeUnknown) where T
    a = Vector{T}()
    for x in itr
        push!(a, x)
    end
    return a
end
```
-/
def collectUnknown [Monad m] [ForIn m X α] (allocate : m A) (push : A → α → m Unit)
    (itr : X) : m A := do
  let a ← allocate
  for x in itr do push a x
  pure a

/--
Julia source: base/array.jl:697-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c, ::Type{T}, itr, isz, shp) where {T} = similar(c, T)
```
-/
-- Source: base/array.jl:697-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def similarForGeneric [Monad m] (similar : C → T → m A)
    (c : C) (t : T) (_itr : X) (_isz : Size) (_shp : Shape) : m A := similar c t

/--
Julia source: base/array.jl:699-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_shape(itr, ::SizeUnknown) = nothing
```
-/
def similarShapeUnknown (_itr : X) : Option I := none

/--
Julia source: base/array.jl:700-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_shape(itr, ::HasLength) = length(itr)::Integer
```
-/
def similarShapeLength (length : X → Z) (itr : X) : Z := length itr

/--
Julia source: base/array.jl:701-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_shape(itr, ::HasShape) = axes(itr)
```
-/
def similarShapeAxes (axes : X → Axes) (itr : X) : Axes := axes itr

/--
Julia source: base/array.jl:703-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c::AbstractArray, ::Type{T}, itr, ::SizeUnknown, ::Nothing) where {T} =
    similar(c, T, 0)
```
-/
-- Source: base/array.jl:703-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def similarForUnknown [Monad m] (similar : C → T → I → m A)
    (c : C) (t : T) (_itr : X) : m A := similar c t zero

/--
Julia source: base/array.jl:705-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c::AbstractArray, ::Type{T}, itr, ::HasLength, len::Integer) where {T} =
    similar(c, T, len)
```
-/
-- Source: base/array.jl:705-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def similarForLength [Monad m] (similar : C → T → Z → m A)
    (c : C) (ty : T) (_itr : X) (len : Z) : m A := similar c ty len

/--
Julia source: base/array.jl:707-708 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c::AbstractArray, ::Type{T}, itr, ::HasShape, axs) where {T} =
    similar(c, T, axs)
```
-/
-- Source: base/array.jl:707-708 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def similarForAxes [Monad m] (similar : C → T → Axes → m A)
    (c : C) (t : T) (_itr : X) (axes : Axes) : m A := similar c t axes

/--
Julia source: base/array.jl:711-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_array_for_inner(::Type{T}, ::SizeUnknown, ::Nothing) where {T} = Vector{T}(undef, 0)
```
-/
def arrayForUnknown [Monad m] (allocate : T → I → m A) (t : T) : m A := allocate t zero

/--
Julia source: base/array.jl:712-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_array_for_inner(::Type{T}, ::HasLength, len::Integer) where {T} = Vector{T}(undef, Int(len))
```
-/
def arrayForLength [Monad m] (toInt : Z → m I)
    (allocate : T → I → m A) (ty : T) (len : Z) : m A := do
  allocate ty (← toInt len)

/--
Julia source: base/array.jl:713-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_array_for_inner(::Type{T}, ::HasShape{N}, axs) where {T,N} = similar(Array{T,N}, axs)
```
-/
def arrayForShape [Monad m] (similar : T → Axes → m A)
    (t : T) (axes : Axes) : m A := similar t axes

/--
Julia source: base/array.jl:716-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_array_for(::Type{T}, itr, isz) where {T} = _array_for_inner(T, isz, _similar_shape(itr, isz))
```
-/
def arrayFor [Monad m] (shape : X → Size → m Shape)
    (inner : T → Size → Shape → m A) (t : T) (itr : X) (isz : Size) : m A := do
  inner t isz (← shape itr isz)

/--
Julia source: base/array.jl:771-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
collect(itr) = _collect(1:1 #= Array =#, itr, IteratorEltype(itr), IteratorSize(itr))
```
-/
def collect [Monad m] (arrayContainer : C) (eltype : X → ET) (size : X → SZ)
    (collect : C → X → ET → SZ → m A) (itr : X) : m A :=
  collect arrayContainer itr (eltype itr) (size itr)

/--
Julia source: base/array.jl:773-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
collect(A::AbstractArray) = _collect_indices(axes(A), A)
```
-/
def collectArray [Monad m] (axes : A → Axes) (collect : Axes → A → m B)
    (a : A) : m B := collect (axes a) a

/--
Julia source: base/array.jl:775-775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
collect_similar(cont, itr) = _collect(cont, itr, IteratorEltype(itr), IteratorSize(itr))
```
-/
def collectSimilar [Monad m] (eltype : X → ET) (size : X → SZ)
    (collect : C → X → ET → SZ → m A) (cont : C) (itr : X) : m A :=
  collect cont itr (eltype itr) (size itr)

/--
Julia source: base/array.jl:777-778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_collect(cont, itr, ::HasEltype, isz::Union{HasLength,HasShape}) =
    copyto!(_similar_for(cont, eltype(itr), itr, isz, _similar_shape(itr, isz)), itr)
```
-/
def collectKnownSized [Monad m] (eltype : X → T) (shape : X → Size → m Shape)
    (similar : C → T → X → Size → Shape → m A) (copy : A → X → m A)
    (cont : C) (itr : X) (isz : Size) : m A := do
  copy (← similar cont (eltype itr) itr isz (← shape itr isz)) itr

/--
Julia source: base/array.jl:780-786 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _collect(cont, itr, ::HasEltype, isz::SizeUnknown)
    a = _similar_for(cont, eltype(itr), itr, isz, nothing)
    for x in itr
        push!(a,x)
    end
    return a
end
```
-/
def collectKnownUnknown [Monad m] [ForIn m X α] (eltype : X → T)
    (similar : C → T → m A) (push : A → α → m Unit) (cont : C) (itr : X) : m A := do
  let a ← similar cont (eltype itr)
  for x in itr do push a x
  pure a

/--
Julia source: base/array.jl:788-792 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _collect_indices(::Tuple{}, A)
    dest = Array{eltype(A),0}(undef)
    isempty(A) && return dest
    return copyto_unaliased!(IndexStyle(dest), dest, IndexStyle(A), A)
end
```
-/
def collectIndicesZero [Monad m] (allocate : A → m B) (isempty : A → m Bool)
    (destStyle : B → Style) (srcStyle : A → Style)
    (copy : Style → B → Style → A → m B) (a : A) : m B := do
  let dest ← allocate a
  if ← isempty a then return dest
  copy (destStyle dest) dest (srcStyle a) a

/--
Julia source: base/array.jl:793-797 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _collect_indices(indsA::Tuple{Vararg{OneTo}}, A)
    dest = Array{eltype(A)}(undef, length.(indsA))
    isempty(A) && return dest
    return copyto_unaliased!(IndexStyle(dest), dest, IndexStyle(A), A)
end
```
-/
def collectIndicesOneTo [Monad m] (axisLength : Axis → I)
    (allocate : A → List I → m B) (isempty : A → m Bool)
    (destStyle : B → Style) (srcStyle : A → Style)
    (copy : Style → B → Style → A → m B) (axes : List Axis) (a : A) : m B := do
  let dest ← allocate a (axes.map axisLength)
  if ← isempty a then return dest
  copy (destStyle dest) dest (srcStyle a) a

/--
Julia source: base/array.jl:798-801 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _collect_indices(indsA, A)
    B = Array{eltype(A)}(undef, length.(indsA))
    copyto!(B, CartesianIndices(axes(B)), A, CartesianIndices(indsA))
end
```
-/
def collectIndicesGeneric [Monad m] (axisLength : Axis → I)
    (allocate : A → List I → m B) (axes : B → Axes)
    (cartesian : Axes → Indices) (copy : B → Indices → A → Indices → m B)
    (indsA : Axes) (lengths : List Axis) (a : A) : m B := do
  let b ← allocate a (lengths.map axisLength)
  copy b (cartesian (axes b)) a (cartesian indsA)

/--
Julia source: base/array.jl:805-815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _iterator_upper_bound(itr)
    x = iterate(itr)
    while x !== nothing
        val = getfield(x, 1)
        if inferencebarrier(nothing)
            return val
        end
        x = iterate(itr, getfield(x, 2))
    end
    throw(nothing)
end
```
-/
def iteratorUpperBound [Monad m] [MonadExceptOf Error m]
    (itr : FiniteIterator m α St) (barrier : m Barrier) (requireBool : Barrier → m Bool) : m α := do
  let rec loop (value : α) (st : St) : m α := do
    if ← requireBool (← barrier) then return value
    match ← itr.next st with
    | none => throw .thrownNothing
    | some (value, next) => loop value next.val
  termination_by itr.rank st
  match ← itr.first with
  | none => throw .thrownNothing
  | some (value, st) => loop value st

/--
Julia source: base/array.jl:821-831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro default_eltype(itr)
    I = esc(itr)
    return quote
        if $I isa Generator && ($I).f isa Type
            T = ($I).f
        else
            T = Base._return_type(_iterator_upper_bound, Tuple{typeof($I)})
        end
        promote_typejoin_union(T)
    end
end
```
-/
def defaultEltype (isGenerator : X → Bool) (functionIsType : X → Bool)
    (functionType inferredType : X → T) (promoteTypejoinUnion : T → T) (itr : X) : T :=
  let t := if isGenerator itr && functionIsType itr then functionType itr else inferredType itr
  promoteTypejoinUnion t

/--
Julia source: base/array.jl:833-853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function collect(itr::Generator)
    isz = IteratorSize(itr.iter)
    et = @default_eltype(itr)
    if isa(isz, SizeUnknown)
        return grow_to!(Vector{et}(), itr)
    else
        shp = _similar_shape(itr, isz)
        y = iterate(itr)
        if y === nothing
            return _array_for_inner(et, isz, shp)
        end
        v1, st = y
        dest = _array_for_inner(typeof(v1), isz, shp)
        # The typeassert gives inference a helping hand on the element type and dimensionality
        # (work-around for #28382)
        et′ = et <: Type ? Type : et
        RT = !(dest isa AbstractArray) ? Any :
             isconcretetype(et′) ? AbstractArray{et′, ndims(dest)} : AbstractArray{<:et′, ndims(dest)}
        collect_to_with_first!(dest, v1, itr, st)::RT
    end
end
```
-/
def collectGenerator [Monad m] (iteratorSize : X → Size) (defaultEltype : X → T)
    (sizeUnknown : Size → Bool) (emptyVector : T → m A) (grow : A → X → m A)
    (similarShape : X → Size → m Shape) (iterate : X → m (Option (α × St)))
    (typeof : α → T) (arrayForInner : T → Size → Shape → m A)
    (isTypeSubtype : T → Bool) (typeType anyType : T)
    (isAbstractArray : A → Bool) (isConcrete : T → Bool) (ndims : A → I)
    (abstractArrayType : T → I → Bool → T) (collectWithFirst : A → α → X → St → m A)
    (typeassert : A → T → m A) (itr : X) : m A := do
  let isz := iteratorSize itr
  let et := defaultEltype itr
  if sizeUnknown isz then return ← grow (← emptyVector et) itr
  let shp ← similarShape itr isz
  match ← iterate itr with
  | none => arrayForInner et isz shp
  | some (v1, st) =>
    let dest ← arrayForInner (typeof v1) isz shp
    let et' := if isTypeSubtype et then typeType else et
    let rt := if !(isAbstractArray dest) then anyType else
      abstractArrayType et' (ndims dest) (isConcrete et')
    typeassert (← collectWithFirst dest v1 itr st) rt

/--
Julia source: base/array.jl:855-856 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_collect(c, itr, ::EltypeUnknown, isz::SizeUnknown) =
    grow_to!(_similar_for(c, @default_eltype(itr), itr, isz, nothing), itr)
```
-/
def collectEltypeUnknown [Monad m] (defaultEltype : X → T)
    (similar : C → T → X → SZ → m A) (grow : A → X → m A)
    (c : C) (itr : X) (isz : SZ) : m A := do
  grow (← similar c (defaultEltype itr) itr isz) itr

/--
Julia source: base/array.jl:858-873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _collect(c, itr, ::EltypeUnknown, isz::Union{HasLength,HasShape})
    et = @default_eltype(itr)
    shp = _similar_shape(itr, isz)
    y = iterate(itr)
    if y === nothing
        return _similar_for(c, et, itr, isz, shp)
    end
    v1, st = y
    dest = _similar_for(c, typeof(v1), itr, isz, shp)
    # The typeassert gives inference a helping hand on the element type and dimensionality
    # (work-around for #28382)
    et′ = et <: Type ? Type : et
    RT = !(dest isa AbstractArray) ? Any :
         isconcretetype(et′) ? AbstractArray{et′, ndims(dest)} : AbstractArray{<:et′, ndims(dest)}
    collect_to_with_first!(dest, v1, itr, st)::RT
end
```
-/
def collectUnknownSized [Monad m] (defaultEltype : X → T)
    (similarShape : X → Size → m Shape) (iterate : X → m (Option (α × St)))
    (typeof : α → T) (similarFor : C → T → X → Size → Shape → m A)
    (isTypeSubtype : T → Bool) (typeType anyType : T)
    (isAbstractArray : A → Bool) (isConcrete : T → Bool) (ndims : A → I)
    (abstractArrayType : T → I → Bool → T) (collectWithFirst : A → α → X → St → m A)
    (typeassert : A → T → m A) (c : C) (itr : X) (isz : Size) : m A := do
  let et := defaultEltype itr
  let shp ← similarShape itr isz
  match ← iterate itr with
  | none => similarFor c et itr isz shp
  | some (v1, st) =>
    let dest ← similarFor c (typeof v1) itr isz shp
    let et' := if isTypeSubtype et then typeType else et
    let rt := if !(isAbstractArray dest) then anyType else
      abstractArrayType et' (ndims dest) (isConcrete et')
    typeassert (← collectWithFirst dest v1 itr st) rt

/--
Julia source: base/array.jl:875-879 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function collect_to_with_first!(dest::AbstractArray, v1, itr, st)
    i1 = first(LinearIndices(dest))
    dest[i1] = v1
    return collect_to!(dest, itr, i1+1, st)
end
```
-/
def collectWithFirstArray [Monad m] (firstLinear : A → m I)
    (set : A → α → I → m Unit) (collect : A → X → I → St → m A)
    (dest : A) (v1 : α) (itr : X) (st : St) : m A := do
  let i1 ← firstLinear dest
  set dest v1 i1
  collect dest itr (i1 + one) st

/--
Julia source: base/array.jl:881-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function collect_to_with_first!(dest, v1, itr, st)
    push!(dest, v1)
    return grow_to!(dest, itr, st)
end
```
-/
def collectWithFirst [Monad m] (push : A → α → m Unit)
    (grow : A → X → St → m A) (dest : A) (v1 : α) (itr : X) (st : St) : m A := do
  push dest v1
  grow dest itr st

/--
Julia source: base/array.jl:886-893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex_widen_up_to(dest::AbstractArray{T}, el, i) where T
    @inline
    new = similar(dest, promote_typejoin(T, typeof(el)))
    f = first(LinearIndices(dest))
    copyto!(new, first(LinearIndices(new)), dest, f, i-f)
    @inbounds new[i] = el
    return new
end
```
-/
def setindexWiden [Monad m] (promoteJoin : T → T → m T)
    (eltype : A → T) (typeof : α → T) (similar : A → T → m A)
    (firstLinear : A → m I) (copy : A → I → A → I → I → m Unit)
    (set : A → α → I → m Unit) (dest : A) (el : α) (i : I) : m A := do
  let joined ← promoteJoin (eltype dest) (typeof el)
  let new ← similar dest joined
  let f ← firstLinear dest
  copy new (← firstLinear new) dest f (i - f)
  set new el i
  pure new

/--
Julia source: base/array.jl:895-912 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function collect_to!(dest::AbstractArray{T}, itr, offs, st) where T
    # collect to dest array, checking the type of each result. if a result does not
    # match, widen the result type and re-dispatch.
    i = offs
    while true
        y = iterate(itr, st)
        y === nothing && break
        el, st = y
        if el isa T
            @inbounds dest[i] = el
            i += 1
        else
            new = setindex_widen_up_to(dest, el, i)
            return collect_to!(new, itr, i+1, st)
        end
    end
    return dest
end
```
-/
def collectTo [Monad m] (itr : FiniteIterator m α St) (isElement : A → α → Bool)
    (set : A → α → I → m Unit) (widen : A → α → I → m A)
    (dest : A) (offs : I) (st : St) : m A := do
  match ← itr.next st with
  | none => pure dest
  | some (el, next) =>
    if isElement dest el then
      set dest el offs
      collectTo itr isElement set widen dest (offs + one) next.val
    else
      let new ← widen dest el offs
      collectTo itr isElement set widen new (offs + one) next.val
termination_by itr.rank st

/--
Julia source: base/array.jl:914-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function grow_to!(dest, itr)
    y = iterate(itr)
    y === nothing && return dest
    dest2 = empty(dest, typeof(y[1]))
    push!(dest2, y[1])
    grow_to!(dest2, itr, y[2])
end
```
-/
def growFirst [Monad m] (iterate : X → m (Option (α × St)))
    (empty : A → α → m A) (push : A → α → m Unit) (grow : A → X → St → m A)
    (dest : A) (itr : X) : m A := do
  let y ← iterate itr
  match y with
  | none => pure dest
  | some (v, st) =>
    let dest2 ← empty dest v
    push dest2 v
    grow dest2 itr st

/--
Julia source: base/array.jl:922-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push_widen(dest, el)
    @inline
    new = sizehint!(empty(dest, promote_typejoin(eltype(dest), typeof(el))), length(dest))
    if new isa AbstractSet
        # TODO: merge back these two branches when copy! is re-enabled for sets/vectors
        union!(new, dest)
    else
        append!(new, dest)
    end
    push!(new, el)
    return new
end
```
-/
def pushWiden [Monad m] (eltype : A → T) (typeof : α → T)
    (join : T → T → m T) (empty : A → T → m A) (length : A → m I)
    (sizehint : A → I → m A) (isSet : A → Bool)
    (union append : A → A → m Unit) (push : A → α → m Unit)
    (dest : A) (el : α) : m A := do
  let joined ← join (eltype dest) (typeof el)
  let new ← sizehint (← empty dest joined) (← length dest)
  if isSet new then union new dest else append new dest
  push new el
  pure new

/--
Julia source: base/array.jl:935-949 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function grow_to!(dest, itr, st)
    T = eltype(dest)
    y = iterate(itr, st)
    while y !== nothing
        el, st = y
        if el isa T
            push!(dest, el)
        else
            new = push_widen(dest, el)
            return grow_to!(new, itr, st)
        end
        y = iterate(itr, st)
    end
    return dest
end
```
-/
def growTo [Monad m] (itr : FiniteIterator m α St) (isElement : A → α → Bool)
    (push : A → α → m Unit) (widen : A → α → m A)
    (dest : A) (st : St) : m A := do
  match ← itr.next st with
  | none => pure dest
  | some (el, next) =>
    if isElement dest el then
      push dest el
      growTo itr isElement push widen dest next.val
    else
      let new ← widen dest el
      growTo itr isElement push widen new next.val
termination_by itr.rank st

-- Declaration without a method body.
-- Source: base/array.jl:972-972 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex end
-- /Source

/--
Julia source: base/array.jl:974-978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::Array, i1::Int, i2::Int, I::Int...)
    @inline
    @boundscheck checkbounds(A, i1, i2, I...) # generally _to_linear_index requires bounds checking
    return @inbounds A[_to_linear_index(A, i1, i2, I...)]
end
```
-/
def getindexCartesian [Monad m] (bounds : A → List I → m Unit)
    (toLinear : A → List I → m I) (get : A → I → m α)
    (a : A) (i1 i2 : I) (rest : List I) : m α := do
  let indices := i1 :: i2 :: rest
  bounds a indices
  get a (← toLinear a indices)

/--
Julia source: base/array.jl:981-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::Array, I::AbstractUnitRange{<:Integer})
    @inline
    @boundscheck checkbounds(A, I)
    lI = length(I)
    X = similar(A, axes(I))
    if lI > 0
        copyto!(X, firstindex(X), A, first(I), lI)
    end
    return X
end
```
-/
def getindexUnitRange [Monad m] (positive : Z → m Bool) (bounds : A → R → m Unit)
    (length : R → m Z) (axes : R → m Axes) (similar : A → Axes → m A)
    (firstindex : A → m I) (first : R → m F)
    (copy : A → I → A → F → Z → m Unit) (a : A) (r : R) : m A := do
  bounds a r
  let li ← length r
  let x ← similar a (← axes r)
  if ← positive li then copy x (← firstindex x) a (← first r) li
  pure x

/--
Julia source: base/array.jl:993-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(a::Array, r::AbstractUnitRange{Bool}) = getindex(a, to_index(r))
```
-/
def getindexBoolRange [Monad m] (toIndex : R → m Indices)
    (get : A → Indices → m B) (a : A) (r : R) : m B := do
  get a (← toIndex r)

/--
Julia source: base/array.jl:995-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::Array, c::Colon)
    lI = length(A)
    X = similar(A, lI)
    if lI > 0
        unsafe_copyto!(X, 1, A, 1, lI)
    end
    return X
end
```
-/
def getindexColon [Monad m] (length : A → m I) (similar : A → I → m A)
    (copy : A → I → A → I → I → m Unit) (a : A) : m A := do
  let li ← length a
  let x ← similar a li
  if li.val > 0 then copy x one a one li
  pure x

/--
Julia source: base/array.jl:1005-1007 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::Array{S}, I::AbstractRange{Int}) where S
    return S[ A[i] for i in I ]
end
```
-/
def getindexRange [Monad m] (get : A → I → m α)
    (literal : List α → m B) (a : A) (indices : List I) : m B := do
  literal (← indices.mapM (get a))

-- Declaration without a method body.
-- Source: base/array.jl:1029-1029 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setindex! end
-- /Source

/--
Julia source: base/array.jl:1031-1035 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Array{T}, x, i::Int) where {T}
    @_propagate_inbounds_meta
    x = x isa T ? x : convert(T, x)::T
    return _setindex!(A, x, i)
end
```
-/
def setindexScalar [Monad m] (alreadyTyped : α → Bool) (asTyped : α → β)
    (convert : α → m β) (set : A → β → I → m A) (a : A) (x : α) (i : I) : m A := do
  let x ← if alreadyTyped x then pure (asTyped x) else convert x
  set a x i

/--
Julia source: base/array.jl:1036-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(A::Array{T}, x::T, i::Int) where {T}
    @_noub_if_noinbounds_meta
    @boundscheck checkbounds(A, i)
    memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false)
    return A
end
```
-/
def setindexTyped [Monad m] (bounds : A → I → m Unit)
    (memoryrefnew : A → I → Bool → m R) (store : R → α → Bool → m Unit)
    (a : A) (x : α) (i : I) : m A := do
  bounds a i
  store (← memoryrefnew a i false) x false
  pure a

/--
Julia source: base/array.jl:1042-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Array{T}, x, i1::Int, i2::Int, I::Int...) where {T}
    @_propagate_inbounds_meta
    x = x isa T ? x : convert(T, x)::T
    return _setindex!(A, x, i1, i2, I...)
end
```
-/
def setindexCartesian [Monad m] (castElement : α → Option β)
    (convert : α → m Converted) (typeassert : Converted → m β)
    (set : A → β → I → I → List I → m A)
    (a : A) (x : α) (i1 i2 : I) (rest : List I) : m A := do
  let value ← match castElement x with
    | some value => pure value
    | none => typeassert (← convert x)
  set a value i1 i2 rest

/--
Julia source: base/array.jl:1047-1053 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(A::Array{T}, x::T, i1::Int, i2::Int, I::Int...) where {T}
    @inline
    @_noub_if_noinbounds_meta
    @boundscheck checkbounds(A, i1, i2, I...) # generally _to_linear_index requires bounds checking
    memoryrefset!(memoryrefnew(A.ref, _to_linear_index(A, i1, i2, I...), false), x, :not_atomic, false)
    return A
end
```
-/
def setindexCartesianTyped [Monad m] (bounds : A → List I → m Unit)
    (toLinear : A → List I → m I) (memoryrefnew : A → I → Bool → m R)
    (store : R → α → Bool → m Unit) (a : A) (x : α) (i1 i2 : I) (rest : List I) : m A := do
  let indices := i1 :: i2 :: rest
  bounds a indices
  store (← memoryrefnew a (← toLinear a indices) false) x false
  pure a

/--
Julia source: base/array.jl:1055-1056 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__safe_setindex!(A::Vector{Any}, @nospecialize(x), i::Int) = (@inline; @_nothrow_noub_meta;
    memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false); return A)
```
-/
def safeSetindex1055 [Monad m] (memoryrefnew : A → I → Bool → m R)
    (store : R → α → Bool → m Unit) (a : A) (x : α) (i : I) : m A := do
  store (← memoryrefnew a i false) x false
  pure a

/--
Julia source: base/array.jl:1057-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__safe_setindex!(A::Vector{T}, x::T, i::Int) where {T} = (@inline; @_nothrow_noub_meta;
    memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false); return A)
```
-/
def safeSetindex1057 [Monad m] (memoryrefnew : A → I → Bool → m R)
    (store : R → α → Bool → m Unit) (a : A) (x : α) (i : I) : m A := do
  store (← memoryrefnew a i false) x false
  pure a

/--
Julia source: base/array.jl:1059-1060 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__safe_setindex!(A::Vector{T}, x,    i::Int) where {T} = (@inline;
    __safe_setindex!(A, convert(T, x)::T, i))
```
-/
def safeSetindexConvert [Monad m] (convert : α → m β)
    (set : A → β → I → m A) (a : A) (x : α) (i : I) : m A := do
  set a (← convert x) i

/--
Julia source: base/array.jl:1063-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Array, X::AbstractArray, I::AbstractVector{Int})
    @_propagate_inbounds_meta
    setindex_shape_check(X, length(I))
    @boundscheck checkbounds(A, I)
    X′ = unalias(A, X)
    I′ = unalias(A, I)
    k = firstindex(I′)
    for j in eachindex(X′)
        @inbounds A[I′[k]] = X′[j]
        k += 1
    end
    return A
end
```
-/
def setindexVector [Monad m] (shapeCheck : X → I → m Unit) (length : Indices → I)
    (bounds : A → Indices → m Unit) (unaliasValues : A → X → m X)
    (unaliasIndices : A → Indices → m Indices) (first : Indices → m I)
    (eachindex : X → m (List K)) (getIndex : Indices → I → m I)
    (getValue : X → K → m α) (set : A → α → I → m Unit)
    (a : A) (x : X) (indices : Indices) : m A := do
  shapeCheck x (length indices)
  bounds a indices
  let x' ← unaliasValues a x
  let i' ← unaliasIndices a indices
  let mut k ← first i'
  for j in (← eachindex x') do
    let index ← getIndex i' k
    let value ← getValue x' j
    set a value index
    k := k + one
  pure a

/--
Julia source: base/array.jl:1078-1087 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Array{T}, X::Array{T}, I::AbstractUnitRange{Int}) where T
    @inline
    @boundscheck checkbounds(A, I)
    lI = length(I)
    setindex_shape_check(X, lI)
    if lI > 0
        unsafe_copyto!(A, first(I), X, 1, lI)
    end
    return A
end
```
-/
def setindexUnitRange [Monad m] (bounds : A → R → m Unit) (length : R → I)
    (shapeCheck : A → I → m Unit) (first : R → I)
    (copy : A → I → A → I → I → m Unit) (a x : A) (indices : R) : m A := do
  bounds a indices
  let li := length indices
  shapeCheck x li
  if li.val > 0 then copy a (first indices) x one li
  pure a

/--
Julia source: base/array.jl:1088-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Array{T}, X::Array{T}, c::Colon) where T
    @inline
    lI = length(A)
    setindex_shape_check(X, lI)
    if lI > 0
        unsafe_copyto!(A, 1, X, 1, lI)
    end
    return A
end
```
-/
def setindexColon [Monad m] (length : A → m I) (shapeCheck : A → I → m Unit)
    (copy : A → I → A → I → I → m Unit) (a x : A) : m A := do
  let li ← length a
  shapeCheck x li
  if li.val > 0 then copy a one x one li
  pure a

/--
Julia source: base/array.jl:1102-1112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function overallocation(maxsize::Int)
    # compute maxsize = maxsize + 3*maxsize^(7/8) + maxsize/8
    # for small n, we grow faster than O(n)
    # for large n, we grow at O(n/8)
    # and as we reach O(memory) for memory>>1MB,
    # this means we end by adding about 10% of memory each time
    # most commonly, this will take steps of 0-3-9-34 or 1-4-16-66 or 2-8-33
    exp2 = sizeof(maxsize) * 8 - Core.Intrinsics.ctlz_int(maxsize)
    extra = (1 << div(exp2 * 7, 8)) * 3 + div(maxsize, 8)
    return maxsize > typemax(Int) - extra ? typemax(Int) : maxsize + extra
end
```
-/
def overallocation [Monad m] (ctlz : I → I) (divide : I → I → m I)
    (shift : I → I → I) (maxsize : I) : m I := do
  let exp2 := JInt.wrap .i64 64 - ctlz maxsize
  let extra := shift one (← divide (exp2 * JInt.wrap .i64 7) (JInt.wrap .i64 8)) *
    JInt.wrap .i64 3 + (← divide maxsize (JInt.wrap .i64 8))
  let max := JInt.typemax .i64
  pure (if maxsize > max - extra then max else maxsize + extra)

/--
Julia source: base/array.jl:1114-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
array_new_memory(mem::Memory, newlen::Int) = typeof(mem)(undef, newlen) # when implemented, this should attempt to first expand mem
```
-/
def arrayNewMemory [Monad m] (allocate : Mem → I → m Mem) (mem : Mem) (newlen : I) : m Mem :=
  allocate mem newlen

/--
Julia source: base/array.jl:1116-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _growbeg_internal!(a::Vector, delta::Int, len::Int)
    @_terminates_locally_meta
    ref = a.ref
    mem = ref.mem
    offset = memoryrefoffset(ref)
    newlen = checked_add(len, delta)
    memlen = length(mem)
    if offset < 1 || offset - 1 > memlen || len > memlen - (offset - 1)
        throw(ConcurrencyViolationError("Vector has invalid state. Don't modify internal fields incorrectly, or resize without correct locks"))
    end
    # since we will allocate the array in the middle of the memory we need at least 2*delta extra space
    # the +1 is because I didn't want to have an off by 1 error.
    newmemlen = max(overallocation(len), checked_add(len, checked_mul(2, delta), 1))
    newoffset = div(newmemlen - newlen, 2) + 1
    # If there is extra data after the end of the array we can use that space so long as there is enough
    # space at the end that there won't be quadratic behavior with a mix of growth from both ends.
    # Specifically, we want to ensure that we will only do this operation once before
    # increasing the size of the array, and that we leave enough space at both the beginning and the end.
    if newlen < memlen && newoffset < memlen - newlen
        newoffset = div(memlen - newlen, 2) + 1
        newmem = mem
        unsafe_copyto!(newmem, newoffset + delta, mem, offset, len)
        for j in offset:min(newoffset + delta, offset + len)-1
            @inbounds unsetindex!(mem, j)
        end
    else
        newmem = array_new_memory(mem, newmemlen)
        unsafe_copyto!(newmem, newoffset + delta, mem, offset, len)
    end
    if ref !== a.ref
        throw(ConcurrencyViolationError("Vector can not be resized concurrently"))
    end
    setfield!(a, :ref, @inbounds memoryref(newmem, newoffset))
end
```
-/
def growbegInternal [Monad m] [MonadExceptOf Error m]
    (s : Storage m A Mem R) (a : A) (delta len : I) : m Unit := do
  let ref ← s.ref a
  let mem := s.memory ref
  let offset := s.offset ref
  let newlen ← s.checkedAdd len delta
  let memlen ← s.memLength mem
  if offset < one || offset - one > memlen || len > memlen - (offset - one) then
    throw (.concurrency "Vector has invalid state. Don't modify internal fields incorrectly, or resize without correct locks")
  let newmemlen := max (← s.overallocation len)
    (← s.checkedAdd (← s.checkedAdd len (← s.checkedMul (JInt.wrap .i64 2) delta)) one)
  let mut newoffset := (← s.divide (newmemlen - newlen) (JInt.wrap .i64 2)) + one
  let newmem ← if newlen < memlen && newoffset < memlen - newlen then do
      newoffset := (← s.divide (memlen - newlen) (JInt.wrap .i64 2)) + one
      s.copyMemory mem (newoffset + delta) mem offset len
      for j in intRange offset (min (newoffset + delta) (offset + len) - one) do
        s.unsetMemory mem j
      pure mem
    else do
      let newmem ← s.allocate mem newmemlen
      s.copyMemory newmem (newoffset + delta) mem offset len
      pure newmem
  if !(s.sameRef ref (← s.ref a)) then
    throw (.concurrency "Vector can not be resized concurrently")
  s.setRef a (← s.memoryref newmem newoffset)

/--
Julia source: base/array.jl:1151-1169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _growbeg!(a::Vector, delta::Integer)
    @_noub_meta
    delta = Int(delta)
    delta == 0 && return # avoid attempting to index off the end
    delta >= 0 || throw(ArgumentError("grow requires delta >= 0"))
    ref = a.ref
    len = length(a)
    offset = memoryrefoffset(ref)
    newlen = checked_add(len, delta)
    # if offset is far enough advanced to fit data in existing memory without copying
    if delta <= offset - 1
        setfield!(a, :ref, @inbounds memoryref(ref, 1 - delta))
        setfield!(a, :size, (newlen,))
    else
        @noinline _growbeg_internal!(a, delta, len)
        setfield!(a, :size, (newlen,))
    end
    return
end
```
-/
def growbeg [Monad m] [MonadExceptOf Error m] (s : Storage m A Mem R) (toInt : Z → m I)
    (internal : A → I → I → m Unit) (a : A) (d : Z) : m Unit := do
  let delta ← toInt d
  if delta.val = 0 then return
  if !(delta ≥ zero) then throw (.argument "grow requires delta >= 0")
  let ref ← s.ref a
  let len ← s.length a
  let offset := s.offset ref
  let newlen ← s.checkedAdd len delta
  if delta ≤ offset - one then
    s.setRef a (← s.shiftref ref (one - delta))
    s.setSize a newlen
  else
    internal a delta len
    s.setSize a newlen

/--
Julia source: base/array.jl:1171-1210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _growend_internal!(a::Vector, delta::Int, len::Int)
    @_terminates_locally_meta
    ref = a.ref
    mem = ref.mem
    memlen = length(mem)
    newlen = checked_add(len, delta)
    offset = memoryrefoffset(ref)
    if offset < 1 || offset - 1 > memlen || len > memlen - (offset - 1)
        throw(ConcurrencyViolationError("Vector has invalid state. Don't modify internal fields incorrectly, or resize without correct locks"))
    end
    newmemlen = checked_add(offset - 1, newlen)

    if offset - 1 > newlen && offset - 1 - newlen > div(newlen, 4)
        # If the offset is far enough that we can copy without resizing
        # while maintaining proportional spacing on both ends of the array
        # note that this branch prevents infinite growth when doing combinations
        # of push! and popfirst! (i.e. when using a Vector as a queue)
        newmem = mem
        newoffset = div(newlen, 8) + 1
    else
        # grow either by our computed overallocation factor
        # or exactly the requested size, whichever is larger
        # TODO we should possibly increase the offset if the current offset is nonzero.
        newmemlen2 = max(overallocation(memlen), newmemlen)
        newmem = array_new_memory(mem, newmemlen2)
        newoffset = offset
    end
    newref = @inbounds memoryref(newmem, newoffset)
    unsafe_copyto!(newref, ref, len)
    if newmem === mem
        for j in max(offset, newoffset + len):offset+len-1
            @inbounds unsetindex!(mem, j)
        end
    end
    if ref !== a.ref
        @noinline throw(ConcurrencyViolationError("Vector can not be resized concurrently"))
    end
    setfield!(a, :ref, newref)
return
end
```
-/
def growendInternal [Monad m] [MonadExceptOf Error m]
    (s : Storage m A Mem R) (a : A) (delta len : I) : m Unit := do
  let ref ← s.ref a
  let mem := s.memory ref
  let memlen ← s.memLength mem
  let newlen ← s.checkedAdd len delta
  let offset := s.offset ref
  if offset < one || offset - one > memlen || len > memlen - (offset - one) then
    throw (.concurrency "Vector has invalid state. Don't modify internal fields incorrectly, or resize without correct locks")
  else
    let newmemlen ← s.checkedAdd (offset - one) newlen
    let (newmem, newoffset) ←
      if offset - one > newlen && offset - one - newlen > (← s.divide newlen (JInt.wrap .i64 4)) then do
        pure (mem, (← s.divide newlen (JInt.wrap .i64 8)) + one)
      else do
        let newmemlen2 := max (← s.overallocation memlen) newmemlen
        pure ((← s.allocate mem newmemlen2), offset)
    let newref ← s.memoryref newmem newoffset
    s.copyRef newref ref len
    let _ ←
      if s.sameMem newmem mem then do
        for j in intRange (max offset (newoffset + len)) (offset + len - one) do
          s.unsetMemory mem j
      else pure ()
    if !(s.sameRef ref (← s.ref a)) then
      throw (.concurrency "Vector can not be resized concurrently")
    else
      s.setRef a newref

/--
Julia source: base/array.jl:1212-1223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _growend!(a::Vector, delta::Integer)
    @_noub_meta
    delta = Int(delta)
    delta >= 0 || throw(ArgumentError("grow requires delta >= 0"))
    ref = a.ref
    len = length(a)
    if length(ref.mem) - (memoryrefoffset(ref) - 1) - len < delta
        @noinline _growend_internal!(a, delta, len)
    end
    setfield!(a, :size, (len + delta,))
    return
end
```
-/
def growend [Monad m] [MonadExceptOf Error m] (s : Storage m A Mem R) (toInt : Z → m I)
    (internal : A → I → I → m Unit) (a : A) (d : Z) : m Unit := do
  let delta ← toInt d
  if !(delta ≥ zero) then throw (.argument "grow requires delta >= 0")
  let ref ← s.ref a
  let len ← s.length a
  if (← s.memLength (s.memory ref)) - (s.offset ref - one) - len < delta then
    internal a delta len
  s.setSize a (len + delta)

/--
Julia source: base/array.jl:1225-1270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _growat!(a::Vector, i::Integer, delta::Integer)
    @_terminates_globally_noub_meta
    delta = Int(delta)
    i = Int(i)
    i == 1 && return _growbeg!(a, delta)
    len = length(a)
    len < typemax(Int) && i == len + 1 && return _growend!(a, delta)
    delta >= 0 || throw(ArgumentError("grow requires delta >= 0"))
    1 < i <= len || throw(BoundsError(a, i))
    ref = a.ref
    mem = ref.mem
    memlen = length(mem)
    newlen = checked_add(len, delta)
    offset = memoryrefoffset(ref)
    newmemlen = checked_add(offset - 1, newlen)

    # which side would we rather grow into?
    prefer_start = i <= div(len, 2)
    # if offset is far enough advanced to fit data in beginning of the memory
    if prefer_start && delta <= offset - 1
        newref = @inbounds memoryref(mem, offset - delta)
        unsafe_copyto!(newref, ref, i)
        setfield!(a, :ref, newref)
        setfield!(a, :size, (newlen,))
        for j in i:i+delta-1
            @inbounds unsetindex!(a, j)
        end
    elseif !prefer_start && memlen >= newmemlen
        unsafe_copyto!(mem, offset - 1 + delta + i, mem, offset - 1 + i, len - i + 1)
        setfield!(a, :size, (newlen,))
        for j in i:i+delta-1
            @inbounds unsetindex!(a, j)
        end
    else
        # since we will allocate the array in the middle of the memory we need at least 2*delta extra space
        # the +1 is because I didn't want to have an off by 1 error.
        newmemlen = max(overallocation(memlen), checked_add(len, checked_mul(2, delta), 1))
        newoffset = (newmemlen - newlen) ÷ 2 + 1
        newmem = array_new_memory(mem, newmemlen)
        newref = @inbounds memoryref(newmem, newoffset)
        unsafe_copyto!(newref, ref, i-1)
        unsafe_copyto!(newmem, newoffset + delta + i - 1, mem, offset + i - 1, len - i + 1)
        setfield!(a, :ref, newref)
        setfield!(a, :size, (newlen,))
    end
end
```
-/
def growat [Monad m] [MonadExceptOf Error m] 
    (s : Storage m A Mem R) (toDeltaInt : Delta → m I) (toIndexInt : Index → m I)
    (growbeg growend : A → I → m Unit) (a : A) (index : Index) (d : Delta) : m Unit := do
  let delta ← toDeltaInt d
  let i ← toIndexInt index
  if i = one then return ← growbeg a delta
  let len ← s.length a
  if len < JInt.typemax .i64 && i = len + one then return ← growend a delta
  if !(delta ≥ zero) then throw (.argument "grow requires delta >= 0")
  if !(one < i ∧ i ≤ len) then throw .bounds
  let ref ← s.ref a
  let mem := s.memory ref
  let memlen ← s.memLength mem
  let newlen ← s.checkedAdd len delta
  let offset := s.offset ref
  let newmemlen ← s.checkedAdd (offset - one) newlen
  let preferStart := i ≤ (← s.divide len (JInt.wrap .i64 2))
  if preferStart && delta ≤ offset - one then
    let newref ← s.memoryref mem (offset - delta)
    s.copyRef newref ref i
    s.setRef a newref
    s.setSize a newlen
    for j in intRange i (i + delta - one) do s.unsetArray a j
  else if !preferStart && memlen ≥ newmemlen then
    s.copyMemory mem (offset - one + delta + i) mem (offset - one + i) (len - i + one)
    s.setSize a newlen
    for j in intRange i (i + delta - one) do s.unsetArray a j
  else
    let newmemlen := max (← s.overallocation memlen)
      (← s.checkedAdd (← s.checkedAdd len (← s.checkedMul (JInt.wrap .i64 2) delta)) one)
    let newoffset := (← s.divide (newmemlen - newlen) (JInt.wrap .i64 2)) + one
    let newmem ← s.allocate mem newmemlen
    let newref ← s.memoryref newmem newoffset
    s.copyRef newref ref (i - one)
    s.copyMemory newmem (newoffset + delta + i - one) mem (offset + i - one) (len - i + one)
    s.setRef a newref
    s.setSize a newlen

/--
Julia source: base/array.jl:1273-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _deletebeg!(a::Vector, delta::Integer)
    delta = Int(delta)
    len = length(a)
    # See comment in _deleteend!
    if unsigned(delta) > unsigned(len)
        throw(ArgumentError("_deletebeg! requires delta in 0:length(a)"))
    end
    for i in 1:delta
        @inbounds unsetindex!(a, i)
    end
    newlen = len - delta
    setfield!(a, :size, (newlen,))
    if newlen != 0 # if newlen==0 we could accidentally index past the memory
        newref = @inbounds memoryref(a.ref, delta + 1)
        setfield!(a, :ref, newref)
    end
    return
end
```
-/
def deletebeg [Monad m] [MonadExceptOf Error m] (s : Storage m A Mem R) (toInt : Z → m I) (a : A) (d : Z) : m Unit := do
  let delta ← toInt d
  let len ← s.length a
  if JInt.rem .u64 delta > JInt.rem .u64 len then
    throw (.argument "_deletebeg! requires delta in 0:length(a)")
  for i in intRange one delta do s.unsetArray a i
  let newlen := len - delta
  s.setSize a newlen
  if newlen.val != 0 then
    let newref ← s.shiftref (← s.ref a) (delta + one)
    s.setRef a newref

/--
Julia source: base/array.jl:1291-1306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _deleteend!(a::Vector, delta::Integer)
    delta = Int(delta)
    len = length(a)
    # Do the comparison unsigned, to so the compiler knows `len` cannot be negative.
    # This works because if delta is negative, it will overflow and still trigger.
    # This enables the compiler to skip the check sometimes.
    if unsigned(delta) > unsigned(len)
        throw(ArgumentError("_deleteend! requires delta in 0:length(a)"))
    end
    newlen = len - delta
    for i in newlen+1:len
        @inbounds unsetindex!(a, i)
    end
    setfield!(a, :size, (newlen,))
    return
end
```
-/
def deleteend [Monad m] [MonadExceptOf Error m] (s : Storage m A Mem R) (toInt : Z → m I) (a : A) (d : Z) : m Unit := do
  let delta ← toInt d
  let len ← s.length a
  if JInt.rem .u64 delta > JInt.rem .u64 len then
    throw (.argument "_deleteend! requires delta in 0:length(a)")
  let newlen := len - delta
  for i in intRange (newlen + one) len do s.unsetArray a i
  s.setSize a newlen

/--
Julia source: base/array.jl:1307-1322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _deleteat!(a::Vector, i::Integer, delta::Integer)
    i = Int(i)
    len = length(a)
    0 <= delta || throw(ArgumentError("_deleteat! requires delta >= 0"))
    1 <= i <= len || throw(BoundsError(a, i))
    delta <= len + 1 - i || throw(BoundsError(a, i + delta - 1))
    newa = a
    if 2*i + delta <= len
        unsafe_copyto!(newa, 1 + delta, a, 1, i - 1)
        _deletebeg!(a, delta)
    else
        unsafe_copyto!(newa, i, a, i + delta, len + 1 - delta - i)
        _deleteend!(a, delta)
    end
    return
end
```
-/
def deleteatWindow [Monad m] [MonadExceptOf Error m] 
    (toInt : Index → m I) (length : A → m I)
    (deltaValue : Delta → Int)
    (plusDelta : I → Delta → Plus) (minusDelta : I → Delta → Minus)
    (leLength : Plus → I → Bool) (minusIndex : Minus → I → Minus)
    (copyPrefix : A → Plus → A → I → I → m Unit)
    (copySuffix : A → I → A → Plus → Minus → m Unit)
    (deletebeg deleteend : A → Delta → m Unit)
    (a : A) (index : Index) (delta : Delta) : m Unit := do
  let i ← toInt index
  let len ← length a
  if !(0 ≤ deltaValue delta) then throw (.argument "_deleteat! requires delta >= 0")
  if !(one ≤ i ∧ i ≤ len) then throw .bounds
  if !(deltaValue delta ≤ (len + one - i).val) then throw .bounds
  let newa := a
  if leLength (plusDelta (JInt.wrap .i64 2 * i) delta) len then
    copyPrefix newa (plusDelta one delta) a one (i - one)
    deletebeg a delta
  else
    copySuffix newa i a (plusDelta i delta) (minusIndex (minusDelta (len + one) delta) i)
    deleteend a delta

-- Declaration without a method body.
-- Source: base/array.jl:1351-1351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function push! end
-- /Source

/--
Julia source: base/array.jl:1353-1360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(a::Vector{T}, item) where T
    @inline
    # convert first so we don't grow the array if the assignment won't work
    # and also to avoid a dynamic dispatch in the common case that
    # `item` is poorly-typed and `a` is well-typed
    item = item isa T ? item : convert(T, item)::T
    return _push!(a, item)
end
```
-/
def push [Monad m] (alreadyTyped : α → Bool) (asTyped : α → β)
    (convert : α → m β) (pushTyped : A → β → m A) (a : A) (item : α) : m A := do
  let item ← if alreadyTyped item then pure (asTyped item) else convert item
  pushTyped a item

/--
Julia source: base/array.jl:1361-1365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _push!(a::Vector{T}, item::T) where T
    _growend!(a, 1)
    @_safeindex a[length(a)] = item
    return a
end
```
-/
def push1361 [Monad m] (growend : A → I → m Unit)
    (length : A → m I) (set : A → α → I → m Unit) (a : A) (item : α) : m A := do
  growend a one
  set a item (← length a)
  pure a

/--
Julia source: base/array.jl:1368-1372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(a::Vector{Any}, @nospecialize x)
    _growend!(a, 1)
    @_safeindex a[length(a)] = x
    return a
end
```
-/
def push1368 [Monad m] (growend : A → I → m Unit)
    (length : A → m I) (set : A → α → I → m Unit) (a : A) (item : α) : m A := do
  growend a one
  set a item (← length a)
  pure a

/--
Julia source: base/array.jl:1373-1382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(a::Vector{Any}, @nospecialize x...)
    @_terminates_locally_meta
    na = length(a)
    nx = length(x)
    _growend!(a, nx)
    @_safeindex for i = 1:nx
        a[na+i] = x[i]
    end
    return a
end
```
-/
def pushAnyMany [Monad m] (length : A → m I) (growend : A → I → m Unit)
    (set : A → α → I → m Unit) (a : A) (xs : List α) : m A := do
  let na ← length a
  let nx := JInt.wrap .i64 xs.length
  growend a nx
  let mut i := one
  for x in xs do
    set a x (na + i)
    i := i + one
  pure a

-- Declaration without a method body.
-- Source: base/array.jl:1420-1420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function append! end
-- /Source

/--
Julia source: base/array.jl:1422-1428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function append!(a::Vector{T}, items::Union{AbstractVector{<:T},Tuple}) where T
    items isa Tuple && (items = map(x -> convert(T, x), items))
    n = Int(length(items))::Int
    _growend!(a, n)
    copyto!(a, length(a)-n+1, items, firstindex(items), n)
    return a
end
```
-/
def appendVector [Monad m] (isTuple : Items → Bool)
    (convertItems : Items → m Items) (length : Items → m (JInt t))
    (toInt : JInt t → m I) (growend : A → I → m Unit) (arrayLength : A → m I)
    (firstindex : Items → m I) (copy : A → I → Items → I → I → m Unit)
    (a : A) (items : Items) : m A := do
  let items ← if isTuple items then convertItems items else pure items
  let n ← toInt (← length items)
  growend a n
  copy a ((← arrayLength a) - n + one) items (← firstindex items) n
  pure a

/--
Julia source: base/array.jl:1432-1432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
append!(a::AbstractVector, iter...) = (foreach(v -> append!(a, v), iter); a)
```
-/
def appendMany [Monad m] (append : A → X → m Unit) (a : A) (itrs : List X) : m A := do
  for itr in itrs do append a itr
  pure a

/--
Julia source: base/array.jl:1434-1441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _append!(a::AbstractVector, ::Union{HasLength,HasShape}, iter)
    n = Int(length(iter))::Int
    sizehint!(a, length(a) + n; shrink=false)
    for item in iter
        push!(a, item)
    end
    a
end
```
-/
def appendSized [Monad m] [ForIn m X α] (length : X → JInt t) (toInt : JInt t → m I)
    (arrayLength : A → m I) (sizehint : A → I → Bool → m Unit)
    (push : A → α → m Unit) (a : A) (itr : X) : m A := do
  let n ← toInt (length itr)
  sizehint a ((← arrayLength a) + n) false
  for item in itr do push a item
  pure a

/--
Julia source: base/array.jl:1442-1447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _append!(a::AbstractVector, ::IteratorSize, iter)
    for item in iter
        push!(a, item)
    end
    a
end
```
-/
def appendUnsized [Monad m] [ForIn m X α] (push : A → α → m Unit) (a : A) (itr : X) : m A := do
  for item in itr do push a item
  pure a

/-- *dispatch*: `_append!(a, IteratorSize(iter), iter)`: `base/array.jl:1434` for
`Union{HasLength,HasShape}` (`sized`), `:1442` for every other `IteratorSize`. -/
def appendDispatch [Monad m] [ForIn m X α]
    (sized : Size → Bool) (length : X → JInt t) (toInt : JInt t → m I) (arrayLength : A → m I)
    (sizehint : A → I → Bool → m Unit) (push : A → α → m Unit)
    (a : A) (isz : Size) (itr : X) : m A :=
  if sized isz then appendSized length toInt arrayLength sizehint push a itr
  else appendUnsized push a itr

/--
Julia source: base/array.jl:1430-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
append!(a::AbstractVector, iter) = _append!(a, IteratorSize(iter), iter)
```
-/
def appendIterator [Monad m] [ForIn m X α]
    (iteratorSize : X → Size) (sized : Size → Bool) (length : X → JInt t)
    (toInt : JInt t → m I) (arrayLength : A → m I) (sizehint : A → I → Bool → m Unit)
    (push : A → α → m Unit) (a : A) (itr : X) : m A :=
  appendDispatch sized length toInt arrayLength sizehint push a (iteratorSize itr) itr

/-- Method selection for append!(a, tuple), including the Vector specialization. -/
def appendTupleDispatch [Monad m] (isVector : A → Bool)
    (convertItems : List α → m (List α)) (length : List α → I)
    (growend : A → I → m Unit) (arrayLength : A → m I)
    (firstindex : List α → m I)
    (copy : A → I → List α → I → I → m Unit)
    (sizehint : A → I → Bool → m Unit) (push : A → α → m Unit)
    (a : A) (items : List α) : m A :=
  if isVector a then
    appendVector (fun _ => true) convertItems (fun xs => pure (length xs)) pure
      growend arrayLength firstindex copy a items
  else
    appendIterator (fun _ => true) id length pure arrayLength sizehint push a items

/--
Julia source: base/array.jl:1431-1431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(a::AbstractVector, iter...) = append!(a, iter)
```
-/
def pushMany [Monad m] (isVector : A → Bool)
    (convertItems : List α → m (List α)) (length : List α → I)
    (growend : A → I → m Unit) (arrayLength : A → m I)
    (firstindex : List α → m I)
    (copy : A → I → List α → I → I → m Unit)
    (sizehint : A → I → Bool → m Unit) (push : A → α → m Unit)
    (a : A) (items : List α) : m A :=
  appendTupleDispatch isVector convertItems length growend arrayLength firstindex copy
    sizehint push a items

-- Declaration without a method body.
-- Source: base/array.jl:1478-1478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function prepend! end
-- /Source

/--
Julia source: base/array.jl:1480-1493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function prepend!(a::Vector{T}, items::Union{AbstractVector{<:T},Tuple}) where T
    if items isa Tuple
        items = map(x -> convert(T, x), items)
    elseif items !== a
        # growing at the front moves the data of `a`, which a view of `a` would then misread
        items = unalias(a, items)
    end
    n = length(items)
    _growbeg!(a, n)
    # in case of aliasing, the _growbeg might have shifted our data, so copy
    # just the last n elements instead of all of them from the first
    copyto!(a, 1, items, lastindex(items)-n+1, n)
    return a
end
```
-/
def prependVector [Monad m] (isTuple : Items → Bool) (convertItems : Items → m Items)
    (sameArray : Items → A → Bool) (unalias : A → Items → m Items)
    (length : Items → m I) (growbeg : A → I → m Unit) (lastindex : Items → m I)
    (copy : A → I → Items → I → I → m Unit) (a : A) (items : Items) : m A := do
  let items ← if isTuple items then convertItems items
    else if !(sameArray items a) then unalias a items else pure items
  let n ← length items
  growbeg a n
  copy a one items ((← lastindex items) - n + one) n
  pure a

/--
Julia source: base/array.jl:1497-1497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prepend!(a::AbstractVector, iter...) = (for v = reverse(iter); prepend!(a, v); end; return a)
```
-/
def prependMany [Monad m] (prepend : A → X → m Unit) (a : A) (itrs : List X) : m A := do
  for itr in itrs.reverse do prepend a itr
  pure a

/--
Julia source: base/array.jl:1499-1511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _prepend!(a::Vector, ::Union{HasLength,HasShape}, iter)
    @_terminates_locally_meta
    require_one_based_indexing(a)
    n = Int(length(iter))::Int
    sizehint!(a, length(a) + n; first=true, shrink=false)
    n = 0
    for item in iter
        n += 1
        pushfirst!(a, item)
    end
    reverse!(a, 1, n)
    a
end
```
-/
def prependSized [Monad m] [ForIn m X α] (requireOneBased : A → m Unit)
    (length : X → JInt t) (toInt : JInt t → m I) (arrayLength : A → m I)
    (sizehint : A → I → Bool → Bool → m Unit) (pushfirst : A → α → m Unit)
    (reverse : A → I → I → m Unit) (a : A) (itr : X) : m A := do
  requireOneBased a
  let n ← toInt (length itr)
  sizehint a ((← arrayLength a) + n) true false
  let mut n := zero
  for item in itr do
    n := n + one
    pushfirst a item
  reverse a one n
  pure a

/--
Julia source: base/array.jl:1512-1520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _prepend!(a::Vector, ::IteratorSize, iter)
    n = 0
    for item in iter
        n += 1
        pushfirst!(a, item)
    end
    reverse!(a, 1, n)
    a
end
```
-/
def prependUnsized [Monad m] [ForIn m X α] (pushfirst : A → α → m Unit)
    (reverse : A → I → I → m Unit) (a : A) (itr : X) : m A := do
  let mut n := zero
  for item in itr do
    n := n + one
    pushfirst a item
  reverse a one n
  pure a

/-- *dispatch*: `_prepend!(a, IteratorSize(iter), iter)`: `base/array.jl:1499` for
`Union{HasLength,HasShape}` (`sized`), `:1512` for every other `IteratorSize`. -/
def prependDispatch [Monad m] [ForIn m X α]
    (sized : Size → Bool) (requireOneBased : A → m Unit) (length : X → JInt t)
    (toInt : JInt t → m I) (arrayLength : A → m I) (sizehint : A → I → Bool → Bool → m Unit)
    (pushfirst : A → α → m Unit) (reverse : A → I → I → m Unit)
    (a : A) (isz : Size) (itr : X) : m A :=
  if sized isz then
    prependSized requireOneBased length toInt arrayLength sizehint pushfirst reverse a itr
  else prependUnsized pushfirst reverse a itr

/--
Julia source: base/array.jl:1495-1495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prepend!(a::AbstractVector, iter) = _prepend!(a, IteratorSize(iter), iter)
```
-/
def prependIterator [Monad m] [ForIn m X α]
    (iteratorSize : X → Size) (sized : Size → Bool) (requireOneBased : A → m Unit)
    (length : X → JInt t) (toInt : JInt t → m I) (arrayLength : A → m I)
    (sizehint : A → I → Bool → Bool → m Unit) (pushfirst : A → α → m Unit)
    (reverse : A → I → I → m Unit) (a : A) (itr : X) : m A :=
  prependDispatch sized requireOneBased length toInt arrayLength sizehint pushfirst reverse a
    (iteratorSize itr) itr

/-- Method selection for prepend!(a, tuple), including the Vector specialization. -/
def prependTupleDispatch [Monad m] (isVector : A → Bool)
    (convertItems : List α → m (List α)) (length : List α → I)
    (growbeg : A → I → m Unit) (lastindex : List α → m I)
    (copy : A → I → List α → I → I → m Unit)
    (requireOneBased : A → m Unit) (arrayLength : A → m I)
    (sizehint : A → I → Bool → Bool → m Unit) (pushfirst : A → α → m Unit)
    (reverse : A → I → I → m Unit) (a : A) (items : List α) : m A :=
  if isVector a then
    prependVector (fun _ => true) convertItems (fun _ _ => false)
      (fun a xs => pure (JuliaLean.base.abstractarray.unaliasOther a xs))
      (fun xs => pure (length xs)) growbeg lastindex copy a items
  else
    prependIterator (fun _ => true) id requireOneBased length pure arrayLength sizehint
      pushfirst reverse a items

/--
Julia source: base/array.jl:1496-1496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pushfirst!(a::AbstractVector, iter...) = prepend!(a, iter)
```
-/
def pushfirstMany [Monad m] (isVector : A → Bool)
    (convertItems : List α → m (List α)) (length : List α → I)
    (growbeg : A → I → m Unit) (lastindex : List α → m I)
    (copy : A → I → List α → I → I → m Unit)
    (requireOneBased : A → m Unit) (arrayLength : A → m I)
    (sizehint : A → I → Bool → Bool → m Unit) (pushfirst : A → α → m Unit)
    (reverse : A → I → I → m Unit) (a : A) (items : List α) : m A :=
  prependTupleDispatch isVector convertItems length growbeg lastindex copy requireOneBased
    arrayLength sizehint pushfirst reverse a items

/--
Julia source: base/array.jl:1559-1574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function resize!(a::Vector, nl_::Integer; first::Bool=false)
    nl = Int(nl_)::Int
    l = length(a)
    if nl > l
        # Since l is positive, if nl > l, both are positive, and so nl-l is also
        # positive. But the compiler does not know that, so we mask out top bit.
        # This allows the compiler to skip the check
        first ? _growbeg!(a, (nl-l) & typemax(Int)) : _growend!(a, (nl-l) & typemax(Int))
    elseif nl != l
        if nl < 0
            _throw_argerror("new length must be ≥ 0")
        end
        first ? _deletebeg!(a, l-nl) : _deleteend!(a, l-nl)
    end
    return a
end
```
-/
def resize [Monad m] [MonadExceptOf Error m] (toInt : Z → m I) (length : A → m I) (andInt : I → I → I)
    (growbeg growend deletebeg deleteend : A → I → m Unit)
    (a : A) (nl' : Z) (first : Bool := false) : m A := do
  let nl ← toInt nl'
  let l ← length a
  if nl > l then
    let d := andInt (nl - l) (JInt.typemax .i64)
    if first then growbeg a d else growend a d
  else if nl != l then
    if nl < zero then throw (.argument "new length must be ≥ 0")
    if first then deletebeg a (l - nl) else deleteend a (l - nl)
  pure a

-- Declaration without a method body.
-- Source: base/array.jl:1610-1610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sizehint! end
-- /Source

/--
Julia source: base/array.jl:1612-1643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sizehint!(a::Vector, sz::Integer; first::Bool=false, shrink::Bool=true)
    len = length(a)
    ref = a.ref
    mem = ref.mem
    memlen = length(mem)
    sz = max(Int(sz), len)
    inc = sz - len
    if sz <= memlen
        # if we don't save at least 1/8th memlen then its not worth it to shrink
        if !shrink || memlen - sz <= div(memlen, 8)
            return a
        end
        newmem = array_new_memory(mem, sz)
        if first && len != 0
            newref = memoryref(newmem, inc + 1)
        else
            newref = memoryref(newmem)
        end
        unsafe_copyto!(newref, ref, len)
        setfield!(a, :ref, newref)
    elseif first
        _growbeg!(a, inc)
        newref = getfield(a, :ref)
        newref = memoryref(newref, inc + 1)
        setfield!(a, :size, (len,)) # undo the size change from _growbeg!
        setfield!(a, :ref, newref) # undo the offset change from _growbeg!
    else # last
        _growend!(a, inc)
        setfield!(a, :size, (len,)) # undo the size change from _growend!
    end
    a
end
```
-/
def sizehint [Monad m] (s : Storage m A Mem R)
    (toInt : Z → m I) (growbeg growend : A → I → m Unit)
    (a : A) (sz : Z) (first : Bool := false) (shrink : Bool := true) : m A := do
  let len ← s.length a
  let ref ← s.ref a
  let mem := s.memory ref
  let memlen ← s.memLength mem
  let sz := max (← toInt sz) len
  let inc := sz - len
  if sz ≤ memlen then
    if !shrink || memlen - sz ≤ (← s.divide memlen (JInt.wrap .i64 8)) then return a
    let newmem ← s.allocate mem sz
    let newref ← if first && len.val != 0 then s.memoryref newmem (inc + one)
      else s.memoryref newmem one
    s.copyRef newref ref len
    s.setRef a newref
  else if first then
    growbeg a inc
    let newref ← s.ref a
    let newref ← s.shiftref newref (inc + one)
    s.setSize a len
    s.setRef a newref
  else
    growend a inc
    s.setSize a len
  pure a

/--
Julia source: base/array.jl:1647-1652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Core.kwcall(kwargs::NamedTuple{names}, ::typeof(sizehint!), a, sz) where names
    get(kwargs, :first, false)::Bool
    get(kwargs, :shrink, true)::Bool
    isempty(diff_names(names, (:first, :shrink))) || kwerr(kwargs, sizehint!, a, sz)
    sizehint!(a, sz)
end
```
-/
def sizehintKwcall [Monad m] (getBool : KW → String → Bool → m Bool)
    (unknownNames : KW → List String) (kwerr : KW → A → Z → m Unit)
    (sizehint : A → Z → m A) (kwargs : KW) (a : A) (sz : Z) : m A := do
  let _ ← getBool kwargs "first" false
  let _ ← getBool kwargs "shrink" true
  if !(unknownNames kwargs).isEmpty then kwerr kwargs a sz
  sizehint a sz

/--
Julia source: base/array.jl:1695-1702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(a::Vector)
    if isempty(a)
        _throw_argerror("array must be non-empty")
    end
    item = a[end]
    _deleteend!(a, 1)
    return item
end
```
-/
def pop [Monad m] [MonadExceptOf Error m] (isempty : A → m Bool)
    (lastindex : A → m I) (get : A → I → m α) (deleteend : A → I → m Unit)
    (a : A) : m α := do
  if ← isempty a then throw (.argument "array must be non-empty")
  let item ← get a (← lastindex a)
  deleteend a one
  pure item

/--
Julia source: base/array.jl:1736-1741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function popat!(a::Vector, i::Integer)
    @_propagate_inbounds_meta
    x = a[i]
    _deleteat!(a, i, 1)
    x
end
```
-/
def popat [Monad m] (get : A → Z → m α)
    (deleteat : A → Z → I → m Unit) (a : A) (i : Z) : m α := do
  let x ← get a i
  deleteat a i one
  pure x

/--
Julia source: base/array.jl:1743-1751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function popat!(a::Vector, i::Integer, default)
    if 1 <= i <= length(a)
        x = @inbounds a[i]
        _deleteat!(a, i, 1)
        x
    else
        default
    end
end
```
-/
def popatDefault [Monad m] (length : A → m I) (value : Z → Int)
    (get : A → Z → m α) (deleteat : A → Z → I → m Unit)
    (a : A) (i : Z) (default : α) : m α := do
  if 1 ≤ value i ∧ value i ≤ (← length a).val then
    let x ← get a i
    deleteat a i one
    pure x
  else pure default

/--
Julia source: base/array.jl:1772-1776 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pushfirst!(a::Vector{T}, item) where T
    @inline
    item = item isa T ? item : convert(T, item)::T
    return _pushfirst!(a, item)
end
```
-/
def pushfirst [Monad m] (alreadyTyped : α → Bool) (asTyped : α → β)
    (convert : α → m β) (pushTyped : A → β → m A) (a : A) (item : α) : m A := do
  let item ← if alreadyTyped item then pure (asTyped item) else convert item
  pushTyped a item

/--
Julia source: base/array.jl:1777-1781 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _pushfirst!(a::Vector{T}, item::T) where T
    _growbeg!(a, 1)
    @_safeindex a[1] = item
    return a
end
```
-/
def pushfirst1777 [Monad m] (growbeg : A → I → m Unit)
    (set : A → α → I → m Unit) (a : A) (item : α) : m A := do
  growbeg a one
  set a item one
  pure a

/--
Julia source: base/array.jl:1784-1788 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pushfirst!(a::Vector{Any}, @nospecialize x)
    _growbeg!(a, 1)
    @_safeindex a[1] = x
    return a
end
```
-/
def pushfirst1784 [Monad m] (growbeg : A → I → m Unit)
    (set : A → α → I → m Unit) (a : A) (item : α) : m A := do
  growbeg a one
  set a item one
  pure a

/--
Julia source: base/array.jl:1789-1797 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pushfirst!(a::Vector{Any}, @nospecialize x...)
    @_terminates_locally_meta
    nx = length(x)
    _growbeg!(a, nx)
    @_safeindex for i = 1:nx
        a[i] = x[i]
    end
    return a
end
```
-/
def pushfirstAnyMany [Monad m] (growbeg : A → I → m Unit)
    (set : A → α → I → m Unit) (a : A) (xs : List α) : m A := do
  let nx := JInt.wrap .i64 xs.length
  growbeg a nx
  let mut i := one
  for x in xs do
    set a x i
    i := i + one
  pure a

/--
Julia source: base/array.jl:1831-1838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function popfirst!(a::Vector)
    if isempty(a)
        _throw_argerror("array must be non-empty")
    end
    item = a[1]
    _deletebeg!(a, 1)
    return item
end
```
-/
def popfirst [Monad m] [MonadExceptOf Error m] (isempty : A → m Bool)
    (get : A → I → m α) (deletebeg : A → I → m Unit) (a : A) : m α := do
  if ← isempty a then throw (.argument "array must be non-empty")
  let item ← get a one
  deletebeg a one
  pure item

/--
Julia source: base/array.jl:1861-1865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function insert!(a::Vector{T}, i::Integer, item) where T
    @_propagate_inbounds_meta
    item = item isa T ? item : convert(T, item)::T
    return _insert!(a, i, item)
end
```
-/
def insert [Monad m] (alreadyTyped : α → Bool) (asTyped : α → β)
    (convert : α → m β) (insertTyped : A → Z → β → m A)
    (a : A) (i : Z) (item : α) : m A := do
  let item ← if alreadyTyped item then pure (asTyped item) else convert item
  insertTyped a i item

/--
Julia source: base/array.jl:1866-1873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _insert!(a::Vector{T}, i::Integer, item::T) where T
    @_noub_meta
    # Throw convert error before changing the shape of the array
    _growat!(a, i, 1)
    # :noub, because _growat! already did bound check
    @inbounds a[i] = item
    return a
end
```
-/
def insertTyped [Monad m] (growat : A → Z → I → m Unit)
    (set : A → α → Z → m Unit) (a : A) (i : Z) (item : α) : m A := do
  growat a i one
  set a item i
  pure a

/--
Julia source: base/array.jl:1894-1898 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deleteat!(a::Vector, i::Integer)
    i isa Bool && depwarn("passing Bool as an index is deprecated", :deleteat!)
    _deleteat!(a, i, 1)
    return a
end
```
-/
def deleteatIndex [Monad m] (isBool : Z → Bool)
    (depwarn : String → String → m Unit) (deleteat : A → Z → I → m Unit)
    (a : A) (i : Z) : m A := do
  if isBool i then depwarn "passing Bool as an index is deprecated" "deleteat!"
  deleteat a i one
  pure a

/--
Julia source: base/array.jl:1900-1909 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deleteat!(a::Vector, r::AbstractUnitRange{<:Integer})
    if eltype(r) === Bool
        return invoke(deleteat!, Tuple{Vector, AbstractVector{Bool}}, a, r)
    else
        f = first(r)
        f isa Bool && depwarn("passing Bool as an index is deprecated", :deleteat!)
        isempty(r) || _deleteat!(a, f, length(r))
        return a
    end
end
```
-/
def deleteatRange [Monad m]  (boolElement : R → Bool)
    (invokeMask : A → R → m A) (first : R → Index) (isBool : Index → Bool)
    (depwarn : String → String → m Unit) (isempty : R → Bool)
    (length : R → Count) (deleteat : A → Index → Count → m Unit)
    (a : A) (r : R) : m A := do
  if boolElement r then return ← invokeMask a r
  let f := first r
  if isBool f then depwarn "passing Bool as an index is deprecated" "deleteat!"
  if !(isempty r) then deleteat a f (length r)
  pure a

/--
Julia source: base/array.jl:1944-1944 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(::Nowhere, _) = nothing
```
-/
def pushNowhere (_value : α) : Unit := ()

/--
Julia source: base/array.jl:1945-1945 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_growend!(::Nowhere, _) = nothing
```
-/
def growendNowhere (_delta : Z) : Unit := ()

/--
Julia source: base/array.jl:1947-1954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _push_deleted!(dltd, a::Vector, ind)
    @_propagate_inbounds_meta
    if isassigned(a, ind)
        push!(dltd, a[ind])
    else
        _growend!(dltd, 1)
    end
end
```
-/
def pushDeleted [Monad m] (isassigned : A → Z → m Bool) (get : A → Z → m α)
    (push : D → α → m Unit) (growend : D → I → m Unit)
    (dltd : D) (a : A) (index : Z) : m Unit := do
  if ← isassigned a index then push dltd (← get a index) else growend dltd one

/--
Julia source: base/array.jl:1956-1963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _copy_item!(a::Vector, p, q)
    @_propagate_inbounds_meta
    if isassigned(a, q)
        a[p] = a[q]
    else
        unsetindex!(a, p)
    end
end
```
-/
def copyItem [Monad m] (isassigned : A → Z → m Bool) (get : A → Z → m α)
    (set : A → α → Z → m Unit) (unset : A → Z → m Unit)
    (a : A) (p q : Z) : m Unit := do
  if ← isassigned a q then set a (← get a q) p else unset a p

/--
Julia source: base/array.jl:1965-1997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _deleteat!(a::Vector, inds, dltd=Nowhere())
    n = length(a)
    y = iterate(inds)
    y === nothing && return a
    (p, s) = y
    checkbounds(a, p)
    @inbounds _push_deleted!(dltd, a, p)
    q = p+1
    while true
        y = iterate(inds, s)
        y === nothing && break
        (i,s) = y
        if !(q <= i <= n)
            if i < q
                _throw_argerror("indices must be unique and sorted")
            else
                throw(BoundsError())
            end
        end
        while q < i
            @inbounds _copy_item!(a, p, q)
            p += 1; q += 1
        end
        @inbounds _push_deleted!(dltd, a, i)
        q = i+1
    end
    while q <= n
        @inbounds _copy_item!(a, p, q)
        p += 1; q += 1
    end
    _deleteend!(a, n-p+1)
    return a
end
```
-/
def deleteatIterator [Monad m] [MonadExceptOf Error m]
    (length : A → m I) (inds : FiniteIterator m Z St)
    (value : Z → Int) (inc : Z → Z) (bounds : A → Z → m Unit)
    (pushDeleted : D → A → Z → m Unit) (copyItem : A → Z → Z → m Unit)
    (subtract : I → Z → I) (deleteend : A → I → m Unit)
    (a : A) (dltd : D) : m A := do
  let n ← length a
  match ← inds.first with
  | none => pure a
  | some (initial, state) =>
    bounds a initial
    pushDeleted dltd a initial
    let rec loop (p q : Z) (st : St) : m (Z × Z) := do
      match ← inds.next st with
      | none => pure (p, q)
      | some (i, next) =>
        if !(value q ≤ value i ∧ value i ≤ n.val) then
          if value i < value q then throw (.argument "indices must be unique and sorted")
          else throw .bounds
        let mut p := p
        let mut q := q
        for _ in List.range (value i - value q).toNat do
          copyItem a p q
          p := inc p
          q := inc q
        pushDeleted dltd a i
        loop p (inc i) next.val
    termination_by inds.rank st
    let (p, q) ← loop initial (inc initial) state
    let mut p := p
    let mut q := q
    for _ in List.range (n.val - value q + 1).toNat do
      copyItem a p q
      p := inc p
      q := inc q
    deleteend a (subtract n p + one)
    pure a

/--
Julia source: base/array.jl:1940-1940 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deleteat!(a::Vector, inds) = _deleteat!(a, inds)
```
-/
def deleteatIndices [Monad m] [MonadExceptOf Error m]
    (length : A → m I) (iterate : Indices → FiniteIterator m Z St)
    (value : Z → Int) (inc : Z → Z) (bounds : A → Z → m Unit)
    (isassigned : A → Z → m Bool) (get : A → Z → m α)
    (set : A → α → Z → m Unit) (unset : A → Z → m Unit)
    (subtract : I → Z → I) (deleteend : A → I → m Unit) (a : A) (inds : Indices) : m A :=
  deleteatIterator length (iterate inds) value inc bounds
    (pushDeleted isassigned get (fun (_ : Unit) x => pure (pushNowhere x))
      (fun (_ : Unit) d => pure (growendNowhere d)))
    (copyItem isassigned get set unset) subtract deleteend a ()

/--
Julia source: base/array.jl:1941-1941 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deleteat!(a::Vector, inds::AbstractVector) = _deleteat!(a, to_indices(a, (inds,))[1])
```
-/
def deleteatIndexVector [Monad m] [MonadExceptOf Error m]
    (toIndices : A → Indices → m Converted) (first : Converted → Index)
    (length : A → m I) (iterate : Index → FiniteIterator m Z St)
    (value : Z → Int) (inc : Z → Z) (bounds : A → Z → m Unit)
    (isassigned : A → Z → m Bool) (get : A → Z → m α)
    (set : A → α → Z → m Unit) (unset : A → Z → m Unit)
    (subtract : I → Z → I) (deleteend : A → I → m Unit) (a : A) (inds : Indices) : m A := do
  deleteatIterator length (iterate (first (← toIndices a inds))) value inc bounds
    (pushDeleted isassigned get (fun (_ : Unit) x => pure (pushNowhere x))
      (fun (_ : Unit) d => pure (growendNowhere d)))
    (copyItem isassigned get set unset) subtract deleteend a ()

/--
Julia source: base/array.jl:2000-2010 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deleteat!(a::Vector, inds::AbstractVector{Bool})
    n = length(a)
    length(inds) == n || throw(BoundsError(a, inds))
    p = 1
    for (q, i) in enumerate(inds)
        @inbounds _copy_item!(a, p, q)
        p += !i
    end
    _deleteend!(a, n-p+1)
    return a
end
```
-/
def deleteatMask [Monad m] [MonadExceptOf Error m] (length : A → m I)
    (copyItem : A → I → I → m Unit) (deleteend : A → I → m Unit)
    (a : A) (mask : List Bool) : m A := do
  let n ← length a
  if (mask.length : Int) != n.val then throw .bounds
  let mut p := one
  let mut q := one
  for i in mask do
    copyItem a p q
    p := p + (if !i then one else zero)
    q := q + one
  deleteend a (n - p + one)
  pure a

/--
Julia source: base/array.jl:2065-2081 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function splice!(a::Vector, i::Integer, ins=_default_splice)
    v = a[i]
    m = length(ins)
    if m == 0
        _deleteat!(a, i, 1)
    elseif m == 1
        a[i] = only(ins)
    else
        _growat!(a, i, m-1)
        k = 1
        for x in ins
            a[i+k-1] = x
            k += 1
        end
    end
    return v
end
```
-/
def spliceIndex [Monad m] [ForIn m Ins β] (get : A → Z → m α) (length : Ins → I)
    (deleteat growat : A → Z → I → m Unit) (only : Ins → m β)
    (set : A → β → Z → m Unit) (add : Z → I → Z) (subtractOne : Z → Z)
    (a : A) (i : Z) (ins : Ins) : m α := do
  let v ← get a i
  let n := length ins
  if n = zero then deleteat a i one
  else if n = one then set a (← only ins) i
  else
    growat a i (n - one)
    let mut k := one
    for x in ins do
      set a x (subtractOne (add i k))
      k := k + one
  pure v

/--
Julia source: base/array.jl:2120-2146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function splice!(a::Vector, r::AbstractUnitRange{<:Integer}, ins=_default_splice)
    v = a[r]
    m = length(ins)
    if m == 0
        deleteat!(a, r)
        return v
    end

    n = length(a)
    f = first(r)
    l = last(r)
    d = length(r)

    if m < d
        delta = d - m
        _deleteat!(a, (f - 1 < n - l) ? f : (l - delta + 1), delta)
    elseif m > d
        _growat!(a, (f - 1 < n - l) ? f : (l + 1), m - d)
    end

    k = 1
    for x in ins
        a[f+k-1] = x
        k += 1
    end
    return v
end
```
-/
def spliceRange [Monad m] [ForIn m Ins α] (get : A → R → m B)
    (insLength : Ins → I) (deleteRange : A → R → m Unit) (length : A → m I)
    (first last : R → Index) (rangeLength : R → Count) (countValue : Count → Int)
    (leftDistance : Index → I → Distance) (rightDistance : I → Index → Distance)
    (distanceLess : Distance → Distance → Bool)
    (subtractLeft : Count → I → Delta) (subtractRight : I → Count → Delta)
    (subtractIndex : Index → Delta → Index) (addOne : Index → Index)
    (addIndex : Index → I → WriteIndex) (subtractOne : WriteIndex → WriteIndex)
    (deleteat growat : A → Index → Delta → m Unit) (set : A → α → WriteIndex → m Unit)
    (a : A) (r : R) (ins : Ins) : m B := do
  let v ← get a r
  let m := insLength ins
  if m = zero then
    deleteRange a r
    return v
  let n ← length a
  let f := first r
  let l := last r
  let d := rangeLength r
  if m.val < countValue d then
    let delta := subtractLeft d m
    deleteat a (if distanceLess (leftDistance f one) (rightDistance n l)
      then f else addOne (subtractIndex l delta)) delta
  else if m.val > countValue d then
    growat a (if distanceLess (leftDistance f one) (rightDistance n l)
      then f else addOne l) (subtractRight m d)
  let mut k := one
  for x in ins do
    set a x (subtractOne (addIndex f k))
    k := k + one
  pure v

/--
Julia source: base/array.jl:2148-2148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
splice!(a::Vector, inds) = (dltds = eltype(a)[]; _deleteat!(a, inds, dltds); dltds)
```
-/
def spliceIndices [Monad m] [MonadExceptOf Error m]
    (empty : A → m D) (length : A → m I) (iterate : Indices → FiniteIterator m Z St)
    (value : Z → Int) (inc : Z → Z) (bounds : A → Z → m Unit)
    (isassigned : A → Z → m Bool) (get : A → Z → m α)
    (push : D → α → m Unit) (growend : D → I → m Unit)
    (set : A → α → Z → m Unit) (unset : A → Z → m Unit)
    (subtract : I → Z → I) (deleteend : A → I → m Unit) (a : A) (inds : Indices) : m D := do
  let dltds ← empty a
  let _ ← deleteatIterator length (iterate inds) value inc bounds
    (pushDeleted isassigned get push growend) (copyItem isassigned get set unset) subtract
    deleteend a dltds
  pure dltds

/--
Julia source: base/array.jl:2150-2153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(a::Vector)
    _deleteend!(a, length(a))
    return a
end
```
-/
def empty [Monad m] (length : A → m I) (deleteend : A → I → m Unit) (a : A) : m A := do
  deleteend a (← length a)
  pure a

/--
Julia source: base/array.jl:2156-2167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cmp(a::Array{UInt8,1}, b::Array{UInt8,1})
    aref = a.ref
    bref = b.ref
    ta = @_gc_preserve_begin aref
    tb = @_gc_preserve_begin bref
    pa = unsafe_convert(Ptr{Cvoid}, aref)
    pb = unsafe_convert(Ptr{Cvoid}, bref)
    c = memcmp(pa, pb, min(length(a),length(b)))
    @_gc_preserve_end ta
    @_gc_preserve_end tb
    return c < 0 ? -1 : c > 0 ? +1 : cmp(length(a),length(b))
end
```
-/
def cmpBytes [Monad m] (ref : A → m R) (preserve : R → m Token)
    (pointer : R → m P) (length : A → m I) (memcmp : P → P → I → m I)
    (endPreserve : Token → m Unit) (cmpLength : I → I → m I) (a b : A) : m I := do
  let aref ← ref a
  let bref ← ref b
  let ta ← preserve aref
  let tb ← preserve bref
  let pa ← pointer aref
  let pb ← pointer bref
  let c ← memcmp pa pb (min (← length a) (← length b))
  endPreserve ta
  endPreserve tb
  if c.val < 0 then pure (JInt.wrap .i64 (-1))
  else if c.val > 0 then pure one else cmpLength (← length a) (← length b)

/--
Julia source: base/array.jl:2171-2186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(a::Arr, b::Arr) where {Arr <: BitIntegerArray}
    if size(a) == size(b)
        aref = a.ref
        bref = b.ref
        ta = @_gc_preserve_begin aref
        tb = @_gc_preserve_begin bref
        pa = unsafe_convert(Ptr{Cvoid}, aref)
        pb = unsafe_convert(Ptr{Cvoid}, bref)
        c = memcmp(pa, pb, sizeof(eltype(Arr)) * length(a))
        @_gc_preserve_end ta
        @_gc_preserve_end tb
        return c == 0
    else
        return false
    end
end
```
-/
def equalBitInteger2171 [Monad m] (shape : A → m D) (sameShape : D → D → Bool)
    (ref : A → m R) (preserve : R → m Token) (pointer : R → m P)
    (length : A → m I) (elementSize : I) (memcmp : P → P → I → m I)
    (endPreserve : Token → m Unit) (a b : A) : m Bool := do
  if sameShape (← shape a) (← shape b) then
    let aref ← ref a
    let bref ← ref b
    let ta ← preserve aref
    let tb ← preserve bref
    let pa ← pointer aref
    let pb ← pointer bref
    let c ← memcmp pa pb (elementSize * (← length a))
    endPreserve ta
    endPreserve tb
    pure (c.val == 0)
  else pure false

/--
Julia source: base/array.jl:2188-2205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(a::Arr, b::Arr) where Arr <: BitIntegerArray{1}
    len = length(a)
    if len == length(b)
        aref = a.ref
        bref = b.ref
        ta = @_gc_preserve_begin aref
        tb = @_gc_preserve_begin bref
        T = eltype(Arr)
        pa = unsafe_convert(Ptr{T}, aref)
        pb = unsafe_convert(Ptr{T}, bref)
        c = memcmp(pa, pb, sizeof(T) * len)
        @_gc_preserve_end ta
        @_gc_preserve_end tb
        return c == 0
    else
        return false
    end
end
```
-/
def equalBitIntegerVector [Monad m] (ref : A → m R) (preserve : R → m Token)
    (pointer : R → m P) (length : A → m I) (elementSize : I)
    (memcmp : P → P → I → m I) (endPreserve : Token → m Unit) (a b : A) : m Bool := do
  let len ← length a
  if len = (← length b) then
    let aref ← ref a
    let bref ← ref b
    let ta ← preserve aref
    let tb ← preserve bref
    let pa ← pointer aref
    let pb ← pointer bref
    let c ← memcmp pa pb (elementSize * len)
    endPreserve ta
    endPreserve tb
    pure (c.val == 0)
  else pure false

/--
Julia source: base/array.jl:2248-2261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reverse(A::AbstractVector, start::Integer, stop::Integer=lastindex(A))
    s, n = Int(start), Int(stop)
    B = similar(A)
    for i = firstindex(A):s-1
        B[i] = A[i]
    end
    for i = s:n
        B[i] = A[n+s-i]
    end
    for i = n+1:lastindex(A)
        B[i] = A[i]
    end
    return B
end
```
-/
-- Source: base/array.jl:2248-2261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def reverse [Monad m]  (toStartInt : Start → m I)
    (toStopInt : Stop → m I) (similar : A → m A)
    (firstindex lastindex : A → m I) (get : A → I → m α) (set : A → α → I → m Unit)
    (a : A) (start : Start) (stop : Stop) : m A := do
  let s ← toStartInt start
  let n ← toStopInt stop
  let b ← similar a
  for i in intRange (← firstindex a) (s - one) do set b (← get a i) i
  for i in intRange s n do set b (← get a (n + s - i)) i
  for i in intRange (n + one) (← lastindex a) do set b (← get a i) i
  pure b

/--
Julia source: base/array.jl:2266-2266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(A::AbstractVector; dims::D=:) where {D} = $_f(A, dims)
```
-/
def reverseDims [Monad m] (reverse : A → D → m A) (a : A) (dims : D) : m A := reverse a dims

/--
Julia source: base/array.jl:2267-2267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $_f(A::AbstractVector, ::Colon) = $f(A, firstindex(A), lastindex(A))
```
-/
-- Source: base/array.jl:2267-2267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def reverseColon [Monad m] (firstindex lastindex : A → m I)
    (reverse : A → I → I → m A) (a : A) : m A := do
  reverse a (← firstindex a) (← lastindex a)

/--
Julia source: base/array.jl:2268-2268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $_f(A::AbstractVector, dim::Tuple{Integer}) = $_f(A, first(dim))
```
-/
-- Source: base/array.jl:2268-2268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def reverseTupleDim [Monad m] (reverse : A → Z → m A)
    (a : A) (dim : Z × Unit) : m A := reverse a dim.1

/--
Julia source: base/array.jl:2269-2272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function $_f(A::AbstractVector, dim::Integer)
            dim == 1 || _throw_argerror(LazyString("invalid dimension ", dim, " ≠ 1"))
            return $_f(A, :)
        end
```
-/
def reverseIntegerDim [Monad m] [MonadExceptOf Error m]
    (isOne : Z → Bool) (showInteger : Z → String) (reverseColon : A → m A)
    (a : A) (dim : Z) : m A := do
  if !(isOne dim) then throw (.argument ("invalid dimension " ++ showInteger dim ++ " ≠ 1"))
  reverseColon a

/--
Julia source: base/array.jl:2276-2279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reverseind(a::AbstractVector, i::Integer)
    li = LinearIndices(a)
    first(li) + last(li) - i
end
```
-/
def reverseind (firstLinear lastLinear : A → I) (subtract : I → Z → W)
    (a : A) (i : Z) : W := subtract (firstLinear a + lastLinear a) i

/--
Julia source: base/array.jl:2283-2283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
midpoint(lo::T, hi::T) where T<:Integer = lo +% ((hi -% lo) >>> 0x01)
```
-/
def midpoint (wrapAdd wrapSub : Z → Z → Z)
    (logicalShift : Z → JInt .u8 → Z) (lo hi : Z) : Z :=
  wrapAdd lo (logicalShift (wrapSub hi lo) (JInt.wrap .u8 1))

/--
Julia source: base/array.jl:2284-2284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
midpoint(lo::Integer, hi::Integer) = midpoint(promote(lo, hi)...)
```
-/
-- Source: base/array.jl:2284-2284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def midpointPromoted [Monad m] (promote : Z → W → m (P × P))
    (midpoint : P → P → m (P)) (lo : Z) (hi : W) : m (P) := do
  let (lo, hi) ← promote lo hi
  midpoint lo hi

/--
Julia source: base/array.jl:2312-2328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reverse!(v::AbstractVector, start::Integer, stop::Integer=lastindex(v))
    s, n = Int(start), Int(stop)
    if n > s # non-empty and non-trivial
        liv = LinearIndices(v)
        if !(first(liv) ≤ s ≤ last(liv))
            throw(BoundsError(v, s))
        elseif !(first(liv) ≤ n ≤ last(liv))
            throw(BoundsError(v, n))
        end
        r = n
        @inbounds for i in s:midpoint(s, n-1)
            v[i], v[r] = v[r], v[i]
            r -= 1
        end
    end
    return v
end
```
-/
def reverseBang [Monad m] [MonadExceptOf Error m]
    (toStartInt : Start → m I) (toStopInt : Stop → m I)
    (linearIndices : A → m Linear) (first last : Linear → m I)
    (midpoint : I → I → m I) (get : A → I → m E)
    (set : A → E → I → m Unit) (a : A) (start : Start) (stop : Stop) : m A := do
  let s ← toStartInt start
  let n ← toStopInt stop
  if n > s then
    let liv ← linearIndices a
    let startInBounds : Bool ← do
      if ¬((← first liv) ≤ s) then pure false
      else pure (decide (s ≤ (← last liv)))
    if !startInBounds then throw .bounds
    let stopInBounds : Bool ← do
      if ¬((← first liv) ≤ n) then pure false
      else pure (decide (n ≤ (← last liv)))
    if !stopInBounds then throw .bounds
    let mut r := n
    for i in intRange s (← midpoint s (n - one)) do
      let right ← get a r
      let left ← get a i
      set a right i
      set a left r
      r := r - one
  pure a

/--
Julia source: base/array.jl:2332-2332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat() = Vector{Any}()
```
-/
def vcatEmpty [Monad m] (allocate : I → m A) : m A := allocate zero

/--
Julia source: base/array.jl:2333-2333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat() = Vector{Any}()
```
-/
def hcatEmpty [Monad m] (allocate : I → m A) : m A := allocate zero

/-- The operations passed to the actual typed-comprehension collector. -/
structure TypedCollectOps (m : Type → Type) (G E T S Shape B : Type) where
  size : G → S
  sized : S → Bool
  unknown : S → Bool
  shape : G → S → m Shape
  arrayForInner : T → S → Shape → m B
  copyto : B → G → m B
  emptyVector : T → m B
  push : B → E → m Unit

/-- Dispatch of _collect(T, generator, IteratorSize(generator)). -/
def typedCollectDispatch [Monad m] [MonadExceptOf Error m] [ForIn m G E]
    (o : TypedCollectOps m G E T S Shape B) (t : T) (g : G) (s : S) : m B :=
  if o.sized s then collectSized o.shape o.arrayForInner o.copyto t g s
  else if o.unknown s then collectUnknown (o.emptyVector t) o.push g
  else throw (.method "_collect")

def typedComprehension [Monad m] [MonadExceptOf Error m] [ForIn m G E]
    (o : TypedCollectOps m G E T S Shape B) (t : T) (g : G) : m B :=
  collectTyped o.size (typedCollectDispatch o) t g

/-- Operations passed to collect(::Generator), including type inference and widening. -/
structure GeneratorCollectOps (m : Type → Type) (G E T S Shape St B : Type) where
  size : G → S
  defaultEltype : G → T
  unknown : S → Bool
  emptyVector : T → m B
  grow : B → G → m B
  shape : G → S → m Shape
  iterate : G → m (Option (E × St))
  typeof : E → T
  arrayForInner : T → S → Shape → m B
  isTypeSubtype : T → Bool
  typeType : T
  anyType : T
  isAbstractArray : B → Bool
  isConcrete : T → Bool
  ndims : B → I
  abstractArrayType : T → I → Bool → T
  collectWithFirst : B → E → G → St → m B
  typeassert : B → T → m B

def generatorComprehension [Monad m]
    (o : GeneratorCollectOps m G E T S Shape St B) (g : G) : m B :=
  collectGenerator o.size o.defaultEltype o.unknown o.emptyVector o.grow o.shape o.iterate
    o.typeof o.arrayForInner o.isTypeSubtype o.typeType o.anyType o.isAbstractArray
    o.isConcrete o.ndims o.abstractArrayType o.collectWithFirst o.typeassert g

abbrev MatrixGenerator (m : Type → Type) (R E : Type) :=
  JuliaLean.base.generator.Generator
    (JuliaLean.base.iterators.ProductIterator (List R)) (List I → m E)

/--
Julia source: base/array.jl:2335-2343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hcat(V::Vector{T}...) where T
    height = length(V[1])
    for j = 2:length(V)
        if length(V[j]) != height
            throw(DimensionMismatch("vectors must have same lengths"))
        end
    end
    return [ V[j][i]::T for i=1:length(V[1]), j=1:length(V) ]
end
```
-/
def hcat [Monad m] [MonadExceptOf Error m]
    (getVector : List A → I → m A) (length : A → m I) (get : A → I → m E)
    (typeAssert : E → m E) (range : I → I → m R)
    (coordinate : List I → I → m I)
    (collectOps : GeneratorCollectOps m (MatrixGenerator m R E) E T S Shape St B)
    (vs : List A) : m B := do
  let height ← length (← getVector vs one)
  for j in intRange (JInt.wrap .i64 2) (JInt.wrap .i64 vs.length) do
    if (← length (← getVector vs j)) != height then
      throw (.dimensionMismatch "vectors must have same lengths")
  let rows ← length (← getVector vs one)
  let rowRange ← range one rows
  let columnRange ← range one (JInt.wrap .i64 vs.length)
  let product := JuliaLean.base.iterators.productModel [rowRange, columnRange]
  let generator : MatrixGenerator m R E := ⟨(fun coordinates => do
    let i ← coordinate coordinates one
    let j ← coordinate coordinates (JInt.wrap .i64 2)
    typeAssert (← get (← getVector vs j) i)), product⟩
  generatorComprehension collectOps generator

structure Val1 where
  deriving Repr, DecidableEq

structure Val2 where
  deriving Repr, DecidableEq

/--
Julia source: base/array.jl:2344-2344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(A::Vector...) = cat(A...; dims=Val(2)) # more special than SparseArrays's hcat
```
-/
def hcatMixed [Monad m] (cat : Val2 → List A → m B) (arrays : List A) : m B :=
  JuliaLean.base.abstractarray.catKeyword cat arrays Val2.mk

/--
Julia source: base/array.jl:2346-2360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function vcat(arrays::Vector{T}...) where T
    n = 0
    for a in arrays
        n += length(a)
    end
    arr = Vector{T}(undef, n)
    nd = 1
    for a in arrays
        na = length(a)
        @assert nd + na <= 1 + length(arr) "Concurrent modification of arrays?"
        unsafe_copyto!(arr, nd, a, 1, na)
        nd += na
    end
    return arr
end
```
-/
def vcat [Monad m] [MonadExceptOf Error m] (length : A → m I)
    (allocate : I → m A) (copy : A → I → A → I → I → m Unit) (arrays : List A) : m A := do
  let mut n := zero
  for a in arrays do n := n + (← length a)
  let arr ← allocate n
  let mut nd := one
  for a in arrays do
    let na ← length a
    if !(nd + na ≤ one + (← length arr)) then
      throw (.assertion "Concurrent modification of arrays?")
    copy arr nd a one na
    nd := nd + na
  pure arr

/--
Julia source: base/array.jl:2361-2361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vcat(A::Vector...) = cat(A...; dims=Val(1)) # more special than SparseArrays's vcat
```
-/
def vcatMixed [Monad m] (cat : Val1 → List A → m B) (arrays : List A) : m B :=
  JuliaLean.base.abstractarray.catKeyword cat arrays Val1.mk

/--
Julia source: base/array.jl:2363-2363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cat(n::Integer, x::Integer...) = reshape([x...], (ntuple(Returns(1), n-1)..., length(x)))
```
-/
def catIntegers [Monad m] (literal : List X → m A)
    (subtract : Dim → I → Count) (ntuple : (I → I) → Count → m (List I))
    (reshape : A → List I → m B) (n : Dim) (xs : List X) : m B := do
  let vector ← literal xs
  let leading ← ntuple (fun _ => one) (subtract n one)
  reshape vector (leading ++ [JInt.wrap .i64 xs.length])

/--
Julia source: base/array.jl:2470-2481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnext(testf::Function, A, start)
    i = oftype(first(keys(A)), start)
    l = last(keys(A))
    i > l && return nothing
    while true
        testf(A[i]) && return i
        i == l && break
        # nextind(A, l) can throw/overflow
        i = nextind(A, i)
    end
    return nothing
end
```
-/
def findnext [Monad m] [DecidableEq K] (firstKey lastKey : A → K)
    (oftype : K → Start → m K) (greater : K → K → Bool)
    (get : A → K → m α) (test : α → m Bool) (rank : K → Nat)
    (nextind : (i : K) → m { j : K // rank j < rank i })
    (a : A) (start : Start) : m (Option K) := do
  let i ← oftype (firstKey a) start
  let l := lastKey a
  if greater i l then return none
  let rec loop (i : K) : m (Option K) := do
    if ← test (← get a i) then return some i
    if i = l then return none
    let next ← nextind i
    loop next.val
  termination_by rank i
  loop i

/--
Julia source: base/array.jl:2399-2399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findnext(A, start) = findnext(identity, A, start)
```
-/
def findnextBool [Monad m] [DecidableEq K] (firstKey lastKey : A → K)
    (oftype : K → Start → m K) (greater : K → K → Bool) (get : A → K → m Bool)
    (rank : K → Nat) (nextind : (i : K) → m { j : K // rank j < rank i })
    (a : A) (start : Start) : m (Option K) :=
  findnext firstKey lastKey oftype greater get (fun x => pure (id x)) rank nextind a start

/--
Julia source: base/array.jl:2439-2439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(A::AbstractArray) = findnext(A, first(keys(A)))
```
-/
def findfirstArrayBool [Monad m] [DecidableEq K] (firstKey' : A → m K)
    (firstKey lastKey : A → K) (oftype : K → K → m K) (greater : K → K → Bool)
    (get : A → K → m Bool) (rank : K → Nat) (nextind : (i : K) → m { j : K // rank j < rank i })
    (a : A) : m (Option K) := do
  findnextBool firstKey lastKey oftype greater get rank nextind a (← firstKey' a)

/--
Julia source: base/array.jl:2518-2523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findfirst(testf::Function, A)
    for (i, a) in pairs(A)
        testf(a) && return i
    end
    return nothing
end
```
-/
def findfirst [Monad m] [ForIn m Pairs (K × α)]
    (test : α → m Bool) (pairs : Pairs) : m (Option K) := do
  for (i, a) in pairs do
    if ← test a then return some i
  return none

/--
Julia source: base/array.jl:2526-2527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(testf::Function, A::Union{AbstractArray, AbstractString}) =
    findnext(testf, A, first(keys(A)))
```
-/
def findfirstArray [Monad m] [DecidableEq K] (firstKey' : A → m K)
    (firstKey lastKey : A → K) (oftype : K → K → m K) (greater : K → K → Bool)
    (get : A → K → m α) (rank : K → Nat) (nextind : (i : K) → m { j : K // rank j < rank i })
    (test : α → m Bool) (a : A) : m (Option K) := do
  findnext firstKey lastKey oftype greater get test rank nextind a (← firstKey' a)

def findfirstBoolDispatch [Monad m] [DecidableEq K] [ForIn m Pairs (K × Bool)]
    (indexed : A → Bool) (pairs : A → Pairs) (firstKey' : A → m K)
    (firstKey lastKey : A → K) (oftype : K → K → m K) (greater : K → K → Bool)
    (get : A → K → m Bool) (rank : K → Nat)
    (next : (i : K) → m { j : K // rank j < rank i }) (a : A) : m (Option K) :=
  if indexed a then
    findfirstArray firstKey' firstKey lastKey oftype greater get rank next (fun b => pure b) a
  else findfirst (fun b => pure b) (pairs a)

/--
Julia source: base/array.jl:2436-2436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(A) = findfirst(identity, A)
```
-/
def findfirstBool [Monad m] [DecidableEq K] [ForIn m Pairs (K × Bool)]
    (indexed : A → Bool) (pairs : A → Pairs) (firstKey' : A → m K)
    (firstKey lastKey : A → K) (oftype : K → K → m K) (greater : K → K → Bool)
    (get : A → K → m Bool) (rank : K → Nat)
    (next : (i : K) → m { j : K // rank j < rank i }) (a : A) : m (Option K) :=
  findfirstBoolDispatch indexed pairs firstKey' firstKey lastKey oftype greater get rank next a

/--
Julia source: base/array.jl:2529-2530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(p::Union{Fix2{typeof(isequal),T},Fix2{typeof(==),T}}, r::OneTo) where {T<:Integer} =
    1 <= p.x <= r.stop ? convert(keytype(r), p.x) : nothing
```
-/
def findfirstOneTo [Monad m] (xValue : X → Int) (stopValue : Stop → Int)
    (convertKey : X → m K) (x : X) (stop : Stop) : m (Option K) := do
  if 1 ≤ xValue x ∧ xValue x ≤ stopValue stop then return some (← convertKey x)
  pure none

/--
Julia source: base/array.jl:2532-2532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(::typeof(iszero), ::OneTo) = nothing
```
-/
def findfirstZeroOneTo (_r : R) : Option K := none

/--
Julia source: base/array.jl:2533-2533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(::typeof(isone), r::OneTo) = isempty(r) ? nothing : oneunit(keytype(r))
```
-/
def findfirstOneOneTo [Monad m] (isempty : R → Bool) (oneunit : R → m K) (r : R) : m (Option K) := do
  if isempty r then return none
  return some (← oneunit r)

/--
Julia source: base/array.jl:2535-2539 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findfirst(p::Union{Fix2{typeof(isequal),T},Fix2{typeof(==),T}}, r::AbstractUnitRange{<:Integer}) where {T<:Integer}
    first(r) <= p.x <= last(r) || return nothing
    i1 = first(keys(r))
    return i1 + oftype(i1, p.x - first(r))
end
```
-/
def findfirstUnitRange [Monad m] (first last : R → V)
    (rangeValue : V → Int) (xValue : X → Int) (firstKey : R → m K)
    (subtract : X → V → Diff) (oftype : K → Diff → m K) (add : K → K → K)
    (x : X) (r : R) : m (Option K) := do
  if !(rangeValue (first r) ≤ xValue x ∧ xValue x ≤ rangeValue (last r)) then return none
  let i1 ← firstKey r
  return some (add i1 (← oftype i1 (subtract x (first r))))

/--
Julia source: base/array.jl:2541-2547 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findfirst(p::Union{Fix2{typeof(isequal),T},Fix2{typeof(==),T}}, r::StepRange{T,S}) where {T,S}
    isempty(r) && return nothing
    minimum(r) <= p.x <= maximum(r) || return nothing
    d = p.x - first(r)
    iszero(d % step(r)) || return nothing
    return convert(keytype(r), d ÷ step(r) + 1)
end
```
-/
def findfirstStepRange [Monad m] (isempty : R → Bool) (minimum maximum first : R → V)
    (step : R → Step) (leLow : V → X → Bool) (leHigh : X → V → Bool)
    (sub : X → V → Diff) (rem : Diff → Step → m Remainder) (iszero : Remainder → Bool)
    (divide : Diff → Step → m QuotientValue) (plusOne : QuotientValue → QuotientValue)
    (convertKey : QuotientValue → m K) (x : X) (r : R) : m (Option K) := do
  if isempty r then return none
  if !(leLow (minimum r) x && leHigh x (maximum r)) then return none
  let d := sub x (first r)
  if !(iszero (← rem d (step r))) then return none
  return some (← convertKey (plusOne (← divide d (step r))))

/--
Julia source: base/array.jl:2549-2549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(::typeof(iszero), r::AbstractRange) = findfirst(==(zero(first(r))), r)
```
-/
def findfirstZeroRange [Monad m] (first : R → V) (constant : V → V)
    (findfirst : V → R → m (Option K)) (r : R) : m (Option K) :=
  findfirst (constant (first r)) r

/--
Julia source: base/array.jl:2550-2550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(::typeof(isone), r::AbstractRange) = findfirst(==(one(first(r))), r)
```
-/
def findfirstOneRange [Monad m] (first : R → V) (constant : V → V)
    (findfirst : V → R → m (Option K)) (r : R) : m (Option K) :=
  findfirst (constant (first r)) r

/--
Julia source: base/array.jl:2666-2677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findprev(testf::Function, A, start)
    f = first(keys(A))
    i = oftype(f, start)
    i < f && return nothing
    while true
        testf(A[i]) && return i
        i == f && break
        # prevind(A, f) can throw/underflow
        i = prevind(A, i)
    end
    return nothing
end
```
-/
def findprev [Monad m] [DecidableEq K] (firstKey : A → K)
    (oftype : K → Start → m K) (less : K → K → Bool)
    (get : A → K → m α) (test : α → m Bool) (rank : K → Nat)
    (prevind : (i : K) → m { j : K // rank j < rank i })
    (a : A) (start : Start) : m (Option K) := do
  let f := firstKey a
  let i ← oftype f start
  if less i f then return none
  let rec loop (i : K) : m (Option K) := do
    if ← test (← get a i) then return some i
    if i = f then return none
    let previous ← prevind i
    loop previous.val
  termination_by rank i
  loop i

/--
Julia source: base/array.jl:2586-2586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findprev(A, start) = findprev(identity, A, start)
```
-/
def findprevBool [Monad m] [DecidableEq K] (firstKey : A → K)
    (oftype : K → Start → m K) (less : K → K → Bool) (get : A → K → m Bool)
    (rank : K → Nat) (prevind : (i : K) → m { j : K // rank j < rank i })
    (a : A) (start : Start) : m (Option K) :=
  findprev firstKey oftype less get (fun x => pure (id x)) rank prevind a start

/--
Julia source: base/array.jl:2627-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(A::AbstractArray) = findprev(A, last(keys(A)))
```
-/
def findlastArrayBool [Monad m] [DecidableEq K] (lastKey' : A → m K) (firstKey : A → K)
    (oftype : K → K → m K) (less : K → K → Bool) (get : A → K → m Bool)
    (rank : K → Nat) (prevind : (i : K) → m { j : K // rank j < rank i })
    (a : A) : m (Option K) := do
  findprevBool firstKey oftype less get rank prevind a (← lastKey' a)

/--
Julia source: base/array.jl:2711-2716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findlast(testf::Function, A)
    for (i, a) in Iterators.reverse(pairs(A))
        testf(a) && return i
    end
    return nothing
end
```
-/
def findlast [Monad m] [ForIn m Reversed (K × α)]
    (reversePairs : Pairs → Reversed) (test : α → m Bool) (pairs : Pairs) : m (Option K) := do
  for (i, a) in reversePairs pairs do
    if ← test a then return some i
  return none

/--
Julia source: base/array.jl:2719-2720 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(testf::Function, A::Union{AbstractArray, AbstractString}) =
    findprev(testf, A, last(keys(A)))
```
-/
def findlastArray [Monad m] [DecidableEq K] (lastKey' : A → m K) (firstKey : A → K)
    (oftype : K → K → m K) (less : K → K → Bool) (get : A → K → m α)
    (rank : K → Nat) (prevind : (i : K) → m { j : K // rank j < rank i })
    (test : α → m Bool) (a : A) : m (Option K) := do
  findprev firstKey oftype less get test rank prevind a (← lastKey' a)

def findlastBoolDispatch [Monad m] [DecidableEq K] [ForIn m Reversed (K × Bool)]
    (indexed : A → Bool) (pairs : A → Pairs) (reversePairs : Pairs → Reversed)
    (lastKey' : A → m K) (firstKey : A → K) (oftype : K → K → m K)
    (less : K → K → Bool) (get : A → K → m Bool) (rank : K → Nat)
    (prev : (i : K) → m { j : K // rank j < rank i }) (a : A) : m (Option K) :=
  if indexed a then
    findlastArray lastKey' firstKey oftype less get rank prev (fun b => pure b) a
  else findlast reversePairs (fun b => pure b) (pairs a)

/--
Julia source: base/array.jl:2624-2624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(A) = findlast(identity, A)
```
-/
def findlastBool [Monad m] [DecidableEq K] [ForIn m Reversed (K × Bool)]
    (indexed : A → Bool) (pairs : A → Pairs) (reversePairs : Pairs → Reversed)
    (lastKey' : A → m K) (firstKey : A → K) (oftype : K → K → m K)
    (less : K → K → Bool) (get : A → K → m Bool) (rank : K → Nat)
    (prev : (i : K) → m { j : K // rank j < rank i }) (a : A) : m (Option K) :=
  findlastBoolDispatch indexed pairs reversePairs lastKey' firstKey oftype less get rank prev a

/--
Julia source: base/array.jl:2723-2726 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findlast(p::Union{Fix2{typeof(isequal),<:Integer},Fix2{typeof(==),<:Integer},typeof(iszero),typeof(isone)},
        r::AbstractUnitRange{<:Integer})
    findfirst(p, r)
end
```
-/
def findlastRange2723 [Monad m] (findfirst : P → R → m (Option K))
    (p : P) (r : R) : m (Option K) := findfirst p r

/--
Julia source: base/array.jl:2728-2731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findlast(p::Union{Fix2{typeof(isequal),T},Fix2{typeof(==),T},typeof(iszero),typeof(isone)},
        r::StepRange{T,S}) where {T,S}
    findfirst(p, r)
end
```
-/
def findlastRange2728 [Monad m] (findfirst : P → R → m (Option K))
    (p : P) (r : R) : m (Option K) := findfirst p r

/--
Julia source: base/array.jl:2784-2787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findall(testf::Function, A)
    gen = (first(p) for p in pairs(A) if testf(last(p)))
    @default_eltype(gen) === Union{} ? collect(@default_eltype(keys(A)), gen) : collect(gen)
end
```
-/
def findallPredicate [Monad m] (pairs : A → Pairs)
    (generator : (Pair → Bool) → (Pair → K) → Pairs → Gen)
    (value : Pair → α) (key : Pair → K) (test : α → Bool)
    (defaultGenTypeBottom : Gen → Bool) (defaultKeyType : A → T)
    (collectTyped : T → Gen → m B) (collect : Gen → m B) (a : A) : m B := do
  let gen := generator (fun p => test (value p)) key (pairs a)
  if defaultGenTypeBottom gen then collectTyped (defaultKeyType a) gen else collect gen

abbrev KeyGenerator (m : Type → Type) (Pairs Pair K : Type) :=
  JuliaLean.base.generator.Generator
    (JuliaLean.base.iterators.Filter (Pair → m Bool) Pairs) (Pair → K)

/-- Generic findall constructs the actual deferred Filter and key Generator. -/
def findallGenericDispatch [Monad m] (pairs : Mask → m Pairs)
    (boolValue : Pair → m Bool) (key : Pair → K)
    (collectOps : GeneratorCollectOps m (KeyGenerator m Pairs Pair K) K T S Shape St B)
    (a : Mask) : m B := do
  let ps ← pairs a
  let filtered := JuliaLean.base.iterators.sourceMethod576 boolValue ps
  let generator : KeyGenerator m Pairs Pair K := ⟨key, filtered⟩
  generatorComprehension collectOps generator

def findallBoolArrayDispatch [Monad m] [ForIn m BoolPairs (K × Bool)]
    (count : Mask → m I) (allocate : I → m B) (pairs : Mask → BoolPairs)
    (set : B → K → I → m Unit) (a : Mask) : m B := do
  let n ← count a
  let indices ← allocate n
  let mut cnt := one
  for (i, value) in pairs a do
    if value then
      set indices i cnt
      cnt := cnt + one
  pure indices

/-- The scalar Bool method's literal uses the file's actual vector-literal model. -/
def findallBoolDispatch [Monad m] (allocate : I → m B) (set : B → I → I → m B)
    (b : Bool) : m B :=
  if b then vectTyped allocate set [one] else allocate zero

/-- Storage operations for the installed, more-specific BitArray findall method. -/
structure BitFindallOps (m : Type → Type) {BitM : Type → Type}
    {BitArray : Nat → Type} {BitIndex : Type} (Mask B : Type) where
  asArray : Mask → Option (Sigma BitArray)
  findAll : {N : Nat} →
    (BitArray N → BitM I) → (I → BitM B) → (B → BitIndex → I → BitM Unit) →
    (B → BitArray N → BitM B) → (JInt .u64 → I) → BitArray N → BitM B
  count : (n : Nat) → BitArray n → BitM I
  allocate : I → BitM B
  set : B → BitIndex → I → BitM Unit
  allindices : (n : Nat) → B → BitArray n → BitM B
  trailingZeros : JInt .u64 → I
  lift : {α : Type} → BitM α → m α

/-- Dispatch retains the scalar, BitArray, Bool-array and generic result methods. -/
def findallDispatch [Monad m] [ForIn m BoolPairs (K × Bool)]
    (asBool : Mask → Option Bool) (scalarAllocate : I → m B)
    (scalarSet : B → I → I → m B)
    {BitM : Type → Type} {BitArray : Nat → Type} {BitIndex : Type}
    (bitOps : @BitFindallOps m BitM BitArray BitIndex Mask B)
    (isBoolArray : Mask → Bool) (count : Mask → m I) (allocate : I → m B)
    (boolPairs : Mask → BoolPairs) (set : B → K → I → m Unit)
    (pairs : Mask → m Pairs) (boolValue : Pair → m Bool) (key : Pair → K)
    (collectOps : GeneratorCollectOps m (KeyGenerator m Pairs Pair K) K T S Shape St B)
    (a : Mask) : m B :=
  match asBool a with
  | some b => findallBoolDispatch scalarAllocate scalarSet b
  | none =>
    match bitOps.asArray a with
    | some ⟨n, bits⟩ =>
      bitOps.lift (bitOps.findAll (bitOps.count n)
        bitOps.allocate bitOps.set (bitOps.allindices n) bitOps.trailingZeros bits)
    | none =>
      if isBoolArray a then findallBoolArrayDispatch count allocate boolPairs set a
      else findallGenericDispatch pairs boolValue key collectOps a

/--
Julia source: base/array.jl:2791-2791 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(testf::F, A::AbstractArray) where {F<:Function} = findall(testf.(A))
```
-/
def findallArrayPredicate [Monad m] [ForIn m BoolPairs (K × Bool)]
    (broadcast : (E → m V) → A → m Mask)
    (asBool : Mask → Option Bool) (scalarAllocate : I → m B)
    (scalarSet : B → I → I → m B)
    {BitM : Type → Type} {BitArray : Nat → Type} {BitIndex : Type}
    (bitOps : @BitFindallOps m BitM BitArray BitIndex Mask B)
    (isBoolArray : Mask → Bool) (count : Mask → m I) (allocate : I → m B)
    (boolPairs : Mask → BoolPairs) (set : B → K → I → m Unit)
    (pairs : Mask → m Pairs) (boolValue : Pair → m Bool) (key : Pair → K)
    (collectOps : GeneratorCollectOps m (KeyGenerator m Pairs Pair K) K T S Shape St B)
    (test : E → m V) (a : A) : m B := do
  findallDispatch asBool scalarAllocate scalarSet bitOps isBoolArray count allocate boolPairs
    set pairs boolValue key collectOps (← broadcast test a)

/--
Julia source: base/array.jl:2833-2835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findall(A)
    collect(first(p) for p in pairs(A) if last(p))
end
```
-/
def findallGeneric [Monad m] (pairs : A → Pairs)
    (generator : (Pair → Bool) → (Pair → K) → Pairs → Gen)
    (value : Pair → Bool) (key : Pair → K) (collect : Gen → m B) (a : A) : m B :=
  collect (generator value key (pairs a))

/--
Julia source: base/array.jl:2838-2849 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findall(A::AbstractArray{Bool})
    n = count(A)
    I = Vector{eltype(keys(A))}(undef, n)
    cnt = 1
    for (i,a) in pairs(A)
        if a
            I[cnt] = i
            cnt += 1
        end
    end
    I
end
```
-/
def findallBoolArray [Monad m] (count : A → m I) (allocate : I → m B)
    (pairs : A → m (List (K × Bool))) (set : B → K → I → m Unit) (a : A) : m B := do
  let n ← count a
  let indices ← allocate n
  let mut cnt := one
  for (i, value) in (← pairs a) do
    if value then
      set indices i cnt
      cnt := cnt + one
  pure indices

/--
Julia source: base/array.jl:2851-2851 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(x::Bool) = x ? [1] : Vector{Int}()
```
-/
def findallBool (x : Bool) : List I := if x then [one] else []

/--
Julia source: base/array.jl:2852-2852 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(testf::Function, x::Number) = testf(x) ? [1] : Vector{Int}()
```
-/
def findallNumber (test : α → Bool) (x : α) : List I := if test x then [one] else []

/--
Julia source: base/array.jl:2853-2853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(p::Fix2{typeof(in)}, x::Number) = x in p.x ? [1] : Vector{Int}()
```
-/
def findallInNumber (contains : α → Collection → Bool) (collection : Collection) (x : α) : List I :=
  if contains x collection then [one] else []

abbrev LookupGenerator (m : Type → Type) (Input E K : Type) :=
  JuliaLean.base.generator.Generator Input (E → m (Option K))

instance [Monad m] [ForIn m Input E] : ForIn m (LookupGenerator m Input E K) (Option K) where
  forIn g init step := forIn g.iter init (fun x acc => do step (← g.f x) acc)

/--
Julia source: base/array.jl:2887-2896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function indexin(a, b::AbstractArray)
    inds = keys(b)
    bdict = Dict{eltype(b),eltype(inds)}()
    for (val, ind) in zip(b, inds)
        get!(bdict, val, ind)
    end
    return Union{eltype(inds), Nothing}[
        get(bdict, i, nothing) for i in a
    ]
end
```
-/
def indexin [Monad m] [MonadExceptOf Error m]
    [ForIn m Zipped (E × K)] [ForIn m (LookupGenerator m InputA E K) (Option K)]
    (keys : InputB → m Keys) (emptyDict : m Dict) (zip : InputB → Keys → Zipped)
    (getOrInsert : Dict → E → K → m Unit)
    (get : Dict → E → Option K → m (Option K))
    (unionKeyType : Keys → T)
    (collectOps : TypedCollectOps m (LookupGenerator m InputA E K) (Option K) T S Shape B)
    (a : InputA) (b : InputB) : m B := do
  let inds ← keys b
  let dict ← emptyDict
  for (value, index) in zip b inds do getOrInsert dict value index
  let gen : LookupGenerator m InputA E K := ⟨(fun i => get dict i none), a⟩
  typedComprehension collectOps (unionKeyType inds) gen

/--
Julia source: base/array.jl:2898-2904 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findin(a::Union{AbstractArray, Tuple}, b::AbstractSet)
    ind  = Vector{eltype(keys(a))}()
    @inbounds for (i,ai) in pairs(a)
        ai in b && push!(ind, i)
    end
    ind
end
```
-/
def findinSet [Monad m] [ForIn m Pairs (K × α)] (empty : m B) (pairs : A → Pairs)
    (contains : α → Set → m Bool) (push : B → K → m Unit) (a : A) (set : Set) : m B := do
  let indices ← empty
  for (i, ai) in pairs a do
    if ← contains ai set then push indices i
  pure indices

/--
Julia source: base/array.jl:2905-2905 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_findin(a::Union{AbstractArray, Tuple}, b) = _findin(a, Set(b))
```
-/
def findin [Monad m] (set : Collection → m Set) (findin : A → Set → m B)
    (a : A) (b : Collection) : m B := do findin a (← set b)

/--
Julia source: base/array.jl:2910-2950 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sortedfindin(v::Union{AbstractArray, Tuple}, w)
    viter, witer = keys(v), eachindex(w)
    out  = eltype(viter)[]
    vy, wy = iterate(viter), iterate(witer)
    if vy === nothing || wy === nothing
        return out
    end
    viteri, i = vy
    witerj, j = wy
    @inbounds begin
        vi, wj = v[viteri], w[witerj]
        while true
            if isless(vi, wj)
                vy = iterate(viter, i)
                if vy === nothing
                    break
                end
                viteri, i = vy
                vi        = v[viteri]
            elseif isless(wj, vi)
                wy = iterate(witer, j)
                if wy === nothing
                    break
                end
                witerj, j = wy
                wj        = w[witerj]
            else
                push!(out, viteri)
                vy = iterate(viter, i)
                if vy === nothing
                    break
                end
                # We only increment the v iterator because v can have
                # repeated matches to a single value in w
                viteri, i = vy
                vi        = v[viteri]
            end
        end
    end
    return out
end
```
-/
def sortedfindin [Monad m] (keys : V → List K) (eachindex : W → List L)
    (empty : m B) (getV : V → K → m α) (getW : W → L → m β)
    (lessVW : α → β → m Bool) (lessWV : β → α → m Bool)
    (push : B → K → m Unit) (v : V) (w : W) : m B := do
  let viter := keys v
  let witer := eachindex w
  let out ← empty
  match viter, witer with
  | [], _ => pure out
  | _, [] => pure out
  | vk :: vr, wk :: wr =>
    let vi ← getV v vk
    let wj ← getW w wk
    let rec loop (vk : K) (vi : α) (vr : List K) (wk : L) (wj : β) (wr : List L) : m B := do
      if ← lessVW vi wj then
        match vr with
        | [] => pure out
        | vk' :: vr' => loop vk' (← getV v vk') vr' wk wj wr
      else if ← lessWV wj vi then
        match wr with
        | [] => pure out
        | wk' :: wr' => loop vk vi vr wk' (← getW w wk') wr'
      else
        push out vk
        match vr with
        | [] => pure out
        | vk' :: vr' => loop vk' (← getV v vk') vr' wk wj wr
    termination_by vr.length + wr.length
    loop vk vi vr wk wj wr

/--
Julia source: base/array.jl:2952-2958 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findall(pred::Fix2{typeof(in),<:Union{Array{<:Real},Real}}, x::Array{<:Real})
    if issorted(x, Sort.Forward) && issorted(pred.x, Sort.Forward)
        return _sortedfindin(x, pred.x)
    else
        return _findin(x, pred.x)
    end
end
```
-/
def findallInSorted [Monad m] (sortedArray : A → Bool) (sortedCollection : B → Bool)
    (sortedFindin findin : A → B → m C) (pred : B) (x : A) : m C :=
  if sortedArray x && sortedCollection pred then sortedFindin x pred else findin x pred

/-- Method selection for the two _findin methods. -/
def findinDispatch [Monad m] [ForIn m Pairs (K × E)]
    (isSet : C → Bool) (asSet : C → Set) (toSet : C → m Set)
    (empty : m B) (pairs : A → Pairs) (contains : E → Set → m Bool)
    (push : B → K → m Unit) (a : A) (c : C) : m B :=
  if isSet c then findinSet empty pairs contains push a (asSet c)
  else findin toSet (findinSet empty pairs contains push) a c

/--
Julia source: base/array.jl:2961-2961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(pred::Fix2{typeof(in)}, x::AbstractArray) = _findin(x, pred.x)
```
-/
def findallIn2961 [Monad m] [ForIn m Pairs (K × E)]
    (isSet : C → Bool) (asSet : C → Set) (toSet : C → m Set)
    (empty : m B) (pairs : A → Pairs) (contains : E → Set → m Bool)
    (push : B → K → m Unit) (pred : C) (x : A) : m B :=
  findinDispatch isSet asSet toSet empty pairs contains push x pred

/--
Julia source: base/array.jl:2962-2962 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(pred::Fix2{typeof(in)}, x::Tuple) = _findin(x, pred.x)
```
-/
def findallIn2962 [Monad m] [ForIn m Pairs (K × E)]
    (isSet : C → Bool) (asSet : C → Set) (toSet : C → m Set)
    (empty : m B) (pairs : A → Pairs) (contains : E → Set → m Bool)
    (push : B → K → m Unit) (pred : C) (x : A) : m B :=
  findinDispatch isSet asSet toSet empty pairs contains push x pred

/--
Julia source: base/array.jl:2965-2974 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function indcopy(sz::Dims, I::Vector)
    n = length(I)
    s = sz[n]
    for i = n+1:length(sz)
        s *= sz[i]
    end
    dst = eltype(I)[_findin(I[i], i < n ? (1:sz[i]) : (1:s)) for i = 1:n]
    src = eltype(I)[I[i][_findin(I[i], i < n ? (1:sz[i]) : (1:s))] for i = 1:n]
    dst, src
end
```
-/
def indcopyVector [Monad m] (sizeLength : Dims → I) (sizeAt : Dims → I → m I)
    (indicesLength : Indices → I) (indexAt : Indices → I → m Range)
    (findin : Range → I → I → m Range) (get : Range → Range → m Range)
    (build : List Range → m Indices) (sz : Dims) (indices : Indices) : m (Indices × Indices) := do
  let n := indicesLength indices
  let mut s ← sizeAt sz n
  for i in intRange (n + one) (sizeLength sz) do s := s * (← sizeAt sz i)
  let dst ← (intRange one n).mapM fun i => do
    let upper ← if i < n then sizeAt sz i else pure s
    findin (← indexAt indices i) one upper
  let dst ← build dst
  let src ← (intRange one n).mapM fun i => do
    let range ← indexAt indices i
    let upper ← if i < n then sizeAt sz i else pure s
    get range (← findin range one upper)
  let src ← build src
  pure (dst, src)

/--
Julia source: base/array.jl:2976-2986 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function indcopy(sz::Dims, I::Tuple{Vararg{RangeIndex}})
    n = length(I)
    _s = sz[n]
    for i = n+1:length(sz)
        _s *= sz[i]
    end
    s = _s
    dst::typeof(I) = ntuple(i-> _findin(I[i], i < n ? (1:sz[i]) : (1:s)), n)::typeof(I)
    src::typeof(I) = ntuple(i-> I[i][_findin(I[i], i < n ? (1:sz[i]) : (1:s))], n)::typeof(I)
    dst, src
end
```
-/
def indcopyTuple [Monad m] (sizeLength : Dims → I) (sizeAt : Dims → I → m I)
    (indicesLength : Indices → I) (indexAt : Indices → I → m Range)
    (findin : Range → I → I → m Range) (get : Range → Range → m Range)
    (build : List Range → m Indices) (sz : Dims) (indices : Indices) : m (Indices × Indices) := do
  let n := indicesLength indices
  let mut s ← sizeAt sz n
  for i in intRange (n + one) (sizeLength sz) do s := s * (← sizeAt sz i)
  let dst ← (intRange one n).mapM fun i => do
    let upper ← if i < n then sizeAt sz i else pure s
    findin (← indexAt indices i) one upper
  let dst ← build dst
  let src ← (intRange one n).mapM fun i => do
    let range ← indexAt indices i
    let upper ← if i < n then sizeAt sz i else pure s
    get range (← findin range one upper)
  let src ← build src
  pure (dst, src)

/--
Julia source: base/array.jl:3015-3025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter(f, a::Array{T, N}) where {T, N}
    j = 1
    b = Vector{T}(undef, length(a))
    for ai in a
        @inbounds b[j] = ai
        j = ifelse(f(ai)::Bool, j+1, j)
    end
    resize!(b, j-1)
    sizehint!(b, length(b))
    b
end
```
-/
def filterArray [Monad m] [ForIn m A α] (length : A → m I) (allocate : I → m B)
    (set : B → α → I → m Unit) (test : α → m Bool)
    (resize : B → I → m Unit) (resultLength : B → m I)
    (sizehint : B → I → m Unit) (a : A) : m B := do
  let mut j := one
  let b ← allocate (← length a)
  for ai in a do
    set b ai j
    let keep ← test ai
    j := if keep then j + one else j
  resize b (j - one)
  sizehint b (← resultLength b)
  pure b

/--
Julia source: base/array.jl:3027-3042 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter(f, a::AbstractArray)
    (IndexStyle(a) != IndexLinear()) && return a[map!(x -> f(x)::Bool, similar(a, Bool), a)]

    j = 1
    idxs = Vector{Int}(undef, length(a))
    for idx in eachindex(a)
        @inbounds idxs[j] = idx
        ai = @inbounds a[idx]
        j = ifelse(f(ai)::Bool, j+1, j)
    end
    resize!(idxs, j-1)
    res = a[idxs]
    empty!(idxs)
    sizehint!(idxs, 0)
    return res
end
```
-/
def filterAbstractArray [Monad m] [ForIn m Keys K]
    (linear : A → m Bool) (similarBool : A → m Mask)
    (mapPredicate : (E → m Bool) → Mask → A → m Mask) (getMask : A → Mask → m B)
    (length : A → m I) (allocateIndices : I → m Indices)
    (eachindex : A → m Keys) (setIndex : Indices → K → I → m Unit)
    (get : A → K → m E) (test : E → m Bool) (resize : Indices → I → m Unit)
    (getIndices : A → Indices → m B) (empty : Indices → m Unit)
    (sizehint : Indices → I → m Unit) (a : A) : m B := do
  if !(← linear a) then
    return ← getMask a (← mapPredicate test (← similarBool a) a)
  let mut j := one
  let idxs ← allocateIndices (← length a)
  for idx in (← eachindex a) do
    setIndex idxs idx j
    let ai ← get a idx
    let keep ← test ai
    j := if keep then j + one else j
  resize idxs (j - one)
  let result ← getIndices a idxs
  empty idxs
  sizehint idxs zero
  pure result

/--
Julia source: base/array.jl:3061-3075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter!(f, a::AbstractVector)
    j = firstindex(a)
    for ai in a
        @inbounds a[j] = ai
        j = ifelse(f(ai)::Bool, nextind(a, j), j)
    end
    j > lastindex(a) && return a
    if a isa Vector
        resize!(a, j-1)
        sizehint!(a, j-1)
    else
        deleteat!(a, j:lastindex(a))
    end
    return a
end
```
-/
def filterBang [Monad m] [ForIn m A α] (firstindex lastindex : A → m I) (set : A → α → I → m Unit) (test : α → m Bool) (nextind : A → I → m I)
    (isVector : A → Bool) (resize sizehint : A → I → m Unit)
    (deleteat : A → I → I → m Unit) (a : A) : m A := do
  let mut j ← firstindex a
  for ai in a do
    set a ai j
    let keep ← test ai
    let next ← nextind a j
    j := if keep then next else j
  if j > (← lastindex a) then return a
  if isVector a then
    resize a (j - one)
    sizehint a (j - one)
  else deleteat a j (← lastindex a)
  pure a

/--
Julia source: base/array.jl:3100-3102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter(f)
    Fix1(filter, f)
end
```
-/
def filterFix1 {F A B σ τ : Type} (showInt typeName : Int → String)
    (stableTypeFunction : (F → A → Unit → B) → σ) (stableTypeValue : F → τ)
    (filter : F → A → Unit → B) (f : F) :
    Jl (JuliaLean.base.operators.Fix (Int.toNat 1) (F → A → Unit → B) F
      (stableTypeFunction filter) (stableTypeValue f)) :=
  JuliaLean.base.operators.makeFix true 1 showInt typeName Int.toNat stableTypeFunction
    stableTypeValue filter f

/--
Julia source: base/array.jl:3129-3129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keepat!(a::Vector, inds) = _keepat!(a, inds)
```
-/
def keepat3129 [Monad m] (keepat : A → Indices → m A) (a : A) (indices : Indices) : m A :=
  keepat a indices

/--
Julia source: base/array.jl:3154-3154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keepat!(a::Vector, m::AbstractVector{Bool}) = _keepat!(a, m)
```
-/
def keepat3154 [Monad m] (keepat : A → Indices → m A) (a : A) (indices : Indices) : m A :=
  keepat a indices

/--
Julia source: base/array.jl:3159-3167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unique_filter!(pred::P, update!::U, state) where {P,U} = function (x)
    # P, U force specialization
    if pred(x, state)
        update!(state, x)
        true
    else
        false
    end
end
```
-/
def uniqueFilter [Monad m] (pred : α → State → m Bool)
    (update : State → α → m Unit) (state : State) : α → m Bool := fun x => do
  if ← pred x state then
    update state x
    pure true
  else pure false

/--
Julia source: base/array.jl:3169-3169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_grow_filter!(seen) = _unique_filter!(∉, push!, seen)
```
-/
def growFilter [Monad m] (notin : α → State → m Bool)
    (push : State → α → m Unit) (seen : State) : α → m Bool := uniqueFilter notin push seen

/--
Julia source: base/array.jl:3170-3170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_shrink_filter!(keep) = _unique_filter!(∈, pop!, keep)
```
-/
def shrinkFilter [Monad m] (contains : α → State → m Bool)
    (pop : State → α → m Unit) (keep : State) : α → m Bool := uniqueFilter contains pop keep

/--
Julia source: base/array.jl:3172-3178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _grow!(pred!, v::AbstractVector, itrs)
    filter!(pred!, v) # uniquify v
    for itr in itrs
        mapfilter(pred!, push!, itr, v)
    end
    return v
end
```
-/
def grow [Monad m] (filter : (α → m Bool) → A → m Unit)
    (push : A → α → m Unit) (mapfilter : (α → m Bool) → (A → α → m Unit) → X → A → m Unit)
    (pred : α → m Bool) (v : A) (itrs : List X) : m A := do
  filter pred v
  for itr in itrs do mapfilter pred push itr v
  pure v

/--
Julia source: base/array.jl:3180-3181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
union!(v::AbstractVector{T}, itrs...) where {T} =
    _grow!(_grow_filter!(sizehint!(Set{T}(), length(v))), v, itrs)
```
-/
def unionBang [Monad m] (emptySet : m Set) (length : A → m I)
    (sizehint : Set → I → m Set) (growFilter : Set → α → m Bool)
    (grow : (α → m Bool) → A → List X → m A) (v : A) (itrs : List X) : m A := do
  grow (growFilter (← sizehint (← emptySet) (← length v))) v itrs

/--
Julia source: base/array.jl:3183-3184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
symdiff!(v::AbstractVector{T}, itrs...) where {T} =
    _grow!(_shrink_filter!(symdiff!(Set{T}(), v, itrs...)), v, itrs)
```
-/
def symdiffBang [Monad m] (emptySet : m Set) (symdiff : Set → A → List X → m Set)
    (shrinkFilter : Set → α → m Bool) (grow : (α → m Bool) → A → List X → m A)
    (v : A) (itrs : List X) : m A := do grow (shrinkFilter (← symdiff (← emptySet) v itrs)) v itrs

/--
Julia source: base/array.jl:3186-3191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _shrink!(shrinker!::F, v::AbstractVector, itrs) where F
    seen = Set{eltype(v)}()
    filter!(_grow_filter!(seen), v)
    shrinker!(seen, itrs...)
    filter!(in(seen), v)
end
```
-/
def shrink [Monad m] (emptySet : m Set) (growFilter : Set → α → m Bool)
    (filter : (α → m Bool) → A → m A) (shrinker : Set → List X → m Unit)
    (contains : Set → α → m Bool) (v : A) (itrs : List X) : m A := do
  let seen ← emptySet
  let _ ← filter (growFilter seen) v
  shrinker seen itrs
  filter (contains seen) v

/--
Julia source: base/array.jl:3193-3193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect!(v::AbstractVector, itrs...) = _shrink!(intersect!, v, itrs)
```
-/
def intersectBang [Monad m] (setOperation : Set → List X → m Unit)
    (shrink : (Set → List X → m Unit) → A → List X → m A) (v : A) (itrs : List X) : m A :=
  shrink setOperation v itrs

/--
Julia source: base/array.jl:3194-3194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setdiff!(  v::AbstractVector, itrs...) = _shrink!(setdiff!, v, itrs)
```
-/
def setdiffBang [Monad m] (setOperation : Set → List X → m Unit)
    (shrink : (Set → List X → m Unit) → A → List X → m A) (v : A) (itrs : List X) : m A :=
  shrink setOperation v itrs

abbrev FilterGenerator (m : Type → Type) (Input E : Type) :=
  JuliaLean.base.generator.Generator
    (JuliaLean.base.iterators.Filter (E → m Bool) Input) (E → E)

instance [Monad m] [ForIn m Input E] : ForIn m (FilterGenerator m Input E) E where
  forIn g init step := forIn g.iter.itr init (fun x acc => do
    if ← g.iter.flt x then step (g.f x) acc else pure (.yield acc))

/--
Julia source: base/array.jl:3196-3196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vectorfilter(T::Type, f, v) = T[x for x in v if f(x)]
```
-/
def vectorfilter [Monad m] [MonadExceptOf Error m]
    [ForIn m (FilterGenerator m Input E) E]
    (collectOps : TypedCollectOps m (FilterGenerator m Input E) E T S Shape B)
    (t : T) (test : E → m Bool) (v : Input) : m B :=
  let filtered := JuliaLean.base.iterators.sourceMethod576 test v
  let generator : FilterGenerator m Input E :=
    ⟨JuliaLean.base.operators.identity, filtered⟩
  typedComprehension collectOps t generator

/--
Julia source: base/array.jl:3198-3202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect(itr, itrs...)
    T = promote_eltype(itr, itrs...)
    keep = intersect!(Set{T}(itr), itrs...)
    vectorfilter(T, _shrink_filter!(keep), itr)
end
```
-/
def intersect [Monad m] (elementType : X → List X → T) (makeSet : T → X → m Set)
    (setOperation : Set → List X → m Set) (shrinkFilter : Set → α → m Bool)
    (vectorfilter : T → (α → m Bool) → X → m A) (itr : X) (itrs : List X) : m A := do
  let t := elementType itr itrs
  let keep ← setOperation (← makeSet t itr) itrs
  vectorfilter t (shrinkFilter keep) itr

/--
Julia source: base/array.jl:3204-3208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setdiff(itr, itrs...)
    T = eltype(itr)
    keep = setdiff!(Set{T}(itr), itrs...)
    vectorfilter(T, _shrink_filter!(keep), itr)
end
```
-/
def setdiff [Monad m] (elementType : X → T) (makeSet : T → X → m Set)
    (setOperation : Set → List X → m Set) (shrinkFilter : Set → α → m Bool)
    (vectorfilter : T → (α → m Bool) → X → m A) (itr : X) (itrs : List X) : m A := do
  let t := elementType itr
  let keep ← setOperation (← makeSet t itr) itrs
  vectorfilter t (shrinkFilter keep) itr

/--
Julia source: base/array.jl:3210-3215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect(v::AbstractVector, r::AbstractRange)
    T = promote_eltype(v, r)
    common = Iterators.filter(in(r), v)
    seen = Set{T}(common)
    return vectorfilter(T, _shrink_filter!(seen), common)
end
```
-/
def intersectVectorRange [Monad m] (promoteEltype : A → R → T)
    (contains : R → α → Bool) (iteratorFilter : (α → Bool) → A → X)
    (makeSet : T → X → m Set) (shrinkFilter : Set → α → m Bool)
    (vectorfilter : T → (α → m Bool) → X → m B) (v : A) (r : R) : m B := do
  let t := promoteEltype v r
  let common := iteratorFilter (contains r) v
  let seen ← makeSet t common
  vectorfilter t (shrinkFilter seen) common

/--
Julia source: base/array.jl:3216-3216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect(r::AbstractRange, v::AbstractVector) = intersect(v, r)
```
-/
def intersectRangeVector [Monad m] (promoteEltype : A → R → T)
    (contains : R → α → Bool) (iteratorFilter : (α → Bool) → A → X)
    (makeSet : T → X → m Set) (shrinkFilter : Set → α → m Bool)
    (vectorfilter : T → (α → m Bool) → X → m B) (r : R) (v : A) : m B :=
  intersectVectorRange promoteEltype contains iteratorFilter makeSet shrinkFilter vectorfilter v r

/--
Julia source: base/array.jl:3219-3225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function getindex(v::AbstractRange, i::Integer)
    if i isa Bool # Not via dispatch to avoid ambiguities
        throw(ArgumentError("invalid index: $i of type Bool"))
    else
        _getindex(v, i)
    end
end
```
-/
def getindexAbstractRange [Monad m] [MonadExceptOf Error m]
    (isBool : Z → Bool) (showBool : Z → String)
    (getindex : R → Z → m α) (r : R) (i : Z) : m α :=
  if isBool i then throw (.argument ("invalid index: " ++ showBool i ++ " of type Bool"))
  else getindex r i

-- Declaration without a method body.
-- Source: base/array.jl:3233-3233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function wrap end
-- /Source

/--
Julia source: base/array.jl:3244-3247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline invalid_wrap_err(len, dims, proddims) = throw(DimensionMismatch(LazyString(
    "Attempted to wrap a MemoryRef of length ", len, " with an Array of size dims=", dims,
    " which is invalid because prod(dims) = ", proddims, " > ", len,
    " so that the array would have more elements than the underlying memory can store.")))
```
-/
def invalidWrapError [Monad m] [MonadExceptOf Error m]
    (renderLength : Len → String) (renderDims : Dims → String)
    (renderProduct : Product → String) (len : Len) (dims : Dims) (product : Product) : m α :=
  throw (.dimensionMismatch (
    "Attempted to wrap a MemoryRef of length " ++ renderLength len ++
    " with an Array of size dims=" ++ renderDims dims ++
    " which is invalid because prod(dims) = " ++ renderProduct product ++
    " > " ++ renderLength len ++
    " so that the array would have more elements than the underlying memory can store."))

def dimensionTupleText (dims : List I) : String :=
  "(" ++ ", ".intercalate (dims.map (fun d => toString d.val)) ++
    (if dims.length = 1 then ",)" else ")")

/--
Julia source: base/array.jl:3236-3242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _wrap(ref::MemoryRef{T}, dims::NTuple{N, Int}) where {T, N}
    mem = ref.mem
    mem_len = length(mem) + 1 - memoryrefoffset(ref)
    len = Core.checked_dims(dims...)
    @boundscheck mem_len >= len || invalid_wrap_err(mem_len, dims, len)
    return ref
end
```
-/
def wrapCheck [Monad m] [MonadExceptOf Error m]
    (memory : R → Mem) (length : Mem → I) (offset : R → I)
    (checkedDims : List I → m I) (ref : R) (dims : List I) : m R := do
  let mem := memory ref
  let memlen := length mem + one - offset ref
  let len ← checkedDims dims
  if !(memlen ≥ len) then
    invalidWrapError (fun x : I => toString x.val) dimensionTupleText
      (fun x : I => toString x.val) memlen dims len
  pure ref

/--
Julia source: base/array.jl:3249-3253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval @propagate_inbounds function wrap(::Type{Array}, m::MemoryRef{T}, dims::NTuple{N, Integer}) where {T, N}
    dims = convert(Dims, dims)
    ref = _wrap(m, dims)
    $(Expr(:new, :(Array{T, N}), :ref, :dims))
end
```
-/
def wrapRefDims [Monad m] (convertDims : D → m (List I))
    (wrap : R → List I → m R) (newArray : R → List I → m A) (ref : R) (dimensions : D) : m A := do
  let dims ← convertDims dimensions
  let ref ← wrap ref dims
  newArray ref dims

/--
Julia source: base/array.jl:3255-3259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval @propagate_inbounds function wrap(::Type{Array}, m::Memory{T}, dims::NTuple{N, Integer}) where {T, N}
    dims = convert(Dims, dims)
    ref = _wrap(memoryref(m), dims)
    $(Expr(:new, :(Array{T, N}), :ref, :dims))
end
```
-/
def wrapMemoryDims [Monad m] (convertDims : D → m (List I))
    (memoryref : M → m R) (wrap : R → List I → m R)
    (newArray : R → List I → m A) (memory : M) (dimensions : D) : m A := do
  let dims ← convertDims dimensions
  let ref ← wrap (← memoryref memory) dims
  newArray ref dims

/--
Julia source: base/array.jl:3260-3264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval @propagate_inbounds function wrap(::Type{Array}, m::MemoryRef{T}, l::Integer) where {T}
    dims = (Int(l),)
    ref = _wrap(m, dims)
    $(Expr(:new, :(Array{T, 1}), :ref, :dims))
end
```
-/
def wrapRefLength [Monad m] (toInt : Z → m I)
    (wrap : R → List I → m R) (newArray : R → List I → m A)
    (ref : R) (length : Z) : m A := do
  let dims := [← toInt length]
  let ref ← wrap ref dims
  newArray ref dims

/--
Julia source: base/array.jl:3265-3269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval @propagate_inbounds function wrap(::Type{Array}, m::Memory{T}, l::Integer) where {T}
    dims = (Int(l),)
    ref = _wrap(memoryref(m), (l,))
    $(Expr(:new, :(Array{T, 1}), :ref, :dims))
end
```
-/
def wrapMemoryLength [Monad m] (toInt : Z → m I)
    (memoryref : M → m R) (wrap : R → List (Z) → m R)
    (newArray : R → List I → m A) (mem : M) (length : Z) : m A := do
  let dims := [← toInt length]
  let ref ← wrap (← memoryref mem) [length]
  newArray ref dims

/--
Julia source: base/array.jl:3270-3274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval @propagate_inbounds function wrap(::Type{Array}, m::Memory{T}) where {T}
    ref = memoryref(m)
    dims = (length(m),)
    $(Expr(:new, :(Array{T, 1}), :ref, :dims))
end
```
-/
def wrapMemory [Monad m] (memoryref : M → m R) (length : M → I)
    (newArray : R → List I → m A) (mem : M) : m A := do
  let ref ← memoryref mem
  let dims := [length mem]
  newArray ref dims


/-! ## Concrete primitive instantiation for standard vector searches

These are `essentials.jl` indexing and integer-conversion callees, together with
termination witnesses for `nextind` and `prevind`; the searches call `findnext`
and `findprev` above directly.
-/

/-- `getindex(::Vector, ::Int)` from essentials.jl, for a fully assigned vector. -/
def vectorGet (xs : List α) (i : I) : Except Error α :=
  if 1 ≤ i.val ∧ i.val ≤ xs.length then
    match xs[(i.val - 1).toNat]? with
    | some x => .ok x
    | none => .error .bounds
  else .error .bounds

def indexConvert {t : IntTy} (i : JInt t) : Except Error I :=
  (JInt.convert (IntTy.i64.name) .i64 i.val).mapError (fun _ => .inexact)

def forwardRank (n : Nat) (i : I) : Nat := ((n : Int) - i.val).toNat

def backwardRank (i : I) : Nat := (i.val - 1).toNat

def nextVectorIndex (n : Nat) (hn : n < 2 ^ 62) (i : I) :
    Except Error { j : I // forwardRank n j < forwardRank n i } :=
  if h : 0 < forwardRank n i then
    .ok ⟨i + one, by
      have hi := i.property
      have hv : (i + one).val = i.val + 1 := by
        change wrapInt .i64 (i.val + one.val) = i.val + 1
        rw [show one.val = 1 from rfl]
        apply wrapInt_of_inRange
        simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at *
        simp only [forwardRank] at h
        omega
      simp only [forwardRank, hv] at *
      omega⟩
  else .error .bounds

def prevVectorIndex (i : I) :
    Except Error { j : I // backwardRank j < backwardRank i } :=
  if h : 0 < backwardRank i then
    .ok ⟨i - one, by
      have hi := i.property
      have hv : (i - one).val = i.val - 1 := by
        change wrapInt .i64 (i.val - one.val) = i.val - 1
        rw [show one.val = 1 from rfl]
        apply wrapInt_of_inRange
        simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at *
        simp only [backwardRank] at h
        omega
      simp only [backwardRank, hv] at *
      omega⟩
  else .error .bounds

/-- Concrete storage for the `essentials.jl` Array primitives. Handles are
stable positions in the heap; `none` is an unassigned reference slot. -/
abbrev VectorHeap (α : Type) := List (List (Option α))

abbrev VectorM (α : Type) := StateT (VectorHeap α) (Except Error)

def heapSlots (handle : Nat) : VectorM α (List (Option α)) := do
  match (← get)[handle]? with
  | some slots => pure slots
  | none => throw .bounds

def heapGet (handle : Nat) (i : I) : VectorM α α := do
  let slots ← heapSlots handle
  match ← liftM (vectorGet slots i) with
  | some x => pure x
  | none => throw .undefinedReference

def heapSet (handle : Nat) (x : α) (i : I) : VectorM α Unit := do
  let slots ← heapSlots handle
  let _ ← liftM (vectorGet slots i)
  modify fun heap => heap.set handle (slots.set (i.val - 1).toNat (some x))

def heapLength (handle : Nat) : VectorM α I := do
  return JInt.wrap .i64 (← heapSlots handle).length

def heapSimilar (handle : Nat) : VectorM α Nat := do
  let slots ← heapSlots handle
  let heap ← get
  set (heap ++ [List.replicate slots.length none])
  return heap.length

/-- The memory.jl reference primitive, with array handles as stable heap positions. -/
def heapReference (handle : Nat) (i : I) : VectorM α (Nat × I) :=
  pure (handle, i)

def heapBounds (handle : Nat) (i : I) : VectorM α Unit := do
  let slots ← heapSlots handle
  if !(1 ≤ i.val ∧ i.val ≤ (slots.length : Int)) then throw .bounds

/-- A memory copy reads the source snapshot before writing the destination.
The conversion callback is the selected memory.jl element-copy operation. -/
def heapCopyReferences (convert : Option α → Except Error (Option α))
    (dest src : Nat × I) (n : I) : VectorM α Unit := do
  let source ← heapSlots src.1
  let destination ← heapSlots dest.1
  if !(0 ≤ n.val ∧ 1 ≤ dest.2.val ∧
      dest.2.val - 1 + n.val ≤ (destination.length : Int) ∧
      1 ≤ src.2.val ∧ src.2.val - 1 + n.val ≤ (source.length : Int)) then throw .bounds
  let values ← liftM (((source.drop (src.2.val - 1).toNat).take n.val.toNat).mapM convert)
  let updated := destination.take (dest.2.val - 1).toNat ++ values ++
    destination.drop (dest.2.val - 1 + n.val).toNat
  modify fun heap => heap.set dest.1 updated

/-- Checked array copying instantiated with the concrete shared heap primitives. -/
def heapCheckedCopy (convert : Option α → Except Error (Option α)) :=
  copyto288 (copytoImpl
    (fun n : I => pure (decide (n.val = 0))) (fun n : I => pure (decide (n.val > 0)))
    heapLength heapLength heapBounds heapBounds
    (fun a b => pure (a - b)) (fun a b => pure (a - b))
    (fun a b => pure (a + b)) (fun a b => pure (a + b))
    (fun n rem : I => pure (decide (n.val ≤ rem.val)))
    (fun n rem : I => pure (decide (n.val ≤ rem.val)))
    (fun _ _ => throw .bounds) (fun _ _ => throw .bounds)
    pure pure pure heapReference heapReference (heapCopyReferences convert))

def heapWholeCopy (convert : Option α → Except Error (Option α)) :=
  copyto325 (fun _ => pure one) (fun _ => pure one) heapLength (heapCheckedCopy convert)

/-- Allocating a fresh vector appends a distinct heap object and preserves old handles. -/
def heapAllocate (n : Nat) : VectorM α Nat := do
  let heap ← get
  set (heap ++ [List.replicate n none])
  pure heap.length

/-- Array header metadata is separate from the shared reference slots. -/
structure HeapArray (Tag : Type) where
  handle : Nat
  elementType : Tag
  dimensions : List Nat
  axes : List (Int × Nat)
  deriving Repr

def heapDimensionsFit (dimensions : List Nat) : Bool :=
  dimensions.all (fun n => decide (n < 2 ^ 63))

/-! ## Runtime memory allocation (`memorynew`) -/

/-- The fields of an element type's `jl_datatype_layout_t` that `jl_alloc_genericmemory` reads:
`layout->size`, `layout->flags.arrayelem_isboxed` and `layout->flags.arrayelem_isunion`. -/
structure MemoryLayout where
  size : Nat
  isboxed : Bool
  isunion : Bool
  deriving Repr, DecidableEq

/--
  Julia source: src/genericmemory.c:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
#define MAXINTVAL (((size_t)-1)>>1)
```
-/
def maxIntVal : Nat := 2 ^ 64 / 2 - 1

/-- `__builtin_mul_overflow` on `size_t`: the wrapped product and whether it overflowed. -/
def sizeMulOverflow (a b : Nat) : Nat × Bool := ((a * b) % 2 ^ 64, decide (2 ^ 64 ≤ a * b))

/-- `__builtin_add_overflow` on `size_t`: the wrapped sum and whether it overflowed. -/
def sizeAddOverflow (a b : Nat) : Nat × Bool := ((a + b) % 2 ^ 64, decide (2 ^ 64 ≤ a + b))

def genericMemorySizeMessage : String :=
  "invalid GenericMemory size: the number of elements is either negative or too large for system address width"

/--
  Julia source: src/genericmemory.c:55-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_genericmemory_t *_new_genericmemory_(jl_value_t *mtype, size_t nel, int8_t isunion, int8_t zeroinit, size_t elsz) JL_CANSAFEPOINT
{
    if (nel == 0) // zero-sized allocation optimization
        return (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
    size_t nbytes = 0; // initialized to workaround clang sa bug on v20: https://github.com/llvm/llvm-project/issues/136292
    int overflow = __builtin_mul_overflow(nel, elsz, &nbytes);
    if (isunion) {
        // an extra byte for each isbits union memory element, stored at m->ptr + m->length
        overflow |= __builtin_add_overflow(nel, nbytes, &nbytes);
    }
    if ((nel >= MAXINTVAL-1) || (nbytes >= MAXINTVAL-1) || overflow)
        jl_exceptionf(jl_argumenterror_type, "invalid GenericMemory size: the number of elements is either negative or too large for system address width");
    jl_task_t *ct = jl_current_task;
    jl_genericmemory_t *m = jl_alloc_genericmemory_unchecked((jl_ptls_t) ct->ptls, nbytes, (jl_datatype_t*)mtype);
    m->length = nel;
    if (zeroinit)
        memset((char*)m->ptr, 0, nbytes);
    return m;
}
```
The memory is `allocate nel`; its slots start unassigned. The zero-element memory is the type's
shared empty instance, `empty`.
-/
def newGenericMemory [Monad m] [MonadExceptOf Error m] (empty : m Mem) (allocate : Nat → m Mem)
    (nel : Nat) (isunion : Bool) (elsz : Nat) : m Mem := do
  if nel = 0 then
    return (← empty)
  let (nbytes, overflow) := sizeMulOverflow nel elsz
  let (nbytes, overflow) :=
    if isunion then
      let r := sizeAddOverflow nel nbytes
      (r.1, overflow || r.2)
    else (nbytes, overflow)
  if nel ≥ maxIntVal - 1 || nbytes ≥ maxIntVal - 1 || overflow then
    throw (Error.argument genericMemorySizeMessage)
  allocate nel

/--
  Julia source: src/genericmemory.c:75-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_genericmemory_t *jl_alloc_genericmemory(jl_value_t *mtype, size_t nel)
{
    assert(jl_is_datatype(mtype));
    jl_genericmemory_t *m = (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
    const jl_datatype_layout_t *layout = ((jl_datatype_t*)mtype)->layout;
    if (m == NULL) {
        jl_value_t *kind = jl_tparam0((jl_datatype_t*)mtype);
        if (kind != (jl_value_t*)jl_not_atomic_sym && kind != (jl_value_t*)jl_atomic_sym)
            jl_error("GenericMemory kind must be :not_atomic or :atomic");
        jl_value_t *addrspace = jl_tparam2((jl_datatype_t*)mtype);
        if (!jl_is_addrspacecore(addrspace) || jl_unbox_uint8(addrspace) != 0)
            jl_error("GenericMemory addrspace must be Core.CPU");
        if (!((jl_datatype_t*)mtype)->has_concrete_subtype || layout == NULL)
            jl_type_error_rt("GenericMemory", "element type", (jl_value_t*)jl_type_type, jl_tparam1(mtype));
        abort(); // this is checked already by jl_get_genericmemory_layout
    }
    assert(((jl_datatype_t*)mtype)->has_concrete_subtype && layout != NULL);
    if (nel == 0) // zero-sized allocation optimization fast path
        return m;

    size_t elsz = layout->size;
    int isboxed = layout->flags.arrayelem_isboxed;
    int isunion = layout->flags.arrayelem_isunion;
    int zi = ((jl_datatype_t*)mtype)->zeroinit;
    if (isboxed)
        elsz = sizeof(void*);
    return _new_genericmemory_(mtype, nel, isunion, zi, elsz);
}
```
`layout` is `none` exactly when the memory type has no instance. Array memory is always
`Memory{T}` (kind `:not_atomic`, addrspace `CPU`), so the kind and addrspace `jl_error` branches
cannot fire for these callers and the remaining branch is the element-type `TypeError`.
`sizeof(void*)` is 8 on the modeled 64-bit platform.
-/
def allocGenericMemory [Monad m] [MonadExceptOf Error m] (layout : Option MemoryLayout)
    (empty : m Mem) (allocate : Nat → m Mem) (nel : Nat) : m Mem := do
  match layout with
  | none => throw (Error.typeError "GenericMemory")
  | some l =>
    if nel = 0 then
      return (← empty)
    let elsz := if l.isboxed then 8 else l.size
    newGenericMemory empty allocate nel l.isunion elsz

/--
  Julia source: src/builtins.c:2233-2241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_CALLABLE(jl_f_memorynew)
{
    JL_NARGS(memorynew, 2, 2);
    jl_datatype_t *jl_genericmemory_type_type = jl_datatype_type;
    JL_TYPECHK(memorynew, genericmemory_type, args[0]);
    JL_TYPECHK(memorynew, long, args[1]);
    size_t nel = jl_unbox_long(args[1]);
    return (jl_value_t*)jl_alloc_genericmemory(args[0], nel);
}
```
`jl_unbox_long` read as `size_t`: a negative `Int` becomes `m + 2^64`.
-/
def memorynew [Monad m] [MonadExceptOf Error m] (layout : Option MemoryLayout)
    (empty : m Mem) (allocate : Nat → m Mem) (n : I) : m Mem :=
  allocGenericMemory layout empty allocate (n.val % 2 ^ 64).toNat

/--
  Julia source: base/boot.jl:762-762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, m::Int) where {T,addrspace,kind} = memorynew(self, m)
```
-/
def memoryUndef [Monad m] [MonadExceptOf Error m] (layout : Option MemoryLayout)
    (empty : m Mem) (allocate : Nat → m Mem) (n : I) : m Mem :=
  memorynew layout empty allocate n

/-! ## Dimension checks -/

/--
  Julia source: base/boot.jl:559-559 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const typemax_Int = Core.Intrinsics.udiv_int(Core.Intrinsics.sext_int(Int, 0xFF), 2)
```
-/
def typemaxInt : I := JInt.wrap .i64 (2 ^ 63 - 1)

/-- `Intrinsics.checked_smul_int(a, b)`: the wrapped product and whether it overflowed. -/
def checkedSmulInt (a b : I) : I × Bool :=
  (JuliaLean.base.int.mul_int a b,
    !decide (IntTy.min .i64 ≤ a.val * b.val ∧ a.val * b.val ≤ IntTy.max .i64))

/--
  Julia source: base/boot.jl:782-782 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_checked_mul_dims() = 1, false
```
-/
def checkedMulDims0 : I × Bool := (one, false)

/--
  Julia source: base/boot.jl:783-783 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_checked_mul_dims(m::Int) = m, Intrinsics.ule_int(typemax_Int, m) # equivalently: (m + 1) < 1
```
-/
def checkedMulDims1 (m : I) : I × Bool := (m, JuliaLean.base.int.ule_int typemaxInt m)

/--
  Julia source: base/boot.jl:784-791 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _checked_mul_dims(m::Int, n::Int)
    b = Intrinsics.checked_smul_int(m, n)
    a = getfield(b, 1)
    ovflw = getfield(b, 2)
    ovflw = Intrinsics.or_int(ovflw, Intrinsics.ule_int(typemax_Int, m))
    ovflw = Intrinsics.or_int(ovflw, Intrinsics.ule_int(typemax_Int, n))
    return a, ovflw
end
```
-/
def checkedMulDims2 (m n : I) : I × Bool :=
  let b := checkedSmulInt m n
  let a := b.1
  let ovflw := b.2
  let ovflw := ovflw || JuliaLean.base.int.ule_int typemaxInt m
  let ovflw := ovflw || JuliaLean.base.int.ule_int typemaxInt n
  (a, ovflw)

/-- The `while` loop of `_checked_mul_dims(m, d...)` over the remaining `d`. -/
def checkedMulDimsLoop : List I → I → Bool → Bool → Bool → I × Bool
  | [], a, ovflw, neg, zero => (a, neg || (ovflw && !zero))
  | di :: d, a, ovflw, neg, zero =>
    let b := checkedSmulInt a di
    let zero := zero || decide (di.val = 0)
    let ovflw := ovflw || b.2
    let neg := neg || JuliaLean.base.int.ule_int typemaxInt di
    checkedMulDimsLoop d b.1 ovflw neg zero

/--
  Julia source: base/boot.jl:792-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _checked_mul_dims(m::Int, d::Int...)
    @_foldable_meta # the compiler needs to know this loop terminates
    a = m
    i = 1
    ovflw = false
    neg = Intrinsics.ule_int(typemax_Int, m)
    zero = false # if m==0 we won't have overflow since we go left to right
    while Intrinsics.sle_int(i, nfields(d))
        di = getfield(d, i)
        b = Intrinsics.checked_smul_int(a, di)
        zero = Intrinsics.or_int(zero, di === 0)
        ovflw = Intrinsics.or_int(ovflw, getfield(b, 2))
        neg = Intrinsics.or_int(neg, Intrinsics.ule_int(typemax_Int, di))
        a = getfield(b, 1)
        i = Intrinsics.add_int(i, 1)
   end
   return a, Intrinsics.or_int(neg, Intrinsics.and_int(ovflw, Intrinsics.not_int(zero)))
end
```
-/
def checkedMulDimsMany (m : I) (d : List I) : I × Bool :=
  checkedMulDimsLoop d m false (JuliaLean.base.int.ule_int typemaxInt m) false

/-- Method dispatch of `_checked_mul_dims(d...)` on the argument count. -/
def checkedMulDims : List I → I × Bool
  | [] => checkedMulDims0
  | [m] => checkedMulDims1 m
  | [m, n] => checkedMulDims2 m n
  | m :: d => checkedMulDimsMany m d

/--
  Julia source: base/boot.jl:812-812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_dims() = 1
```
-/
def checkedDims0 : I := one

/--
  Julia source: base/boot.jl:813-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_dims(m::Int) = m # defer this check to Memory constructor instead
```
-/
def checkedDims1 (m : I) : I := m

/--
  Julia source: base/boot.jl:814-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checked_dims(d::Int...)
    b = _checked_mul_dims(d...)
    getfield(b, 2) && throw(ArgumentError("invalid Array dimensions"))
    return getfield(b, 1)
end
```
-/
def checkedDimsMany [Monad m] [MonadExceptOf Error m] (d : List I) : m I := do
  let b := checkedMulDims d
  if b.2 then throw (Error.argument "invalid Array dimensions")
  return b.1

/-- Method dispatch of `checked_dims(d...)` on the argument count. -/
def checkedDims [Monad m] [MonadExceptOf Error m] : List I → m I
  | [] => pure checkedDims0
  | [m] => pure (checkedDims1 m)
  | d => checkedDimsMany d

/-! ## `Array{T,N}(undef, dims)` -/

/--
  Julia source: base/boot.jl:779-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
new_as_memoryref(self::Type{GenericMemoryRef{kind,T,addrspace}}, m::Int) where {T,kind,addrspace} = memoryref(fieldtype(self, :mem)(undef, m))
```
-/
def newAsMemoryref [Monad m] [MonadExceptOf Error m] (layout : Option MemoryLayout)
    (empty : m Mem) (allocate : Nat → m Mem) (n : I) : m Mem :=
  memoryUndef layout empty allocate n

/--
  Julia source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
    mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
    return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
end))
```
-/
def arrayUndef1 [Monad m] [MonadExceptOf Error m] (layout : Option MemoryLayout)
    (empty : m Mem) (allocate : Nat → m Mem) (header : Mem → List I → m A) (m' : I) : m A := do
  let mem ← memoryUndef layout empty allocate m'
  header mem [m']

/--
  Julia source: base/boot.jl:825-827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
    return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
end))
```
-/
def arrayUndef2 [Monad m] [MonadExceptOf Error m] (layout : Option MemoryLayout)
    (empty : m Mem) (allocate : Nat → m Mem) (header : Mem → List I → m A) (m' n : I) : m A := do
  let mem ← newAsMemoryref layout empty allocate (← checkedDims [m', n])
  header mem [m', n]

/--
  Julia source: base/boot.jl:828-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eval(Core, :(function (self::Type{Array{T,3}})(::UndefInitializer, m::Int, n::Int, o::Int) where {T}
    return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n, o))), :((m, n, o))))
end))
```
-/
def arrayUndef3 [Monad m] [MonadExceptOf Error m] (layout : Option MemoryLayout)
    (empty : m Mem) (allocate : Nat → m Mem) (header : Mem → List I → m A) (m' n o : I) : m A := do
  let mem ← newAsMemoryref layout empty allocate (← checkedDims [m', n, o])
  header mem [m', n, o]

/--
  Julia source: base/boot.jl:831-833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eval(Core, :(function (self::Type{Array{T, N}})(::UndefInitializer, d::Vararg{Int, N}) where {T, N}
    return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(d...))), :d))
end))
```
-/
def arrayUndefN [Monad m] [MonadExceptOf Error m] (layout : Option MemoryLayout)
    (empty : m Mem) (allocate : Nat → m Mem) (header : Mem → List I → m A) (d : List I) : m A := do
  let mem ← newAsMemoryref layout empty allocate (← checkedDims d)
  header mem d

/-- Method dispatch of `Array{T,N}(undef, d::NTuple{N,Int})` (boot.jl:835-838, 840-845) on `N`:
the specialised methods for `N = 1, 2, 3`, the `Vararg` method otherwise (including `N = 0`). -/
def arrayUndef [Monad m] [MonadExceptOf Error m] (layout : Option MemoryLayout)
    (empty : m Mem) (allocate : Nat → m Mem) (header : Mem → List I → m A) : List I → m A
  | [m'] => arrayUndef1 layout empty allocate header m'
  | [m', n] => arrayUndef2 layout empty allocate header m' n
  | [m', n, o] => arrayUndef3 layout empty allocate header m' n o
  | d => arrayUndefN layout empty allocate header d

/-- `Array{T,N}(undef, dims)` on the shared heap: the memory is a fresh heap object of `nel`
unassigned slots (an empty one for zero elements; no slot read or write can tell it from the
shared empty instance), and the header records the dimensions, all nonnegative on success. -/
def heapArrayUndef {Tag α : Type} (layout : Tag → Option MemoryLayout) (target : Tag) (dims : List I) :
    VectorM α (HeapArray Tag) :=
  arrayUndef (layout target) (heapAllocate 0) heapAllocate
    (fun handle ds => pure ⟨handle, target, ds.map (·.val.toNat), ds.map (fun d => (1, d.val.toNat))⟩)
    dims

/-- `Vector{T}(undef, n)`. -/
def heapVectorAllocate {Tag α : Type} (layout : Tag → Option MemoryLayout) (target : Tag) (n : I) :
    VectorM α (HeapArray Tag) :=
  heapArrayUndef layout target [n]

/-- `Array{T,N}(undef, dims)` for `Int` dimensions. -/
def heapAllocateIntDims {Tag α : Type} (layout : Tag → Option MemoryLayout) (target : Tag) (dims : List I) :
    VectorM α (HeapArray Tag) :=
  heapArrayUndef layout target dims

/-- Dimensions given as naturals are first converted by `Int` (`InexactError` for one beyond
`typemax(Int)`), then allocated as above. -/
def heapAllocateArray {Tag α : Type} (layout : Tag → Option MemoryLayout) (elementType : Tag)
    (dimensions : List Nat) : VectorM α (HeapArray Tag) := do
  if !(heapDimensionsFit dimensions) then throw .inexact
  heapArrayUndef layout elementType (dimensions.map (fun n : Nat => JInt.wrap .i64 (Int.ofNat n)))

/-- The fields of one Array header; memory belongs to the shared heap. -/
structure MutableVector where
  reference : Nat × I
  size : I
  deriving Repr

/-- Concrete memory primitives retain writes when a later Julia operation throws. -/
structure MutableMemory (α : Type) where
  memories : List (List (Option α))
  arrays : List MutableVector
  deriving Repr

abbrev MutationM (α : Type) := ExceptT Error (StateM (MutableMemory α))

def MutableMemory.initial (xs : List (Option α)) : MutableMemory α :=
  ⟨[xs ++ List.replicate 32 none], [⟨(0, one), JInt.wrap .i64 xs.length⟩]⟩

def MutableMemory.initialMany (vectors : List (List (Option α))) : MutableMemory α :=
  ⟨vectors.map (fun xs => xs ++ List.replicate 32 none),
    vectors.zipIdx |>.map fun (xs, i) => MutableVector.mk (i, one) (JInt.wrap .i64 xs.length)⟩

def MutableMemory.contents (s : MutableMemory α) (handle : Nat := 0) : List (Option α) :=
  match s.arrays[handle]? with
  | none => []
  | some a =>
    ((s.memories[a.reference.1]?.getD []).drop (a.reference.2.val - 1).toNat).take a.size.val.toNat

/-- A live Array header describes a nonnegative, in-memory window. -/
def MutableMemory.validVector (s : MutableMemory α) (handle : Nat) : Prop :=
  match s.arrays[handle]? with
  | none => False
  | some a =>
    match s.memories[a.reference.1]? with
    | none => False
    | some slots =>
      0 ≤ a.size.val ∧ 1 ≤ a.reference.2.val ∧
      a.reference.2.val - 1 + a.size.val ≤ (slots.length : Int) ∧
      slots.length < 2 ^ 63

instance (s : MutableMemory α) (handle : Nat) : Decidable (s.validVector handle) := by
  unfold MutableMemory.validVector
  split
  · infer_instance
  · split <;> infer_instance

def memoryRead (mem : Nat) : MutationM α (List (Option α)) := do
  match (← get).memories[mem]? with
  | some xs => pure xs
  | none => throw .bounds

def memoryWrite (mem : Nat) (i : I) (x : Option α) : MutationM α Unit := do
  let xs ← memoryRead mem
  if !(1 ≤ i.val ∧ i.val ≤ (xs.length : Int)) then throw .bounds
  modify fun s => { s with memories := s.memories.set mem (xs.set (i.val - 1).toNat x) }

def memoryMove (dest : Nat) (doffs : I) (src : Nat) (soffs n : I) : MutationM α Unit := do
  let source ← memoryRead src
  let destination ← memoryRead dest
  if !(0 ≤ n.val ∧ 1 ≤ doffs.val ∧ doffs.val - 1 + n.val ≤ (destination.length : Int) ∧
      1 ≤ soffs.val ∧ soffs.val - 1 + n.val ≤ (source.length : Int)) then throw .bounds
  let values := (source.drop (soffs.val - 1).toNat).take n.val.toNat
  for (x, k) in values.zipIdx do
    memoryWrite dest (doffs + JInt.wrap .i64 k) x

def mutableVector (handle : Nat) : MutationM α MutableVector := do
  match (← get).arrays[handle]? with
  | some a => pure a
  | none => throw .bounds

def mutableLength (a : Nat) : MutationM α I := do return (← mutableVector a).size

def mutableRef (a : Nat) : MutationM α (Nat × I) := do return (← mutableVector a).reference

def mutableGet (a : Nat) (i : I) : MutationM α α := do
  let s ← mutableVector a
  if !(1 ≤ i.val ∧ i ≤ s.size) then throw .bounds
  let xs ← memoryRead s.reference.1
  match xs[(s.reference.2.val + i.val - 2).toNat]? with
  | some (some x) => pure x
  | some none => throw .undefinedReference
  | none => throw .bounds

/-- The array bounds predicate and memory-reference primitives live outside array.jl. -/
def mutableInBounds (a : Nat) (i : I) : MutationM α Bool := do
  return decide (one ≤ i ∧ i ≤ (← mutableLength a))

def mutableBounds (a : Nat) (i : I) : MutationM α Unit := do
  if !(← mutableInBounds a i) then throw .bounds

def mutableMemoryref (a : Nat) (i : I) : MutationM α (Nat × I) := do
  let ref ← mutableRef a
  pure (ref.1, ref.2 + i - one)

def mutableSet (a : Nat) (x : α) (i : I) : MutationM α Unit := do
  let _ ← setindexTyped mutableBounds
    (fun a i _ => mutableMemoryref a i)
    (fun ref value _ => memoryWrite ref.1 ref.2 (some value)) a x i
  pure ()

/-- Raw-cell access preserves the memory bounds checks without introducing a value
read or an UndefRefError for an unassigned slot. -/
def mutableMemoryUnset (layout : DictLayout) (mem : Nat) (i : I) : MutationM α Unit := do
  let slots ← memoryRead mem
  let old ← match slots[(i.val - 1).toNat]? with
    | some value => pure value
    | none => throw .bounds
  memoryWrite mem i (unsetCell layout i.val.toNat old)

/--
Julia source: base/array.jl:209-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsetindex!(A::Array, i::Int)
    @inline
    @boundscheck checkbounds(A, i)
    @inbounds unsetindex!(memoryref(A.ref, i))
    return A
end
```
-/
def mutableUnset (layout : DictLayout) (a : Nat) (i : I) : MutationM α Unit := do
  let _ ← unsetindexInt mutableBounds mutableMemoryref
    (fun ref => mutableMemoryUnset layout ref.1 ref.2) a i
  pure ()

def mutableAssigned (a : Nat) (i : I) : MutationM α Bool :=
  isassignedVector mutableInBounds
    (fun a i _ => mutableMemoryref a i)
    (fun ref => do return ((← memoryRead ref.1)[(ref.2.val - 1).toNat]?.join).isSome) a i

def mutableCopy (dest : Nat) (doffs : I) (src : Nat) (soffs n : I) : MutationM α Unit := do
  let _ ← unsafeCopyArray (fun n : I => n.val == 0) mutableMemoryref mutableMemoryref
    (fun d s n => memoryMove d.1 d.2 s.1 s.2 n) dest doffs src soffs n
  pure ()

def mutableCopyto (dest : Nat) (doffs : I) (src : Nat) (soffs n : I) : MutationM α Unit := do
  let _ ← copyto288
    (copytoImpl
      (fun n : I => pure (decide (n.val = 0))) (fun n : I => pure (decide (n.val > 0)))
      mutableLength mutableLength mutableBounds mutableBounds
      (fun a b => pure (a - b)) (fun a b => pure (a - b))
      (fun a b => pure (a + b)) (fun a b => pure (a + b))
      (fun n rem : I => pure (decide (n.val ≤ rem.val)))
      (fun n rem : I => pure (decide (n.val ≤ rem.val)))
      (fun _ _ => throw .bounds) (fun _ _ => throw .bounds)
      pure pure pure mutableMemoryref mutableMemoryref
      (fun d s n => memoryMove d.1 d.2 s.1 s.2 n))
    dest doffs src soffs n
  pure ()

/-- A fresh memory of `n` unassigned slots in the growable-vector store. -/
def mutableFreshMemory (n : Nat) : MutationM α Nat := do
  let s ← get
  let mem := s.memories.length
  set { s with memories := s.memories ++ [List.replicate n none] }
  pure mem

/-- `Vector{T}(undef, n)` (boot.jl:821-824) in the growable-vector store, for element layout `layout`. -/
def mutableAllocate (layout : Option MemoryLayout) (_a : Nat) (n : I) : MutationM α Nat :=
  arrayUndef1 layout (mutableFreshMemory 0) mutableFreshMemory
    (fun mem dims => do
      let s ← get
      let handle := s.arrays.length
      set { s with arrays := s.arrays ++ [MutableVector.mk (mem, one) (dims.headD n)] }
      pure handle)
    n

/-- Allocation metadata projected from the same native GenericMemory header. -/
def allocationSummary (layout : DictLayout) : MemoryLayout :=
  ⟨layout.metadata.memoryLayout.size.val.toNat,
    JuliaLean.src.genericmemory_c.isBoxed layout.metadata,
    JuliaLean.src.genericmemory_c.isUnion layout.metadata⟩

structure MemoryLayoutMetadata where
  allocation : Option MemoryLayout
  runtime : DictLayout
  allocation_matches : match allocation with
    | none => True
    | some summary => summary = allocationSummary runtime

def MemoryLayoutMetadata.ofRuntime (layout : DictLayout) : MemoryLayoutMetadata :=
  ⟨some (allocationSummary layout), layout, rfl⟩

def mutableStorage (layout : MemoryLayoutMetadata) : Storage (MutationM α) Nat Nat (Nat × I) where
  ref := mutableRef
  memory := Prod.fst
  offset := Prod.snd
  length := mutableLength
  memLength := fun mem => do return JInt.wrap .i64 (← memoryRead mem).length
  sameRef := fun a b => a == b
  sameMem := fun a b => a == b
  setRef := fun a ref => do
    let v ← mutableVector a
    modify fun s => { s with arrays := s.arrays.set a { v with reference := ref } }
  setSize := fun a n => do
    let v ← mutableVector a
    modify fun s => { s with arrays := s.arrays.set a { v with size := n } }
  memoryref := fun mem offset => pure (mem, offset)
  shiftref := fun ref offset => pure (ref.1, ref.2 + offset - one)
  allocate := fun _ n => memoryUndef layout.allocation (mutableFreshMemory 0) mutableFreshMemory n
  copyMemory := memoryMove
  copyRef := fun d s n => memoryMove d.1 d.2 s.1 s.2 n
  unsetMemory := mutableMemoryUnset layout.runtime
  unsetArray := mutableUnset layout.runtime
  checkedAdd := fun a b =>
    if IntTy.i64.min ≤ a.val + b.val ∧ a.val + b.val ≤ IntTy.i64.max then
      pure (a + b)
    else throw .overflow
  checkedMul := fun a b =>
    if IntTy.i64.min ≤ a.val * b.val ∧ a.val * b.val ≤ IntTy.i64.max then
      pure (a * b)
    else throw .overflow
  divide := fun a b =>
    if b.val = 0 then throw .divide
    else pure (JInt.wrap .i64 (a.val.tdiv b.val))
  overallocation := overallocation
    (fun n => JInt.wrap .i64 (if n.val = 0 then 64 else 63 - (n.val.toNat.log2 : Int)))
    (fun a b => pure (JInt.wrap .i64 (a.val.tdiv b.val)))
    (fun a b => JInt.wrap .i64 (a.val * (2 : Int) ^ b.val.toNat))

def mutablePush (layout : MemoryLayoutMetadata) (a : Nat) (x : α) : MutationM α Unit := do
  let _ ← push1361 (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
    mutableLength mutableSet a x
  pure ()

def mutableTypedSet (a : Nat) (x : α) (i : I) : MutationM α Nat :=
  setindexTyped mutableBounds (fun a i _ => mutableMemoryref a i)
    (fun ref value _ => memoryWrite ref.1 ref.2 (some value)) a x i

/-- A remaining-list state implements Julia's finite iterator protocol. -/
def listIterator [Monad m] (xs : List α) : FiniteIterator m α (List α) where
  rank := List.length
  first := pure (match xs with | [] => none | x :: tail => some (x, tail))
  next := fun st => pure (match st with
    | [] => none
    | x :: tail => some (x, ⟨tail, by simp⟩))

/-- Hash-table insertion retains the first key for an equal value. -/
def dictInsertFirst [Monad m] [MonadStateOf (List (α × K)) m]
    (equal : α → α → Bool) (value : α) (key : K) : m Unit :=
  modify fun entries => if entries.any (fun p => equal value p.1) then entries
    else entries ++ [(value, key)]

def dictGet [Monad m] [MonadStateOf (List (α × K)) m]
    (equal : α → α → Bool) (value : α) (default : Option K) : m (Option K) := do
  return ((← get).find? (fun p => equal value p.1)).map Prod.snd |>.or default

/-- Column-major Cartesian keys, used by the multidimensional bounds primitives. -/
def cartesianKeys : List Nat → List (List I)
  | [] => [[]]
  | n :: tail => (cartesianKeys tail).flatMap fun key =>
      (List.range n).map fun (i : Nat) => JInt.wrap .i64 ((i : Int) + 1) :: key

def cartesianGreater (a b : List I) : Bool :=
  compare (a.reverse.map Subtype.val) (b.reverse.map Subtype.val) == Ordering.gt

def cartesianRank (dims : List Nat) (key : List I) : Nat :=
  ((cartesianKeys dims).filter (fun other => cartesianGreater other key)).length

def cartesianNext (dims : List Nat) (key : List I) :
    Except Error { next : List I // cartesianRank dims next < cartesianRank dims key } :=
  match (cartesianKeys dims).find? (fun other => cartesianGreater other key) with
  | none => .error .bounds
  | some next =>
    if h : cartesianRank dims next < cartesianRank dims key then .ok ⟨next, h⟩
    else .error .bounds

end JuliaLean.base.array

/-
Method inventory (pinned Julia source line -> Lean definition).
14 -> dimensionMismatch
132 -> safeindexMacro
135 -> safeindex
158 -> vectEmpty
159 -> vectTyped
183 -> vectPromoted
188 -> asizeFrom
190 -> allocatedinline
206 -> isbitsunion
208 -> unsetindexInteger
209 -> unsetindexInt
218 -> elsizeArray
219 -> elsizePtr
226 -> elsizeBottom
227 -> elsizeBottomArgs
229 -> sizeofArray
231 -> isassignedArray
239 -> isassignedVector
259 -> unsafeCopyPtr
276 -> unsafeCopyArray
288 -> copyto288
290 -> copyto290
292 -> copyto292
296 -> copyto296
299 -> copytoImpl
321 -> throwArgument
323 -> copyto2arg
325 -> copyto325
326 -> copyto326
327 -> copyto327
330 -> copyto330
331 -> copyto331
332 -> copyto332
368 -> fillBang
373 -> fillTyped
391 -> JuliaLean.base.abstractarray.ArrayCallees.copyArray
402 -> takeBang
414 -> similar414
415 -> similar415
416 -> similar416
417 -> similar417
418 -> similar418
419 -> similar419
420 -> similar420
421 -> similar421
445 -> typedLiteral
463 -> anyLiteral
471 -> anyLiteralEmpty
473 -> fillBytes
482 -> toDimInteger
483 -> toDimOneTo
583 -> fillVarargs
584 -> fillMixedDims
585 -> fill585
586 -> fill586
587 -> fill587
633 -> constantVarargs
634 -> constantTypedVarargs
635 -> constantDefaultType
636 -> constantMixedDims
637 -> constant637
642 -> constant642
647 -> constant647
657 -> convertArray
659 -> promoteArrayRule
664 -> arrayConstructor
665 -> abstractArrayConstructor
684 -> collectTyped
686 -> collectSized
688 -> collectUnknown
697 -> similarForGeneric
699 -> similarShapeUnknown
700 -> similarShapeLength
701 -> similarShapeAxes
703 -> similarForUnknown
705 -> similarForLength
707 -> similarForAxes
711 -> arrayForUnknown
712 -> arrayForLength
713 -> arrayForShape
716 -> arrayFor
771 -> collect
773 -> collectArray
775 -> collectSimilar
777 -> collectKnownSized
780 -> collectKnownUnknown
788 -> collectIndicesZero
793 -> collectIndicesOneTo
798 -> collectIndicesGeneric
805 -> iteratorUpperBound
821 -> defaultEltype
833 -> collectGenerator
855 -> collectEltypeUnknown
858 -> collectUnknownSized
875 -> collectWithFirstArray
881 -> collectWithFirst
886 -> setindexWiden
895 -> collectTo
914 -> growFirst
922 -> pushWiden
935 -> growTo
974 -> getindexCartesian
981 -> getindexUnitRange
993 -> getindexBoolRange
995 -> getindexColon
1005 -> getindexRange
1031 -> setindexScalar
1036 -> setindexTyped
1042 -> setindexCartesian
1047 -> setindexCartesianTyped
1055 -> safeSetindex1055
1057 -> safeSetindex1057
1059 -> safeSetindexConvert
1063 -> setindexVector
1078 -> setindexUnitRange
1088 -> setindexColon
1102 -> overallocation
1114 -> arrayNewMemory
1116 -> growbegInternal
1151 -> growbeg
1171 -> growendInternal
1212 -> growend
1225 -> growat
1273 -> deletebeg
1291 -> deleteend
1307 -> deleteatWindow
1353 -> push
1361 -> push1361
1368 -> push1368
1373 -> pushAnyMany
1422 -> appendVector
1430 -> appendIterator
1431 -> pushMany
1432 -> appendMany
1434 -> appendSized
1442 -> appendUnsized
1480 -> prependVector
1495 -> prependIterator
1496 -> pushfirstMany
1497 -> prependMany
1499 -> prependSized
1512 -> prependUnsized
1559 -> resize
1612 -> sizehint
1647 -> sizehintKwcall
1695 -> pop
1736 -> popat
1743 -> popatDefault
1772 -> pushfirst
1777 -> pushfirst1777
1784 -> pushfirst1784
1789 -> pushfirstAnyMany
1831 -> popfirst
1861 -> insert
1866 -> insertTyped
1894 -> deleteatIndex
1900 -> deleteatRange
1940 -> deleteatIndices
1941 -> deleteatIndexVector
1944 -> pushNowhere
1945 -> growendNowhere
1947 -> pushDeleted
1956 -> copyItem
1965 -> deleteatIterator
2000 -> deleteatMask
2065 -> spliceIndex
2120 -> spliceRange
2148 -> spliceIndices
2150 -> empty
2156 -> cmpBytes
2171 -> equalBitInteger2171
2188 -> equalBitIntegerVector
2248 -> reverse
2266 -> reverseDims
2267 -> reverseColon
2268 -> reverseTupleDim
2269 -> reverseIntegerDim
2276 -> reverseind
2283 -> midpoint
2284 -> midpointPromoted
2312 -> reverseBang
2332 -> vcatEmpty
2333 -> hcatEmpty
2335 -> hcat
2344 -> hcatMixed
2346 -> vcat
2361 -> vcatMixed
2363 -> catIntegers
2399 -> findnextBool
2436 -> findfirstBool
2439 -> findfirstArrayBool
2470 -> findnext
2518 -> findfirst
2526 -> findfirstArray
2529 -> findfirstOneTo
2532 -> findfirstZeroOneTo
2533 -> findfirstOneOneTo
2535 -> findfirstUnitRange
2541 -> findfirstStepRange
2549 -> findfirstZeroRange
2550 -> findfirstOneRange
2586 -> findprevBool
2624 -> findlastBool
2627 -> findlastArrayBool
2666 -> findprev
2711 -> findlast
2719 -> findlastArray
2723 -> findlastRange2723
2728 -> findlastRange2728
2784 -> findallPredicate
2791 -> findallArrayPredicate
2833 -> findallGeneric
2838 -> findallBoolArray
2851 -> findallBool
2852 -> findallNumber
2853 -> findallInNumber
2887 -> indexin
2898 -> findinSet
2905 -> findin
2910 -> sortedfindin
2952 -> findallInSorted
2961 -> findallIn2961
2962 -> findallIn2962
2965 -> indcopyVector
2976 -> indcopyTuple
3015 -> filterArray
3027 -> filterAbstractArray
3061 -> filterBang
3100 -> filterFix1
3129 -> keepat3129
3154 -> keepat3154
3159 -> uniqueFilter
3169 -> growFilter
3170 -> shrinkFilter
3172 -> grow
3180 -> unionBang
3183 -> symdiffBang
3186 -> shrink
3193 -> intersectBang
3194 -> setdiffBang
3196 -> vectorfilter
3198 -> intersect
3204 -> setdiff
3210 -> intersectVectorRange
3216 -> intersectRangeVector
3219 -> getindexAbstractRange
3236 -> wrapCheck
3244 -> invalidWrapError
3249 -> wrapRefDims
3255 -> wrapMemoryDims
3260 -> wrapRefLength
3265 -> wrapMemoryLength
3270 -> wrapMemory
-/

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

/-- A representable Julia argument tuple. The bound is the native `nfields`
length invariant, not an assumption that allocating its result will succeed. -/
structure TupleArgs (α : Type) where
  values : List α
  lengthFits : values.length < 2 ^ 63

/-- Source `base/array.jl:159-166`, with the already-selected homogeneous
`vect` method's allocator and safe setter bound to existing mutable primitives.
`α` represents the selected element type, including reference identities. The
empty public call dispatches to source 158, not this homogeneous overload.
No uninitialized cell is read before being overwritten. The established
allocation boundary does not expose physical OOM, GC, or empty-memory identity. -/
-- Source: base/array.jl:159-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function vect(X::T...) where T
--     @_terminates_locally_meta
--     vec = Vector{T}(undef, length(X))
--     @_safeindex for i = 1:length(X)
--         vec[i] = X[i]
--     end
--     return vec
-- end
-- /Source
def vectHomogeneous {α : Type} (layout : Option MemoryLayout)
    (args : TupleArgs α) : MutationM α Nat :=
  vectTyped (mutableAllocate layout 0)
    (safeSetindex1057
      (fun a i _ => mutableMemoryref a i)
      (fun reference value _ => memoryWrite reference.1 reference.2 (some value)))
    args.values

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean

abbrev LayoutM := JuliaLean.base.io.M

/-- Reuse the existing runtime/interface boundaries without supplying a missing
Base layout implementation. `types` is runtime_internals.TypeOps;
`jlStoredInline` and `jlIslayoutInline` are explicit C-call inputs from the
existing array and runtime_internals models.
`newRef` and `readRef` are the RefValue constructor/index interface operands
already exposed by uniontypeLayout. They are not a complete model of RefValue
allocation or indexing. The installed alignedSizeof, uniontypeLayout,
datatypeAlignment, and alignInt implementations are composed below. -/
structure LayoutBoundary (World V D N Mod P Sym Ref : Type) where
  types : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym
  jlStoredInline : V → JInt .i32
  newRef : JInt .u64 → LayoutM World Ref
  readRef : Ref → LayoutM World (JInt .u64)
  jlIslayoutInline : V → Ref → Ref → LayoutM World (JInt .i32)

/-- Source base/array.jl:218, composed over the existing Core/C and RefValue
interface boundaries above. Array type parameter T is `elementType`; no
correctness assumption or opaque replacement for aligned_sizeof is supplied. -/
-- Source: base/array.jl:218-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- elsize(::Type{A}) where {T,A<:Array{T}} = aligned_sizeof(T)
-- /Source
def elsizeArrayRuntime
    (runtime : LayoutBoundary World V D N Mod P Sym Ref)
    (elementType : V) : LayoutM World (JInt .i64) :=
  JuliaLean.base.runtime_internals.alignedSizeof runtime.types
    (fun t => pure (JuliaLean.base.array.allocatedinline runtime.jlStoredInline t))
    (JuliaLean.base.runtime_internals.uniontypeLayout
      runtime.newRef runtime.readRef runtime.jlIslayoutInline)
    (JInt.wrap .i64 8) elementType

/-- Bind the existing elsizePtr wrapper to installed Julia alignment code and
existing Core type operations. Source base/array.jl:219-225. Importantly, the
`sizeof(Any)` action is evaluated for a non-DataType; its native exception is
propagated before any attempt to obtain that type's layout. The Any fast path
uses the pinned 64-bit pointer size and does not execute any M action. -/
-- Source: base/array.jl:219-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function elsize(::Type{Ptr{T}}) where T
--     # this only must return something valid for values which satisfy is_valid_intrinsic_elptr(T),
--     # which includes Any and most concrete datatypes
--     T === Any && return sizeof(Ptr{Any})
--     T isa DataType || sizeof(Any) # throws
--     return LLT_ALIGN(Core.sizeof(T), datatype_alignment(T))
-- end
-- /Source
def elsizePtrRuntime
    (types : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym)
    (elementType : V) : LayoutM World (JInt .i64) :=
  JuliaLean.base.array.elsizePtr
    (fun t => types.egal t types.any)
    (fun t => (types.asDatatype t).isSome)
    (types.coreSizeof types.any)
    (JInt.wrap .i64 8)
    types.coreSizeof
    (fun t => do
      let some datatype := types.asDatatype t |
        throw (JuliaLean.base.io.Error.foreignError "MethodError" "datatype_alignment")
      JuliaLean.base.runtime_internals.datatypeAlignment types datatype)
    JuliaLean.base.runtime_internals.alignInt elementType

/-- Read-only projection of an existing Array header, not an Array constructor.
No raw slot contents are needed by sizeof. Properties impose necessary native
header representation invariants; this projection alone does not certify
complete byte/address constructibility. All stored dimensions are Julia Ints. -/
structure SizeHeader (V : Type) where
  elementType : V
  dimensions : List (JInt .i64)

/-- A singleton Julia dimension tuple, using the existing list representation
of tuples. Its length witness permits the fixed field-1 projection without a
fallback value or a fabricated bounds-error branch. -/
abbrev SizeTuple1 := { dimensions : List (JInt .i64) // dimensions.length = 1 }

/-- Source base/essentials.jl:12. Bind the installed sizeArray's fixed
getfield(:size) read to the stored dimension tuple. -/
-- Source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- /Source
def sizeHeader (a : SizeHeader V) : List (JInt .i64) :=
  JuliaLean.base.essentials.sizeArray
    (fun a : SizeHeader V => fun _ => a.dimensions) a

/-- Sources base/essentials.jl:13,1296. The one-dimensional method first reads
its singleton size tuple, then projects its fixed first field. Other ranks
reuse lengthAbstract and the existing machine-integer dimension product. -/
-- Source: base/essentials.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
-- Source: base/essentials.jl:1296-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(a::Array{T,1}) where {T} = getfield(getfield(a, :size), 1)
-- /Source
def lengthHeader (a : SizeHeader V) : JInt .i64 :=
  match a.dimensions with
  | [dimension] =>
      JuliaLean.base.essentials.lengthArray1
        (fun (_ : SizeHeader V) (_ : String) =>
          (⟨[dimension], rfl⟩ : SizeTuple1))
        (fun (dimensions : SizeTuple1) (_ : Nat) =>
          dimensions.val.get ⟨0,
            Eq.mpr (congrArg (fun n : Nat => 0 < n) dimensions.property)
              (Nat.zero_lt_succ 0)⟩) a
  | _ =>
      JuliaLean.base.essentials.lengthAbstract sizeHeader
        JuliaLean.base.essentials.prodDims a

/-- Source base/array.jl:229. Obtain length before evaluating elsize; the
existing sizeofArray performs the machine multiplication. Nothing assumes
that a logical element count times its stride fits Int. -/
-- Source: base/array.jl:229-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sizeof(a::Array) = length(a) * elsize(typeof(a)) # n.b. this ignores bitsunion bytes, as a historical fact
-- /Source
def sizeofArrayRuntime
    (runtime : LayoutBoundary World V D N Mod P Sym Ref)
    (a : SizeHeader V) : LayoutM World (JInt .i64) := do
  let count := lengthHeader a
  let stride ← elsizeArrayRuntime runtime a.elementType
  pure (JuliaLean.base.array.sizeofArray
    (fun (_ : Unit) => count) (fun (_ : Unit) => stride) ())

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- A native Memory object's window in a shared physical cell region.
The identity names the Julia object; backing names a MutableMemory.memories region.
The offset and length fields are Julia machine Int values. Used by base/array.jl:231-237 and the partial copy adapters. -/
structure CopyMemoryWindow where
  identity : Nat
  backing : Nat
  offset : I
  length : I

/-- An Array header of arbitrary rank. refOffset is one-based within memory;
dimensions preserve the entire size tuple, including the empty tuple for rank zero.
Used by base/array.jl:231-237 and the partial copy adapters. Header fields are never modified by these methods. -/
structure CopyArrayHeader where
  identity : Nat
  memory : CopyMemoryWindow
  refOffset : I
  dimensions : List I

/-- The native collection projections used at base/array.jl:231-237,299-315.
Every operand in one MutationM alpha run has the same Julia element type,
represented by alpha; no element conversion or type callback is supplied. -/
inductive CopyOperand where
  | array (header : CopyArrayHeader)
  | memory (header : CopyMemoryWindow)

/-- Native Array length used by base/array.jl:231-237. Reuse the installed
size/length composition, preserving the singleton size-tuple intermediate and
wrapping multiplication at every other rank. Sources:
base/essentials.jl:12-13,1296. -/
-- Source: base/essentials.jl:12-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
-- Source: base/essentials.jl:1296-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(a::Array{T,1}) where {T} = getfield(getfield(a, :size), 1)
-- /Source
def copyArrayLength (a : CopyArrayHeader) : I :=
  lengthHeader (V := Unit) ⟨(), a.dimensions⟩

/-- Concrete interpretation of the unchecked reference construction at
base/array.jl:236,310-312 in the existing cell runtime. Every offset operation is
native wrapping Int arithmetic. The source bounds checks and valid
window representation ensure the resulting physical reference is accessible.
Julia source: base/array.jl:310-312; boot.jl:769-770. -/
-- Source: base/array.jl:310-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @inbounds let dest = memoryref(dest isa Array ? getfield(dest, :ref) : dest, doffs),
--                   src = memoryref(src isa Array ? getfield(src, :ref) : src, soffs)
--         unsafe_copyto!(dest, src, n)
-- /Source
def copyOperandReference {α : Type} (a : CopyOperand) (i : I) :
    MutationM α (Nat × I) :=
  match a with
  | .array header => pure (header.memory.backing,
      header.memory.offset + header.refOffset - one + i - one)
  | .memory header => pure (header.backing, header.offset + i - one)


end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- The two existing error families are preserved without collapsing an
abstract-array exception into BoundsError. -/
abbrev AssignedError := Sum Error JuliaLean.base.abstractarray.ArrayError

/-- A local error sum over the existing state, with state retained on errors. -/
abbrev AssignedM (α β : Type) :=
  ExceptT AssignedError (StateM (MutableMemory α)) β

/-- Preserve every existing runtime error and all prior mutation effects. -/
def assignedLiftRuntime {α β : Type} (action : MutationM α β) : AssignedM α β := do
  let before ← get
  let (result, after) := action.run before
  set after
  match result with
  | .ok value => pure value
  | .error error => throwThe AssignedError (.inl error)

/-- Preserve abstractarray.jl's existing error type, without a default result. -/
def assignedLiftArray {α β : Type}
    (action : JuliaLean.base.abstractarray.Result β) : AssignedM α β :=
  match action with
  | .ok value => pure value
  | .error error => throwThe AssignedError (.inr error)

/-- Native size-field projection needed at base/array.jl:235. -/
-- Source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- /Source
def assignedSize (a : CopyArrayHeader) : List I :=
  JuliaLean.base.essentials.sizeArray
    (fun header : CopyArrayHeader => fun _ => header.dimensions) a

/-- Native Array axes use the installed unchecked OneTo constructor, including
zero-length dimensions. Julia source: base/abstractarray.jl:100-103. -/
-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source
def assignedAxes (a : CopyArrayHeader) :
    JuliaLean.base.abstractarray.Result (List (JuliaLean.base.range.OneTo I)) :=
  JuliaLean.base.abstractarray.axesDefault
    (fun header : CopyArrayHeader => .ok (assignedSize header))
    JuliaLean.base.range.unchecked_oneto a

/-- The installed native OneTo bounds and length methods, composed with the
actual checkbounds_indices recursion. A missing axis is OneTo(1); after indices
are exhausted, every remaining axis must have length one. Source:
base/abstractarray.jl:722-728,753; base/range.jl:817. -/
-- Source: base/abstractarray.jl:722-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
def assignedAxesCheck : List (JuliaLean.base.range.OneTo I) → List I →
    JuliaLean.base.abstractarray.Result Bool
  | axes, [] => JuliaLean.base.abstractarray.checkboundsIndicesNil
      (fun axis => .ok (JuliaLean.base.range.length_OneTo_bigints axis)) axes
  | axes, index :: rest => JuliaLean.base.abstractarray.checkboundsIndicesCons
      (JuliaLean.base.range.unchecked_oneto one)
      (fun axis index => .ok (JuliaLean.base.abstractarray.checkindexOneTo axis.stop index))
      (fun remaining _ => assignedAxesCheck remaining rest) axes index rest

/-- Native dispatch of checkbounds(Bool, a, indices...). Exactly one Int
selects the essentials.jl Array/Memory specialization; other arities use the
installed abstractarray.jl axes recursion. Source:
base/essentials.jl:385-388; base/abstractarray.jl:682-685. -/
-- Source: base/essentials.jl:385-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::Union{Array, Memory}, i::Int)
--     @inline
--     ult_int(bitcast(UInt, sub_int(i, 1)), bitcast(UInt, length(A)))
-- end
-- /Source
-- Source: base/abstractarray.jl:682-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, I...)
--     @inline
--     checkbounds_indices(Bool, axes(A), I)
-- end
-- /Source
def assignedBounds (a : CopyArrayHeader) (indices : List I) :
    JuliaLean.base.abstractarray.Result Bool :=
  match indices with
  | [index] => .ok (JuliaLean.base.essentials.checkboundsBool (copyArrayLength a) index)
  | _ => JuliaLean.base.abstractarray.checkboundsMany assignedAxes assignedAxesCheck a indices

/-- Concrete native-Int binding of _sub2ind_recurse, nextL and offsetin.
All intermediate arithmetic is the installed wrapping Int arithmetic. Tuple
reads call the existing checked tuple primitive, so any error is retained.
Source: base/abstractarray.jl:3193-3207. -/
-- Source: base/abstractarray.jl:3193-3207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
-- 
-- nextL(L, l::Integer) = L*l
-- nextL(L, r::AbstractUnitRange) = L*length(r)
-- nextL(L, r::Slice) = L*length(r.indices)
-- offsetin(i, l::Integer) = i-1
-- /Source
def assignedSub2indRec : List I → I → I → List I →
    JuliaLean.base.abstractarray.Result I
  | dims, stride, index, [] =>
      .ok (JuliaLean.base.abstractarray.sub2indRecurseDone dims stride index)
  | [], stride, index, coordinate :: rest =>
      JuliaLean.base.abstractarray.sub2indRecurseEmpty
        (fun a b : I => .ok (JuliaLean.base.int.sub a b))
        (fun a b : I => .ok (JuliaLean.base.int.mul a b))
        (fun a b : I => .ok (JuliaLean.base.int.add a b))
        (fun _ nextStride nextIndex _ =>
          assignedSub2indRec [] nextStride nextIndex rest)
        stride index coordinate rest
  | dimension :: remaining, stride, index, coordinate :: rest =>
      JuliaLean.base.abstractarray.sub2indRecurse
        (fun dims : List I => JuliaLean.base.abstractarray.tupleGet dims one)
        (fun dims : List I => .ok dims.tail)
        (JuliaLean.base.abstractarray.nextLInteger
          (fun a b : I => .ok (JuliaLean.base.int.mul a b)))
        (JuliaLean.base.abstractarray.offsetinInteger
          (fun a b : I => .ok (JuliaLean.base.int.sub a b)))
        (fun a b : I => .ok (JuliaLean.base.int.mul a b))
        (fun a b : I => .ok (JuliaLean.base.int.add a b))
        (fun dims nextStride nextIndex _ =>
          assignedSub2indRec dims nextStride nextIndex rest)
        (dimension :: remaining) stride index coordinate rest

/-- Exact empty/nonempty Dims dispatch of _sub2ind(size(a), indices...).
The empty coordinate tuple returns the first linear location; all other cases
use the installed source router and native recursion. Source:
base/abstractarray.jl:3178-3184. -/
-- Source: base/abstractarray.jl:3178-3184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind(::Tuple{}) = 1
-- _sub2ind(::DimsInteger) = 1
-- _sub2ind(::Indices) = 1
-- _sub2ind(::Tuple{}, I::Integer...) = (@inline; _sub2ind_recurse((), 1, 1, I...))
-- 
-- # Generic cases
-- _sub2ind(dims::DimsInteger, I::Integer...) = (@inline; _sub2ind_recurse(dims, 1, 1, I...))
-- /Source
def assignedSub2ind (dims indices : List I) :
    JuliaLean.base.abstractarray.Result I :=
  match dims, indices with
  | [], [] => .ok JuliaLean.base.abstractarray.sub2indEmpty
  | _, [] => .ok (JuliaLean.base.abstractarray.sub2indDimsNoIndices dims)
  | [], _ => JuliaLean.base.abstractarray.sub2indEmptyIndices
      (fun _ stride index coordinates => assignedSub2indRec [] stride index coordinates)
      indices
  | _, _ => JuliaLean.base.abstractarray.sub2indDims assignedSub2indRec dims indices

/-- Non-atomic native assignment test at the existing cell projection. Boxed
and inline-pointer slots carry their null/non-null condition in Option; native
pointer-free storage returns true without examining any value. The source is
copied from the bundled src/genericmemory_c.lean pinned-source block, whose
original C range is 382-400. Needed by base/array.jl:236. -/
-- Source: src/genericmemory.c:382-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static int _jl_memoryref_isassigned(jl_genericmemoryref_t m, int isatomic)
-- {
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     _Atomic(jl_value_t*) *elem = (_Atomic(jl_value_t*)*)m.ptr_or_offset;
--     if (layout->flags.arrayelem_isboxed) {
--     }
--     else if (layout->first_ptr >= 0) {
--         elem = &elem[layout->first_ptr];
--     }
--     else {
--         return 1;
--     }
--     return (isatomic ? jl_atomic_load(elem) : jl_atomic_load_relaxed(elem)) != NULL;
-- }
-- 
-- jl_value_t *jl_memoryref_isassigned(jl_genericmemoryref_t m, int isatomic)
-- {
--     return _jl_memoryref_isassigned(m, isatomic) ? jl_true : jl_false;
-- }
-- /Source
def assignedNativeCell {α : Type} (layout : JuliaLean.src.genericmemory_c.DictLayout)
    (slot : Option α) : Bool :=
  if JuliaLean.src.genericmemory_c.isBoxed layout.metadata then
    slot.isSome
  else if 0 ≤ layout.metadata.memoryLayout.firstptr.val then
    slot.isSome
  else
    true

/-- Reuse the installed memory interface with the concrete native query above.
Only that query is selected by isassignedRef; no atomic store or user code is
invoked. This preserves the existing explicit runtime boundary at
base/genericmemory.jl:195 and src/genericmemory.c:382-400. -/
def assignedAccessOps {α : Type} (layout : JuliaLean.src.genericmemory_c.DictLayout) :
    JuliaLean.base.genericmemory.MemoryAccessOps (StateM (Nat → Option α))
      Unit Nat (Option α) (Option α) :=
  { JuliaLean.src.genericmemory_c.runtimeAccessOps (α := α) layout with
    memoryrefIsAssigned := fun reference _ _ => fun slots =>
      (assignedNativeCell layout (slots reference.ptr_or_offset), slots) }

/-- The source GenericMemoryRef wrapper, evaluated on the selected physical
cell. The memoryRead/index guards are the existing unsafe-access obligations;
valid Array headers and the preceding bounds check ensure they are satisfied.
No undefined-reference value read is performed. Source: base/genericmemory.jl:195,
used at base/array.jl:236. -/
-- Source: base/genericmemory.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isassigned(a::GenericMemoryRef) = memoryref_isassigned(a, default_access_order(a), @_boundscheck)
-- /Source
def assignedAtReference {α : Type} (layout : JuliaLean.src.genericmemory_c.DictLayout)
    (reference : Nat × I) : MutationM α Bool := do
  let cells ← memoryRead reference.1
  if reference.2.val < 1 then throw .bounds
  match cells[(reference.2.val - 1).toNat]? with
  | none => throw .bounds
  | some slot =>
    let nativeRef : JuliaLean.base.genericmemory.GenericMemoryRef Unit Nat :=
      ⟨(), reference.2.val.toNat⟩
    let result := Id.run ((JuliaLean.base.genericmemory.isassignedRef
      (assignedAccessOps (α := α) layout) false nativeRef).run (fun _ => slot))
    pure result.1

/-- Concrete isassigned(Array, Int...) for every native rank and index-tuple
arity. It preserves source bounds-before-linearization order, calculates the
physical shared-memory reference with native wrapping arithmetic, and invokes
the actual GenericMemoryRef wrapper over the concrete non-atomic native query.
Array dimensions/offsets and index tuples retain their native representation.
Source: base/array.jl:231-237. -/
-- Source: base/array.jl:231-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isassigned(a::Array, i::Int...)
--     @inline
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(Bool, a, i...) || return false
--     ii = _sub2ind(size(a), i...)
--     return @inbounds isassigned(memoryrefnew(a.ref, ii, false))
-- end
-- /Source
def assignedArray {α : Type} (layout : JuliaLean.src.genericmemory_c.DictLayout)
    (a : CopyArrayHeader) (indices : TupleArgs I) : AssignedM α Bool :=
  JuliaLean.base.array.isassignedArray (m := AssignedM α)
    (fun header coordinates => assignedLiftArray (assignedBounds header coordinates))
    (fun header => pure (assignedSize header))
    (fun dims coordinates => assignedLiftArray (assignedSub2ind dims coordinates))
    (fun header index _ => assignedLiftRuntime
      (copyOperandReference (α := α) (.array header) index))
    (fun reference => assignedLiftRuntime (assignedAtReference layout reference))
    a indices.values

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- The existing byte heap plus arbitrary native state. No cell partition or
non-aliasing restriction is imposed. -/
structure NativeCopyWorld (State : Type) where
  bytes : JuliaLean.base.pointer.ByteHeap
  other : State

/-- A native Memory header, using the installed pointer model's metadata view.
The capacity is a Julia Int. T is the common method element type. -/
structure NativeCopyMemory (T : Type) extends JuliaLean.base.pointer.PointerMemoryObject T where
  identity : Nat
  capacity : I

abbrev NativeCopyRef (T : Type) :=
  JuliaLean.base.genericmemory.GenericMemoryRef (NativeCopyMemory T) (JInt .u64)

/-- Read-only Array header; dimensions retain the native Int type and the
reference retains its physical pointer-or-offset representation. -/
structure NativeCopyArray (T : Type) where
  identity : Nat
  ref : NativeCopyRef T
  dimensions : List I

inductive NativeCopyOperand (T : Type) where
  | array (header : NativeCopyArray T)
  | memory (header : NativeCopyMemory T)

/-- Preserve array, abstract-array and native error families separately. The
underlying installed IO/runtime monad retains partial state and divergence. -/
abbrev NativeCopyM (World A : Type) :=
  ExceptT Error (ExceptT JuliaLean.base.abstractarray.ArrayError (LayoutM World)) A

/-- Inject a native computation without altering its error, state or divergence. -/
def nativeCopyLift {World A : Type} (action : LayoutM World A) : NativeCopyM World A :=
  ExceptT.lift (ExceptT.lift action)

/-- Preserve the installed abstract-array error family. -/
def nativeCopyLiftArray {World A : Type}
    (action : JuliaLean.base.abstractarray.Result A) : NativeCopyM World A :=
  ExceptT.lift (ExceptT.mk (pure action))

/-- Existing MemoryCopyOps native boundary. Only ccallCopy and the two GC
preservation fields are inherited by nativeCopyOps; every reached Base field
is replaced below. The other fields are unreachable in unsafeCopytoRefs false. -/
abbrev NativeCopyOps (State T : Type) :=
  JuliaLean.base.genericmemory.MemoryCopyOps
    (NativeCopyM (NativeCopyWorld State)) (NativeCopyMemory T) (JInt .u64)
    I I I I (JuliaLean.base.pointer.Ptr Unit) Nat

/-- The existing CMemoryOps.memmoveC ABI boundary, copied as a field type only:
byte heap, Cvoid pointers, Csize_t, then resulting heap and returned pointer.
No C law is added or assumed; this is not a Base copy callback. -/
abbrev NativeMemmove := JuliaLean.base.pointer.ByteHeap →
  JuliaLean.base.pointer.Ptr Unit → JuliaLean.base.pointer.Ptr Unit → JInt .u64 →
  JuliaLean.base.pointer.ByteHeap × JuliaLean.base.pointer.Ptr Unit

/-- Source base/essentials.jl:12-14,1296. Array length reuses the group-13
source composition. Memory length is the product of its singleton size tuple;
the local tuple projection is the native getfield(:length) boundary. -/
-- Source: base/essentials.jl:12-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- size(a::GenericMemory) = (getfield(a, :length),)
-- /Source
-- Source: base/essentials.jl:1296-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(a::Array{T,1}) where {T} = getfield(getfield(a, :size), 1)
-- /Source
def nativeCopyLength : NativeCopyOperand T → I
  | .array a => lengthHeader (V := Unit) ⟨(), a.dimensions⟩
  | .memory m => JuliaLean.base.essentials.lengthAbstract
      (fun memory : NativeCopyMemory T => [memory.capacity])
      JuliaLean.base.essentials.prodDims m

/-- Source base/abstractarray.jl:394,452; range.jl:868. Reuse both installed
firstindex/eachindex methods and first_OneTo, including empty operands. -/
-- Source: base/abstractarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::Union{Array, Memory}) = unchecked_oneto(length(A))
-- /Source
-- Source: base/abstractarray.jl:452-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- firstindex(a::AbstractArray) = (@inline; first(eachindex(IndexLinear(), a)))
-- /Source
def nativeCopyFirst (operand : NativeCopyOperand T) :
    JuliaLean.base.abstractarray.Result I :=
  JuliaLean.base.abstractarray.firstindexArray
    (JuliaLean.base.abstractarray.eachindexDense
      (fun a => .ok (nativeCopyLength a)) JuliaLean.base.range.unchecked_oneto)
    (fun axis => .ok (JuliaLean.base.range.first_OneTo axis)) operand

/-- Pointer-or-offset representation of the first Memory element, at the
existing native header boundary. It is the same representation used by the
bundled round6e.memoryref and pointer.unsafeConvertMemoryRefCvoid. Source:
base/boot.jl:768 and the address selection in src/genericmemory.c:262.
This does not model boxing/GC allocation of a Core reference object. -/
-- Source: base/boot.jl:768-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- memoryref(mem::GenericMemory) = memoryrefnew(mem)
-- /Source
-- Source: src/genericmemory.c:256-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_value_t *jl_genericmemoryref(jl_genericmemory_t *mem, size_t i)
-- {
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(mem))->layout;
--     int isatomic = layout->flags.arrayelem_isatomic || layout->flags.arrayelem_islocked;
--     jl_genericmemoryref_t m;
--     m.mem = mem;
--     m.ptr_or_offset = (layout->flags.arrayelem_isunion || layout->size == 0) ? (void*)i : (void*)((char*)mem->ptr + layout->size * i);
--     return jl_memoryrefget(m, isatomic);
-- /Source
def nativeCopyMemoryref (memory : NativeCopyMemory T) : NativeCopyRef T :=
  ⟨memory, if memory.arrayElement = 2 ∨ memory.layoutBytes.val = 0 then
    JInt.wrap .u64 0 else memory.ptr.address⟩

/-- Source src/genericmemory.c:311-323, reached through
base/boot.jl:769-770. Native address increment after Int(i)-1, with UInt
pointer wrapping. The C assertions are access obligations, not Julia errors;
valid headers and the preceding Base bounds checks establish them. -/
-- Source: base/boot.jl:769-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- memoryref(mem::GenericMemory, i::Integer) = memoryrefnew(mem, Int(i), @_boundscheck)
-- memoryref(ref::GenericMemoryRef, i::Integer) = memoryrefnew(ref, Int(i), @_boundscheck)
-- /Source
-- Source: src/genericmemory.c:311-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_genericmemoryref_t jl_memoryrefindex(jl_genericmemoryref_t m JL_PROPAGATES_ROOT, size_t idx)
-- {
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     if ((layout->flags.arrayelem_isboxed || !layout->flags.arrayelem_isunion) && layout->size != 0) {
--         m.ptr_or_offset = (void*)((char*)m.ptr_or_offset + idx * layout->size);
--         assert((char*)m.ptr_or_offset - (char*)m.mem->ptr < layout->size * m.mem->length);
--     }
--     else {
--         m.ptr_or_offset = (void*)((size_t)m.ptr_or_offset + idx);
--         assert((size_t)m.ptr_or_offset < m.mem->length);
--     }
--     return m;
-- }
-- /Source
def nativeCopyShift (reference : NativeCopyRef T) (index : I) : NativeCopyRef T :=
  let offset := JuliaLean.base.pointer.int64ToUInt64 (index - one)
  let delta := if reference.mem.arrayElement ≠ 2 ∧ reference.mem.layoutBytes.val ≠ 0 then
      offset * JuliaLean.base.pointer.int64ToUInt64 reference.mem.layoutBytes
    else offset
  ⟨reference.mem, reference.ptr_or_offset + delta⟩

/-- Source base/array.jl:310-312. Select the Array ref or Memory header, then
invoke the concrete unchecked native reference increment. -/
-- Source: base/array.jl:310-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @inbounds let dest = memoryref(dest isa Array ? getfield(dest, :ref) : dest, doffs),
--                   src = memoryref(src isa Array ? getfield(src, :ref) : src, soffs)
--         unsafe_copyto!(dest, src, n)
-- /Source
def nativeCopyReference (operand : NativeCopyOperand T) (index : I) : NativeCopyRef T :=
  nativeCopyShift (match operand with
    | .array a => a.ref
    | .memory m => nativeCopyMemoryref m) index

/-- Source base/pointer.jl:75-87. Reuse the installed pointer conversion,
including union and zero-size layouts. It observes physical byte addresses. -/
-- Source: base/pointer.jl:75-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_convert(::Type{Ptr{Cvoid}}, a::GenericMemoryRef{<:Any,T,Core.CPU}) where {T}
--     mem = getfield(a, :mem)
--     offset = getfield(a, :ptr_or_offset)
--     MemT = typeof(mem)
--     arrayelem = datatype_arrayelem(MemT)
--     elsz = datatype_layoutsize(MemT)
--     isunion = 2
--     if arrayelem == isunion || elsz == 0
--         offset = UInt(offset) * elsz
--         offset += unsafe_convert(Ptr{Cvoid}, mem)
--     end
--     return offset
-- end
-- /Source
def nativeCopyPointer (reference : NativeCopyRef T) : JuliaLean.base.pointer.Ptr Unit :=
  JuliaLean.base.pointer.unsafeConvertMemoryRefCvoid
    ⟨reference.mem.toPointerMemoryObject, reference.ptr_or_offset⟩

/-- Native-Int specialization of base/cmem.jl:26-29.
Bind the existing CMemoryOps.memmoveC ABI shape, perform the
checked Csize_t conversion and preserve the returned byte heap. The C library
itself remains the native boundary; no law about its effects is assumed. -/
-- Source: base/cmem.jl:26-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function memmove(dst::Ptr, src::Ptr, n::Integer)
--     @_terminates_globally_meta
--     ccall(:memmove, Ptr{Cvoid}, (Ptr{Cvoid}, Ptr{Cvoid}, Csize_t), dst, src, n)
-- end
-- /Source
def nativeCopyMemmove (ccall : NativeMemmove)
    (dest src : JuliaLean.base.pointer.Ptr Unit) (count : I) :
    NativeCopyM (NativeCopyWorld State) (JuliaLean.base.pointer.Ptr Unit) := do
  let size ← nativeCopyLift (JuliaLean.base.io.liftJl
    (JuliaLean.base.int.convert .u64 count))
  let before ← nativeCopyLift JuliaLean.base.io.getWorld
  let result := ccall before.bytes
    (JuliaLean.base.pointer.convertPtrType dest)
    (JuliaLean.base.pointer.convertPtrType src) size
  nativeCopyLift (JuliaLean.base.io.setWorld { before with bytes := result.1 })
  pure result.2

/-- Close every reached Base callee of genericmemory.jl:198-214. The retained
fields ccallCopy and gcPreserveBegin/End are the existing explicit C/Core
boundaries. isbitstype, pointer conversion, aligned_sizeof, native multiplication
and Int conversion are actual installed/composed implementations. -/
-- Source: base/genericmemory.jl:198-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_copyto!(dest::MemoryRef{T}, src::MemoryRef{T}, n) where {T}
--     @_terminates_globally_notaskstate_meta
--     n == 0 && return dest
--     @boundscheck memoryref(dest, n), memoryref(src, n)
--     if isbitstype(T)
--         tdest = @_gc_preserve_begin dest
--         tsrc = @_gc_preserve_begin src
--         pdest = unsafe_convert(Ptr{Cvoid}, dest)
--         psrc = unsafe_convert(Ptr{Cvoid}, src)
--         memmove(pdest, psrc, aligned_sizeof(T) * n)
--         @_gc_preserve_end tdest
--         @_gc_preserve_end tsrc
--     else
--         ccall(:jl_genericmemory_copyto, Cvoid, (Any, Ptr{Cvoid}, Any, Ptr{Cvoid}, Int), dest.mem, dest.ptr_or_offset, src.mem, src.ptr_or_offset, Int(n))
--     end
--     return dest
-- end
-- /Source
def nativeCopyOps
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove) :
    NativeCopyOps State T :=
  { native with
    isZero := fun n => JuliaLean.base.int.eq n zero
    toInt := fun n => nativeCopyLift (JuliaLean.base.io.liftJl
      (JuliaLean.base.int.convert .i64 n))
    byteCount := fun _ n => do
      let stride ← nativeCopyLift (elsizeArrayRuntime layout elementType)
      pure (JuliaLean.base.int.mul stride n)
    isBitsType := fun _ => JuliaLean.base.runtime_internals.isbitstype layout.types elementType
    unsafeConvert := fun reference => pure (nativeCopyPointer reference)
    memmove := fun dest src count => do
      let _ ← nativeCopyMemmove ccall dest src count
      pure () }

/-- Source base/essentials.jl:385-393. Concrete native-Int Array/Memory bounds,
retaining the existing array BoundsError family. -/
-- Source: base/essentials.jl:385-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::Union{Array, Memory}, i::Int)
--     @inline
--     ult_int(bitcast(UInt, sub_int(i, 1)), bitcast(UInt, length(A)))
-- end
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
def nativeCopyBounds (operand : NativeCopyOperand T) (index : I) : NativeCopyM World Unit := do
  if !(JuliaLean.base.essentials.checkboundsBool (nativeCopyLength operand) index) then
    throwThe Error .bounds

/-- Source base/array.jl:299-315. This is only the same-T native-Int
specialization required by the three whole-copy methods. General Integer and
mixed-element _copyto_impl! signatures are not claimed. Actual Base checks run
before physical references and unsafeCopytoRefs, in the original order. -/
-- Source: base/array.jl:299-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _copyto_impl!(dest::Union{Array,Memory}, doffs::Integer, src::Union{Array,Memory}, soffs::Integer, n::Integer)
--     @inline
--     n == 0 && return dest
--     n > 0 || _throw_argerror("Number of elements to copy must be non-negative.")
--     @boundscheck checkbounds(dest, doffs)
--     @boundscheck n <= length(dest) - doffs + 1 || throw(BoundsError(dest, length(dest) + 1))
--     @boundscheck checkbounds(src, soffs)
--     @boundscheck n <= length(src) - soffs + 1 || throw(BoundsError(src, length(src) + 1))
--     doffs = Int(doffs)
--     soffs = Int(soffs)
--     n = Int(n)
--     @inbounds let dest = memoryref(dest isa Array ? getfield(dest, :ref) : dest, doffs),
--                   src = memoryref(src isa Array ? getfield(src, :ref) : src, soffs)
--         unsafe_copyto!(dest, src, n)
--     end
--     return dest
-- end
-- /Source
def nativeCopyImpl
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (dest : NativeCopyOperand T) (doffs : I) (src : NativeCopyOperand T) (soffs n : I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyOperand T) :=
  JuliaLean.base.array.copytoImpl
    (fun n => pure (JuliaLean.base.int.eq n zero))
    (fun n => pure (JuliaLean.base.int.lt zero n))
    (fun a => pure (nativeCopyLength a)) (fun a => pure (nativeCopyLength a))
    nativeCopyBounds nativeCopyBounds
    (fun a b => pure (JuliaLean.base.int.sub a b))
    (fun a b => pure (JuliaLean.base.int.sub a b))
    (fun a b => pure (JuliaLean.base.int.add a b))
    (fun a b => pure (JuliaLean.base.int.add a b))
    (fun a b => pure (JuliaLean.base.int.le a b))
    (fun a b => pure (JuliaLean.base.int.le a b))
    (fun _ _ => throwThe Error .bounds) (fun _ _ => throwThe Error .bounds)
    (fun n => nativeCopyLift (JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 n)))
    (fun n => nativeCopyLift (JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 n)))
    (fun n => nativeCopyLift (JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 n)))
    (fun a i => do
      let index ← nativeCopyLift (JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 i))
      pure (nativeCopyReference a index))
    (fun a i => do
      let index ← nativeCopyLift (JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 i))
      pure (nativeCopyReference a index))
    (fun d s n => do
      let _ ← JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
        (nativeCopyOps layout elementType native ccall) false d s n
      pure ()) dest doffs src soffs n

/-- Source base/array.jl:330. Whole same-T copy for every native rank,
composed through the installed offset-copy adapter and _copyto_impl!.
Only the explicit native Core/C boundaries described above remain supplied. -/
-- Source: base/array.jl:330-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copyto!(dest::Array{T}, src::Array{T}) where {T} = _copyto2arg!(dest, src)
-- /Source
def nativeCopyArrayArray
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (dest : NativeCopyArray T) (src : NativeCopyArray T) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  JuliaLean.base.array.copyto330
    (fun d => nativeCopyLiftArray (nativeCopyFirst (.array d)))
    (fun s => nativeCopyLiftArray (nativeCopyFirst (.array s)))
    (fun s => pure (nativeCopyLength (.array s)))
    (fun d doffs s soffs n => do
      let _ ← JuliaLean.base.array.copyto296
        (nativeCopyImpl layout elementType native ccall)
        (.array d) doffs (.array s) soffs n
      pure d) dest src

/-- Source base/array.jl:331. Whole same-T copy for every native rank,
composed through the installed offset-copy adapter and _copyto_impl!.
Only the explicit native Core/C boundaries described above remain supplied. -/
-- Source: base/array.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copyto!(dest::Array{T}, src::Memory{T}) where {T} = _copyto2arg!(dest, src)
-- /Source
def nativeCopyArrayMemory
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (dest : NativeCopyArray T) (src : NativeCopyMemory T) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  JuliaLean.base.array.copyto331
    (fun d => nativeCopyLiftArray (nativeCopyFirst (.array d)))
    (fun s => nativeCopyLiftArray (nativeCopyFirst (.memory s)))
    (fun s => pure (nativeCopyLength (.memory s)))
    (fun d doffs s soffs n => do
      let _ ← JuliaLean.base.array.copyto290
        (nativeCopyImpl layout elementType native ccall)
        (.array d) doffs (.memory s) soffs n
      pure d) dest src

/-- Source base/array.jl:332. Whole same-T copy for every native rank,
composed through the installed offset-copy adapter and _copyto_impl!.
Only the explicit native Core/C boundaries described above remain supplied. -/
-- Source: base/array.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copyto!(dest::Memory{T}, src::Array{T}) where {T} = _copyto2arg!(dest, src)
-- /Source
def nativeCopyMemoryArray
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (dest : NativeCopyMemory T) (src : NativeCopyArray T) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyMemory T) :=
  JuliaLean.base.array.copyto332
    (fun d => nativeCopyLiftArray (nativeCopyFirst (.memory d)))
    (fun s => nativeCopyLiftArray (nativeCopyFirst (.array s)))
    (fun s => pure (nativeCopyLength (.array s)))
    (fun d doffs s soffs n => do
      let _ ← JuliaLean.base.array.copyto292
        (nativeCopyImpl layout elementType native ccall)
        (.memory d) doffs (.array s) soffs n
      pure d) dest src

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- Existing native allocation interfaces for the selected Julia element type T.
The layout is the installed Memory allocation summary. empty/allocate are the
existing newGenericMemory/allocGenericMemory primitive operands; headerIdentity
is the Core Expr(:new,...) allocation operand already exposed by arrayUndef.
It returns only the native identity: the actual reference, element type index T
and dimensions of the result are constructed by nativeArrayHeader. No ordinary
Array constructor or content-initialization callback is supplied. Raw payloads,
freshness, GC/OOM and native header allocation remain at these exact interfaces.
Sources: src/genericmemory.c:55-102; base/boot.jl:821-838. -/
structure NativeAllocationBoundary (State T : Type) where
  layout : Option MemoryLayout
  empty : LayoutM (NativeCopyWorld State) (NativeCopyMemory T)
  allocate : Nat → LayoutM (NativeCopyWorld State) (NativeCopyMemory T)
  headerIdentity : NativeCopyRef T → List I → LayoutM (NativeCopyWorld State) Nat

/-- Concrete Array header fields around the existing Core header-allocation
identity. This does not assume that the supplied native identity is fresh;
that is a property of the existing Core allocation boundary. Source:
base/boot.jl:821-824,831-833; required by base/array.jl:414-421 and391. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
def nativeArrayHeader (allocation : NativeAllocationBoundary State T)
    (reference : NativeCopyRef T) (dimensions : List I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) := do
  let identity ← nativeCopyLift (allocation.headerIdentity reference dimensions)
  pure ⟨identity, reference, dimensions⟩

/-- Bind the native memoryref(mem) address representation before constructing
an Array header. Native reference boxing/GC allocation remains outside the
installed pointer projection. Source: base/boot.jl:768,821-824. -/
-- Source: base/boot.jl:768-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- memoryref(mem::GenericMemory) = memoryrefnew(mem)
-- /Source
def nativeArrayFromMemory (allocation : NativeAllocationBoundary State T)
    (memory : NativeCopyMemory T) (dimensions : List I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  nativeArrayHeader allocation (nativeCopyMemoryref memory) dimensions

/-- Actual rank-dispatched Array{T,N}(undef,dims) with the native allocation and
Core header operands above. The body is the installed arrayUndef; all dimension,
count, type and byte-size checks therefore remain in their original order.
Source: base/boot.jl:835-838; required by base/array.jl:419-421. -/
-- Source: base/boot.jl:835-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{Array{T,1}})(::UndefInitializer, d::NTuple{1, Int}) where {T} = self(undef, getfield(d, 1))
-- (self::Type{Array{T,2}})(::UndefInitializer, d::NTuple{2, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2))
-- (self::Type{Array{T,3}})(::UndefInitializer, d::NTuple{3, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2), getfield(d, 3))
-- (self::Type{Array{T,N}})(::UndefInitializer, d::NTuple{N, Int}) where {T, N} = self(undef, d...)
-- /Source
def nativeArrayUndef (allocation : NativeAllocationBoundary State T)
    (dimensions : List I) : NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  arrayUndef allocation.layout
    (nativeCopyLift allocation.empty)
    (fun count => nativeCopyLift (allocation.allocate count))
    (nativeArrayFromMemory allocation) dimensions

/-- Bind the actual Vector constructor used by base/array.jl:414,416,418.
The negative/oversized dimension check stays in the Memory constructor rather
than an invented Array-dimension guard. Source: base/boot.jl:821-824. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
def nativeVectorUndef (allocation : NativeAllocationBoundary State T) (dimension : I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  arrayUndef1 allocation.layout
    (nativeCopyLift allocation.empty)
    (fun count => nativeCopyLift (allocation.allocate count))
    (nativeArrayFromMemory allocation) dimension

/-- Bind the actual Matrix constructor and its ordered checked_dims call,
used by base/array.jl:415,417. Source: base/boot.jl:825-827. -/
-- Source: base/boot.jl:825-827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
-- end))
-- /Source
def nativeMatrixUndef (allocation : NativeAllocationBoundary State T) (rows cols : I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  arrayUndef2 allocation.layout
    (nativeCopyLift allocation.empty)
    (fun count => nativeCopyLift (allocation.allocate count))
    (nativeArrayFromMemory allocation) rows cols

/-- Rank is part of the selected Julia Vector/Matrix source dispatch, not a
success condition about similar. The full native dimension tuple is retained. -/
abbrev NativeRankArray (T : Type) (rank : Nat) :=
  { array : NativeCopyArray T // array.dimensions.length = rank }

/-- Actual size(a,dim) body with native Int conversion, size-field projection,
and the installed tuple index/error behavior. Sources:
base/abstractarray.jl:42-46; base/essentials.jl:12. -/
-- Source: base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function size(t::AbstractArray, dim)
--     d = Int(dim)::Int
--     s = size(t)
--     d <= length(s) ? s[d] : 1
-- end
-- /Source
def nativeSimilarSize (array : NativeCopyArray T) (dimension : I) :
    NativeCopyM (NativeCopyWorld State) I :=
  nativeCopyLiftArray (JuliaLean.base.abstractarray.sizeDim
    (fun index : I => (JuliaLean.base.int.convert .i64 index).mapError
      JuliaLean.base.abstractarray.ArrayError.julia)
    (fun header : NativeCopyArray T =>
      .ok (sizeHeader (V := Unit) ⟨(), header.dimensions⟩)) array dimension)

/-- Snapshot of typeof(mem)'s already-constructed native Memory layout.
The fields are the existing PointerMemoryObject metadata, and boxed storage
retains the ordinary allocator's eight-byte override. This is a Core metadata
projection, not an unconstrained array_new_memory/constructor callback.
Source: array.jl:1114; src/genericmemory.c:94-102. -/
-- Source: base/array.jl:1114-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- array_new_memory(mem::Memory, newlen::Int) = typeof(mem)(undef, newlen) # when implemented, this should attempt to first expand mem
-- /Source
def nativeMemoryHeaderLayout (memory : NativeCopyMemory T) : MemoryLayout :=
  ⟨memory.layoutBytes.val.toNat, decide (memory.arrayElement = 1),
    decide (memory.arrayElement = 2)⟩

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- The Array type fixes its rank; the dimensions and reference remain mutable.
The tuple-length witness is a representation invariant, not an allocation law. -/
structure NativeLiveHeader (T : Type) (rank : Nat) where
  reference : NativeCopyRef T
  dimensions : List I
  rankValid : dimensions.length = rank

/-- Every rank has a typed mutable header map. An object identity is interpreted
at its fixed Array{T,rank} type. Other element types and native state remain in
other. Native callbacks can modify source references and dimensions in this
same world, while the type of each size tuple remains fixed. -/
structure NativeLiveState (State T : Type) where
  headers : (rank : Nat) → Nat → NativeLiveHeader T rank
  other : State

abbrev NativeLiveWorld (State T : Type) := NativeCopyWorld (NativeLiveState State T)
abbrev NativeLiveM (State T A : Type) := NativeCopyM (NativeLiveWorld State T) A
abbrev NativeLiveDimensions (rank : Nat) := { dimensions : List I // dimensions.length = rank }

/-- Read the current Core reference field once at base/array.jl:395. Later
native allocation/copy effects cannot change this already-captured reference. -/
-- Source: base/array.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ref = a.ref
-- /Source
def nativeLiveReadRef (rank handle : Nat) : NativeLiveM State T (NativeCopyRef T) := do
  let world ← nativeCopyLift JuliaLean.base.io.getWorld
  pure (world.other.headers rank handle).reference

/-- Source base/essentials.jl:13,1296, used separately at array.jl:396 and397.
Each call reads the current header before invoking the installed native length
composition. A previous native callback's dimension changes are observable. -/
-- Source: base/essentials.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
-- Source: base/essentials.jl:1296-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(a::Array{T,1}) where {T} = getfield(getfield(a, :size), 1)
-- /Source
def nativeLiveLength (rank handle : Nat) : NativeLiveM State T I := do
  let world ← nativeCopyLift JuliaLean.base.io.getWorld
  let header := world.other.headers rank handle
  pure (nativeCopyLength (.array ⟨handle, header.reference, header.dimensions⟩))

/-- Source base/essentials.jl:12, used after copying at array.jl:398. This
returns the live size tuple and its already-fixed Array rank, rather than a
cached pre-allocation shape. -/
-- Source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- /Source
def nativeLiveSize (rank handle : Nat) : NativeLiveM State T (NativeLiveDimensions rank) := do
  let world ← nativeCopyLift JuliaLean.base.io.getWorld
  let header := world.other.headers rank handle
  pure ⟨JuliaLean.base.essentials.sizeArray
    (fun h : NativeLiveHeader T rank => fun _ => h.dimensions) header, header.rankValid⟩

/-- Core Expr(:new,...) at base/array.jl:398. Observe the existing native
header-identity allocation, then record the actual constructor fields at that
identity in the current typed store. The store update preserves every other
header and every native effect of the raw identity action. No freshness law is
assumed. The dimension tuple was already read before this native action. -/
-- Source: base/array.jl:398-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     return $(Expr(:new, :(typeof(a)), :(memoryref(newmem)), :(a.size)))
-- /Source
def nativeLiveNewArray
    (allocation : NativeAllocationBoundary (NativeLiveState State T) T)
    (rank : Nat) (reference : NativeCopyRef T) (dimensions : NativeLiveDimensions rank) :
    NativeLiveM State T Nat := do
  let identity ← nativeCopyLift (allocation.headerIdentity reference dimensions.val)
  let world ← nativeCopyLift JuliaLean.base.io.getWorld
  let header : NativeLiveHeader T rank := ⟨reference, dimensions.val, dimensions.property⟩
  let headers : (otherRank : Nat) → Nat → NativeLiveHeader T otherRank :=
    fun otherRank key =>
      if sameRank : otherRank = rank then
        if key = identity then
          cast (congrArg (NativeLiveHeader T) sameRank.symm) header
        else world.other.headers otherRank key
      else world.other.headers otherRank key
  nativeCopyLift (JuliaLean.base.io.setWorld
    { world with other := { world.other with headers := headers } })
  pure identity

/-- Source base/array.jl:391-399. Close the installed copyArray body over live
all-rank headers, the checked Memory constructor, same-T unsafeCopytoRefs and
the existing Core allocation boundary. The initial reference is captured once;
length is read anew before and after allocation, and size is read after copying.
The source Memory's own metadata selects typeof(ref.mem). T and rank retain
Julia's type identity, while all mutable fields reside in the shared world.
Raw allocation and Core header freshness remain explicit native boundaries. -/
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
def nativeOrdinaryCopy
    (allocation : NativeAllocationBoundary (NativeLiveState State T) T)
    (layout : LayoutBoundary (NativeLiveWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeLiveState State T) T)
    (ccall : NativeMemmove) (rank source : Nat) : NativeLiveM State T Nat :=
  JuliaLean.base.abstractarray.ArrayCallees.copyArray
    (nativeLiveReadRef rank)
    (nativeLiveLength rank)
    (fun reference count => JuliaLean.base.array.memoryUndef
      (some (nativeMemoryHeaderLayout reference.mem))
      (nativeCopyLift allocation.empty)
      (fun size => nativeCopyLift (allocation.allocate size)) count)
    (fun memory => pure (nativeCopyMemoryref memory))
    (fun dest src count => do
      let _ ← JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
        (nativeCopyOps layout elementType native ccall) false dest src count
      pure ())
    (nativeLiveSize rank)
    (nativeLiveNewArray allocation rank) source

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- Concrete source base/array.jl:414. Preserve the selected source rank,
ordered size queries, target element type and actual Core Array constructor.
The result's uninitialized contents remain in the existing native boundary. -/
-- Source: base/array.jl:414-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::Vector{T}) where {T}                    = Vector{T}(undef, size(a,1))
-- /Source
def nativeSimilar414 (allocation : NativeAllocationBoundary State T)
    (array : NativeRankArray T 1) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  JuliaLean.base.array.similar414 nativeSimilarSize
    (nativeVectorUndef allocation) array.val

/-- Concrete source base/array.jl:415. Preserve the selected source rank,
ordered size queries, target element type and actual Core Array constructor.
The result's uninitialized contents remain in the existing native boundary. -/
-- Source: base/array.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::Matrix{T}) where {T}                    = Matrix{T}(undef, size(a,1), size(a,2))
-- /Source
def nativeSimilar415 (allocation : NativeAllocationBoundary State T)
    (array : NativeRankArray T 2) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  JuliaLean.base.array.similar415 nativeSimilarSize
    (nativeMatrixUndef allocation) array.val

/-- Concrete source base/array.jl:416. Preserve the selected source rank,
ordered size queries, target element type and actual Core Array constructor.
The result's uninitialized contents remain in the existing native boundary. -/
-- Source: base/array.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::Vector{T}, S::Type) where {T}           = Vector{S}(undef, size(a,1))
-- /Source
def nativeSimilar416 (allocation : NativeAllocationBoundary State S)
    (array : NativeRankArray T 1) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray S) :=
  JuliaLean.base.array.similar416 nativeSimilarSize
    (nativeVectorUndef allocation) array.val

/-- Concrete source base/array.jl:417. Preserve the selected source rank,
ordered size queries, target element type and actual Core Array constructor.
The result's uninitialized contents remain in the existing native boundary. -/
-- Source: base/array.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::Matrix{T}, S::Type) where {T}           = Matrix{S}(undef, size(a,1), size(a,2))
-- /Source
def nativeSimilar417 (allocation : NativeAllocationBoundary State S)
    (array : NativeRankArray T 2) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray S) :=
  JuliaLean.base.array.similar417 nativeSimilarSize
    (nativeMatrixUndef allocation) array.val

/-- Concrete source base/array.jl:418. The existing source Array is ignored;
the full native Int dimension reaches the actual Vector constructor. -/
-- Source: base/array.jl:418-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::Array{T}, m::Int) where {T}              = Vector{T}(undef, m)
-- /Source
def nativeSimilar418 (allocation : NativeAllocationBoundary State T)
    (array : NativeCopyArray T) (dimension : I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  JuliaLean.base.array.similar418 (nativeVectorUndef allocation) array dimension

/-- Concrete source base/array.jl:419. The target element type is the static S
index and its native allocation snapshot. Every representable native dimension
tuple, including negative or zero dimensions, is accepted for source checking. -/
-- Source: base/array.jl:419-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::Array, T::Type, dims::Dims{N}) where {N} = Array{T,N}(undef, dims)
-- /Source
def nativeSimilar419 (allocation : NativeAllocationBoundary State S)
    (array : NativeCopyArray T) (dimensions : TupleArgs I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray S) :=
  JuliaLean.base.array.similar419 (nativeArrayUndef allocation) array dimensions.values

/-- Concrete source base/array.jl:420. The native constructor receives the
requested size tuple and the source element type T, at every native rank. -/
-- Source: base/array.jl:420-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::Array{T}, dims::Dims{N}) where {T,N}     = Array{T,N}(undef, dims)
-- /Source
def nativeSimilar420 (allocation : NativeAllocationBoundary State T)
    (array : NativeCopyArray T) (dimensions : TupleArgs I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  JuliaLean.base.array.similar420 (nativeArrayUndef allocation) array dimensions.values

/-- Concrete source base/array.jl:421. The input Array type's rank is discarded
by the actual similarStorageDims callee; the output rank is dimensions.length.
The target Array{T} constructor is bound to nativeArrayUndef, not supplied as an
ordinary constructor callback. Source: base/abstractarray.jl:873. -/
-- Source: base/abstractarray.jl:873-873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(::Type{T}, dims::Dims) where {T<:AbstractArray} = T(undef, dims)
-- /Source
-- Source: base/array.jl:421-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(::Type{Array{T,N}}, dims::Dims) where {T,N} = similar(Array{T}, dims)
-- /Source
def nativeSimilar421 (allocation : NativeAllocationBoundary State T)
    (_sourceRank : I) (dimensions : TupleArgs I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) :=
  JuliaLean.base.array.similar421
    (fun dims : List I => JuliaLean.base.abstractarray.similarStorageDims
      (fun (_ : Type) dimensions => nativeArrayUndef allocation dimensions)
      (NativeCopyArray T) dims) dimensions.values

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- Concrete source base/array.jl:463-470. The abstract value type α is the
heterogeneous Julia value universe; values retain their identity and are stored
without convert or promotion. The fixed boxed layout is the existing native
Memory layout and the setter is the actual Vector{Any} safe-set specialization.
The zero-argument public call separately dispatches to base/array.jl:471. -/
-- Source: base/array.jl:463-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(::Type{Any}, @nospecialize vals...)
--     @_effect_free_terminates_locally_meta
--     a = Vector{Any}(undef, length(vals))
--     @_safeindex for i = 1:length(vals)
--         a[i] = vals[i]
--     end
--     return a
-- end
-- /Source
def anyValues {α : Type} (args : TupleArgs α) : MutationM α Nat :=
  anyLiteral
    (mutableAllocate
      (some (allocationSummary JuliaLean.src.genericmemory_c.boxedDictLayout)) 0)
    (safeSetindex1055
      (fun a i _ => mutableMemoryref a i)
      (fun reference value _ => memoryWrite reference.1 reference.2 (some value)))
    args.values

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- Static Julia typeof dispatch, with OtherType indexing every native concrete
type except UInt8 and Int8. This is a disjoint type representation, not a runtime
Boolean condition or a restriction to a chosen non-byte value type. -/
inductive NativeFillKind (OtherType : Type) where
  | uint8
  | int8
  | other (typeKey : OtherType)

/-- Actual scalar payload type selected by typeof(v). Host types retain arbitrary
native payloads and object identities in the non-byte cases. -/
def NativeFillValue {OtherType : Type} (Values : OtherType → Type) :
    NativeFillKind OtherType → Type
  | .uint8 => JInt .u8
  | .int8 => JInt .i8
  | .other key => Values key

/-- The existing CMemoryOps.memsetC field type. The Cint argument is signed;
negative Int8 values must not first be converted to UInt8. -/
abbrev NativeMemset := JuliaLean.base.pointer.ByteHeap →
  JuliaLean.base.pointer.Ptr Unit → JInt .i32 → JInt .u64 →
  JuliaLean.base.pointer.ByteHeap × JuliaLean.base.pointer.Ptr Unit

/-- Extract only the native operands actually reached by scalar fill. The
memoryrefNew/memoryrefSet types are exactly the existing MemoryAccessOps
fields; GC fields are those of MemoryCopyOps; memset is CMemoryOps.memsetC. No unused
ordinary Base conversion/indexing/pointer callback is supplied. Allocation and
native payload/GC semantics remain at their already-existing interfaces. -/
structure NativeFillBoundary (State T : Type) where
  allocation : NativeAllocationBoundary State T
  memoryrefNew : NativeCopyRef T → I → Bool →
    NativeCopyM (NativeCopyWorld State) (NativeCopyRef T)
  memoryrefSet : NativeCopyRef T → T →
    JuliaLean.base.genericmemory.MemoryOrder → Bool →
    NativeCopyM (NativeCopyWorld State) Unit
  gcPreserveBegin : NativeCopyRef T → Nat
  gcPreserveEnd : Nat → NativeCopyM (NativeCopyWorld State) Unit
  memset : NativeMemset

/-- Keep the installed range exception family distinct, including its native
JlError payload, while retaining all existing NativeCopyM errors/worlds. -/
abbrev NativeFillM (World A : Type) :=
  ExceptT JuliaLean.base.range.Exc (NativeCopyM World) A

/-- Error/state-preserving injection of an existing native computation. -/
def nativeFillLift {World A : Type} (action : NativeCopyM World A) : NativeFillM World A :=
  ExceptT.lift action

/-- The range result is injected without replacing any exception by a default. -/
def nativeFillRange {World A : Type} (action : JuliaLean.base.range.JlX A) :
    NativeFillM World A := ExceptT.mk (pure action)

/-- Lean iteration carrier for the actual OneTo{Int} returned by eachindex.
The wrapper introduces no additional Julia collection or precomputed index list. -/
structure NativeFillIndices where
  range : JuliaLean.base.range.OneTo I
/-- Source array.jl:373-378; doc/src/manual/interfaces.md:37-55. Lift the
existing fuel-free io.whileLoop through the exception transformers. Every
error exits with its exact post-error world; no continuation runs after an error
or divergence. This is the operational adapter for the Julia for-loop. -/
-- Source: base/array.jl:373-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _fill!(A::AbstractArray{T}, x::T) where T
--     for i in eachindex(A)
--         A[i] = x
--     end
--     return A
-- end
-- /Source
def nativeFillWhile {World S A : Type} (step : S → NativeFillM World (Sum A S))
    (initial : S) : NativeFillM World A :=
  ExceptT.mk (ExceptT.mk (ExceptT.mk
    (JuliaLean.base.io.whileLoop (fun state => do
      let result ← (step state).run.run.run
      match result with
      | .error error => pure (.inl (.error error))
      | .ok (.error error) => pure (.inl (.ok (.error error)))
      | .ok (.ok (.error error)) => pure (.inl (.ok (.ok (.error error))))
      | .ok (.ok (.ok (.inl value))) => pure (.inl (.ok (.ok (.ok value))))
      | .ok (.ok (.ok (.inr next))) => pure (.inr next)) initial)))

/-- Source range.jl:711,868,877,935. All OneTo{Int} iterate callees
are the installed range models, with native machine comparison/conversion.
The repeated first(r) calls of the source remain in iterate_OrdinalRange. -/
-- Source: base/range.jl:711-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(r::AbstractUnitRange) = first(r) > last(r)
-- /Source
-- Source: base/range.jl:868-868 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OneTo{T}) where {T} = oneunit(T)
-- /Source
-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
-- Source: base/range.jl:935-935 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(r::OrdinalRange) = isempty(r) ? nothing : (first(r), first(r))
-- /Source
def nativeFillIterate (axis : JuliaLean.base.range.OneTo I) :
    JuliaLean.base.range.JlX (Option (I × I)) :=
  letI : JuliaLean.base.range.JEltype (JuliaLean.base.range.OneTo I) I := ⟨⟩
  letI : JuliaLean.base.range.JFieldStop (JuliaLean.base.range.OneTo I) I := ⟨fun r => r.stop⟩
  letI : JuliaLean.base.range.JFirst (JuliaLean.base.range.OneTo I) I :=
    ⟨fun r => .ok (JuliaLean.base.range.first_OneTo r)⟩
  letI : JuliaLean.base.range.JLast (JuliaLean.base.range.OneTo I) I :=
    ⟨JuliaLean.base.range.last_OrdinalRange⟩
  letI : JuliaLean.base.range.JLt I I := ⟨JuliaLean.base.int.lt⟩
  letI : JuliaLean.base.range.JIsempty (JuliaLean.base.range.OneTo I) :=
    ⟨JuliaLean.base.range.isempty_AbstractUnitRange⟩
  JuliaLean.base.range.iterate_OrdinalRange axis

/-- Source range.jl:736,877,937-942. The next state uses actual
last, step, native Int addition and checked same-width conversion, with the
source equality test before addition. No Nat iteration counter is substituted. -/
-- Source: base/range.jl:736-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- step(r::AbstractUnitRange{T}) where {T} = oneunit(T) - zero(T)
-- /Source
-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
-- Source: base/range.jl:937-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(r::OrdinalRange{T}, i) where {T}
--     @inline
--     i == last(r) && return nothing
--     next = convert(T, i + step(r))
--     (next, next)
-- end
-- /Source
def nativeFillIterateState (axis : JuliaLean.base.range.OneTo I) (state : I) :
    JuliaLean.base.range.JlX (Option (I × I)) :=
  letI : JuliaLean.base.range.JEltype (JuliaLean.base.range.OneTo I) I := ⟨⟩
  letI : JuliaLean.base.range.JFieldStop (JuliaLean.base.range.OneTo I) I := ⟨fun r => r.stop⟩
  letI : JuliaLean.base.range.JLast (JuliaLean.base.range.OneTo I) I :=
    ⟨JuliaLean.base.range.last_OrdinalRange⟩
  letI : JuliaLean.base.range.JEq I I := ⟨JuliaLean.base.int.eq⟩
  letI : JuliaLean.base.range.JZero I := ⟨zero⟩
  letI : JuliaLean.base.range.JStep (JuliaLean.base.range.OneTo I) I :=
    ⟨fun r => .ok (JuliaLean.base.range.step_AbstractUnitRange r)⟩
  JuliaLean.base.range.iterate_OrdinalRange_state axis state

/-- Source array.jl:373-378; Julia loop lowering is documented at
doc/src/manual/interfaces.md:37-55. Invoke the actual first iterator, run the
body, then invoke the actual stateful iterator. The fuel-free loop preserves
the source order even if a native body errors, diverges or changes its world. -/
-- Source: base/array.jl:373-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _fill!(A::AbstractArray{T}, x::T) where T
--     for i in eachindex(A)
--         A[i] = x
--     end
--     return A
-- end
-- /Source
instance nativeFillForIn {World : Type} : ForIn (NativeFillM World) NativeFillIndices I where
  forIn {β} indices initial action :=
    nativeFillWhile (fun state : Option I × β => do
      let next ← nativeFillRange (match state.1 with
        | none => nativeFillIterate indices.range
        | some previous => nativeFillIterateState indices.range previous)
      match next with
      | none => pure (.inl state.2)
      | some (value, token) =>
          match ← action value state.2 with
          | .done result => pure (.inl result)
          | .yield result => pure (.inr (some token, result))) (none, initial)

/-- Source indices.jl:94,98; abstractarray.jl:384,394. The rank-zero
Array selected by source587 takes the AbstractArray eachindex method. Close
typeof/IndexStyle dispatch to actual Array and bind actual dense eachindex,
length and unchecked_oneto. The argument to dense eachindex is statically the
IndexLinear overload selected by this dispatch. -/
-- Source: base/indices.jl:94-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- IndexStyle(A::AbstractArray) = IndexStyle(typeof(A))
-- /Source
-- Source: base/indices.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- IndexStyle(::Type{<:Array}) = IndexLinear()
-- /Source
-- Source: base/abstractarray.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(A::AbstractArray) = (@inline(); eachindex(IndexStyle(A), A))
-- /Source
-- Source: base/abstractarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::Union{Array, Memory}) = unchecked_oneto(length(A))
-- /Source
def nativeFillEachindex (array : NativeCopyArray T) :
    NativeFillM (NativeCopyWorld State) NativeFillIndices := do
  let axis ← nativeFillLift (nativeCopyLiftArray
    (JuliaLean.base.abstractarray.eachindexArray
      (fun a => .ok (JuliaLean.base.indices.IndexStyle_AbstractArray
        (fun _ : NativeCopyArray T => JuliaLean.base.indices.ArrayType.array)
        JuliaLean.base.indices.IndexStyle_Type a))
      (fun _ a => JuliaLean.base.abstractarray.eachindexDense
        (fun a => .ok (nativeCopyLength (.array a)))
        JuliaLean.base.range.unchecked_oneto a) array))
  pure ⟨axis⟩

/-- Source boot.jl:382. The same-type Core conversion body is
used by generic fill and setindex, which select
the isa branch; this actual same-type method closes their unexecuted conversion
slots rather than supplying an unconstrained identity callback. -/
-- Source: base/boot.jl:382-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T) where {T} = x
-- /Source
def nativeFillConvertSame (value : T) : T := value

/-- Source essentials.jl:384-393. Actual Array/Int Bool bounds
dispatch is more specific than abstractarray.checkboundsOne. Reuse that
installed machine comparison; this local native-header version of the early
checkbounds wrapper maps the sole BoundsError to the existing array.Error
representation. It does not substitute a no-op for the source bounds check. -/
-- Source: base/essentials.jl:384-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # These checkbounds methods are defined early for bootstrapping
-- function checkbounds(::Type{Bool}, A::Union{Array, Memory}, i::Int)
--     @inline
--     ult_int(bitcast(UInt, sub_int(i, 1)), bitcast(UInt, length(A)))
-- end
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
def nativeFillBounds (array : NativeCopyArray T) (index : I) :
    NativeFillM (NativeCopyWorld State) Unit := do
  if JuliaLean.base.essentials.checkboundsBool (nativeCopyLength (.array array)) index then
    pure ()
  else
    throwThe Error .bounds

/-- Source array.jl:1039. Invoke the existing MemoryAccessOps.memoryrefNew
Core boundary with the source's false Bool operand. The native result, errors,
partial world and divergence are retained; no capacity test or pointer-shift
rule is substituted for the unavailable native implementation. This helper is
reached at the constructed rank-zero Array's initial reference. -/
-- Source: base/array.jl:1039-1039 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false)
-- /Source
def nativeFillOriginRef (native : NativeFillBoundary State T)
    (array : NativeCopyArray T) (index : I) :
    NativeFillM (NativeCopyWorld State) (NativeCopyRef T) :=
  nativeFillLift (native.memoryrefNew array.ref index false)

/-- Source array.jl:1031-1041. This is the scalar rank-zero setter
selected during source587, not the Vector safe-index specializations. The value
already has typeof(v), so isa is true. Reuse both existing setter bodies, with
actual Array bounds and the existing raw Core memoryrefnew/memoryrefset!
operands. Their false Bool operands and not_atomic store order are preserved. -/
-- Source: base/array.jl:1031-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setindex!(A::Array{T}, x, i::Int) where {T}
--     @_propagate_inbounds_meta
--     x = x isa T ? x : convert(T, x)::T
--     return _setindex!(A, x, i)
-- end
-- function _setindex!(A::Array{T}, x::T, i::Int) where {T}
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false)
--     return A
-- end
-- /Source
def nativeFillSet (native : NativeFillBoundary State T)
    (array : NativeCopyArray T) (value : T) (index : I) :
    NativeFillM (NativeCopyWorld State) (NativeCopyArray T) :=
  setindexScalar (fun _ => true) id
    (fun x => pure (nativeFillConvertSame x))
    (setindexTyped nativeFillBounds
      (fun a i _ => nativeFillOriginRef native a i)
      (fun reference x checked => nativeFillLift
        (native.memoryrefSet reference x .notAtomic checked))) array value index

/-- Source array.jl:368-378. Reuse both fill! and _fill! bodies,
with same-type dispatch, actual eachindex/OneTo iteration and the concrete
scalar setter. This path is selected for every typeof(v) except UInt8/Int8;
all native effects and exceptions are preserved without assuming a successful
store or an initialized allocation payload. -/
-- Source: base/array.jl:368-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(A::AbstractArray{T}, x) where T
--     @inline
--     xT = x isa T ? x : convert(T, x)::T
--     return _fill!(A, xT)
-- end
-- function _fill!(A::AbstractArray{T}, x::T) where T
--     for i in eachindex(A)
--         A[i] = x
--     end
--     return A
-- end
-- /Source
def nativeFillOrdinary (native : NativeFillBoundary State T)
    (array : NativeCopyArray T) (value : T) :
    NativeFillM (NativeCopyWorld State) (NativeCopyArray T) :=
  fillBang (fun _ => true) id (fun x => pure (nativeFillConvertSame x))
    (fillTyped nativeFillEachindex (fun a x i => do
      let _ ← nativeFillSet native a x i
      pure ())) array value

/-- Source cmem.jl:40-43. Close the local memset wrapper at the
existing CMemoryOps raw ABI field. Cint conversion precedes Csize_t conversion;
the raw C pointer return is retained by this wrapper and discarded only by the
fill! caller. Only the byte heap is replaced by the raw C result. -/
-- Source: base/cmem.jl:40-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function memset(p::Ptr, val, n::Integer)
--     @_terminates_globally_meta
--     ccall(:memset, Ptr{Cvoid}, (Ptr{Cvoid}, Cint, Csize_t), p, val, n)
-- end
-- /Source
def nativeFillMemset {t : IntTy} (ccall : NativeMemset)
    (pointer : JuliaLean.base.pointer.Ptr Unit) (value : JInt t) (count : JInt .u64) :
    NativeFillM (NativeCopyWorld State) (JuliaLean.base.pointer.Ptr Unit) := do
  let cValue ← nativeFillLift (nativeCopyLift (JuliaLean.base.io.liftJl
    (JuliaLean.base.int.convert .i32 value)))
  let size ← nativeFillLift (nativeCopyLift (JuliaLean.base.io.liftJl
    (JuliaLean.base.int.convert .u64 count)))
  let before ← nativeFillLift (nativeCopyLift JuliaLean.base.io.getWorld)
  let result := ccall before.bytes
    (JuliaLean.base.pointer.convertPtrType pointer) cValue size
  nativeFillLift (nativeCopyLift
    (JuliaLean.base.io.setWorld { before with bytes := result.1 }))
  pure result.2

/-- Source array.jl:473-480. The byte overload is selected only
for UInt8/Int8 in source587. Reuse fillBytes, actual pointer conversion, Array
length and the local C wrapper. Since the scalar and Array element types agree,
no convert branch executes. The existing GC begin is pure; its end action may
error, mutate state or diverge and is invoked only after memset returns. -/
-- Source: base/array.jl:473-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(a::Union{Array{UInt8}, Array{Int8}}, x::Integer)
--     ref = a.ref
--     t = @_gc_preserve_begin ref
--     p = unsafe_convert(Ptr{Cvoid}, ref)
--     memset(p, x isa eltype(a) ? x : convert(eltype(a), x), length(a) % UInt)
--     @_gc_preserve_end t
--     return a
-- end
-- /Source
def nativeFillByte {t : IntTy} (native : NativeFillBoundary State (JInt t))
    (array : NativeCopyArray (JInt t)) (value : JInt t) :
    NativeFillM (NativeCopyWorld State) (NativeCopyArray (JInt t)) :=
  fillBytes (fun a => pure a.ref)
    (fun reference => pure (native.gcPreserveBegin reference))
    (fun reference => pure (nativeCopyPointer reference))
    (fun _ => true) id
    (fun x => pure (JuliaLean.base.number.convertSame x))
    (fun a => pure (nativeCopyLength (.array a)))
    (fun pointer x count => do
      let _ ← nativeFillMemset native.memset pointer x count
      pure ())
    (fun token => nativeFillLift (native.gcPreserveEnd token)) array value

/-- Source array.jl:587. Complete scalar fill(v,()) composition
over its existing native interfaces. The empty dimension tuple is the full
selected public domain; it gives exactly one logical element, irrespective of
the scalar payload type. Native allocation/header failures are retained before
fill! dispatch, and the source returns the original constructed Array identity
after successful filling. Byte and non-byte branches use their actual methods. -/
-- Source: base/array.jl:587-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fill(v, dims::Tuple{}) = (a=Array{typeof(v),0}(undef, dims); fill!(a, v); a)
-- /Source
def nativeFillScalar {OtherType : Type} (Values : OtherType → Type)
    (kind : NativeFillKind OtherType) :
    NativeFillBoundary State (NativeFillValue Values kind) →
    NativeFillValue Values kind →
    NativeFillM (NativeCopyWorld State) (NativeCopyArray (NativeFillValue Values kind)) :=
  match kind with
  | .uint8 => fun native value =>
      fill587 (fun dimensions => nativeFillLift
        (nativeArrayUndef native.allocation dimensions))
        (nativeFillByte native) value ([] : List I)
  | .int8 => fun native value =>
      fill587 (fun dimensions => nativeFillLift
        (nativeArrayUndef native.allocation dimensions))
        (nativeFillByte native) value ([] : List I)
  | .other _ => fun native value =>
      fill587 (fun dimensions => nativeFillLift
        (nativeArrayUndef native.allocation dimensions))
        (nativeFillOrdinary native) value ([] : List I)

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- Source base/array.jl:711. The selected Julia element type is represented by
α and its existing native allocation metadata. Bind the actual arrayForUnknown
wrapper to the installed Core Array/Memory allocation model. The `0` supplied
to mutableAllocate is its unused source-array handle, not a new runtime input.
No uninitialized cell is read, so the empty result introduces no isbits payload
approximation. Physical OOM, GC, and shared empty-Memory identity remain outside
the existing mutableAllocate boundary, as elsewhere in the bundled model. -/
-- Source: base/array.jl:711-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _array_for_inner(::Type{T}, ::SizeUnknown, ::Nothing) where {T} = Vector{T}(undef, 0)
-- /Source
def arrayForUnknownRuntime {α : Type} (layout : Option MemoryLayout) : MutationM α Nat :=
  JuliaLean.base.array.arrayForUnknown
    (fun metadata n => mutableAllocate metadata 0 n) layout

/-- Preserve arbitrary iterator exceptions separately from the existing Array
and essentials exception representations. These sums add no new Julia exception
class and do not discard a native exception payload. -/
abbrev UpperBoundError (E : Type) :=
  Sum E (Sum JuliaLean.base.array.Error JuliaLean.base.essentials.Err)

abbrev UpperBoundExec (E World A : Type) :=
  JuliaLean.base.iterators.Exec (UpperBoundError E) World A

/-- Source loop in base/array.jl:807-815. The `run` signature is the existing
iterators.lean Exec iteration interface (as used by iterateTake/iterateDrop),
not a supplied correctness implementation for a missing Base callee.
The documented iterate protocol supplies Nothing or a value/state tuple;
see doc/src/manual/interfaces.md:8-54. It imposes no finite-rank restriction. Malformed custom iterate return
objects and their getfield errors remain outside this existing documented
value/state-pair interface; they are not silently assigned a default result.
The existing Exec boundary retains arbitrary iterator state, errors, effects,
and divergence. Tuple field 1 is read before the installed inferencebarrier;
field 2 and the next iterate call remain in the source false branch.
The dynamic Bool check is Julia's language rule documented at
manual/control-flow.md:180-191 and already used by essentials.equalSVec.
For inferencebarrier(nothing), the non-Bool branch throws TypeError, but the
unreachable source continuation is retained rather than supplied as a stub. -/
-- Source: base/array.jl:807-815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     while x !== nothing
--         val = getfield(x, 1)
--         if inferencebarrier(nothing)
--             return val
--         end
--         x = iterate(itr, getfield(x, 2))
--     end
--     throw(nothing)
-- end
-- /Source
def iteratorUpperBoundLoop {E World Iter State : Type}
    (run : Iter → Option State →
      JuliaLean.base.iterators.Exec E World (Option (JuliaLean.BootCov.JVal × State)))
    (itr : Iter) (x : Option (JuliaLean.BootCov.JVal × State)) :
    UpperBoundExec E World JuliaLean.BootCov.JVal := fun before =>
  match x with
  | none => some (.error (.inr (.inl .thrownNothing)), before)
  | some valueState =>
      let value := valueState.1
      match JuliaLean.base.essentials.inferencebarrier JuliaLean.BootCov.JVal.nothing with
      | .error error => some (.error (.inr (.inr error)), before)
      | .ok condition =>
          match condition with
          | .bool true => some (.ok value, before)
          | .bool false =>
              let state := valueState.2
              match run itr (some state) before with
              | none => none
              | some (.error error, after) => some (.error (.inl error), after)
              | some (.ok next, after) => iteratorUpperBoundLoop run itr next after
          | _ => some (.error (.inr (.inl (.typeError "if"))), before)
partial_fixpoint

/-- Source base/array.jl:805-815 with the existing Exec iteration interface.
No first-iteration success, termination, or correctness law is assumed.
Iterator failure/divergence is retained; an empty iterator throws the existing
thrownNothing outcome, while a nonempty iterator reaches the dynamic Bool check
on the actual installed inferencebarrier(nothing) value. This inference-only
helper is not a new Julia bug claim (source comments at array.jl:803-804). -/
-- Source: base/array.jl:805-815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _iterator_upper_bound(itr)
--     x = iterate(itr)
--     while x !== nothing
--         val = getfield(x, 1)
--         if inferencebarrier(nothing)
--             return val
--         end
--         x = iterate(itr, getfield(x, 2))
--     end
--     throw(nothing)
-- end
-- /Source
def iteratorUpperBoundRuntime {E World Iter State : Type}
    (run : Iter → Option State →
      JuliaLean.base.iterators.Exec E World (Option (JuliaLean.BootCov.JVal × State)))
    (itr : Iter) : UpperBoundExec E World JuliaLean.BootCov.JVal := fun before =>
  match run itr none before with
  | none => none
  | some (.error error, after) => some (.error (.inl error), after)
  | some (.ok x, after) => iteratorUpperBoundLoop run itr x after

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array

/-- The installed physical GenericMemoryRef representation, retaining both
Memory object identity and the exact native pointer-or-offset bits. No logical
offset decoding, bounds behavior or address separation is assumed here. -/
abbrev NativeGrowthRef (T : Type) := NativeCopyRef T

/-- An actual Vector header has a singleton size tuple and a mutable reference.
The store key is its Core object identity; both fields may be changed by an
existing native callback before the source re-reads its reference. -/
structure NativeGrowthVector (T : Type) where
  reference : NativeGrowthRef T
  size : I

structure NativeGrowthState (State T : Type) where
  headers : Nat → NativeGrowthVector T
  other : State

abbrev NativeGrowthWorld (State T : Type) := NativeCopyWorld (NativeGrowthState State T)
abbrev NativeGrowthM (State T A : Type) := NativeCopyM (NativeGrowthWorld State T) A

/-- The already-existing raw Core memory access interface. Only its
memoryrefUnset field is reached by the growth compositions below; the complete
record is retained because the frozen genericmemory unset models take it.
No supplied Base conversion/indexing callback is executed. -/
abbrev NativeGrowthAccess (State T : Type) :=
  JuliaLean.base.genericmemory.MemoryAccessOps (NativeGrowthM State T)
    (NativeCopyMemory T) (JInt .u64) T T

/-- Typed cases of the already-existing boot.CoreOps.memoryrefnewIndex
primitive. Its Value input can be a Memory object or a MemoryRef; the fields
below merely expose these two existing runtime cases at their native types.
The Int argument and boundscheck Bool are passed unchanged after the actual
Base conversion. This retains every primitive error/effect/divergence without
choosing between conflicting bundled models of the false-Bool behavior.
No ordinary memoryref Base callback or correctness law is supplied.
Sources: boot.jl:769-770; JuliaLean/base/boot.lean CoreOps.memoryrefnewIndex. -/
structure NativeGrowthReferenceOps (State T : Type) where
  memoryIndex : NativeCopyMemory T → I → Bool →
    NativeGrowthM State T (NativeGrowthRef T)
  referenceIndex : NativeGrowthRef T → I → Bool →
    NativeGrowthM State T (NativeGrowthRef T)

/-- Source boot.jl:770. Bind the actual native Int conversion and then the
existing Core indexed-reference primitive, retaining its Bool and complete
runtime outcome. The raw physical reference returned by Core is not rebuilt
or normalized by this Base wrapper. -/
-- Source: base/boot.jl:770-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- memoryref(ref::GenericMemoryRef, i::Integer) = memoryrefnew(ref, Int(i), @_boundscheck)
-- /Source
def nativeGrowthShiftRef (references : NativeGrowthReferenceOps State T)
    (boundscheck : Bool) (reference : NativeGrowthRef T) (index : I) :
    NativeGrowthM State T (NativeGrowthRef T) := do
  let index ← nativeCopyLift (JuliaLean.base.io.liftJl
    (JuliaLean.base.int.convert .i64 index))
  references.referenceIndex reference index boundscheck

/-- Source boot.jl:769. Memory input selects its own typed case of the
existing Core primitive directly, after actual Int conversion. It is not
rewritten into a Reference-input call or an assumed bounds/address formula. -/
-- Source: base/boot.jl:769-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- memoryref(mem::GenericMemory, i::Integer) = memoryrefnew(mem, Int(i), @_boundscheck)
-- /Source
def nativeGrowthMemoryref (references : NativeGrowthReferenceOps State T)
    (boundscheck : Bool) (memory : NativeCopyMemory T) (index : I) :
    NativeGrowthM State T (NativeGrowthRef T) := do
  let index ← nativeCopyLift (JuliaLean.base.io.liftJl
    (JuliaLean.base.int.convert .i64 index))
  references.memoryIndex memory index boundscheck

/-- Core getfield observation at array.jl:1118,1145. It reads the current
header map on each call, so native allocation/copy/unset effects are visible. -/
-- Source: base/array.jl:1118-1118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ref = a.ref
-- /Source
def nativeGrowthReadRef (handle : Nat) : NativeGrowthM State T (NativeGrowthRef T) := do
  let world ← nativeCopyLift JuliaLean.base.io.getWorld
  pure (world.other.headers handle).reference

/-- Core setfield! at array.jl:1208, with only its return value discarded by
this storage operation. Updating the current header preserves its current size
and every other header. The growbeg wrapper separately returns the assigned
reference because that source method has no explicit trailing return. -/
-- Source: base/array.jl:1208-1208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     setfield!(a, :ref, newref)
-- /Source
def nativeGrowthWriteRef (handle : Nat) (reference : NativeGrowthRef T) :
    NativeGrowthM State T Unit := do
  let world ← nativeCopyLift JuliaLean.base.io.getWorld
  let current := world.other.headers handle
  let headers := fun key =>
    if key = handle then { current with reference := reference }
    else world.other.headers key
  nativeCopyLift (JuliaLean.base.io.setWorld
    { world with other := { world.other with headers := headers } })

/-- Source array.jl:1114. Bind the actual Memory undef constructor, including
its count/type/byte checks, to the native allocation operands. T and the input
Memory's snapshot layout select typeof(mem); the unrelated target-layout field
of the allocation record is not substituted for that existing Memory type.
The allocated raw payloads, empty singleton, GC/OOM and native identity remain
at the existing allocation interface. -/
-- Source: base/array.jl:1114-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- array_new_memory(mem::Memory, newlen::Int) = typeof(mem)(undef, newlen) # when implemented, this should attempt to first expand mem
-- /Source
def nativeArrayNewMemory
    (allocation : NativeAllocationBoundary State T)
    (memory : NativeCopyMemory T) (newLength : I) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyMemory T) :=
  arrayNewMemory
    (fun memory n => memoryUndef (some (nativeMemoryHeaderLayout memory))
      (nativeCopyLift allocation.empty)
      (fun count => nativeCopyLift (allocation.allocate count)) n)
    memory newLength

/-- Close the Memory-input Base memoryref wrapper reached by the existing
unsetindex! model. Its call is lexically @inbounds in the growth source, so
Core receives false; the raw primitive remains responsible for its outcome.
Core.memoryrefunset! is the existing native field, also passed false by the
actual unset wrappers. The other frozen record fields are unreachable here.
Source: genericmemory.jl:119,148; array.jl:1139,1202. -/
-- Source: base/genericmemory.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsetindex!(A::MemoryRef) = (@_propagate_inbounds_meta; Core.memoryrefunset!(A, :not_atomic, @_boundscheck); A)
-- /Source
-- Source: base/genericmemory.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsetindex!(A::Memory, i::Int) = (@_propagate_inbounds_meta; unsetindex!(memoryref(A, i)); A)
-- /Source
def nativeGrowthAccessOps (references : NativeGrowthReferenceOps State T)
    (native : NativeGrowthAccess State T) : NativeGrowthAccess State T :=
  { native with
    memoryrefAt := nativeGrowthMemoryref references false
    memoryrefNew := references.referenceIndex }

/-- Physical-reference adapter around the already-closed native copy
operations. The reached Base memoryref wrappers pass true to the existing
Core indexed-reference fields for both Memory starts and Reference endpoints;
the growth copy calls are not themselves lexically @inbounds. Core offset is
the existing raw MemoryCopyOps.memoryrefoffset field. C/GC/pointer operations
receive the actual physical references. No ordinary Base callback or native
bounds/address law is supplied. Source: genericmemory.jl:198-227. -/
-- Source: base/genericmemory.jl:198-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_copyto!(dest::MemoryRef{T}, src::MemoryRef{T}, n) where {T}
--     @_terminates_globally_notaskstate_meta
--     n == 0 && return dest
--     @boundscheck memoryref(dest, n), memoryref(src, n)
--     if isbitstype(T)
--         tdest = @_gc_preserve_begin dest
--         tsrc = @_gc_preserve_begin src
--         pdest = unsafe_convert(Ptr{Cvoid}, dest)
--         psrc = unsafe_convert(Ptr{Cvoid}, src)
--         memmove(pdest, psrc, aligned_sizeof(T) * n)
--         @_gc_preserve_end tdest
--         @_gc_preserve_end tsrc
--     else
--         ccall(:jl_genericmemory_copyto, Cvoid, (Any, Ptr{Cvoid}, Any, Ptr{Cvoid}, Int), dest.mem, dest.ptr_or_offset, src.mem, src.ptr_or_offset, Int(n))
--     end
--     return dest
-- end
-- 
-- function unsafe_copyto!(dest::GenericMemoryRef, src::GenericMemoryRef, n)
--     n == 0 && return dest
--     @boundscheck memoryref(dest, n), memoryref(src, n)
--     unsafe_copyto!(dest.mem, memoryrefoffset(dest), src.mem, memoryrefoffset(src), n)
--     return dest
-- end
-- 
-- function unsafe_copyto!(dest::Memory{T}, doffs, src::Memory{T}, soffs, n) where{T}
--     n == 0 && return dest
--     unsafe_copyto!(memoryref(dest, doffs), memoryref(src, soffs), n)
--     return dest
-- end
-- /Source
def nativeGrowthCopyOps
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove) (references : NativeGrowthReferenceOps State T) :
    NativeCopyOps (NativeGrowthState State T) T :=
  let operations := nativeCopyOps layout elementType native ccall
  { operations with
    checkEnd := nativeGrowthShiftRef references true
    memoryrefDest := nativeGrowthMemoryref references true
    memoryrefSource := nativeGrowthMemoryref references true
    memoryrefoffset := native.memoryrefoffset }

/-- Existing Storage closure for the native-Int growth methods. Every reached
ordinary Base field is bound: checked arithmetic, native div, overallocation,
Memory allocation, Memory/MemoryRef unsafe copy and both unsetindex! wrappers.
Only the already-existing Core/C allocation/indexed-reference/offset/copy/GC/
unset operands remain.
Array fields are mutable in the shared world; no cached header is used for the
source's final concurrent-resize guard. Source: array.jl:1116-1210. -/
-- Source: base/array.jl:1116-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _growbeg_internal!(a::Vector, delta::Int, len::Int)
--     @_terminates_locally_meta
--     ref = a.ref
--     mem = ref.mem
--     offset = memoryrefoffset(ref)
--     newlen = checked_add(len, delta)
--     memlen = length(mem)
--     if offset < 1 || offset - 1 > memlen || len > memlen - (offset - 1)
--         throw(ConcurrencyViolationError("Vector has invalid state. Don't modify internal fields incorrectly, or resize without correct locks"))
--     end
--     # since we will allocate the array in the middle of the memory we need at least 2*delta extra space
--     # the +1 is because I didn't want to have an off by 1 error.
--     newmemlen = max(overallocation(len), checked_add(len, checked_mul(2, delta), 1))
--     newoffset = div(newmemlen - newlen, 2) + 1
--     # If there is extra data after the end of the array we can use that space so long as there is enough
--     # space at the end that there won't be quadratic behavior with a mix of growth from both ends.
--     # Specifically, we want to ensure that we will only do this operation once before
--     # increasing the size of the array, and that we leave enough space at both the beginning and the end.
--     if newlen < memlen && newoffset < memlen - newlen
--         newoffset = div(memlen - newlen, 2) + 1
--         newmem = mem
--         unsafe_copyto!(newmem, newoffset + delta, mem, offset, len)
--         for j in offset:min(newoffset + delta, offset + len)-1
--             @inbounds unsetindex!(mem, j)
--         end
--     else
--         newmem = array_new_memory(mem, newmemlen)
--         unsafe_copyto!(newmem, newoffset + delta, mem, offset, len)
--     end
--     if ref !== a.ref
--         throw(ConcurrencyViolationError("Vector can not be resized concurrently"))
--     end
--     setfield!(a, :ref, @inbounds memoryref(newmem, newoffset))
-- end
-- /Source
def nativeGrowthStorage
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove)
    (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T)
    (references : NativeGrowthReferenceOps State T) :
    Storage (NativeGrowthM State T) Nat (NativeCopyMemory T) (NativeGrowthRef T) :=
  let copy := nativeGrowthCopyOps layout elementType native ccall references
  let memory := nativeGrowthAccessOps references access
  let divide : I → I → NativeGrowthM State T I := fun a b => nativeCopyLift (JuliaLean.base.io.liftJl
    (JuliaLean.base.int.div_BitSigned64 a b))
  let bounds : Nat → I → NativeGrowthM State T Unit := fun handle index => do
    let world ← nativeCopyLift JuliaLean.base.io.getWorld
    if !(JuliaLean.base.essentials.checkboundsBool (world.other.headers handle).size index) then
      throwThe Error .bounds
  { ref := nativeGrowthReadRef
    memory := fun reference => reference.mem
    offset := native.memoryrefoffset
    length := fun handle => do
      let world ← nativeCopyLift JuliaLean.base.io.getWorld
      let header := world.other.headers handle
      pure (nativeCopyLength (.array
        ⟨handle, header.reference, [header.size]⟩))
    memLength := fun memory => pure (nativeCopyLength (.memory memory))
    sameRef := fun left right =>
      decide (left.mem.identity = right.mem.identity) &&
      JuliaLean.base.int.eq left.ptr_or_offset right.ptr_or_offset
    sameMem := fun left right => decide (left.identity = right.identity)
    setRef := nativeGrowthWriteRef
    setSize := fun handle size => do
      let world ← nativeCopyLift JuliaLean.base.io.getWorld
      let current := world.other.headers handle
      let headers := fun key =>
        if key = handle then { current with size := size }
        else world.other.headers key
      nativeCopyLift (JuliaLean.base.io.setWorld
        { world with other := { world.other with headers := headers } })
    memoryref := nativeGrowthMemoryref references false
    shiftref := nativeGrowthShiftRef references false
    allocate := nativeArrayNewMemory allocation
    copyMemory := fun dest destOffset src srcOffset count => do
      let _ ← JuliaLean.base.genericmemory.unsafeCopytoMemoryTyped (T := T)
        copy true dest destOffset src srcOffset count
      pure ()
    copyRef := fun dest src count => do
      let _ ← JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T) copy true dest src count
      pure ()
    unsetMemory := fun mem index => do
      let _ ← JuliaLean.base.genericmemory.unsetindexMemoryInt memory false mem index
      pure ()
    unsetArray := fun handle index => do
      let _ ← unsetindexInt bounds
        (fun handle index => do nativeGrowthShiftRef references false (← nativeGrowthReadRef handle) index)
        (fun reference => do
          let _ ← JuliaLean.base.genericmemory.unsetindexRef memory false reference
          pure ()) handle index
      pure ()
    checkedAdd := fun a b => nativeCopyLift (JuliaLean.base.io.liftJl
      (JuliaLean.base.checked.checkedAddBits a b))
    checkedMul := fun a b => nativeCopyLift (JuliaLean.base.io.liftJl
      (JuliaLean.base.checked.checkedMulBits a b))
    divide := divide
    overallocation := overallocation JuliaLean.base.int.ctlz_int divide
      JuliaLean.base.int.shl_Int }

/-- Source array.jl:1116-1149, over the concrete native store. Unlike the frozen
Unit-returning growbegInternal abstraction, this complete source variant
returns the MemoryRef produced by its final setfield! expression. The old
model remains unchanged. Checked arithmetic, allocation/copy/unset and the
post-callback reference re-read retain their source order. -/
-- Source: base/array.jl:1116-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _growbeg_internal!(a::Vector, delta::Int, len::Int)
--     @_terminates_locally_meta
--     ref = a.ref
--     mem = ref.mem
--     offset = memoryrefoffset(ref)
--     newlen = checked_add(len, delta)
--     memlen = length(mem)
--     if offset < 1 || offset - 1 > memlen || len > memlen - (offset - 1)
--         throw(ConcurrencyViolationError("Vector has invalid state. Don't modify internal fields incorrectly, or resize without correct locks"))
--     end
--     # since we will allocate the array in the middle of the memory we need at least 2*delta extra space
--     # the +1 is because I didn't want to have an off by 1 error.
--     newmemlen = max(overallocation(len), checked_add(len, checked_mul(2, delta), 1))
--     newoffset = div(newmemlen - newlen, 2) + 1
--     # If there is extra data after the end of the array we can use that space so long as there is enough
--     # space at the end that there won't be quadratic behavior with a mix of growth from both ends.
--     # Specifically, we want to ensure that we will only do this operation once before
--     # increasing the size of the array, and that we leave enough space at both the beginning and the end.
--     if newlen < memlen && newoffset < memlen - newlen
--         newoffset = div(memlen - newlen, 2) + 1
--         newmem = mem
--         unsafe_copyto!(newmem, newoffset + delta, mem, offset, len)
--         for j in offset:min(newoffset + delta, offset + len)-1
--             @inbounds unsetindex!(mem, j)
--         end
--     else
--         newmem = array_new_memory(mem, newmemlen)
--         unsafe_copyto!(newmem, newoffset + delta, mem, offset, len)
--     end
--     if ref !== a.ref
--         throw(ConcurrencyViolationError("Vector can not be resized concurrently"))
--     end
--     setfield!(a, :ref, @inbounds memoryref(newmem, newoffset))
-- end
-- /Source
def nativeGrowbegInternal
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove)
    (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T)
    (references : NativeGrowthReferenceOps State T) (handle : Nat) (delta len : I) :
    NativeGrowthM State T (NativeGrowthRef T) := do
  let storage := nativeGrowthStorage layout elementType native ccall allocation access references
  let reference ← storage.ref handle
  let memory := storage.memory reference
  let offset := storage.offset reference
  let newLength ← storage.checkedAdd len delta
  let memoryLength ← storage.memLength memory
  if offset < one || offset - one > memoryLength || len > memoryLength - (offset - one) then
    throwThe Error (.concurrency "Vector has invalid state. Don't modify internal fields incorrectly, or resize without correct locks")
  let grown ← storage.overallocation len
  let twiceDelta ← storage.checkedMul (JInt.wrap .i64 2) delta
  let requested ← nativeCopyLift (JuliaLean.base.io.liftJl
    (JuliaLean.base.checked.checkedAdd3 JuliaLean.base.checked.checkedAddBits
      JuliaLean.base.checked.checkedAddBits len twiceDelta one))
  let newMemoryLength := max grown requested
  let mut newOffset := (← storage.divide (newMemoryLength - newLength) (JInt.wrap .i64 2)) + one
  let newMemory ← if newLength < memoryLength && newOffset < memoryLength - newLength then do
      newOffset := (← storage.divide (memoryLength - newLength) (JInt.wrap .i64 2)) + one
      storage.copyMemory memory (newOffset + delta) memory offset len
      for index in intRange offset (min (newOffset + delta) (offset + len) - one) do
        storage.unsetMemory memory index
      pure memory
    else do
      let allocated ← storage.allocate memory newMemoryLength
      storage.copyMemory allocated (newOffset + delta) memory offset len
      pure allocated
  if !(storage.sameRef reference (← storage.ref handle)) then
    throwThe Error (.concurrency "Vector can not be resized concurrently")
  let result ← storage.memoryref newMemory newOffset
  storage.setRef handle result
  pure result

/-- Source array.jl:1171-1210. The existing growendInternal body has the
correct explicit trailing nothing return and is reused with the complete
native storage closure. It forms newref before copying, unsets only when the
Memory object identities match, then re-reads the current Vector reference. -/
-- Source: base/array.jl:1171-1210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _growend_internal!(a::Vector, delta::Int, len::Int)
--     @_terminates_locally_meta
--     ref = a.ref
--     mem = ref.mem
--     memlen = length(mem)
--     newlen = checked_add(len, delta)
--     offset = memoryrefoffset(ref)
--     if offset < 1 || offset - 1 > memlen || len > memlen - (offset - 1)
--         throw(ConcurrencyViolationError("Vector has invalid state. Don't modify internal fields incorrectly, or resize without correct locks"))
--     end
--     newmemlen = checked_add(offset - 1, newlen)
-- 
--     if offset - 1 > newlen && offset - 1 - newlen > div(newlen, 4)
--         # If the offset is far enough that we can copy without resizing
--         # while maintaining proportional spacing on both ends of the array
--         # note that this branch prevents infinite growth when doing combinations
--         # of push! and popfirst! (i.e. when using a Vector as a queue)
--         newmem = mem
--         newoffset = div(newlen, 8) + 1
--     else
--         # grow either by our computed overallocation factor
--         # or exactly the requested size, whichever is larger
--         # TODO we should possibly increase the offset if the current offset is nonzero.
--         newmemlen2 = max(overallocation(memlen), newmemlen)
--         newmem = array_new_memory(mem, newmemlen2)
--         newoffset = offset
--     end
--     newref = @inbounds memoryref(newmem, newoffset)
--     unsafe_copyto!(newref, ref, len)
--     if newmem === mem
--         for j in max(offset, newoffset + len):offset+len-1
--             @inbounds unsetindex!(mem, j)
--         end
--     end
--     if ref !== a.ref
--         @noinline throw(ConcurrencyViolationError("Vector can not be resized concurrently"))
--     end
--     setfield!(a, :ref, newref)
-- return
-- end
-- /Source
def nativeGrowendInternal
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove)
    (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T)
    (references : NativeGrowthReferenceOps State T) (handle : Nat) (delta len : I) :
    NativeGrowthM State T Unit :=
  growendInternal (nativeGrowthStorage layout elementType native ccall allocation access references)
    handle delta len

end JuliaLean.base.array.Models1Group13

namespace JuliaLean.base.array.Models1Group14

open JuliaLean
open JuliaLean.base.array (I one zero)

/-- Source-faithful sized iterator append, including effects and exceptions of
`length(iter)` and `Int(length(iter))`. The generic integer representation `Z`
belongs to the existing user-method boundary; it is not restricted to a machine
integer before the source's explicit `Int` conversion. The remaining interface
arguments have the same roles as in the frozen `appendSized` model. No law about
their correctness is assumed. Julia source: base/array.jl:1434-1441. -/
-- Source: base/array.jl:1434-1441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _append!(a::AbstractVector, ::Union{HasLength,HasShape}, iter)
--     n = Int(length(iter))::Int
--     sizehint!(a, length(a) + n; shrink=false)
--     for item in iter
--         push!(a, item)
--     end
--     a
-- end
-- /Source
def appendSized [Monad m] [ForIn m X E]
    (length : X → m Z) (toInt : Z → m I) (arrayLength : A → m I)
    (sizehint : A → I → Bool → m Unit) (push : A → E → m Unit)
    (a : A) (itr : X) : m A := do
  let n ← toInt (← length itr)
  sizehint a ((← arrayLength a) + n) false
  for item in itr do push a item
  pure a

/-- Iterator append retains the source's trait call and then selects the actual
sized or unsized helper. Trait/length calls may throw or change the runtime state.
The sized helper above is a required local dependency of this earlier public
wrapper. `classifySize` represents dispatch on the returned iterator-size tag;
`none` denotes a value outside IteratorSize and raises MethodError.
Julia source: base/array.jl:1430. -/
-- Source: base/array.jl:1430-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- append!(a::AbstractVector, iter) = _append!(a, IteratorSize(iter), iter)
-- /Source
def appendIterator [Monad m] [MonadExceptOf JuliaLean.base.array.Error m] [ForIn m X E]
    (iteratorSize : X → m Size) (classifySize : Size → Option Bool)
    (length : X → m Z) (toInt : Z → m I) (arrayLength : A → m I)
    (sizehint : A → I → Bool → m Unit) (push : A → E → m Unit)
    (a : A) (itr : X) : m A := do
  let isz ← iteratorSize itr
  match classifySize isz with
  | none => throw (.method "_append!")
  | some true => appendSized length toInt arrayLength sizehint push a itr
  | some false => JuliaLean.base.array.appendUnsized push a itr

/-- Source-faithful sized prepend at the existing generic method boundary. The
one-based-indexing check precedes both effectful length calls; the counter uses
Julia `Int` arithmetic. User iterator/array operations remain explicit boundary
inputs, without supplied correctness laws. Julia source: base/array.jl:1499-1511. -/
-- Source: base/array.jl:1499-1511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _prepend!(a::Vector, ::Union{HasLength,HasShape}, iter)
--     @_terminates_locally_meta
--     require_one_based_indexing(a)
--     n = Int(length(iter))::Int
--     sizehint!(a, length(a) + n; first=true, shrink=false)
--     n = 0
--     for item in iter
--         n += 1
--         pushfirst!(a, item)
--     end
--     reverse!(a, 1, n)
--     a
-- end
-- /Source
def prependSized [Monad m] [ForIn m X E]
    (requireOneBased : A → m Unit) (length : X → m Z)
    (toInt : Z → m I) (arrayLength : A → m I)
    (sizehint : A → I → Bool → Bool → m Unit)
    (pushfirst : A → E → m Unit) (reverse : A → I → I → m Unit)
    (a : A) (itr : X) : m A := do
  requireOneBased a
  let n ← toInt (← length itr)
  sizehint a ((← arrayLength a) + n) true false
  let mut n := zero
  for item in itr do
    n := n + one
    pushfirst a item
  reverse a one n
  pure a

/-- Generic prepend forwarding at the closed pinned-Base method-table boundary.
The IteratorSize call occurs before `_prepend!` dispatch. Only native Vector
receivers have installed `_prepend!` methods (1499 and 1512). `isVector` is the
existing resolved runtime type tag; `classifySize` is `some true` for HasLength
or HasShape, `some false` for another IteratorSize, and `none` for a malformed
trait result. These are type/dispatch projections, not unknown callee bodies.
User-added `_prepend!` extensions are outside this explicitly closed method table.
Both selected bodies are actual models, including the refined sized helper above.
Julia source: base/array.jl:1495; helper dispatch:1499-1520. -/
-- Source: base/array.jl:1495-1495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- prepend!(a::AbstractVector, iter) = _prepend!(a, IteratorSize(iter), iter)
-- /Source
def prependIterator [Monad m] [MonadExceptOf JuliaLean.base.array.Error m]
    [ForIn m X E] (isVector : A → Bool)
    (iteratorSize : X → m Size) (classifySize : Size → Option Bool)
    (requireOneBased : A → m Unit) (length : X → m Z)
    (toInt : Z → m I) (arrayLength : A → m I)
    (sizehint : A → I → Bool → Bool → m Unit)
    (pushfirst : A → E → m Unit) (reverse : A → I → I → m Unit)
    (a : A) (itr : X) : m A := do
  let trait ← iteratorSize itr
  if !(isVector a) then throw (.method "_prepend!")
  match classifySize trait with
  | none => throw (.method "_prepend!")
  | some true =>
    prependSized requireOneBased length toInt arrayLength sizehint pushfirst reverse a itr
  | some false =>
    JuliaLean.base.array.prependUnsized pushfirst reverse a itr

end JuliaLean.base.array.Models1Group14


namespace JuliaLean.base.array.Models1Group14

open JuliaLean

/-- The existing array/storage and user-defined iteration boundary for
`deleteat!(a::Vector, inds::AbstractVector{Bool})`, base/array.jl:2000.
`Count` is the actual result type of the mask's `length`; it is not silently
converted to `Int`. Equality may itself have effects or throw for a user type.
The array's mutation primitives are those of the pre-existing `Storage`.
These fields expose extension points; they do not implement arbitrary user code. -/
structure MaskOps (m : Type → Type) (A Mem Ref Mask Count E : Type) where
  storage : Storage m A Mem Ref
  maskLength : Mask → m Count
  sameLength : Count → I → m Bool
  assigned : A → I → m Bool
  read : A → I → m E
  write : A → E → I → m Unit

/-- Live mask iteration for base/array.jl:2000-2010. Unlike the earlier
`List Bool` specialization, each `ForIn` step reads the next Boolean only after
the previous array mutation. The existing `copyItem` and `deleteend` bodies are
used, including their unassigned-slot handling and errors. The `ForIn` instance
is the same explicit custom-iterator interface used elsewhere in this file. -/
-- Source: base/array.jl:2000-2010 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function deleteat!(a::Vector, inds::AbstractVector{Bool})
--     n = length(a)
--     length(inds) == n || throw(BoundsError(a, inds))
--     p = 1
--     for (q, i) in enumerate(inds)
--         @inbounds _copy_item!(a, p, q)
--         p += !i
--     end
--     _deleteend!(a, n-p+1)
--     return a
-- end
-- /Source
def deleteatMask [Monad m] [MonadExceptOf Error m] [ForIn m Mask Bool]
    (o : MaskOps m A Mem Ref Mask Count E) (a : A) (inds : Mask) : m A := do
  let n ← o.storage.length a
  let count ← o.maskLength inds
  if !(← o.sameLength count n) then throw .bounds
  let mut p := one
  let mut q := one
  for i in inds do
    copyItem o.assigned o.read o.write o.storage.unsetArray a p q
    p := p + (if !i then one else zero)
    q := q + one
  deleteend o.storage pure a (n - p + one)
  pure a


end JuliaLean.base.array.Models1Group14

namespace JuliaLean.base.array.Models1Group14

open JuliaLean JuliaLean.base.array

/-- `reverseind(a::AbstractVector, i::Integer)`, base/array.jl:2276-2279.
Retains construction of LinearIndices and both endpoint observations as effectful
calls, using the same existing boundary as reverseBang. Addition has native Int
width; subtraction receives the original index type Z, preserving promotion and
any exception from an extended Integer subtraction. No index conversion occurs. -/
-- Source: base/array.jl:2276-2279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function reverseind(a::AbstractVector, i::Integer)
--     li = LinearIndices(a)
--     first(li) + last(li) - i
-- end
-- /Source
def reverseindEffectful {m : Type → Type} [Monad m]
    {A Linear Z W : Type} (linearIndices : A → m Linear)
    (first last : Linear → m I) (subtract : I → Z → m W)
    (a : A) (i : Z) : m W := do
  let li ← linearIndices a
  let lower ← first li
  let upper ← last li
  subtract (lower + upper) i

end JuliaLean.base.array.Models1Group14

namespace JuliaLean.base.array.Models1Group14

open JuliaLean JuliaLean.base.array

/-- Error channels retained by the existing array/abstractarray bodies and by
arbitrary user interfaces reached from `findall`, base/array.jl:2784-2787. -/
inductive FindallError (UserError : Type) where
  | array (error : JuliaLean.base.array.Error)
  | abstractArray (error : JuliaLean.base.abstractarray.ArrayError)
  | user (error : UserError)

/-- The installed iterator execution domain: `none` denotes divergence and a
returned exception retains the state at its throw point. No iteration fuel or
finite-rank restriction is added for base/array.jl:2784-2787. -/
abbrev FindallM (UserError World : Type) :=
  JuliaLean.base.iterators.Exec (FindallError UserError) World

instance findallErrorExcept {UserError World : Type} :
    MonadExceptOf (FindallError UserError) (FindallM UserError World) where
  throw error := fun world => some (.error error, world)
  tryCatch action handler := fun world => do
    let (result, world) ← action world
    match result with
    | .ok value => some (.ok value, world)
    | .error error => handler error world

instance findallArrayExcept {UserError World : Type} :
    MonadExceptOf JuliaLean.base.array.Error (FindallM UserError World) where
  throw error := fun world => some (.error (.array error), world)
  tryCatch action handler := fun world => do
    let (result, world) ← action world
    match result with
    | .ok value => some (.ok value, world)
    | .error (.array error) => handler error world
    | .error error => some (.error error, world)

instance findallAbstractArrayExcept {UserError World : Type} :
    MonadExceptOf JuliaLean.base.abstractarray.ArrayError (FindallM UserError World) where
  throw error := fun world => some (.error (.abstractArray error), world)
  tryCatch action handler := fun world => do
    let (result, world) ← action world
    match result with
    | .ok value => some (.ok value, world)
    | .error (.abstractArray error) => handler error world
    | .error error => some (.error error, world)

/-- The actual Filter and Generator representations in the generator expression
at base/array.jl:2785. Both pair projections and the predicate may have effects.
Construction itself does not iterate, project a pair, or invoke the predicate. -/
abbrev FindallGenerator (m : Type → Type) (Pairs Pair Key : Type) :=
  JuliaLean.base.generator.Generator
    (JuliaLean.base.iterators.Filter (Pair → m Bool) Pairs) (Pair → m Key)

/-- Existing iterator, pair, collection and type-inference interfaces used by
base/array.jl:2784-2787. The two pair decoders retain the distinction between
destructuring in Filter and Generator's Tuple{Any,Any} assertion. `test` includes
Julia's Boolean-condition check, so a non-Bool result throws TypeError through
this existing typed-condition interface. The compiler inference operation and
type-join operation remain the explicit type-runtime boundary of defaultEltype;
they are not claimed to be complete compiler models.

`functionField` includes errors when a repeated `keys(A)` result has no `.f`
field. `Tag` admits the values encountered by that field read, including values
that are not types. `promoteUnion` includes its resulting dispatch errors. -/
structure FindallInterfaces (m : Type → Type)
    (A Pairs Pair Value Key State Raw Keys Tag : Type) where
  pairs : A → m Pairs
  iteratePairs : Pairs → Option State → m (Option Raw)
  unpackPairState : Raw → m (Pair × State)
  isTuple2 : Raw → Bool
  tuple2 : Pair → State → Raw
  assertPairState : Raw → m (Pair × State)
  pairValue : Pair → m Value
  pairKey : Pair → m Key
  test : Value → m Bool
  keys : A → m Keys
  keysIsGenerator : Keys → Bool
  functionField : Keys → m Tag
  isType : Tag → Bool
  inferKeys : Keys → m Tag
  inferGenerator : FindallGenerator m Pairs Pair Key → m Tag
  promoteUnion : Tag → m Tag
  isBottom : Tag → Bool

/-- Native output-Vector runtime boundaries already used by Array's allocation,
push, sizehint, copy and widening models. Type tags and element conversion remain
runtime operations. In particular, `storage.copyRef` is the existing raw memory
copy boundary, including element conversion when source/destination types differ;
this declaration does not claim to implement genericmemory.jl's raw copy.

`dormantUnion` is the existing generic pushWiden interface slot. The native Vector
receiver fixes its AbstractSet test to false, so this slot is never executed. -/
structure FindallVectorRuntime (m : Type → Type) (Key Tag B Mem Ref : Type) where
  storage : Storage m B Mem Ref
  elementType : B → Tag
  valueType : Key → Tag
  isElement : Tag → Key → Bool
  promoteJoin : Tag → Tag → m Tag
  layout : Tag → Option MemoryLayout
  emptyMemory : Tag → m Mem
  allocateMemory : Tag → Nat → m Mem
  newHeader : Tag → Mem → List I → m B
  /-- Includes `convert(T, item)::T`, its effects, and its TypeError. -/
  convertElement : B → Key → m Key
  bounds : B → I → m Unit
  memoryrefnew : B → I → Bool → m Ref
  store : Ref → Key → Bool → m Unit
  dormantUnion : B → B → m Unit

/-- Empty/native Vector allocation reached by findall's two collectors,
base/array.jl:688-689,833-837. Calls the installed Array constructor body. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
def findallAllocate {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {Key Tag B Mem Ref : Type} (ops : FindallVectorRuntime m Key Tag B Mem Ref)
    (tag : Tag) (n : I) : m B :=
  arrayUndef1 (ops.layout tag) (ops.emptyMemory tag)
    (ops.allocateMemory tag) (ops.newHeader tag) n

/-- Native Vector `empty`, base/abstractarray.jl:892. The abstractarray model's
type parameter is a Lean Type, whereas this file retains runtime type tags;
the local adapter invokes the installed Array `similar` and allocation bodies. -/
-- Source: base/abstractarray.jl:892-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- empty(a::AbstractVector{T}, ::Type{U}=T) where {T,U} = similar(a, U, 0)
-- /Source
def findallEmpty {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {Key Tag B Mem Ref : Type} (ops : FindallVectorRuntime m Key Tag B Mem Ref)
    (a : B) (tag : Tag) : m B :=
  similar419 (fun n => findallAllocate ops tag n) a zero

/-- The installed native Vector push!/growend!/safe-store bodies used by
base/array.jl:691,918,931,942. Conversion precedes growth. -/
-- Source: base/array.jl:1353-1365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function push!(a::Vector{T}, item) where T
--     @inline
--     # convert first so we don't grow the array if the assignment won't work
--     # and also to avoid a dynamic dispatch in the common case that
--     # `item` is poorly-typed and `a` is well-typed
--     item = item isa T ? item : convert(T, item)::T
--     return _push!(a, item)
-- end
-- function _push!(a::Vector{T}, item::T) where T
--     _growend!(a, 1)
--     @_safeindex a[length(a)] = item
--     return a
-- end
-- /Source
def findallPush {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {Key Tag B Mem Ref : Type} (ops : FindallVectorRuntime m Key Tag B Mem Ref)
    (dest : B) (key : Key) : m Unit := do
  let _ ← JuliaLean.base.array.push (ops.isElement (ops.elementType dest)) id
    (ops.convertElement dest)
    (push1361
      (growend ops.storage pure (growendInternal ops.storage))
      ops.storage.length
      (fun a value i => do
        let _ ← safeSetindex1057 ops.memoryrefnew ops.store a value i
        pure ())) dest key
  pure ()

/-- Source-ordered checked Array copy used by append during push_widen,
base/array.jl:299-315,1427,929. The native offsets/count retain wrapping Int
arithmetic; the final raw-memory copy is Storage's existing runtime boundary. -/
-- Source: base/array.jl:288-289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copyto!(dest::Array, doffs::Integer, src::Array, soffs::Integer, n::Integer) =
--     (@_propagate_inbounds_meta; _copyto_impl!(dest, doffs, src, soffs, n))
-- /Source
-- Source: base/array.jl:299-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _copyto_impl!(dest::Union{Array,Memory}, doffs::Integer, src::Union{Array,Memory}, soffs::Integer, n::Integer)
--     @inline
--     n == 0 && return dest
--     n > 0 || _throw_argerror("Number of elements to copy must be non-negative.")
--     @boundscheck checkbounds(dest, doffs)
--     @boundscheck n <= length(dest) - doffs + 1 || throw(BoundsError(dest, length(dest) + 1))
--     @boundscheck checkbounds(src, soffs)
--     @boundscheck n <= length(src) - soffs + 1 || throw(BoundsError(src, length(src) + 1))
--     doffs = Int(doffs)
--     soffs = Int(soffs)
--     n = Int(n)
--     @inbounds let dest = memoryref(dest isa Array ? getfield(dest, :ref) : dest, doffs),
--                   src = memoryref(src isa Array ? getfield(src, :ref) : src, soffs)
--         unsafe_copyto!(dest, src, n)
--     end
--     return dest
-- end
-- /Source
def findallCopy {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {Key Tag B Mem Ref : Type} (ops : FindallVectorRuntime m Key Tag B Mem Ref)
    (dest : B) (destOffset : I) (src : B) (srcOffset count : I) : m Unit := do
  let _ ← copyto288
    (copytoImpl
      (fun n => pure (decide (n = zero))) (fun n => pure (decide (n > zero)))
      ops.storage.length ops.storage.length ops.bounds ops.bounds
      (fun n i => pure (n - i)) (fun n i => pure (n - i))
      (fun n i => pure (n + i)) (fun n i => pure (n + i))
      (fun n remaining => pure (decide (n ≤ remaining)))
      (fun n remaining => pure (decide (n ≤ remaining)))
      (fun _ _ => throwThe Error .bounds) (fun _ _ => throwThe Error .bounds)
      pure pure pure
      (fun a i => do ops.storage.shiftref (← ops.storage.ref a) i)
      (fun a i => do ops.storage.shiftref (← ops.storage.ref a) i)
      ops.storage.copyRef)
    dest destOffset src srcOffset count
  pure ()

/-- Widening copies a native Vector into the newly allocated native Vector
with the installed append! method, base/array.jl:1422-1428,929. Runtime
promote_typejoin is the existing type boundary that determines the new element
type; its result contains the old element type, selecting this specialization. -/
-- Source: base/array.jl:1422-1428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function append!(a::Vector{T}, items::Union{AbstractVector{<:T},Tuple}) where T
--     items isa Tuple && (items = map(x -> convert(T, x), items))
--     n = Int(length(items))::Int
--     _growend!(a, n)
--     copyto!(a, length(a)-n+1, items, firstindex(items), n)
--     return a
-- end
-- /Source
def findallAppend {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {Key Tag B Mem Ref : Type} (ops : FindallVectorRuntime m Key Tag B Mem Ref)
    (dest src : B) : m Unit := do
  let _ ← JuliaLean.base.array.appendVector (fun _ => false) pure
    ops.storage.length pure
    (growend ops.storage pure (growendInternal ops.storage))
    ops.storage.length (fun _ => pure one) (findallCopy ops) dest src
  pure ()

/-- The actual sizehint!/growth model reached by push_widen, base/array.jl:924.
The omitted keywords retain their source defaults first=false, shrink=true. -/
-- Source: base/array.jl:1612-1643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sizehint!(a::Vector, sz::Integer; first::Bool=false, shrink::Bool=true)
--     len = length(a)
--     ref = a.ref
--     mem = ref.mem
--     memlen = length(mem)
--     sz = max(Int(sz), len)
--     inc = sz - len
--     if sz <= memlen
--         # if we don't save at least 1/8th memlen then its not worth it to shrink
--         if !shrink || memlen - sz <= div(memlen, 8)
--             return a
--         end
--         newmem = array_new_memory(mem, sz)
--         if first && len != 0
--             newref = memoryref(newmem, inc + 1)
--         else
--             newref = memoryref(newmem)
--         end
--         unsafe_copyto!(newref, ref, len)
--         setfield!(a, :ref, newref)
--     elseif first
--         _growbeg!(a, inc)
--         newref = getfield(a, :ref)
--         newref = memoryref(newref, inc + 1)
--         setfield!(a, :size, (len,)) # undo the size change from _growbeg!
--         setfield!(a, :ref, newref) # undo the offset change from _growbeg!
--     else # last
--         _growend!(a, inc)
--         setfield!(a, :size, (len,)) # undo the size change from _growend!
--     end
--     a
-- end
-- /Source
def findallSizehint {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {Key Tag B Mem Ref : Type} (ops : FindallVectorRuntime m Key Tag B Mem Ref)
    (dest : B) (n : I) : m B :=
  JuliaLean.base.array.sizehint ops.storage pure
    (growbeg ops.storage pure (growbegInternal ops.storage))
    (growend ops.storage pure (growendInternal ops.storage)) dest n

/-- The installed push_widen body, base/array.jl:922-933, closed for native
Vector allocation, sizehint, append and push. Only its existing type-runtime
and Storage primitive boundaries remain parameters. -/
-- Source: base/array.jl:922-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function push_widen(dest, el)
--     @inline
--     new = sizehint!(empty(dest, promote_typejoin(eltype(dest), typeof(el))), length(dest))
--     if new isa AbstractSet
--         # TODO: merge back these two branches when copy! is re-enabled for sets/vectors
--         union!(new, dest)
--     else
--         append!(new, dest)
--     end
--     push!(new, el)
--     return new
-- end
-- /Source
def findallWiden {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {Key Tag B Mem Ref : Type} (ops : FindallVectorRuntime m Key Tag B Mem Ref)
    (dest : B) (key : Key) : m B :=
  pushWiden ops.elementType ops.valueType ops.promoteJoin (findallEmpty ops)
    ops.storage.length (findallSizehint ops) (fun _ => false)
    ops.dormantUnion (findallAppend ops) (findallPush ops) dest key

/-- Expansion of default_eltype at an expression with effects,
base/array.jl:821-831. Each occurrence of the macro argument is evaluated anew.
The field access and compiler/type operations are existing runtime interfaces;
no evaluation of keys(A) is hoisted, shared, or discarded. -/
-- Source: base/array.jl:821-831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro default_eltype(itr)
--     I = esc(itr)
--     return quote
--         if $I isa Generator && ($I).f isa Type
--             T = ($I).f
--         else
--             T = Base._return_type(_iterator_upper_bound, Tuple{typeof($I)})
--         end
--         promote_typejoin_union(T)
--     end
-- end
-- /Source
def findallDefaultEltypeExpression {m : Type → Type} [Monad m]
    {Keys Tag : Type} (expression : m Keys) (isGenerator : Keys → Bool)
    (functionField : Keys → m Tag) (isType : Tag → Bool)
    (inferredType : Keys → m Tag) (promoteUnion : Tag → m Tag) : m Tag := do
  let first ← expression
  let typeFunction ← if isGenerator first then do
      pure (isType (← functionField (← expression)))
    else pure false
  let tag ← if typeFunction then functionField (← expression)
    else inferredType (← expression)
  promoteUnion tag

/-- The local Generator mapping function is an anonymous function, never a
type object, so its default_eltype expansion takes the inference branch.
Base/array.jl:821-831,2785-2786. -/
-- Source: base/array.jl:821-831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro default_eltype(itr)
--     I = esc(itr)
--     return quote
--         if $I isa Generator && ($I).f isa Type
--             T = ($I).f
--         else
--             T = Base._return_type(_iterator_upper_bound, Tuple{typeof($I)})
--         end
--         promote_typejoin_union(T)
--     end
-- end
-- /Source
def findallDefaultGeneratorType {m : Type → Type} [Monad m]
    {A Pairs Pair Value Key State Raw Keys Tag : Type}
    (ops : FindallInterfaces m A Pairs Pair Value Key State Raw Keys Tag)
    (g : FindallGenerator m Pairs Pair Key) : m Tag := do
  ops.promoteUnion (← ops.inferGenerator g)

/-- One deferred step of the actual Filter followed by the actual Generator
model, base/iterators.jl:578-592 and base/generator.jl:44-50. Rejected values do
not read their key, and an accepted key is evaluated before collection stores. -/
-- Source: base/iterators.jl:578-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(f::Filter, state...)
--     y = iterate(f.itr, state...)
--     while y !== nothing
--         v, s = y
--         if f.flt(v)
--             if y isa Tuple{Any,Any}
--                 return (v, s) # incorporate type information that may be improved by user-provided `f.flt`
--             else
--                 return y
--             end
--         end
--         y = iterate(f.itr, s)
--     end
--     nothing
-- end
-- 
-- /Source
-- Source: base/generator.jl:44-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(g::Generator, s...)
--     @inline
--     y = iterate(g.iter, s...)
--     y === nothing && return nothing
--     y = y::Tuple{Any, Any} # try to give inference some idea of what to expect about the behavior of the next line
--     return (g.f(y[1]), y[2])
-- end
-- /Source
def findallIterate {UserError World A Pairs Pair Value Key State Raw Keys Tag : Type}
    (ops : FindallInterfaces (FindallM UserError World)
      A Pairs Pair Value Key State Raw Keys Tag)
    (g : FindallGenerator (FindallM UserError World) Pairs Pair Key)
    (state : Option State) : FindallM UserError World (Option (Key × State)) :=
  JuliaLean.base.generator.iterateGenerator (fun f p => f p)
    (JuliaLean.base.iterators.filterScan ops.iteratePairs ops.unpackPairState
      (fun test p => test p) ops.isTuple2 ops.tuple2)
    ops.assertPairState g state

/-- Lowered loop driver for the typed collector's Julia for loop,
base/array.jl:690-692. This uses the installed Exec flat least-fixpoint domain;
divergent iteration/predicates remain divergent rather than producing a value. -/
-- Source: base/array.jl:688-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _collect(::Type{T}, itr, isz::SizeUnknown) where T
--     a = Vector{T}()
--     for x in itr
--         push!(a, x)
--     end
--     return a
-- end
-- /Source
def findallForInLoop {UserError World A Pairs Pair Value Key State Raw Keys Tag Acc : Type}
    (ops : FindallInterfaces (FindallM UserError World)
      A Pairs Pair Value Key State Raw Keys Tag)
    (g : FindallGenerator (FindallM UserError World) Pairs Pair Key)
    (state : Option State) (acc : Acc)
    (step : Key → Acc → FindallM UserError World (ForInStep Acc)) :
    FindallM UserError World Acc :=
  fun world => match findallIterate ops g state world with
  | none => none
  | some (.error error, world) => some (.error error, world)
  | some (.ok none, world) => some (.ok acc, world)
  | some (.ok (some (key, next)), world) =>
      match step key acc world with
      | none => none
      | some (.error error, world) => some (.error error, world)
      | some (.ok (.done acc), world) => some (.ok acc, world)
      | some (.ok (.yield acc), world) =>
          findallForInLoop ops g (some next) acc step world
partial_fixpoint

/-- Local ForIn dictionary for the real deferred Generator, used only by the
existing typed collect body at base/array.jl:688-694. -/
-- Source: base/array.jl:688-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _collect(::Type{T}, itr, isz::SizeUnknown) where T
--     a = Vector{T}()
--     for x in itr
--         push!(a, x)
--     end
--     return a
-- end
-- /Source
def findallGeneratorForIn {UserError World A Pairs Pair Value Key State Raw Keys Tag : Type}
    (ops : FindallInterfaces (FindallM UserError World)
      A Pairs Pair Value Key State Raw Keys Tag) :
    ForIn (FindallM UserError World)
      (FindallGenerator (FindallM UserError World) Pairs Pair Key) Key where
  forIn g acc step := findallForInLoop ops g none acc step

/-- General grow_to! loop, base/array.jl:935-949. The installed finite growTo
model cannot represent arbitrary Julia iterators, so this necessary dependency
uses the existing Exec partial-fixpoint machinery. The output Vector's element
type is an immutable runtime field; successful pushes do not change it. A
widening call returns a new handle, whose type is read at redispatch. -/
-- Source: base/array.jl:935-949 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function grow_to!(dest, itr, st)
--     T = eltype(dest)
--     y = iterate(itr, st)
--     while y !== nothing
--         el, st = y
--         if el isa T
--             push!(dest, el)
--         else
--             new = push_widen(dest, el)
--             return grow_to!(new, itr, st)
--         end
--         y = iterate(itr, st)
--     end
--     return dest
-- end
-- /Source
def findallGrowTo {UserError World A Pairs Pair Value Key State Raw Keys Tag B Mem Ref : Type}
    (ops : FindallInterfaces (FindallM UserError World)
      A Pairs Pair Value Key State Raw Keys Tag)
    (vectors : FindallVectorRuntime (FindallM UserError World) Key Tag B Mem Ref)
    (dest : B) (g : FindallGenerator (FindallM UserError World) Pairs Pair Key)
    (state : State) : FindallM UserError World B :=
  let tag := vectors.elementType dest
  fun world => match findallIterate ops g (some state) world with
  | none => none
  | some (.error error, world) => some (.error error, world)
  | some (.ok none, world) => some (.ok dest, world)
  | some (.ok (some (key, next)), world) =>
      if vectors.isElement tag key then
        match findallPush vectors dest key world with
        | none => none
        | some (.error error, world) => some (.error error, world)
        | some (.ok (), world) => findallGrowTo ops vectors dest g next world
      else
        match findallWiden vectors dest key world with
        | none => none
        | some (.error error, world) => some (.error error, world)
        | some (.ok new, world) => findallGrowTo ops vectors new g next world
partial_fixpoint

/-- Initial grow_to! dispatch calls the installed growFirst body,
base/array.jl:914-920, and the general loop above. The first accepted key is
read before the replacement Vector allocation, then pushed before further
iteration. The initially allocated empty Vector survives an empty iterator. -/
-- Source: base/array.jl:914-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function grow_to!(dest, itr)
--     y = iterate(itr)
--     y === nothing && return dest
--     dest2 = empty(dest, typeof(y[1]))
--     push!(dest2, y[1])
--     grow_to!(dest2, itr, y[2])
-- end
-- /Source
def findallGrowFirst {UserError World A Pairs Pair Value Key State Raw Keys Tag B Mem Ref : Type}
    (ops : FindallInterfaces (FindallM UserError World)
      A Pairs Pair Value Key State Raw Keys Tag)
    (vectors : FindallVectorRuntime (FindallM UserError World) Key Tag B Mem Ref)
    (dest : B) (g : FindallGenerator (FindallM UserError World) Pairs Pair Key) :
    FindallM UserError World B :=
  growFirst (fun g => findallIterate ops g none)
    (fun a value => findallEmpty vectors a (vectors.valueType value))
    (findallPush vectors) (findallGrowTo ops vectors) dest g

/-- Both real collector bodies for the actual SizeUnknown Filter generator,
base/array.jl:684-694,833-853. The trait is fixed by Filter's installed trait
method, not chosen by a caller. Every reachable allocation, growth, push and
widening operation is a concrete composition of installed bodies.

`dormant` retains the original structured collector interface's sized branch
fields only; they are not executed, nor claimed to implement missing callees.
The reachable size/defaultEltype/unknown/emptyVector/grow fields are overwritten.
The inferred tag is computed by the caller at the exact default_eltype point. -/
-- Source: base/array.jl:833-853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function collect(itr::Generator)
--     isz = IteratorSize(itr.iter)
--     et = @default_eltype(itr)
--     if isa(isz, SizeUnknown)
--         return grow_to!(Vector{et}(), itr)
--     else
--         shp = _similar_shape(itr, isz)
--         y = iterate(itr)
--         if y === nothing
--             return _array_for_inner(et, isz, shp)
--         end
--         v1, st = y
--         dest = _array_for_inner(typeof(v1), isz, shp)
--         # The typeassert gives inference a helping hand on the element type and dimensionality
--         # (work-around for #28382)
--         et′ = et <: Type ? Type : et
--         RT = !(dest isa AbstractArray) ? Any :
--              isconcretetype(et′) ? AbstractArray{et′, ndims(dest)} : AbstractArray{<:et′, ndims(dest)}
--         collect_to_with_first!(dest, v1, itr, st)::RT
--     end
-- end
-- /Source
def findallCollectGenerator {UserError World A Pairs Pair Value Key State Raw Keys Tag B Mem Ref Shape Size : Type}
    (ops : FindallInterfaces (FindallM UserError World)
      A Pairs Pair Value Key State Raw Keys Tag)
    (vectors : FindallVectorRuntime (FindallM UserError World) Key Tag B Mem Ref)
    (dormant : GeneratorCollectOps (FindallM UserError World)
      (FindallGenerator (FindallM UserError World) Pairs Pair Key)
      Key Tag Size Shape State B)
    (tag : Tag) (g : FindallGenerator (FindallM UserError World) Pairs Pair Key) :
    FindallM UserError World B :=
  collectGenerator
    (fun _ => JuliaLean.base.iterators.filterIteratorSize) (fun _ => tag)
    (fun _ => true) (fun tag => findallAllocate vectors tag zero)
    (findallGrowFirst ops vectors)
    (fun g _ => dormant.shape g (dormant.size g))
    (fun g => findallIterate ops g none) vectors.valueType
    (fun tag _ shape => dormant.arrayForInner tag (dormant.size g) shape)
    dormant.isTypeSubtype dormant.typeType dormant.anyType
    (fun _ => true) dormant.isConcrete (fun _ => one)
    dormant.abstractArrayType dormant.collectWithFirst dormant.typeassert g

/-- Generic predicate findall, base/array.jl:2784-2787. Pair construction is
effectful, Filter/Generator construction remains deferred, default_eltype
retains all repeated keys(A) evaluations, and both collectors are actual models.
The same deferred generator is passed through the chosen collection branch.
Runtime/type interfaces are explicit; no callback stands for collect/grow. -/
-- Source: base/array.jl:2784-2787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findall(testf::Function, A)
--     gen = (first(p) for p in pairs(A) if testf(last(p)))
--     @default_eltype(gen) === Union{} ? collect(@default_eltype(keys(A)), gen) : collect(gen)
-- end
-- /Source
def findallPredicate {UserError World A Pairs Pair Value Key State Raw Keys Tag B Mem Ref Shape Size : Type}
    (ops : FindallInterfaces (FindallM UserError World)
      A Pairs Pair Value Key State Raw Keys Tag)
    (vectors : FindallVectorRuntime (FindallM UserError World) Key Tag B Mem Ref)
    (dormant : GeneratorCollectOps (FindallM UserError World)
      (FindallGenerator (FindallM UserError World) Pairs Pair Key)
      Key Tag Size Shape State B)
    (a : A) : FindallM UserError World B := do
  let ps ← ops.pairs a
  let filtered := JuliaLean.base.iterators.sourceMethod576
    (fun p => do ops.test (← ops.pairValue p)) ps
  let gen : FindallGenerator (FindallM UserError World) Pairs Pair Key :=
    ⟨ops.pairKey, filtered⟩
  let tag ← findallDefaultGeneratorType ops gen
  if ops.isBottom tag then
    let keyTag ← findallDefaultEltypeExpression (ops.keys a) ops.keysIsGenerator
      ops.functionField ops.isType ops.inferKeys ops.promoteUnion
    letI := findallGeneratorForIn ops
    collectTyped (fun _ => JuliaLean.base.iterators.filterIteratorSize)
      (fun tag g _ => collectUnknown (findallAllocate vectors tag zero)
        (findallPush vectors) g) keyTag gen
  else
    let inferred ← findallDefaultGeneratorType ops gen
    findallCollectGenerator ops vectors dormant inferred gen

end JuliaLean.base.array.Models1Group14



namespace JuliaLean.base.array.Models1Group14

open JuliaLean JuliaLean.base.array

/-- The existing runtime condition boundary, with every non-Bool result retained as
`none`. This is a projection of a returned Julia value, not Julia's `nothing` value.
Exceptions from evaluating the predicate are carried by `m` before this check.
Julia documentation: doc/src/manual/control-flow.md:180-207. -/
def requireBool [Monad m] [MonadExceptOf Error m] (value : Option Bool) : m Bool :=
  match value with
  | some b => pure b
  | none => throw (.typeError "non-boolean condition")

/-- Effectful scalar predicate search, including the runtime Bool check and actual
fresh-vector literal path. The predicate is a user function at the existing
explicit interface boundary; its implementation is not assumed correct.
Julia source: base/array.jl:2852; documentation: base/array.jl:2733-2783,
2795-2832; scalar keys: base/number.jl:99. -/
-- Source: base/array.jl:2852-2852 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findall(testf::Function, x::Number) = testf(x) ? [1] : Vector{Int}()
-- /Source
def findallNumber [Monad m] [MonadExceptOf Error m]
    (test : Number → m (Option Bool)) (allocate : I → m A)
    (set : A → I → I → m A) (x : Number) : m A := do
  let condition ← test x
  let keep ← requireBool condition
  JuliaLean.base.array.findallBoolDispatch allocate set keep

/-- Scalar membership search preserves membership effects/errors before checking
the condition and allocating the result. `contains` is the existing user-extensible
membership interface, not a replacement implementation of `in` or of a Set.
Julia source: base/array.jl:2853; documentation: base/array.jl:2733-2783,
2795-2832; scalar keys: base/number.jl:99. -/
-- Source: base/array.jl:2853-2853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findall(p::Fix2{typeof(in)}, x::Number) = x in p.x ? [1] : Vector{Int}()
-- /Source
def findallInNumber [Monad m] [MonadExceptOf Error m]
    (contains : Number → Collection → m (Option Bool))
    (allocate : I → m A) (set : A → I → I → m A)
    (collection : Collection) (x : Number) : m A := do
  let condition ← contains x collection
  let keep ← requireBool condition
  JuliaLean.base.array.findallBoolDispatch allocate set keep

/-- The 64-bit target's built-in Int layout. Both result lengths (zero and one)
are constructible and use the existing checked Array allocation implementation. -/
def scalarIntLayout : MemoryLayout :=
  { size := 8, isboxed := false, isunion := false }

/-- Concrete shared-store closure of the scalar public method. The existing
`mutableAllocate` calls `arrayUndef1`/`memoryUndef`; `mutableTypedSet` writes the
allocated vector. Predicate writes survive later errors in `MutationM`.
The inherited allocator represents its shared-empty-memory boundary by a fresh
empty memory record; no property below promises fresh backing memory.
Julia source: base/array.jl:2852. -/
-- Source: base/array.jl:2852-2852 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findall(testf::Function, x::Number) = testf(x) ? [1] : Vector{Int}()
-- /Source
def findallNumberHeap (test : Number → MutationM I (Option Bool))
    (x : Number) : MutationM I Nat :=
  findallNumber test (mutableAllocate (some scalarIntLayout) 0) mutableTypedSet x

/-- Concrete shared-store closure of the membership overload, using the same
existing allocation and assignment models as the predicate overload.
Julia source: base/array.jl:2853. -/
-- Source: base/array.jl:2853-2853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findall(p::Fix2{typeof(in)}, x::Number) = x in p.x ? [1] : Vector{Int}()
-- /Source
def findallInNumberHeap (contains : Number → Collection → MutationM I (Option Bool))
    (collection : Collection) (x : Number) : MutationM I Nat :=
  findallInNumber contains (mutableAllocate (some scalarIntLayout) 0)
    mutableTypedSet collection x

end JuliaLean.base.array.Models1Group14

namespace JuliaLean.base.array.Models1Group14

open JuliaLean JuliaLean.base.array

/-- Existing array storage, allocation, native indexing, and conversion boundaries
used by `indcopy` at base/array.jl:2965-2974. `B` denotes native Vector handles;
`E` denotes Julia values, including heterogeneous index collections. A handle's
length and element type are its stored runtime fields. The conversion operation
includes the source `convert(T,x)::T` assertion and may mutate or throw.

The allocation and setter bodies below are the installed models, rather than
callbacks for a whole comprehension or for `copyto!`. Raw memory/header effects,
layout metadata, element conversion, scalar reads and general slicing remain
at the pre-existing runtime/interface boundary. -/
structure IndcopyVectorRuntime (m : Type → Type) (E Tag B Mem Ref : Type) where
  storage : Storage m B Mem Ref
  elementType : B → Tag
  layout : Tag → Option MemoryLayout
  emptyMemory : Tag → m Mem
  allocateMemory : Tag → Nat → m Mem
  newHeader : Tag → Mem → List I → m B
  readIndex : B → I → m E
  alreadyTyped : B → E → Bool
  convertElement : B → E → m E
  bounds : B → I → m Unit
  memoryrefnew : B → I → Bool → m Ref
  store : Ref → E → Bool → m Unit
  getSlice : E → E → m E

/-- Typed storage used by comprehension copying at base/array.jl:2971-2972.
Calls both installed Array setindex! bodies, preserving conversion before bounds
checking and raw memory storage (base/array.jl:1031-1041). -/
def indcopySet {m : Type → Type} [Monad m]
    {E Tag B Mem Ref : Type} (ops : IndcopyVectorRuntime m E Tag B Mem Ref)
    (dest : B) (i : I) (x : E) : m Unit := do
  let _ ← setindexScalar (ops.alreadyTyped dest) id (ops.convertElement dest)
    (setindexTyped ops.bounds ops.memoryrefnew ops.store) dest x i
  pure ()


end JuliaLean.base.array.Models1Group14

namespace JuliaLean.base.array.Models1Group14

open JuliaLean JuliaLean.base.array

/-- Actual native Vector allocation in `findall(A::AbstractArray{Bool})`,
base/array.jl:2840. The key-type tag and count are observed before calling this
installed `arrayUndef1` body. Layout/type validation, native length checks, raw
memory allocation and header construction retain the existing runtime boundary.
This is not an unconstrained callback for a whole Vector constructor. -/
def boolFindallAllocate {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {K Tag B Mem Ref : Type} (vectors : IndcopyVectorRuntime m K Tag B Mem Ref)
    (keyType : Tag) (n : I) : m B :=
  arrayUndef1 (vectors.layout keyType) (vectors.emptyMemory keyType)
    (vectors.allocateMemory keyType) (vectors.newHeader keyType) n

/-- `findall(A::AbstractArray{Bool})`, base/array.jl:2838-2849, with the
existing count/keys/eltype/pairs interfaces made explicit in source order.
The count result uses the existing native-Int count boundary. No correctness
law about count, keys, key-type discovery or custom iteration is assumed, and
these operations are not claimed to be closed callee implementations.

After counting, the actual keys object supplies the output element-type tag;
native allocation precedes construction of the live pairs iterator. Every true
pair is converted and stored through the installed Array setter bodies before
the wrapping native counter is advanced. Neither pass snapshots the values for
the other: effects and aliases remain in the shared monad. If live values change
after counting, the source's underfilled output or store error is preserved;
the model does not resize or repair it. -/
-- Source: base/array.jl:2838-2849 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findall(A::AbstractArray{Bool})
--     n = count(A)
--     I = Vector{eltype(keys(A))}(undef, n)
--     cnt = 1
--     for (i,a) in pairs(A)
--         if a
--             I[cnt] = i
--             cnt += 1
--         end
--     end
--     I
-- end
-- /Source
def findallBoolArray {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Keys Tag Pairs K B Mem Ref : Type} [ForIn m Pairs (K × Bool)]
    (count : A → m I) (keys : A → m Keys) (keyType : Keys → m Tag)
    (pairs : A → m Pairs) (vectors : IndcopyVectorRuntime m K Tag B Mem Ref)
    (a : A) : m B := do
  let n ← count a
  let ks ← keys a
  let t ← keyType ks
  let indices ← boolFindallAllocate vectors t n
  let mut cnt := one
  let ps ← pairs a
  for (i, value) in ps do
    if value then
      indcopySet vectors indices cnt i
      cnt := cnt + one
  pure indices

end JuliaLean.base.array.Models1Group14

namespace JuliaLean.base.array.Models1Group14

open JuliaLean

/-- Generic pair search now observes `pairs(A)` in the effectful runtime before
entering the existing search loop. The loop itself is reused unchanged, including
predicate effects and early return. `pairs`, `ForIn`, and the checked Boolean
predicate are existing collection/user-function boundaries, not invented callee
implementations. Julia source: base/array.jl:2518-2523. -/
-- Source: base/array.jl:2518-2523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findfirst(testf::Function, A)
--     for (i, a) in pairs(A)
--         testf(a) && return i
--     end
--     return nothing
-- end
-- /Source
def findfirst [Monad m] [ForIn m Pairs (K × E)]
    (pairs : A → m Pairs) (test : E → m Bool) (a : A) : m (Option K) := do
  let ps ← pairs a
  JuliaLean.base.array.findfirst test ps

/-- Generic last-search observes pair construction and reverse-iterator
construction, in that order and exactly once, before reusing the existing loop.
The pure function passed to that loop only returns the already computed reverse
iterator; no missing reverse implementation or correctness law is substituted.
Julia source: base/array.jl:2711-2716. -/
-- Source: base/array.jl:2711-2716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findlast(testf::Function, A)
--     for (i, a) in Iterators.reverse(pairs(A))
--         testf(a) && return i
--     end
--     return nothing
-- end
-- /Source
def findlast [Monad m] [ForIn m Reversed (K × E)]
    (pairs : A → m Pairs) (reversePairs : Pairs → m Reversed)
    (test : E → m Bool) (a : A) : m (Option K) := do
  let ps ← pairs a
  let reversed ← reversePairs ps
  JuliaLean.base.array.findlast (fun (_ : Unit) => reversed) test ()


end JuliaLean.base.array.Models1Group14

namespace JuliaLean.base.array.Completion
open JuliaLean JuliaLean.base.array

-- Source: base/array.jl:368-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(A::AbstractArray{T}, x) where T
--     @inline
--     xT = x isa T ? x : convert(T, x)::T
--     return _fill!(A, xT)
-- end
-- /Source
def fillChecked [Monad m] [MonadExceptOf Error m]
    (cast : V → Option E) (convert : V → m V)
    (fill : A → E → m A) (a : A) (x : V) : m A := do
  let value ← match cast x with
    | some value => pure value
    | none => do
      let converted ← convert x
      match cast converted with
      | some value => pure value
      | none => throw (.typeError "fill!")
  fill a value

-- Source: base/array.jl:657-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, a::AbstractArray) where {T<:Array} = a isa T ? a : T(a)::T
-- /Source
def convertChecked [Monad m] [MonadExceptOf Error m]
    (cast : V → Option A) (constructor : V → m V) (a : V) : m A := do
  match cast a with
  | some value => pure value
  | none =>
    let result ← constructor a
    match cast result with
    | some value => pure value
    | none => throw (.typeError "convert(Array)")

-- Source: base/array.jl:700-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _similar_shape(itr, ::HasLength) = length(itr)::Integer
-- /Source
def similarShapeLength [Monad m] [MonadExceptOf Error m]
    (length : X → m V) (integer : V → Option Z) (itr : X) : m Z := do
  let value ← length itr
  match integer value with
  | some n => pure n
  | none => throw (.typeError "_similar_shape")

-- Source: base/array.jl:701-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _similar_shape(itr, ::HasShape) = axes(itr)
-- /Source
def similarShapeAxes [Monad m] (axes : X → m Axes) (itr : X) : m Axes := axes itr

-- Source: base/array.jl:2399-2399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findnext(A, start) = findnext(identity, A, start)
-- /Source
def findnextIdentity [Monad m] (search : (E → E) → A → Start → m R)
    (a : A) (start : Start) : m R := search id a start

-- Source: base/array.jl:2436-2436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findfirst(A) = findfirst(identity, A)
-- /Source
def findfirstIdentity [Monad m] (search : (E → E) → A → m R)
    (a : A) : m R := search id a

-- Source: base/array.jl:2439-2439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findfirst(A::AbstractArray) = findnext(A, first(keys(A)))
-- /Source
def findfirstArrayIdentity [Monad m] (keys : A → m Keys) (endpoint : Keys → m K)
    (search : A → K → m R)
    (a : A) : m R := do
  let ks ← keys a
  let key ← endpoint ks
  search a key

-- Source: base/array.jl:2526-2527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findfirst(testf::Function, A::Union{AbstractArray, AbstractString}) =
--     findnext(testf, A, first(keys(A)))
-- /Source
def findfirstArrayPredicate [Monad m] (keys : A → m Keys) (endpoint : Keys → m K)
    (search : (E → m Bool) → A → K → m R)
    (test : E → m Bool) (a : A) : m R := do
  let ks ← keys a
  let key ← endpoint ks
  search test a key

-- Source: base/array.jl:2586-2586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findprev(A, start) = findprev(identity, A, start)
-- /Source
def findprevIdentity [Monad m] (search : (E → E) → A → Start → m R)
    (a : A) (start : Start) : m R := search id a start

-- Source: base/array.jl:2624-2624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findlast(A) = findlast(identity, A)
-- /Source
def findlastIdentity [Monad m] (search : (E → E) → A → m R)
    (a : A) : m R := search id a

-- Source: base/array.jl:2627-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findlast(A::AbstractArray) = findprev(A, last(keys(A)))
-- /Source
def findlastArrayIdentity [Monad m] (keys : A → m Keys) (endpoint : Keys → m K)
    (search : A → K → m R)
    (a : A) : m R := do
  let ks ← keys a
  let key ← endpoint ks
  search a key

-- Source: base/array.jl:2719-2720 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findlast(testf::Function, A::Union{AbstractArray, AbstractString}) =
--     findprev(testf, A, last(keys(A)))
-- /Source
def findlastArrayPredicate [Monad m] (keys : A → m Keys) (endpoint : Keys → m K)
    (search : (E → m Bool) → A → K → m R)
    (test : E → m Bool) (a : A) : m R := do
  let ks ← keys a
  let key ← endpoint ks
  search test a key

end JuliaLean.base.array.Completion

namespace JuliaLean.base.array.Completion2
open JuliaLean JuliaLean.base.array
abbrev Exec (W A : Type) := JuliaLean.base.iterators.Exec Error W A

-- Source: base/array.jl:684-684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- collect(::Type{T}, itr) where {T} = _collect(T, itr, IteratorSize(itr))
-- /Source
def collectTyped [Monad m] (iteratorSize : X → m Size)
    (collect : T → X → Size → m A) (t : T) (itr : X) : m A := do
  collect t itr (← iteratorSize itr)

-- Source: base/array.jl:716-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _array_for(::Type{T}, itr, isz) where {T} = _array_for_inner(T, isz, _similar_shape(itr, isz))
-- /Source
def arrayFor [Monad m] (shape : X → Size → m Shape)
    (inner : T → Size → Shape → m A) (t : T) (itr : X) (size : Size) : m A := do
  inner t size (← shape itr size)

-- Source: base/array.jl:771-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- collect(itr) = _collect(1:1 #= Array =#, itr, IteratorEltype(itr), IteratorSize(itr))
-- /Source
def collect [Monad m] (eltype : X → m ET) (size : X → m SZ)
    (collect : JuliaLean.base.range.UnitRange I → X → ET → SZ → m A) (itr : X) : m A := do
  let et ← eltype itr
  let sz ← size itr
  collect ⟨one, one⟩ itr et sz

-- Source: base/array.jl:773-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- collect(A::AbstractArray) = _collect_indices(axes(A), A)
-- /Source
def collectArray [Monad m] (axes : A → m Axes)
    (collect : Axes → A → m B) (a : A) : m B := do
  collect (← axes a) a

-- Source: base/array.jl:775-775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- collect_similar(cont, itr) = _collect(cont, itr, IteratorEltype(itr), IteratorSize(itr))
-- /Source
def collectSimilar [Monad m] (eltype : X → m ET) (size : X → m SZ)
    (collect : C → X → ET → SZ → m A) (c : C) (itr : X) : m A := do
  let et ← eltype itr
  let sz ← size itr
  collect c itr et sz

inductive SizedShape (Z Axes : Type) where
  | length (n : Z)
  | axes (axs : Axes)

-- Source: base/array.jl:777-778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _collect(cont, itr, ::HasEltype, isz::Union{HasLength,HasShape}) =
--     copyto!(_similar_for(cont, eltype(itr), itr, isz, _similar_shape(itr, isz)), itr)
-- /Source
def collectKnownSized [Monad m] [MonadExceptOf Error m]
    (isLength : Size → Bool) (size : Size) (length : X → m V) (integer : V → Option Z)
    (axes : X → m Axes) (eltype : X → m T)
    (similar : C → T → X → Size → SizedShape Z Axes → m A)
    (copy : A → X → m A) (cont : C) (itr : X) : m A := do
  let ty ← eltype itr
  let shape ← if isLength size then do
      let value ← length itr
      match integer value with
      | none => throw (.typeError "_similar_shape")
      | some n => pure (.length n)
    else do pure (.axes (← axes itr))
  copy (← similar cont ty itr size shape) itr

-- Source: base/array.jl:780-786 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _collect(cont, itr, ::HasEltype, isz::SizeUnknown)
--     a = _similar_for(cont, eltype(itr), itr, isz, nothing)
--     for x in itr
--         push!(a,x)
--     end
--     return a
-- end
-- /Source
def collectKnownUnknown [Monad m] [ForIn m X E]
    (eltype : X → m T) (similar : C → T → X → m A)
    (push : A → E → m Unit) (cont : C) (itr : X) : m A := do
  let a ← similar cont (← eltype itr) itr
  for x in itr do push a x
  pure a

-- Source: base/array.jl:881-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function collect_to_with_first!(dest, v1, itr, st)
--     push!(dest, v1)
--     return grow_to!(dest, itr, st)
-- end
-- /Source
def collectWithFirst [Monad m] (push : A → E → m Unit)
    (grow : A → X → St → m A) (dest : A) (value : E) (itr : X) (st : St) : m A := do
  push dest value
  grow dest itr st

-- Source: base/array.jl:914-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function grow_to!(dest, itr)
--     y = iterate(itr)
--     y === nothing && return dest
--     dest2 = empty(dest, typeof(y[1]))
--     push!(dest2, y[1])
--     grow_to!(dest2, itr, y[2])
-- end
-- /Source
def growFirst [Monad m] (iterate : X → m (Option (E × St)))
    (typeof : E → T) (empty : A → T → m A) (push : A → E → m Unit)
    (grow : A → X → St → m A) (dest : A) (itr : X) : m A := do
  match ← iterate itr with
  | none => pure dest
  | some (value, st) =>
    let dest2 ← empty dest (typeof value)
    push dest2 value
    grow dest2 itr st

-- Source: base/array.jl:1431-1431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- push!(a::AbstractVector, iter...) = append!(a, iter)
-- /Source
def pushMany [Monad m] (append : A → List X → m R)
    (a : A) (values : List X) : m R := append a values

-- Source: base/array.jl:1496-1496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- pushfirst!(a::AbstractVector, iter...) = prepend!(a, iter)
-- /Source
def pushfirstMany [Monad m] (prepend : A → List X → m R)
    (a : A) (values : List X) : m R := prepend a values

-- Source: base/array.jl:3172-3178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _grow!(pred!, v::AbstractVector, itrs)
--     filter!(pred!, v) # uniquify v
--     for itr in itrs
--         mapfilter(pred!, push!, itr, v)
--     end
--     return v
-- end
-- /Source
def grow [Monad m] [ForIn m Itrs X]
    (filter : (E → m Bool) → A → m Unit)
    (push : A → E → m Unit)
    (mapfilter : (E → m Bool) → (A → E → m Unit) → X → A → m Unit)
    (pred : E → m Bool) (v : A) (itrs : Itrs) : m A := do
  filter pred v
  for itr in itrs do mapfilter pred push itr v
  pure v

-- Source: base/array.jl:3216-3216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- intersect(r::AbstractRange, v::AbstractVector) = intersect(v, r)
-- /Source
def intersectRangeVector [Monad m] (intersect : A → R → m B)
    (range : R) (vector : A) : m B := intersect vector range

-- Source: base/array.jl:402-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _take!(dst::Array{T,N}, src::Array{T,N}) where {T,N}
--     if getfield(dst, :ref) !== getfield(src, :ref)
--         setfield!(dst, :ref, getfield(src, :ref))
--     end
--     if getfield(dst, :size) !== getfield(src, :size)
--         setfield!(dst, :size, getfield(src, :size))
--     end
--     return dst
-- end
-- /Source
def takeFields {Ref Dims : Type} [DecidableEq Ref] [DecidableEq Dims]
    (dst src : Nat) : StateM (Nat → Ref × Dims) Nat :=
  takeBang (fun a heap => ((heap a).1, heap)) (fun a b => decide (a = b))
    (fun a ref => modify (fun heap i => if i = a then (ref, (heap i).2) else heap i))
    (fun a heap => ((heap a).2, heap)) (fun a b => decide (a = b))
    (fun a dims => modify (fun heap i => if i = a then ((heap i).1, dims) else heap i))
    dst src

-- Source: base/array.jl:483-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- to_dim(d::OneTo) = last(d)
-- /Source
def toDimOneTo {T : Type} [JuliaLean.base.range.JConvert T T]
    (d : JuliaLean.base.range.OneTo T) : JuliaLean.base.range.JlX T :=
  letI : JuliaLean.base.range.JEltype (JuliaLean.base.range.OneTo T) T := ⟨⟩
  letI : JuliaLean.base.range.JFieldStop (JuliaLean.base.range.OneTo T) T := ⟨fun r => r.stop⟩
  JuliaLean.base.range.last_OrdinalRange d

-- Source: base/array.jl:895-912 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function collect_to!(dest::AbstractArray{T}, itr, offs, st) where T
--     # collect to dest array, checking the type of each result. if a result does not
--     # match, widen the result type and re-dispatch.
--     i = offs
--     while true
--         y = iterate(itr, st)
--         y === nothing && break
--         el, st = y
--         if el isa T
--             @inbounds dest[i] = el
--             i += 1
--         else
--             new = setindex_widen_up_to(dest, el, i)
--             return collect_to!(new, itr, i+1, st)
--         end
--     end
--     return dest
-- end
-- /Source
def collectToLoop {W A X E St Index : Type}
    (iterate : X → St → Exec W (Option (E × St))) (isElement : E → Bool)
    (set : A → E → Index → Exec W Unit) (increment : Index → Exec W Index)
    (widen : A → E → Index → Exec W A)
    (redispatch : A → X → Index → St → Exec W A)
    (dest : A) (itr : X) (index : Index) (st : St) : Exec W A := fun world =>
  match iterate itr st world with
  | none => none
  | some (.error error, after) => some (.error error, after)
  | some (.ok none, after) => some (.ok dest, after)
  | some (.ok (some (value, next)), after) =>
    if isElement value then
      match set dest value index after with
      | none => none
      | some (.error error, final) => some (.error error, final)
      | some (.ok (), final) =>
        match increment index final with
        | none => none
        | some (.error error, final) => some (.error error, final)
        | some (.ok index, final) =>
          collectToLoop iterate isElement set increment widen redispatch dest itr index next final
    else
      match widen dest value index after with
      | none => none
      | some (.error error, final) => some (.error error, final)
      | some (.ok new, final) =>
        match increment index final with
        | none => none
        | some (.error error, final) => some (.error error, final)
        | some (.ok index, final) => redispatch new itr index next final
partial_fixpoint

-- Source: base/array.jl:935-949 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function grow_to!(dest, itr, st)
--     T = eltype(dest)
--     y = iterate(itr, st)
--     while y !== nothing
--         el, st = y
--         if el isa T
--             push!(dest, el)
--         else
--             new = push_widen(dest, el)
--             return grow_to!(new, itr, st)
--         end
--         y = iterate(itr, st)
--     end
--     return dest
-- end
-- /Source
def growToLoop {W A X E St T : Type}
    (iterate : X → St → Exec W (Option (E × St))) (isElement : T → E → Bool)
    (push : A → E → Exec W Unit) (widen : A → E → Exec W A)
    (redispatch : A → X → St → Exec W A)
    (t : T) (dest : A) (itr : X) (st : St) : Exec W A := fun world =>
  match iterate itr st world with
  | none => none
  | some (.error error, after) => some (.error error, after)
  | some (.ok none, after) => some (.ok dest, after)
  | some (.ok (some (value, next)), after) =>
    if isElement t value then
      match push dest value after with
      | none => none
      | some (.error error, final) => some (.error error, final)
      | some (.ok (), final) =>
        growToLoop iterate isElement push widen redispatch t dest itr next final
    else
      match widen dest value after with
      | none => none
      | some (.error error, final) => some (.error error, final)
      | some (.ok new, final) => redispatch new itr next final
partial_fixpoint

inductive RawExpr (Atom : Type) where
  | atom (value : Atom)
  | globalRef (name : String)
  | expr (head : String) (args : List (RawExpr Atom))
  deriving Repr

-- Source: base/array.jl:135-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _safeindex(ex)
--     isa(ex, Expr) || return ex
--     if ex.head === :(=)
--         lhs = ex.args[1]
--         if isa(lhs, Expr) && lhs.head === :ref # xs[i] = x
--             rhs = ex.args[2]
--             xs = lhs.args[1]
--             args = Vector{Any}(undef, length(lhs.args)-1)
--             for i = 2:length(lhs.args)
--                 args[i-1] = _safeindex(lhs.args[i])
--             end
--             return Expr(:call, GlobalRef(@__MODULE__, :__safe_setindex!), xs, _safeindex(rhs), args...)
--         end
--     elseif ex.head === :ref # xs[i]
--         return Expr(:call, GlobalRef(@__MODULE__, :__safe_getindex), ex.args...)
--     end
--     args = Vector{Any}(undef, length(ex.args))
--     for i = 1:length(ex.args)
--         args[i] = _safeindex(ex.args[i])
--     end
--     return Expr(ex.head, args...)
-- end
-- /Source
def safeindexRaw : RawExpr Atom → Except Error (RawExpr Atom)
  | .atom x => .ok (.atom x)
  | .globalRef name => .ok (.globalRef name)
  | .expr "=" [] => .error .bounds
  | .expr "=" (.expr "ref" (xs :: indices) :: rhs :: _) => do
    let args ← indices.mapM safeindexRaw
    let value ← safeindexRaw rhs
    pure (.expr "call" (.globalRef "__safe_setindex!" :: xs :: value :: args))
  | .expr "=" (.expr "ref" _ :: _) => .error .bounds
  | .expr "ref" args => .ok (.expr "call" (.globalRef "__safe_getindex" :: args))
  | .expr head args => do
    pure (.expr head (← args.mapM safeindexRaw))
termination_by e => sizeOf e

-- Source: base/array.jl:132-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _safeindex(ex)
--     return esc(_safeindex(ex))
-- end
-- /Source
def safeindexMacro (e : RawExpr Atom) : Except Error (RawExpr Atom) :=
  (safeindexRaw e).map (fun rewritten => .expr "escape" [rewritten])

-- Source: base/array.jl:935-949 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function grow_to!(dest, itr, st)
--     T = eltype(dest)
--     y = iterate(itr, st)
--     while y !== nothing
--         el, st = y
--         if el isa T
--             push!(dest, el)
--         else
--             new = push_widen(dest, el)
--             return grow_to!(new, itr, st)
--         end
--         y = iterate(itr, st)
--     end
--     return dest
-- end
-- /Source
def growTo {W A X E St T : Type}
    (eltype : A → Exec W T)
    (iterate : X → St → Exec W (Option (E × St))) (isElement : T → E → Bool)
    (push : A → E → Exec W Unit) (widen : A → E → Exec W A)
    (redispatch : A → X → St → Exec W A)
    (dest : A) (itr : X) (st : St) : Exec W A := do
  let t ← eltype dest
  growToLoop iterate isElement push widen redispatch t dest itr st

end JuliaLean.base.array.Completion2

namespace JuliaLean.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

-- Source: base/array.jl:183-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function vect(X...)
--     T = promote_typeof(X...)
--     return T[X...]
-- end
-- /Source
def vectPromoted [Monad m] (promoteTypeof : List E → m T)
    (literal : T → List E → m A) (xs : List E) : m A := do
  literal (← promoteTypeof xs) xs

-- Source: base/array.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _copyto2arg!(dest, src) = copyto!(dest, firstindex(dest), src, firstindex(src), length(src))
-- /Source
def copyto2arg [Monad m] (firstDest : D → m DI) (firstSrc : S → m SI)
    (length : S → m Count) (copy : D → DI → S → SI → Count → m R)
    (dest : D) (src : S) : m R := do
  let di ← firstDest dest
  let si ← firstSrc src
  let n ← length src
  copy dest di src si n

-- Source: base/array.jl:583-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fill(v, dims::DimOrInd...) = fill(v, dims)
-- /Source
def fillVarargs [Monad m] (fill : E → List D → m A) (v : E) (dims : List D) : m A :=
  fill v dims

inductive Dim (T : Type) where
  | integer (value : T)
  | oneTo (axis : JuliaLean.base.range.OneTo T)

-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
-- The effectful conversion is selected by the unspecified Integer element type.
def oneToEndpoint [Monad m] (convertSame : T → m T) (r : JuliaLean.base.range.OneTo T) : m T :=
  convertSame r.stop

-- Source: base/array.jl:482-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- to_dim(d::Integer) = d
-- to_dim(d::OneTo) = last(d)
-- /Source
def dimValue [Monad m] (convertSame : T → m T) : Dim T → m T
  | .integer value => pure (toDimInteger value)
  | .oneTo axis => oneToEndpoint convertSame axis

-- Source: base/array.jl:584-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fill(v, dims::NTuple{N, Union{Integer, OneTo}}) where {N} = fill(v, map(to_dim, dims))
-- /Source
def fillMixedDims [Monad m] (convertSame : T → m T)
    (fill : E → List T → m A) (value : E) (dims : List (Dim T)) : m A := do
  fill value (← dims.mapM (dimValue convertSame))

-- Source: base/array.jl:633-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $fname(dims::DimOrInd...) = $fname(dims)
-- /Source
def constantVarargs [Monad m] (constant : List D → m A) (dims : List D) : m A :=
  constant dims

-- Source: base/array.jl:634-634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $fname(::Type{T}, dims::DimOrInd...) where {T} = $fname(T, dims)
-- /Source
def constantTypedVarargs [Monad m] (constant : T → List D → m A)
    (t : T) (dims : List D) : m A := constant t dims

inductive TypeArgument (Other : Type) where
  | float64
  | other (value : Other)

-- Source: base/array.jl:635-635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $fname(dims::Tuple{Vararg{DimOrInd}}) = $fname(Float64, dims)
-- /Source
def constantDefaultType [Monad m] (constant : TypeArgument Other → D → m A)
    (dims : D) : m A := constant .float64 dims

-- Source: base/array.jl:636-636 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $fname(::Type{T}, dims::NTuple{N, Union{Integer, OneTo}}) where {T,N} = $fname(T, map(to_dim, dims))
-- /Source
def constantMixedDims [Monad m] (convertSame : Z → m Z)
    (constant : T → List Z → m A) (t : T) (dims : List (Dim Z)) : m A := do
  constant t (← dims.mapM (dimValue convertSame))

-- Source: base/array.jl:922-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function push_widen(dest, el)
--     @inline
--     new = sizehint!(empty(dest, promote_typejoin(eltype(dest), typeof(el))), length(dest))
--     if new isa AbstractSet
--         # TODO: merge back these two branches when copy! is re-enabled for sets/vectors
--         union!(new, dest)
--     else
--         append!(new, dest)
--     end
--     push!(new, el)
--     return new
-- end
-- /Source
def pushWiden [Monad m] (eltype : A → m T) (typeof : E → T)
    (join : T → T → m T) (empty : A → T → m A) (length : A → m N)
    (sizehint : A → N → m A) (isSet : A → Bool)
    (union append : A → A → m Unit) (push : A → E → m Unit)
    (dest : A) (el : E) : m A := do
  let oldType ← eltype dest
  let joined ← join oldType (typeof el)
  let fresh ← empty dest joined
  let n ← length dest
  let new ← sizehint fresh n
  if isSet new then union new dest else append new dest
  push new el
  pure new

-- Source: base/array.jl:1647-1652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Core.kwcall(kwargs::NamedTuple{names}, ::typeof(sizehint!), a, sz) where names
--     get(kwargs, :first, false)::Bool
--     get(kwargs, :shrink, true)::Bool
--     isempty(diff_names(names, (:first, :shrink))) || kwerr(kwargs, sizehint!, a, sz)
--     sizehint!(a, sz)
-- end
-- /Source
def sizehintKwcall [Monad m] [MonadExceptOf Error m]
    (names : List String) (field : String → Option V) (boolCast : V → Option Bool)
    (sizehint : A → Z → m R) (a : A) (sz : Z) : m R := do
  match field "first" with
  | none => pure ()
  | some value =>
    match boolCast value with
    | some _ => pure ()
    | none => throw (.typeError "sizehint!:first")
  match field "shrink" with
  | none => pure ()
  | some value =>
    match boolCast value with
    | some _ => pure ()
    | none => throw (.typeError "sizehint!:shrink")
  if names.any (fun name => name != "first" && name != "shrink") then
    throw (.method "kwcall(sizehint!)")
  sizehint a sz

section NativeGrowth
variable {State T V D N Mod P Sym Ref Z X : Type}
variable (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
  (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
  (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
  (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)

-- Source: base/array.jl:1151-1169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _growbeg!(a::Vector, delta::Integer)
--     @_noub_meta
--     delta = Int(delta)
--     delta == 0 && return # avoid attempting to index off the end
--     delta >= 0 || throw(ArgumentError("grow requires delta >= 0"))
--     ref = a.ref
--     len = length(a)
--     offset = memoryrefoffset(ref)
--     newlen = checked_add(len, delta)
--     # if offset is far enough advanced to fit data in existing memory without copying
--     if delta <= offset - 1
--         setfield!(a, :ref, @inbounds memoryref(ref, 1 - delta))
--         setfield!(a, :size, (newlen,))
--     else
--         @noinline _growbeg_internal!(a, delta, len)
--         setfield!(a, :size, (newlen,))
--     end
--     return
-- end
-- /Source
def growbeg (toInt : Z → NativeGrowthM State T I) (a : Nat) (delta : Z) :
    NativeGrowthM State T Unit :=
  JuliaLean.base.array.growbeg
    (nativeGrowthStorage layout elementType native ccall allocation access references) toInt
    (fun a d n => do
      let _ ← nativeGrowbegInternal layout elementType native ccall allocation access references a d n
      pure ()) a delta

-- Source: base/array.jl:1212-1223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _growend!(a::Vector, delta::Integer)
--     @_noub_meta
--     delta = Int(delta)
--     delta >= 0 || throw(ArgumentError("grow requires delta >= 0"))
--     ref = a.ref
--     len = length(a)
--     if length(ref.mem) - (memoryrefoffset(ref) - 1) - len < delta
--         @noinline _growend_internal!(a, delta, len)
--     end
--     setfield!(a, :size, (len + delta,))
--     return
-- end
-- /Source
def growend (toInt : Z → NativeGrowthM State T I) (a : Nat) (delta : Z) :
    NativeGrowthM State T Unit :=
  JuliaLean.base.array.growend
    (nativeGrowthStorage layout elementType native ccall allocation access references) toInt
    (nativeGrowendInternal layout elementType native ccall allocation access references) a delta

-- Source: base/array.jl:1273-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _deletebeg!(a::Vector, delta::Integer)
--     delta = Int(delta)
--     len = length(a)
--     # See comment in _deleteend!
--     if unsigned(delta) > unsigned(len)
--         throw(ArgumentError("_deletebeg! requires delta in 0:length(a)"))
--     end
--     for i in 1:delta
--         @inbounds unsetindex!(a, i)
--     end
--     newlen = len - delta
--     setfield!(a, :size, (newlen,))
--     if newlen != 0 # if newlen==0 we could accidentally index past the memory
--         newref = @inbounds memoryref(a.ref, delta + 1)
--         setfield!(a, :ref, newref)
--     end
--     return
-- end
-- /Source
def deletebeg (toInt : Z → NativeGrowthM State T I) (a : Nat) (delta : Z) :
    NativeGrowthM State T Unit :=
  JuliaLean.base.array.deletebeg
    (nativeGrowthStorage layout elementType native ccall allocation access references) toInt a delta

-- Source: base/array.jl:1291-1306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _deleteend!(a::Vector, delta::Integer)
--     delta = Int(delta)
--     len = length(a)
--     # Do the comparison unsigned, to so the compiler knows `len` cannot be negative.
--     # This works because if delta is negative, it will overflow and still trigger.
--     # This enables the compiler to skip the check sometimes.
--     if unsigned(delta) > unsigned(len)
--         throw(ArgumentError("_deleteend! requires delta in 0:length(a)"))
--     end
--     newlen = len - delta
--     for i in newlen+1:len
--         @inbounds unsetindex!(a, i)
--     end
--     setfield!(a, :size, (newlen,))
--     return
-- end
-- /Source
def deleteend (toInt : Z → NativeGrowthM State T I) (a : Nat) (delta : Z) :
    NativeGrowthM State T Unit :=
  JuliaLean.base.array.deleteend
    (nativeGrowthStorage layout elementType native ccall allocation access references) toInt a delta

-- Source: base/array.jl:208-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsetindex!(A::Array, i::Integer) = unsetindex!(A, to_index(i))
-- /Source
def unsetInteger (toIndex : Z → NativeGrowthM State T I) (a : Nat) (i : Z) :
    NativeGrowthM State T Nat := do
  let index ← toIndex i
  (nativeGrowthStorage layout elementType native ccall allocation access references).unsetArray a index
  pure a

-- Source: base/array.jl:1059-1060 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- __safe_setindex!(A::Vector{T}, x,    i::Int) where {T} = (@inline;
--     __safe_setindex!(A, convert(T, x)::T, i))
-- /Source
def safeSetindexConvert (convert : X → NativeGrowthM State T X) (cast : X → Option T)
    (a : Nat) (x : X) (i : I) : NativeGrowthM State T Nat := do
  let converted ← convert x
  let value ← match cast converted with
    | none => throwThe Error (.typeError "__safe_setindex!")
    | some value => pure value
  safeSetindex1057
    (fun handle index _ => do
      let ref ← nativeGrowthReadRef handle
      nativeGrowthShiftRef references false ref index)
    (fun ref value checked => access.memoryrefSet ref value .notAtomic checked) a value i

end NativeGrowth

-- Source: base/array.jl:259-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_copyto!(dest::Ptr{T}, src::Ptr{T}, n) where T
--     # Do not use this to copy data between pointer arrays.
--     # It can't be made safe no matter how carefully you checked.
--     memmove(dest, src, n * aligned_sizeof(T))
--     return dest
-- end
-- /Source
def unsafeCopyPointer {State T V D N Mod P Sym Ref Count Bytes : Type}
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (multiply : Count → I → NativeCopyM (NativeCopyWorld State) Bytes)
    (isInteger : Bytes → Bool) (toCsize : Bytes → NativeCopyM (NativeCopyWorld State) (JInt .u64))
    (ccall : NativeMemmove) (dest src : JuliaLean.base.pointer.Ptr T) (n : Count) :
    NativeCopyM (NativeCopyWorld State) (JuliaLean.base.pointer.Ptr T) := do
  let stride ← nativeCopyLift (elsizeArrayRuntime layout elementType)
  let bytes ← multiply n stride
  if !isInteger bytes then throwThe Error (.method "memmove")
  let count ← toCsize bytes
  let world ← nativeCopyLift JuliaLean.base.io.getWorld
  let result := ccall world.bytes (JuliaLean.base.pointer.convertPtrType dest)
    (JuliaLean.base.pointer.convertPtrType src) count
  nativeCopyLift (JuliaLean.base.io.setWorld { world with bytes := result.1 })
  pure dest

abbrev Exec (W A : Type) := JuliaLean.base.iterators.Exec Error W A

def boolValue (value : Option Bool) : Exec W Bool :=
  match value with
  | some value => pure value
  | none => JuliaLean.base.iterators.fail (.typeError "search condition")

-- Source: base/array.jl:2470-2481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findnext(testf::Function, A, start)
--     i = oftype(first(keys(A)), start)
--     l = last(keys(A))
--     i > l && return nothing
--     while true
--         testf(A[i]) && return i
--         i == l && break
--         # nextind(A, l) can throw/overflow
--         i = nextind(A, i)
--     end
--     return nothing
-- end
-- /Source
def findnextLoop {W A K E : Type}
    (get : A → K → Exec W E) (test : E → Exec W (Option Bool))
    (equal : K → K → Exec W (Option Bool)) (nextind : A → K → Exec W K)
    (a : A) (i last : K) : Exec W (Option K) := fun world =>
  match ((do
    let value ← get a i
    let matched ← boolValue (← test value)
    if matched then pure (.inl (some i))
    else if ← boolValue (← equal i last) then pure (.inl none)
    else pure (.inr (← nextind a i))) : Exec W (Sum (Option K) K)) world with
  | none => none
  | some (.error error, after) => some (.error error, after)
  | some (.ok (.inl result), after) => some (.ok result, after)
  | some (.ok (.inr key), after) => findnextLoop get test equal nextind a key last after
partial_fixpoint

-- Source: base/array.jl:2470-2481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findnext(testf::Function, A, start)
--     i = oftype(first(keys(A)), start)
--     l = last(keys(A))
--     i > l && return nothing
--     while true
--         testf(A[i]) && return i
--         i == l && break
--         # nextind(A, l) can throw/overflow
--         i = nextind(A, i)
--     end
--     return nothing
-- end
-- /Source
def findnext {W A Keys K Start E : Type}
    (keys : A → Exec W Keys) (first last : Keys → Exec W K)
    (oftype : K → Start → Exec W K) (outside : K → K → Exec W (Option Bool))
    (get : A → K → Exec W E) (test : E → Exec W (Option Bool))
    (equal : K → K → Exec W (Option Bool)) (nextind : A → K → Exec W K)
    (a : A) (start : Start) : Exec W (Option K) := do
  let i ← oftype (← first (← keys a)) start
  let last ← last (← keys a)
  if ← boolValue (← outside i last) then pure none
  else findnextLoop get test equal nextind a i last

-- Source: base/array.jl:2666-2677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findprev(testf::Function, A, start)
--     f = first(keys(A))
--     i = oftype(f, start)
--     i < f && return nothing
--     while true
--         testf(A[i]) && return i
--         i == f && break
--         # prevind(A, f) can throw/underflow
--         i = prevind(A, i)
--     end
--     return nothing
-- end
-- /Source
def findprevLoop {W A K E : Type}
    (get : A → K → Exec W E) (test : E → Exec W (Option Bool))
    (equal : K → K → Exec W (Option Bool)) (prevind : A → K → Exec W K)
    (a : A) (i last : K) : Exec W (Option K) := fun world =>
  match ((do
    let value ← get a i
    let matched ← boolValue (← test value)
    if matched then pure (.inl (some i))
    else if ← boolValue (← equal i last) then pure (.inl none)
    else pure (.inr (← prevind a i))) : Exec W (Sum (Option K) K)) world with
  | none => none
  | some (.error error, after) => some (.error error, after)
  | some (.ok (.inl result), after) => some (.ok result, after)
  | some (.ok (.inr key), after) => findprevLoop get test equal prevind a key last after
partial_fixpoint

-- Source: base/array.jl:2666-2677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findprev(testf::Function, A, start)
--     f = first(keys(A))
--     i = oftype(f, start)
--     i < f && return nothing
--     while true
--         testf(A[i]) && return i
--         i == f && break
--         # prevind(A, f) can throw/underflow
--         i = prevind(A, i)
--     end
--     return nothing
-- end
-- /Source
def findprev {W A Keys K Start E : Type}
    (keys : A → Exec W Keys) (first : Keys → Exec W K)
    (oftype : K → Start → Exec W K) (outside : K → K → Exec W (Option Bool))
    (get : A → K → Exec W E) (test : E → Exec W (Option Bool))
    (equal : K → K → Exec W (Option Bool)) (prevind : A → K → Exec W K)
    (a : A) (start : Start) : Exec W (Option K) := do
  let firstKey ← first (← keys a)
  let i ← oftype firstKey start
  if ← boolValue (← outside i firstKey) then pure none
  else findprevLoop get test equal prevind a i firstKey

-- Source: base/array.jl:2312-2328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function reverse!(v::AbstractVector, start::Integer, stop::Integer=lastindex(v))
--     s, n = Int(start), Int(stop)
--     if n > s # non-empty and non-trivial
--         liv = LinearIndices(v)
--         if !(first(liv) ≤ s ≤ last(liv))
--             throw(BoundsError(v, s))
--         elseif !(first(liv) ≤ n ≤ last(liv))
--             throw(BoundsError(v, n))
--         end
--         r = n
--         @inbounds for i in s:midpoint(s, n-1)
--             v[i], v[r] = v[r], v[i]
--             r -= 1
--         end
--     end
--     return v
-- end
-- /Source
def reverseBang [Monad m] [MonadExceptOf Error m]
    (toStart : Start → m I) (toStop : Stop → m I)
    (linear : A → m Linear) (first last : Linear → m Bound)
    (lower : Bound → I → m (Option Bool)) (upper : I → Bound → m (Option Bool))
    (get : A → I → m E) (set : A → E → I → m Unit)
    (a : A) (start : Start) (stop : Stop) : m A := do
  let s ← toStart start
  let n ← toStop stop
  if n > s then
    let indices ← linear a
    let startOK ← do
      if !(← Models1Group14.requireBool (← lower (← first indices) s)) then pure false
      else Models1Group14.requireBool (← upper s (← last indices))
    if !startOK then throw .bounds
    let stopOK ← do
      if !(← Models1Group14.requireBool (← lower (← first indices) n)) then pure false
      else Models1Group14.requireBool (← upper n (← last indices))
    if !stopOK then throw .bounds
    let midpoint := JuliaLean.base.array.midpoint JuliaLean.base.int.add
      JuliaLean.base.int.sub JuliaLean.base.int.lshr_BitInteger_BitUnsigned s (n - one)
    let mut r := n
    for i in intRange s midpoint do
      let right ← get a r
      let left ← get a i
      set a right i
      set a left r
      r := r - one
  pure a

end JuliaLean.base.array.Completion3

namespace JuliaLean.base.array.Completion4
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

-- Source: base/array.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- asize_from(a::Array, n) = n > ndims(a) ? () : (size(a,n), asize_from(a, n+1)...)
-- /Source
def asizeFrom [Monad m] [MonadExceptOf Error m]
    [MonadExceptOf JuliaLean.base.ntuple.NtupleError m]
    (rank : I) (greater : Z → I → m (Option Bool)) (toInt : Z → m I)
    (add : I → Z → m SumIndex) (subtractOne : SumIndex → m Index)
    (size : A → Index → m Extent) (a : A) (n : Z) : m (List Extent) := do
  if ← Models1Group14.requireBool (← greater n rank) then return []
  let count := rank - (← toInt n) + one
  JuliaLean.base.ntuple.ntupleInt
    (fun i => do size a (← subtractOne (← add i n))) count
    (fun count => pure (ULift.up (intRange one count)))

-- Source: base/array.jl:586-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fill(v, dims::NTuple{N, DimOrInd}) where {N} = (a=similar(Array{typeof(v),N}, dims); fill!(a, v); a)
-- /Source
def fillAxes [Monad m] (similar : Dims → m A) (fill : A → E → m R)
    (value : E) (dims : Dims) : m A := do
  let a ← similar dims
  let _ ← fill a value
  pure a

-- Source: base/array.jl:647-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function $fname(::Type{T}, dims::NTuple{N, DimOrInd}) where {T,N}
--             a = similar(Array{T,N}, dims)
--             fill!(a, $felt(T))
--             return a
--         end
-- /Source
def constantAxes [Monad m] (similar : Dims → m A) (element : m E)
    (fill : A → E → m R) (dims : Dims) : m A := do
  let a ← similar dims
  let value ← element
  let _ ← fill a value
  pure a

-- Source: base/array.jl:713-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _array_for_inner(::Type{T}, ::HasShape{N}, axs) where {T,N} = similar(Array{T,N}, axs)
-- /Source
def arrayForShape [Monad m] (similar : T → Axes → m A)
    (t : T) (axes : Axes) : m A := similar t axes

-- Source: base/array.jl:875-879 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function collect_to_with_first!(dest::AbstractArray, v1, itr, st)
--     i1 = first(LinearIndices(dest))
--     dest[i1] = v1
--     return collect_to!(dest, itr, i1+1, st)
-- end
-- /Source
def collectWithFirstArray [Monad m] (linear : A → m Linear) (first : Linear → m Index)
    (set : A → E → Index → m Unit) (increment : Index → m NextIndex)
    (collect : A → X → NextIndex → St → m R)
    (dest : A) (value : E) (itr : X) (st : St) : m R := do
  let i ← first (← linear dest)
  set dest value i
  collect dest itr (← increment i) st

-- Source: base/array.jl:886-893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setindex_widen_up_to(dest::AbstractArray{T}, el, i) where T
--     @inline
--     new = similar(dest, promote_typejoin(T, typeof(el)))
--     f = first(LinearIndices(dest))
--     copyto!(new, first(LinearIndices(new)), dest, f, i-f)
--     @inbounds new[i] = el
--     return new
-- end
-- /Source
def setindexWiden [Monad m] (elementType : A → T) (typeof : E → T)
    (join : T → T → m T) (similar : A → T → m A)
    (linear : A → m Linear) (first : Linear → m FirstIndex)
    (subtract : Index → FirstIndex → m Count)
    (copy : A → FirstIndex → A → FirstIndex → Count → m Unit)
    (set : A → E → Index → m Unit) (dest : A) (el : E) (i : Index) : m A := do
  let new ← similar dest (← join (elementType dest) (typeof el))
  let f ← first (← linear dest)
  let newFirst ← first (← linear new)
  let n ← subtract i f
  copy new newFirst dest f n
  set new el i
  pure new

-- Source: base/array.jl:993-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(a::Array, r::AbstractUnitRange{Bool}) = getindex(a, to_index(r))
-- /Source
def getindexBoolRange [Monad m] (toIndex : R → m Indices)
    (get : A → Indices → m B) (a : A) (r : R) : m B := do
  get a (← toIndex r)

-- Source: base/array.jl:981-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, I::AbstractUnitRange{<:Integer})
--     @inline
--     @boundscheck checkbounds(A, I)
--     lI = length(I)
--     X = similar(A, axes(I))
--     if lI > 0
--         copyto!(X, firstindex(X), A, first(I), lI)
--     end
--     return X
-- end
-- /Source
def getindexUnitRange [Monad m] [MonadExceptOf Error m] (bounds : A → R → m Unit)
    (length : R → m Count) (axes : R → m Axes) (similar : A → Axes → m B)
    (positive : Count → m (Option Bool)) (firstindex : B → m DestIndex)
    (first : R → m SrcIndex)
    (copy : B → DestIndex → A → SrcIndex → Count → m C) (a : A) (r : R) : m B := do
  bounds a r
  let n ← length r
  let x ← similar a (← axes r)
  if ← Models1Group14.requireBool (← positive n) then
    let _ ← copy x (← firstindex x) a (← first r) n
    pure ()
  pure x

-- Source: base/array.jl:659-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(a::Type{Array{T,n}}, b::Type{Array{S,n}}) where {T,n,S} = el_same(promote_type(T,S), a, b)
-- /Source
def promoteArrayRule [Monad m] {T : Type} [DecidableEq T]
    (promoteType : T → T → m T) (promoteJoin : T → T → m T)
    (leftElement rightElement leftArray rightArray : T) : m T := do
  let promoted ← promoteType leftElement rightElement
  if promoted = leftElement then
    pure (JuliaLean.base.range.el_same_T_S promoted leftArray rightArray)
  else if promoted = rightElement then
    pure (JuliaLean.base.range.el_same_S_T promoted leftArray rightArray)
  else
    letI : JuliaLean.base.range.JPromoteTypejoinOf (m T) :=
      ⟨fun left right => do promoteJoin (← left) (← right)⟩
    JuliaLean.base.range.el_same_Any (pure promoted : m T) (pure leftArray) (pure rightArray)

-- Source: base/array.jl:1078-1087 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setindex!(A::Array{T}, X::Array{T}, I::AbstractUnitRange{Int}) where T
--     @inline
--     @boundscheck checkbounds(A, I)
--     lI = length(I)
--     setindex_shape_check(X, lI)
--     if lI > 0
--         unsafe_copyto!(A, first(I), X, 1, lI)
--     end
--     return A
-- end
-- /Source
def setindexUnitRange [Monad m] [MonadExceptOf Error m]
    (bounds : A → R → m Unit) (length : R → m Count)
    (shapeCheck : A → Count → m Unit) (positive : Count → m (Option Bool))
    (first : R → m Start) (copy : A → Start → A → I → Count → m C)
    (a x : A) (r : R) : m A := do
  bounds a r
  let n ← length r
  shapeCheck x n
  if ← Models1Group14.requireBool (← positive n) then
    let _ ← copy a (← first r) x one n
    pure ()
  pure a

-- Source: base/array.jl:1031-1035 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setindex!(A::Array{T}, x, i::Int) where {T}
--     @_propagate_inbounds_meta
--     x = x isa T ? x : convert(T, x)::T
--     return _setindex!(A, x, i)
-- end
-- /Source
def setindexScalar {State T X : Type}
    (native : NativeFillBoundary (NativeLiveState State T) T)
    (cast : X → Option T) (convert : X → NativeLiveM State T X)
    (rank a : Nat) (x : X) (i : I) : NativeLiveM State T Nat := do
  let value ← match cast x with
    | some value => pure value
    | none => do
      let converted ← convert x
      match cast converted with
      | some value => pure value
      | none => throwThe Error (.typeError "setindex!")
  JuliaLean.base.array.setindexTyped
    (fun handle index => do
      let n ← nativeLiveLength rank handle
      if !(JuliaLean.base.essentials.checkboundsBool n index) then throwThe Error .bounds)
    (fun handle index _ => do
      native.memoryrefNew (← nativeLiveReadRef rank handle) index false)
    (fun ref value checked => native.memoryrefSet ref value .notAtomic checked) a value i

-- Source: base/array.jl:712-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _array_for_inner(::Type{T}, ::HasLength, len::Integer) where {T} = Vector{T}(undef, Int(len))
-- /Source
def arrayForLength {State T Z : Type} (allocation : NativeAllocationBoundary State T)
    (toInt : Z → NativeCopyM (NativeCopyWorld State) I) (length : Z) :
    NativeCopyM (NativeCopyWorld State) (NativeCopyArray T) := do
  nativeVectorUndef allocation (← toInt length)

end JuliaLean.base.array.Completion4

namespace JuliaLean.base.array.Completion5
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

inductive GrowatReturn where
  | nothing
  | sizeTuple (size : I)

section
variable {State T V D N Mod P Sym Ref Z Index : Type}
variable (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
  (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
  (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
  (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)

-- Source: base/array.jl:1225-1270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _growat!(a::Vector, i::Integer, delta::Integer)
--     @_terminates_globally_noub_meta
--     delta = Int(delta)
--     i = Int(i)
--     i == 1 && return _growbeg!(a, delta)
--     len = length(a)
--     len < typemax(Int) && i == len + 1 && return _growend!(a, delta)
--     delta >= 0 || throw(ArgumentError("grow requires delta >= 0"))
--     1 < i <= len || throw(BoundsError(a, i))
--     ref = a.ref
--     mem = ref.mem
--     memlen = length(mem)
--     newlen = checked_add(len, delta)
--     offset = memoryrefoffset(ref)
--     newmemlen = checked_add(offset - 1, newlen)
-- 
--     # which side would we rather grow into?
--     prefer_start = i <= div(len, 2)
--     # if offset is far enough advanced to fit data in beginning of the memory
--     if prefer_start && delta <= offset - 1
--         newref = @inbounds memoryref(mem, offset - delta)
--         unsafe_copyto!(newref, ref, i)
--         setfield!(a, :ref, newref)
--         setfield!(a, :size, (newlen,))
--         for j in i:i+delta-1
--             @inbounds unsetindex!(a, j)
--         end
--     elseif !prefer_start && memlen >= newmemlen
--         unsafe_copyto!(mem, offset - 1 + delta + i, mem, offset - 1 + i, len - i + 1)
--         setfield!(a, :size, (newlen,))
--         for j in i:i+delta-1
--             @inbounds unsetindex!(a, j)
--         end
--     else
--         # since we will allocate the array in the middle of the memory we need at least 2*delta extra space
--         # the +1 is because I didn't want to have an off by 1 error.
--         newmemlen = max(overallocation(memlen), checked_add(len, checked_mul(2, delta), 1))
--         newoffset = (newmemlen - newlen) ÷ 2 + 1
--         newmem = array_new_memory(mem, newmemlen)
--         newref = @inbounds memoryref(newmem, newoffset)
--         unsafe_copyto!(newref, ref, i-1)
--         unsafe_copyto!(newmem, newoffset + delta + i - 1, mem, offset + i - 1, len - i + 1)
--         setfield!(a, :ref, newref)
--         setfield!(a, :size, (newlen,))
--     end
-- end
-- /Source
def growat (toDeltaInt : Z → NativeGrowthM State T I)
    (toIndexInt : Index → NativeGrowthM State T I) (a : Nat) (index : Index) (d : Z) :
    NativeGrowthM State T GrowatReturn := do
  let storage := nativeGrowthStorage layout elementType native ccall allocation access references
  let delta ← toDeltaInt d
  let i ← toIndexInt index
  let intIdentity := fun n : I => nativeCopyLift
    (JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 n))
  if i = one then
    Completion3.growbeg layout elementType native ccall allocation access references intIdentity a delta
    return .nothing
  let len ← storage.length a
  if len < typemaxInt && i = len + one then
    Completion3.growend layout elementType native ccall allocation access references intIdentity a delta
    return .nothing
  if delta < zero then throwThe Error (.argument "grow requires delta >= 0")
  if !(one < i && i ≤ len) then throwThe Error .bounds
  let ref ← storage.ref a
  let mem := storage.memory ref
  let memlen ← storage.memLength mem
  let newlen ← storage.checkedAdd len delta
  let offset := storage.offset ref
  let newmemlen ← storage.checkedAdd (offset - one) newlen
  let preferStart := i ≤ (← storage.divide len (JInt.wrap .i64 2))
  if preferStart && delta ≤ offset - one then
    let newref ← storage.memoryref mem (offset - delta)
    storage.copyRef newref ref i
    storage.setRef a newref
    storage.setSize a newlen
    for j in intRange i (i + delta - one) do storage.unsetArray a j
    return .nothing
  else if !preferStart && memlen ≥ newmemlen then
    storage.copyMemory mem (offset - one + delta + i) mem (offset - one + i) (len - i + one)
    storage.setSize a newlen
    for j in intRange i (i + delta - one) do storage.unsetArray a j
    return .nothing
  else
    let grown ← storage.overallocation memlen
    let twice ← storage.checkedMul (JInt.wrap .i64 2) delta
    let requested ← storage.checkedAdd len twice
    let requested ← storage.checkedAdd requested one
    let newmemlen := max grown requested
    let newoffset := (← storage.divide (newmemlen - newlen) (JInt.wrap .i64 2)) + one
    let newmem ← storage.allocate mem newmemlen
    let newref ← storage.memoryref newmem newoffset
    storage.copyRef newref ref (i - one)
    storage.copyMemory newmem (newoffset + delta + i - one) mem (offset + i - one) (len - i + one)
    storage.setRef a newref
    storage.setSize a newlen
    return .sizeTuple newlen

-- Source: base/array.jl:1307-1322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _deleteat!(a::Vector, i::Integer, delta::Integer)
--     i = Int(i)
--     len = length(a)
--     0 <= delta || throw(ArgumentError("_deleteat! requires delta >= 0"))
--     1 <= i <= len || throw(BoundsError(a, i))
--     delta <= len + 1 - i || throw(BoundsError(a, i + delta - 1))
--     newa = a
--     if 2*i + delta <= len
--         unsafe_copyto!(newa, 1 + delta, a, 1, i - 1)
--         _deletebeg!(a, delta)
--     else
--         unsafe_copyto!(newa, i, a, i + delta, len + 1 - delta - i)
--         _deleteend!(a, delta)
--     end
--     return
-- end
-- /Source
def deleteat (toIndexInt : Index → NativeGrowthM State T I)
    (toDeltaInt : Z → NativeGrowthM State T I)
    (nonnegative : Z → NativeGrowthM State T (Option Bool))
    (fits : Z → I → NativeGrowthM State T (Option Bool))
    (plusDelta : I → Z → NativeGrowthM State T Offset)
    (subtractOne : Offset → NativeGrowthM State T BadIndex)
    (leLength : Offset → I → NativeGrowthM State T (Option Bool))
    (minusDelta : I → Z → NativeGrowthM State T Remainder)
    (minusIndex : Remainder → I → NativeGrowthM State T Count)
    (copyFirst : Nat → Offset → Nat → I → I → NativeGrowthM State T Unit)
    (copyLast : Nat → I → Nat → Offset → Count → NativeGrowthM State T Unit)
    (a : Nat) (index : Index) (delta : Z) : NativeGrowthM State T Unit := do
  let storage := nativeGrowthStorage layout elementType native ccall allocation access references
  let i ← toIndexInt index
  let len ← storage.length a
  if !(← Models1Group14.requireBool (← nonnegative delta)) then
    throwThe Error (.argument "_deleteat! requires delta >= 0")
  if !(one ≤ i && i ≤ len) then throwThe Error .bounds
  if !(← Models1Group14.requireBool (← fits delta (len + one - i))) then
    let _ ← subtractOne (← plusDelta i delta)
    throwThe Error .bounds
  if ← Models1Group14.requireBool (← leLength (← plusDelta (JInt.wrap .i64 2 * i) delta) len) then
    let offset ← plusDelta one delta
    copyFirst a offset a one (i - one)
    Completion3.deletebeg layout elementType native ccall allocation access references toDeltaInt a delta
  else
    let offset ← plusDelta i delta
    let count ← minusIndex (← minusDelta (len + one) delta) i
    copyLast a i a offset count
    Completion3.deleteend layout elementType native ccall allocation access references toDeltaInt a delta

end
end JuliaLean.base.array.Completion5

namespace JuliaLean.base.array.Completion6
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Install the fields of the actual newly constructed Vector in the existing
live-header world. The native identity result and all preceding effects remain intact. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
def vectorUndef (allocation : NativeAllocationBoundary (NativeGrowthState State T) T) (n : I) :
    NativeGrowthM State T Nat := do
  let array ← nativeVectorUndef allocation n
  let world ← nativeCopyLift JuliaLean.base.io.getWorld
  let header : NativeGrowthVector T := ⟨array.ref, n⟩
  let headers := fun handle => if handle = array.identity then header else world.other.headers handle
  nativeCopyLift (JuliaLean.base.io.setWorld { world with other := { world.other with headers := headers } })
  pure array.identity

-- Source: base/array.jl:1057-1060 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- __safe_setindex!(A::Vector{T}, x::T, i::Int) where {T} = (@inline; @_nothrow_noub_meta;
--     memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false); return A)
-- __safe_setindex!(A::Vector{T}, x,    i::Int) where {T} = (@inline;
--     __safe_setindex!(A, convert(T, x)::T, i))
-- /Source
def safeSet (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (cast : E → Option T) (convert : E → NativeGrowthM State T E)
    (a : Nat) (x : E) (i : I) : NativeGrowthM State T Nat := do
  match cast x with
  | some value =>
    safeSetindex1057
      (fun handle index _ => do nativeGrowthShiftRef references false (← nativeGrowthReadRef handle) index)
      (fun ref value checked => access.memoryrefSet ref value .notAtomic checked) a value i
  | none => Completion3.safeSetindexConvert access references convert cast a x i

section
variable {State T V D N Mod P Sym Ref E X : Type}
variable (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
  (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
  (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
  (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)

-- Source: base/array.jl:445-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(::Type{T}, vals...) where T
--     @inline
--     @_effect_free_terminates_locally_meta
--     a = Vector{T}(undef, length(vals))
--     if vals isa NTuple
--         @_safeindex for i in 1:length(vals)
--             a[i] = vals[i]
--         end
--     else
--         # use afoldl to avoid type instability inside loop
--         afoldl(1, vals...) do i, v
--             @inbounds a[i] = v
--             return i + 1
--         end
--     end
--     return a
-- end
-- /Source
def typedLiteral (cast : E → Option T) (convert : E → NativeGrowthM State T E)
    (homogeneous : Bool) (values : TupleArgs E) : NativeGrowthM State T Nat :=
  JuliaLean.base.array.typedLiteral (vectorUndef allocation)
    (safeSet access references cast convert) homogeneous values.values

-- Source: base/array.jl:688-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _collect(::Type{T}, itr, isz::SizeUnknown) where T
--     a = Vector{T}()
--     for x in itr
--         push!(a, x)
--     end
--     return a
-- end
-- /Source
def collectUnknown [ForIn (NativeGrowthM State T) X E]
    (cast : E → Option T) (convert : E → NativeGrowthM State T E)
    (isAny : Bool) (asAny : E → T) (itr : X) : NativeGrowthM State T Nat := do
  let pushValue : Nat → E → NativeGrowthM State T Unit := fun a x => do
    let value ← if isAny then pure (asAny x) else
      match cast x with
      | some value => pure value
      | none => do
        let converted ← convert x
        match cast converted with
        | some value => pure value
        | none => throwThe Error (.typeError "push!")
    let grow := Completion3.growend layout elementType native ccall allocation access references
      (fun i : I => nativeCopyLift (JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 i)))
    let storage := nativeGrowthStorage layout elementType native ccall allocation access references
    let set := fun a value i => do
      let _ ← (if isAny then safeSetindex1055 else safeSetindex1057)
        (fun handle index _ => do nativeGrowthShiftRef references false (← nativeGrowthReadRef handle) index)
        (fun ref value checked => access.memoryrefSet ref value .notAtomic checked) a value i
      pure ()
    let _ ← if isAny then JuliaLean.base.array.push1368 grow storage.length set a value
      else JuliaLean.base.array.push1361 grow storage.length set a value
    pure ()
  JuliaLean.base.array.collectUnknown (vectorUndef allocation zero) pushValue itr

end

-- Source: base/array.jl:686-687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _collect(::Type{T}, itr, isz::Union{HasLength,HasShape}) where {T} =
--     copyto!(_array_for_inner(T, isz, _similar_shape(itr, isz)), itr)
-- /Source
def collectSized {State T X Size V Z Axes A R : Type}
    (allocation : NativeAllocationBoundary State T) (embed : NativeCopyArray T → A)
    (isLength : Size → Bool) (length : X → NativeCopyM (NativeCopyWorld State) V)
    (integer : V → Option Z) (toInt : Z → NativeCopyM (NativeCopyWorld State) I)
    (axes : X → NativeCopyM (NativeCopyWorld State) Axes)
    (similar : Size → Axes → NativeCopyM (NativeCopyWorld State) A)
    (copy : A → X → NativeCopyM (NativeCopyWorld State) R)
    (itr : X) (size : Size) : NativeCopyM (NativeCopyWorld State) R := do
  let array ← if isLength size then do
      let value ← length itr
      let n ← match integer value with
        | some n => pure n
        | none => throwThe Error (.typeError "_similar_shape")
      pure (embed (← nativeVectorUndef allocation (← toInt n)))
    else similar size (← axes itr)
  copy array itr

end JuliaLean.base.array.Completion6

namespace JuliaLean.base.array.Completion7
open JuliaLean JuliaLean.base.array

-- Source: base/array.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- AbstractArray{T,N}(A::AbstractArray{S,N}) where {T,N,S} = copyto_axcheck!(similar(A,T), A)
-- /Source
def abstractArrayConstructor [Monad m] [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m]
    (similar : S → m A) (axesDest : A → m Axes) (axesSrc : S → m Axes)
    (eq : Axes → Axes → m Bool) (showAxes : Axes → m String)
    (copy : A → S → m A) (a : S) : m A := do
  let dest ← similar a
  JuliaLean.base.abstractarray.Models1Group2.copytoAxesCheckLinked axesDest axesSrc eq showAxes copy dest a

end JuliaLean.base.array.Completion7

namespace JuliaLean.AbstractArrays.GVec

/-- `reverse(A)` preserves the axis and reverses iteration values,
`base/array.jl:2253-2265`. -/
def reverse (v : GVec α) : GVec α := { v with slots := v.slots.reverse }

/-- `_fill!`, `base/array.jl:368-377`. -/
def fill (v : GVec α) (x : α) : GVec α :=
  { v with slots := List.replicate v.slots.length (some x) }

end JuliaLean.AbstractArrays.GVec

namespace JuliaLean.Multidim

/-- Axes of a 1-based `Array` of size `sz`. -/
def oneAxes (sz : List Nat) : List (Int × Int) := sz.map fun (n : Nat) => ((1 : Int), (n : Int))

/-- The loop of the generic `findnext(testf, A, start)`, `base/array.jl:2475-2486`,
with `keys(A) = CartesianIndices(axes(A))` for an `Array` of size `sz`; `A[i]` throws
`BoundsError` outside the array and `nextind(A, i)` is `inc(i.I, iter.indices)`
(`base/multidimensional.jl:159-164`). `fuel` bounds the number of iterations. -/
def findLoop (inc : List I64 → List Rng → Bool × List I64)
    (sz : List Nat) (A : List Int → Bool) : Nat → List I64 → R (Option (List I64))
  | 0, _ => .ok none
  | fuel + 1, i =>
    if !inAxes (oneAxes sz) (i.map (·.val)) then .error .boundsError
    else if A (i.map (·.val)) then .ok (some i)
    else if i = sz.map (fun (n : Nat) => i64 n) then .ok none
    else findLoop inc sz A fuel (inc i (sz.map fun (n : Nat) => (⟨i64 1, i64 1, n⟩ : Rng))).2

/-- `findnext(testf, A, start)`, `base/array.jl:2475-2486`: `l = last(keys(A))`,
`i > l && return nothing`, then the loop. -/
def findnext (inc : List I64 → List Rng → Bool × List I64)
    (ciLess : List I64 → List I64 → Bool)
    (sz : List Nat) (A : List Int → Bool) (start : List I64) : R (Option (List I64)) :=
  let l := sz.map fun (n : Nat) => i64 n
  if ciLess l start then .ok none
  else findLoop inc sz A (sz.foldl (· * ·) 1 + 1) start

/-- `findfirst(testf, A::AbstractArray) = findnext(testf, A, first(keys(A)))`,
`base/array.jl:2444, 2531-2532`. -/
def findfirst (inc : List I64 → List Rng → Bool × List I64)
    (ciLess : List I64 → List I64 → Bool)
    (sz : List Nat) (A : List Int → Bool) : R (Option (List I64)) :=
  findnext inc ciLess sz A (sz.map fun _ => i64 1)

end JuliaLean.Multidim

namespace JuliaLean.ArrayCov


structure ArrayShape where
  elementType : Int
  dims : List Int
  deriving Repr, DecidableEq

/-- `DimensionMismatch()`, `base/array.jl:14`. -/
def array14DimensionMismatch (_ : Unit) : String := ""

/-- `vect()`, `base/array.jl:158`. -/
def array158Vect (_ : Unit) : List Int := []

/-- The recursive calls made by `asize_from`. -/
def array188AsizeLoop (size : Int → Int) : Int → Nat → List Int
  | _, 0 => []
  | n, fuel + 1 => size n :: array188AsizeLoop size (n + 1) fuel

/-- `asize_from(a, n)`, `base/array.jl:188`, including nonpositive `n`. -/
def array188AsizeFrom (size : Int → Int) (ndims n : Int) : List Int :=
  if n > ndims then []
  else array188AsizeLoop size n (ndims - n + 1).toNat

/-- `allocatedinline(T)`, `base/array.jl:190`. -/
def array190AllocatedInline (storedInline : Int → Int) (type : Int) : Bool :=
  storedInline type != 0

/-- `isbitsunion(u)`, `base/array.jl:206`. -/
def array206IsbitsUnion (isUnion : Int → Bool) (allocatedInline : Int → Bool)
    (type : Int) : Bool :=
  isUnion type && allocatedInline type

/-- The integer-index wrapper of `unsetindex!`, `base/array.jl:208`. -/
def array208UnsetIndexInteger (toIndex : Int → Jl Int)
    (unsetIndex : List Bool → Int → Jl (List Bool))
    (assigned : List Bool) (i : Int) : Jl (List Bool) := do
  let index ← toIndex i
  unsetIndex assigned index

/-- `elsize(::Type{Array})`, `base/array.jl:218`. -/
def array218ElsizeArray (alignedSizeof : Int → JInt64) (elementType : Int) : JInt64 :=
  alignedSizeof elementType

/-- `elsize(::Type{Union{}})`, `base/array.jl:226`. -/
def array226ElsizeBottom (_ : Unit) : Nat := 0

/-- The slurping bottom-type `elsize` method, `base/array.jl:227`. -/
def array227ElsizeBottomExtra (argumentCount : Nat) : Jl Nat :=
  .error (.methodError s!"elsize/{argumentCount + 1}")

/-- `sizeof(a::Array)`, `base/array.jl:229`; multiplication is wrapping `Int`. -/
def array229Sizeof (length elsize : JInt64) : JInt64 := length * elsize

/-- `_throw_argerror(s)`, `base/array.jl:321`. -/
def array321ThrowArgError (message : String) : Jl Unit :=
  .error (.argumentError message)

/-- `_copyto2arg!(dest, src)`, `base/array.jl:323`. -/
def array323Copyto2Arg
    (copyto : List Int → Int → List Int → Int → Nat → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto dest 1 src 1 src.length

/-- `copyto!(::Array, ::Array)`, `base/array.jl:325`. -/
def array325CopytoArrayArray
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- `copyto!(::Array, ::Memory)`, `base/array.jl:326`. -/
def array326CopytoArrayMemory
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- `copyto!(::Memory, ::Array)`, `base/array.jl:327`. -/
def array327CopytoMemoryArray
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- Same-element `copyto!(::Array, ::Array)`, `base/array.jl:330`. -/
def array330CopytoSameArray
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- Same-element `copyto!(::Array, ::Memory)`, `base/array.jl:331`. -/
def array331CopytoSameArrayMemory
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- Same-element `copyto!(::Memory, ::Array)`, `base/array.jl:332`. -/
def array332CopytoSameMemoryArray
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- `similar(a::Vector{T})`, `base/array.jl:414`. -/
def array414SimilarVector (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) : Jl ArrayShape :=
  array a.elementType [a.dims.getD 0 0]

/-- `similar(a::Matrix{T})`, `base/array.jl:415`. -/
def array415SimilarMatrix (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) : Jl ArrayShape :=
  array a.elementType [a.dims.getD 0 0, a.dims.getD 1 0]

/-- `similar(a::Vector{T}, S)`, `base/array.jl:416`. -/
def array416SimilarVectorType (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) (newType : Int) : Jl ArrayShape :=
  array newType [a.dims.getD 0 0]

/-- `similar(a::Matrix{T}, S)`, `base/array.jl:417`. -/
def array417SimilarMatrixType (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) (newType : Int) : Jl ArrayShape :=
  array newType [a.dims.getD 0 0, a.dims.getD 1 0]

/-- `similar(a::Array{T}, m)`, `base/array.jl:418`. -/
def array418SimilarLength (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) (length : Int) : Jl ArrayShape :=
  array a.elementType [length]

/-- `similar(a::Array, T, dims)`, `base/array.jl:419`. -/
def array419SimilarTypeDims (array : Int → List Int → Jl ArrayShape)
    (_a : ArrayShape) (newType : Int) (dims : List Int) : Jl ArrayShape :=
  array newType dims

/-- `similar(a::Array{T}, dims)`, `base/array.jl:420`. -/
def array420SimilarDims (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) (dims : List Int) : Jl ArrayShape :=
  array a.elementType dims

/-- `similar(::Type{Array{T,N}}, dims)`, `base/array.jl:421`. -/
def array421SimilarArrayType (similarArray : Int → List Int → Jl ArrayShape)
    (elementType : Int) (dims : List Int) : Jl ArrayShape :=
  similarArray elementType dims

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


inductive DimArg where
  | integer (value : Int)
  | oneTo (last : Int)
  deriving Repr, DecidableEq

/-- `to_dim(d::Integer)`, `base/array.jl:482`. -/
def array482ToDimInteger (d : Int) : Int := d

/-- `to_dim(d::OneTo)`, `base/array.jl:483`. -/
def array483ToDimOneTo (last : Int) : Int := last

def dimArgValue : DimArg → Int
  | .integer value => array482ToDimInteger value
  | .oneTo last => array483ToDimOneTo last

/-- Vararg `fill`, `base/array.jl:583`. -/
def array583FillVarargs (fillTuple : Int → List DimArg → Jl ArrayShape)
    (value : Int) (dims : List DimArg) : Jl ArrayShape :=
  fillTuple value dims

/-- Union-dimension tuple `fill`, `base/array.jl:584`. -/
def array584FillMapped (fillInts : Int → List Int → Jl ArrayShape)
    (value : Int) (dims : List DimArg) : Jl ArrayShape :=
  fillInts value (dims.map dimArgValue)

/-- Integer-dimension `fill`, `base/array.jl:585`: allocate, fill, return. -/
def array585FillInteger (allocate : Int → List Int → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape)
    (value type : Int) (dims : List Int) : Jl ArrayShape := do
  let array ← allocate type dims
  fillBang array value

/-- General-dimension `fill`, `base/array.jl:586`: similar, fill, return. -/
def array586FillDimArgs (similar : Int → List DimArg → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape)
    (value type : Int) (dims : List DimArg) : Jl ArrayShape := do
  let array ← similar type dims
  fillBang array value

/-- Zero-dimensional `fill`, `base/array.jl:587`. -/
def array587FillZero (allocate : Int → List Int → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape)
    (value type : Int) : Jl ArrayShape := do
  let array ← allocate type []
  fillBang array value

/-- Generated `zeros`/`ones` vararg wrapper, `base/array.jl:633`. -/
def array633FilledVarargs (call : List DimArg → Jl ArrayShape)
    (dims : List DimArg) : Jl ArrayShape := call dims

/-- Generated typed vararg wrapper, `base/array.jl:634`. -/
def array634FilledTypedVarargs (call : Int → List DimArg → Jl ArrayShape)
    (type : Int) (dims : List DimArg) : Jl ArrayShape := call type dims

/-- Generated default-Float64 tuple wrapper, `base/array.jl:635`. -/
def array635FilledDefaultTuple (call : Int → List DimArg → Jl ArrayShape)
    (float64 : Int) (dims : List DimArg) : Jl ArrayShape := call float64 dims

/-- Generated typed mapped-dimension wrapper, `base/array.jl:636`. -/
def array636FilledMapped (call : Int → List Int → Jl ArrayShape)
    (type : Int) (dims : List DimArg) : Jl ArrayShape :=
  call type (dims.map dimArgValue)

/-- Generated integer-dimension body, `base/array.jl:637-641`. -/
def array637FilledInteger (allocate : Int → List Int → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape) (felt : Int → Int)
    (type : Int) (dims : List Int) : Jl ArrayShape := do
  let array ← allocate type dims
  fillBang array (felt type)

/-- Generated zero-dimensional body, `base/array.jl:642-646`. -/
def array642FilledZero (allocate : Int → List Int → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape) (felt : Int → Int)
    (type : Int) : Jl ArrayShape := do
  let array ← allocate type []
  fillBang array (felt type)

/-- Generated general-dimension body, `base/array.jl:647-651`. -/
def array647FilledDimArgs (similar : Int → List DimArg → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape) (felt : Int → Int)
    (type : Int) (dims : List DimArg) : Jl ArrayShape := do
  let array ← similar type dims
  fillBang array (felt type)
/-- `convert(::Type{T}, a::AbstractArray)`, `base/array.jl:657`. -/
def array657Convert (isType : List Int → Bool) (construct : List Int → Jl (List Int))
    (array : List Int) : Jl (List Int) :=
  if isType array then .ok array else construct array

/-- `promote_rule(::Type{Array}, ::Type{Array})`, `base/array.jl:659`. -/
def array659PromoteRule (promoteType : Int → Int → Int)
    (elSame : Int → Int → Int → Int) (left right leftArray rightArray : Int) : Int :=
  elSame (promoteType left right) leftArray rightArray

/-- Concrete Array conversion constructor, `base/array.jl:664`. -/
def array664ArrayConstructor (size : List Int → List Int)
    (allocate : List Int → Jl (List Int))
    (copyAxes : List Int → List Int → Jl (List Int)) (source : List Int) : Jl (List Int) := do
  let dest ← allocate (size source)
  copyAxes dest source

/-- AbstractArray conversion constructor, `base/array.jl:665`. -/
def array665AbstractConstructor (similar : List Int → Jl (List Int))
    (copyAxes : List Int → List Int → Jl (List Int)) (source : List Int) : Jl (List Int) := do
  let dest ← similar source
  copyAxes dest source

inductive IteratorSizeModel where
  | unknown | hasLength | hasShape
  deriving Repr, DecidableEq

/-- `collect(T, itr)`, `base/array.jl:684`. -/
def array684Collect (iteratorSize : List Int → IteratorSizeModel)
    (collectInner : List Int → IteratorSizeModel → Jl (List Int))
    (iterator : List Int) : Jl (List Int) :=
  collectInner iterator (iteratorSize iterator)

/-- Sized `_collect`, `base/array.jl:686-687`. -/
def array686CollectSized (similarShape : List Int → IteratorSizeModel → Int)
    (arrayFor : IteratorSizeModel → Int → Jl (List Int))
    (copyto : List Int → List Int → Jl (List Int))
    (iterator : List Int) (size : IteratorSizeModel) : Jl (List Int) := do
  let dest ← arrayFor size (similarShape iterator size)
  copyto dest iterator

def array688PushAll (push : List Int → Int → Jl (List Int)) :
    List Int → List Int → Jl (List Int)
  | dest, [] => .ok dest
  | dest, value :: rest => do
      let dest ← push dest value
      array688PushAll push dest rest

/-- Unknown-size `_collect`, `base/array.jl:688-694`. -/
def array688CollectUnknown (push : List Int → Int → Jl (List Int))
    (iterator : List Int) : Jl (List Int) :=
  array688PushAll push [] iterator

/-- Generic `_similar_for`, `base/array.jl:697`. -/
def array697SimilarFor (similar : Int → Int → Jl Int)
    (container type : Int) : Jl Int :=
  similar container type

def array699SimilarShapeUnknown (_iterator : List Int) : Option Int := none
def array700SimilarShapeLength (iterator : List Int) : Int := iterator.length
def array701SimilarShapeAxes (axes : List Int → Int) (iterator : List Int) : Int := axes iterator

def array703SimilarForUnknown (similar : Int → Int → Int → Jl Int)
    (container type : Int) : Jl Int := similar container type 0

def array705SimilarForLength (similar : Int → Int → Int → Jl Int)
    (container type length : Int) : Jl Int := similar container type length

def array707SimilarForShape (similar : Int → Int → Int → Jl Int)
    (container type axes : Int) : Jl Int := similar container type axes

def array711ArrayForUnknown (allocate : Int → Int → Jl Int) (type : Int) : Jl Int :=
  allocate type 0

def array712ArrayForLength (allocate : Int → Int → Jl Int)
    (type length : Int) : Jl Int := allocate type length

def array713ArrayForShape (similar : Int → Int → Jl Int)
    (type axes : Int) : Jl Int := similar type axes

def array716ArrayFor (similarShape : List Int → IteratorSizeModel → Int)
    (arrayFor : IteratorSizeModel → Int → Jl Int)
    (iterator : List Int) (size : IteratorSizeModel) : Jl Int :=
  arrayFor size (similarShape iterator size)

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


inductive ExprModel where
  | atom (value : Int)
  | node (head : Int) (args : List ExprModel)
  | ref (array : ExprModel) (indices : List ExprModel)
  | assign (left right : ExprModel)
  | call (fn : Int) (args : List ExprModel)

def array132SafeIndexMacro (escape recurse : ExprModel → ExprModel)
    (expression : ExprModel) : ExprModel := escape (recurse expression)

def array135SafeIndex (recurse : ExprModel → ExprModel)
    (safeGet safeSet : Int) : ExprModel → ExprModel
  | ExprModel.atom value => .atom value
  | ExprModel.assign (ExprModel.ref array indices) right =>
      .call safeSet (array :: recurse right :: indices.map recurse)
  | ExprModel.ref array indices => .call safeGet (array :: indices)
  | ExprModel.node head args => .node head (args.map recurse)
  | ExprModel.assign left right => .assign (recurse left) (recurse right)
  | ExprModel.call fn args => .call fn (args.map recurse)

def array159VectLoop (setindex : List Int → Nat → Int → List Int) :
    List Int → Nat → List Int → List Int
  | output, _, [] => output
  | output, index, value :: rest =>
      array159VectLoop setindex (setindex output index value) (index + 1) rest

def array159Vect (allocate : Nat → List Int)
    (setindex : List Int → Nat → Int → List Int) (values : List Int) : List Int :=
  array159VectLoop setindex (allocate values.length) 1 values

def array183VectPromoted (promoteType : List Int → Int)
    (typedLiteral : Int → List Int → Jl (List Int)) (values : List Int) : Jl (List Int) :=
  typedLiteral (promoteType values) values

structure DenseArrayModel where
  data : List Int
  assigned : List Bool
  dims : List Int
  deriving Repr, DecidableEq

def array209UnsetIndex (checkbounds : DenseArrayModel → JInt64 → Bool)
    (unset : DenseArrayModel → JInt64 → DenseArrayModel)
    (array : DenseArrayModel) (index : JInt64) : Jl DenseArrayModel :=
  if checkbounds array index then .ok (unset array index) else .error .boundsError

def array219ElsizePtr (isAny : Int → Bool) (isDataType : Int → Bool)
    (pointerSize : JInt64) (coreSize alignment : Int → JInt64)
    (align : JInt64 → JInt64 → JInt64) (type : Int) : Jl JInt64 :=
  if isAny type then .ok pointerSize
  else if !isDataType type then .error (.methodError "sizeof")
  else .ok (align (coreSize type) (alignment type))

def array231IsAssigned (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (sub2ind : List Int → List JInt64 → JInt64)
    (memoryAssigned : DenseArrayModel → JInt64 → Bool)
    (array : DenseArrayModel) (indices : List JInt64) : Bool :=
  if !checkbounds array indices then false
  else memoryAssigned array (sub2ind array.dims indices)

def array239IsAssignedVector (checkbounds : DenseArrayModel → JInt64 → Bool)
    (memoryAssigned : DenseArrayModel → JInt64 → Bool)
    (array : DenseArrayModel) (index : JInt64) : Bool :=
  if !checkbounds array index then false else memoryAssigned array index

def array259UnsafeCopyPtr (alignedSize : Int → JInt64)
    (memmove : Int → JInt64 → JInt64 → JInt64 → Int)
    (memory type : Int) (dest src count : JInt64) : JInt64 × Int :=
  let memory := memmove memory dest src (count * alignedSize type)
  (dest, memory)

def array276UnsafeCopyArray
    (memoryRef : DenseArrayModel → JInt64 → JInt64)
    (copyPtr : Int → JInt64 → JInt64 → JInt64 → Int)
    (memory : Int)
    (dest : DenseArrayModel) (destOffset : JInt64)
    (src : DenseArrayModel) (srcOffset count : JInt64) : DenseArrayModel × Int :=
  if count.val = 0 then (dest, memory)
  else
    let memory := copyPtr memory (memoryRef dest destOffset) (memoryRef src srcOffset) count
    (dest, memory)

def array288Copyto (copyImpl : DenseArrayModel → Int → DenseArrayModel → Int → Int → Jl DenseArrayModel)
    (dest : DenseArrayModel) (destOffset : Int) (src : DenseArrayModel)
    (srcOffset count : Int) : Jl DenseArrayModel :=
  copyImpl dest destOffset src srcOffset count

def array290CopytoArrayMemory := array288Copyto
def array292CopytoMemoryArray := array288Copyto
def array296CopytoSameArray := array288Copyto

def array373FillLoop (setindex : DenseArrayModel → Nat → Int → DenseArrayModel) :
    DenseArrayModel → Nat → Nat → Int → DenseArrayModel
  | array, _, 0, _ => array
  | array, index, fuel + 1, value =>
      array373FillLoop setindex (setindex array index value) (index + 1) fuel value

def array368Fill (isType : Int → Bool) (convert : Int → Jl Int)
    (fillTyped : DenseArrayModel → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) : Jl DenseArrayModel := do
  let value ← if isType value then pure value else convert value
  pure (fillTyped array value)

def array373Fill (setindex : DenseArrayModel → Nat → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) : DenseArrayModel :=
  array373FillLoop setindex array 1 array.data.length value

def array391Copy (allocate : Nat → DenseArrayModel)
    (unsafeCopy : DenseArrayModel → DenseArrayModel → Nat → DenseArrayModel)
    (array : DenseArrayModel) : DenseArrayModel :=
  let output := allocate array.data.length
  let output := unsafeCopy output array array.data.length
  { output with dims := array.dims }

def array402Take (sameRef sameSize : DenseArrayModel → DenseArrayModel → Bool)
    (setRef setSize : DenseArrayModel → DenseArrayModel → DenseArrayModel)
    (dest src : DenseArrayModel) : DenseArrayModel :=
  let dest := if sameRef dest src then dest else setRef dest src
  if sameSize dest src then dest else setSize dest src

def array445LiteralLoop (setindex : List Int → Nat → Int → Jl (List Int)) :
    List Int → Nat → List Int → Jl (List Int)
  | output, _, [] => .ok output
  | output, index, value :: rest => do
      let output ← setindex output index value
      array445LiteralLoop setindex output (index + 1) rest

def array445TypedLiteral (allocate : Nat → List Int)
    (tupleSet foldSet : List Int → Nat → Int → Jl (List Int))
    (isTuple : Bool) (values : List Int) : Jl (List Int) :=
  let output := allocate values.length
  if isTuple then array445LiteralLoop tupleSet output 1 values
  else array445LiteralLoop foldSet output 1 values

def array463AnyLoop (setindex : List Int → Nat → Int → List Int) :
    List Int → Nat → List Int → List Int
  | output, _, [] => output
  | output, index, value :: rest =>
      array463AnyLoop setindex (setindex output index value) (index + 1) rest

def array463AnyLiteral (allocate : Nat → List Int)
    (setindex : List Int → Nat → Int → List Int) (values : List Int) : List Int :=
  array463AnyLoop setindex (allocate values.length) 1 values

def array471AnyEmpty (_ : Unit) : List Int := []

def array473FillBytes (convert : Int → Jl Int)
    (memset : DenseArrayModel → Int → Nat → DenseArrayModel)
    (alreadyType : Int → Bool) (array : DenseArrayModel) (value : Int) : Jl DenseArrayModel := do
  let value ← if alreadyType value then pure value else convert value
  pure (memset array value array.data.length)

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


def array974GetCartesian (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (linearIndex : DenseArrayModel → List JInt64 → JInt64)
    (getindex : DenseArrayModel → JInt64 → Jl Int)
    (array : DenseArrayModel) (indices : List JInt64) : Jl Int := do
  if checkbounds array indices then pure () else throw .boundsError
  getindex array (linearIndex array indices)

def array981GetRange (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (axes : List JInt64 → List Int)
    (similar : DenseArrayModel → List Int → Jl DenseArrayModel)
    (firstIndex : DenseArrayModel → JInt64)
    (copyto : DenseArrayModel → JInt64 → DenseArrayModel → JInt64 → Nat →
      Jl DenseArrayModel)
    (array : DenseArrayModel) (range : List JInt64) : Jl DenseArrayModel := do
  if checkbounds array range then pure () else throw .boundsError
  let output ← similar array (axes range)
  if range.isEmpty then return output
  copyto output (firstIndex output) array (range.getD 0 (JInt.lit .i64 1)) range.length

def array993GetBoolRange (toIndex : List Bool → Jl (List JInt64))
    (getindex : DenseArrayModel → List JInt64 → Jl DenseArrayModel)
    (array : DenseArrayModel) (range : List Bool) : Jl DenseArrayModel := do
  let indices ← toIndex range
  getindex array indices

def array995GetColon (similar : DenseArrayModel → Nat → Jl DenseArrayModel)
    (unsafeCopy : DenseArrayModel → DenseArrayModel → Nat → Jl DenseArrayModel)
    (array : DenseArrayModel) : Jl DenseArrayModel := do
  let length := array.data.length
  let output ← similar array length
  if length = 0 then return output
  unsafeCopy output array length

def array1005GetRangeComprehension
    (getindex : DenseArrayModel → JInt64 → Jl Int)
    (typedLiteral : List Int → Jl DenseArrayModel)
    (array : DenseArrayModel) (range : List JInt64) : Jl DenseArrayModel := do
  let values ← range.mapM (getindex array)
  typedLiteral values

def array1031SetLinear (isType : Int → Bool) (convert : Int → Jl Int)
    (setTyped : DenseArrayModel → Int → JInt64 → Jl DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (index : JInt64) : Jl DenseArrayModel := do
  let value ← if isType value then pure value else convert value
  setTyped array value index

def array1036SetLinearTyped (checkbounds : DenseArrayModel → JInt64 → Bool)
    (memorySet : DenseArrayModel → JInt64 → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (index : JInt64) : Jl DenseArrayModel :=
  if checkbounds array index then .ok (memorySet array index value) else .error .boundsError

def array1042SetCartesian (isType : Int → Bool) (convert : Int → Jl Int)
    (setTyped : DenseArrayModel → Int → List JInt64 → Jl DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (indices : List JInt64) : Jl DenseArrayModel := do
  let value ← if isType value then pure value else convert value
  setTyped array value indices

def array1047SetCartesianTyped (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (linearIndex : DenseArrayModel → List JInt64 → JInt64)
    (memorySet : DenseArrayModel → JInt64 → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (indices : List JInt64) : Jl DenseArrayModel :=
  if checkbounds array indices then
    .ok (memorySet array (linearIndex array indices) value)
  else .error .boundsError

def array1055SafeSetAny (memorySet : DenseArrayModel → JInt64 → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (index : JInt64) : DenseArrayModel :=
  memorySet array index value

def array1057SafeSetTyped := array1055SafeSetAny

def array1059SafeSetConvert (convert : Int → Jl Int)
    (safeSet : DenseArrayModel → Int → JInt64 → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) (index : JInt64) : Jl DenseArrayModel := do
  let value ← convert value
  pure (safeSet array value index)

def array1063ScatterLoop
    (getIndex : List JInt64 → Nat → JInt64)
    (getValue : List Int → Nat → Int)
    (setindex : DenseArrayModel → JInt64 → Int → DenseArrayModel) :
    DenseArrayModel → List JInt64 → List Int → Nat → Nat → DenseArrayModel
  | array, _, _, _, 0 => array
  | array, indices, values, position, fuel + 1 =>
      array1063ScatterLoop getIndex getValue setindex
        (setindex array (getIndex indices position) (getValue values position))
        indices values (position + 1) fuel

def array1063Scatter (shapeCheck : List Int → Nat → Jl Unit)
    (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (unaliasValues : DenseArrayModel → List Int → List Int)
    (unaliasIndices : DenseArrayModel → List JInt64 → List JInt64)
    (getIndex : List JInt64 → Nat → JInt64) (getValue : List Int → Nat → Int)
    (setindex : DenseArrayModel → JInt64 → Int → DenseArrayModel)
    (array : DenseArrayModel) (values : List Int) (indices : List JInt64) :
    Jl DenseArrayModel := do
  shapeCheck values indices.length
  if checkbounds array indices then pure () else throw .boundsError
  let values := unaliasValues array values
  let indices := unaliasIndices array indices
  pure (array1063ScatterLoop getIndex getValue setindex array indices values 0 values.length)

def array1078SetRange (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (shapeCheck : DenseArrayModel → Nat → Jl Unit)
    (unsafeCopy : DenseArrayModel → JInt64 → DenseArrayModel → Nat → Jl DenseArrayModel)
    (array values : DenseArrayModel) (range : List JInt64) : Jl DenseArrayModel := do
  if checkbounds array range then pure () else throw .boundsError
  shapeCheck values range.length
  if range.isEmpty then return array
  unsafeCopy array (range.getD 0 (JInt.lit .i64 1)) values range.length

def array1088SetColon (shapeCheck : DenseArrayModel → Nat → Jl Unit)
    (unsafeCopy : DenseArrayModel → DenseArrayModel → Nat → Jl DenseArrayModel)
    (array values : DenseArrayModel) : Jl DenseArrayModel := do
  let length := array.data.length
  shapeCheck values length
  if length = 0 then return array
  unsafeCopy array values length

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


structure GrowthState where
  length : Int
  memoryLength : Int
  offset : Int
  deriving Repr, DecidableEq

inductive GrowthError where
  | argument | bounds | concurrency | overflow | keyword
  deriving Repr, DecidableEq

abbrev GrowthJl (α : Type) := Except GrowthError α

def array1102Overallocation (ctlz shiftOne : Int → Int)
    (mulWrap addWrap subWrap divInt : Int → Int → Int)
    (maxInt maxSize : Int) : Int :=
  let exponent := 64 - ctlz maxSize
  let extra := addWrap (mulWrap (shiftOne (divInt (mulWrap exponent 7) 8)) 3)
    (divInt maxSize 8)
  if maxSize > subWrap maxInt extra then maxInt else addWrap maxSize extra

def array1116GrowBeginInternal
    (checkedAdd checkedMul : Int → Int → GrowthJl Int)
    (overallocation : Int → Int)
    (reuseMove allocateMove : GrowthState → Int → Int → GrowthJl GrowthState)
    (state : GrowthState) (delta len : Int) : GrowthJl GrowthState := do
  let newLength ← checkedAdd len delta
  let _ ← (if state.offset < 1 || state.offset - 1 > state.memoryLength ||
      len > state.memoryLength - (state.offset - 1) then throw .concurrency else pure ())
  let twice ← checkedMul 2 delta
  let exact ← checkedAdd len twice >>= fun value => checkedAdd value 1
  let newMemoryLength := max (overallocation len) exact
  let newOffset := (newMemoryLength - newLength) / 2 + 1
  if newLength < state.memoryLength && newOffset < state.memoryLength - newLength then
    reuseMove state delta newLength
  else allocateMove { state with memoryLength := newMemoryLength, offset := newOffset } delta newLength

def array1151GrowBegin (convert : Int → GrowthJl Int)
    (checkedAdd : Int → Int → GrowthJl Int)
    (moveRef : GrowthState → Int → GrowthState)
    (internal : GrowthState → Int → Int → GrowthJl GrowthState)
    (state : GrowthState) (rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  if delta = 0 then return state
  if delta < 0 then throw .argument
  let newLength ← checkedAdd state.length delta
  let state ← if delta ≤ state.offset - 1 then
    pure (moveRef state (1 - delta))
  else internal state delta state.length
  pure { state with length := newLength }

def array1171GrowEndInternal
    (checkedAdd : Int → Int → GrowthJl Int) (overallocation : Int → Int)
    (reuseMove allocateMove : GrowthState → Int → Int → GrowthJl GrowthState)
    (state : GrowthState) (delta len : Int) : GrowthJl GrowthState := do
  let newLength ← checkedAdd len delta
  let _ ← (if state.offset < 1 || state.offset - 1 > state.memoryLength ||
      len > state.memoryLength - (state.offset - 1) then throw .concurrency else pure ())
  let needed ← checkedAdd (state.offset - 1) newLength
  if state.offset - 1 > newLength && state.offset - 1 - newLength > newLength / 4 then
    return ← reuseMove state newLength (newLength / 8 + 1)
  else
    return ← (allocateMove { state with memoryLength := max (overallocation state.memoryLength) needed }
      newLength state.offset)

def array1212GrowEnd (convert : Int → GrowthJl Int)
    (checkedAdd : Int → Int → GrowthJl Int)
    (internal : GrowthState → Int → Int → GrowthJl GrowthState)
    (state : GrowthState) (rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  if delta < 0 then throw .argument
  let newLength ← checkedAdd state.length delta
  let needed ← checkedAdd (state.offset - 1) newLength
  let state ← if state.memoryLength < needed then internal state delta state.length else pure state
  pure { state with length := newLength }

def array1230GrowAt (convert : Int → GrowthJl Int)
    (growBegin growEnd : GrowthState → Int → GrowthJl GrowthState)
    (checkedAdd : Int → Int → GrowthJl Int)
    (frontMove backMove allocateMove : GrowthState → Int → Int → GrowthJl GrowthState)
    (maxInt : Int) (state : GrowthState) (rawIndex rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  let index ← convert rawIndex
  if index = 1 then return ← growBegin state delta
  if state.length < maxInt && index = state.length + 1 then return ← growEnd state delta
  if delta < 0 then throw .argument
  if !(1 < index && index ≤ state.length) then throw .bounds
  let newLength ← checkedAdd state.length delta
  let preferStart := index ≤ state.length / 2
  if preferStart && delta ≤ state.offset - 1 then
    frontMove { state with length := newLength, offset := state.offset - delta } index delta
  else if !preferStart && state.memoryLength ≥ state.offset - 1 + newLength then
    backMove { state with length := newLength } index delta
  else allocateMove { state with length := newLength } index delta

def array1278DeleteBegin (convert : Int → GrowthJl Int)
    (unsetRange : GrowthState → Int → Int → GrowthState)
    (moveRef : GrowthState → Int → GrowthState)
    (state : GrowthState) (rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  if delta < 0 || state.length < delta then throw .argument
  let state := unsetRange state 1 delta
  let newLength := state.length - delta
  let state := { state with length := newLength }
  if newLength = 0 then return state
  pure (moveRef state (delta + 1))

def array1296DeleteEnd (convert : Int → GrowthJl Int)
    (unsetRange : GrowthState → Int → Int → GrowthState)
    (state : GrowthState) (rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  if delta < 0 || state.length < delta then throw .argument
  let newLength := state.length - delta
  pure { (unsetRange state (newLength + 1) state.length) with length := newLength }

def array1312DeleteAt (copy : GrowthState → Int → Int → Int → GrowthJl GrowthState)
    (deleteBegin deleteEnd : GrowthState → Int → GrowthJl GrowthState)
    (state : GrowthState) (index delta : Int) : GrowthJl GrowthState := do
  if delta < 0 then throw .argument
  if !(1 ≤ index && index ≤ state.length) then throw .bounds
  if index + delta > state.length + 1 then throw .bounds
  if 2 * index + delta ≤ state.length then
    let state ← copy state (1 + delta) 1 (index - 1)
    deleteBegin state delta
  else
    let state ← copy state index (index + delta) (state.length + 1 - delta - index)
    deleteEnd state delta

def array1564Resize (convert : Int → GrowthJl Int)
    (growBegin growEnd deleteBegin deleteEnd : GrowthState → Int → GrowthJl GrowthState)
    (state : GrowthState) (rawLength : Int) (first : Bool) : GrowthJl GrowthState := do
  let newLength ← convert rawLength
  if state.length < newLength then
    if first then growBegin state (newLength - state.length)
    else growEnd state (newLength - state.length)
  else if newLength != state.length then
    if newLength < 0 then throw .argument
    if first then deleteBegin state (state.length - newLength)
    else deleteEnd state (state.length - newLength)
  else pure state

def array1617Sizehint
    (convert : Int → GrowthJl Int)
    (reallocateCopy : GrowthState → Int → Bool → GrowthJl GrowthState)
    (growBegin growEnd : GrowthState → Int → GrowthJl GrowthState)
    (state : GrowthState) (rawSize : Int) (first shrink : Bool) : GrowthJl GrowthState := do
  let requested ← convert rawSize
  let size := max requested state.length
  let increment := size - state.length
  if size ≤ state.memoryLength then
    if !shrink || state.memoryLength - size ≤ state.memoryLength / 8 then return state
    reallocateCopy state size first
  else if first then do
    let grown ← growBegin state increment
    pure { grown with length := state.length }
  else do
    let grown ← growEnd state increment
    pure { grown with length := state.length }

def array1652Kwcall (getBool : Int → Bool → GrowthJl Bool)
    (extraEmpty : Bool) (kwerr : GrowthJl GrowthState)
    (sizehint : GrowthState → Int → GrowthJl GrowthState)
    (state : GrowthState) (size : Int) : GrowthJl GrowthState := do
  let _first ← getBool 0 false
  let _shrink ← getBool 1 true
  if !extraEmpty then kwerr else sizehint state size

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


def array1114NewMemory (allocateLike : List Int → Int → Jl (List Int))
    (memory : List Int) (newLength : Int) : Jl (List Int) :=
  allocateLike memory newLength

def array1358Push (sameType : Int → Bool) (convert : Int → Jl Int)
    (pushTyped : List Int → Int → Jl (List Int))
    (array : List Int) (item : Int) : Jl (List Int) := do
  let item ← if sameType item then pure item else convert item
  pushTyped array item

def array1366PushTyped (growEnd : List Int → Nat → Jl (List Int))
    (safeSet : List Int → Nat → Int → List Int)
    (array : List Int) (item : Int) : Jl (List Int) := do
  let array ← growEnd array 1
  pure (safeSet array array.length item)

def array1373PushAny := array1366PushTyped

def array1378PushAnyLoop (safeSet : List Int → Nat → Int → List Int) :
    List Int → Nat → List Int → List Int
  | array, _, [] => array
  | array, index, item :: rest =>
      array1378PushAnyLoop safeSet (safeSet array index item) (index + 1) rest

def array1378PushAnyMany (growEnd : List Int → Nat → Jl (List Int))
    (safeSet : List Int → Nat → Int → List Int)
    (array items : List Int) : Jl (List Int) := do
  let oldLength := array.length
  let array ← growEnd array items.length
  pure (array1378PushAnyLoop safeSet array (oldLength + 1) items)

def array1427Append (isTuple sameObject : Bool) (convertAll : List Int → Jl (List Int))
    (convertLength : Nat → Jl Int) (growEnd : List Int → Int → Jl (List Int))
    (copyto : List Int → Int → List Int → Int → Int → Jl (List Int))
    (array items : List Int) : Jl (List Int) := do
  let items ← if isTuple then convertAll items else pure items
  let count ← convertLength items.length
  let array ← growEnd array count
  let source := if sameObject && !isTuple then array else items
  copyto array (array.length - count + 1) source 1 count

def array1435AppendIterator (iteratorSize : List Int → Int)
    (appendInner : List Int → Int → List Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) :=
  appendInner array (iteratorSize iterator) iterator

def array1436PushMany (append : List Int → List Int → Jl (List Int))
    (array items : List Int) : Jl (List Int) := append array items

def array1437AppendManyLoop (append : List Int → List Int → Jl (List Int)) :
    List Int → List (List Int) → Jl (List Int)
  | array, [] => .ok array
  | array, items :: rest => do
      let array ← append array items
      array1437AppendManyLoop append array rest

def array1439AppendSized (convertLength : Nat → Jl Int)
    (sizehint : List Int → Int → Bool → Jl (List Int))
    (push : List Int → Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) := do
  let count ← convertLength iterator.length
  let array ← sizehint array (array.length + count) false
  iterator.foldlM push array

def array1447AppendUnknown (push : List Int → Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) := iterator.foldlM push array

def array1485Prepend (isTuple sameObject : Bool)
    (convertAll : List Int → Jl (List Int))
    (unalias : List Int → List Int → List Int)
    (growBegin : List Int → Nat → Jl (List Int))
    (copyto : List Int → Int → List Int → Int → Nat → Jl (List Int))
    (array items : List Int) : Jl (List Int) := do
  let items ← if isTuple then convertAll items
    else pure (if sameObject then items else unalias array items)
  let count := items.length
  let array ← growBegin array count
  let source := if sameObject && !isTuple then array else items
  copyto array 1 source (source.length - count + 1) count

def array1500PrependIterator (iteratorSize : List Int → Int)
    (prependInner : List Int → Int → List Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) :=
  prependInner array (iteratorSize iterator) iterator

def array1501PushFirstMany (prepend : List Int → List Int → Jl (List Int))
    (array items : List Int) : Jl (List Int) := prepend array items

def array1502PrependForward (prepend : List Int → List Int → Jl (List Int)) :
    List Int → List (List Int) → Jl (List Int)
  | array, [] => .ok array
  | array, items :: rest => do
      let array ← prepend array items
      array1502PrependForward prepend array rest

def array1502PrependManyLoop (prepend : List Int → List Int → Jl (List Int))
    (array : List Int) (collections : List (List Int)) : Jl (List Int) :=
  array1502PrependForward prepend array collections.reverse

def array1504PrependSized (oneBased : List Int → Jl Unit)
    (convertLength : Nat → Jl Int)
    (sizehint : List Int → Int → Bool → Bool → Jl (List Int))
    (pushFirst : List Int → Int → Jl (List Int))
    (reverse : List Int → Int → Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) := do
  oneBased array
  let count ← convertLength iterator.length
  let array ← sizehint array (array.length + count) true false
  let (array, inserted) ← iterator.foldlM (fun (state : List Int × Int) item => do
    let array ← pushFirst state.1 item
    pure (array, state.2 + 1)) (array, 0)
  reverse array 1 inserted

def array1517PrependUnknown (pushFirst : List Int → Int → Jl (List Int))
    (reverse : List Int → Int → Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) := do
  let (array, inserted) ← iterator.foldlM (fun (state : List Int × Int) item => do
    let array ← pushFirst state.1 item
    pure (array, state.2 + 1)) (array, 0)
  reverse array 1 inserted

def array1777PushFirst (sameType : Int → Bool) (convert : Int → Jl Int)
    (pushTyped : List Int → Int → Jl (List Int))
    (array : List Int) (item : Int) : Jl (List Int) := do
  let item ← if sameType item then pure item else convert item
  pushTyped array item

def array1782PushFirstTyped (growBegin : List Int → Nat → Jl (List Int))
    (safeSet : List Int → Nat → Int → List Int)
    (array : List Int) (item : Int) : Jl (List Int) := do
  let array ← growBegin array 1
  pure (safeSet array 1 item)

def array1789PushFirstAny := array1782PushFirstTyped

def array1794PushFirstMany (growBegin : List Int → Nat → Jl (List Int))
    (safeSet : List Int → Nat → Int → List Int)
    (array items : List Int) : Jl (List Int) := do
  let array ← growBegin array items.length
  pure (array1378PushAnyLoop safeSet array 1 items)

def array1866Insert (sameType : Int → Bool) (convert : Int → Jl Int)
    (insertTyped : List Int → Int → Int → Jl (List Int))
    (array : List Int) (index item : Int) : Jl (List Int) := do
  let item ← if sameType item then pure item else convert item
  insertTyped array index item

def array1871InsertTyped (growAt : List Int → Int → Nat → Jl (List Int))
    (setindex : List Int → Int → Int → List Int)
    (array : List Int) (index item : Int) : Jl (List Int) := do
  let array ← growAt array index 1
  pure (setindex array index item)

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


inductive DeleteRouteError where
  | empty | bounds
  deriving Repr, DecidableEq

abbrev DeleteJl (α : Type) := Except DeleteRouteError α

def array1700Pop (getLast : List Int → Int)
    (deleteEnd : List Int → Nat → List Int) (array : List Int) : DeleteJl (Int × List Int) :=
  if array.isEmpty then .error .empty
  else .ok (getLast array, deleteEnd array 1)

def array1741PopAt (getindex : List Int → Int → DeleteJl Int)
    (deleteAt : List Int → Int → Nat → DeleteJl (List Int))
    (array : List Int) (index : Int) : DeleteJl (Int × List Int) := do
  let value ← getindex array index
  let array ← deleteAt array index 1
  pure (value, array)

def array1748PopAtDefault (getindex : List Int → Int → Int)
    (deleteAt : List Int → Int → Nat → List Int)
    (array : List Int) (index default : Int) : Int × List Int :=
  if 1 ≤ index && index ≤ array.length then
    (getindex array index, deleteAt array index 1)
  else (default, array)

def array1836PopFirst (getFirst : List Int → Int)
    (deleteBegin : List Int → Nat → List Int) (array : List Int) :
    DeleteJl (Int × List Int) :=
  if array.isEmpty then .error .empty
  else .ok (getFirst array, deleteBegin array 1)

def array1945DeleteIndices (delete : List Int → List Int → DeleteJl (List Int))
    (array indices : List Int) : DeleteJl (List Int) := delete array indices

def array1946DeleteVector (toIndices : List Int → List Int → DeleteJl (List Int))
    (delete : List Int → List Int → DeleteJl (List Int))
    (array indices : List Int) : DeleteJl (List Int) := do
  let indices ← toIndices array indices
  delete array indices

def array1949NowherePush (_item : Int) : Unit := ()
def array1950NowhereGrow (_count : Nat) : Unit := ()

def array1952PushDeleted (isassigned : List Int → Int → Bool)
    (getindex : List Int → Int → Int)
    (push : List Int → Int → List Int) (growEnd : List Int → Nat → List Int)
    (deleted array : List Int) (index : Int) : List Int :=
  if isassigned array index then push deleted (getindex array index)
  else growEnd deleted 1

def array1961CopyItem (isassigned : List Int → Int → Bool)
    (getindex : List Int → Int → Int) (setindex : List Int → Int → Int → List Int)
    (unset : List Int → Int → List Int) (array : List Int) (dest src : Int) : List Int :=
  if isassigned array src then setindex array dest (getindex array src)
  else unset array dest

def array2153SpliceIndices (emptyLike : List Int → List Int)
    (delete : List Int → List Int → List Int → DeleteJl (List Int × List Int))
    (array indices : List Int) : DeleteJl (List Int × List Int) :=
  let deleted := emptyLike array
  delete array indices deleted

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


def array2155Empty (deleteEnd : List Int → Nat → List Int)
    (array : List Int) : List Int := deleteEnd array array.length

def array2161CmpBytes (pointer : List UInt8 → Int)
    (memcmp : Int → Int → Nat → Int) (cmpLength : Nat → Nat → Int)
    (left right : List UInt8) : Int :=
  let result := memcmp (pointer left) (pointer right) (min left.length right.length)
  if result < 0 then -1 else if result > 0 then 1 else cmpLength left.length right.length

def array2176EqualBits (size : List Int → List Int)
    (pointer : List Int → Int) (sizeofElement : Nat)
    (memcmp : Int → Int → Nat → Int) (left right : List Int) : Bool :=
  if size left = size right then
    memcmp (pointer left) (pointer right) (sizeofElement * left.length) = 0
  else false

def array2193EqualBitVector (pointer : List Int → Int) (sizeofElement : Nat)
    (memcmp : Int → Int → Nat → Int) (left right : List Int) : Bool :=
  if left.length = right.length then
    memcmp (pointer left) (pointer right) (sizeofElement * left.length) = 0
  else false

def array2271ReverseDims (route : List Int → Int → Jl (List Int))
    (array : List Int) (dims : Int) : Jl (List Int) := route array dims

def array2272ReverseColon (reverseWindow : List Int → Int → Int → Jl (List Int))
    (first last : List Int → Int) (array : List Int) : Jl (List Int) :=
  reverseWindow array (first array) (last array)

def array2273ReverseTuple (route : List Int → Int → Jl (List Int))
    (array : List Int) (dim : Int) : Jl (List Int) := route array dim

def array2274ReverseDim (throwArg : Int → Jl Unit)
    (colonRoute : List Int → Jl (List Int)) (array : List Int) (dim : Int) : Jl (List Int) := do
  if dim = 1 then pure () else throwArg dim
  colonRoute array

def array2281ReverseIndex (linearIndices : List Int → List Int)
    (first last : List Int → Int) (array : List Int) (index : Int) : Int :=
  let linear := linearIndices array
  first linear + last linear - index

def array2288Midpoint (subWrap : Int → Int → Int)
    (logicalShiftOne : Int → Int) (addWrap : Int → Int → Int)
    (low high : Int) : Int :=
  addWrap low (logicalShiftOne (subWrap high low))

def array2289MidpointPromoted (promote : Int → Int → Int × Int)
    (midpoint : Int → Int → Int) (low high : Int) : Int :=
  let promoted := promote low high
  midpoint promoted.1 promoted.2

inductive ConcatError where
  | dimensionMismatch | assertion
  deriving Repr, DecidableEq

abbrev ConcatJl (α : Type) := Except ConcatError α

def array2337VcatEmpty (_ : Unit) : List Int := []
def array2338HcatEmpty (_ : Unit) : List Int := []

def array2340Hcat (vectors : List (List Int)) : ConcatJl (List (List Int)) :=
  match vectors with
  | [] => .ok []
  | first :: rest =>
      if rest.any (fun vector => vector.length != first.length) then
        .error .dimensionMismatch
      else .ok (List.range first.length |>.map fun i =>
        vectors.map fun vector => vector.getD i 0)

def array2349HcatGeneric (cat : List (List Int) → Int → ConcatJl (List Int))
    (vectors : List (List Int)) : ConcatJl (List Int) := cat vectors 2

def array2351Total (addWrap : Int → Int → Int) : List (List Int) → Int
  | [] => 0
  | vector :: rest => addWrap vector.length (array2351Total addWrap rest)

def array2351CopyLoop
    (copy : List Int → Int → List Int → Nat → ConcatJl (List Int)) :
    List Int → Int → List (List Int) → ConcatJl (List Int)
  | output, _, [] => .ok output
  | output, offset, vector :: rest => do
      if offset + vector.length > output.length + 1 then throw .assertion
      let output ← copy output offset vector vector.length
      array2351CopyLoop copy output (offset + vector.length) rest

def array2351Vcat (addWrap : Int → Int → Int)
    (allocate : Int → ConcatJl (List Int))
    (copy : List Int → Int → List Int → Nat → ConcatJl (List Int))
    (vectors : List (List Int)) : ConcatJl (List Int) := do
  let length := array2351Total addWrap vectors
  let output ← allocate length
  array2351CopyLoop copy output 1 vectors

def array2366VcatGeneric (cat : List (List Int) → Int → ConcatJl (List Int))
    (vectors : List (List Int)) : ConcatJl (List Int) := cat vectors 1

def array2368CatIntegers (reshape : List Int → List Int → ConcatJl (List Int))
    (rank : Nat) (values : List Int) : ConcatJl (List Int) :=
  reshape values (List.replicate (rank - 1) (1 : Int) ++ [(values.length : Int)])

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


def array2404FindNext (identity : Int → Bool)
    (findnext : (Int → Bool) → List Int → Int → Option Int)
    (array : List Int) (start : Int) : Option Int :=
  findnext identity array start

def array2441FindFirst (identity : Int → Bool)
    (findfirst : (Int → Bool) → List Int → Option Int)
    (array : List Int) : Option Int := findfirst identity array

def array2444FindFirstArray (keys : List Int → List Int)
    (first : List Int → Int)
    (findnext : List Int → Int → Option Int) (array : List Int) : Option Int :=
  findnext array (first (keys array))

def array2523FindFirstPairs : List (Int × Int) → (Int → Bool) → Option Int
  | [], _ => none
  | (index, value) :: rest, predicate =>
      if predicate value then some index else array2523FindFirstPairs rest predicate

def array2531FindFirstIndexed (keys : List Int → List Int)
    (first : List Int → Int)
    (findnext : (Int → Bool) → List Int → Int → Option Int)
    (predicate : Int → Bool) (array : List Int) : Option Int :=
  findnext predicate array (first (keys array))

def array2591FindPrev (identity : Int → Bool)
    (findprev : (Int → Bool) → List Int → Int → Option Int)
    (array : List Int) (start : Int) : Option Int :=
  findprev identity array start

def array2629FindLast (identity : Int → Bool)
    (findlast : (Int → Bool) → List Int → Option Int)
    (array : List Int) : Option Int := findlast identity array

def array2632FindLastArray (keys : List Int → List Int)
    (last : List Int → Int)
    (findprev : List Int → Int → Option Int) (array : List Int) : Option Int :=
  findprev array (last (keys array))

def array2716FindLastPairs (pairs : List (Int × Int))
    (predicate : Int → Bool) : Option Int :=
  array2523FindFirstPairs pairs.reverse predicate

def array2724FindLastIndexed (keys : List Int → List Int)
    (last : List Int → Int)
    (findprev : (Int → Bool) → List Int → Int → Option Int)
    (predicate : Int → Bool) (array : List Int) : Option Int :=
  findprev predicate array (last (keys array))

def array2728FindLastUnit (findfirst : (Int → Bool) → List Int → Option Int)
    (predicate : Int → Bool) (range : List Int) : Option Int :=
  findfirst predicate range

def array2733FindLastStep := array2728FindLastUnit

def array2534FindOneTo (convert : Int → Jl Int) (value stop : Int) : Jl (Option Int) :=
  if 1 ≤ value && value ≤ stop then (convert value).map some else .ok none

def array2537FindZeroOneTo (_ : Unit) : Option Int := none

def array2538FindOneOneTo (oneunit : Int → Int) (keyType stop : Int) : Option Int :=
  if stop < 1 then none else some (oneunit keyType)

def array2540FindUnitRange (first last firstKey : Int)
    (convertOffset : Int → Int) (value : Int) : Option Int :=
  if !(first ≤ value && value ≤ last) then none
  else some (firstKey + convertOffset (value - first))

def array2546FindStep (minimum maximum first step : JInt64)
    (convert : JInt64 → Jl Int) (value : JInt64) : Jl (Option Int) := do
  if maximum < minimum then return none
  if value < minimum || maximum < value then return none
  let difference := value - first
  let remainder ← JInt.remInt difference step
  if remainder.val != 0 then return none
  let quotient ← JInt.div difference step
  (convert (quotient + JInt.lit .i64 1)).map some

def array2554FindZeroRange (first : List Int → Int) (zero : Int → Int)
    (findfirst : Int → List Int → Option Int) (range : List Int) : Option Int :=
  findfirst (zero (first range)) range

def array2555FindOneRange (first : List Int → Int) (one : Int → Int)
    (findfirst : Int → List Int → Option Int) (range : List Int) : Option Int :=
  findfirst (one (first range)) range

def array2789FindAll (defaultEltype : List Int → Option Int)
    (defaultKeyType : List Int → Int)
    (collectTyped : Int → List Int → List Int)
    (collect : List Int → List Int)
    (predicate : Int → Bool) (pairs : List (Int × Int)) : List Int :=
  let selected := (pairs.filter fun pair => predicate pair.2).map (·.1)
  match defaultEltype selected with
  | none => collectTyped (defaultKeyType selected) selected
  | some _ => collect selected

def array2796FindAllBroadcast (broadcast : (Int → Bool) → List Int → List Bool)
    (findall : List Bool → List Int) (predicate : Int → Bool)
    (array : List Int) : List Int := findall (broadcast predicate array)

def array2838FindAll (pairs : List (Int × Bool)) : List Int :=
  (pairs.filter fun pair => pair.2).map (·.1)

def array2843FindAllBoolLoop : List (Int × Bool) → List Int
  | [] => []
  | (index, value) :: rest =>
      if value then index :: array2843FindAllBoolLoop rest else array2843FindAllBoolLoop rest

def array2843FindAllBool (count : List Bool → Nat)
    (pairs : List (Int × Bool)) : List Int :=
  (array2843FindAllBoolLoop pairs).take (count (pairs.map (·.2)))

def array2856FindAllBoolScalar (value : Bool) : List Int := if value then [1] else []
def array2857FindAllNumber (predicate : Int → Bool) (value : Int) : List Int :=
  if predicate value then [1] else []
def array2858FindAllInNumber (contains : Int → List Int → Bool)
    (value : Int) (set : List Int) : List Int := if contains value set then [1] else []

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


def array2903FindIn (contains : Int → List Int → Bool)
    (array set : List Int) : List Nat :=
  ((List.range array.length).zip array).filterMap fun (index, value) =>
    if contains value set then some (index + 1) else none

def array2910FindInConvert (makeSet : List Int → List Int)
    (findin : List Int → List Int → List Nat) (array values : List Int) : List Nat :=
  findin array (makeSet values)

def array2915SortedFindLoop (isless : Int → Int → Bool) :
    Nat → List Int → List Int → Nat → Nat → List Nat → List Nat
  | 0, _, _, _, _, output => output.reverse
  | fuel + 1, left, right, i, j, output =>
      if i ≥ left.length || j ≥ right.length then output.reverse
      else
        let l := left.getD i 0
        let r := right.getD j 0
        if isless l r then array2915SortedFindLoop isless fuel left right (i + 1) j output
        else if isless r l then array2915SortedFindLoop isless fuel left right i (j + 1) output
        else array2915SortedFindLoop isless fuel left right (i + 1) j ((i + 1) :: output)

def array2915SortedFind (isless : Int → Int → Bool)
    (left right : List Int) : List Nat :=
  array2915SortedFindLoop isless (left.length + right.length + 1) left right 0 0 []

def array2957FindAllIn (issorted : List Int → Bool)
    (sortedFind findIn : List Int → List Int → List Nat)
    (array values : List Int) : List Nat :=
  if issorted array && issorted values then sortedFind array values else findIn array values

def array3020FilterLoop (setindex : List Int → Nat → Int → List Int)
    (predicate : Int → Bool) : List Int → List Int → Nat → List Int × Nat
  | [], output, index => (output, index)
  | value :: rest, output, index =>
      let output := setindex output index value
      let index := if predicate value then index + 1 else index
      array3020FilterLoop setindex predicate rest output index

def array3020FilterArray (allocate : Nat → List Int)
    (setindex : List Int → Nat → Int → List Int) (resize : List Int → Nat → List Int)
    (sizehint : List Int → Nat → List Int) (predicate : Int → Bool)
    (array : List Int) : List Int :=
  let result := array3020FilterLoop setindex predicate array (allocate array.length) 1
  let output := resize result.1 (result.2 - 1)
  sizehint output output.length

def array3032FilterAbstract (linear : Bool)
    (logicalIndex : List Int → List Bool → List Int)
    (integerIndex : List Int → List Int → List Int)
    (allocate : Nat → List Int) (setindex : List Int → Nat → Int → List Int)
    (resize : List Int → Nat → List Int) (empty : List Int → List Int)
    (sizehint : List Int → Nat → List Int)
    (predicate : Int → Bool) (array : List Int) : List Int :=
  if !linear then logicalIndex array (array.map predicate)
  else
    let result := array3020FilterLoop setindex predicate array (allocate array.length) 1
    let indices := resize result.1 (result.2 - 1)
    let output := integerIndex array indices
    let indices := empty indices
    let _ := sizehint indices 0
    output

def array3105FilterFix (filter : (Int → Bool) → List Int → List Int)
    (predicate : Int → Bool) : List Int → List Int :=
  fun array => filter predicate array

def array3134KeepAt (keep : List Int → List Int → Jl (List Int))
    (array indices : List Int) : Jl (List Int) := keep array indices

def array3159KeepMask (keep : List Int → List Bool → Jl (List Int))
    (array : List Int) (mask : List Bool) : Jl (List Int) := keep array mask

def array3164UniqueFilter (predicate : Int → List Int → Bool)
    (update : List Int → Int → List Int) (state : List Int) :
    Int → Bool × List Int :=
  fun value => if predicate value state then (true, update state value) else (false, state)

def array3174GrowFilter
    (uniqueFilter : (Int → List Int → Bool) → (List Int → Int → List Int) →
      List Int → (Int → Bool × List Int))
    (notIn : Int → List Int → Bool) (push : List Int → Int → List Int)
    (seen : List Int) : Int → Bool × List Int := uniqueFilter notIn push seen

def array3175ShrinkFilter
    (uniqueFilter : (Int → List Int → Bool) → (List Int → Int → List Int) →
      List Int → (Int → Bool × List Int))
    (isIn : Int → List Int → Bool) (pop : List Int → Int → List Int)
    (keep : List Int) : Int → Bool × List Int := uniqueFilter isIn pop keep

def array3177Grow (filter : (Int → Bool × List Int) → List Int → List Int)
    (mapfilter : (Int → Bool × List Int) → List Int → List Int → List Int)
    (predicate : Int → Bool × List Int) (vector : List Int)
    (iterators : List (List Int)) : List Int :=
  iterators.foldl (fun result iterator => mapfilter predicate iterator result)
    (filter predicate vector)

def array3185Union (makeSeen : List Int → List Int)
    (growFilter : List Int → Int → Bool × List Int)
    (grow : (Int → Bool × List Int) → List Int → List (List Int) → List Int)
    (vector : List Int) (iterators : List (List Int)) : List Int :=
  grow (growFilter (makeSeen vector)) vector iterators

def array3188Symdiff := array3185Union

def array3191Shrink (unique : List Int → List Int)
    (shrinkSet : List Int → List (List Int) → List Int)
    (filterIn : List Int → List Int → List Int)
    (vector : List Int) (iterators : List (List Int)) : List Int :=
  let vector := unique vector
  let seen := shrinkSet vector iterators
  filterIn seen vector

def array3198Intersect (shrink : List Int → List (List Int) → List Int)
    (vector : List Int) (iterators : List (List Int)) : List Int := shrink vector iterators

def array3199Setdiff := array3198Intersect

def array3201VectorFilter (predicate : Int → Bool) (vector : List Int) : List Int :=
  vector.filter predicate

def array3203Intersect (promote : List Int → List (List Int) → Int)
    (setIntersect : Int → List Int → List (List Int) → List Int)
    (vectorFilter : Int → (Int → Bool) → List Int → List Int)
    (shrinkPredicate : List Int → Int → Bool)
    (iterator : List Int) (iterators : List (List Int)) : List Int :=
  let type := promote iterator iterators
  let keep := setIntersect type iterator iterators
  vectorFilter type (shrinkPredicate keep) iterator

def array3209Setdiff (setDiff : List Int → List (List Int) → List Int)
    (vectorFilter : (Int → Bool) → List Int → List Int)
    (shrinkPredicate : List Int → Int → Bool)
    (iterator : List Int) (iterators : List (List Int)) : List Int :=
  let keep := setDiff iterator iterators
  vectorFilter (shrinkPredicate keep) iterator

def array3215IntersectRange (contains : Int → List Int → Bool)
    (unique : List Int → List Int) (vector range : List Int) : List Int :=
  unique (vector.filter fun value => contains value range)

def array3221IntersectRangeReverse (intersect : List Int → List Int → List Int)
    (range vector : List Int) : List Int := intersect vector range

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


def indcopyTrailing (mulWrap : Int → Int → Int)
    (sizes : List Int) (start : Nat) : Int :=
  (sizes.drop start).foldl mulWrap 1

def array2970Indcopy (mulWrap : Int → Int → Int)
    (findin : List Int → List Int → List Int)
    (sizes : List Int) (indices : List (List Int)) :
    Jl (List (List Int) × List (List Int)) :=
  let n := indices.length
  if n = 0 then .error .boundsError
  else
    let trailing := indcopyTrailing mulWrap sizes (n - 1)
    let destination := (List.range n).map fun i =>
      findin (indices.getD i [])
        (List.range (if i + 1 < n then (sizes.getD i 0).toNat else trailing.toNat) |>.map
          fun x => ((x + 1 : Nat) : Int))
    let source := (List.range n).map fun i =>
      let positions := destination.getD i []
      positions.map fun position => (indices.getD i []).getD (position - 1).toNat 0
    .ok (destination, source)

def array2981IndcopyTuple := array2970Indcopy

inductive RangeIndexInput where
  | bool (value : Bool)
  | integer (value : Int)
  deriving Repr, DecidableEq

def array3224RangeGet (getindex : List Int → Int → Jl Int)
    (range : List Int) (index : RangeIndexInput) : Jl Int :=
  match index with
  | .bool _ => .error (.argumentError "invalid Bool index")
  | .integer value => getindex range value

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov

open JuliaLean.base.range (JlX)


inductive CollectSize where
  | unknown | length | shape
  deriving Repr, DecidableEq

def array771Collect (iteratorEltype : List Int → Int)
    (iteratorSize : List Int → CollectSize)
    (collect : Int → List Int → Int → CollectSize → Jl (List Int))
    (iterator : List Int) : Jl (List Int) :=
  collect 1 iterator (iteratorEltype iterator) (iteratorSize iterator)

def array773CollectArray (axes : List Int → List Int)
    (collectIndices : List Int → List Int → Jl (List Int))
    (array : List Int) : Jl (List Int) := collectIndices (axes array) array

def array775CollectSimilar (iteratorEltype : List Int → Int)
    (iteratorSize : List Int → CollectSize)
    (collect : Int → List Int → Int → CollectSize → Jl (List Int))
    (container : Int) (iterator : List Int) : Jl (List Int) :=
  collect container iterator (iteratorEltype iterator) (iteratorSize iterator)

def array777CollectSized (eltype : List Int → Int)
    (similarShape : List Int → CollectSize → Int)
    (similarFor : Int → Int → List Int → CollectSize → Int → Jl (List Int))
    (copyto : List Int → List Int → Jl (List Int))
    (container : Int) (iterator : List Int) (size : CollectSize) : Jl (List Int) := do
  let dest ← similarFor container (eltype iterator) iterator size (similarShape iterator size)
  copyto dest iterator

def array780CollectUnknown (eltype : List Int → Int)
    (similarFor : Int → Int → List Int → Jl (List Int))
    (push : List Int → Int → Jl (List Int))
    (container : Int) (iterator : List Int) : Jl (List Int) := do
  let dest ← similarFor container (eltype iterator) iterator
  iterator.foldlM push dest

def array788CollectZero (eltype : List Int → Int) (allocate : Int → Jl (List Int))
    (copy : List Int → List Int → Jl (List Int)) (array : List Int) : Jl (List Int) := do
  let dest ← allocate (eltype array)
  if array.isEmpty then return dest
  copy dest array

def array793CollectOneTo (eltype : List Int → Int)
    (lengths : List Int → List Int) (allocate : Int → List Int → Jl (List Int))
    (copy : List Int → List Int → Jl (List Int))
    (indices array : List Int) : Jl (List Int) := do
  let dest ← allocate (eltype array) (lengths indices)
  if array.isEmpty then return dest
  copy dest array

def array798CollectIndices (eltype : List Int → Int)
    (lengths : List Int → List Int) (allocate : Int → List Int → Jl (List Int))
    (axes cartesian : List Int → List Int)
    (copy : List Int → List Int → List Int → List Int → Jl (List Int))
    (indices array : List Int) : Jl (List Int) := do
  let dest ← allocate (eltype array) (lengths indices)
  copy dest (cartesian (axes dest)) array (cartesian indices)

def array805IteratorUpperLoop (iterateNext : Int → Option (Int × Int))
    (barrier : Unit → Bool) : Nat → Option (Int × Int) → Except Unit Int
  | 0, _ => .error ()
  | _ + 1, none => .error ()
  | fuel + 1, some (value, state) =>
      if barrier () then .ok value
      else array805IteratorUpperLoop iterateNext barrier fuel (iterateNext state)

def array805IteratorUpper (iterateFirst : Unit → Option (Int × Int))
    (iterateNext : Int → Option (Int × Int)) (barrier : Unit → Bool)
    (fuel : Nat) : Except Unit Int :=
  array805IteratorUpperLoop iterateNext barrier fuel (iterateFirst ())

def array821DefaultEltype (isGenerator : Int → Bool) (functionIsType : Int → Bool)
    (generatorFunction : Int → Int) (returnType : Int → Int)
    (promoteUnion : Int → Int) (iterator : Int) : Int :=
  let type := if isGenerator iterator && functionIsType iterator then
    generatorFunction iterator else returnType iterator
  promoteUnion type

def array833CollectGenerator (iteratorSize : Int → CollectSize)
    (defaultEltype : Int → Int) (grow : Int → Int → JlX Int)
    (similarShape : Int → CollectSize → Int)
    (iterate : Int → Option (Int × Int))
    (arrayFor : Int → CollectSize → Int → JlX Int)
    (collectFirst : Int → Int → Int → Int → JlX Int)
    (iterator : Int) : JlX Int := do
  let size := iteratorSize iterator
  let elementType := defaultEltype iterator
  if size = .unknown then return ← grow elementType iterator
  let shape := similarShape iterator size
  match iterate iterator with
  | none => arrayFor elementType size shape
  | some (first, state) => do
      let dest ← arrayFor first size shape
      collectFirst dest first iterator state

def array855CollectUnknownEltype (defaultEltype : Int → Int)
    (similar : Int → Int → Int → JlX Int) (grow : Int → Int → JlX Int)
    (container iterator : Int) : JlX Int := do
  let dest ← similar container (defaultEltype iterator) iterator
  grow dest iterator

def array858CollectKnownSize (defaultEltype : Int → Int)
    (similarShape : Int → CollectSize → Int)
    (iterate : Int → Option (Int × Int))
    (similar : Int → Int → Int → CollectSize → Int → JlX Int)
    (collectFirst : Int → Int → Int → Int → JlX Int)
    (container iterator : Int) (size : CollectSize) : JlX Int := do
  let elementType := defaultEltype iterator
  let shape := similarShape iterator size
  match iterate iterator with
  | none => similar container elementType iterator size shape
  | some (first, state) => do
      let dest ← similar container first iterator size shape
      collectFirst dest first iterator state

def array875CollectFirstArray (firstLinear : Int → Int)
    (setindex : Int → Int → Int → Int) (collectTo : Int → Int → Int → Int → JlX Int)
    (dest first iterator state : Int) : JlX Int :=
  let index := firstLinear dest
  collectTo (setindex dest index first) iterator (index + 1) state

def array881CollectFirstGeneric (push : Int → Int → Int)
    (grow : Int → Int → Int → JlX Int) (dest first iterator state : Int) : JlX Int :=
  grow (push dest first) iterator state

def array886Widen (promote : Int → Int → Int) (similar : Int → Int → Int)
    (firstLinear : Int → Int) (copy : Int → Int → Int → Int → Int → Int)
    (setindex : Int → Int → Int → Int) (dest element : Int) (index : Int) : Int :=
  let new := similar dest (promote dest element)
  let first := firstLinear dest
  let new := copy new (firstLinear new) dest first (index - first)
  setindex new index element
/-- base/array.jl:895-912. Fuel limits processed elements, including widening.
The iterator is checked first so completed collection succeeds with no fuel. -/
def array895CollectToLoop (iterate : Int → Int → Option (Int × Int))
    (isType : Int → Int → Bool) (setindex : Int → Int → Int → Int)
    (widen : Int → Int → Int → Int) :
    Int → Int → Int → Int → Nat → JlX Int
  | dest, iterator, index, state, fuel =>
      match iterate iterator state with
      | none => .ok dest
      | some (element, nextState) =>
          match fuel with
          | 0 => .error (.errorException "fuel")
          | fuel + 1 =>
              if isType dest element then
                array895CollectToLoop iterate isType setindex widen
                  (setindex dest index element) iterator (index + 1) nextState fuel
              else
                array895CollectToLoop iterate isType setindex widen
                  (widen dest element index) iterator (index + 1) nextState fuel

def array895CollectTo (iterate : Int → Int → Option (Int × Int))
    (isType : Int → Int → Bool) (setindex : Int → Int → Int → Int)
    (widen : Int → Int → Int → Int)
    (dest iterator offset state : Int) (fuel : Nat) : JlX Int :=
  array895CollectToLoop iterate isType setindex widen dest iterator offset state fuel

def array914GrowFirst (iterate : Int → Option (Int × Int))
    (empty : Int → Int → Int) (push : Int → Int → Int)
    (grow : Int → Int → Int → JlX Int) (dest iterator : Int) : JlX Int :=
  match iterate iterator with
  | none => .ok dest
  | some (first, state) => grow (push (empty dest first) first) iterator state

def array922PushWiden (promote : Int → Int → Int) (empty : Int → Int → Int)
    (sizehint : Int → Int → Int) (isSet : Int → Bool)
    (union append : Int → Int → Int) (push : Int → Int → Int)
    (eltype length : Int → Int) (dest element : Int) : Int :=
  let new := sizehint (empty dest (promote (eltype dest) element)) (length dest)
  let new := if isSet new then union new dest else append new dest
  push new element

/-- base/array.jl:935-949. Widening re-dispatch uses the same remaining budget. -/
def array935GrowLoop (iterate : Int → Int → Option (Int × Int))
    (isType : Int → Int → Bool) (push : Int → Int → Int)
    (widen : Int → Int → Int) :
    Int → Int → Int → Nat → JlX Int
  | dest, iterator, state, fuel =>
      match iterate iterator state with
      | none => .ok dest
      | some (element, nextState) =>
          match fuel with
          | 0 => .error (.errorException "fuel")
          | fuel + 1 =>
              if isType dest element then
                array935GrowLoop iterate isType push widen
                  (push dest element) iterator nextState fuel
              else
                array935GrowLoop iterate isType push widen
                  (widen dest element) iterator nextState fuel

def array935GrowTo (iterate : Int → Int → Option (Int × Int))
    (isType : Int → Int → Bool) (push : Int → Int → Int)
    (widen : Int → Int → Int)
    (dest iterator state : Int) (fuel : Nat) : JlX Int :=
  array935GrowLoop iterate isType push widen dest iterator state fuel

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


structure MemoryRefModel where
  memoryLength : JInt64
  offset : JInt64
  deriving Repr, DecidableEq

structure WrappedArrayModel where
  ref : MemoryRefModel
  dims : List JInt64
  deriving Repr, DecidableEq

inductive WrapError where
  | dimensionMismatch | conversion | invalidDimensions
  deriving Repr, DecidableEq

abbrev WrapJl (α : Type) := Except WrapError α

def array3241WrapCheck (checkedDims : List JInt64 → WrapJl JInt64)
    (ref : MemoryRefModel) (dims : List JInt64) : WrapJl MemoryRefModel := do
  let memoryLength := ref.memoryLength + JInt.lit .i64 1 - ref.offset
  let length ← checkedDims dims
  if memoryLength < length then throw .dimensionMismatch
  pure ref

def array3249InvalidWrap (_length : JInt64) (_dims : List JInt64)
    (_product : JInt64) : WrapJl Unit := .error .dimensionMismatch

def array3254WrapRefDims (convertDims : List Int → WrapJl (List JInt64))
    (wrapCheck : MemoryRefModel → List JInt64 → WrapJl MemoryRefModel)
    (ref : MemoryRefModel) (rawDims : List Int) : WrapJl WrappedArrayModel := do
  let dims ← convertDims rawDims
  let ref ← wrapCheck ref dims
  pure ⟨ref, dims⟩

def array3260WrapMemoryDims (memoryRef : JInt64 → MemoryRefModel)
    (convertDims : List Int → WrapJl (List JInt64))
    (wrapCheck : MemoryRefModel → List JInt64 → WrapJl MemoryRefModel)
    (memoryLength : JInt64) (rawDims : List Int) : WrapJl WrappedArrayModel := do
  let dims ← convertDims rawDims
  let ref ← wrapCheck (memoryRef memoryLength) dims
  pure ⟨ref, dims⟩

def array3265WrapRefLength (convertInt : Int → WrapJl JInt64)
    (wrapCheck : MemoryRefModel → List JInt64 → WrapJl MemoryRefModel)
    (ref : MemoryRefModel) (rawLength : Int) : WrapJl WrappedArrayModel := do
  let length ← convertInt rawLength
  let dims := [length]
  let ref ← wrapCheck ref dims
  pure ⟨ref, dims⟩

def array3275WrapMemory (memoryRef : JInt64 → MemoryRefModel)
    (memoryLength : JInt64) : WrappedArrayModel :=
  let ref := memoryRef memoryLength
  ⟨ref, [memoryLength]⟩

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


inductive IntegerKind where
  | int | other
  deriving Repr, DecidableEq

/-- `wrap(Array, m::Memory, l::Integer)`, `base/array.jl:3270-3274`.
The source converts `l` to `dims`, calls `_wrap(memoryref(m), (l,))` with the
original integer type, and constructs the array only if that call returns. -/
def wrapMemory (kind : IntegerKind) (length capacity : Nat) : Jl Nat :=
  let _dims := length
  match kind with
  | .other => .error (.methodError "_wrap")
  | .int =>
      if length > capacity then .error .boundsError
      else .ok length

inductive FloatKey where
  | negZero | posZero | nan | finite (value : Int)
  deriving Repr, DecidableEq

/-- Julia `==` on the distinguished floating-point cases used by the property. -/
def memberEq : FloatKey → FloatKey → Bool
  | .negZero, .posZero | .posZero, .negZero => true
  | .nan, _ | _, .nan => false
  | x, y => x == y

/-- Julia `isequal`, which is the equality used by Dict keys. -/
def keyEqual : FloatKey → FloatKey → Bool
  | .negZero, .negZero | .posZero, .posZero | .nan, .nan => true
  | .finite x, .finite y => x == y
  | _, _ => false

def firstIndexBy (eq : FloatKey → FloatKey → Bool) (needle : FloatKey) :
    List FloatKey → Nat → Option Nat
  | [], _ => none
  | value :: rest, index =>
      if eq needle value then some index else firstIndexBy eq needle rest (index + 1)

/-- `indexin(a, b::AbstractArray)`, `base/array.jl:2892-2901`.
The first loop inserts each `b` value with `get!`, retaining its first index;
the comprehension then performs Dict lookups for the values from `a`. -/
def indexinModel (a b : List FloatKey) : List (Option Nat) :=
  a.map fun value => firstIndexBy keyEqual value b 1

end JuliaLean.ArrayCov

namespace JuliaLean.AbstractArraySpecs

/-- `@inbounds for i in s:midpoint(s, n-1); v[i], v[r] = v[r], v[i]; r -= 1; end`
(base/array.jl:2326-2330); `k` is the number of iterations left. -/
def revLoop {α : Type} : Nat → Arr α → I64 → I64 → R (Arr α)
  | 0, v, _, _ => .ok v
  | k + 1, v, i, r => do
    let x ← getindex v [r]
    let y ← getindex v [i]
    let v1 ← setindex v x [i]
    let v2 ← setindex v1 y [r]
    revLoop k v2 (i + i64 1) (r - i64 1)

/-- `midpoint(lo, hi) = lo +% ((hi -% lo) >>> 0x01)` (base/array.jl:2288) for `Int`s. -/
def midpoint (lo hi : I64) : I64 := lo + i64 (wrapInt .u64 (hi - lo).val / 2)

/-- `reverse!(v::AbstractVector, start, stop)` (base/array.jl:2317-2333) for `Int`
arguments; `liv = LinearIndices(v)` is the range `linearAxis v`. -/
def reverseRange {α : Type} (v : Arr α) (s n : I64) : R (Arr α) :=
  if n > s then
    let liv := linearAxis v
    if ¬(liv.lo ≤ s ∧ s ≤ liv.hi) then .error .boundsError
    else if ¬(liv.lo ≤ n ∧ n ≤ liv.hi) then .error .boundsError
    else
      let m := midpoint s (n - i64 1)
      revLoop (if s ≤ m then (m.val - s.val + 1).toNat else 0) v s n
  else .ok v

end JuliaLean.AbstractArraySpecs

namespace JuliaLean.AbstractArraySpecs

/-- `fill(x)` (base/array.jl:583-587): allocate the zero-dimensional
`Array{typeof(x),0}`, then `_fill!` (lines 373-378) stores x at its only index `[]`. -/
def fillScalar {α : Type} (x : TypedValue α) : TypedCatOut α :=
  let A : TypedCatOut α := ⟨x.typeCode, ⟨[], [none]⟩⟩
  { A with storage := { A.storage with cells := A.storage.cells.set 0 (some x.payload) } }

end JuliaLean.AbstractArraySpecs

namespace JuliaLean.ArrayOps

open JuliaLean

variable {α β : Type}

/-- `midpoint(lo, hi) = lo +% ((hi -% lo) >>> 0x01)`, `base/array.jl:2288`, for `lo ≤ hi`
(the only use, where the result is exact). -/
def midpoint (lo hi : Int) : Int := lo + (hi - lo) / 2

/-- The swap loop `for i in s:midpoint(s, n-1); v[i], v[r] = v[r], v[i]; r -= 1; end`
(`k` iterations left). -/
def swapLoop [Inhabited α] (v : List α) (i r : Int) : Nat → List α
  | 0 => v
  | k + 1 =>
    let vi := v[(i - 1).toNat]!
    let vr := v[(r - 1).toNat]!
    swapLoop ((v.set (i - 1).toNat vr).set (r - 1).toNat vi) (i + 1) (r - 1) k

/-- `reverse!(v, start, stop)`, `base/array.jl:2317-2333`. -/
def reverseBang [Inhabited α] {s t : IntTy} (v : List α) (start : JInt s) (stop : JInt t) :
    Jl (List α) := do
  let s ← toInt start
  let n ← toInt stop
  if n.val > s.val then
    if ¬ (1 ≤ s.val ∧ s.val ≤ v.length) then throw .boundsError
    else if ¬ (1 ≤ n.val ∧ n.val ≤ v.length) then throw .boundsError
    else pure (swapLoop v s.val n.val (midpoint s.val (n.val - 1) - s.val + 1).toNat)
  else pure v

/-- `for i = lo:hi; body(i); end` for `Int` bounds, stopping at the first exception. -/
def forRange {σ : Type} (body : Int → σ → Jl σ) : Int → Nat → σ → Jl σ
  | _, 0, st => .ok st
  | i, k + 1, st => do forRange body (i + 1) k (← body i st)

/-- `B[i] = A[j]` for `B = similar(A)` held as slots: read `A[j]`, then store. -/
def copySlot (A : List α) (i j : Int) (B : Vec α) : Jl (Vec α) := do
  let x ← getAt A (JInt.wrap .i64 j)
  if 1 ≤ i ∧ i ≤ B.length then pure (B.set (i - 1).toNat (some x)) else throw .boundsError

/-- Number of iterations of `lo:hi` for `Int` bounds (`hi` already wrapped). -/
def iterCount (lo hi : Int) : Nat := (hi - lo + 1).toNat

/-- `reverse(A, start, stop)`, `base/array.jl:2253-2266`: three copy loops into
`B = similar(A)`. The bounds `s-1` and `n+1` are computed in `Int`, wrapping. -/
def reverseCopy {s t : IntTy} (A : List α) (start : JInt s) (stop : JInt t) :
    Jl (List (Option α)) := do
  let s ← toInt start
  let n ← toInt stop
  let len : Int := A.length
  let B : Vec α := List.replicate A.length none
  let sm1 := (s - JInt.lit .i64 1).val
  let np1 := (n + JInt.lit .i64 1).val
  let B ← forRange (fun i B => copySlot A i i B) 1 (iterCount 1 sm1) B
  let B ← forRange (fun i B => copySlot A i (n.val + s.val - i) B) s.val (iterCount s.val n.val) B
  forRange (fun i B => copySlot A i i B) np1 (iterCount np1 len) B


/-- `fill(x, n)`, `base/array.jl:583-585` → `Array{T}(undef, n)`: `Int(n)`
(`InexactError`), then the allocation rejects a negative length (`ArgumentError`). -/
def fill {t : IntTy} (x : α) (n : JInt t) : Jl (List α) := do
  let n ← toInt n
  if n.val < 0 then throw (.argumentError "invalid GenericMemory size")
  pure (List.replicate n.val.toNat x)

/-! ### `copyto!(dest, doffs, src, soffs, n)` -/

/-- `_copyto_impl!(dest, doffs, src, soffs, n)`, `base/array.jl:299-316`, for
`dest::Array` and `src::Array`; `src = none` stands for `src === dest`. `length(dest) - doffs + 1`
is computed in the promoted type (it cannot wrap once `checkbounds(dest, doffs)`
holds). The copy is a `memmove`: the source block is read before any store. -/
def copyto {s t u : IntTy} (dest : List α) (doffs : JInt s) (src : Option (List α)) (soffs : JInt t)
    (n : JInt u) : Jl (List α) :=
  let srcv := src.getD dest
  if n.val = 0 then .ok dest
  else if ¬ n.val > 0 then .error (.argumentError "Number of elements to copy must be non-negative.")
  else if ¬ (1 ≤ doffs.val ∧ doffs.val ≤ dest.length) then .error .boundsError
  else if ¬ n.val ≤ dest.length - doffs.val + 1 then .error .boundsError
  else if ¬ (1 ≤ soffs.val ∧ soffs.val ≤ srcv.length) then .error .boundsError
  else if ¬ n.val ≤ srcv.length - soffs.val + 1 then .error .boundsError
  else
    let d := (doffs.val - 1).toNat
    let block := (srcv.drop (soffs.val - 1).toNat).take n.val.toNat
    .ok (dest.take d ++ block ++ dest.drop (d + n.val.toNat))

/-! ### `findnext` and `findprev` -/

/-- The loop of `findnext(testf, A, start)` from `i` (`k` iterations bound). -/
def findnextLoop (f : α → Bool) (a : List α) (l : Int) : Int → Nat → Jl (Option JInt64)
  | _, 0 => .ok none
  | i, k + 1 => do
    let x ← getAt a (JInt.wrap .i64 i)
    if f x then return some (JInt.wrap .i64 i)
    if i = l then return none
    findnextLoop f a l (i + 1) k

/-- `findnext(testf::Function, A, start)`, `base/array.jl:2475-2486`, for a vector:
`i = oftype(first(keys(A)), start)`, `l = last(keys(A))`. -/
def findnext {t : IntTy} (f : α → Bool) (a : List α) (start : JInt t) : Jl (Option JInt64) := do
  let i ← toInt start
  let l : Int := a.length
  if i.val > l then return none
  findnextLoop f a l i.val (l - i.val + 1).toNat

/-- The loop of `findprev(testf, A, start)` from `i` down to `f = 1`. -/
def findprevLoop (f : α → Bool) (a : List α) : Int → Nat → Jl (Option JInt64)
  | _, 0 => .ok none
  | i, k + 1 => do
    let x ← getAt a (JInt.wrap .i64 i)
    if f x then return some (JInt.wrap .i64 i)
    if i = 1 then return none
    findprevLoop f a (i - 1) k

/-- `findprev(testf::Function, A, start)`, `base/array.jl:2671-2682`, for a vector. -/
def findprev {t : IntTy} (f : α → Bool) (a : List α) (start : JInt t) : Jl (Option JInt64) := do
  let i ← toInt start
  if i.val < 1 then return none
  findprevLoop f a i.val i.val.toNat


end JuliaLean.ArrayOps

namespace JuliaLean.ArrayOps

open JuliaLean


section
variable {α β : Type}



/-- `unsafe_copyto!(dest::Array, doffs, src::Array, soffs, n)` with `dest === src`,
`base/array.jl:276-280`: nothing for `n == 0`, otherwise the two `memoryref`
bounds checks. Only the checks are modelled; callers compute the moved contents. -/
def selfCopyCheck {s t u : IntTy} (len : Nat) (doffs : JInt s) (soffs : JInt t) (n : JInt u) :
    Jl Unit :=
  if n.val = 0 then pure () else do
    memoryrefCheck len doffs
    memoryrefCheck len soffs

/-- `_deletebeg!(a, delta)`, `base/array.jl:1278-1295`. -/
def deletebeg {t : IntTy} (a : Vec α) (delta : JInt t) : Out α Unit :=
  match toInt delta with
  | .error e => ⟨a, .error e⟩
  | .ok d =>
    -- `unsigned(delta) > unsigned(len)`: a negative delta is a huge unsigned value
    if d.val < 0 ∨ d.val > a.length then
      ⟨a, .error (.argumentError "_deletebeg! requires delta in 0:length(a)")⟩
    else ⟨a.drop d.val.toNat, .ok ()⟩

/-- `_deleteend!(a, delta)`, `base/array.jl:1296-1311`. -/
def deleteend {t : IntTy} (a : Vec α) (delta : JInt t) : Out α Unit :=
  match toInt delta with
  | .error e => ⟨a, .error e⟩
  | .ok d =>
    if d.val < 0 ∨ d.val > a.length then
      ⟨a, .error (.argumentError "_deleteend! requires delta in 0:length(a)")⟩
    else ⟨a.take (a.length - d.val.toNat), .ok ()⟩

/-- `_growbeg!(a, delta)`, `base/array.jl:1151-1168`: `delta` unassigned slots in front. -/
def growbeg {t : IntTy} (a : Vec α) (delta : JInt t) : Out α Unit :=
  match toInt delta with
  | .error e => ⟨a, .error e⟩
  | .ok d =>
    if d.val = 0 then ⟨a, .ok ()⟩
    else if ¬ 0 ≤ d.val then ⟨a, .error (.argumentError "grow requires delta >= 0")⟩
    else ⟨List.replicate d.val.toNat none ++ a, .ok ()⟩

/-- `_growend!(a, delta)`, `base/array.jl:1213-1228`: `delta` unassigned slots at the end. -/
def growend {t : IntTy} (a : Vec α) (delta : JInt t) : Out α Unit :=
  match toInt delta with
  | .error e => ⟨a, .error e⟩
  | .ok d =>
    if ¬ 0 ≤ d.val then ⟨a, .error (.argumentError "grow requires delta >= 0")⟩
    else ⟨a ++ List.replicate d.val.toNat none, .ok ()⟩

/-- `_growat!(a, i, delta)`, `base/array.jl:1230-1275`: `delta` unassigned slots
before position `i`. The three memory strategies move the same contents. -/
def growat {s t : IntTy} (a : Vec α) (i : JInt s) (delta : JInt t) : Out α Unit :=
  match toInt delta, toInt i with
  | .error e, _ => ⟨a, .error e⟩
  | .ok _, .error e => ⟨a, .error e⟩
  | .ok d, .ok i =>
    let len : Int := a.length
    if i.val = 1 then growbeg a d
    else if len < IntTy.i64.max ∧ i.val = len + 1 then growend a d
    else if ¬ 0 ≤ d.val then ⟨a, .error (.argumentError "grow requires delta >= 0")⟩
    else if ¬ (1 < i.val ∧ i.val ≤ len) then ⟨a, .error .boundsError⟩
    else
      let k := (i.val - 1).toNat
      ⟨a.take k ++ List.replicate d.val.toNat none ++ a.drop k, .ok ()⟩

/-- `_deleteat!(a, i, delta)`, `base/array.jl:1312-1327`. `delta` keeps its own type
(the `length` of the caller's range), so `i + delta` and `2*i + delta` are computed
in the promoted type, wrapping. The first branch moves the `i-1` leading elements
right by `delta` and drops `delta` from the front, the second moves the tail left
and drops `delta` from the end; both leave `a[1:i-1]` followed by `a[i+delta:end]`. -/
def deleteatAt {s t : IntTy} (a : Vec α) (i : JInt s) (delta : JInt t) : Out α Unit :=
  match toInt i with
  | .error e => ⟨a, .error e⟩
  | .ok i =>
    let len : Int := a.length
    let one : JInt64 := JInt.lit .i64 1
    let rest := a.take (i.val - 1).toNat ++ a.drop (i.val - 1 + delta.val).toNat
    if ¬ 0 ≤ delta.val then ⟨a, .error (.argumentError "_deleteat! requires delta >= 0")⟩
    else if ¬ (1 ≤ i.val ∧ i.val ≤ len) then ⟨a, .error .boundsError⟩
    else if ¬ (addMixed i delta).val ≤ len + 1 then ⟨a, .error .boundsError⟩
    else if (addMixed (JInt.lit .i64 2 * i) delta).val ≤ len then
      -- unsafe_copyto!(newa, 1 + delta, a, 1, i - 1); _deletebeg!(a, delta)
      match selfCopyCheck a.length (addMixed one delta) one (i - one) with
      | .error e => ⟨a, .error e⟩
      | .ok () =>
        match deletebeg a delta with
        | ⟨_, .error e⟩ => ⟨a, .error e⟩
        | ⟨_, .ok ()⟩ => ⟨rest, .ok ()⟩
    else
      -- unsafe_copyto!(newa, i, a, i + delta, len + 1 - delta - i); _deleteend!(a, delta)
      let n := JInt.wrap (IntTy.promote .i64 t) (len + 1 - delta.val - i.val)
      match selfCopyCheck a.length i (addMixed i delta) n with
      | .error e => ⟨a, .error e⟩
      | .ok () =>
        match deleteend a delta with
        | ⟨_, .error e⟩ => ⟨a, .error e⟩
        | ⟨_, .ok ()⟩ => ⟨rest, .ok ()⟩

/-! ### Dequeue operations -/

/-- `push!(a, item)`, `base/array.jl:1358-1370` (item already converted). -/
def push (a : Vec α) (x : α) : Out α Unit :=
  match growend a (JInt.lit .i64 1) with
  | ⟨a, .ok ()⟩ => ⟨a.set (a.length - 1) (some x), .ok ()⟩
  | o => o

/-- `pop!(a)`, `base/array.jl:1700-1707`. -/
def pop (a : Vec α) : Out α (Option α) :=
  if a.isEmpty then ⟨a, .error (.argumentError "array must be non-empty")⟩
  else
    let item := a.getLast?.join
    match deleteend a (JInt.lit .i64 1) with
    | ⟨a, .ok ()⟩ => ⟨a, .ok item⟩
    | ⟨a, .error e⟩ => ⟨a, .error e⟩

/-- `pushfirst!(a, item)`, `base/array.jl:1777-1786` (item already converted). -/
def pushfirst (a : Vec α) (x : α) : Out α Unit :=
  match growbeg a (JInt.lit .i64 1) with
  | ⟨a, .ok ()⟩ => ⟨a.set 0 (some x), .ok ()⟩
  | o => o

/-- `popfirst!(a)`, `base/array.jl:1836-1843`. -/
def popfirst (a : Vec α) : Out α (Option α) :=
  if a.isEmpty then ⟨a, .error (.argumentError "array must be non-empty")⟩
  else
    let item := a.head?.join
    match deletebeg a (JInt.lit .i64 1) with
    | ⟨a, .ok ()⟩ => ⟨a, .ok item⟩
    | ⟨a, .error e⟩ => ⟨a, .error e⟩

/-- `insert!(a, i, item)`, `base/array.jl:1866-1878` (item already converted):
`_growat!(a, i, 1)`, then `a[i] = item`. -/
def insert {t : IntTy} (a : Vec α) (i : JInt t) (x : α) : Out α Unit :=
  match growat a i (JInt.lit .i64 1) with
  | ⟨a', .ok ()⟩ => ⟨a'.set (i.val - 1).toNat (some x), .ok ()⟩
  | o => o

/-! ### Deletion -/

/-- `deleteat!(a, i::Integer)`, `base/array.jl:1899-1903`. -/
def deleteatIndex {t : IntTy} (a : Vec α) (i : JInt t) : Out α Unit :=
  deleteatAt a i (JInt.lit .i64 1)


/-- `deleteat!(a, r::AbstractUnitRange{<:Integer})` for `r = lo:hi` of a non-`Bool`
type, `base/array.jl:1905-1914`. -/
def deleteatRange {t : IntTy} (a : Vec α) (lo hi : JInt t) : Out α Unit :=
  if lo.val > hi.val then ⟨a, .ok ()⟩ else deleteatAt a lo (unitLength lo hi)

/-- `_copy_item!(a, p, q)`, `base/array.jl:1961-1968`: `a[p] = a[q]`, or unset. -/
def copyItem (a : Vec α) (p q : Int) : Vec α :=
  a.set (p - 1).toNat (a[(q - 1).toNat]?.join)

/-- `while q < i; _copy_item!(a, p, q); p += 1; q += 1; end` (`k = i - q` steps). -/
def compact (a : Vec α) (p q : Int) : Nat → Vec α × Int × Int
  | 0 => (a, p, q)
  | k + 1 => compact (copyItem a p q) (p + 1) (q + 1) k

/-- The loop of `_deleteat!(a, inds)` after the first index, `base/array.jl:1977-2000`. -/
def deleteatLoop (a : Vec α) (n : Nat) (p q : Int) : List JInt64 → Out α Unit
  | [] =>
    let (a, p, _) := compact a p q (n + 1 - q).toNat
    deleteend a (JInt.wrap .i64 (n - p + 1))
  | i :: rest =>
    if ¬ (q ≤ i.val ∧ i.val ≤ n) then
      if i.val < q then ⟨a, .error (.argumentError "indices must be unique and sorted")⟩
      else ⟨a, .error .boundsError⟩
    else
      let (a, p, _) := compact a p q (i.val - q).toNat
      deleteatLoop a n p (i.val + 1) rest

/-- `deleteat!(a, inds)` for a vector `inds` of `Int`, `base/array.jl:1946, 1970-2002`
(`to_indices` returns `inds` itself; deleted items go to `Nowhere`). -/
def deleteatInds (a : Vec α) (inds : List JInt64) : Out α Unit :=
  match inds with
  | [] => ⟨a, .ok ()⟩
  | p :: rest =>
    if ¬ (1 ≤ p.val ∧ p.val ≤ a.length) then ⟨a, .error .boundsError⟩
    else deleteatLoop a a.length p.val (p.val + 1) rest

/-- The loop `for (q, i) in enumerate(inds); _copy_item!(a, p, q); p += !i; end`. -/
def maskLoop (a : Vec α) (p q : Int) : List Bool → Vec α × Int
  | [] => (a, p)
  | i :: rest => maskLoop (copyItem a p q) (if i then p else p + 1) (q + 1) rest

/-- `deleteat!(a, inds::AbstractVector{Bool})`, `base/array.jl:2005-2015`. -/
def deleteatMask (a : Vec α) (mask : List Bool) : Out α Unit :=
  if mask.length ≠ a.length then ⟨a, .error .boundsError⟩
  else
    let (a', p) := maskLoop a 1 1 mask
    deleteend a' (JInt.wrap .i64 (a.length - p + 1))


/-- `keepat!(a, inds)` for a vector `inds` of `Int`, `base/array.jl:3134`:
the loop, then `deleteat!(a, i:lastindex(a))`. -/
def keepat (a : Vec α) (inds : List JInt64) : Out α Unit :=
  match keepatLoop copyItem a 1 none inds with
  | ⟨a, .error e⟩ => ⟨a, .error e⟩
  | ⟨a, .ok i⟩ => deleteatRange a (JInt.wrap .i64 i) (JInt.wrap .i64 a.length)

/-- `filter!(f, a)` for a `Vector`, `base/array.jl:3066-3079`: compaction loop
(`j` is advanced after storing), then `resize!(a, j-1)`. `f` sees the stored value;
unassigned slots are not supported (they throw `UndefRefError` in Julia), so the
loop stores `none` and skips it. -/
def filterLoop (f : α → Bool) (a : Vec α) (j : Nat) : List (Option α) → Vec α × Nat
  | [] => (a, j)
  | ai :: rest =>
    let a := a.set (j - 1) ai
    filterLoop f a (if ai.any f then j + 1 else j) rest

def filterBang (f : α → Bool) (a : Vec α) : Vec α :=
  let (a', j) := filterLoop f a 1 a
  if j > a.length then a' else a'.take (j - 1)

/-! ### `splice!` -/

/-- Store the replacement values `a[f+k-1] = x` for `k = 1, 2, ...`
(`base/array.jl:2079-2083, 2145-2149`). Each store converts its value to the
element type (`conv`), which may throw; earlier stores remain. -/
def storeAll {β : Type} (conv : β → Jl α) (a : Vec α) (f : Int) : List β → Out α Unit
  | [] => ⟨a, .ok ()⟩
  | x :: rest =>
    match conv x with
    | .error e => ⟨a, .error e⟩
    | .ok y =>
      if ¬ (1 ≤ f ∧ f ≤ a.length) then ⟨a, .error .boundsError⟩
      else storeAll conv (a.set (f - 1).toNat (some y)) (f + 1) rest

/-- `splice!(a, r::AbstractUnitRange{Int}, ins)` for `r = f:l` (`l ≥ f - 1`),
`base/array.jl:2125-2151`. `ins` holds values of a source type `β`, each converted
to the element type by `conv` when stored. Returns the removed items `a[r]`. -/
def spliceRange {β : Type} (conv : β → Jl α) (a : Vec α) (f l : JInt64) (ins : List β) :
    Out α (Vec α) :=
  -- v = a[r]: checkbounds(a, r), then copy
  if ¬ (f.val > l.val ∨ (1 ≤ f.val ∧ l.val ≤ a.length)) then ⟨a, .error .boundsError⟩
  else
    let v := (a.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat
    let m : JInt64 := JInt.wrap .i64 ins.length
    if m.val = 0 then
      match deleteatRange a f l with
      | ⟨a, .ok ()⟩ => ⟨a, .ok v⟩
      | ⟨a, .error e⟩ => ⟨a, .error e⟩
    else
      let n : JInt64 := JInt.wrap .i64 a.length
      let one : JInt64 := JInt.lit .i64 1
      let d : JInt64 := l - f + one
      let front := (f - one).val < (n - l).val
      let shaped : Out α Unit :=
        if m.val < d.val then
          let delta := d - m
          deleteatAt a (if front then f else l - delta + one) delta
        else if m.val > d.val then
          growat a (if front then f else l + one) (m - d)
        else ⟨a, .ok ()⟩
      match shaped with
      | ⟨a, .error e⟩ => ⟨a, .error e⟩
      | ⟨a, .ok ()⟩ =>
        match storeAll conv a f.val ins with
        | ⟨a, .ok ()⟩ => ⟨a, .ok v⟩
        | ⟨a, .error e⟩ => ⟨a, .error e⟩

/-! ### `resize!` -/

/-- `resize!(a, n; first)`, `base/array.jl:1564-1579`. -/
def resize {t : IntTy} (a : Vec α) (n : JInt t) (first : Bool := false) : Out α Unit :=
  match toInt n with
  | .error e => ⟨a, .error e⟩
  | .ok nl =>
    let l : Int := a.length
    if nl.val > l then
      let d := JInt.wrap .i64 (nl.val - l)
      if first then growbeg a d else growend a d
    else if nl.val ≠ l then
      if nl.val < 0 then ⟨a, .error (.argumentError "new length must be ≥ 0")⟩
      else
        let d := JInt.wrap .i64 (l - nl.val)
        if first then deletebeg a d else deleteend a d
    else ⟨a, .ok ()⟩

/-! ### `append!` and `prepend!` -/

/-- A collection argument of `append!`/`prepend!`: the vector being mutated itself,
or another vector with the given contents (already of the element type). -/
inductive Src (α : Type) where
  | self
  | other (xs : Vec α)

/-- The contents a source has when it is read, given the current vector. -/
def Src.read (a : Vec α) : Src α → Vec α
  | .self => a
  | .other xs => xs

/-- `append!(a::Vector{T}, items::AbstractVector{<:T})`, `base/array.jl:1427-1433`:
`_growend!(a, n)`, then `copyto!(a, length(a)-n+1, items, firstindex(items), n)`.
For `items === a` the copy reads the first `n` elements, which are the old contents. -/
def append1 (a : Vec α) (items : Src α) : Vec α :=
  let xs := items.read a
  a ++ xs

/-- `append!(a, iter...)`, `base/array.jl:1437`: `foreach(v -> append!(a, v), iter)`. -/
def append (a : Vec α) : List (Src α) → Vec α
  | [] => a
  | s :: rest => append (append1 a s) rest

/-- `prepend!(a::Vector{T}, items::AbstractVector{<:T})`, `base/array.jl:1485-1498`:
items other than `a` are unaliased; `_growbeg!(a, n)` then
`copyto!(a, 1, items, lastindex(items)-n+1, n)`, which for `items === a` reads the
last `n` elements, i.e. the old contents. -/
def prepend1 (a : Vec α) (items : Src α) : Vec α :=
  items.read a ++ a

/-- `prepend!(a, iter...)`, `base/array.jl:1502`: `for v = reverse(iter); prepend!(a, v); end`. -/
def prepend (a : Vec α) (srcs : List (Src α)) : Vec α :=
  srcs.reverse.foldl prepend1 a

end

end JuliaLean.ArrayOps

namespace JuliaLean.ReduceCov.Indices


/-- `getindex(v::AbstractRange, i::Integer)` (`base/array.jl:3224-3230`), reached by a
`Slice` with a non-`Int` integer: `i isa Bool` throws, otherwise `checkbounds` and
`unsafe_getindex(v, i) = first(v) + (i - 1) * step(v)` (`base/range.jl:985`). -/
def rangeGetindexInteger (S : UR) (i : Ix) (k : Int) : RJ (List Int) := do
  checkbounds S i; pure [S.first + (k - 1)]

end JuliaLean.ReduceCov.Indices

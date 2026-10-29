import JuliaLean.Core

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
def vectPromoted [Monad m] (promoteTypeof : List α → T)
    (literal : T → List α → m A) (xs : List α) : m A := do
  let t := promoteTypeof xs
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
def copytoImpl [Monad m] [MonadExceptOf Error m] 
    (countValue : Count → Int) (destLength : D → m I) (srcLength : S → m I)
    (destBounds : D → OffsetD → m Unit) (srcBounds : S → OffsetS → m Unit)
    (destSub : I → OffsetD → I) (srcSub : I → OffsetS → I)
    (toDestInt : OffsetD → m I) (toSrcInt : OffsetS → m I) (toCountInt : Count → m I)
    (destRef : D → I → m R) (srcRef : S → I → m R)
    (copy : R → R → I → m Unit)
    (dest : D) (doffs : OffsetD) (src : S) (soffs : OffsetS) (n : Count) : m D := do
  if countValue n = 0 then return dest
  if !(countValue n > 0) then
    throw (.argument "Number of elements to copy must be non-negative.")
  destBounds dest doffs
  if !(countValue n ≤ ((destSub (← destLength dest) doffs + one)).val) then throw .bounds
  srcBounds src soffs
  if !(countValue n ≤ ((srcSub (← srcLength src) soffs + one)).val) then throw .bounds
  let doffs ← toDestInt doffs
  let soffs ← toSrcInt soffs
  let n ← toCountInt n
  copy (← destRef dest doffs) (← srcRef src soffs) n
  pure dest

/--
Julia source: base/array.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_throw_argerror(s) = (@noinline; throw(ArgumentError(s)))
```
-/
def throwArgument [Monad m] [MonadExceptOf Error m] (s : String) : m α :=
  throw (.argument s)

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
def copyto325 [Monad m] (copy : D → S → m D) (dest : D) (src : S) : m D :=
  copy dest src

/--
Julia source: base/array.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array, src::Memory) = _copyto2arg!(dest, src)
```
-/
def copyto326 [Monad m] (copy : D → S → m D) (dest : D) (src : S) : m D :=
  copy dest src

/--
Julia source: base/array.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Memory, src::Array) = _copyto2arg!(dest, src)
```
-/
def copyto327 [Monad m] (copy : D → S → m D) (dest : D) (src : S) : m D :=
  copy dest src

/--
Julia source: base/array.jl:330-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array{T}, src::Array{T}) where {T} = _copyto2arg!(dest, src)
```
-/
def copyto330 [Monad m] (copy : D → S → m D) (dest : D) (src : S) : m D :=
  copy dest src

/--
Julia source: base/array.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Array{T}, src::Memory{T}) where {T} = _copyto2arg!(dest, src)
```
-/
def copyto331 [Monad m] (copy : D → S → m D) (dest : D) (src : S) : m D :=
  copy dest src

/--
Julia source: base/array.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Memory{T}, src::Array{T}) where {T} = _copyto2arg!(dest, src)
```
-/
def copyto332 [Monad m] (copy : D → S → m D) (dest : D) (src : S) : m D :=
  copy dest src

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
def fillTyped [Monad m] (eachindex : A → m (List K))
    (set : A → α → K → m Unit) (a : A) (x : α) : m A := do
  for i in (← eachindex a) do
    set a x i
  pure a

/--
Julia source: base/array.jl:391-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval function copy(a::Array)
    # `copy` only throws when the size exceeds the max allocation size,
    # but since we're copying an existing array, we're guaranteed that this will not happen.
    @_nothrow_meta
    ref = a.ref
    newmem = typeof(ref.mem)(undef, length(a))
    @inbounds unsafe_copyto!(memoryref(newmem), ref, length(a))
    return $(Expr(:new, :(typeof(a)), :(memoryref(newmem)), :(a.size)))
end
```
-/
def copyArray [Monad m] (ref : A → m R) (length : A → m I)
    (allocateMemory : R → I → m Mem) (memoryref : Mem → m R)
    (copy : R → R → I → m Unit) (size : A → m D) (newArray : R → D → m A)
    (a : A) : m A := do
  let ref ← ref a
  let newmem ← allocateMemory ref (← length a)
  copy (← memoryref newmem) ref (← length a)
  newArray (← memoryref newmem) (← size a)

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
    (constructor : A → m B) (a : A) : m B :=
  if alreadyTyped a then pure (asTyped a) else constructor a

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
def similarForUnknown [Monad m] (similar : C → T → I → m A)
    (c : C) (t : T) (_itr : X) : m A := similar c t zero

/--
Julia source: base/array.jl:705-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c::AbstractArray, ::Type{T}, itr, ::HasLength, len::Integer) where {T} =
    similar(c, T, len)
```
-/
def similarForLength [Monad m] (similar : C → T → Z → m A)
    (c : C) (ty : T) (_itr : X) (len : Z) : m A := similar c ty len

/--
Julia source: base/array.jl:707-708 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c::AbstractArray, ::Type{T}, itr, ::HasShape, axs) where {T} =
    similar(c, T, axs)
```
-/
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
def setindexWiden [Monad m] (promoteJoin : T → T → T)
    (eltype : A → T) (typeof : α → T) (similar : A → T → m A)
    (firstLinear : A → m I) (copy : A → I → A → I → I → m Unit)
    (set : A → α → I → m Unit) (dest : A) (el : α) (i : I) : m A := do
  let new ← similar dest (promoteJoin (eltype dest) (typeof el))
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
    (join : T → T → T) (empty : A → T → m A) (length : A → m I)
    (sizehint : A → I → m A) (isSet : A → Bool)
    (union append : A → A → m Unit) (push : A → α → m Unit)
    (dest : A) (el : α) : m A := do
  let new ← sizehint (← empty dest (join (eltype dest) (typeof el))) (← length dest)
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
def getindexUnitRange [Monad m]  (value : Z → Int) (bounds : A → R → m Unit)
    (length : R → Z) (axes : R → Axes) (similar : A → Axes → m A)
    (firstindex : A → m I) (first : R → Z)
    (copy : A → I → A → Z → Z → m Unit) (a : A) (r : R) : m A := do
  bounds a r
  let li := length r
  let x ← similar a (axes r)
  if value li > 0 then copy x (← firstindex x) a (first r) li
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
def setindexCartesian [Monad m] (alreadyTyped : α → Bool) (asTyped : α → β)
    (convert : α → m β) (set : A → β → I → I → List I → m A)
    (a : A) (x : α) (i1 i2 : I) (rest : List I) : m A := do
  let x ← if alreadyTyped x then pure (asTyped x) else convert x
  set a x i1 i2 rest

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
Julia source: base/array.jl:1430-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
append!(a::AbstractVector, iter) = _append!(a, IteratorSize(iter), iter)
```
-/
def appendIterator [Monad m] (iteratorSize : X → Size)
    (append : A → Size → X → m A) (a : A) (itr : X) : m A := append a (iteratorSize itr) itr

/--
Julia source: base/array.jl:1431-1431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(a::AbstractVector, iter...) = append!(a, iter)
```
-/
def pushMany [Monad m] (append : A → List α → m A) (a : A) (items : List α) : m A :=
  append a items

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
Julia source: base/array.jl:1495-1495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prepend!(a::AbstractVector, iter) = _prepend!(a, IteratorSize(iter), iter)
```
-/
def prependIterator [Monad m] (iteratorSize : X → Size)
    (prepend : A → Size → X → m A) (a : A) (itr : X) : m A := prepend a (iteratorSize itr) itr

/--
Julia source: base/array.jl:1496-1496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pushfirst!(a::AbstractVector, iter...) = prepend!(a, iter)
```
-/
def pushfirstMany [Monad m] (prepend : A → List α → m A) (a : A) (items : List α) : m A :=
  prepend a items

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
Julia source: base/array.jl:1940-1940 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deleteat!(a::Vector, inds) = _deleteat!(a, inds)
```
-/
def deleteatIndices [Monad m] (deleteat : A → Indices → m A)
    (a : A) (indices : Indices) : m A := deleteat a indices

/--
Julia source: base/array.jl:1941-1941 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deleteat!(a::Vector, inds::AbstractVector) = _deleteat!(a, to_indices(a, (inds,))[1])
```
-/
def deleteatIndexVector [Monad m] (toIndices : A → Indices → m Converted)
    (first : Converted → Index) (deleteat : A → Index → m A)
    (a : A) (indices : Indices) : m A := do deleteat a (first (← toIndices a indices))

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
def spliceIndices [Monad m] (empty : A → m D) (deleteat : A → Indices → D → m Unit)
    (a : A) (indices : Indices) : m D := do
  let dltds ← empty a
  deleteat a indices dltds
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
    (pointer : R → m P) (length : A → m I) (memcmp : P → P → I → m (JInt .i32))
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
    (length : A → m I) (elementSize : I) (memcmp : P → P → I → m (JInt .i32))
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
    (memcmp : P → P → I → m (JInt .i32)) (endPreserve : Token → m Unit) (a b : A) : m Bool := do
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
def reverseColon [Monad m] (firstindex lastindex : A → m I)
    (reverse : A → I → I → m A) (a : A) : m A := do
  reverse a (← firstindex a) (← lastindex a)

/--
Julia source: base/array.jl:2268-2268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $_f(A::AbstractVector, dim::Tuple{Integer}) = $_f(A, first(dim))
```
-/
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
    (firstLinear lastLinear : A → m I) (midpoint : I → I → m I)
    (get : A → I → m α) (set : A → α → I → m Unit)
    (a : A) (start : Start) (stop : Stop) : m A := do
  let s ← toStartInt start
  let n ← toStopInt stop
  if n > s then
    let first ← firstLinear a
    let last ← lastLinear a
    if !(first ≤ s ∧ s ≤ last) then throw .bounds
    else if !(first ≤ n ∧ n ≤ last) then throw .bounds
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
def hcat [Monad m] [MonadExceptOf Error m] (getVector : List A → I → m A)
    (length : A → m I) (get : A → I → m α) (typeAssert : α → m α)
    (matrixLiteral : List (List α) → m B)
    (vs : List A) : m B := do
  let height ← length (← getVector vs one)
  for j in intRange (JInt.wrap .i64 2) (JInt.wrap .i64 vs.length) do
    if (← length (← getVector vs j)) != height then
      throw (.dimensionMismatch "vectors must have same lengths")
  let rows ← (intRange one (← length (← getVector vs one))).mapM fun i =>
    (intRange one (JInt.wrap .i64 vs.length)).mapM fun j => do
      typeAssert (← get (← getVector vs j) i)
  matrixLiteral rows

/--
Julia source: base/array.jl:2344-2344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hcat(A::Vector...) = cat(A...; dims=Val(2)) # more special than SparseArrays's hcat
```
-/
def hcatMixed [Monad m] (cat : List A → I → m B) (arrays : List A) : m B :=
  cat arrays (JInt.wrap .i64 2)

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
def vcatMixed [Monad m] (cat : List A → I → m B) (arrays : List A) : m B :=
  cat arrays one

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
Julia source: base/array.jl:2399-2399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findnext(A, start) = findnext(identity, A, start)
```
-/
def findnextBool [Monad m] (findnext : (Bool → Bool) → A → K → m (Option K))
    (a : A) (start : K) : m (Option K) := findnext id a start

/--
Julia source: base/array.jl:2436-2436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(A) = findfirst(identity, A)
```
-/
def findfirstBool [Monad m] (findfirst : (Bool → Bool) → A → m (Option K))
    (a : A) : m (Option K) := findfirst id a

/--
Julia source: base/array.jl:2439-2439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(A::AbstractArray) = findnext(A, first(keys(A)))
```
-/
def findfirstArrayBool [Monad m] (firstKey : A → m K)
    (findnext : A → K → m (Option K)) (a : A) : m (Option K) := do
  findnext a (← firstKey a)

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
def findfirstArray [Monad m] (firstKey : A → m K)
    (findnext : (α → m Bool) → A → K → m (Option K))
    (test : α → m Bool) (a : A) : m (Option K) := do
  findnext test a (← firstKey a)

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
Julia source: base/array.jl:2586-2586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findprev(A, start) = findprev(identity, A, start)
```
-/
def findprevBool [Monad m] (findprev : (Bool → Bool) → A → K → m (Option K))
    (a : A) (start : K) : m (Option K) := findprev id a start

/--
Julia source: base/array.jl:2624-2624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(A) = findlast(identity, A)
```
-/
def findlastBool [Monad m] (findlast : (Bool → Bool) → A → m (Option K))
    (a : A) : m (Option K) := findlast id a

/--
Julia source: base/array.jl:2627-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(A::AbstractArray) = findprev(A, last(keys(A)))
```
-/
def findlastArrayBool [Monad m] (lastKey : A → m K)
    (findprev : A → K → m (Option K)) (a : A) : m (Option K) := do
  findprev a (← lastKey a)

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
def findlastArray [Monad m] (lastKey : A → m K)
    (findprev : (α → m Bool) → A → K → m (Option K))
    (test : α → m Bool) (a : A) : m (Option K) := do
  findprev test a (← lastKey a)

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

/--
Julia source: base/array.jl:2791-2791 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(testf::F, A::AbstractArray) where {F<:Function} = findall(testf.(A))
```
-/
def findallArrayPredicate [Monad m] (broadcast : (α → Bool) → A → m Mask)
    (findall : Mask → m B) (test : α → Bool) (a : A) : m B := do findall (← broadcast test a)

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
def indexin [Monad m] (keys : B → Keys) (emptyDict : m Dict)
    (zip : B → Keys → List (α × K)) (getOrInsert : Dict → α → K → m Unit)
    (get : Dict → α → Option K → m (Option K)) (collect : List (Option K) → m A)
    (a : List α) (b : B) : m A := do
  let inds := keys b
  let dict ← emptyDict
  for (value, index) in zip b inds do getOrInsert dict value index
  collect (← a.mapM (fun i => get dict i none))

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
def findinSet [Monad m] (empty : m B) (pairs : A → List (K × α))
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

/--
Julia source: base/array.jl:2961-2961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(pred::Fix2{typeof(in)}, x::AbstractArray) = _findin(x, pred.x)
```
-/
def findallIn2961 [Monad m] (findin : A → B → m C) (pred : B) (x : A) : m C :=
  findin x pred

/--
Julia source: base/array.jl:2962-2962 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(pred::Fix2{typeof(in)}, x::Tuple) = _findin(x, pred.x)
```
-/
def findallIn2962 [Monad m] (findin : A → B → m C) (pred : B) (x : A) : m C :=
  findin x pred

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
def filterAbstractArray [Monad m] (linear : A → Bool) (similarBool : A → m Mask)
    (mapPredicate : (α → m Bool) → Mask → A → m Mask) (getMask : A → Mask → m B)
    (length : A → m I) (allocateIndices : I → m Indices)
    (eachindex : A → List I) (setIndex : Indices → I → I → m Unit)
    (get : A → I → m α) (test : α → m Bool) (resize : Indices → I → m Unit)
    (getIndices : A → Indices → m B) (empty : Indices → m Unit)
    (sizehint : Indices → I → m Unit) (a : A) : m B := do
  if !(linear a) then return ← getMask a (← mapPredicate test (← similarBool a) a)
  let mut j := one
  let idxs ← allocateIndices (← length a)
  for idx in eachindex a do
    setIndex idxs idx j
    let ai ← get a idx
    let keep ← test ai
    j := if keep then j + one else j
  resize idxs (j - one)
  let res ← getIndices a idxs
  empty idxs
  sizehint idxs zero
  pure res

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
def filterFix1 (filter : F → A → B) (f : F) : A → B := fun x => filter f x

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

/--
Julia source: base/array.jl:3196-3196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
vectorfilter(T::Type, f, v) = T[x for x in v if f(x)]
```
-/
def vectorfilter [Monad m] (literal : List α → m A) (test : α → m Bool) (v : List α) : m A := do
  literal (← v.filterM test)

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
def intersectRangeVector [Monad m] (intersect : A → R → m B) (r : R) (v : A) : m B :=
  intersect v r

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
    (isBool : Z → Bool) (getindex : R → Z → m α) (r : R) (i : Z) : m α :=
  if isBool i then throw (.argument "invalid index of type Bool") else getindex r i

-- Declaration without a method body.
-- Source: base/array.jl:3233-3233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function wrap end
-- /Source

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
  if !(memlen ≥ len) then throw (.dimensionMismatch "array exceeds underlying memory")
  pure ref

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
    (_len : I) (_dims : List I) (_product : I) : m α :=
  throw (.dimensionMismatch "array exceeds underlying memory")

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
  (JInt.convert .i64 i.val).mapError (fun _ => .inexact)

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
  copyto288 (copytoImpl Subtype.val heapLength heapLength heapBounds heapBounds
    (· - ·) (· - ·) pure pure pure heapReference heapReference (heapCopyReferences convert))

def heapWholeCopy (convert : Option α → Except Error (Option α)) :=
  copyto325 (copyto2arg (fun _ => pure one) (fun _ => pure one) heapLength
    (heapCheckedCopy convert))

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

def heapAllocateArray (elementType : Tag) (dimensions : List Nat) : VectorM α (HeapArray Tag) := do
  if !(heapDimensionsFit dimensions) then throw .inexact
  if !(dimensions.prod < 2 ^ 63) then throw (.argument "invalid Array dimensions")
  let handle ← heapAllocate dimensions.prod
  pure ⟨handle, elementType, dimensions, dimensions.map (fun n => (1, n))⟩

/-- The Core vector allocator checks its signed dimension and gives it distinct storage. -/
def heapVectorAllocate {Tag α : Type} (target : Tag) (n : I) : VectorM α (HeapArray Tag) :=
  if n.val < 0 then throw (.argument "invalid Array dimensions")
  else heapAllocateArray target [n.val.toNat]

def heapAllocateIntDims (target : Tag) (dims : List I) : VectorM α (HeapArray Tag) := do
  if dims.any (fun dim => decide (dim.val < 0)) then
    throw (.argument "invalid Array dimensions")
  heapAllocateArray target (dims.map (fun dim => dim.val.toNat))

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

def mutableUnset (a : Nat) (i : I) : MutationM α Unit := do
  let _ ← unsetindexInt mutableBounds mutableMemoryref
    (fun ref => memoryWrite ref.1 ref.2 none) a i
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
    (copytoImpl Subtype.val mutableLength mutableLength mutableBounds mutableBounds
      (· - ·) (· - ·) pure pure pure mutableMemoryref mutableMemoryref
      (fun d s n => memoryMove d.1 d.2 s.1 s.2 n))
    dest doffs src soffs n
  pure ()

def mutableAllocate (_a : Nat) (n : I) : MutationM α Nat := do
  if n < zero then throw (.argument "negative array size")
  let s : MutableMemory α ← get
  let mem := s.memories.length
  let handle := s.arrays.length
  set { s with
    memories := s.memories ++ [List.replicate n.val.toNat none]
    arrays := s.arrays ++ [MutableVector.mk (mem, one) n] }
  pure handle

def mutableStorage : Storage (MutationM α) Nat Nat (Nat × I) where
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
  allocate := fun _ n => do
    if n < zero then throw (.argument "negative memory size")
    let s ← get
    let mem := s.memories.length
    modify fun s => { s with memories := s.memories ++ [List.replicate n.val.toNat none] }
    pure mem
  copyMemory := memoryMove
  copyRef := fun d s n => memoryMove d.1 d.2 s.1 s.2 n
  unsetMemory := fun mem i => memoryWrite mem i none
  unsetArray := mutableUnset
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

def mutablePush (a : Nat) (x : α) : MutationM α Unit := do
  let _ ← push1361 (growend mutableStorage pure (growendInternal mutableStorage))
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
The ten declaration-only rows have no Julia method body.
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
391 -> copyArray
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
581 -> declaration only
583 -> fillVarargs
584 -> fillMixedDims
585 -> fill585
586 -> fill586
587 -> fill587
608 -> declaration only
629 -> declaration only
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
972 -> declaration only
974 -> getindexCartesian
981 -> getindexUnitRange
993 -> getindexBoolRange
995 -> getindexColon
1005 -> getindexRange
1029 -> declaration only
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
1351 -> declaration only
1353 -> push
1361 -> push1361
1368 -> push1368
1373 -> pushAnyMany
1420 -> declaration only
1422 -> appendVector
1430 -> appendIterator
1431 -> pushMany
1432 -> appendMany
1434 -> appendSized
1442 -> appendUnsized
1478 -> declaration only
1480 -> prependVector
1495 -> prependIterator
1496 -> pushfirstMany
1497 -> prependMany
1499 -> prependSized
1512 -> prependUnsized
1559 -> resize
1610 -> declaration only
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
3233 -> declaration only
3236 -> wrapCheck
3244 -> invalidWrapError
3249 -> wrapRefDims
3255 -> wrapMemoryDims
3260 -> wrapRefLength
3265 -> wrapMemoryLength
3270 -> wrapMemory
-/

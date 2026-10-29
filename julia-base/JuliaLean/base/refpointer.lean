import JuliaLean.Core
import JuliaLean.base.pointer

/-!
# Model of `base/refpointer.jl`

Typed model of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform.
Pointer values and arithmetic use `JuliaLean.base.pointer`; `RefValue` constructors from another
Julia file and `AbstractArray` operations remain typed parameters.
An `AbstractArray` remains a typed value with its `getindex` and `setindex!` operations supplied.
Pointer-array conversions model the array loop as an ordered traversal of its elements.
-/

namespace JuliaLean.base.refpointer

open JuliaLean

abbrev I64 := JInt .i64

def int64 (n : Int) : I64 := JInt.lit .i64 n

inductive RefElementType : Type 1 where
  | any
  | element (α : Type)

inductive RefIteratorSize where
  | hasShape0
  deriving DecidableEq

inductive RefError where
  | errorException (message : String)
  deriving DecidableEq, Repr

structure RefArray (T A R : Type) where
  x : A
  index : I64
  roots : R

structure PointerArrayTypeTests where
  sameElementType : Bool
  isBitsElement : Bool
  pointerOrCStringLayout : Bool
  elementSubtypeOfPointer : Bool

inductive PointerArrayRef (T P Existing Root : Type) where
  | existing (reference : Existing)
  | direct (reference : RefArray P (List T) Unit)
  | converted (reference : RefArray P (List P) (List Root))

private def convertPointerArrayLoop {T P Root Q : Type}
    (cconvert : T → Jl Root) (unsafeConvert : Root → Jl Q)
    (assertPointer : Q → Jl P) : List T → Jl (List P × List Root)
  | [] => .ok ([], [])
  | value :: values => do
      let root ← cconvert value
      let pointer ← unsafeConvert root
      let pointer ← assertPointer pointer
      let (pointers, roots) ← convertPointerArrayLoop cconvert unsafeConvert assertPointer values
      pure (pointer :: pointers, root :: roots)

/--
Julia source: base/refpointer.jl:97-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(x::Type{<:Ref{T}}) where {T} = @isdefined(T) ? T : Any
```
-/
def refEltype (elementType : Option Type) : RefElementType :=
  match elementType with
  | some α => .element α
  | none => .any

/--
Julia source: base/refpointer.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Ref{T}}, x::Ref{T}) where {T} = x
```
-/
def convertRefSame {R : Type} (x : R) : R := x

/--
Julia source: base/refpointer.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(x::Ref) = ()
```
-/
def refSize {R : Type} (_x : R) : Unit := ()

/--
Julia source: base/refpointer.jl:100-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(x::Ref) = ()
```
-/
def refAxes {R : Type} (_x : R) : Unit := ()

/--
Julia source: base/refpointer.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(x::Ref) = 1
```
-/
def refLength {R : Type} (_x : R) : I64 := int64 1

/--
Julia source: base/refpointer.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(x::Ref) = false
```
-/
def refIsEmpty {R : Type} (_x : R) : Bool := false

/--
Julia source: base/refpointer.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(x::Ref) = 0
```
-/
def refNdims {R : Type} (_x : R) : I64 := int64 0

/--
Julia source: base/refpointer.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(::Type{<:Ref}) = 0
```
-/
def refNdimsType (_refType : Type) : I64 := int64 0

/--
Julia source: base/refpointer.jl:105-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::Ref) = (r[], nothing)
```
-/
def iterateRef {R α E : Type} (get : R → Except E α) (r : R) : Except E (α × Option Unit) := do
  let value ← get r
  pure (value, none)

/--
Julia source: base/refpointer.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::Ref, s) = nothing
```
-/
def iterateRefState {R S α : Type} (_r : R) (_state : S) : Option (α × Option Unit) := none

/--
Julia source: base/refpointer.jl:107-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Ref}) = HasShape{0}()
```
-/
def refIteratorSize : RefIteratorSize := .hasShape0

/--
Julia source: base/refpointer.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ref{T}}, x::Ref{T}) where {T} = unsafe_convert(Ptr{T}, x)
```
-/
def unsafeConvertRefSame {R P : Type} (unsafeConvert : R → Jl P) (x : R) : Jl P :=
  unsafeConvert x

/--
Julia source: base/refpointer.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ref{T}}, x) where {T} = unsafe_convert(Ptr{T}, x)
```
-/
def unsafeConvertRefAny {X P : Type} (unsafeConvert : X → Jl P) (x : X) : Jl P :=
  unsafeConvert x

/--
Julia source: base/refpointer.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Ref{T}}, x) where {T} = RefValue{T}(x)::RefValue{T}
```
-/
def convertRefValue {X R : Type} (construct : X → Jl R) (x : X) : Jl R :=
  construct x

/--
Julia source: base/refpointer.jl:116-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct RefArray{T,A<:AbstractArray{T},R} <: Ref{T}
    x::A
    i::Int
    roots::R # should be either ::Nothing or ::Any
    RefArray{T,A,R}(x,i,roots=nothing) where {T,A<:AbstractArray{T},R} = new(x,i,roots)
end
```
-/
def makeRefArray {T A R : Type} (x : A) (index : I64) (roots : R) : RefArray T A R :=
  ⟨x, index, roots⟩

/--
Julia source: base/refpointer.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
RefArray(x::AbstractArray{T}, i::Int, roots::Any) where {T} = RefArray{T,typeof(x),Any}(x, i, roots)
```
-/
def refArrayIntAnyRoots {T A R : Type} (x : A) (index : I64) (roots : R) : RefArray T A R :=
  makeRefArray x index roots

/--
Julia source: base/refpointer.jl:123-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
RefArray(x::AbstractArray{T}, i::Int=1, roots::Nothing=nothing) where {T} = RefArray{T,typeof(x),Nothing}(x, i, nothing)
```
-/
def refArrayIntNothingRoots {T A : Type} (x : A) (index : Option I64) : RefArray T A Unit :=
  makeRefArray x (index.getD (int64 1)) ()

/--
Julia source: base/refpointer.jl:124-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
RefArray(x::AbstractArray{T}, i::Integer, roots::Any) where {T} = RefArray{T,typeof(x),Any}(x, Int(i), roots)
```
-/
def refArrayIntegerAnyRoots {T A R I : Type} (toInt : I → Jl I64)
    (x : A) (index : I) (roots : R) : Jl (RefArray T A R) := do
  let index ← toInt index
  pure (refArrayIntAnyRoots x index roots)

/--
Julia source: base/refpointer.jl:125-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
RefArray(x::AbstractArray{T}, i::Integer, roots::Nothing=nothing) where {T} = RefArray{T,typeof(x),Nothing}(x, Int(i), nothing)
```
-/
def refArrayIntegerNothingRoots {T A I : Type} (toInt : I → Jl I64)
    (x : A) (index : I) : Jl (RefArray T A Unit) := do
  let index ← toInt index
  pure (refArrayIntNothingRoots x (some index))

/--
Julia source: base/refpointer.jl:126-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Ref{T}}, x::AbstractArray{T}) where {T} = RefArray(x, 1)
```
-/
def convertArrayToRef {T A : Type} (x : A) : RefArray T A Unit :=
  refArrayIntNothingRoots x (some (int64 1))

/--
Julia source: base/refpointer.jl:128-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_convert(P::Union{Type{Ptr{T}},Type{Ptr{Cvoid}}}, b::RefArray{T})::P where T
    if allocatedinline(T)
        p = pointer(b.x, b.i)
    elseif isconcretetype(T) && ismutabletype(T)
        p = pointer_from_objref(b.x[b.i])
    else
        # see comment on equivalent branch for RefValue
        p = pointerref(Ptr{Ptr{Cvoid}}(pointer(b.x, b.i)), 1, Core.sizeof(Ptr{Cvoid}))
    end
    return p
end
```
-/
def unsafeConvertRefArray {T A R P Q V : Type}
    (allocatedinline isConcrete isMutable : Type → Bool)
    (pointer : A → I64 → Jl P) (getindex : A → I64 → Jl V)
    (pointerFromObjRef : V → P) (toPtrPtrCvoid : P → Q)
    (pointerref : Q → I64 → I64 → Jl P) (sizePtrCvoid : I64)
    (b : RefArray T A R) : Jl P := do
  if allocatedinline T then
    pointer b.x b.index
  else if isConcrete T && isMutable T then do
    let value ← getindex b.x b.index
    pure (pointerFromObjRef value)
  else do
    let p ← pointer b.x b.index
    pointerref (toPtrPtrCvoid p) (int64 1) sizePtrCvoid

/--
Julia source: base/refpointer.jl:139-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_convert(::Type{Ptr{Any}}, b::RefArray{Any})::Ptr{Any}
    return pointer(b.x, b.i)
end
```
-/
inductive AnyElement where
  | any

def unsafeConvertRefArrayAny {A R P : Type}
    (pointer : A → I64 → Jl P) (b : RefArray AnyElement A R) : Jl P :=
  pointer b.x b.index

/--
Julia source: base/refpointer.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Ref(x::Any) = RefValue(x)
```
-/
def refAny {X R : Type} (construct : X → Jl R) (x : X) : Jl R :=
  construct x

/--
Julia source: base/refpointer.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Ref{T}() where {T} = RefValue{T}() # Ref{T}()
```
-/
def refUndefined {T R : Type} (construct : Type → Jl R) : Jl R :=
  construct T

/--
Julia source: base/refpointer.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Ref{T}(x) where {T} = RefValue{T}(x) # Ref{T}(x)
```
-/
def refTyped {T X R : Type} (construct : Type → X → Jl R) (x : X) : Jl R :=
  construct T x

/--
Julia source: base/refpointer.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Ref(x::Ref, i::Integer) = (i != 1 && error("Ref only has one element"); x)
```
-/
def refRefIndex {R I : Type} [DecidableEq I] (x : R) (index one : I) : Except RefError R :=
  if index != one then .error (.errorException "Ref only has one element") else .ok x

/--
Julia source: base/refpointer.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Ref(x::Ptr{T}, i::Integer) where {T} = x + (i - 1) * Core.sizeof(T)
```
-/
def refPointerIndex {T I S O : Type}
    (one : I) (subtract : I → I → I) (sizeOf : Type → S) (multiply : I → S → O)
    (toUInt : O → JuliaLean.base.pointer.U64) (x : JuliaLean.base.pointer.Ptr T)
    (index : I) : JuliaLean.base.pointer.Ptr T :=
  JuliaLean.base.pointer.ptrAddInteger toUInt x (multiply (subtract index one) (sizeOf T))

/--
Julia source: base/refpointer.jl:154-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Ref{P}(a::Array{T}) where P<:Union{Ptr,Cwstring,Cstring} where T
        if P == T
            return getfield(a, :ref)
        elseif (isbitstype(T) ? T <: Ptr || T <: Union{Cwstring,Cstring} : T <: eltype(P))
            # this Array already has the right memory layout for the requested Ref
            # but the wrong eltype for the constructor
            return RefArray{P,typeof(a),Nothing}(a, 1, nothing) # effectively a no-op
        else
            ptrs = Vector{P}(undef, length(a)+1)
            roots = Vector{Any}(undef, length(a))
            for i = 1:length(a)
                root = cconvert(P, a[i])
                ptrs[i] = unsafe_convert(P, root)::P
                roots[i] = root
            end
            ptrs[length(a)+1] = C_NULL
            return RefArray{P,typeof(ptrs),typeof(roots)}(ptrs, 1, roots)
        end
    end
```
-/
def refPointerArray {T P Existing Root Q : Type}
    (tests : PointerArrayTypeTests) (arrayRef : List T → Existing)
    (cconvert : T → Jl Root) (unsafeConvert : Root → Jl Q)
    (assertPointer : Q → Jl P) (null : P) (array : List T) :
    Jl (PointerArrayRef T P Existing Root) := do
  if tests.sameElementType then
    pure (.existing (arrayRef array))
  else if (if tests.isBitsElement then tests.pointerOrCStringLayout else tests.elementSubtypeOfPointer) then
    pure (.direct (makeRefArray array (int64 1) ()))
  else do
    let (pointers, roots) ← convertPointerArrayLoop cconvert unsafeConvert assertPointer array
    let pointers := pointers ++ [null]
    pure (.converted (makeRefArray pointers (int64 1) roots))

/--
Julia source: base/refpointer.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Ref(x::AbstractArray, i::Integer) = RefArray(x, i)
```
-/
def refAbstractArray {T A I : Type} (toInt : I → Jl I64) (x : A) (index : I) :
    Jl (RefArray T A Unit) :=
  refArrayIntegerNothingRoots toInt x index

/--
Julia source: base/refpointer.jl:176-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{P}}, a::Array{<:Union{Ptr,Cwstring,Cstring}}) where {P<:Union{Ptr,Cwstring,Cstring}} = getfield(a, :ref)
```
-/
def cconvertPtrArrayExisting {A R : Type}
    (getArrayRef : A → R) (a : A) : R :=
  getArrayRef a

/--
Julia source: base/refpointer.jl:177-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ref{P}}, a::Array{<:Union{Ptr,Cwstring,Cstring}}) where {P<:Union{Ptr,Cwstring,Cstring}} = getfield(a, :ref)
```
-/
def cconvertRefArrayExisting {A R : Type}
    (getArrayRef : A → R) (a : A) : R :=
  getArrayRef a

/--
Julia source: base/refpointer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{P}}, a::Array) where {P<:Union{Ptr,Cwstring,Cstring}} = Ref{P}(a)
```
-/
def cconvertPtrArray {T P Existing Root Q : Type}
    (tests : PointerArrayTypeTests) (arrayRef : List T → Existing)
    (cconvert : T → Jl Root) (unsafeConvert : Root → Jl Q)
    (assertPointer : Q → Jl P) (null : P) (array : List T) :
    Jl (PointerArrayRef T P Existing Root) :=
  refPointerArray tests arrayRef cconvert unsafeConvert assertPointer null array

/--
Julia source: base/refpointer.jl:179-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ref{P}}, a::Array) where {P<:Union{Ptr,Cwstring,Cstring}} = Ref{P}(a)
```
-/
def cconvertRefPointerArray {T P Existing Root Q : Type}
    (tests : PointerArrayTypeTests) (arrayRef : List T → Existing)
    (cconvert : T → Jl Root) (unsafeConvert : Root → Jl Q)
    (assertPointer : Q → Jl P) (null : P) (array : List T) :
    Jl (PointerArrayRef T P Existing Root) :=
  refPointerArray tests arrayRef cconvert unsafeConvert assertPointer null array

/--
Julia source: base/refpointer.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ref{T}}, t::NTuple{N,T}) where {N,T} = Ref{NTuple{N,T}}(t)
```
-/
def cconvertTupleRef {T : Type} {N : Nat} {R : Type}
    (construct : Vector T N → Jl R) (tuple : Vector T N) : Jl R :=
  construct tuple

/--
Julia source: base/refpointer.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ref{T}}, r::Ref{NTuple{N,T}}) where {N,T} = r
```
-/
def cconvertTupleRefIdentity {R : Type} (reference : R) : R := reference

/--
Julia source: base/refpointer.jl:184-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ref{T}}, r::Ref{NTuple{N,T}}) where {N,T} =
    convert(Ptr{T}, unsafe_convert(Ptr{NTuple{N,T}}, r))
```
-/
def unsafeConvertRefTuple {R TuplePointer RefPointer : Type}
    (unsafeConvert : R → Jl TuplePointer) (convert : TuplePointer → Jl RefPointer)
    (reference : R) : Jl RefPointer := do
  let pointer ← unsafeConvert reference
  convert pointer

/--
Julia source: base/refpointer.jl:186-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{T}}, r::Ref{NTuple{N,T}}) where {N,T} =
    convert(Ptr{T}, unsafe_convert(Ptr{NTuple{N,T}}, r))
```
-/
def unsafeConvertPtrTupleRef {R TuplePointer ElementPointer : Type}
    (unsafeConvert : R → Jl TuplePointer) (convert : TuplePointer → Jl ElementPointer)
    (reference : R) : Jl ElementPointer := do
  let pointer ← unsafeConvert reference
  convert pointer

/--
Julia source: base/refpointer.jl:188-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{T}}, r::Ptr{NTuple{N,T}}) where {N,T} =
    convert(Ptr{T}, r)
```
-/
def unsafeConvertPtrTuple {TuplePointer ElementPointer : Type}
    (convert : TuplePointer → Jl ElementPointer) (pointer : TuplePointer) : Jl ElementPointer :=
  convert pointer

/--
Julia source: base/refpointer.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(b::RefArray) = b.x[b.i]
```
-/
def getindexRefArray {T A R : Type} (getindex : A → I64 → Jl T)
    (b : RefArray T A R) : Jl T :=
  getindex b.x b.index

/--
Julia source: base/refpointer.jl:194-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(b::RefArray, x) = (b.x[b.i] = x; b)
```
-/
def setindexRefArray {T A R : Type} (setindex : A → I64 → T → Jl A)
    (b : RefArray T A R) (value : T) : Jl (RefArray T A R) := do
  let array ← setindex b.x b.index value
  pure { b with x := array }

end JuliaLean.base.refpointer
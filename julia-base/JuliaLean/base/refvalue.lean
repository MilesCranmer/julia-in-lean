import JuliaLean.Core
import JuliaLean.base.pointer
import JuliaLean.base.refpointer

/-!
# Model of `base/refvalue.jl`

A `RefValue` carries its object address and distinguishes an uninitialized inline field from an
undefined reference field. Julia field conversion and object-pointer operations remain typed
parameters where their implementations live outside this file.
-/

namespace JuliaLean.base.refvalue

open JuliaLean JuliaLean.base.pointer JuliaLean.base.refpointer

/-- A `RefValue{T}` slot, including `new()`'s uninitialized inline storage. -/
inductive RefValueField (T : Type) where
  | undefined
  | uninitializedInline
  | assigned (value : T)

/--
Julia source: base/refvalue.jl:5-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct RefValue{T} <: Ref{T}
    x::T
    RefValue{T}() where {T} = new()
    RefValue{T}(x) where {T} = new(x)
end
```
-/
structure RefValue (T : Type) where
  address : Ptr Unit
  x : RefValueField T


inductive RefValueError (E : Type) where
  | undefRefError
  | conversionError (error : E)

abbrev RefValueResult (E : Type) (α : Type) := Except (RefValueError E) α

/-- Memory order used by `atomic_pointerref`. -/
inductive RefValueMemoryOrder where
  | monotonic
  deriving DecidableEq, Repr


/--
Julia source: base/refvalue.jl:7-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    RefValue{T}() where {T} = new()
```
-/
def refValueDefault {T : Type} (isBits : Type → Bool) (address : Ptr Unit) :
    RefValue T :=
  { address := address,
    x := if isBits T then .uninitializedInline else .undefined }
/--
Julia source: base/refvalue.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    RefValue{T}(x) where {T} = new(x)
```
-/
def refValueTyped {T X E : Type} (convert : X → Except E T) (address : Ptr Unit) (x : X) :
    RefValueResult E (RefValue T) :=
  match convert x with
  | .error error => .error (.conversionError error)
  | .ok value => .ok { address := address, x := .assigned value }

/--
Julia source: base/refvalue.jl:10-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
RefValue(x::T) where {T} = RefValue{T}(x)
```
-/
def refValueInferred {T E : Type} (convert : T → Except E T) (address : Ptr Unit) (x : T) :
    RefValueResult E (RefValue T) :=
  refValueTyped convert address x

/--
Julia source: base/refvalue.jl:11-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    isassigned(ref::RefValue)::Bool

Test whether the given [`Ref`](@ref) is associated with a value.
This is always true for a [`Ref`](@ref) of a bitstype object.
Return `false` if the reference is undefined.

# Examples
```jldoctest
julia> ref = Ref{Function}()
Base.RefValue{Function}(#undef)

julia> isassigned(ref)
false

julia> ref[] = (foobar(x) = x)
foobar (generic function with 1 method)

julia> isassigned(ref)
true

julia> isassigned(Ref{Int}())
true
```
"""
isassigned(x::RefValue) = isdefined(x, :x)
````
-/
def isassigned {T : Type} (isBits : Type → Bool) (x : RefValue T) : Bool :=
  match x.x with
  | .undefined => isBits T
  | .uninitializedInline | .assigned _ => true

/--
Julia source: base/refvalue.jl:38-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_convert(P::Union{Type{Ptr{T}},Type{Ptr{Cvoid}}}, b::RefValue{T})::P where T
    if allocatedinline(T)
        p = pointer_from_objref(b)
    elseif isconcretetype(T) && ismutabletype(T)
        p = pointer_from_objref(b.x)
    else
        # If the slot is not leaf type, it could be either immutable or not.
        # If it is actually an immutable, then we can't take its pointer directly
        # Instead, explicitly load the pointer from the `RefValue`,
        # which also ensures this returns same pointer as the one rooted in the `RefValue` object.
        p = atomic_pointerref(Ptr{Ptr{Cvoid}}(pointer_from_objref(b)), :monotonic)
        if p == C_NULL
            throw(UndefRefError())
        end
    end
    return p
end
```
-/
def unsafeConvert {T P E : Type}
    (allocatedinline isconcretetype ismutabletype : Type → Bool)
    (pointerFromObjRef : {A : Type} → A → Ptr Unit)
    (atomicPointerRef : Ptr (Ptr Unit) → RefValueMemoryOrder → Ptr Unit)
    (b : RefValue T) : RefValueResult E (Ptr P) :=
  if allocatedinline T then
    .ok (convertPtrType (pointerFromObjRef b))
  else if isconcretetype T && ismutabletype T then
    match b.x with
    | .undefined | .uninitializedInline => .error .undefRefError
    | .assigned value => .ok (convertPtrType (pointerFromObjRef value))
  else
    let p := atomicPointerRef (convertPtrType (pointerFromObjRef b)) .monotonic
    if p.address = C_NULL.address then .error .undefRefError
    else .ok (convertPtrType p)

/--
Julia source: base/refvalue.jl:55-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_convert(::Type{Ptr{Any}}, b::RefValue{Any})::Ptr{Any}
    return pointer_from_objref(b)
end
```
-/
def unsafeConvertAny (pointerFromObjRef : {A : Type} → A → Ptr Unit)
    (b : RefValue AnyElement) : Ptr AnyElement :=
  convertPtrType (pointerFromObjRef b)

/--
Julia source: base/refvalue.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(b::RefValue) = b.x
```
-/
def getindex {T E : Type} (uninitializedValue : T) (b : RefValue T) : RefValueResult E T :=
  match b.x with
  | .undefined => .error .undefRefError
  | .uninitializedInline => .ok uninitializedValue
  | .assigned value => .ok value

/--
Julia source: base/refvalue.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(b::RefValue, x) = (b.x = x; b)
```
-/
def setindex! {T X E : Type} (convert : X → Except E T) (b : RefValue T) (x : X) :
    RefValueResult E (RefValue T) :=
  match convert x with
  | .error error => .error (.conversionError error)
  | .ok value => .ok { b with x := .assigned value }

end JuliaLean.base.refvalue

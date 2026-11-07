import JuliaLean.Core
import JuliaLean.base.genericmemory
import JuliaLean.base.array
import JuliaLean.base.iddict

/-!
# Model of `base/deepcopy.jl`

The stack dictionary is a native IdDict address in the shared heap. All recursive calls, field operations, allocation, and errors use the same execution state, so aliases and failed calls retain memo-table changes.
-/

namespace JuliaLean.base.deepcopy

open JuliaLean
open JuliaLean.src.identity_runtime (Word M Error fail)

structure StackOps where
  runtime : iddict.Callees
  box : {X : Type} → X → Word
  cast : {X : Type} → Word → M X
  assertSameType : Word → Word → M Word

def stackLookup (ops : StackOps) (dict key : Word) : M (Option Word) := do
  if ← iddict.inKeySet ops.runtime dict key then
    return some (← iddict.getindex ops.runtime dict key)
  else return none

def stackLookupTyped {X : Type} (ops : StackOps) (dict : Word) (x : X) : M (Option X) := do
  match ← stackLookup ops dict (ops.box x) with
  | none => pure none
  | some value => pure (some (← ops.cast value))

def stackInsert (ops : StackOps) (dict key value : Word) : M Unit := do
  let _ ← iddict.setindex! ops.runtime dict value key
  pure ()

def stackInsertTyped {X : Type} (ops : StackOps) (dict : Word) (x y : X) : M Unit :=
  stackInsert ops dict (ops.box x) (ops.box y)

/--
Julia source: base/deepcopy.jl:10-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

Create a deep copy of `x`: everything is copied recursively, resulting in a fully
independent object. For example, deep-copying an array creates deep copies of all
the objects it contains and produces a new array with the consistent relationship
structure (e.g., if the first two elements are the same object in the original array,
the first two elements of the new array will also be the same `deepcopy`ed object).
Calling `deepcopy` on an object should generally
have the same effect as serializing and then deserializing it.

While it isn't normally necessary, user-defined types can override the default `deepcopy`
behavior by defining a specialized version of the function
`deepcopy_internal(x::T, dict::IdDict)` (which shouldn't otherwise be used),
where `T` is the type to be specialized for, and `dict` keeps track of objects copied
so far within the recursion. Within the definition, `deepcopy_internal` should be used
in place of `deepcopy`, and the `dict` variable should be
updated as appropriate before returning.

!!! warning
    It is better to avoid this function in favor of custom `copy` methods or use-case-specific
    copying functions. `deepcopy` is slow and can easily copy too many objects, or generate an
    object that violates invariants, since it does not respect abstraction boundaries.
"""
function deepcopy(@nospecialize x)
    isbitstype(typeof(x)) && return x
    return deepcopy_internal(x, IdDict())::typeof(x)
end
```
-/
def deepcopy {X TypeRep : Type}
    (ops : StackOps) (typeOf : X → TypeRep) (isBitstype : TypeRep → Bool)
    (deepcopyInternal : Word → Word → M Word) (x : X) : M X := do
  if isBitstype (typeOf x) then pure x
  else
    let dict ← iddict.emptyAny ops.runtime
    ops.cast (← deepcopyInternal (ops.box x) dict)

/--
Julia source: base/deepcopy.jl:37-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deepcopy_internal(x::Union{Symbol,Core.MethodInstance,Method,GlobalRef,DataType,Union,UnionAll,Task,Regex,
                           Core.CancellationTokenSource},
                  stackdict::IdDict) = x
```
-/
def deepcopyIdentity {X : Type} (x : X) (_dict : Word) : M X := pure x

/-- Tuple access and construction are the typed interface to `x[i]` and `ntuple`. -/
structure TupleOps (Tuple : Type) where
  length : Tuple → Nat
  get : Tuple → Nat → M Word
  construct : Tuple → List Word → M Tuple

/-- Recursively copy values in the given index order, threading memoized identities. -/
def copySequence (copy : Word → Word → M Word) (get : Nat → M Word) :
    List Nat → Word → M (List Word)
  | [], _ => pure []
  | index :: rest, dict => do
    let value ← copy (← get index) dict
    let values ← copySequence copy get rest dict
    pure (value :: values)

/--
Julia source: base/deepcopy.jl:40-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deepcopy_internal(x::Tuple, stackdict::IdDict) =
    ntuple(i->deepcopy_internal(x[i], stackdict), length(x))
```
-/
def deepcopyTuple {Tuple : Type} (tupleOps : TupleOps Tuple)
    (copy : Word → Word → M Word) (x : Tuple) (dict : Word) : M Tuple := do
  let values ← copySequence copy (fun index => tupleOps.get x (index+1))
    (List.range (tupleOps.length x)) dict
  tupleOps.construct x values

/--
Julia source: base/deepcopy.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deepcopy_internal(x::Module, stackdict::IdDict) = error("deepcopy of Modules not supported")
```
-/
def deepcopyModule {Module : Type} (errorException : String → Error)
    (_module : Module) (_dict : Word) : M Module :=
  fail (errorException "deepcopy of Modules not supported")

/-- Buffer allocation, indexed writes, and `Core.svec` construction for a `SimpleVector`. -/
structure SimpleVectorOps (SVec Buffer : Type) where
  length : SVec → M (JInt .i64)
  get : SVec → JInt .i64 → M Word
  newBuffer : JInt .i64 → M Buffer
  setBuffer : Buffer → JInt .i64 → Word → M Unit
  makeSVec : Buffer → M SVec

def copySimpleVectorItems {SVec Buffer : Type}
    (ops : SimpleVectorOps SVec Buffer) (copy : Word → Word → M Word)
    (x : SVec) (buffer : Buffer) : List Nat → Word → M Unit
  | [], _ => pure ()
  | offset :: rest, dict => do
    let index := JInt.wrap .i64 (Int.ofNat (offset+1))
    let value ← copy (← ops.get x index) dict
    ops.setBuffer buffer index value
    copySimpleVectorItems ops copy x buffer rest dict

/--
Julia source: base/deepcopy.jl:44-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(x::SimpleVector, stackdict::IdDict)
    if haskey(stackdict, x)
        return stackdict[x]::typeof(x)
    end
    y = Core.svec(Any[deepcopy_internal(x[i], stackdict) for i = 1:length(x)]...)
    stackdict[x] = y
    return y
end
```
-/
def deepcopySimpleVector {SVec Buffer : Type}
    (stackOps : StackOps) (ops : SimpleVectorOps SVec Buffer)
    (copy : Word → Word → M Word) (x : SVec) (dict : Word) : M SVec := do
  match ← stackLookupTyped stackOps dict x with
  | some cached => pure cached
  | none =>
    let length ← ops.length x
    let buffer ← ops.newBuffer length
    copySimpleVectorItems ops copy x buffer (List.range length.val.toNat) dict
    let y ← ops.makeSVec buffer
    stackInsertTyped stackOps dict x y
    pure y

structure StringCopyOps (String : Type) where
  unsafeCopy : String → M String

/--
Julia source: base/deepcopy.jl:53-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(x::String, stackdict::IdDict)
    if haskey(stackdict, x)
        return stackdict[x]::typeof(x)
    end
    y = GC.@preserve x unsafe_string(pointer(x), sizeof(x))
    stackdict[x] = y
    return y
end
```
-/
def deepcopyString {String : Type}
    (stackOps : StackOps) (ops : StringCopyOps String) (x : String) (dict : Word) : M String := do
  match ← stackLookupTyped stackOps dict x with
  | some cached => pure cached
  | none =>
    let y ← ops.unsafeCopy x
    stackInsertTyped stackOps dict x y
    pure y

/-- Type layout, field access, and raw runtime allocation used by the generic struct method. -/
structure GenericStructOps (X TypeRep Fields : Type) where
  typeOf : X → M TypeRep
  nfields : X → M (JInt .i64)
  isMutable : X → M Bool
  isBitstype : TypeRep → Bool
  isBitsValue : Word → Bool
  isDefined : X → JInt .i64 → M Bool
  getField : X → JInt .i64 → M Word
  newUninitialized : TypeRep → M X
  setNthField : X → JInt .u64 → Word → M Unit
  newFieldVector : JInt .i64 → M Fields
  setFieldVector : Fields → JInt .i64 → Word → M Unit
  csizeIndex : JInt .i64 → M (JInt .u64)
  uint32Count : JInt .i64 → M (JInt .u32)
  newStructv : TypeRep → Fields → JInt .u32 → M X

def deepcopyField (stackOps : StackOps) (isBitsValue : Word → Bool)
    (copy : Word → Word → M Word) (value dict : Word) : M Word := do
  if isBitsValue value then pure value
  else stackOps.assertSameType value (← copy value dict)

def copyMutableFields {X TypeRep Fields : Type}
    (stackOps : StackOps) (ops : GenericStructOps X TypeRep Fields)
    (copy : Word → Word → M Word) (source destination : X) : List Nat → Word → M Unit
  | [], _ => pure ()
  | offset :: rest, dict => do
    let index := JInt.wrap .i64 (Int.ofNat (offset+1))
    if ← ops.isDefined source index then
      let value ← deepcopyField stackOps ops.isBitsValue copy (← ops.getField source index) dict
      let fieldOffset ← ops.csizeIndex (JInt.wrap .i64 (Int.ofNat offset))
      ops.setNthField destination fieldOffset value
    copyMutableFields stackOps ops copy source destination rest dict

def copyImmutableFields {X TypeRep Fields : Type}
    (stackOps : StackOps) (ops : GenericStructOps X TypeRep Fields)
    (copy : Word → Word → M Word) (source : X) (buffer : Fields) (count : JInt .i64) :
    List Nat → Word → M (Fields × JInt .i64)
  | [], _ => pure (buffer, count)
  | offset :: rest, dict => do
    let index := JInt.wrap .i64 (Int.ofNat (offset+1))
    if ← ops.isDefined source index then
      let value ← deepcopyField stackOps ops.isBitsValue copy (← ops.getField source index) dict
      ops.setFieldVector buffer index value
      copyImmutableFields stackOps ops copy source buffer count rest dict
    else pure (buffer, JInt.wrap .i64 (Int.ofNat offset))

/--
Julia source: base/deepcopy.jl:62-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(@nospecialize(x), stackdict::IdDict)
    T = typeof(x)::DataType
    nf = nfields(x)
    if ismutable(x)
        if haskey(stackdict, x)
            return stackdict[x]::typeof(x)
        end
        y = ccall(:jl_new_struct_uninit, Any, (Any,), T)
        stackdict[x] = y
        for i in 1:nf
            if isdefined(x, i)
                xi = getfield(x, i)
                if !isbits(xi)
                    xi = deepcopy_internal(xi, stackdict)::typeof(xi)
                end
                ccall(:jl_set_nth_field, Cvoid, (Any, Csize_t, Any), y, i-1, xi)
            end
        end
    elseif nf == 0 || isbitstype(T)
        y = x
    else
        flds = Vector{Any}(undef, nf)
        for i in 1:nf
            if isdefined(x, i)
                xi = getfield(x, i)
                if !isbits(xi)
                    xi = deepcopy_internal(xi, stackdict)::typeof(xi)
                end
                flds[i] = xi
            else
                nf = i - 1 # rest of tail must be undefined values
                break
            end
        end
        y = ccall(:jl_new_structv, Any, (Any, Ptr{Any}, UInt32), T, flds, nf)
    end
    return y::T
end
```
-/
def deepcopyGeneric {X TypeRep Fields : Type}
    (stackOps : StackOps) (ops : GenericStructOps X TypeRep Fields)
    (copy : Word → Word → M Word) (x : X) (dict : Word) : M X := do
  let typeRep ← ops.typeOf x
  let fieldCount ← ops.nfields x
  if ← ops.isMutable x then
    match ← stackLookupTyped stackOps dict x with
    | some cached => pure cached
    | none =>
      let destination ← ops.newUninitialized typeRep
      stackInsertTyped stackOps dict x destination
      copyMutableFields stackOps ops copy x destination (List.range fieldCount.val.toNat) dict
      pure destination
  else if fieldCount.val == 0 || ops.isBitstype typeRep then pure x
  else
    let buffer ← ops.newFieldVector fieldCount
    let (buffer, count) ← copyImmutableFields stackOps ops copy x buffer fieldCount
      (List.range fieldCount.val.toNat) dict
    ops.newStructv typeRep buffer (← ops.uint32Count count)

/-- Memory and MemoryRef calls already modelled by `genericmemory.jl`, plus runtime allocation and reads. -/
structure MemoryOps (Memory PtrOffset Element TypeRep Ptr Preserve : Type) where
  access : JuliaLean.base.genericmemory.MemoryAccessOps M Memory PtrOffset Element Word
  copyOps : JuliaLean.base.genericmemory.MemoryCopyOps M Memory PtrOffset
    (JInt .i64) (JInt .i64) (JInt .i64) (JInt .i64) Ptr Preserve
  typeOf : Memory → M TypeRep
  eltype : Memory → M TypeRep
  isBitstype : TypeRep → Bool
  isBitsValue : Word → Bool
  length : Memory → M (JInt .i64)
  construct : JInt .i64 → M Memory
  allocate : TypeRep → JInt .i64 → M Memory
  memoryrefGet : JuliaLean.base.genericmemory.GenericMemoryRef Memory PtrOffset →
    JuliaLean.base.genericmemory.MemoryOrder → Bool → M Word
  toElement : Word → M Element

def copyMemoryItems {Memory PtrOffset Element TypeRep Ptr Preserve : Type}
    (stackOps : StackOps) (ops : MemoryOps Memory PtrOffset Element TypeRep Ptr Preserve)
    (copy : Word → Word → M Word)
    (source dest : JuliaLean.base.genericmemory.GenericMemoryRef Memory PtrOffset) :
    List Nat → Word → M Unit
  | [], _ => pure ()
  | offset :: rest, dict => do
    let index := JInt.wrap .i64 (Int.ofNat (offset+1))
    let sourceIndex ← ops.access.memoryrefNew source index false
    if ← ops.access.memoryrefIsAssigned sourceIndex .notAtomic false then
      let value ← deepcopyField stackOps ops.isBitsValue copy
        (← ops.memoryrefGet sourceIndex .notAtomic false) dict
      let destIndex ← ops.access.memoryrefNew dest index false
      let _ ← ops.access.memoryrefSet destIndex (← ops.toElement value) .notAtomic false
      pure ()
    copyMemoryItems stackOps ops copy source dest rest dict

/--
Julia source: base/deepcopy.jl:101-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(x::Memory, stackdict::IdDict)
    if haskey(stackdict, x)
        return stackdict[x]::typeof(x)
    end
    _deepcopy_memory_t(x, eltype(x), stackdict)
end
```
-/
def deepcopyMemory {Memory PtrOffset Element TypeRep Ptr Preserve : Type}
    (stackOps : StackOps) (ops : MemoryOps Memory PtrOffset Element TypeRep Ptr Preserve)
    (copyMemoryT : Memory → TypeRep → Word → M Memory)
    (x : Memory) (dict : Word) : M Memory := do
  match ← stackLookupTyped stackOps dict x with
  | some cached => pure cached
  | none => copyMemoryT x (← ops.eltype x) dict

/--
Julia source: base/deepcopy.jl:108-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _deepcopy_memory_t(@nospecialize(x::Memory), T, stackdict::IdDict)
    if isbitstype(T)
        return (stackdict[x]=copy(x))
    end
    dest = typeof(x)(undef, length(x))
    stackdict[x] = dest
    xr = memoryref(x)
    dr = memoryref(dest)
    for i = 1:length(x)
        xi = Core.memoryrefnew(xr, i, false)
        if Core.memoryref_isassigned(xi, :not_atomic, false)
            xi = Core.memoryrefget(xi, :not_atomic, false)
            if !isbits(xi)
                xi = deepcopy_internal(xi, stackdict)::typeof(xi)
            end
            di = Core.memoryrefnew(dr, i, false)
            Core.memoryrefset!(di, xi, :not_atomic, false)
        end
    end
    return dest
end
```
-/
def deepcopyMemoryT {Memory PtrOffset Element TypeRep Ptr Preserve : Type}
    (stackOps : StackOps) (ops : MemoryOps Memory PtrOffset Element TypeRep Ptr Preserve)
    (copy : Word → Word → M Word)
    (x : Memory) (elementType : TypeRep) (dict : Word) : M Memory := do
  if ops.isBitstype elementType then
    let copied ← JuliaLean.base.genericmemory.copyMemory (M := Memory) (P := PtrOffset)
      (T := Element) (Ptr := Ptr) (Token := Preserve) ops.copyOps ops.length ops.construct x
    stackInsertTyped stackOps dict x copied
    pure copied
  else
    let memoryType ← ops.typeOf x
    let length ← ops.length x
    let dest ← ops.allocate memoryType length
    stackInsertTyped stackOps dict x dest
    let sourceRef ← ops.access.memoryref x
    let destRef ← ops.access.memoryref dest
    let count ← ops.length x
    copyMemoryItems stackOps ops copy sourceRef destRef (List.range count.val.toNat) dict
    pure dest

/-- Array memory allocation and field access used by the generic `Array` constructor. -/
structure ArrayCopyOps (Array TypeRep Ref Size Mem : Type) where
  rank : TypeRep → Nat
  memoryLayout : TypeRep → Option JuliaLean.base.array.MemoryLayout
  emptyMemory : M Mem
  allocateMemory : Nat → M Mem
  constructHeader : Mem → List (JInt .i64) → M Array
  reference : Array → Ref
  size : Array → Size
  setReference : Array → Ref → M Unit
  setSize : Array → Size → M Unit

/--
Julia source: base/deepcopy.jl:129-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(x::Array{T, N}, stackdict::IdDict) where {T, N}
    if haskey(stackdict, x)
        return stackdict[x]::typeof(x)
    end
    y = stackdict[x] = Array{T, N}(undef, ntuple(Returns(0), Val{N}()))
    setfield!(y, :ref, deepcopy_internal(x.ref, stackdict))
    setfield!(y, :size, x.size)
    y
end
```
-/
def deepcopyArray {Array TypeRep Ref Size Mem : Type}
    (stackOps : StackOps) (ops : ArrayCopyOps Array TypeRep Ref Size Mem)
    (copy : Word → Word → M Word) (arrayType : TypeRep) (x : Array) (dict : Word) : M Array := do
  match ← stackLookupTyped stackOps dict x with
  | some cached => pure cached
  | none =>
    let dimensions := List.replicate (ops.rank arrayType) (JInt.wrap .i64 0)
    let destination ← JuliaLean.base.array.arrayUndef (ops.memoryLayout arrayType) ops.emptyMemory
      ops.allocateMemory ops.constructHeader dimensions
    stackInsertTyped stackOps dict x destination
    let copiedRef ← copy (stackOps.box (ops.reference x)) dict
    ops.setReference destination (← stackOps.cast copiedRef)
    ops.setSize destination (ops.size x)
    pure destination

/--
Julia source: base/deepcopy.jl:138-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(x::GenericMemoryRef, stackdict::IdDict)
    if haskey(stackdict, x)
        return stackdict[x]::typeof(x)
    end
    mem = getfield(x, :mem)
    dest = memoryref(deepcopy_internal(mem, stackdict)::typeof(mem))
    i = memoryrefoffset(x)
    i == 1 || (dest = Core.memoryrefnew(dest, i, true))
    return dest
end
```
-/
def deepcopyMemoryRef {Memory PtrOffset Element TypeRep Ptr Preserve : Type}
    (stackOps : StackOps) (ops : MemoryOps Memory PtrOffset Element TypeRep Ptr Preserve)
    (memoryrefoffset : JuliaLean.base.genericmemory.GenericMemoryRef Memory PtrOffset → M (JInt .i64))
    (copy : Word → Word → M Word)
    (x : JuliaLean.base.genericmemory.GenericMemoryRef Memory PtrOffset) (dict : Word) :
    M (JuliaLean.base.genericmemory.GenericMemoryRef Memory PtrOffset) := do
  match ← stackLookupTyped stackOps dict x with
  | some cached => pure cached
  | none =>
    let sourceMemory := JuliaLean.base.genericmemory.parent x
    let copiedMemory ← stackOps.cast (X := Memory) (← copy (stackOps.box sourceMemory) dict)
    let destinationRef ← ops.access.memoryref copiedMemory
    let offset ← memoryrefoffset x
    if offset == JInt.wrap .i64 1 then pure destinationRef
    else ops.access.memoryrefNew destinationRef offset true

/-- Generic dictionary operations used by `Dict` and `IdDict` specializations. -/
structure DictCopyOps (Dict TypeRep : Type) where
  eltype : Dict → TypeRep
  isBitstype : TypeRep → Bool
  copy : Dict → M Dict
  empty : Dict → M Dict
  forPairs : {State : Type} → Dict → (Word → Word → State → M State) → State → M State
  setindex : Dict → Word → Word → M Dict

def deepcopyDictUnion {Dict TypeRep : Type}
    (stackOps : StackOps) (ops : DictCopyOps Dict TypeRep)
    (copy : Word → Word → M Word) (x : Dict) (dict : Word) : M Dict := do
  match ← stackLookupTyped stackOps dict x with
  | some cached => pure cached
  | none =>
    if ops.isBitstype (ops.eltype x) then
      let destination ← ops.copy x
      stackInsertTyped stackOps dict x destination
      pure destination
    else
      let destination ← ops.empty x
      stackInsertTyped stackOps dict x destination
      ops.forPairs x (fun key value destination => do
        let key ← copy key dict
        let value ← copy value dict
        ops.setindex destination value key) destination

/--
Julia source: base/deepcopy.jl:150-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(x::Union{Dict,IdDict}, stackdict::IdDict)
    if haskey(stackdict, x)
        return stackdict[x]::typeof(x)
    end

    if isbitstype(eltype(x))
        return (stackdict[x] = copy(x))
    end

    dest = empty(x)
    stackdict[x] = dest
    for (k, v) in x
        dest[deepcopy_internal(k, stackdict)] = deepcopy_internal(v, stackdict)
    end
    dest
end
```
-/
def deepcopyLock {Lock : Type}
    (stackOps : StackOps) (construct : Lock → M Lock) (x : Lock) (dict : Word) : M Lock := do
  match ← stackLookupTyped stackOps dict x with
  | some cached => pure cached
  | none =>
    let destination ← construct x
    stackInsertTyped stackOps dict x destination
    pure destination

/--
Julia source: base/deepcopy.jl:167-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(x::AbstractLock, stackdict::IdDict)
    if haskey(stackdict, x)
        return stackdict[x]::typeof(x)
    end
    y = typeof(x)()
    stackdict[x] = y
    return y
end
```
-/
structure ConditionCopyOps (Condition Lock : Type) where
  lock : Condition → Lock
  construct : Condition → Lock → M Condition

/--
Julia source: base/deepcopy.jl:176-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(x::GenericCondition, stackdict::IdDict)
    if haskey(stackdict, x)
        return stackdict[x]::typeof(x)
    end
    y = typeof(x)(deepcopy_internal(x.lock, stackdict))
    stackdict[x] = y
    return y
end
```
-/
def deepcopyCondition {Condition Lock : Type}
    (stackOps : StackOps) (ops : ConditionCopyOps Condition Lock)
    (copy : Word → Word → M Word) (x : Condition) (dict : Word) : M Condition := do
  match ← stackLookupTyped stackOps dict x with
  | some cached => pure cached
  | none =>
    let copiedLock ← stackOps.cast (X := Lock) (← copy (stackOps.box (ops.lock x)) dict)
    let destination ← ops.construct x copiedLock
    stackInsertTyped stackOps dict x destination
    pure destination

/-- Atomic task reads, `_nslots`, and fresh `WaitEntryN` allocation. -/
structure WaitEntryCopyOps (Entry Task : Type) where
  atomicTask : Entry → JuliaLean.base.genericmemory.MemoryOrder → M Task
  nslots : Entry → M (JInt .i64)
  construct : Task → JInt .i64 → M Entry

/--
Julia source: base/deepcopy.jl:194-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deepcopy_internal(x::Core.WaitEntryN, stackdict::IdDict)
    if haskey(stackdict, x)
        return stackdict[x]::typeof(x)
    end
    y = WaitEntryN((@atomic :monotonic x.task), _nslots(x))
    stackdict[x] = y
    return y
end
```
-/
def deepcopyWaitEntryN {Entry Task : Type}
    (stackOps : StackOps) (ops : WaitEntryCopyOps Entry Task) (x : Entry) (dict : Word) : M Entry := do
  match ← stackLookupTyped stackOps dict x with
  | some cached => pure cached
  | none =>
    let task ← ops.atomicTask x .monotonic
    let nslots ← ops.nslots x
    let destination ← ops.construct task nslots
    stackInsertTyped stackOps dict x destination
    pure destination


end JuliaLean.base.deepcopy

namespace JuliaLean.DictsCov.DeepcopyRows


abbrev R (α : Type) := Except String α

structure Obj where
  id : Nat
  mutable_ : Bool
  bitstype : Bool
  weakref : Bool
  registered : Bool
  fields : List (Option Nat)
  deriving Repr, DecidableEq

abbrev Stack := List (Nat × Obj)

def lookup (stack : Stack) (id : Nat) : Option Obj :=
  (stack.find? fun p => p.1 == id).map Prod.snd

def replace (stack : Stack) (id : Nat) (value : Obj) : Stack :=
  (id, value) :: stack.filter (fun p => p.1 != id)

def copyMutableFields (deep : Nat → Stack → R (Nat × Stack)) :
    List (Option Nat) → Stack → R (List (Option Nat) × Stack)
  | [], stack => .ok ([], stack)
  | none :: fields, stack => do
      let (rest, stack) ← copyMutableFields deep fields stack
      return (none :: rest, stack)
  | some value :: fields, stack => do
      let (value, stack) ← deep value stack
      let (rest, stack) ← copyMutableFields deep fields stack
      return (some value :: rest, stack)

def copyImmutableFields (deep : Nat → Stack → R (Nat × Stack)) :
    List (Option Nat) → Stack → R (List (Option Nat) × Stack)
  | [], stack => .ok ([], stack)
  | none :: _, stack => .ok ([], stack)
  | some value :: fields, stack => do
      let (value, stack) ← deep value stack
      let (rest, stack) ← copyImmutableFields deep fields stack
      return (some value :: rest, stack)

/-- `deepcopy(x)`, `base/deepcopy.jl:32-35`. -/
def method32 (isBitsType : α → Bool) (deepcopyInternal : α → R α) (x : α) : R α :=
  if isBitsType x then .ok x else deepcopyInternal x

/-- Identity specializations, `base/deepcopy.jl:37-39`. -/
def method37 (x : α) (_stack : Stack) : α := x

def mapTuple (deep : α → Stack → R (α × Stack)) : List α → Stack → R (List α × Stack)
  | [], stack => .ok ([], stack)
  | x :: xs, stack => do
      let (x, stack) ← deep x stack
      let (xs, stack) ← mapTuple deep xs stack
      return (x :: xs, stack)

/-- Tuple specialization, `base/deepcopy.jl:40-41`. -/
def method40 (deep : α → Stack → R (α × Stack)) (x : List α) (stack : Stack) :
    R (List α × Stack) := mapTuple deep x stack

/-- Module specialization, `base/deepcopy.jl:42`. -/
def method42 (_module : α) (_stack : Stack) : R α := .error "deepcopy of Modules not supported"

def cachedSequence (copyOne : Nat → Stack → R (Nat × Stack))
    (allocate : List Nat → Obj) (x : Obj) (values : List Nat) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => do
      let (values, stack) ← mapTuple copyOne values stack
      let y := allocate values
      let stack := replace stack x.id y
      return (y, stack)

/-- SimpleVector specialization, `base/deepcopy.jl:44-51`. -/
def method44 (deep : Nat → Stack → R (Nat × Stack)) (svec : List Nat → Obj)
    (x : Obj) (values : List Nat) (stack : Stack) : R (Obj × Stack) :=
  cachedSequence deep svec x values stack

/-- String specialization, `base/deepcopy.jl:53-60`. -/
def method53 (unsafeCopy : Obj → Obj) (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none =>
      let y := unsafeCopy x
      .ok (y, replace stack x.id y)

/-- Generic object specialization, `base/deepcopy.jl:62-99`. -/
def method62 (deep : Nat → Stack → R (Nat × Stack)) (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  if x.mutable_ then
    match lookup stack x.id with
    | some y => .ok (y, stack)
    | none => do
        let y : Obj :=
          { id := x.id, mutable_ := x.mutable_, bitstype := x.bitstype,
            weakref := x.weakref, registered := false,
            fields := List.replicate x.fields.length none }
        let stack := replace stack x.id y
        let (fields, stack) ← copyMutableFields deep x.fields stack
        let y := { y with fields := fields }
        return (y, replace stack x.id y)
  else if x.fields.isEmpty || x.bitstype then
    .ok (x, stack)
  else do
    let (fields, stack) ← copyImmutableFields deep x.fields stack
    return ({ x with fields := fields }, stack)

def weakInput : Obj :=
  { id := 1, mutable_ := true, bitstype := false, weakref := true,
    registered := true, fields := [some 7] }

def weakDeep (value : Nat) (stack : Stack) : R (Nat × Stack) := .ok (value + 100, stack)

def deepcopyWeak : R Obj :=
  method32 (fun _ : Obj => false)
    (fun x => (method62 weakDeep x []).map Prod.fst) weakInput

/-- Memory dispatcher, `base/deepcopy.jl:101-106`. -/
def method101 (deepcopyMemoryT : Obj → Stack → R (Obj × Stack))
    (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => deepcopyMemoryT x stack

def copyMemoryElems (deep : Nat → Stack → R (Nat × Stack)) :
    List (Option Nat) → Stack → R (List (Option Nat) × Stack) := copyMutableFields deep

/-- `_deepcopy_memory_t`, `base/deepcopy.jl:108-128`. -/
def method108 (isBitsType : Bool) (copy : Obj → Obj)
    (deep : Nat → Stack → R (Nat × Stack)) (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  if isBitsType then
    let y := copy x
    .ok (y, replace stack x.id y)
  else do
    let dest : Obj := { x with fields := List.replicate x.fields.length none }
    let stack := replace stack x.id dest
    let (fields, stack) ← copyMemoryElems deep x.fields stack
    let dest := { dest with fields := fields }
    return (dest, replace stack x.id dest)

structure ArrayObj where
  object : Obj
  ref : Obj
  size : List Nat
  deriving Repr, DecidableEq

/-- Array specialization, `base/deepcopy.jl:129-137`. -/
def method129 (deepRef : Obj → Stack → R (Obj × Stack)) (x : ArrayObj) (stack : Stack) :
    R (ArrayObj × Stack) :=
  match lookup stack x.object.id with
  | some y => .ok ({ x with object := y }, stack)
  | none => do
      let emptyObj := { x.object with fields := [] }
      let y := { x with object := emptyObj }
      let stack := replace stack x.object.id emptyObj
      let (ref, stack) ← deepRef x.ref stack
      return ({ y with ref := ref, size := x.size }, stack)

structure MemRef where
  mem : Obj
  offset : Nat
  deriving Repr, DecidableEq

/-- GenericMemoryRef specialization, `base/deepcopy.jl:138-147`. -/
def method138 (deepMem : Obj → Stack → R (Obj × Stack)) (x : MemRef) (stack : Stack) :
    R (MemRef × Stack) := do
  let (mem, stack) ← deepMem x.mem stack
  let dest := { mem := mem, offset := 1 }
  return (if x.offset == 1 then dest else { dest with offset := x.offset }, stack)

def copyPairs (deep : Nat → Stack → R (Nat × Stack)) :
    List (Nat × Nat) → Stack → R (List (Nat × Nat) × Stack)
  | [], stack => .ok ([], stack)
  | (k, v) :: pairs, stack => do
      let (k, stack) ← deep k stack
      let (v, stack) ← deep v stack
      let (pairs, stack) ← copyPairs deep pairs stack
      return ((k, v) :: pairs, stack)

/-- Dict and IdDict specialization, `base/deepcopy.jl:150-165`. -/
def method150 (bitsEltype : Bool) (copy : Obj → Obj)
    (empty : Obj → Obj) (deep : Nat → Stack → R (Nat × Stack))
    (x : Obj) (pairs : List (Nat × Nat)) (stack : Stack) : R (Obj × List (Nat × Nat) × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, pairs, stack)
  | none =>
      if bitsEltype then
        let y := copy x
        .ok (y, pairs, replace stack x.id y)
      else do
        let dest := empty x
        let stack := replace stack x.id dest
        let (pairs, stack) ← copyPairs deep pairs stack
        return (dest, pairs, stack)

/-- AbstractLock specialization, `base/deepcopy.jl:167-174`. -/
def method167 (construct : Obj → Obj) (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => let y := construct x; .ok (y, replace stack x.id y)

/-- GenericCondition specialization, `base/deepcopy.jl:176-183`. -/
def method176 (deepLock : Obj → Stack → R (Obj × Stack))
    (construct : Obj → Obj) (x lock : Obj) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => do
      let (lock, stack) ← deepLock lock stack
      let y := construct lock
      return (y, replace stack x.id y)

/-- WaitEntryN specialization, `base/deepcopy.jl:194-201`. -/
def method194 (allocate : Nat → Nat → Obj) (x : Obj) (task slots : Nat) (stack : Stack) :
    R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => let y := allocate task slots; .ok (y, replace stack x.id y)

end JuliaLean.DictsCov.DeepcopyRows

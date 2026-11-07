import JuliaLean.Core
import JuliaLean.base.int

/-!
# Typed model of `base/summarysize.jl`

Julia's `Any`, type-introspection, identity dictionary, pointer, and Core layout operations are typed interfaces. The synchronized `frontier_x` and `frontier_i` vectors are represented as a newest-first list of pairs, preserving their end/pop traversal order.
-/

namespace JuliaLean.base.summarysize

open JuliaLean

abbrev I := JInt .i64

def int (n : Int) : I := JInt.wrap .i64 n

def intAdd (a b : I) : I := JuliaLean.base.int.add a b

def intSub (a b : I) : I := JuliaLean.base.int.sub a b

def intMul (a b : I) : I := JuliaLean.base.int.mul a b

inductive SummarySizeMethod where
  | general
  | symbol
  | state
  | string
  | dataType
  | typeName
  | genericMemory
  | simpleVector
  | module
  | cancellationTokenSource
  | waitEntryN
  | task
  | bigInt
  deriving DecidableEq

structure TypeTags (T : Type) where
  symbol : T
  summarySize : T
  string : T
  dataType : T
  typeName : T
  genericMemory : T
  simpleVector : T
  module : T
  union : T
  unionAll : T
  cancellationTokenSource : T
  waitEntryN : T
  task : T
  bigInt : T

structure FieldNames (Name : Type) where
  parameters : Name
  types : Name
  code : Name
  storage : Name
  doneNotify : Name
  result : Name

structure IdentityOps (Obj Key Seen Ptr Error : Type) where
  newSeen : Except Error Seen
  objectKey : Obj → Key
  pointerKey : Ptr → Key
  hasKey : Seen → Key → Except Error Bool
  insertKey : Seen → Key → Except Error Seen
  pointerFromObjRef : Obj → Except Error Ptr
  valuePointer : Obj → Except Error Ptr
  memoryPointer : Obj → Except Error Ptr
  addPointer : Ptr → I → Ptr
  samePointer : Ptr → Ptr → Bool

structure SummarySizeOps (Obj T Key Seen Ptr Name Error : Type) where
  types : TypeTags T
  fields : FieldNames Name
  identity : IdentityOps Obj Key Seen Ptr Error
  dispatch : Obj → SummarySizeMethod
  typeof : Obj → T
  isa : Obj → T → Bool
  isaType : T → T → Bool
  isSingletonType : T → Bool
  pointerCount : T → I
  allocatedInline : T → Bool
  dataTypePointerFree : T → Bool
  isNothing : Obj → Bool
  sizeOfInt : I
  sizeOfDataType : I
  sizeOfLimb : I
  coreSizeof : Obj → Except Error I
  gcAlignment : I → I
  nthPointerIsDefinedRaw : Obj → I → JInt .i32
  getNthPointerRaw : Obj → I → Obj
  isEmpty : Obj → Except Error Bool
  length : Obj → Except Error I
  isAssigned : Obj → I → Except Error Bool
  getIndex : Obj → I → Except Error Obj
  memoryEltype : Obj → T
  isDefinedField : Obj → Name → Bool
  getField : Obj → Name → Except Error Obj
  moduleNames : Obj → List Name
  isDeprecated : Obj → Name → Bool
  parentModule : Obj → Obj
  sameObject : Obj → Obj → Bool
  unwrapUnionAll : Obj → Obj
  nameofType : Obj → Name
  sameName : Name → Name → Bool
  dataTypeName : Obj → Obj
  cancelParentCount : Obj → I
  cancelParent : Obj → I → Except Error Obj
  waitEntrySlots : Obj → I
  waitEntryTask : Obj → Except Error Obj
  waitEntrySlot : Obj → I → Except Error (Obj × Obj)
  bigIntAlloc : Obj → JInt .i32
  divremInt : I → I → Except Error (I × I)
  defaultExclude : T
  defaultChargeAll : T

/--
Julia source: base/summarysize.jl:3-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct SummarySize
    seen::IdDict{Any,Any}
    frontier_x::Vector{Any}
    frontier_i::Vector{Int}
    exclude::Any
    chargeall::Any
    count::Bool
end
```
-/
structure SummarySize (Obj T Seen : Type) where
  seen : Seen
  frontier : List (Obj × I)
  exclude : T
  chargeAll : T
  count : Bool


def pushFrontier {Obj T Seen : Type} (state : SummarySize Obj T Seen)
    (obj : Obj) (index : I) : SummarySize Obj T Seen :=
  {state with frontier := (obj, index) :: state.frontier}

def markSeen {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (key : Key) : Except Error (SummarySize Obj T Seen) := do
  let seen ← ops.identity.insertKey state.seen key
  pure {state with seen := seen}

def seenBefore {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (key : Key) : Except Error Bool :=
  ops.identity.hasKey state.seen key

/--
Julia source: base/summarysize.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nth_pointer_isdefined(obj, i::Int) = ccall(:jl_nth_pointer_isdefined, Cint, (Any, Csize_t), obj, i-1) != 0
```
-/
def nthPointerIsDefined {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error) (obj : Obj) (i : I) : Bool :=
  ops.nthPointerIsDefinedRaw obj (intSub i (int 1)) != JInt.wrap .i32 0

/--
Julia source: base/summarysize.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_nth_pointer(obj, i::Int) = ccall(:jl_get_nth_pointer, Any, (Any, Csize_t), obj, i-1)
```
-/
def getNthPointer {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error) (obj : Obj) (i : I) : Obj :=
  ops.getNthPointerRaw obj (intSub i (int 1))


/--
Julia source: base/summarysize.jl:122-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _summarysize(ss::SummarySize, @nospecialize(obj), count::Bool)
    issingletontype(typeof(obj)) && return 0
    # NOTE: this attempts to discover multiple copies of the same immutable value,
    # and so is somewhat approximate.
    key = ccall(:jl_value_ptr, Ptr{Cvoid}, (Any,), obj)
    haskey(ss.seen, key) ? (return 0) : (ss.seen[key] = true)
    if datatype_npointers(typeof(obj)) > 0
        push!(ss.frontier_x, obj)
        push!(ss.frontier_i, 1)
    end
    if isa(obj, UnionAll) || isa(obj, Union)
        # black-list of items that don't have a Core.sizeof
        sz = 2 * sizeof(Int)
    else
        sz = Core.sizeof(obj)
    end
    if sz == 0
        # 0-field mutable structs are not unique
        return gc_alignment(0)
    end
    return count ? 1 : sz
end
```
-/
def summarySizeGeneral {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (obj : Obj) (count : Bool) :
    Except Error (I × SummarySize Obj T Seen) := do
  let objType := ops.typeof obj
  if ops.isSingletonType objType then return (int 0, state)
  let pointer ← ops.identity.valuePointer obj
  let key := ops.identity.pointerKey pointer
  if ← seenBefore ops state key then return (int 0, state)
  let state ← markSeen ops state key
  let state := if ops.pointerCount objType > int 0 then
      pushFrontier state obj (int 1)
    else state
  let size ← if ops.isa obj ops.types.unionAll || ops.isa obj ops.types.union then
      pure (intMul (int 2) ops.sizeOfInt)
    else ops.coreSizeof obj
  if size == int 0 then return (ops.gcAlignment (int 0), state)
  return (if count then int 1 else size, state)
/--
Julia source: base/summarysize.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(ss::SummarySize)(@nospecialize obj) = _summarysize(ss, obj, ss.count)
```
-/
def summarySizeApply {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) :=
  summarySizeGeneral ops state obj state.count

/--
Julia source: base/summarysize.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::SummarySize)(obj::Symbol) = 0
```
-/
def summarySizeSymbol {Obj T Seen Error : Type}
    (state : SummarySize Obj T Seen) (_obj : Obj) : Except Error (I × SummarySize Obj T Seen) :=
  .ok (int 0, state)

/--
Julia source: base/summarysize.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::SummarySize)(obj::SummarySize) = 0
```
-/
def summarySizeState {Obj T Seen Error : Type}
    (state : SummarySize Obj T Seen) (_obj : Obj) : Except Error (I × SummarySize Obj T Seen) :=
  .ok (int 0, state)

/--
Julia source: base/summarysize.jl:148-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (ss::SummarySize)(obj::String)
    key = ccall(:jl_value_ptr, Ptr{Cvoid}, (Any,), obj)
    haskey(ss.seen, key) ? (return 0) : (ss.seen[key] = true)
    return (ss.count ? 1 : (Core.sizeof(Int) + Core.sizeof(obj)))
end
```
-/
def summarySizeString {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let pointer ← ops.identity.valuePointer obj
  let key := ops.identity.pointerKey pointer
  if ← seenBefore ops state key then return (int 0, state)
  let state ← markSeen ops state key
  let size ← if state.count then pure (int 1) else do
      let objectSize ← ops.coreSizeof obj
      pure (intAdd ops.sizeOfInt objectSize)
  return (size, state)

/--
Julia source: base/summarysize.jl:154-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (ss::SummarySize)(obj::DataType)
    key = pointer_from_objref(obj)
    haskey(ss.seen, key) ? (return 0) : (ss.seen[key] = true)
    size::Int = ss.count ? 1 : sizeof(DataType)
    size += ss(obj.parameters)::Int
    if isdefined(obj, :types)
        size += ss(obj.types)::Int
    end
    return size
end
```
-/
def summarySizeDataType {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (recur : Obj → SummarySize Obj T Seen → Except Error (I × SummarySize Obj T Seen))
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let pointer ← ops.identity.pointerFromObjRef obj
  let key := ops.identity.pointerKey pointer
  if ← seenBefore ops state key then return (int 0, state)
  let state ← markSeen ops state key
  let mut size := if state.count then int 1 else ops.sizeOfDataType
  let parameters ← ops.getField obj ops.fields.parameters
  let (part, nextState) ← recur parameters state
  size := intAdd size part
  let state := nextState
  if ops.isDefinedField obj ops.fields.types then
    let fields ← ops.getField obj ops.fields.types
    let (part, nextState) ← recur fields state
    size := intAdd size part
    return (size, nextState)
  return (size, state)

/--
Julia source: base/summarysize.jl:165-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (ss::SummarySize)(obj::Core.TypeName)
    key = pointer_from_objref(obj)
    haskey(ss.seen, key) ? (return 0) : (ss.seen[key] = true)
    return (ss.count ? 1 : Core.sizeof(obj))
end
```
-/
def summarySizeTypeName {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let pointer ← ops.identity.pointerFromObjRef obj
  let key := ops.identity.pointerKey pointer
  if ← seenBefore ops state key then return (int 0, state)
  let state ← markSeen ops state key
  let size ← if state.count then pure (int 1) else ops.coreSizeof obj
  return (size, state)

/--
Julia source: base/summarysize.jl:171-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (ss::SummarySize)(obj::GenericMemory)
    haskey(ss.seen, obj) ? (return 0) : (ss.seen[obj] = true)
    headersize = 2 * sizeof(Int)
    size::Int = (ss.count ? 1 : headersize)
    datakey = unsafe_convert(Ptr{Cvoid}, obj)
    if !haskey(ss.seen, datakey)
        ss.seen[datakey] = true
        if !ss.count
            size += sizeof(obj)
        elseif pointer_from_objref(obj) + 16 != datakey
            size += 1
        end
        T = eltype(obj)
        if !isempty(obj) && T !== Symbol && (!allocatedinline(T) || (T isa DataType && !datatype_pointerfree(T)))
            push!(ss.frontier_x, obj)
            push!(ss.frontier_i, 1)
        end
    end
    return size
end
```
-/
def summarySizeGenericMemory {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let objectKey := ops.identity.objectKey obj
  if ← seenBefore ops state objectKey then return (int 0, state)
  let state ← markSeen ops state objectKey
  let headerSize := intMul (int 2) ops.sizeOfInt
  let initialSize := if state.count then int 1 else headerSize
  let dataPointer ← ops.identity.memoryPointer obj
  let dataKey := ops.identity.pointerKey dataPointer
  if ← seenBefore ops state dataKey then return (initialSize, state)
  let state ← markSeen ops state dataKey
  let size ← if state.count then do
      let objectPointer ← ops.identity.pointerFromObjRef obj
      let endOfHeader := ops.identity.addPointer objectPointer (int 16)
      pure (if ops.identity.samePointer endOfHeader dataPointer then initialSize
            else intAdd initialSize (int 1))
    else do
      let objectSize ← ops.coreSizeof obj
      pure (intAdd initialSize objectSize)
  let elementType := ops.memoryEltype obj
  let empty ← ops.isEmpty obj
  if !empty && !ops.isaType elementType ops.types.symbol &&
      (!ops.allocatedInline elementType ||
       (ops.isaType elementType ops.types.dataType && !ops.dataTypePointerFree elementType)) then
    return (size, pushFrontier state obj (int 1))
  return (size, state)

/--
Julia source: base/summarysize.jl:192-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (ss::SummarySize)(obj::Core.SimpleVector)
    key = pointer_from_objref(obj)
    haskey(ss.seen, key) ? (return 0) : (ss.seen[key] = true)
    size::Int = (ss.count ? 1 : Core.sizeof(obj))
    if !isempty(obj)
        push!(ss.frontier_x, obj)
        push!(ss.frontier_i, 1)
    end
    return size
end
```
-/
def summarySizeSimpleVector {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let pointer ← ops.identity.pointerFromObjRef obj
  let key := ops.identity.pointerKey pointer
  if ← seenBefore ops state key then return (int 0, state)
  let state ← markSeen ops state key
  let size ← if state.count then pure (int 1) else ops.coreSizeof obj
  let empty ← ops.isEmpty obj
  if empty then return (size, state)
  return (size, pushFrontier state obj (int 1))

/--
Julia source: base/summarysize.jl:203-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (ss::SummarySize)(obj::Module)
    haskey(ss.seen, obj) ? (return 0) : (ss.seen[obj] = true)
    size::Int = (ss.count ? 1 : Core.sizeof(obj))
    for binding in names(obj, all = true)
        if isdefined(obj, binding) && !isdeprecated(obj, binding)
            value = getfield(obj, binding)
            if !isa(value, Module) || parentmodule(value) === obj
                size += ss(value)::Int
                if isa(value, UnionAll)
                    value = unwrap_unionall(value)
                end
                if isa(value, DataType) && parentmodule(value) === obj && nameof(value) === binding
                    # charge a TypeName to its module (but not to the type)
                    size += ss(value.name)::Int
                end
            end
        end
    end
    return size
end
```
-/
def summarySizeModule {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (recur : Obj → SummarySize Obj T Seen → Except Error (I × SummarySize Obj T Seen))
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let key := ops.identity.objectKey obj
  if ← seenBefore ops state key then return (int 0, state)
  let state ← markSeen ops state key
  let initialSize ← if state.count then pure (int 1) else ops.coreSizeof obj
  let mut size := initialSize
  let mut current := state
  for binding in ops.moduleNames obj do
    if ops.isDefinedField obj binding && !ops.isDeprecated obj binding then
      let value ← ops.getField obj binding
      if !ops.isa value ops.types.module ||
          ops.sameObject (ops.parentModule value) obj then
        let (part, next) ← recur value current
        size := intAdd size part
        current := next
        let value := if ops.isa value ops.types.unionAll then
            ops.unwrapUnionAll value
          else value
        if ops.isa value ops.types.dataType &&
            ops.sameObject (ops.parentModule value) obj &&
            ops.sameName (ops.nameofType value) binding then
          let nameObject := ops.dataTypeName value
          let (nameSize, next) ← recur nameObject current
          size := intAdd size nameSize
          current := next
  return (size, current)

/--
Julia source: base/summarysize.jl:224-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (ss::SummarySize)(obj::Core.CancellationTokenSource)
    key = pointer_from_objref(obj)
    haskey(ss.seen, key) ? (return 0) : (ss.seen[key] = true)
    # Variable-sized: Core.sizeof includes the trailing parent link entries.
    # The (strong) parent references are traversed through the iterative
    # frontier (see the branch in `summarysize`), which keeps deep chains
    # off the stack and honors `exclude`; the child list is weak - a source
    # does not keep its children alive - so it is deliberately not followed.
    if Int(obj.nparents) > 0
        push!(ss.frontier_x, obj)
        push!(ss.frontier_i, 1)
    end
    return ss.count ? 1 : Core.sizeof(obj)
end
```
-/
def summarySizeCancellationTokenSource {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let pointer ← ops.identity.pointerFromObjRef obj
  let key := ops.identity.pointerKey pointer
  if ← seenBefore ops state key then return (int 0, state)
  let state ← markSeen ops state key
  let parentCount := ops.cancelParentCount obj
  let state := if parentCount > int 0 then pushFrontier state obj (int 1) else state
  let size ← if state.count then pure (int 1) else ops.coreSizeof obj
  return (size, state)

/--
Julia source: base/summarysize.jl:239-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (ss::SummarySize)(obj::Core.WaitEntryN)
    key = pointer_from_objref(obj)
    haskey(ss.seen, key) ? (return 0) : (ss.seen[key] = true)
    # Variable-sized: Core.sizeof includes the trailing wait slots, whose
    # strong owner/next references (invisible to the layout) are traversed
    # through the iterative frontier alongside `task`.
    push!(ss.frontier_x, obj)
    push!(ss.frontier_i, 1)
    return ss.count ? 1 : Core.sizeof(obj)
end
```
-/
def summarySizeWaitEntryN {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let pointer ← ops.identity.pointerFromObjRef obj
  let key := ops.identity.pointerKey pointer
  if ← seenBefore ops state key then return (int 0, state)
  let state ← markSeen ops state key
  let state := pushFrontier state obj (int 1)
  let size ← if state.count then pure (int 1) else ops.coreSizeof obj
  return (size, state)

/--
Julia source: base/summarysize.jl:250-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (ss::SummarySize)(obj::Task)
    haskey(ss.seen, obj) ? (return 0) : (ss.seen[obj] = true)
    size::Int = (ss.count ? 1 : Core.sizeof(obj))
    if isdefined(obj, :code)
        size += ss(obj.code)::Int
    end
    size += ss(obj.storage)::Int
    size += ss(obj.donenotify)::Int
    size += ss(obj.result)::Int
    # TODO: add stack size, and possibly traverse stack roots
    return size
end
```
-/
def summarySizeTask {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (recur : Obj → SummarySize Obj T Seen → Except Error (I × SummarySize Obj T Seen))
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let key := ops.identity.objectKey obj
  if ← seenBefore ops state key then return (int 0, state)
  let state ← markSeen ops state key
  let initialSize ← if state.count then pure (int 1) else ops.coreSizeof obj
  let mut size := initialSize
  let mut current := state
  if ops.isDefinedField obj ops.fields.code then
    let code ← ops.getField obj ops.fields.code
    let (part, next) ← recur code current
    size := intAdd size part
    current := next
  for field in [ops.fields.storage, ops.fields.doneNotify, ops.fields.result] do
    let value ← ops.getField obj field
    let (part, next) ← recur value current
    size := intAdd size part
    current := next
  return (size, current)

/--
Julia source: base/summarysize.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(ss::SummarySize)(obj::BigInt) = _summarysize(ss, obj, ss.count) + (ss.count ? 1 : obj.alloc * sizeof(GMP.Limb))
```
-/
def summarySizeBigInt {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (obj : Obj) : Except Error (I × SummarySize Obj T Seen) := do
  let (size, state) ← summarySizeGeneral ops state obj state.count
  let extra := if state.count then int 1 else
      intMul (JInt.wrap .i64 (ops.bigIntAlloc obj).val) ops.sizeOfLimb
  return (intAdd size extra, state)

def frontierCandidate {Obj T Key Seen Ptr Name Error : Type}
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (obj : Obj) (i : I) : Except Error (I × Option Obj) := do
  if ops.isa obj ops.types.simpleVector then
    let nf ← ops.length obj
    let value ← if ← ops.isAssigned obj i then
        pure (some (← ops.getIndex obj i))
      else pure none
    return (nf, value)
  else if ops.isa obj ops.types.cancellationTokenSource then
    let nf := ops.cancelParentCount obj
    let value ← ops.cancelParent obj i
    return (nf, some value)
  else if ops.isa obj ops.types.waitEntryN then
    let slots := ops.waitEntrySlots obj
    let nf := intAdd (int 1) (intMul (int 2) slots)
    if i == int 1 then
      let task ← ops.waitEntryTask obj
      return (nf, if ops.isNothing task then none else some task)
    else
      let (slotIndex, fieldIndex) ← ops.divremInt (intSub i (int 2)) (int 2)
      let (owner, next) ← ops.waitEntrySlot obj (intAdd slotIndex (int 1))
      let value := if fieldIndex == int 0 then owner else next
      return (nf, if ops.isNothing value then none else some value)
  else if ops.isa obj ops.types.genericMemory then
    let elementType := ops.memoryEltype obj
    if ops.allocatedInline elementType then
      let np := ops.pointerCount elementType
      let nf := intMul (← ops.length obj) np
      let firstIndex := intSub i (int 1)
      let (elementIndex, _) ← ops.divremInt firstIndex np
      let elementIndex := intAdd elementIndex (int 1)
      if ← ops.isAssigned obj elementIndex then
        let element ← ops.getIndex obj elementIndex
        let (_, pointerIndex) ← ops.divremInt firstIndex np
        let pointerIndex := intAdd pointerIndex (int 1)
        if nthPointerIsDefined ops element pointerIndex then
          return (nf, some (getNthPointer ops element pointerIndex))
      return (nf, none)
    else
      let nf ← ops.length obj
      let value ← if ← ops.isAssigned obj i then
          pure (some (← ops.getIndex obj i))
        else pure none
      return (nf, value)
  else
    let nf := ops.pointerCount (ops.typeof obj)
    let value := if nthPointerIsDefined ops obj i then
        some (getNthPointer ops obj i)
      else none
    return (nf, value)

partial def summarySizeCall {Obj T Key Seen Ptr Name Error : Type} [Inhabited Error]
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (obj : Obj) (state : SummarySize Obj T Seen) : Except Error (I × SummarySize Obj T Seen) :=
  match ops.dispatch obj with
  | .general => summarySizeApply ops state obj
  | .symbol => summarySizeSymbol state obj
  | .state => summarySizeState state obj
  | .string => summarySizeString ops state obj
  | .dataType => summarySizeDataType ops (summarySizeCall ops) state obj
  | .typeName => summarySizeTypeName ops state obj
  | .genericMemory => summarySizeGenericMemory ops state obj
  | .simpleVector => summarySizeSimpleVector ops state obj
  | .module => summarySizeModule ops (summarySizeCall ops) state obj
  | .cancellationTokenSource => summarySizeCancellationTokenSource ops state obj
  | .waitEntryN => summarySizeWaitEntryN ops state obj
  | .task => summarySizeTask ops (summarySizeCall ops) state obj
  | .bigInt => summarySizeBigInt ops state obj

partial def summarySizeFrontier {Obj T Key Seen Ptr Name Error : Type} [Inhabited Error]
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error)
    (state : SummarySize Obj T Seen) (total : I) : Except Error I := do
  match state.frontier with
  | [] => return total
  | (obj, i) :: rest =>
      let (nf, value) ← frontierCandidate ops obj i
      let state := if nf > i then
          {state with frontier := (obj, intAdd i (int 1)) :: rest}
        else {state with frontier := rest}
      let (size, state) ← match value with
        | none => pure (int 0, state)
        | some value =>
            if ops.isNothing value || ops.isa value ops.types.module then
              pure (int 0, state)
            else if ops.isa value state.exclude && !ops.isa obj state.chargeAll then
              pure (int 0, state)
            else summarySizeCall ops value state
      summarySizeFrontier ops state (intAdd total size)

/--
Julia source: base/summarysize.jl:45-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function summarysize(obj;
                     count::Bool = false,
                     exclude = Union{DataType, Core.TypeName, Core.MethodInstance},
                     chargeall = Union{Core.TypeMapEntry, Method})
    @nospecialize obj exclude chargeall
    ss = SummarySize(IdDict(), Any[], Int[], exclude, chargeall, count)
    size::Int = ss(obj)
    while !isempty(ss.frontier_x)
        # DFS heap traversal of everything without a specialization
        # BFS heap traversal of anything with a specialization
        x = ss.frontier_x[end]
        i = ss.frontier_i[end]
        val = nothing
        if isa(x, Core.SimpleVector)
            nf = length(x)
            if isassigned(x, i)
                val = x[i]
            end
        elseif isa(x, Core.CancellationTokenSource)
            # the strong references of a source are its (hidden, trailing)
            # parent links, enumerated here rather than via the layout
            nf = Int(x.nparents)
            val = _cancel_parent(x, i)
        elseif isa(x, Core.WaitEntryN)
            # `task` plus the (strong) owner/next pair of each hidden
            # trailing wait slot
            ns = _nslots(x)
            nf = 1 + 2 * ns
            if i == 1
                t = @atomic :monotonic x.task
                t === nothing || (val = t)
            else
                si, k = divrem(i - 2, 2)
                slot = slots(x)[si + 1]
                v = k == 0 ? slot.owner : slot.next
                v === nothing || (val = v)
            end
        elseif isa(x, GenericMemory)
            T = eltype(x)
            if allocatedinline(T)
                np = datatype_npointers(T)
                nf = length(x) * np
                idx = (i-1) ÷ np + 1
                if @inbounds @inline isassigned(x, idx)
                    elt = x[idx]
                    p = (i-1) % np + 1
                    if nth_pointer_isdefined(elt, p)
                        val = get_nth_pointer(elt, p)
                    end
                end
            else
                nf = length(x)
                if @inbounds @inline isassigned(x, i)
                    val = x[i]
                end
            end
        else
            nf = datatype_npointers(typeof(x))
            if nth_pointer_isdefined(x, i)
                val = get_nth_pointer(x, i)
            end
        end
        if nf > i
            ss.frontier_i[end] = i + 1
        else
            pop!(ss.frontier_x)
            pop!(ss.frontier_i)
        end
        if val !== nothing && !isa(val, Module) && (!isa(val, ss.exclude) || isa(x, ss.chargeall))
            size += ss(val)::Int
        end
    end
    return size
end
```
-/
def summarysize {Obj T Key Seen Ptr Name Error : Type} [Inhabited Error]
    (ops : SummarySizeOps Obj T Key Seen Ptr Name Error) (obj : Obj)
    (count : Bool := false) (exclude : T := ops.defaultExclude)
    (chargeAll : T := ops.defaultChargeAll) : Except Error I := do
  let seen ← ops.identity.newSeen
  let state : SummarySize Obj T Seen :=
    ⟨seen, [], exclude, chargeAll, count⟩
  let (size, state) ← summarySizeCall ops obj state
  summarySizeFrontier ops state size

end JuliaLean.base.summarysize

namespace JuliaLean.NumMisc.Coverage

open JuliaLean

/-! ## `base/summarysize.jl` -/

inductive SummaryKind where
  | tuple | cancellation | waitEntry | memoryInline | memoryBoxed | generic | string
  | datatype | typename | simpleVector | module | task | bigint
  deriving DecidableEq, Repr

structure SummaryObject where
  identity : Nat
  bytes : Nat
  pointers : List Nat
  kind : SummaryKind
  deriving DecidableEq, Repr

structure SummaryState where
  seen : List Nat
  frontier : List SummaryObject
  size : Nat
  deriving DecidableEq, Repr

def chargeObject (count : Bool) (object : SummaryObject) : Nat := if count then 1 else object.bytes
def nthPointerDefined (object : SummaryObject) (index : Nat) : Bool := index ≥ 1 && index ≤ object.pointers.length
def getNthPointer (object : SummaryObject) (index : Nat) : Nat := object.pointers.getD (index - 1) 0

def summaryChildren (object : SummaryObject) : List Nat :=
  match object.kind with
  | .string | .bigint => []
  | .memoryInline | .memoryBoxed | .tuple | .cancellation | .waitEntry | .generic
  | .datatype | .typename | .simpleVector | .module | .task => object.pointers

def summaryVisit (count excluded chargeAll : Bool) (object : SummaryObject)
    (state : SummaryState) : SummaryState :=
  if state.seen.contains object.identity then state
  else if excluded && !chargeAll then { state with seen := object.identity :: state.seen }
  else { seen := object.identity :: state.seen,
         frontier := (summaryChildren object).map (fun identity => { object with identity }) ++ state.frontier,
         size := state.size + chargeObject count object }

def summaryLoop (count : Bool) : List SummaryObject → SummaryState → SummaryState
  | [], state => state
  | object :: rest, state => summaryLoop count rest (summaryVisit count false false object state)

end JuliaLean.NumMisc.Coverage

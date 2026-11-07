import JuliaLean.src.iddict_c
import JuliaLean.base.dict

/-! Native Julia values, IdDict fields, and C table cells use one byte heap.
Dictionary aliases have the same address. Selected Julia/Core callees
are explicit Callees fields, without laws. -/
namespace JuliaLean.base.iddict
open JuliaLean
open JuliaLean.src.identity_runtime (Word Memory Error GC M fail)

inductive IteratorSize where
  | hasLength
  | hasShape
  | unknown
  deriving Repr, DecidableEq
namespace C
export JuliaLean.src.iddict_c (jl_idtable_rehash jl_eqtable_put jl_eqtable_get jl_eqtable_pop jl_eqtable_nextind)
export JuliaLean.src.identity_runtime (allocMemoryAny memoryOwner getWorld modifyWorld
  loadWord encodeWord datatypeAt typeof gcWriteAtomic)
export JuliaLean.src.builtins_identity_c (jl_egal_)
end C

structure DictFields where
  ht : Memory
  count : JInt .i64
  ndel : JInt .i64
  keyType : Word
  valueType : Word

/-- Field views for IdDict{K,V}: Memory{Any}, Int64, Int64 on the target ABI.
The two type parameters come from the actual datatype's SimpleVector. -/
def dictionary (address : Word) : M DictFields := do
  let memoryAddress ← C.loadWord address
  let memory ← match (← C.getWorld).memories memoryAddress with
    | none => fail (.undefinedBehavior "IdDict.ht GenericMemory object" memoryAddress)
    | some memory => pure memory
  let datatype ← C.datatypeAt (← C.typeof address)
  let keyType ← C.loadWord (datatype.parameters+8)
  let valueType ← C.loadWord (datatype.parameters+16)
  let count ← C.loadWord (address+8)
  let ndel ← C.loadWord (address+16)
  return ⟨memory, JInt.wrap .i64 (Int.ofNat count.toNat),
    JInt.wrap .i64 (Int.ofNat ndel.toNat), keyType, valueType⟩

def storeHT (address : Word) (memory : Memory) : M Unit := do
  C.gcWriteAtomic address address (C.memoryOwner memory) .notAtomic
  let owner := C.memoryOwner memory
  C.modifyWorld fun world => { world with
    memories := fun query =>
      if query == owner then some memory else world.memories query }

def storeIntField (address : Word) (offset : Nat) (value : JInt .i64) : M Unit := do
  let location := address + UInt64.ofNat offset
  JuliaLean.src.identity_runtime.requireReadable location 8
  let bytes := C.encodeWord (UInt64.ofNat (JuliaLean.base.int.remT .u64 value).val.toNat)
  C.modifyWorld fun world => { world with
    raw := { world.raw with heap := world.raw.heap.writeBytes location.toNat bytes } }

/-- These are Julia/Core callees, not C identity-table replacements. User
methods may mutate this same heap or throw. The proposal lists each gap. -/
structure Callees where
  gc : GC
  newObject : Word → Word → Memory → JInt .i64 → JInt .i64 → M Word
  copyMemory : Memory → M Memory
  isa : Word → Word → M Bool
  convert : Word → Word → M Word
  toCsize : Word → M Word
  doubleInteger : Word → M Word
  tableSize : Word → M Word
  lessThanInt : Word → JInt .i64 → M Bool
  lengthArgument : Nat → M Word
  newPair : Word → Word → Word → Word → M Word
  filterInOnePass : (Word → M Word) → Word → M Word

/--
Julia source: base/abstractdict.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const secret_table_token = :__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__
```
-/
def secretToken : M Word := do
  match (← C.getWorld).internedSymbols "__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__" with
  | some value => pure value
  | none => fail (.undefinedBehavior "Base.secret_table_token interned Symbol" 0)

/-- The Any branch is the builtin's universal type, not a caller's success law. -/
def isa (calls : Callees) (value type : Word) : M Bool := do
  if type == (← C.getWorld).globals.anyType then pure true
  else calls.isa value type

def assertType (calls : Callees) (value type : Word) : M Word := do
  if ← isa calls value type then pure value
  else fail (.typeAssertion type value)

def construct (calls : Callees) (keyType valueType : Word) (memory : Memory)
    (count ndel : JInt .i64) : M Word := do
  let address ← calls.newObject keyType valueType memory count ndel
  let owner := C.memoryOwner memory
  C.modifyWorld fun world => { world with
    memories := fun query =>
      if query == owner then some memory else world.memories query }
  pure address

/--
Julia source: base/iddict.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IdDict{K,V}() where {K, V} = new{K,V}(Memory{Any}(undef, 32), 0, 0)
```
-/
def emptyTyped (calls : Callees) (keyType valueType : Word) : M Word := do
  let memory ← (C.allocMemoryAny calls.gc 32)
  construct calls keyType valueType memory (JInt.wrap .i64 0) (JInt.wrap .i64 0)

/--
Julia source: base/iddict.jl:49-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IdDict{K,V}(d::IdDict{K,V}) where {K, V} = new{K,V}(copy(d.ht), d.count, d.ndel)
end
```
-/
def copyConstruct (calls : Callees) (address : Word) : M Word := do
  let fields ← dictionary address
  let memory ← (calls.copyMemory fields.ht)
  let fields ← dictionary address
  construct calls fields.keyType fields.valueType memory fields.count fields.ndel

/--
Julia source: base/iddict.jl:52-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict() = IdDict{Any,Any}()
```
-/
def emptyAny (calls : Callees) : M Word := do
  let anyType := (← C.getWorld).globals.anyType
  emptyTyped calls anyType anyType

/--
Julia source: base/iddict.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(kv::Tuple{}) = IdDict()
```
-/
def emptyTuple (calls : Callees) (_pairs : Unit) : M Word := emptyAny calls

/--
Julia source: base/iddict.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(d::IdDict, ::Type{K}, ::Type{V}) where {K, V} = IdDict{K,V}()
```
-/
def emptyOf (calls : Callees) (_dict keyType valueType : Word) : M Word :=
  emptyTyped calls keyType valueType

/--
Julia source: base/iddict.jl:64-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rehash!(d::IdDict, newsz::Integer = length(d.ht)%UInt)
    d.ht = ccall(:jl_idtable_rehash, Memory{Any}, (Any, Csize_t), d.ht, newsz)
    d
end
```
-/
def rehashCsize (calls : Callees) (address size : Word) : M Word := do
  let fields ← dictionary address
  let memory ← (C.jl_idtable_rehash calls.gc fields.ht size)
  storeHT address memory
  pure address

def rehash (calls : Callees) (address integer : Word) : M Word := do
  rehashCsize calls address (← (calls.toCsize integer))

def rehashDefault (calls : Callees) (address : Word) : M Word := do
  let fields ← dictionary address
  rehashCsize calls address (UInt64.ofNat fields.ht.length)

/--
Julia source: base/iddict.jl:69-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sizehint!(d::IdDict, newsz::Integer)
    newsz = _tablesz(newsz*2)  # *2 for keys and values in same array
    oldsz = length(d.ht)
    # grow at least 25%
    if newsz < (oldsz*5)>>2
        return d
    end
    rehash!(d, newsz)
end
```
-/
def sizehint! (calls : Callees) (address size : Word) : M Word := do
  let size ← (calls.doubleInteger size)
  let size ← (calls.tableSize size)
  let fields ← dictionary address
  let oldsz := JInt.wrap .i64 (Int.ofNat fields.ht.length)
  let minimum := JuliaLean.base.int.ashr_int (oldsz * JInt.wrap .i64 5) (JInt.wrap .i64 2)
  if ← (calls.lessThanInt size minimum) then pure address
  else rehash calls address size

/--
Julia source: base/iddict.jl:79-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(d::IdDict{K,V}, @nospecialize(val), @nospecialize(key)) where {K, V}
    !isa(key, K) && throw(KeyTypeError(K, key))
    if !(val isa V) # avoid a dynamic call
        val = convert(V, val)::V
    end
    if d.ndel >= ((3*length(d.ht))>>2)
        rehash!(d, max((length(d.ht)%UInt)>>1, 32))
        d.ndel = 0
    end
    inserted = RefValue{Cint}(0)
    d.ht = ccall(:jl_eqtable_put, Memory{Any}, (Any, Any, Any, Ptr{Cint}), d.ht, key, val, inserted)
    d.count += inserted[]
    return d
end
```
-/
def setindex! (calls : Callees) (address value key : Word) : M Word := do
  let fields ← dictionary address
  if !(← isa calls key fields.keyType) then fail (.keyTypeError fields.keyType key)
  let value ← if ← isa calls value fields.valueType then pure value
    else assertType calls (← (calls.convert fields.valueType value)) fields.valueType
  let fields ← dictionary address
  let threshold := JuliaLean.base.int.ashr_int
    (JInt.wrap .i64 3 * JInt.wrap .i64 (Int.ofNat fields.ht.length)) (JInt.wrap .i64 2)
  if fields.ndel.val ≥ threshold.val then
    let half := UInt64.ofNat fields.ht.length >>> 1
    let _ ← rehashCsize calls address (if half < 32 then 32 else half)
    storeIntField address 16 (JInt.wrap .i64 0)
  let fields ← dictionary address
  let (memory, inserted) ← (C.jl_eqtable_put calls.gc fields.ht key value true)
  match inserted with
  | none => fail (.abort "jl_eqtable_put omitted requested Cint output")
  | some inserted =>
    storeHT address memory
    let fields ← dictionary address
    storeIntField address 8 (fields.count + JInt.wrap .i64 (if inserted then 1 else 0))
    pure address

/--
Julia source: base/iddict.jl:94-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(d::IdDict{K,V}, @nospecialize(key), @nospecialize(default)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, default)
    val === default ? default : val::V
end
```
-/
def get (calls : Callees) (address key fallback : Word) : M Word := do
  let fields ← dictionary address
  let value ← (C.jl_eqtable_get fields.ht key fallback)
  if ← (C.jl_egal_ value fallback) then pure fallback
  else assertType calls value fields.valueType

/--
Julia source: base/iddict.jl:99-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(d::IdDict{K,V}, @nospecialize(key)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, secret_table_token)
    val === secret_table_token && throw(KeyError(key))
    return val::V
end
```
-/
def getindex (calls : Callees) (address key : Word) : M Word := do
  let fields ← dictionary address
  let token ← secretToken
  let value ← (C.jl_eqtable_get fields.ht key token)
  if ← (C.jl_egal_ value token) then fail (.keyError key)
  assertType calls value fields.valueType

/--
Julia source: base/iddict.jl:105-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(d::IdDict{K,V}, @nospecialize(key), @nospecialize(default)) where {K, V}
    found = RefValue{Cint}(0)
    val = ccall(:jl_eqtable_pop, Any, (Any, Any, Any, Ptr{Cint}), d.ht, key, default, found)
    if found[] === Cint(0)
        return default
    else
        d.count -= 1
        d.ndel += 1
        return val::V
    end
end
```
-/
def popDefault (calls : Callees) (address key fallback : Word) : M Word := do
  let fields ← dictionary address
  let (value, found) ← (C.jl_eqtable_pop fields.ht key fallback true)
  match found with
  | none => fail (.abort "jl_eqtable_pop omitted requested Cint output")
  | some false => pure fallback
  | some true =>
    storeIntField address 8 (fields.count - JInt.wrap .i64 1)
    storeIntField address 16 (fields.ndel + JInt.wrap .i64 1)
    assertType calls value fields.valueType

/--
Julia source: base/iddict.jl:117-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(d::IdDict{K,V}, @nospecialize(key)) where {K, V}
    val = pop!(d, key, secret_table_token)
    val === secret_table_token && throw(KeyError(key))
    return val::V
end
```
-/
def pop (calls : Callees) (address key : Word) : M Word := do
  let token ← secretToken
  let value ← popDefault calls address key token
  if ← (C.jl_egal_ value token) then fail (.keyError key)
  let fields ← dictionary address
  assertType calls value fields.valueType

/--
Julia source: base/iddict.jl:123-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function delete!(d::IdDict{K}, @nospecialize(key)) where K
    pop!(d, key, secret_table_token)
    d
end
```
-/
def deleteBang (calls : Callees) (address key : Word) : M Word := do
  let _ ← popDefault calls address key (← secretToken)
  pure address

/--
Julia source: base/iddict.jl:128-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(d::IdDict)
    d.ht = Memory{Any}(undef, 32)
    ht = d.ht
    t = @_gc_preserve_begin ht
    memset(unsafe_convert(Ptr{Cvoid}, ht), 0, sizeof(ht) % UInt)
    @_gc_preserve_end t
    d.ndel = 0
    d.count = 0
    return d
end
```
-/
def emptyBang (calls : Callees) (address : Word) : M Word := do
  let memory ← (C.allocMemoryAny calls.gc 32)
  storeHT address memory
  do
    let root ← JuliaLean.src.identity_runtime.newLocal (some memory)
    JuliaLean.src.identity_runtime.pushRoots [root]
    let bytes := memory.length * 8
    JuliaLean.src.identity_runtime.requireReadable (UInt64.ofNat memory.ptr) bytes
    JuliaLean.src.identity_runtime.modifyWorld fun world => { world with
      raw := { world.raw with
        heap := world.raw.heap.writeBytes memory.ptr (List.replicate bytes (JInt.wrap .u8 0)) } }
    JuliaLean.src.identity_runtime.popRoots
  storeIntField address 16 (JInt.wrap .i64 0)
  storeIntField address 8 (JInt.wrap .i64 0)
  pure address

/--
Julia source: base/iddict.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_oidd_nextind(a, i) = reinterpret(Int, ccall(:jl_eqtable_nextind, Csize_t, (Any, Csize_t), a, i))
```
-/
def oiddNextind (memory : Memory) (index : Word) : M (JInt .i64) := do
  let next ← (C.jl_eqtable_nextind memory index)
  pure (JInt.wrap .i64 (Int.ofNat next.toNat))

/-- essentials.jl:400-404 and builtins.c's boxed memoryrefget path:
checked, one-based Memory{Any} reads preserve BoundsError and UndefRefError. -/
def memoryAt (memory : Memory) (index : JInt .i64) : M Word := do
  if index.val < 1 || index.val.toNat > memory.length then fail (.array .bounds)
  let value ← JuliaLean.src.identity_runtime.plainReadCell memory (UInt64.ofNat (index.val-1).toNat)
  if value == 0 then fail (.array .undefinedReference) else pure value

/--
Julia source: base/iddict.jl:141-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(d::IdDict{K,V}, idx=0) where {K, V}
    idx = _oidd_nextind(d.ht, idx%UInt)
    idx == -1 && return nothing
    return (Pair{K, V}(d.ht[idx + 1]::K, d.ht[idx + 2]::V), idx + 2)
end
```
-/
def iterate (calls : Callees) (address : Word) (cursor : JInt .i64 := JInt.wrap .i64 0) :
    M (Option (Word × JInt .i64)) := do
  let fields ← dictionary address
  let idx ← oiddNextind fields.ht (UInt64.ofNat (JuliaLean.base.int.remT .u64 cursor).val.toNat)
  if idx.val == -1 then pure none
  else
    let rawKey ← memoryAt fields.ht (idx+JInt.wrap .i64 1)
    let key ← assertType calls rawKey fields.keyType
    let rawValue ← memoryAt fields.ht (idx+JInt.wrap .i64 2)
    let value ← assertType calls rawValue fields.valueType
    let pair ← calls.newPair fields.keyType fields.valueType key value
    pure (some (pair, idx+JInt.wrap .i64 2))

/--
Julia source: base/iddict.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(d::IdDict) = d.count
```
-/
def length (address : Word) : M (JInt .i64) := do pure (← dictionary address).count

/--
Julia source: base/iddict.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(d::IdDict) = typeof(d)(d)
```
-/
def copyDict (calls : Callees) (address : Word) : M Word := copyConstruct calls address

/--
Julia source: base/iddict.jl:151-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(d::IdDict{K,V}, @nospecialize(key), @nospecialize(default)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, secret_table_token)
    if val === secret_table_token
        val = isa(default, V) ? default : convert(V, default)::V
        setindex!(d, val, key)
        return val
    else
        return val::V
    end
end
```
-/
def getBang (calls : Callees) (address key fallback : Word) : M Word := do
  let fields ← dictionary address
  let token ← secretToken
  let value ← (C.jl_eqtable_get fields.ht key token)
  if ← (C.jl_egal_ value token) then
    let value ← if ← isa calls fallback fields.valueType then pure fallback
      else assertType calls (← (calls.convert fields.valueType fallback)) fields.valueType
    let _ ← setindex! calls address value key
    pure value
  else assertType calls value fields.valueType

/--
Julia source: base/iddict.jl:162-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(default::Callable, d::IdDict{K,V}, @nospecialize(key)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, secret_table_token)
    if val === secret_table_token
        return default()
    else
        return val::V
    end
end
```
-/
def getCallable (calls : Callees) (default : Unit → M Word) (address key : Word) : M Word := do
  let fields ← dictionary address
  let token ← secretToken
  let value ← (C.jl_eqtable_get fields.ht key token)
  if ← (C.jl_egal_ value token) then default ()
  else assertType calls value fields.valueType

/--
Julia source: base/iddict.jl:171-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(default::Callable, d::IdDict{K,V}, @nospecialize(key)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, secret_table_token)
    if val === secret_table_token
        val = default()
        if !isa(val, V)
            val = convert(V, val)::V
        end
        setindex!(d, val, key)
        return val
    else
        return val::V
    end
end
```
-/
def getBangCallable (calls : Callees) (default : Unit → M Word) (address key : Word) : M Word := do
  let fields ← dictionary address
  let token ← secretToken
  let value ← (C.jl_eqtable_get fields.ht key token)
  if ← (C.jl_egal_ value token) then
    let value ← default ()
    let value ← if ← isa calls value fields.valueType then pure value
      else assertType calls (← (calls.convert fields.valueType value)) fields.valueType
    let _ ← setindex! calls address value key
    pure value
  else assertType calls value fields.valueType

/--
Julia source: base/iddict.jl:185-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(@nospecialize(k), v::KeySet{<:Any,<:IdDict}) = get(v.dict, k, secret_table_token) !== secret_table_token
```
-/
def inKeySet (calls : Callees) (address key : Word) : M Bool := do
  let token ← secretToken
  let value ← get calls address key token
  return !(← (C.jl_egal_ value token))


def insertPairList (calls : Callees) (address : Word) : List (Word × Word) → M Unit
  | [] => pure ()
  | (key, value)::rest => do
    let _ ← setindex! calls address value key
    insertPairList calls address rest

/--
Julia source: base/iddict.jl:42-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function IdDict{K,V}(pairs::Pair...) where {K, V}
        d = IdDict{K,V}()
        sizehint!(d, length(pairs))
        for (k,v) in pairs; d[k] = v; end
        d
    end
```
-/
def fromPairs (calls : Callees) (keyType valueType : Word) (pairs : List (Word × Word)) : M Word := do
  let address ← emptyTyped calls keyType valueType
  let count ← calls.lengthArgument pairs.length
  let _ ← sizehint! calls address count
  insertPairList calls address pairs
  pure address

/-- The iterator protocol and destructuring calls remain selected Julia methods.
The loop below consumes exactly their actual results, without an iteration cap. -/
structure IteratorCalls (I S : Type) where
  size : I → M JuliaLean.base.iddict.IteratorSize
  length : I → M Word
  iterate : I → Option S → M (Option (Word × S))
  destructure : Word → M (Word × Word)

def insertIterator {I S : Type} (calls : Callees) (iter : IteratorCalls I S)
    (address : Word) (value : I) (state : Option S) : M Unit := do
  match ← iter.iterate value state with
  | none => pure ()
  | some (item, next) =>
    let (key, value') ← iter.destructure item
    let _ ← setindex! calls address value' key
    insertIterator calls iter address value (some next)
partial_fixpoint

/--
Julia source: base/iddict.jl:33-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function IdDict{K,V}(itr) where {K, V}
        d = IdDict{K,V}()
        if IteratorSize(itr) isa Union{HasLength, HasShape}
            sizehint!(d, length(itr))
        end
        for (k,v) in itr; d[k] = v; end
        d
    end
```
-/
def fromIterator {I S : Type} (calls : Callees) (iter : IteratorCalls I S)
    (keyType valueType : Word) (value : I) : M Word := do
  let address ← emptyTyped calls keyType valueType
  let size ← iter.size value
  if size == .hasLength || size == .hasShape then
    let _ ← sizehint! calls address (← iter.length value)
  insertIterator calls iter address value none
  pure address

/--
Julia source: base/iddict.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(ps::Pair{K,V}...)           where {K,V} = IdDict{K,V}(ps)
```
-/
def fromPairsKV {I S : Type} (calls : Callees) (iter : IteratorCalls I S)
    (keyType valueType : Word) (pairs : I) : M Word :=
  fromIterator calls iter keyType valueType pairs

/--
Julia source: base/iddict.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(ps::Pair{K}...)             where {K}   = IdDict{K,Any}(ps)
```
-/
def fromPairsK {I S : Type} (calls : Callees) (iter : IteratorCalls I S)
    (keyType : Word) (pairs : I) : M Word := do
  fromIterator calls iter keyType (← C.getWorld).globals.anyType pairs

/--
Julia source: base/iddict.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(ps::(Pair{K,V} where K)...) where {V}   = IdDict{Any,V}(ps)
```
-/
def fromPairsV {I S : Type} (calls : Callees) (iter : IteratorCalls I S)
    (valueType : Word) (pairs : I) : M Word := do
  fromIterator calls iter (← C.getWorld).globals.anyType valueType pairs

/--
Julia source: base/iddict.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(ps::Pair...)                            = IdDict{Any,Any}(ps)
```
-/
def fromPairsAny {I S : Type} (calls : Callees) (iter : IteratorCalls I S) (pairs : I) : M Word := do
  let anyType := (← C.getWorld).globals.anyType
  fromIterator calls iter anyType anyType pairs


/--
Julia source: base/iddict.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(kv) = dict_with_eltype((K, V) -> IdDict{K, V}, kv, eltype(kv))
```
-/
def fromEltype {I S : Type} (calls : Callees) (iter : IteratorCalls I S)
    (dictWithEltype : (Word → Word → I → M Word) → I → Word → M Word)
    (value : I) (eltype : I → Word) : M Word :=
  dictWithEltype (fun keyType valueType value => fromIterator calls iter keyType valueType value)
    value (eltype value)

/--
Julia source: base/iddict.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter!(f, d::IdDict) = filter_in_one_pass!(f, d)
```
-/
def filterBang (calls : Callees) (predicate : Word → M Word) (address : Word) : M Word :=
  calls.filterInOnePass predicate address

end JuliaLean.base.iddict
/-!
# Values, `===`, `isequal` and types for the identity collections

`IdDict`, `IdSet` and `WeakValueIdDict` compare keys with `===` (`egal`);
`Set`, `Dict` and `WeakKeyDict` compare with `isequal`. The bugs of this area
live in the gap between the two, so the value universe has `===`-distinct
values that are `isequal`:

* `int n` (`Int64`) and `flt n` (the `Float64` with integral value `n`):
  `isequal(1, 1.0)`, `1 !== 1.0`;
* `vec id c` (`Vector{Int}` holding `[c]`) and `fvec id c` (`Vector{Float64}`
  holding `[c.0]`): mutable, so `===` compares the object identity `id`
  (together with the constructor), while `isequal` compares contents;
* `sym s` (`Symbol`) and `str s` (`String`): `===` and `isequal` both
  compare contents (Julia's egal compares `String` bytes);
* `nothing`.

No arithmetic is performed on `int n` or `flt n`; they are opaque Julia
values, so `Int` is enough to name them. `==` (used by `in` on vectors)
coincides with `isequal` on this universe: it has no `NaN`, `-0.0` or
`missing`.
-/

namespace JuliaLean.IdDicts

/-- `===` (`jl_egal`): every constructor argument is part of the identity. -/
def egal (a b : JVal) : Bool := a == b

/-- `isa(x, T)`. -/
def isa : JVal → JTy → Bool
  | _, .any => true
  | .int _, .int => true
  | .flt _, .flt => true
  | .sym _, .sym => true
  | .str _, .str => true
  | .vec _ _, .vec => true
  | .fvec _ _, .fvec => true
  | .nothing, .nothing => true
  | _, _ => false

/-- `convert(T, x)` on the universe: identity when `isa(x, T)`, the numeric
conversions `Int64 ↔ Float64` of integral values, and `Vector{Int} ↔
Vector{Float64}`, which allocates a new array (modelled as the object with the
other constructor and the same `id`, `===`-distinct from `x`). Every other
pair is a `MethodError`. -/
def convert (T : JTy) (x : JVal) : Except IErr JVal :=
  if isa x T then .ok x else
  match T, x with
  | .int, .flt n => .ok (.int n)
  | .flt, .int n => .ok (.flt n)
  | .vec, .fvec i c => .ok (.vec i c)
  | .fvec, .vec i c => .ok (.fvec i c)
  | _, _ => .error .methodError

end JuliaLean.IdDicts
/-!
# `IdDict`, base/iddict.jl (master `bbfa0ce4150`)

The table `d.ht::Memory{Any}` is manipulated only through the C functions
`jl_eqtable_put/get/pop/nextind` and `jl_idtable_rehash` (src/iddict.c). They
are modelled as a primitive map with `===` keys: `Tab` is the list of live
`(key, value)` pairs in slot order. src/iddict.c implements exactly this: a
deleted slot holds the tombstone `(nothing, NULL)`, skipped by
`jl_eqtable_nextind`, and the probe loops continue past tombstones (also for
the key `nothing`, src/iddict.c:67-71, 128-130).

The Julia wrapper code is mirrored line by line: the `count`/`ndel`
bookkeeping, the `ndel` rehash trigger, the `secret_table_token` sentinel, the
type checks and conversions, and the `::K`/`::V` casts.

Modelling decisions:
* `sz` is `length(d.ht)`. `jl_eqtable_put` may replace the array by a larger
  one (src/iddict.c:87-103); that growth is not tracked: it preserves the live
  pairs, and `sz` only decides when `setindex!` rehashes, which also
  preserves them.
* `count`, `ndel`, `sz` are `Nat`: on a table that fits in memory the Int
  arithmetic of base/iddict.jl:84-85,90,111-112 cannot wrap. `sizehint!`, the
  one place where a user integer enters, uses wrapping `JInt .i64`.
* Iteration order is the slot order of `Tab`; in Julia it is the hash order.
  No property depends on the order.
-/

namespace JuliaLean.IdDicts

/-- The live `(key, value)` pairs of an eqtable, in slot order. -/
abbrev Tab := List (JVal × JVal)

/-- `jl_eqtable_get(h, key, deflt)`, src/iddict.c:151-156. -/
def eqtableGet : Tab → JVal → JVal → JVal
  | [], _, deflt => deflt
  | (k', v') :: t, k, deflt => if egal k k' then v' else eqtableGet t k deflt

/-- `jl_eqtable_put(h, key, val, &inserted)`, src/iddict.c:140-147: replaces
the value of a `===` key in place (`inserted = 0`) or fills a free slot
(`inserted = 1`). -/
def eqtablePut : Tab → JVal → JVal → Tab × Nat
  | [], k, v => ([(k, v)], 1)
  | (k', v') :: t, k, v =>
      if egal k k' then ((k', v) :: t, 0)
      else let r := eqtablePut t k v; ((k', v') :: r.1, r.2)

/-- `jl_eqtable_pop(h, key, deflt, &found)`, src/iddict.c:164-176: the value
(or `deflt`), `found`, and the table with the pair cleared. -/
def eqtablePop : Tab → JVal → JVal → JVal × Bool × Tab
  | [], _, deflt => (deflt, false, [])
  | (k', v') :: t, k, deflt =>
      if egal k k' then (v', true, t)
      else let r := eqtablePop t k deflt; (r.1, r.2.1, (k', v') :: r.2.2)

/-- `IdDict{K,V}` fields, base/iddict.jl:27-31. -/
structure IdDict where
  K : JTy
  V : JTy
  ht : Tab
  /-- `length(d.ht)` -/
  sz : Nat
  count : Nat
  ndel : Nat

/-- `IdDict{K,V}()`, base/iddict.jl:31: `Memory{Any}(undef, 32)`. -/
def IdDict.new (K V : JTy) : IdDict := ⟨K, V, [], 32, 0, 0⟩

/-- `rehash!(d, newsz)`, base/iddict.jl:64-67: `jl_idtable_rehash` copies the
live pairs into a fresh array of `newsz` slots. -/
def IdDict.rehash (d : IdDict) (newsz : Nat) : IdDict := { d with sz := newsz }

/-- `sizehint!(d, newsz)`, base/iddict.jl:69-77 (`newsz*2` wraps). -/
def IdDict.sizehint (d : IdDict) (newsz : JInt .i64) : IdDict :=
  let newsz := JuliaLean.Dicts.tableszI64 (newsz * JInt.lit .i64 2)
  let oldsz := d.sz
  if newsz.val < ((oldsz * 5 / 4 : Nat) : Int) then d
  else d.rehash newsz.val.toNat

/-- `x::T` -/
def cast (x : JVal) (T : JTy) : Except IErr JVal :=
  if isa x T then .ok x else .error .typeError

/-- `setindex!(d, val, key)`, base/iddict.jl:79-92. -/
def IdDict.setindex (d : IdDict) (val key : JVal) : Out IdDict Unit :=
  if !isa key d.K then (d, .error .typeError) else
  let val? : Except IErr JVal :=
    if isa val d.V then .ok val else (convert d.V val).bind (cast · d.V)
  match val? with
  | .error e => (d, .error e)
  | .ok val =>
    let d := if d.ndel ≥ (3 * d.sz) / 4 then { d.rehash (max (d.sz / 2) 32) with ndel := 0 } else d
    let r := eqtablePut d.ht key val
    ({ d with ht := r.1, count := d.count + r.2 }, .ok ())

/-- `get(d, key, default)`, base/iddict.jl:94-97. -/
def IdDict.get (d : IdDict) (key default : JVal) : Except IErr JVal :=
  let val := eqtableGet d.ht key default
  if egal val default then .ok default else cast val d.V

/-- `getindex(d, key)`, base/iddict.jl:99-103. -/
def IdDict.getindex (d : IdDict) (key : JVal) : Except IErr JVal :=
  let val := eqtableGet d.ht key token
  if egal val token then .error .keyError else cast val d.V

/-- `pop!(d, key, default)`, base/iddict.jl:105-115. -/
def IdDict.pop3 (d : IdDict) (key default : JVal) : Out IdDict JVal :=
  let r := eqtablePop d.ht key default
  let d := { d with ht := r.2.2 }
  if !r.2.1 then (d, .ok default)
  else ({ d with count := d.count - 1, ndel := d.ndel + 1 }, cast r.1 d.V)

/-- `pop!(d, key)`, base/iddict.jl:117-121. -/
def IdDict.pop (d : IdDict) (key : JVal) : Out IdDict JVal :=
  let r := d.pop3 key token
  match r.2 with
  | .error e => (r.1, .error e)
  | .ok val => if egal val token then (r.1, .error .keyError) else (r.1, cast val d.V)

/-- `delete!(d, key)`, base/iddict.jl:123-126. -/
def IdDict.delete (d : IdDict) (key : JVal) : Out IdDict Unit :=
  let r := d.pop3 key token
  (r.1, r.2.map fun _ => ())

/-- `empty!(d)`, base/iddict.jl:128-137. -/
def IdDict.empty (d : IdDict) : IdDict := { d with ht := [], sz := 32, ndel := 0, count := 0 }

/-- `iterate(d)` to exhaustion, base/iddict.jl:139-145: `_oidd_nextind`
visits every live pair once; each yields `Pair{K,V}(ht[i]::K, ht[i+1]::V)`. -/
def IdDict.iterate (d : IdDict) : Except IErr Tab :=
  d.ht.mapM fun p => do
    let k ← cast p.1 d.K
    let v ← cast p.2 d.V
    pure (k, v)

/-- `length(d) = d.count`, base/iddict.jl:147. -/
def IdDict.length (d : IdDict) : Nat := d.count

/-- `haskey(d, k) = in(k, keys(d))`, base/abstractdict.jl:19 and
`in(k, ::KeySet{<:Any,<:IdDict})`, base/iddict.jl:185. -/
def IdDict.haskey (d : IdDict) (k : JVal) : Except IErr Bool :=
  (d.get k token).map fun v => !egal v token

/-- `get!(d, key, default)`, base/iddict.jl:151-160. -/
def IdDict.getBang (d : IdDict) (key default : JVal) : Out IdDict JVal :=
  let val := eqtableGet d.ht key token
  if egal val token then
    let val? : Except IErr JVal :=
      if isa default d.V then .ok default else (convert d.V default).bind (cast · d.V)
    match val? with
    | .error e => (d, .error e)
    | .ok val =>
      let r := d.setindex val key
      (r.1, r.2.map fun _ => val)
  else (d, cast val d.V)

/-- `get!(default::Callable, d, key)`, base/iddict.jl:171-183, for a `default`
that returns `fv` without touching `d`. -/
def IdDict.getBangF (d : IdDict) (fv key : JVal) : Out IdDict JVal :=
  let val := eqtableGet d.ht key token
  if egal val token then
    let val? : Except IErr JVal :=
      if !isa fv d.V then (convert d.V fv).bind (cast · d.V) else .ok fv
    match val? with
    | .error e => (d, .error e)
    | .ok val =>
      let r := d.setindex val key
      (r.1, r.2.map fun _ => val)
  else (d, cast val d.V)

end JuliaLean.IdDicts
/-!
# The `IdDict` hash table slot by slot, `src/iddict.c` and `base/iddict.jl`

`JuliaLean.IdDicts` models `d.ht` as the list of live pairs. Iterating while
assigning (the generic `map!(f, values(d))` and `mergewith!(f, d, d)`,
`base/abstractdict.jl:288-293,673-681`) depends on where the pairs sit, so this
file mirrors the C table functions on the array itself: `ht` is the
`Memory{Any}` of length `2 * slots` holding key/value pairs; `none` is `NULL`.
A deleted pair leaves the key `nothing` with a `NULL` value
(`jl_eqtable_pop`, src/iddict.c:164-176).

Keys and values are `Int`s here (an `IdDict{Int,Int}`); `===` on `Int` is
equality, and `keyhash` (`jl_object_id_`) is a parameter.
-/

namespace JuliaLean.DictsCov.EqTable

/-- `jl_alloc_memory_any(n)`: `n` entries, all `NULL` (`n/2` pairs). -/
def alloc (n : Nat) : Mem := List.replicate (n / 2) (.null, none)

def getSlot (a : Mem) (i : Nat) : KSlot × Option Int := a.getD i (.null, none)

/-- `max_probe(size)`, src/iddict.c:6. -/
def maxProbe (size : Nat) : Nat := if size ≤ 1024 then 16 else size / 64

/-- The probe loop of `jl_table_assign_bp`, src/iddict.c:50-79, over pair
indices (`index/2`). Returns `inr ()` when the value of a present key was
replaced, `inl (some j)` for the first free slot (`NULL` or deleted), `inl none`
when the table is full. -/
def probe (a : Mem) (key : Int) (sz : Nat) (orig : Nat) :
    Nat → Nat → Nat → Option Nat → Sum (Option Nat) Nat
  | 0, _, _, es => .inl es
  | fuel + 1, index, iter, es =>
    let (k2, v2) := getSlot a index
    if k2 == .null then .inl (if es.isNone then some index else es)
    else
      -- `jl_egal(key, k2)` with a present value: replace
      if k2 == .key key ∧ v2.isSome then .inr index
      else
        let es := if es.isNone ∧ v2.isNone then some index else es
        let index := (index + 1) % sz
        let iter := iter + 1
        if iter ≤ maxProbe sz ∧ index ≠ orig then probe a key sz orig fuel index iter es
        else .inl es

/-- Write pair slot `j`. -/
def setSlot (a : Mem) (j : Nat) (p : KSlot × Option Int) : Mem := a.set j p

/-- `jl_idtable_rehash(a, newsz)`, src/iddict.c:13-30: re-insert every pair
with a non-`NULL` value, in index order, into a fresh array of `newsz`
entries, with the insertion `ins`. -/
def rehashWith (ins : Mem → Int → Int → Mem) (a : Mem) (newsz : Nat) : Mem :=
  a.foldl (fun b p => match p with
    | (.key k, some v) => ins b k v
    | _ => b) (alloc newsz)

/-- `jl_table_assign_bp(&a, key, val)`, src/iddict.c:32-104: the new array and
`inserted`. `fuel` bounds the number of growths. -/
def assign (keyhash : Int → Nat) : Nat → Mem → Int → Int → Mem × Nat
  | 0, a, _, _ => (a, 0)
  | fuel + 1, a, key, val =>
    let a := if a.length = 0 then alloc 32 else a
    let sz := a.length
    let index := keyhash key % sz
    match probe a key sz index (sz + 1) index 0 none with
    | .inr j => (setSlot a j (.key key, some val), 0)
    | .inl (some j) => (setSlot a j (.key key, some val), 1)
    | .inl none =>
      let len := 2 * sz
      let newsz := if len < 32 then 32 else if len ≥ 2 ^ 19 ∨ len ≤ 2 ^ 8 then len * 2 else len * 4
      assign keyhash fuel (rehashWith (fun b k v => (assign keyhash fuel b k v).1) a newsz) key val

/-- `jl_idtable_rehash` with the insertion of `jl_table_assign_bp`. -/
def rehash (keyhash : Int → Nat) (fuel : Nat) (a : Mem) (newsz : Nat) : Mem :=
  rehashWith (fun b k v => (assign keyhash fuel b k v).1) a newsz

/-- The probe loop of `jl_table_peek_bp` for an `Int` key, src/iddict.c:118-133. -/
def peekGo (a : Mem) (key : Int) (sz orig : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, index, iter =>
    let (k2, v2) := getSlot a index
    if k2 == .null then none
    else if k2 == .key key then (if v2.isSome then some index else none)
    else
      let index := (index + 1) % sz
      let iter := iter + 1
      if iter ≤ maxProbe sz ∧ index ≠ orig then peekGo a key sz orig fuel index iter else none

/-- `jl_table_peek_bp(a, key)`, src/iddict.c:108-134: the pair index holding
`key` with a non-`NULL` value. -/
def peekH (keyhash : Int → Nat) (a : Mem) (key : Int) : Option Nat :=
  let sz := a.length
  if sz = 0 then none else
  let orig := keyhash key % sz
  peekGo a key sz orig (sz + 1) orig 0

/-- `IdDict{K,V}()`: `Memory{Any}(undef, 32)`, base/iddict.jl:31. -/
def IdD.new : IdD := ⟨alloc 32, 0, 0⟩

/-- `length(d.ht)` -/
def IdD.len (d : IdD) : Nat := 2 * d.ht.length

/-- Enough growths for any table in this file. -/
def fuel : Nat := 64

/-- `setindex!(d, val, key)`, base/iddict.jl:79-92, for `Int` keys and values. -/
def IdD.setindex (keyhash : Int → Nat) (d : IdD) (val key : Int) : IdD :=
  let d := if d.ndel ≥ (3 * d.len) / 4 then
      { d with ht := rehash keyhash fuel d.ht (max (d.len / 2) 32), ndel := 0 }
    else d
  let r := assign keyhash fuel d.ht key val
  { d with ht := r.1, count := d.count + r.2 }

/-- `delete!(d, key)` = `pop!(d, key, secret_table_token)`, base/iddict.jl:105-126. -/
def IdD.delete (keyhash : Int → Nat) (d : IdD) (key : Int) : IdD :=
  match peekH keyhash d.ht key with
  | some j => { d with ht := setSlot d.ht j (.nothing, none), count := d.count - 1, ndel := d.ndel + 1 }
  | none => d

/-- `get(d, key, default)`, base/iddict.jl:94-97. -/
def IdD.get (keyhash : Int → Nat) (d : IdD) (key : Int) : Option Int :=
  match peekH keyhash d.ht key with
  | some j => (getSlot d.ht j).2
  | none => none

/-- `jl_eqtable_nextind(t, i)` on pair indices, src/iddict.c:178-188. -/
def nextind (a : Mem) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, j => if j ≥ a.length then none
    else if (getSlot a j).2.isSome then some j else nextind a fuel (j + 1)

/-- `iterate(d, idx)`, base/iddict.jl:141-145: the pair at the next live slot
at or after pair index `j`, and the next state (the following slot). -/
def IdD.iterate (d : IdD) (j : Nat) : Option ((Int × Int) × Nat) :=
  match nextind d.ht (d.ht.length + 1) j with
  | none => none
  | some i => match getSlot d.ht i with
    | (.key k, some v) => some ((k, v), i + 1)
    | _ => none

end JuliaLean.DictsCov.EqTable

namespace JuliaLean.DictsCov.IdDictRows


abbrev R (α : Type) := Except String α

structure State (K V : Type) where
  slots : List (Option (K × V))
  rawWords : Nat
  count : Int
  ndel : Int
  deriving Repr

def emptyState : State K V :=
  { slots := List.replicate 16 none, rawWords := 32, count := 0, ndel := 0 }

def foldSet (setindex : State K V → K → V → R (State K V)) :
    State K V → List (K × V) → R (State K V)
  | state, [] => .ok state
  | state, (k, v) :: pairs => do
      let state ← setindex state k v
      foldSet setindex state pairs

/-- Empty typed constructor, `base/iddict.jl:31`. -/
def method31 : State K V := emptyState

/-- Iterator constructor, `base/iddict.jl:33-40`. -/
def method33 (hasLength : Bool) (sizehint : State K V → Nat → State K V)
    (setindex : State K V → K → V → R (State K V)) (pairs : List (K × V)) : R (State K V) :=
  let d : State K V := method31
  let d := if hasLength then sizehint d pairs.length else d
  foldSet setindex d pairs

/-- Pair-vararg constructor, `base/iddict.jl:42-47`. -/
def method42 (sizehint : State K V → Nat → State K V)
    (setindex : State K V → K → V → R (State K V)) (pairs : List (K × V)) : R (State K V) :=
  let d : State K V := method31
  let d := sizehint d pairs.length
  foldSet setindex d pairs

/-- Same-type copy constructor, `base/iddict.jl:49`. -/
def method49 (copySlots : List (Option (K × V)) → List (Option (K × V)))
    (d : State K V) : State K V :=
  { slots := copySlots d.slots, rawWords := d.rawWords, count := d.count, ndel := d.ndel }

/-- Untyped empty constructor, `base/iddict.jl:52`. -/
def method52 : State K V := method31

/-- Empty-tuple constructor, `base/iddict.jl:53`. -/
def method53 (_emptyTuple : Unit) : State K V := method52

/-- Fully typed pair-vararg forwarding method, `base/iddict.jl:55`. -/
def method55 (typed : List (K × V) → R (State K V)) (pairs : List (K × V)) := typed pairs

/-- Key-typed pair-vararg forwarding method, `base/iddict.jl:56`. -/
def method56 (typed : List (K × V) → R (State K V)) (pairs : List (K × V)) := typed pairs

/-- Value-typed pair-vararg forwarding method, `base/iddict.jl:57`. -/
def method57 (typed : List (K × V) → R (State K V)) (pairs : List (K × V)) := typed pairs

/-- Any/Any pair-vararg forwarding method, `base/iddict.jl:58`. -/
def method58 (typed : List (K × V) → R (State K V)) (pairs : List (K × V)) := typed pairs

/-- Eltype-selecting constructor, `base/iddict.jl:60`. -/
def method60 (eltype : I → T) (dictWithEltype : I → T → R (State K V)) (kv : I) : R (State K V) :=
  dictWithEltype kv (eltype kv)

/-- `empty` specialization, `base/iddict.jl:62`. -/
def method62 : State K V := method31

/-- Runtime rehash wrapper, `base/iddict.jl:64-67`. -/
def method64 (rehash : List (Option (K × V)) → Nat → List (Option (K × V)))
    (d : State K V) (newsz : Nat) : State K V :=
  { d with slots := rehash d.slots newsz, rawWords := newsz }

inductive RawGet (V : Type) where
  | default
  | value (v : V)

/-- Three-argument `get`, `base/iddict.jl:94-97`. -/
def method94 (eqtableGet : State K V → Q → V → RawGet V)
    (d : State K V) (key : Q) (default : V) : V :=
  match eqtableGet d key default with
  | .default => default
  | .value value => value

structure PopResult (V : Type) where
  value : V
  found : Bool

/-- Defaulted pop, `base/iddict.jl:105-115`. -/
def method105 (eqtablePop : State K V → Q → V → PopResult V)
    (d : State K V) (key : Q) (default : V) : V × State K V :=
  let result := eqtablePop d key default
  if result.found then
    (result.value, { d with count := d.count - 1, ndel := d.ndel + 1 })
  else (default, d)

inductive Cell (V : Type) where
  | sentinel
  | stored (v : V)

/-- Sentinel-checking pop wrapper, `base/iddict.jl:117-121`. -/
def method117 (popDefault : State K V → Q → Cell V → Cell V × State K V)
    (d : State K V) (key : Q) : R (V × State K V) :=
  match popDefault d key .sentinel with
  | (.sentinel, _) => .error "KeyError"
  | (.stored value, d) => .ok (value, d)

/-- Runtime next-index wrapper, `base/iddict.jl:139`. -/
def method139 (eqtableNextind : A → Nat → Nat) (reinterpretInt : Nat → Int) (a : A) (i : Nat) : Int :=
  reinterpretInt (eqtableNextind a i)

/-- Copy wrapper, `base/iddict.jl:149`. -/
def method149 (sameTypeConstructor : State K V → State K V) (d : State K V) : State K V :=
  sameTypeConstructor d

/-- Value-defaulting `get!`, `base/iddict.jl:151-160`. -/
def method151 (getRaw : State K V → Q → Cell V) (convert : W → R V)
    (setindex : State K V → Q → V → R (State K V))
    (d : State K V) (key : Q) (default : W) : R (V × State K V) :=
  match getRaw d key with
  | .stored value => .ok (value, d)
  | .sentinel => do
      let value ← convert default
      let d ← setindex d key value
      return (value, d)

/-- Callable `get`, `base/iddict.jl:162-169`. -/
def method162 (getRaw : State K V → Q → Cell V) (default : Unit → R V)
    (d : State K V) (key : Q) : R V :=
  match getRaw d key with
  | .sentinel => default ()
  | .stored value => .ok value

/-- Callable `get!`, `base/iddict.jl:171-183`. -/
def method171 (getRaw : State K V → Q → Cell V) (default : Unit → R W)
    (convert : W → R V) (setindex : State K V → Q → V → R (State K V))
    (d : State K V) (key : Q) : R (V × State K V) :=
  match getRaw d key with
  | .stored value => .ok (value, d)
  | .sentinel => do
      let raw ← default ()
      let value ← convert raw
      let d ← setindex d key value
      return (value, d)

/-- IdDict filter delegation, `base/iddict.jl:189`. -/
def method189 (filterOnePass : (K × V → Bool) → State K V → State K V)
    (f : K × V → Bool) (d : State K V) : State K V := filterOnePass f d

end JuliaLean.DictsCov.IdDictRows

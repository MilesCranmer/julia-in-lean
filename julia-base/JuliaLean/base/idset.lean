import JuliaLean.src.idset_c
import JuliaLean.base.iddict

/-! IdSet objects, keys, and integer indices share the same native byte heap
as the IdDict binding. C index algorithms are concrete; selected Julia/Core
callees remain explicit. -/
namespace JuliaLean.base.idset
open JuliaLean
open JuliaLean.src.identity_runtime (Word Memory Error GC M fail)
namespace R
export JuliaLean.src.identity_runtime (getWorld modifyWorld loadWord encodeWord datatypeAt
  typeof typetag memoryOwner allocMemoryAny newLocal pushRoots popRoots gcWriteAtomic)
end R
namespace C
export JuliaLean.src.idset_c (memoryAtAddress keyAt keySet signed unsigned jl_idset_peek_bp
  jl_idset_put_key jl_idset_put_idx jl_idset_pop)
end C
namespace S
export JuliaLean.src.smallintset_c (Primitives elementWidth copyBytes zeroBytes)
end S
namespace D
export JuliaLean.base.iddict (storeHT storeIntField memoryAt)
end D

structure SetFields where
  list : Memory
  indices : Memory
  count : JInt .i64
  maximum : JInt .i64
  elementType : Word

structure Callees where
  gc : GC
  indices : S.Primitives
  newObject : Word → Memory → Memory → JInt .i64 → JInt .i64 → M Word
  copyKeys : Memory → M Memory
  isa : Word → Word → M Bool
  union : Word → Word → M Word
  setdiff : Word → Word → M Word
  unsafeFilter : (Word → M Bool) → Word → M Word

def fields (address : Word) : M SetFields := do
  let list ← C.memoryAtAddress (← R.loadWord address)
  let indices ← C.memoryAtAddress (← R.loadWord (address+8))
  let count ← R.loadWord (address+16)
  let maximum ← R.loadWord (address+24)
  let datatype ← R.datatypeAt (← R.typeof address)
  let elementType ← R.loadWord (datatype.parameters+8)
  pure ⟨list, indices, C.signed count, C.signed maximum, elementType⟩

def registerMemory (memory : Memory) : M Unit := do
  let owner := R.memoryOwner memory
  R.modifyWorld fun world => { world with
    memories := fun query => if query == owner then some memory else world.memories query }

def storeIndices (address : Word) (memory : Memory) : M Unit := do
  R.gcWriteAtomic address (address+8) (R.memoryOwner memory) .notAtomic
  registerMemory memory

def allocateBits (p : S.Primitives) (type : Word) (width : Nat) (empty : Memory) (length : Nat) : M Memory := do
  let memory ← JuliaLean.base.array.allocGenericMemory (some ⟨width, false, false⟩)
    (pure empty) (p.allocateBits type width) length
  registerMemory memory
  pure memory

def allocateIndices8 (p : S.Primitives) (length : Nat) : M Memory :=
  allocateBits p p.uint8Type 1 p.empty8 length

/-- genericmemory.jl's copy path for the three IdSet index types: allocate
same-type memory, then the installed native bits path copies its bytes. -/
def copyIndices (p : S.Primitives) (memory : Memory) : M Memory := do
  let type ← R.typetag (R.memoryOwner memory)
  let width ← S.elementWidth p memory false
  let empty := if width = 1 then p.empty8 else if width = 2 then p.empty16 else p.empty32
  let fresh ← allocateBits p type width empty memory.length
  if memory.length != 0 then
    S.copyBytes (UInt64.ofNat fresh.ptr) (UInt64.ofNat memory.ptr)
      (UInt64.ofNat memory.length * UInt64.ofNat width)
  pure fresh

def assertElement (calls : Callees) (value type : Word) : M Word := do
  if type == (← R.getWorld).globals.anyType then return value
  if ← calls.isa value type then pure value else fail (.typeAssertion type value)

def isAssigned (memory : Memory) (index : JInt .i64) : M Bool := do
  if index.val < 1 || index.val.toNat > memory.length then return false
  return (← C.keyAt memory (UInt64.ofNat (index.val-1).toNat)) != 0

def setMemory (memory : Memory) (index : JInt .i64) (value : Word) : M Unit := do
  if index.val < 1 || index.val.toNat > memory.length then fail (.array .bounds)
  JuliaLean.src.identity_runtime.writeCell memory (UInt64.ofNat (index.val-1).toNat) value .notAtomic

def unsetMemory (memory : Memory) (index : JInt .i64) : M Unit := do
  if index.val < 1 || index.val.toNat > memory.length then fail (.array .bounds)
  let data := memory.ptr + 8*(index.val-1).toNat
  match JuliaLean.src.genericmemory_c.memoryrefUnsetProgram memory.metadata data false with
  | .error error => fail (.abort ("invalid Memory{Any} layout: " ++ reprStr error))
  | .ok effects =>
    R.modifyWorld fun world => { world with
      raw := effects.foldl JuliaLean.src.genericmemory_c.interpretRawEffect world.raw }

def checkedUnsigned (value : JInt .i64) : M Word := do
  match JInt.convert "UInt64" .u64 value.val with
  | .error error => fail (.julia error)
  | .ok word => pure (UInt64.ofNat word.val.toNat)

def checkedInt (value : Word) : M (JInt .i64) := do
  match JInt.convert "Int64" .i64 (Int.ofNat value.toNat) with
  | .error error => fail (.julia error)
  | .ok word => pure word

def construct (calls : Callees) (type : Word) (list indices : Memory)
    (count maximum : JInt .i64) : M Word := do
  let address ← calls.newObject type list indices count maximum
  registerMemory list
  registerMemory indices
  pure address

/--
Julia source: base/idset.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IdSet{T}() where {T} = new(Memory{Any}(undef, 0), Memory{UInt8}(undef, 0), 0, 0)
```
-/
def emptyTyped (calls : Callees) (type : Word) : M Word := do
  let list ← R.allocMemoryAny calls.gc 0
  let indices ← allocateIndices8 calls.indices 0
  construct calls type list indices (JInt.wrap .i64 0) (JInt.wrap .i64 0)

/--
Julia source: base/idset.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IdSet{T}(s::IdSet{T}) where {T} = new(copy(s.list), copy(s.idxs), s.count, s.max)
```
-/
def copyConstruct (calls : Callees) (address : Word) : M Word := do
  let first ← fields address
  let list ← calls.copyKeys first.list
  let second ← fields address
  let indices ← copyIndices calls.indices second.indices
  let last ← fields address
  construct calls last.elementType list indices last.count last.maximum

/--
Julia source: base/idset.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdSet{T}(itr) where {T} = union!(IdSet{T}(), itr)
```
-/
def fromIterator (calls : Callees) (type iterator : Word) : M Word := do
  calls.union (← emptyTyped calls type) iterator

/--
Julia source: base/idset.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdSet() = IdSet{Any}()
```
-/
def emptyAny (calls : Callees) : M Word := do emptyTyped calls (← R.getWorld).globals.anyType

/--
Julia source: base/idset.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copymutable(s::IdSet) = typeof(s)(s)
```
-/
def copymutable (calls : Callees) (address : Word) : M Word := copyConstruct calls address

/--
Julia source: base/idset.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
emptymutable(s::IdSet{T}, ::Type{U}=T) where {T,U} = IdSet{U}()
```
-/
def emptymutable (calls : Callees) (address : Word) : M Word := do
  emptyTyped calls (← fields address).elementType

def emptymutableAs (calls : Callees) (_address type : Word) : M Word := emptyTyped calls type

/--
Julia source: base/idset.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(s::IdSet) = typeof(s)(s)
```
-/
def copy (calls : Callees) (address : Word) : M Word := copyConstruct calls address

/--
Julia source: base/idset.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haskey(s::IdSet, @nospecialize(key)) = ccall(:jl_idset_peek_bp, Int, (Any, Any, Any), s.list, s.idxs, key) != -1
```
-/
def haskey (calls : Callees) (address key : Word) : M Bool := do
  let current ← fields address
  return (← C.jl_idset_peek_bp calls.indices current.list current.indices key).val != -1

/--
Julia source: base/idset.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(s::IdSet) = s.count == 0
```
-/
def isempty (address : Word) : M Bool := do return (← fields address).count.val == 0

/--
Julia source: base/idset.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(s::IdSet)  = s.count
```
-/
def length (address : Word) : M (JInt .i64) := do return (← fields address).count

/--
Julia source: base/idset.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(@nospecialize(x), s::IdSet) = haskey(s, x)
```
-/
def «in» (calls : Callees) (value address : Word) : M Bool := haskey calls address value

/--
Julia source: base/idset.jl:48-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(s::IdSet, @nospecialize(x))
    idx = ccall(:jl_idset_peek_bp, Int, (Any, Any, Any), s.list, s.idxs, x)
    if idx >= 0
        s.list[idx + 1] = x
    else
        if s.max < length(s.list)
            idx = s.max
            @assert !isassigned(s.list, idx + 1) "bucket is already occupied"
            s.list[idx + 1] = x
            s.max = idx + 1
        else
            newidx = RefValue{Int}(0)
            newmax = RefValue{Csize_t}(s.max)
            setfield!(s, :list, ccall(:jl_idset_put_key, Any, (Any, Any, Ptr{Csize_t}, Ptr{Int}), s.list, x, newmax, newidx))
            idx = newidx[]
            s.max = Int(newmax[])
        end
        @assert s.list[s.max] === x "unexpected object in bucket"
        setfield!(s, :idxs, ccall(:jl_idset_put_idx, Any, (Any, Any, Int), s.list, s.idxs, idx))
        s.count += 1
    end
    s
end
```
-/
def push! (calls : Callees) (address value : Word) : M Word := do
  let before ← fields address
  let index ← C.jl_idset_peek_bp calls.indices before.list before.indices value
  if index.val ≥ 0 then
    let current ← fields address
    setMemory current.list (index+JInt.wrap .i64 1) value
  else
    let current ← fields address
    let index ← if current.maximum.val < Int.ofNat current.list.length then do
        let index := current.maximum
        if ← isAssigned current.list (index+JInt.wrap .i64 1) then
          fail (.array (.assertion "bucket is already occupied"))
        setMemory current.list (index+JInt.wrap .i64 1) value
        D.storeIntField address 24 (index+JInt.wrap .i64 1)
        pure index
      else do
        let maximum ← checkedUnsigned current.maximum
        let (list, maximum, index) ← C.jl_idset_put_key calls.gc current.list value maximum
        D.storeHT address list
        let maximum ← checkedInt maximum
        D.storeIntField address 24 maximum
        pure index
    let current ← fields address
    let stored ← D.memoryAt current.list current.maximum
    if !(← JuliaLean.src.builtins_identity_c.jl_egal_ stored value) then
      fail (.array (.assertion "unexpected object in bucket"))
    let current ← fields address
    let indices ← C.jl_idset_put_idx calls.indices current.list current.indices index
    storeIndices address indices
    let current ← fields address
    D.storeIntField address 16 (current.count+JInt.wrap .i64 1)
  pure address

def shrinkMaximum (address : Word) : M Unit := do
  let current ← fields address
  if current.maximum.val > 0 then
    if !(← isAssigned current.list current.maximum) then
      D.storeIntField address 24 (current.maximum-JInt.wrap .i64 1)
      shrinkMaximum address
partial_fixpoint

/--
Julia source: base/idset.jl:71-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _pop!(s::IdSet, @nospecialize(x))
    removed = ccall(:jl_idset_pop, Int, (Any, Any, Any), s.list, s.idxs, x)
    if removed != -1
        s.count -= 1
        while s.max > 0 && !isassigned(s.list, s.max)
            s.max -= 1
        end
    end
    removed
end
```
-/
def _pop! (calls : Callees) (address value : Word) : M (JInt .i64) := do
  let current ← fields address
  let removed ← C.jl_idset_pop calls.indices current.list current.indices value
  if removed.val != -1 then
    let current ← fields address
    D.storeIntField address 16 (current.count-JInt.wrap .i64 1)
    shrinkMaximum address
  pure removed

/--
Julia source: base/idset.jl:81-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pop!(s::IdSet, @nospecialize(x)) = _pop!(s, x) == -1 ? throw(KeyError(x)) : x
```
-/
def pop! (calls : Callees) (address value : Word) : M Word := do
  if (← _pop! calls address value).val == -1 then fail (.keyError value) else pure value

/--
Julia source: base/idset.jl:82-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pop!(s::IdSet, @nospecialize(x), @nospecialize(default)) = _pop!(s, x) == -1 ? default : x
```
-/
def popDefault (calls : Callees) (address value fallback : Word) : M Word := do
  if (← _pop! calls address value).val == -1 then pure fallback else pure value

/--
Julia source: base/idset.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
delete!(s::IdSet, @nospecialize(x)) = (_pop!(s, x); s)
```
-/
def delete! (calls : Callees) (address value : Word) : M Word := do
  let _ ← _pop! calls address value
  pure address

/--
Julia source: base/idset.jl:85-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sizehint!(s::IdSet, newsz::Integer)
    # TODO: grow/compact list and perform rehash, if profitable?
    # TODO: shrink?
    # s.list = resize(s.list, newsz)
    # newsz = _tablesz(newsz)
    # oldsz = length(s.idxs)
    # #grow at least 25%
    # if newsz < (oldsz*5)>>2
    #     return s
    # end
    # rehash!(s, newsz)
    nothing
end
```
-/
def sizehint! (_address _size : Word) : M Unit := pure ()

/--
Julia source: base/idset.jl:99-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _zero!(a::Memory{<:BitInteger})
    t = @_gc_preserve_begin a
    p = unsafe_convert(Ptr{Cvoid}, a)
    T = eltype(a)
    memset(p, 0x0, (sizeof(T) * length(a)) % UInt)
    @_gc_preserve_end t
    return a
end
```
-/
def _zero! (memory : Memory) : M Memory := do
  let root ← R.newLocal (some memory)
  R.pushRoots [root]
  let width := JInt.wrap .i64 memory.metadata.memoryLayout.size.val
  let count := width * JInt.wrap .i64 (Int.ofNat memory.length)
  S.zeroBytes (UInt64.ofNat memory.ptr) (C.unsigned count)
  R.popRoots
  pure memory

def clearList (list : Memory) (maximum index : Nat) : M Unit := do
  if index > maximum then return ()
  unsetMemory list (JInt.wrap .i64 (Int.ofNat index))
  clearList list maximum (index+1)
partial_fixpoint

/--
Julia source: base/idset.jl:108-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(s::IdSet)
    _zero!(s.idxs)
    list = s.list
    for i = 1:s.max
        unsetindex!(list, i)
    end
    s.count = 0
    s.max = 0
    s
end
```
-/
def empty! (address : Word) : M Word := do
  let current ← fields address
  let _ ← _zero! current.indices
  let current ← fields address
  clearList current.list current.maximum.val.toNat 1
  D.storeIntField address 16 (JInt.wrap .i64 0)
  D.storeIntField address 24 (JInt.wrap .i64 0)
  pure address

/--
Julia source: base/idset.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter!(f, d::IdSet) = unsafe_filter!(f, d)
```
-/
def filter! (calls : Callees) (predicate : Word → M Bool) (address : Word) : M Word :=
  calls.unsafeFilter predicate address

/--
Julia source: base/idset.jl:121-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(s::IdSet{S}, state=0) where {S}
    while true
        state += 1
        state > s.max && return nothing
        isassigned(s.list, state) && return s.list[state]::S, state
    end
end
```
-/
def iterate (calls : Callees) (address : Word) (state : JInt .i64 := JInt.wrap .i64 0) :
    M (Option (Word × JInt .i64)) := do
  let state := state+JInt.wrap .i64 1
  let current ← fields address
  if state.val > current.maximum.val then return none
  if ← isAssigned current.list state then
    let value ← D.memoryAt current.list state
    let value ← assertElement calls value current.elementType
    pure (some (value, state))
  else iterate calls address state
partial_fixpoint

end JuliaLean.base.idset

namespace JuliaLean.BitSetsCov.Bugs

structure IdValue where
  identity : Nat
  value : Nat
  deriving DecidableEq

end JuliaLean.BitSetsCov.Bugs

namespace JuliaLean.BitSetsCov.Coll

open Bugs

/-! ## `base/idset.jl` -/

abbrev IdState := List IdValue

def idFind (identity : Nat) (s : IdState) : Option IdValue := s.find? (fun x => x.identity = identity)
def idErase (identity : Nat) (s : IdState) : IdState := s.filter (fun x => x.identity != identity)
def idPush (s : IdState) (x : IdValue) : IdState := idErase x.identity s ++ [x]
def idOfList (xs : IdState) : IdState := xs.foldl idPush []
def idEmpty : IdState := []
def idCopy (s : IdState) : IdState := s
def idHasKey (s : IdState) (x : IdValue) : Bool := decide (idFind x.identity s).isSome
def idIsEmpty (s : IdState) : Bool := s.isEmpty
def idPopInternal (s : IdState) (x : IdValue) : Int × IdState :=
  if idHasKey s x then (0, idErase x.identity s) else (-1, s)
def idPopKey (s : IdState) (x : IdValue) : Option (IdValue × IdState) :=
  if idHasKey s x then some (x, idErase x.identity s) else none
def idPopDefault (s : IdState) (x default : IdValue) : IdValue × IdState :=
  if idHasKey s x then (x, idErase x.identity s) else (default, s)
def idZero (a : List Nat) : List Nat := List.replicate a.length 0
def idFilter (f : IdValue → Bool) (s : IdState) : IdState := s.filter f

end JuliaLean.BitSetsCov.Coll
/-!
# `IdSet`, base/idset.jl (master `bbfa0ce4150`)

`s.list::Memory{Any}` is modelled slot by slot (`none` = `#undef`), because
the Julia code reads and writes it directly (`s.list[idx + 1] = x`,
`isassigned`, the `s.max` scan, `iterate`). The hash index `s.idxs` is only
touched by the C functions `jl_idset_peek_bp`, `jl_idset_put_idx` and
`jl_idset_pop` (src/idset.c), modelled as a primitive with `===` semantics:
`peek` returns the slot holding a `===` element, `put_idx` has no state of
its own in the model. `jl_idset_put_key` (src/idset.c:83-108) is mirrored:
stable compaction of the keys when the list is full, growth by 50% when less
than a third is free afterwards, then the new key at the first free slot.

Modelling decisions:
* The `newidx` result of `jl_idset_put_key` only feeds `jl_idset_put_idx`,
  i.e. the abstract index; it is not modelled.
* `count` and `max` are `Nat` (indices of an in-memory list cannot wrap).
* 1.13.2 differs only in how `push!` learns the new `max`
  (`s.max = idx < 0 ? -idx : idx + 1`, base/idset.jl:62 in 1.13.2), which
  computes the same value.
-/

namespace JuliaLean.IdDicts

/-- `IdSet{T}` fields, base/idset.jl:29-36. -/
structure IdSet where
  T : JTy
  list : List (Option JVal)
  count : Nat
  max : Nat

/-- `IdSet{T}()`, base/idset.jl:34. -/
def IdSet.new (T : JTy) : IdSet := ⟨T, [], 0, 0⟩

/-- `jl_idset_peek_bp(list, idxs, x)`, src/idset.c:36-40: the 0-based slot of
the element `=== x`, or `-1` (`none`). -/
def peek : List (Option JVal) → JVal → Option Nat
  | [], _ => none
  | o :: t, x => if o = some x then some 0 else (peek t x).map (· + 1)

/-- The compaction loop `idset_compact`, src/idset.c:51-68: the assigned slots
moved to the front in order. -/
def compact (l : List (Option JVal)) : List (Option JVal) :=
  (l.filterMap id).map some ++ List.replicate (l.length - (l.filterMap id).length) none

/-- `jl_idset_put_key(keys, key, &max, &newidx)`, src/idset.c:83-108: the new
keys array and the new `max`. -/
def putKey (keys : List (Option JVal)) (key : JVal) (max : Nat) : List (Option JVal) × Nat :=
  let l := keys.length
  let (keys, i) :=
    if max = l then
      let keys := compact keys
      let i := (keys.filterMap id).length
      if i ≥ l / 3 * 2 then
        let nl := if l < 4 then 4 else (l * 3) / 2
        (keys.take i ++ List.replicate (nl - i) none, i)
      else (keys, i)
    else (keys, max)
  (keys.set i (some key), i + 1)

/-- `push!(s, x)`, base/idset.jl:48-70. -/
def IdSet.push (s : IdSet) (x : JVal) : Out IdSet Unit :=
  match peek s.list x with
  | some idx => ({ s with list := s.list.set idx (some x) }, .ok ())
  | none =>
    let r : Except IErr (List (Option JVal) × Nat) :=
      if s.max < s.list.length then
        -- `@assert !isassigned(s.list, idx + 1)`
        if (s.list[s.max]?).join.isSome then .error .assertionError
        else .ok (s.list.set s.max (some x), s.max + 1)
      else .ok (putKey s.list x s.max)
    match r with
    | .error e => (s, .error e)
    | .ok (list, max) =>
      let s := { s with list := list, max := max }
      -- `@assert s.list[s.max] === x`
      if (s.list[s.max - 1]?).join != some x then (s, .error .assertionError)
      else ({ s with count := s.count + 1 }, .ok ())

/-- `while s.max > 0 && !isassigned(s.list, s.max); s.max -= 1; end`,
base/idset.jl:75-77. -/
def shrinkMax (l : List (Option JVal)) : Nat → Nat
  | 0 => 0
  | m + 1 => if (l[m]?).join.isNone then shrinkMax l m else m + 1

/-- `_pop!(s, x)`, base/idset.jl:71-80; `jl_idset_pop` (src/idset.c:132-139)
unsets the slot. Returns whether `x` was removed. -/
def IdSet.pop! (s : IdSet) (x : JVal) : IdSet × Bool :=
  match peek s.list x with
  | none => (s, false)
  | some idx =>
    let l := s.list.set idx none
    ({ s with list := l, count := s.count - 1, max := shrinkMax l s.max }, true)

/-- `pop!(s, x)`, base/idset.jl:81. -/
def IdSet.pop (s : IdSet) (x : JVal) : Out IdSet JVal :=
  let r := s.pop! x
  (r.1, if r.2 then .ok x else .error .keyError)

/-- `delete!(s, x)`, base/idset.jl:83. -/
def IdSet.delete (s : IdSet) (x : JVal) : IdSet := (s.pop! x).1

/-- `for i = 1:m; unsetindex!(list, i); end` -/
def unsetPrefix (l : List (Option JVal)) (m : Nat) : List (Option JVal) :=
  List.replicate (min m l.length) none ++ l.drop m

/-- `empty!(s)`, base/idset.jl:108-117 (`_zero!(s.idxs)` clears the index). -/
def IdSet.empty (s : IdSet) : IdSet :=
  { s with list := unsetPrefix s.list s.max, count := 0, max := 0 }

/-- The slots `iterate` visits, base/idset.jl:121-126: `1:s.max`, assigned
ones only, in order. -/
def IdSet.elems (s : IdSet) : List JVal := (s.list.take s.max).filterMap id

/-- `iterate(s)` to exhaustion, with the `s.list[state]::S` cast. -/
def IdSet.iterate (s : IdSet) : Except IErr (List JVal) := s.elems.mapM (cast' s.T)
where cast' (T : JTy) (x : JVal) : Except IErr JVal := if isa x T then .ok x else .error .typeError

/-- `in(x, s)`, base/idset.jl:44,47. -/
def IdSet.mem (s : IdSet) (x : JVal) : Bool := (peek s.list x).isSome

/-- `length(s) = s.count`, base/idset.jl:46. -/
def IdSet.length (s : IdSet) : Nat := s.count

/-- `IdSet{T}(itr) = union!(IdSet{T}(), itr)`, base/idset.jl:37. -/
def IdSet.ofList (union : IdSet → List JVal → Out IdSet Unit) (T : JTy) (xs : List JVal) : IdSet :=
  (union (IdSet.new T) xs).1
end JuliaLean.IdDicts

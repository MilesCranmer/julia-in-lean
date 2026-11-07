import JuliaLean.src.iddict_c

/-! Native 64-bit smallintset.c operations used by idset.c. Integer cells use
the same byte heap as object pointers. Hash/equality parameters are the C
function pointers, bound to idset_hash/idset_eq by the IdSet mirror. -/
namespace JuliaLean.src.smallintset_c
open JuliaLean
open JuliaLean.src.identity_runtime

structure Primitives where
  uint8Type : Word
  uint16Type : Word
  uint32Type : Word
  anyMemoryType : Word
  empty8 : Memory
  empty16 : Memory
  empty32 : Memory
  allocateBits : Word → Nat → Nat → M Memory

abbrev Hash := Word → Word → M Word
abbrev Equal := Word → Word → Word → Word → M Bool

def elementWidth (p : Primitives) (memory : Memory) (allowAny : Bool) : M Nat := do
  let tag ← typetag (memoryOwner memory)
  if tag == p.uint8Type then pure 1
  else if tag == p.uint16Type then pure 2
  else if tag == p.uint32Type then pure 4
  else if allowAny && tag == p.anyMemoryType then pure 0
  else fail (.abort "smallintset unsupported GenericMemory type")

/-- C memset's byte effect on a valid nonwrapping destination range. -/
def zeroBytes (address size : Word) : M Unit := do
  requireReadable address size.toNat
  modifyWorld fun world =>
    let heap := world.raw.heap
    { world with
      raw := { world.raw with
        heap := { heap with
          byteAt := fun query =>
            if address.toNat ≤ query && query < address.toNat+size.toNat
            then JInt.wrap .u8 0 else heap.byteAt query } }
      events := world.events ++ [.memset address size] }

/-- C memcpy reads its original source bytes and requires disjoint ranges.
Both idset callers copy into a newly allocated memory. -/
def copyBytes (destination source size : Word) : M Unit := do
  requireReadable destination size.toNat
  requireReadable source size.toNat
  if size != 0 && !(destination.toNat+size.toNat ≤ source.toNat ||
      source.toNat+size.toNat ≤ destination.toNat) then
    fail (.undefinedBehavior "overlapping memcpy" destination)
  modifyWorld fun world =>
    let heap := world.raw.heap
    { world with
      raw := { world.raw with
        heap := { heap with
          byteAt := fun query =>
            if destination.toNat ≤ query && query < destination.toNat+size.toNat
            then heap.readByte (source.toNat+query-destination.toNat) else heap.byteAt query } }
      events := world.events ++ [.memcpy destination source size] }

def readInteger (memory : Memory) (index : Word) (width : Nat)
    (order : JuliaLean.base.genericmemory.MemoryOrder) : M Word := do
  let address := UInt64.ofNat memory.ptr + UInt64.ofNat width*index
  if index.toNat ≥ memory.length then fail (.undefinedBehavior "smallintset integer indexing" address)
  requireReadable address width
  let heap := (← getWorld).raw.heap
  let mut value : Word := 0
  for byte in [0:width] do
    value := value ||| (UInt64.ofNat (heap.readByte (address.toNat+byte)).val.toNat <<< UInt64.ofNat (8*byte))
  modifyWorld fun world => { world with events := world.events ++ [.atomicIntegerLoad address value width order] }
  pure value

def writeInteger (memory : Memory) (index value : Word) (width : Nat) : M Unit := do
  let address := UInt64.ofNat memory.ptr + UInt64.ofNat width*index
  if index.toNat ≥ memory.length then fail (.undefinedBehavior "smallintset integer indexing" address)
  requireReadable address width
  let mask := ((1 : Word) <<< UInt64.ofNat (8*width))-1
  let value := value &&& mask
  let bytes := (encodeWord value).take width
  modifyWorld fun world => { world with
    raw := { world.raw with heap := world.raw.heap.writeBytes address.toNat bytes }
    events := world.events ++ [.atomicIntegerStore address value width .release] }

def readAtomicLocal (index : Nat) : M Memory := do
  let memory ← readLocal index
  modifyWorld fun world => { world with events := world.events ++ [.localAtomicLoad index (memoryOwner memory)] }
  pure memory

def writeAtomicLocal (parent : Word) (index : Nat) (memory : Memory) : M Unit := do
  if parent != 0 then
    let old ← readLocal index
    modifyWorld fun world => { world with
      events := world.events ++ [.localWriteBarrier parent index (memoryOwner old) (memoryOwner memory)] }
  writeLocal index memory
  modifyWorld fun world => { world with events := world.events ++ [.localAtomicStore index (memoryOwner memory)] }

-- Source: src/smallintset.c:27-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline size_t ignore_tombstone(size_t val, size_t tombstone) JL_NOTSAFEPOINT
-- {
--     return val == tombstone ? 0 : val;
-- }
-- static inline size_t jl_intref(const jl_genericmemory_t *arr, size_t idx) JL_NOTSAFEPOINT
-- {
--     jl_value_t *el = (jl_value_t*)jl_typetagof(arr);
--     if (el == jl_memory_uint8_type)
--         return ignore_tombstone(jl_atomic_load_relaxed(&((_Atomic(uint8_t)*)arr->ptr)[idx]), (uint8_t)-1);
--     else if (el == jl_memory_uint16_type)
--         return ignore_tombstone(jl_atomic_load_relaxed(&((_Atomic(uint16_t)*)arr->ptr)[idx]), (uint16_t)-1);
--     else if (el == jl_memory_uint32_type)
--         return ignore_tombstone(jl_atomic_load_relaxed(&((_Atomic(uint32_t)*)arr->ptr)[idx]), UINT32_MAX);
--     else
--         abort();
-- }
-- /Source
def ignore_tombstone (value tombstone : Word) : Word := if value == tombstone then 0 else value

def jl_intref (p : Primitives) (memory : Memory) (index : Word) : M Word := do
  let width ← elementWidth p memory false
  let value ← readInteger memory index width .monotonic
  pure (ignore_tombstone value (((1 : Word) <<< UInt64.ofNat (8*width))-1))

-- Source: src/smallintset.c:44-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline size_t acquire_tombstone(size_t val, size_t tombstone) JL_NOTSAFEPOINT
-- {
--     return val == tombstone ? (size_t)-1 : val;
-- }
-- static inline size_t jl_intref_acquire(const jl_genericmemory_t *arr, size_t idx) JL_NOTSAFEPOINT
-- {
--     jl_value_t *el = (jl_value_t*)jl_typetagof(arr);
--     if (el == jl_memory_uint8_type)
--         return acquire_tombstone(jl_atomic_load_acquire(&((_Atomic(uint8_t)*)arr->ptr)[idx]), (uint8_t)-1);
--     else if (el == jl_memory_uint16_type)
--         return acquire_tombstone(jl_atomic_load_acquire(&((_Atomic(uint16_t)*)arr->ptr)[idx]), (uint16_t)-1);
--     else if (el == jl_memory_uint32_type)
--         return acquire_tombstone(jl_atomic_load_acquire(&((_Atomic(uint32_t)*)arr->ptr)[idx]), UINT32_MAX);
--     else
--         abort();
-- }
-- /Source
def acquire_tombstone (value tombstone : Word) : Word :=
  if value == tombstone then ~~~(0 : Word) else value

def jl_intref_acquire (p : Primitives) (memory : Memory) (index : Word) : M Word := do
  let width ← elementWidth p memory false
  let value ← readInteger memory index width .acquire
  pure (acquire_tombstone value (((1 : Word) <<< UInt64.ofNat (8*width))-1))

-- Source: src/smallintset.c:61-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline void jl_intset_release(const jl_genericmemory_t *arr, size_t idx, size_t val) JL_NOTSAFEPOINT
-- {
--     jl_value_t *el = (jl_value_t*)jl_typetagof(arr);
--     if (el == jl_memory_uint8_type)
--         jl_atomic_store_release(&((_Atomic(uint8_t)*)arr->ptr)[idx], val);
--     else if (el == jl_memory_uint16_type)
--         jl_atomic_store_release(&((_Atomic(uint16_t)*)arr->ptr)[idx], val);
--     else if (el == jl_memory_uint32_type)
--         jl_atomic_store_release(&((_Atomic(uint32_t)*)arr->ptr)[idx], val);
--     else
--         abort();
-- }
-- /Source
def jl_intset_release (p : Primitives) (memory : Memory) (index value : Word) : M Unit := do
  writeInteger memory index value (← elementWidth p memory false)

-- Source: src/smallintset.c:74-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline size_t jl_max_int(const jl_genericmemory_t *arr) JL_NOTSAFEPOINT
-- {
--     jl_value_t *el = (jl_value_t*)jl_typetagof(arr);
--     if (el == jl_memory_uint8_type)
--         return 0xFF;
--     else if (el == jl_memory_uint16_type)
--         return 0xFFFF;
--     else if (el == jl_memory_uint32_type)
--         return 0xFFFFFFFF;
--     else if (el == jl_memory_any_type)
--         return 0;
--     else
--         abort();
-- }
-- /Source
def jl_max_int (p : Primitives) (memory : Memory) : M Word := do
  let width ← elementWidth p memory true
  if width = 0 then pure 0 else pure (((1 : Word) <<< UInt64.ofNat (8*width))-1)

-- Source: src/smallintset.c:89-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- void smallintset_empty(const jl_genericmemory_t *a) JL_NOTSAFEPOINT
-- {
--     size_t elsize;
--     jl_value_t *el = (jl_value_t*)jl_typetagof(a);
--     if (el == jl_memory_uint8_type)
--         elsize = sizeof(uint8_t);
--     else if (el == jl_memory_uint16_type)
--         elsize = sizeof(uint16_t);
--     else if (el == jl_memory_uint32_type)
--         elsize = sizeof(uint32_t);
--     else if (el == jl_memory_any_type)
--         elsize = 0;
--     else
--         abort();
--     memset(a->ptr, 0, a->length * elsize);
-- }
-- /Source
def smallintset_empty (p : Primitives) (memory : Memory) : M Unit := do
  let width ← elementWidth p memory true
  zeroBytes (UInt64.ofNat memory.ptr) (UInt64.ofNat memory.length * UInt64.ofNat width)

-- Source: src/smallintset.c:106-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static jl_genericmemory_t *jl_alloc_int_1d(size_t np, size_t len) JL_CANSAFEPOINT
-- {
--     jl_value_t *ty;
--     if (np < 0xFF)
--         ty = jl_memory_uint8_type;
--     else if (np < 0xFFFF)
--         ty = jl_memory_uint16_type;
--     else
--         ty = jl_memory_uint32_type;
--     assert(np < 0x7FFFFFFF);
--     jl_genericmemory_t *a = jl_alloc_genericmemory(ty, len);
--     smallintset_empty(a);
--     return a;
-- }
-- /Source
def jl_alloc_int_1d (p : Primitives) (np length : Word) : M Memory := do
  let (type, width, empty) := if np < 0xff then (p.uint8Type, 1, p.empty8)
    else if np < 0xffff then (p.uint16Type, 2, p.empty16)
    else (p.uint32Type, 4, p.empty32)
  if np ≥ 0x7fffffff then fail (.abort "np < 0x7FFFFFFF")
  let memory ← JuliaLean.base.array.allocGenericMemory (some ⟨width, false, false⟩)
    (pure empty) (p.allocateBits type width) length.toNat
  let owner := memoryOwner memory
  modifyWorld fun world => { world with
    memories := fun address => if address == owner then some memory else world.memories address }
  smallintset_empty p memory
  pure memory

def lookupLoop (p : Primitives) (cache : Memory) (eq : Equal) (key data hash : Word)
    (pop : Bool) (size maxprobe origin index iter : Word) : M Word := do
  let value ← jl_intref_acquire p cache index
  if value == 0 then
    popRoots
    return ~~~(0 : Word)
  if value != ~~~(0 : Word) then
    if ← eq (value-1) key data hash then
      popRoots
      if pop then jl_intset_release p cache index (~~~(0 : Word))
      return value-1
  let next := (index+1) &&& (size-1)
  let iter := iter+1
  if iter ≤ maxprobe && next != origin then
    lookupLoop p cache eq key data hash pop size maxprobe origin next iter
  else
    popRoots
    pure (~~~(0 : Word))
partial_fixpoint

-- Source: src/smallintset.c:121-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ssize_t jl_smallintset_lookup(jl_genericmemory_t *cache, smallintset_eq eq, const void *key, jl_value_t *data, uint_t hv, int pop)
-- {
--     size_t sz = cache->length;
--     if (sz == 0)
--         return -1;
--     JL_GC_PUSH1(&cache);
--     size_t maxprobe = max_probe(sz);
--     size_t index = h2index(hv, sz);
--     size_t orig = index;
--     size_t iter = 0;
--     do {
--         size_t val1 = jl_intref_acquire(cache, index);
--         if (val1 == 0) {
--             JL_GC_POP();
--             return -1;
--         }
--         if (val1 != -1 && eq(val1 - 1, key, data, hv)) {
--             JL_GC_POP();
--             if (pop)
--                 jl_intset_release(cache, index, (size_t)-1); // replace with tombstone
--             return val1 - 1;
--         }
--         index = (index + 1) & (sz - 1);
--         iter++;
--     } while (iter <= maxprobe && index != orig);
--     JL_GC_POP();
--     return -1;
-- }
-- /Source
def jl_smallintset_lookup (p : Primitives) (cache : Memory) (eq : Equal)
    (key data hash : Word) (pop : Bool) : M Word := do
  let size := UInt64.ofNat cache.length
  if size == 0 then return ~~~(0 : Word)
  let root ← newLocal (some cache)
  pushRoots [root]
  let index := hash &&& (size-1)
  lookupLoop p cache eq key data hash pop size (JuliaLean.src.iddict_c.max_probe size) index index 0

def insertLoop (p : Primitives) (memory : Memory) (value size maxprobe origin index iter : Word) : M Bool := do
  if (← jl_intref p memory index) == 0 then
    jl_intset_release p memory index value
    return true
  let next := (index+1) &&& (size-1)
  let iter := iter+1
  if iter ≤ maxprobe && next != origin then insertLoop p memory value size maxprobe origin next iter
  else pure false
partial_fixpoint

-- Source: src/smallintset.c:150-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static int smallintset_insert_(jl_genericmemory_t *a, uint_t hv, size_t val1) JL_NOTSAFEPOINT
-- {
--     size_t sz = a->length;
--     if (sz <= 1)
--         return 0;
--     size_t orig, index, iter;
--     iter = 0;
--     index = h2index(hv, sz);
--     orig = index;
--     size_t maxprobe = max_probe(sz);
--     do {
--         if (jl_intref(a, index) == 0) {
--             jl_intset_release(a, index, val1);
--             return 1;
--         }
--         index = (index + 1) & (sz - 1);
--         iter++;
--     } while (iter <= maxprobe && index != orig);
--     return 0;
-- }
-- /Source
def smallintset_insert_ (p : Primitives) (memory : Memory) (hash value : Word) : M Bool := do
  let size := UInt64.ofNat memory.length
  if size ≤ 1 then return false
  let index := hash &&& (size-1)
  insertLoop p memory value size (JuliaLean.src.iddict_c.max_probe size) index index 0

def maximumIndex (p : Primitives) (memory : Memory) (size index maximum : Word) : M Word := do
  if index ≥ size then return maximum
  let value ← jl_intref p memory index
  maximumIndex p memory size (index+1) (if value > maximum then value else maximum)
partial_fixpoint

def reinsertLoop (p : Primitives) (old fresh : Memory) (hash : Hash) (data size index : Word) : M Bool := do
  if index ≥ size then return true
  let value ← jl_intref p old index
  if value != 0 then
    if !(← smallintset_insert_ p fresh (← hash (value-1) data) value) then return false
  reinsertLoop p old fresh hash data size (index+1)
partial_fixpoint

def rehashRetry (p : Primitives) (memory : Memory) (hash : Hash) (data size newsz np : Word) : M Memory := do
  let fresh ← jl_alloc_int_1d p (np+1) newsz
  let root ← newLocal (some fresh)
  pushRoots [root]
  let complete ← reinsertLoop p memory fresh hash data size 0
  popRoots
  if complete then pure fresh else rehashRetry p memory hash data size (newsz <<< 1) np
partial_fixpoint

-- Source: src/smallintset.c:249-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_genericmemory_t* smallintset_rehash(jl_genericmemory_t* a, smallintset_hash hash, jl_value_t *data, size_t newsz, size_t np)
-- {
--     size_t sz = a->length;
--     size_t i;
--     for (i = 0; i < sz; i += 1) {
--         size_t val = jl_intref(a, i);
--         if (val > np)
--             np = val;
--     }
--     while (1) {
--         jl_genericmemory_t *newa = jl_alloc_int_1d(np + 1, newsz);
--         JL_GC_PUSH1(&newa);
--         for (i = 0; i < sz; i += 1) {
--             size_t val1 = jl_intref(a, i);
--             if (val1 != 0) {
--                 if (!smallintset_insert_(newa, hash(val1 - 1, data), val1)) {
--                     break;
--                 }
--             }
--         }
--         JL_GC_POP();
--         if (i == sz)
--             return newa;
--         newsz <<= 1;
--     }
-- }
-- /Source
def smallintset_rehash (p : Primitives) (memory : Memory) (hash : Hash)
    (data newsz np : Word) : M Memory := do
  let size := UInt64.ofNat memory.length
  let np ← maximumIndex p memory size 0 np
  rehashRetry p memory hash data size newsz np

def insertRetry (p : Primitives) (pcache : Nat) (parent : Word) (memory : Memory)
    (hash : Hash) (value data : Word) : M Unit := do
  if ← smallintset_insert_ p memory (← hash value data) (value+1) then return ()
  let memory ← readAtomicLocal pcache
  let size := UInt64.ofNat memory.length
  let newsz : Word := if size < 32 then 32
    else if size ≥ ((1 : Word) <<< 19) || size ≤ ((1 : Word) <<< 8) then size <<< 1
    else size <<< 2
  let memory ← smallintset_rehash p memory hash data newsz 0
  writeAtomicLocal parent pcache memory
  insertRetry p pcache parent memory hash value data
partial_fixpoint

-- Source: src/smallintset.c:172-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- void jl_smallintset_insert(_Atomic(jl_genericmemory_t*) *pcache, jl_value_t *parent, smallintset_hash hash, size_t val, jl_value_t *data)
-- {
--     jl_genericmemory_t *a = jl_atomic_load_relaxed(pcache);
--     if (val + 1 >= jl_max_int(a)) {
--         a = smallintset_rehash(a, hash, data, a->length, val + 1);
--         if (parent) jl_gc_wb(parent, (void*)pcache, a);
--         jl_atomic_store_release(pcache, a);
--     }
--     while (1) {
--         if (smallintset_insert_(a, hash(val, data), val + 1))
--             return;
-- 
--         /* table full */
--         /* rehash to grow and retry the insert */
--         /* it's important to grow the table really fast; otherwise we waste */
--         /* lots of time rehashing all the keys over and over. */
--         size_t newsz;
--         a = jl_atomic_load_relaxed(pcache);
--         size_t sz = a->length;
--         if (sz < HT_N_INLINE)
--             newsz = HT_N_INLINE;
--         else if (sz >= (1 << 19) || (sz <= (1 << 8)))
--             newsz = sz << 1;
--         else
--             newsz = sz << 2;
--         a = smallintset_rehash(a, hash, data, newsz, 0);
--         if (parent) jl_gc_wb(parent, (void*)pcache, a);
--         jl_atomic_store_release(pcache, a);
--     }
-- }
-- /Source
def jl_smallintset_insert (p : Primitives) (pcache : Nat) (parent : Word)
    (hash : Hash) (value data : Word) : M Unit := do
  let memory ← readAtomicLocal pcache
  let memory ← if value+1 ≥ (← jl_max_int p memory) then do
      let fresh ← smallintset_rehash p memory hash data (UInt64.ofNat memory.length) (value+1)
      writeAtomicLocal parent pcache fresh
      pure fresh
    else pure memory
  insertRetry p pcache parent memory hash value data

end JuliaLean.src.smallintset_c

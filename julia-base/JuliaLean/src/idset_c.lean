import JuliaLean.src.smallintset_c

/-! Pinned idset.c over the shared GenericMemory heap. C out-parameters are
returned in their source meanings: (keys, newmax::size_t, newidx::ssize_t).
In particular newidx retains the negative full-rehash marker. -/
namespace JuliaLean.src.idset_c
open JuliaLean
open JuliaLean.src.identity_runtime
namespace S
export JuliaLean.src.smallintset_c (Primitives smallintset_rehash jl_smallintset_lookup
  jl_smallintset_insert smallintset_empty readAtomicLocal copyBytes)
end S
namespace B
export JuliaLean.src.builtins_identity_c (jl_object_id jl_egal_)
end B

def signed (word : Word) : JInt .i64 := JInt.wrap .i64 (Int.ofNat word.toNat)
def unsigned (value : JInt .i64) : Word := UInt64.ofNat (JuliaLean.base.int.remT .u64 value).val.toNat

def memoryAtAddress (address : Word) : M Memory := do
  match (← getWorld).memories address with
  | some memory => pure memory
  | none => fail (.undefinedBehavior "GenericMemory field view" address)

/-- src/julia.h:1541-1557. These helpers assert boxed layout and bounds. -/
def keyAt (memory : Memory) (index : Word) : M Word := do
  if !JuliaLean.src.genericmemory_c.isBoxed memory.metadata then fail (.abort "arrayelem_isboxed")
  if index.toNat ≥ memory.length then fail (.abort "i < m_->length")
  readCell memory index

def keySet (memory : Memory) (index value : Word) : M Unit := do
  if !JuliaLean.src.genericmemory_c.isBoxed memory.metadata then fail (.abort "arrayelem_isboxed")
  if index.toNat ≥ memory.length then fail (.abort "i < m_->length")
  writeCell memory index value .release

-- Source: src/support/dtypes.h:254-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- STATIC_INLINE unsigned int next_power_of_two(unsigned int val) JL_NOTSAFEPOINT
-- {
--     /* this function taken from libuv src/unix/core.c */
--     val -= 1;
--     val |= val >> 1;
--     val |= val >> 2;
--     val |= val >> 4;
--     val |= val >> 8;
--     val |= val >> 16;
--     val += 1;
--     return val;
-- }
-- /Source
def next_power_of_two (value : UInt32) : UInt32 := Id.run do
  let mut value := value-1
  value := value ||| (value >>> 1)
  value := value ||| (value >>> 2)
  value := value ||| (value >>> 4)
  value := value ||| (value >>> 8)
  value := value ||| (value >>> 16)
  return value+1

-- Source: src/idset.c:4-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static uint_t idset_hash(size_t idx, jl_value_t *data)
-- {
--     if (idx >= ((jl_genericmemory_t*)data)->length)
--         return 0; // We got a OOB access, probably due to a data race
--     jl_value_t *x = jl_genericmemory_ptr_ref(data, idx);
--     // x should not be NULL, unless there was concurrent corruption
--     return x == NULL ? 0 : jl_object_id(x);
-- }
-- /Source
def idset_hash (index data : Word) : M Word := do
  let keys ← memoryAtAddress data
  if index.toNat ≥ keys.length then return 0
  let value ← keyAt keys index
  if value == 0 then pure 0 else B.jl_object_id value

-- Source: src/idset.c:13-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static int idset_eq(size_t idx, const void *y, jl_value_t *data, uint_t hv)
-- {
--     if (idx >= ((jl_genericmemory_t*)data)->length)
--         return 0; // We got a OOB access, probably due to a data race
--     jl_value_t *x = jl_genericmemory_ptr_ref(data, idx);
--     // x should not be NULL, unless there was concurrent corruption
--     return x == NULL ? 0 : jl_egal(x, (jl_value_t*)y);
-- }
-- /Source
def idset_eq (index key data _hash : Word) : M Bool := do
  let keys ← memoryAtAddress data
  if index.toNat ≥ keys.length then return false
  let value ← keyAt keys index
  if value == 0 then pure false else B.jl_egal_ value key

-- Source: src/idset.c:22-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_genericmemory_t *jl_idset_rehash(jl_genericmemory_t *keys, jl_genericmemory_t *idxs, size_t newsz)
-- {
--     if (newsz == 0)
--         return idxs;
--     newsz = next_power_of_two(newsz);
--     //if (idxs->length == newsz)
--     //    jl_idset_put_idx(keys, idxs, -newsz+1);
--     //else
--     return smallintset_rehash(idxs, idset_hash, (jl_value_t*)keys, newsz, 0);
-- }
-- /Source
def jl_idset_rehash (p : S.Primitives) (keys indices : Memory) (newsz : Word) : M Memory := do
  if newsz == 0 then return indices
  let newsz := (next_power_of_two (UInt32.ofNat newsz.toNat)).toUInt64
  S.smallintset_rehash p indices idset_hash (memoryOwner keys) newsz 0

-- Source: src/idset.c:33-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- // Return idx if key is in hash, otherwise -1
-- // Note: lookup in the IdSet is permitted concurrently, if you avoid deletions,
-- // and assuming you do use an external lock around all insertions
-- ssize_t jl_idset_peek_bp(jl_genericmemory_t *keys, jl_genericmemory_t *idxs, jl_value_t *key) JL_NOTSAFEPOINT
-- {
--     uintptr_t hv = jl_object_id(key);
--     return jl_smallintset_lookup(idxs, idset_eq, key, (jl_value_t*)keys, hv, 0);
-- }
-- /Source
def jl_idset_peek_bp (p : S.Primitives) (keys indices : Memory) (key : Word) : M (JInt .i64) := do
  let hash ← B.jl_object_id key
  return signed (← S.jl_smallintset_lookup p indices idset_eq key (memoryOwner keys) hash false)

-- Source: src/idset.c:42-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_value_t *jl_idset_get(jl_genericmemory_t *keys, jl_genericmemory_t *idxs, jl_value_t *key) JL_NOTSAFEPOINT
-- {
--     ssize_t idx = jl_idset_peek_bp(keys, idxs, key);
--     if (idx == -1)
--         return NULL;
--     return jl_genericmemory_ptr_ref(keys, idx);
-- }
-- /Source
def jl_idset_get (p : S.Primitives) (keys indices : Memory) (key : Word) : M Word := do
  let index ← jl_idset_peek_bp p keys indices key
  if index.val == -1 then pure 0 else keyAt keys (unsigned index)

def compactLoop (keys : Memory) (index count : Word) (rehash : Bool) : M (Word × Bool) := do
  if index.toNat ≥ keys.length then return (count, rehash)
  let key ← keyAt keys index
  if key != 0 then
    if index != count then
      keySet keys count key
      keySet keys index 0
      compactLoop keys (index+1) (count+1) true
    else compactLoop keys (index+1) (count+1) rehash
  else compactLoop keys (index+1) count rehash
partial_fixpoint

-- Source: src/idset.c:51-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static ssize_t idset_compact(jl_genericmemory_t *keys)
-- {
--     // compact keys before rehashing idxs
--     ssize_t i, j;
--     ssize_t rehash = 0;
--     for (i = j = 0; i < keys->length; i++) {
--         jl_value_t *k = jl_genericmemory_ptr_ref(keys, i);
--         if (k != NULL) {
--             if (i != j) {
--                 rehash = 1;
--                 jl_genericmemory_ptr_set(keys, j, k);
--                 jl_genericmemory_ptr_set(keys, i, NULL);
--             }
--             j++;
--         }
--     }
--     return rehash ? -j : j;
-- }
-- /Source
def idset_compact (keys : Memory) : M (JInt .i64) := do
  let (count, rehash) ← compactLoop keys 0 0 false
  let count := signed count
  pure (if rehash then JInt.wrap .i64 (-count.val) else count)

def maxLoop (keys : Memory) (index : Word) : M Word := do
  if index == 0 then return 0
  if (← keyAt keys (index-1)) == 0 then maxLoop keys (index-1) else pure index
partial_fixpoint

-- Source: src/idset.c:70-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- // Return the slot just past the last key of `keys`, for callers of
-- // jl_idset_put_key that do not keep track of it themselves.
-- size_t jl_idset_max(jl_genericmemory_t *keys) JL_NOTSAFEPOINT
-- {
--     size_t i = keys->length;
--     while (i > 0 && jl_genericmemory_ptr_ref(keys, i - 1) == NULL)
--         i--;
--     return i;
-- }
-- /Source
def jl_idset_max (keys : Memory) : M Word := maxLoop keys (UInt64.ofNat keys.length)

-- Source: src/idset.c:80-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- // Insert `key` at the end of the ordered set `keys` (growing and compacting
-- // are insertion-order-preserving). `*max` is the slot just past the last key,
-- // which the caller keeps track of (or gets from jl_idset_max), and is updated.
-- jl_genericmemory_t *jl_idset_put_key(jl_genericmemory_t *keys, jl_value_t *key, size_t *max, ssize_t *newidx)
-- {
--     ssize_t l = keys->length;
--     ssize_t i = *max;
--     assert(i <= l && (i == 0 || jl_genericmemory_ptr_ref(keys, i - 1) != NULL));
--     // i points to the place to insert
--     *newidx = i;
--     if (i == l) {
--         i = idset_compact(keys);
--         if (i < 0) {
--             *newidx = i - 1;
--             i = -i;
--         }
--         if (i >= l / 3 * 2) {
--             size_t nl = l < 4 ? 4 : (l * 3) >> 1; // grow space by 50% if less than 33% free after compacting
--             jl_genericmemory_t *nk = jl_alloc_genericmemory(jl_memory_any_type, nl);
--             if (i > 0)
--                 memcpy(nk->ptr, keys->ptr, sizeof(void*) * i);
--             keys = nk;
--         }
--     }
--     assert(jl_genericmemory_ptr_ref(keys, i) == NULL);
--     jl_genericmemory_ptr_set(keys, i, key);
--     *max = i + 1;
--     return keys;
-- }
-- /Source
def jl_idset_put_key (gc : GC) (keys : Memory) (key maximum : Word) :
    M (Memory × Word × JInt .i64) := do
  let length := JInt.wrap .i64 (Int.ofNat keys.length)
  let mut index := signed maximum
  if index.val > length.val then fail (.abort "i <= l")
  if index.val != 0 then
    if (← keyAt keys (unsigned (index-JInt.wrap .i64 1))) == 0 then
      fail (.abort "i == 0 || keys[i-1] != NULL")
  let mut newidx := index
  let mut keys := keys
  if index.val == length.val then
    index ← idset_compact keys
    if index.val < 0 then
      newidx := index-JInt.wrap .i64 1
      index := JInt.wrap .i64 (-index.val)
    if index.val ≥ (length.val / 3)*2 then
      let newLength : Word := if length.val < 4 then 4
        else unsigned (JuliaLean.base.int.ashr_int (length*JInt.wrap .i64 3) (JInt.wrap .i64 1))
      let fresh ← allocMemoryAny gc newLength
      if index.val > 0 then
        S.copyBytes (UInt64.ofNat fresh.ptr) (UInt64.ofNat keys.ptr) (8*unsigned index)
      keys := fresh
  if (← keyAt keys (unsigned index)) != 0 then fail (.abort "keys[i] == NULL")
  keySet keys (unsigned index) key
  return (keys, unsigned (index+JInt.wrap .i64 1), newidx)

def putIndicesLoop (p : S.Primitives) (keys : Memory) (root : Nat) (limit index : Word) : M Unit := do
  if index ≥ limit then return ()
  if (← keyAt keys index) != 0 then
    S.jl_smallintset_insert p root 0 idset_hash index (memoryOwner keys)
  putIndicesLoop p keys root limit (index+1)
partial_fixpoint

-- Source: src/idset.c:110-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_genericmemory_t *jl_idset_put_idx(jl_genericmemory_t *keys, jl_genericmemory_t *idxs, ssize_t idx)
-- {
--     _Atomic(jl_genericmemory_t*) newidxs = idxs;
--     JL_GC_PUSH1(&newidxs);
--     if (idx < 0) { // full rehash
--         smallintset_empty(idxs);
--         for (ssize_t i = 0; i < -idx; i++)
--             if (jl_genericmemory_ptr_ref(keys, i) != NULL)
--                 jl_smallintset_insert(&newidxs, NULL, idset_hash, i, (jl_value_t*)keys);
--     }
--     else {
--         jl_smallintset_insert(&newidxs, NULL, idset_hash, idx, (jl_value_t*)keys);
--     }
--     JL_GC_POP();
--     return jl_atomic_load_relaxed(&newidxs);
-- }
-- /Source
def jl_idset_put_idx (p : S.Primitives) (keys indices : Memory) (index : JInt .i64) : M Memory := do
  let root ← newLocal (some indices)
  pushRoots [root]
  if index.val < 0 then
    if index.val == -(2^63) then fail (.undefinedBehavior "ssize_t negation overflow" 0)
    S.smallintset_empty p indices
    putIndicesLoop p keys root (UInt64.ofNat (-index.val).toNat) 0
  else S.jl_smallintset_insert p root 0 idset_hash (unsigned index) (memoryOwner keys)
  popRoots
  S.readAtomicLocal root

-- Source: src/idset.c:127-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- // Removal NULLs the key's slot in place, leaving an interior hole until a
-- // later insertion compacts the list. That breaks the packed-prefix guarantee
-- // of the ordered-set insertion, so this must not be used on sets whose
-- // consumers rely on that property for lock-free iteration (such as `Method.interferences`).
-- // Returns idx if key is in hash, otherwise -1.
-- ssize_t jl_idset_pop(jl_genericmemory_t *keys, jl_genericmemory_t *idxs, jl_value_t *key) JL_NOTSAFEPOINT
-- {
--     uintptr_t hv = jl_object_id(key);
--     ssize_t idx = jl_smallintset_lookup(idxs, idset_eq, key, (jl_value_t*)keys, hv, 1);
--     if (idx != -1)
--         jl_genericmemory_ptr_set(keys, idx, NULL);
--     return idx;
-- }
-- /Source
def jl_idset_pop (p : S.Primitives) (keys indices : Memory) (key : Word) : M (JInt .i64) := do
  let hash ← B.jl_object_id key
  let index := signed (← S.jl_smallintset_lookup p indices idset_eq key (memoryOwner keys) hash true)
  if index.val != -1 then keySet keys (unsigned index) 0
  pure index

end JuliaLean.src.idset_c

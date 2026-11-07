import JuliaLean.src.builtins_identity_c

/-! Native 64-bit mirrors of src/iddict.c. Table cells and values share the
installed GenericMemory byte heap. The two C out-parameters are returned
alongside the C result; a missing out-pointer produces none. -/
namespace JuliaLean.src.iddict_c
open JuliaLean.src.identity_runtime
open JuliaLean.src.builtins_identity_c

-- Source: src/iddict.c:3-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #define hash_size(h) (h->length / 2)
-- 
-- // compute empirical max-probe for a given size
-- #define max_probe(size) ((size) <= 1024 ? 16 : (size) >> 6)
-- 
-- #define keyhash(k) jl_object_id_(jl_typetagof(k), k)
-- #define h2index(hv, sz) (size_t)(((hv) & ((sz)-1)) * 2)
-- /Source
def hash_size (memory : Memory) : Word := UInt64.ofNat memory.length / 2
def max_probe (size : Word) : Word := if size ≤ 1024 then 16 else size >>> 6
def h2index (hash size : Word) : Word := (hash &&& (size-1))*2
def keyhash (key : Word) : M Word := do jl_object_id_ (← typetag key) key

/-- src/support/htable.h:6. -/
def inlineSize : Word := 32

inductive Probe where
  | existing (index : Word)
  | vacant (index : Word)
  | full

def assignProbe (memory : Memory) (key size maxprobe origin index iter empty : Word) : M Probe := do
  let k2 ← readCell memory index
  if k2 == 0 then return .vacant (if empty == ~~~(0 : Word) then index else empty)
  let mut empty := empty
  if ← jl_egal_ key k2 then
    if (← readCell memory (index+1)) != 0 then return .existing index
    if key != (← getWorld).globals.nothing then fail (.abort "key == jl_nothing")
    if empty == ~~~(0 : Word) then empty := index
  if empty == ~~~(0 : Word) then
    if (← readCell memory (index+1)) == 0 then
      if (← readCell memory index) != (← getWorld).globals.nothing then
        fail (.abort "tab[index] == jl_nothing")
      empty := index
  let next := (index+2) &&& (size-1)
  let iter := iter+1
  if iter ≤ maxprobe && next != origin then
    assignProbe memory key size maxprobe origin next iter empty
  else if empty != ~~~(0 : Word) then pure (.vacant empty)
  else pure .full
partial_fixpoint

mutual
-- Source: src/iddict.c:13-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_genericmemory_t *jl_idtable_rehash(jl_genericmemory_t *a, size_t newsz)
-- {
--     size_t sz = a->length;
--     size_t i;
--     jl_value_t **ol = (jl_value_t **) a->ptr;
--     jl_genericmemory_t *newa = NULL;
--     // keep the original memory in the original slot since we need `ol`
--     // to be valid in the loop below.
--     JL_GC_PUSH2(&newa, &a);
--     newa = jl_alloc_memory_any(newsz);
--     for (i = 0; i < sz; i += 2) {
--         if (ol[i + 1] != NULL) {
--             jl_table_assign_bp(&newa, ol[i], ol[i + 1]);
--         }
--     }
--     JL_GC_POP();
--     return newa;
-- }
-- /Source
  def jl_idtable_rehash (gc : GC) (memory : Memory) (newsz : Word) : M Memory := do
    let newRef ← newLocal none
    let oldRef ← newLocal (some memory)
    pushRoots [newRef, oldRef]
    writeLocal newRef (← allocMemoryAny gc newsz)
    rehashLoop gc memory newRef (UInt64.ofNat memory.length) 0
    popRoots
    readLocal newRef
  partial_fixpoint

  def rehashLoop (gc : GC) (old : Memory) (newRef : Nat) (size index : Word) : M Unit := do
    if index < size then
      let value ← plainReadCell old (index+1)
      if value != 0 then
        let key ← plainReadCell old index
        let _ ← jl_table_assign_bp gc newRef key value
      rehashLoop gc old newRef size (index+2)
    else pure ()
  partial_fixpoint

-- Source: src/iddict.c:32-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline int jl_table_assign_bp(jl_genericmemory_t **pa, jl_value_t *key, jl_value_t *val)
-- {
--     // pa points to a **un**rooted address
--     uint_t hv;
--     jl_genericmemory_t *a = *pa;
--     size_t orig, index, iter, empty_slot;
--     size_t newsz, sz = hash_size(a);
--     if (sz == 0) {
--         a = jl_alloc_memory_any(HT_N_INLINE);
--         sz = hash_size(a);
--         *pa = a;
--     }
--     size_t maxprobe = max_probe(sz);
--     _Atomic(jl_value_t*) *tab = (_Atomic(jl_value_t*)*) a->ptr;
-- 
--     hv = keyhash(key);
--     while (1) {
--         iter = 0;
--         index = h2index(hv, sz);
--         sz *= 2;
--         orig = index;
--         empty_slot = -1;
-- 
--         do {
--             jl_value_t *k2 = jl_atomic_load_relaxed(&tab[index]);
--             if (k2 == NULL) {
--                 if (empty_slot == -1)
--                     empty_slot = index;
--                 break;
--             }
--             if (jl_egal(key, k2)) {
--                 if (jl_atomic_load_relaxed(&tab[index + 1]) != NULL) {
--                     jl_gc_write_atomic(a, tab[index + 1], jl_value_t, val, release);
--                     return 0;
--                 }
--                 // `nothing` is our sentinel value for deletion, so need to keep searching if it's also our search key
--                 assert(key == jl_nothing);
--                 if (empty_slot == -1)
--                     empty_slot = index;
--             }
--             if (empty_slot == -1 && jl_atomic_load_relaxed(&tab[index + 1]) == NULL) {
--                 assert(jl_atomic_load_relaxed(&tab[index]) == jl_nothing);
--                 empty_slot = index;
--             }
-- 
--             index = (index + 2) & (sz - 1);
--             iter++;
--         } while (iter <= maxprobe && index != orig);
-- 
--         if (empty_slot != -1) {
--             jl_gc_write_atomic(a, tab[empty_slot], jl_value_t, key, release);
--             jl_gc_write_atomic(a, tab[empty_slot + 1], jl_value_t, val, release);
--             return 1;
--         }
-- 
--         /* table full */
--         /* grow size, rehash, retry the insert */
--         /* it's important to grow the table really fast; otherwise we waste */
--         /* lots of time rehashing all the keys over and over. */
--         sz = a -> length;
--         if (sz < HT_N_INLINE)
--             newsz = HT_N_INLINE;
--         else if (sz >= (1 << 19) || (sz <= (1 << 8)))
--             newsz = sz << 1;
--         else
--             newsz = sz << 2;
--         *pa = jl_idtable_rehash(*pa, newsz);
-- 
--         a = *pa;
--         tab =  (_Atomic(jl_value_t*)*) a->ptr;
--         sz = hash_size(a);
--         maxprobe = max_probe(sz);
--     }
-- }
-- /Source
  def jl_table_assign_bp (gc : GC) (pa : Nat) (key value : Word) : M Bool := do
    let mut memory ← readLocal pa
    if hash_size memory == 0 then
      memory ← allocMemoryAny gc inlineSize
      writeLocal pa memory
    let hash ← keyhash key
    assignOuter gc pa memory key value hash
  partial_fixpoint

  def assignOuter (gc : GC) (pa : Nat) (memory : Memory) (key value hash : Word) : M Bool := do
    let size := hash_size memory
    let index := h2index hash size
    match ← assignProbe memory key (size*2) (max_probe size) index index 0 (~~~(0 : Word)) with
    | .existing index =>
      writeCell memory (index+1) value .release
      pure false
    | .vacant index =>
      writeCell memory index key .release
      writeCell memory (index+1) value .release
      pure true
    | .full =>
      let size := UInt64.ofNat memory.length
      let newsz := if size < inlineSize then inlineSize
        else if size ≥ ((1 : Word) <<< 19) || size ≤ ((1 : Word) <<< 8) then size <<< 1
        else size <<< 2
      let grown ← jl_idtable_rehash gc (← readLocal pa) newsz
      writeLocal pa grown
      assignOuter gc pa grown key value hash
  partial_fixpoint
end

def peekLoop (memory : Memory) (key size maxprobe origin index iter : Word) : M Word := do
  let k2 ← readCell memory index
  if k2 == 0 then return 0
  if ← jl_egal_ key k2 then
    if (← readCell memory (index+1)) != 0 then return cellAddress memory (index+1)
    if key != (← getWorld).globals.nothing then return 0
  let next := (index+2) &&& (size-1)
  let iter := iter+1
  if iter ≤ maxprobe && next != origin then
    peekLoop memory key size maxprobe origin next iter
  else pure 0
partial_fixpoint

-- Source: src/iddict.c:107-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /* returns bp if key is in hash, otherwise NULL */
-- inline _Atomic(jl_value_t*) *jl_table_peek_bp(jl_genericmemory_t *a, jl_value_t *key) JL_NOTSAFEPOINT
-- {
--     size_t sz = hash_size(a);
--     if (sz == 0)
--         return NULL;
--     size_t maxprobe = max_probe(sz);
--     _Atomic(jl_value_t*) *tab = (_Atomic(jl_value_t*)*) a->ptr;
--     uint_t hv = keyhash(key);
--     size_t index = h2index(hv, sz);
--     sz *= 2;
--     size_t orig = index;
--     size_t iter = 0;
-- 
--     do {
--         jl_value_t *k2 = jl_atomic_load_relaxed(&tab[index]); // just to ensure the load doesn't get duplicated
--         if (k2 == NULL)
--             return NULL;
--         if (jl_egal(key, k2)) {
--             if (jl_atomic_load_relaxed(&tab[index + 1]) != NULL)
--                 return &tab[index + 1];
--             // `nothing` is our sentinel value for deletion, so need to keep searching if it's also our search key
--             if (key != jl_nothing)
--                 return NULL; // concurrent insertion hasn't completed yet
--         }
-- 
--         index = (index + 2) & (sz - 1);
--         iter++;
--     } while (iter <= maxprobe && index != orig);
-- 
--     return NULL;
-- }
-- /Source
def jl_table_peek_bp (memory : Memory) (key : Word) : M Word := do
  let size := hash_size memory
  if size == 0 then return 0
  let maxprobe := max_probe size
  let index := h2index (← keyhash key) size
  peekLoop memory key (size*2) maxprobe index index 0

-- Source: src/iddict.c:140-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT
-- jl_genericmemory_t *jl_eqtable_put(jl_genericmemory_t *h, jl_value_t *key, jl_value_t *val, int *p_inserted)
-- {
--     int inserted = jl_table_assign_bp(&h, key, val);
--     if (p_inserted)
--         *p_inserted = inserted;
--     return h;
-- }
-- /Source
def jl_eqtable_put (gc : GC) (memory : Memory) (key value : Word)
    (hasInsertedPointer : Bool := true) : M (Memory × Option Bool) := do
  let pointer ← newLocal (some memory)
  let inserted ← jl_table_assign_bp gc pointer key value
  return (← readLocal pointer, if hasInsertedPointer then some inserted else none)

-- Source: src/iddict.c:149-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- // Note: lookup in the IdDict is permitted concurrently, if you avoid deletions,
-- // and assuming you do use an external lock around all insertions
-- JL_DLLEXPORT
-- jl_value_t *jl_eqtable_get(jl_genericmemory_t *h, jl_value_t *key, jl_value_t *deflt) JL_NOTSAFEPOINT
-- {
--     _Atomic(jl_value_t*) *bp = jl_table_peek_bp(h, key);
--     return (bp == NULL) ? deflt : jl_atomic_load_relaxed(bp);
-- }
-- /Source
def jl_eqtable_get (memory : Memory) (key fallback : Word) : M Word := do
  let pointer ← jl_table_peek_bp memory key
  if pointer == 0 then pure fallback else atomicLoad pointer

-- Source: src/iddict.c:158-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_value_t *jl_eqtable_getkey(jl_genericmemory_t *h, jl_value_t *key, jl_value_t *deflt) JL_NOTSAFEPOINT
-- {
--     _Atomic(jl_value_t*) *bp = jl_table_peek_bp(h, key);
--     return (bp == NULL) ? deflt : jl_atomic_load_relaxed(bp - 1);
-- }
-- /Source
def jl_eqtable_getkey (memory : Memory) (key fallback : Word) : M Word := do
  let pointer ← jl_table_peek_bp memory key
  if pointer == 0 then pure fallback else atomicLoad (pointer-8)

-- Source: src/iddict.c:164-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT
-- jl_value_t *jl_eqtable_pop(jl_genericmemory_t *h, jl_value_t *key, jl_value_t *deflt, int *found)
-- {
--     _Atomic(jl_value_t*) *bp = jl_table_peek_bp(h, key);
--     if (found)
--         *found = (bp != NULL);
--     if (bp == NULL)
--         return deflt;
--     jl_value_t *val = jl_atomic_load_relaxed(bp);
--     jl_gc_write_atomic(h, bp[-1], jl_value_t, jl_nothing, relaxed); // clear the key
--     jl_gc_write_atomic(h, *bp, jl_value_t, NULL, relaxed); // and the value (briefly corrupting the table)
--     return val;
-- }
-- /Source
def jl_eqtable_pop (memory : Memory) (key fallback : Word)
    (hasFoundPointer : Bool := true) : M (Word × Option Bool) := do
  let pointer ← jl_table_peek_bp memory key
  let found := if hasFoundPointer then some (pointer != 0) else none
  if pointer == 0 then return (fallback, found)
  let value ← atomicLoad pointer
  gcWriteAtomic (memoryOwner memory) (pointer-8) (← getWorld).globals.nothing .monotonic
  gcWriteAtomic (memoryOwner memory) pointer 0 .monotonic
  return (value, found)

def nextindLoop (memory : Memory) (index : Word) : M Word := do
  if index ≥ UInt64.ofNat memory.length then pure (~~~(0 : Word))
  else if (← plainReadCell memory (index+1)) == 0 then nextindLoop memory (index+2)
  else pure index
partial_fixpoint

-- Source: src/iddict.c:178-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT
-- size_t jl_eqtable_nextind(jl_genericmemory_t *t, size_t i)
-- {
--     if (i & 1)
--         i++;
--     size_t alen = t->length;
--     while (i < alen && ((void**) t->ptr)[i + 1] == NULL)
--         i += 2;
--     if (i >= alen)
--         return (size_t)-1;
--     return i;
-- }
-- /Source
def jl_eqtable_nextind (memory : Memory) (index : Word) : M Word := do
  let index := if index &&& 1 != 0 then index+1 else index
  nextindLoop memory index

end JuliaLean.src.iddict_c

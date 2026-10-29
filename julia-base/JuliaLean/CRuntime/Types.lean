import JuliaLean.CRuntime.Memory

/-!
GC storage shapes from Julia master
`bbfa0ce4150ea33f2532198cabcf319a49399360`.

Finite object, page, array and address IDs are representation parameters.
Increasing them represents any finite execution with more allocations; no
protocol is specialized to one object or one queue slot. Integer fields retain
their C widths as bit vectors. Queue indices are signed interpretations of
64-bit vectors; capacity/mask are signed interpretations of 32-bit vectors.
Pointers are nullable finite IDs. `Address` preserves pointer equality without
classifying its allocation target; in particular `gc_allocd_scratch` does not
encode padded page-stack target typing. Heap storage is separate from typed
atomic locations, so accessing an atomic field must emit a `Memory.Event`.

These definitions cover GC-relevant TLS/global fields; unrelated task,
exception, profiler and code-generation fields are omitted. They describe
logical field contents and pointer identity, not C byte layout or padding.
-/

namespace JuliaLean.CRuntime

/-- Representation sizes for the heap structures in `src/julia.h:171-189`,
`src/gc-stock.h:80-144`, `src/gc-tls-stock.h:17-67`, `bbfa0ce4150`.
`wordBits` is 32 or 64 in an instantiated Julia target. -/
structure Config where
  objects : Nat
  pages : Nat
  arrays : Nat
  threads : Nat
  addresses : Nat
  wordBits : Nat := 64
  deriving DecidableEq, Repr

/-- Julia target pointer widths, `src/julia.h:174-178`, `bbfa0ce4150`. -/
def Config.Valid (cfg : Config) : Prop := cfg.wordBits = 32 ∨ cfg.wordBits = 64

abbrev ObjectId (cfg : Config) := Fin cfg.objects
abbrev PageId (cfg : Config) := Fin cfg.pages
abbrev ArrayId (cfg : Config) := Fin cfg.arrays
abbrev ThreadId (cfg : Config) := Fin cfg.threads
abbrev Address (cfg : Config) := Fin cfg.addresses
abbrev Ptr (α : Type) := Option α
abbrev uintptr_t (cfg : Config) := BitVec cfg.wordBits

/-- A typed reference to an atomic field, whose effects are checked by
`Memory.Candidate`; `_Atomic(T)` in `src/julia_atomics.h:36-39`,
`bbfa0ce4150`. The type parameter records the field's C value type. -/
structure AtomicRef (Loc α : Type) where
  location : Loc
  deriving DecidableEq, Repr

/-- Actual two GC header bits, `src/julia_internal.h:422-428` and
`src/julia.h:171-178`, `bbfa0ce4150`. -/
abbrev GCBits := BitVec 2

/-- `src/julia_internal.h:422`, `bbfa0ce4150`. -/
def GC_CLEAN : GCBits := 0
/-- `src/julia_internal.h:423`, `bbfa0ce4150`. -/
def GC_MARKED : GCBits := 1
/-- `src/julia_internal.h:424`, `bbfa0ce4150`. -/
def GC_OLD : GCBits := 2
/-- `src/julia_internal.h:428`, `bbfa0ce4150`. -/
def GC_OLD_MARKED : GCBits := 3
/-- `src/julia_internal.h:425`, `bbfa0ce4150`. -/
def GC_IN_IMAGE : BitVec 4 := 4
/-- `src/julia_internal.h:426`, `bbfa0ce4150`. -/
def GC_IN_IMAGE_REMSET : BitVec 4 := 8
/-- `src/julia_internal.h:429`, `bbfa0ce4150`. -/
def GC_IN_IMAGE_NOT_REMSET : BitVec 4 := 4

/-- `src/gc-common.h:143-146`, `bbfa0ce4150`. -/
def gc_marked (bits : BitVec n) : Bool := (bits &&& 1) != 0

/-- `src/gc-common.h:148-151`, `bbfa0ce4150`. -/
def gc_old (bits : BitVec n) : Bool := (bits &&& 2) != 0

/-- `src/gc-common.h:153-156`, `bbfa0ce4150`. The supplied GC bits replace
exactly the low two header bits. -/
def gc_set_bits (tag : BitVec n) (bits : GCBits) : BitVec n :=
  (tag &&& ~~~(3 : BitVec n)) ||| BitVec.ofNat n bits.toNat

/-- `src/julia.h:171-179`, `bbfa0ce4150`. `tag` excludes the four low
header bits and is 60 bits on the 64-bit target, 28 bits on the 32-bit target. -/
structure jl_taggedvalue_bits (cfg : Config) where
  gc : GCBits
  in_image : BitVec 2
  tag : BitVec (cfg.wordBits - 4)
  deriving DecidableEq, Repr

/-- The union in `src/julia.h:181-189`, `bbfa0ce4150`. `header` is the
single stored word. `next` and `type` below are views of that same word. -/
structure jl_taggedvalue_t (cfg : Config) where
  header : uintptr_t cfg
  deriving DecidableEq, Repr

/-- `src/julia.h:183-184`, `bbfa0ce4150`. -/
def jl_taggedvalue_t.next (v : jl_taggedvalue_t cfg) : uintptr_t cfg := v.header
/-- `src/julia.h:183,185`, `bbfa0ce4150`. -/
def jl_taggedvalue_t.type (v : jl_taggedvalue_t cfg) : uintptr_t cfg := v.header
/-- `src/julia.h:171-178,183,186`, `bbfa0ce4150`. -/
def jl_taggedvalue_t.bits (v : jl_taggedvalue_t cfg) : jl_taggedvalue_bits cfg :=
  { gc := BitVec.ofNat 2 v.header.toNat
    in_image := BitVec.ofNat 2 (v.header.toNat / 4)
    tag := BitVec.ofNat (cfg.wordBits - 4) (v.header.toNat / 16) }

/-- Header followed by payload, `src/julia.h:159-162,181-204`,
`bbfa0ce4150`. Field references identify ordinary/atomic accesses in traces. -/
structure GCObject (Loc : Type) (cfg : Config) where
  tagged : jl_taggedvalue_t cfg
  fields : Array (Ptr (ObjectId cfg))
  header_location : Loc
  field_locations : Array Loc

/-- Pointer-tagged remset entries, `src/gc-stock.h:97` and
`src/gc-tls-stock.h:27-30`, `bbfa0ce4150`. -/
structure RemsetEntry (cfg : Config) where
  value : Ptr (ObjectId cfg)
  tagged : Bool
  deriving DecidableEq, Repr

/-- `src/support/arraylist.h:16-21`, `bbfa0ce4150`. `items` represents the
pointed-to storage; its allocated capacity and logical length stay separate. -/
structure arraylist_t (cfg : Config) (α : Type) where
  len : uintptr_t cfg
  max : uintptr_t cfg
  items : Array (Ptr α)
  _space : Vector (Ptr α) 29

/-- `src/support/arraylist.h:30-35`, `bbfa0ce4150`. -/
structure small_arraylist_t (cfg : Config) (α : Type) where
  len : uintptr_t cfg
  max : uintptr_t cfg
  items : Array (Ptr α)
  _space : Vector (Ptr α) 5

/-- `src/work-stealing-queue.h:24-28`, `bbfa0ce4150`. Each `buffer` entry
represents one memcpy element; byte-address calculations remain client checks. -/
structure ws_array_t (α : Type) where
  buffer : Array α
  capacity : BitVec 32
  mask : BitVec 32
  deriving Repr

/-- Atomic fields in `src/work-stealing-queue.h:45-50`, `bbfa0ce4150`.
The queue's array pointer can name any currently allocated array ID. -/
structure ws_queue_t (Loc : Type) (cfg : Config) where
  top : AtomicRef Loc (BitVec 64)
  bottom : AtomicRef Loc (BitVec 64)
  array : AtomicRef Loc (Ptr (ArrayId cfg))
  deriving DecidableEq, Repr

/-- `src/gc-stock.h:72-78`, `bbfa0ce4150`. -/
inductive gc_chunk_id_t where
  | GC_empty_chunk | GC_objary_chunk | GC_ary8_chunk | GC_ary16_chunk | GC_finlist_chunk
  deriving DecidableEq, Repr

/-- `src/gc-stock.h:80-89`, `bbfa0ce4150`. Addresses identify positions
in the client's payload/descriptor arrays, including one-past-end positions. -/
structure jl_gc_chunk_t (cfg : Config) where
  cid : gc_chunk_id_t
  parent : Ptr (ObjectId cfg)
  «begin» : Ptr (Address cfg)
  «end» : Ptr (Address cfg)
  elem_begin : Ptr (Address cfg)
  elem_end : Ptr (Address cfg)
  step : BitVec 32
  nptr : uintptr_t cfg
  deriving DecidableEq, Repr

/-- `src/gc-tls-stock.h:37-41`, `bbfa0ce4150`. Replaced arrays stay in
`reclaim_set` until the source's reclamation phase. -/
structure jl_gc_markqueue_t (Loc : Type) (cfg : Config) where
  chunk_queue : ws_queue_t Loc cfg
  ptr_queue : ws_queue_t Loc cfg
  reclaim_set : arraylist_t cfg (ArrayId cfg)

/-- Every field of `src/gc-stock.h:100-144`, `bbfa0ce4150`. -/
structure jl_gc_pagemeta_t (Loc : Type) (cfg : Config) where
  next : Ptr (PageId cfg)
  pool_n : BitVec 8
  has_marked : BitVec 8
  has_young : BitVec 8
  has_weak_processing : AtomicRef Loc (BitVec 8)
  nold : BitVec 16
  prev_nold : BitVec 16
  nfree : BitVec 16
  osize : BitVec 16
  fl_begin_offset : BitVec 16
  fl_end_offset : BitVec 16
  thread_n : BitVec 16
  data : Ptr (Address cfg)

/-- `src/gc-tls-stock.h:50-52`, `bbfa0ce4150`. -/
structure jl_gc_page_stack_t (Loc : Type) (cfg : Config) where
  bottom : AtomicRef Loc (Ptr (PageId cfg))
  deriving DecidableEq, Repr

/-- Padding has no logical field content, `src/gc-stock.h:230-243`,
`bbfa0ce4150`. -/
structure jl_gc_padded_page_stack_t (Loc : Type) (cfg : Config) where
  stack : jl_gc_page_stack_t Loc cfg
  deriving DecidableEq, Repr

/-- `src/gc-tls-stock.h:17-21`, `bbfa0ce4150`. -/
structure jl_gc_pool_t (cfg : Config) where
  freelist : Ptr (ObjectId cfg)
  newpages : Ptr (ObjectId cfg)
  osize : BitVec 16
  deriving DecidableEq, Repr

/-- `src/gc-tls-stock.h:23-35`, `bbfa0ce4150`. The source fixes the pool
count to 51. Big-value IDs share object identity with their header/payload. -/
structure jl_thread_heap_t (cfg : Config) where
  young_generation_of_bigvals : Ptr (ObjectId cfg)
  remset_nptr : BitVec 32
  remset : arraylist_t cfg (RemsetEntry cfg)
  norm_pools : Vector (jl_gc_pool_t cfg) 51

/-- `src/gc-tls-stock.h:43-48`, `bbfa0ce4150`. -/
structure jl_gc_mark_cache_t (cfg : Config) where
  perm_scanned_bytes : uintptr_t cfg
  scanned_bytes : uintptr_t cfg
  deriving DecidableEq, Repr

/-- `src/gc-tls-stock.h:54-67`, `bbfa0ce4150`. -/
structure jl_gc_tls_states_t (Loc : Type) (cfg : Config) where
  heap : jl_thread_heap_t cfg
  page_metadata_allocd : jl_gc_page_stack_t Loc cfg
  mark_queue : jl_gc_markqueue_t Loc cfg
  gc_cache : jl_gc_mark_cache_t cfg
  gc_sweeps_requested : AtomicRef Loc (uintptr_t cfg)
  gc_stack_sweep_requested : AtomicRef Loc (uintptr_t cfg)
  sweep_objs : arraylist_t cfg (ObjectId cfg)
  weak_processing_objs : small_arraylist_t cfg (ObjectId cfg)

/-- Exact values of `src/julia_threads.h:186-198`, `bbfa0ce4150`. -/
inductive GCState where
  | «unsafe» | waiting | safe | parallelCollector | concurrentCollector
  deriving DecidableEq, Repr

def GCState.toBits : GCState → BitVec 8
  | .unsafe => 0
  | .waiting => 1
  | .safe => 2
  | .parallelCollector => 3
  | .concurrentCollector => 4

/-- GC-related projection of `src/julia_threads.h:178-216`,
`bbfa0ce4150`. `gc_state` remains an atomic int8 field. Task objects use
`ObjectId`, retaining their identity among other heap objects. Global finalizer
arrays and the pending hint are represented by the finalizer protocol model. -/
structure jl_tls_states_t (Loc : Type) (cfg : Config) where
  tid : BitVec 16
  threadpoolid : BitVec 8
  rngseed : BitVec 64
  safepoint : AtomicRef Loc (Ptr (Address cfg))
  sleep_check_state : AtomicRef Loc (BitVec 8)
  gc_state : AtomicRef Loc (BitVec 8)
  in_pure_callback : BitVec 16
  in_finalizer : BitVec 16
  disable_gc : BitVec 16
  finalizers_inhibited : BitVec 32
  gc_tls : jl_gc_tls_states_t Loc cfg
  current_task : AtomicRef Loc (Ptr (ObjectId cfg))
  next_task : Ptr (ObjectId cfg)
  previous_task : Ptr (ObjectId cfg)
  root_task : Ptr (ObjectId cfg)

/-- GC global fields: `src/julia_internal.h:1395-1396`,
`src/gc-stock.c:38-72`, `src/gc-stock.h:146-149`,
`src/gc-common.h:224-225`, `src/threading.h:17`,
`src/jl_exported_data.inc:171`, `bbfa0ce4150`. Unrelated statistics and OS
handles are omitted; mutex identity is preserved for memory events. Global C
`int` fields use the signed interpretation of their 32-bit vectors. -/
structure GlobalGCState (Loc : Type) (cfg : Config) where
  jl_gc_running : AtomicRef Loc (BitVec 32)
  jl_gc_disable_counter : AtomicRef Loc (BitVec 32)
  jl_n_threads : AtomicRef Loc (BitVec 32)
  jl_all_tls_states : AtomicRef Loc (Ptr (Address cfg))
  gc_n_threads : BitVec 32
  gc_all_tls_states : Array (Ptr (ThreadId cfg))
  gc_first_tid : BitVec 32
  jl_n_markthreads : BitVec 32
  gc_n_threads_marking : AtomicRef Loc (BitVec 32)
  gc_initiator_tid : AtomicRef Loc (BitVec 32)
  gc_queue_observer_lock : Nat
  gc_threads_lock : Nat
  gc_n_threads_sweeping_pools : AtomicRef Loc (BitVec 32)
  gc_allocd_scratch : AtomicRef Loc (Ptr (Address cfg))
  jl_n_sweepthreads : BitVec 32
  gc_n_threads_sweeping_stacks : AtomicRef Loc (BitVec 32)
  gc_ptls_sweep_idx : AtomicRef Loc (BitVec 32)
  gc_stack_free_idx : AtomicRef Loc (BitVec 32)
  global_page_pool_lazily_freed : jl_gc_page_stack_t Loc cfg
  global_page_pool_lazily_freed_n : AtomicRef Loc (uintptr_t cfg)
  global_page_pool_clean : jl_gc_page_stack_t Loc cfg
  global_page_pool_freed : jl_gc_page_stack_t Loc cfg
  oldest_generation_of_bigvals : Ptr (ObjectId cfg)
  objects : ObjectId cfg → Option (GCObject Loc cfg)
  pages : PageId cfg → Option (jl_gc_pagemeta_t Loc cfg)
  threads : ThreadId cfg → Option (jl_tls_states_t Loc cfg)

example : gc_marked GC_CLEAN = false ∧ gc_old GC_CLEAN = false := by decide
example : gc_marked GC_MARKED = true ∧ gc_old GC_MARKED = false := by decide
example : gc_marked GC_OLD = false ∧ gc_old GC_OLD = true := by decide
example : gc_marked GC_OLD_MARKED = true ∧ gc_old GC_OLD_MARKED = true := by decide
example : gc_set_bits (0x1234 : BitVec 64) GC_OLD_MARKED = 0x1237 := by decide

end JuliaLean.CRuntime

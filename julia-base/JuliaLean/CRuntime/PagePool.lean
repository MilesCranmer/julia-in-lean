import JuliaLean.CRuntime.Memory
import JuliaLean.CRuntime.Types
import JuliaLean.Registry.Types

/-!
Page stacks and page sweeping at Julia bbfa0ce4150ea33f2532198cabcf319a49399360.

The stack nodes below are the actual page metadata nodes. Their `next` fields
remain shared after a pop; a pop saves `next` before attempting compare-exchange.
The model checks the non-reinsertion premise in `src/gc-stock.h:151-169`,
including the Windows commit-failure path.

The page-granularity machine retains the page fields read by prescan, the
allocated, clean, freed, and lazily-freed stacks, scratch and temporary stacks,
the allocation map, sweep requests, active workers, retention count, collector
publication, and the concurrent freeing program counter. Profiling output and
the objects within a page have separate boundaries: `has_marked`, `has_young`,
and the result of a cell scan are inputs at a page-sweep checkpoint. The cell
scanner at `src/gc-stock.c:978-1082` is not a proof of object marking.
The Windows API is represented by its commit-result input at
`src/gc-pages.c:171`. The rollback witness assumes a valid popped page and
a failed commit; it models no Windows address-alignment, commit-granularity,
resource-accounting policy or other API side effects.

All source citations in this file refer to the commit above. `run` is an
operational interpreter, with no C11-legality check of its own. Only the
single-thread Windows rollback is registered from that interpreter. The race
entries stop at conflicting ordinary accesses. The counter/pointer candidate
establishes an accepted-zero checkpoint with a retained pointer. Its focused
continuation models empty stack copy and merge steps followed by scratch
allocation lifetime end. Its ghost history records the worker's pre-free
non-NULL base load while that worker remains paused. It stops before line 1471
pointer arithmetic, dereference or decrement and establishes no post-free C
pointer value, use-after-free, crash or completed worker sweep.
-/

namespace JuliaLean.CRuntime.PagePool

open JuliaLean.CRuntime.Memory

/-- `src/gc-stock.h:320-323,325-366`: names for the four valid byte values
0, 1, 2, 3. The C page-table field and its modeled accesses remain ordinary
memory; this enumeration introduces no atomicity or synchronization. -/
inductive MapState where
  | unmapped | allocated | lazilyFreed | freed
  deriving DecidableEq, Repr, BEq

/-- `src/gc-stock.h:99-144`: valid-metadata abstraction. Pool and thread
indices range over existing pools/TLS entries. `WellFormed` limits those
domains to their C widths. Boolean
flags represent the 0/1 values written by this protocol. `data` labels a page
base address through `State.address`; it need not equal the metadata ID.
Offsets and count fields retain their C widths. -/
structure Metadata (pages threads pools : Nat) where
  next : Option (Fin pages)
  pool_n : Fin pools
  has_marked : Bool
  has_young : Bool
  has_weak_processing : Bool
  nold : UInt16
  prev_nold : UInt16
  nfree : UInt16
  osize : UInt16
  fl_begin_offset : UInt16
  fl_end_offset : UInt16
  thread_n : Fin threads
  data : Fin pages

/-- `src/gc-stock.c:808-814,1361-1364,1471`; `src/gc-tls-stock.h:50-60`.
Scratch and temporary stacks have distinct addresses from allocated stacks. -/
inductive Stack (threads : Nat) where
  | lazy | clean | freed
  | allocated (thread : Fin threads)
  | scratch (thread : Fin threads)
  | temporary (thread : Fin threads)
  deriving DecidableEq, Repr, BEq

/-- `src/gc-stock.h:172-229`: five C stack entry points. -/
inductive StackOp where
  | push | pushNoSync | pop | tryPop | popNoSync
  deriving DecidableEq, Repr, BEq

/-- `src/gc-stock.h:174-176,182-187,194-201,208-213,220-227`.
Reading `old_back->next` is separate from the compare-exchange. -/
inductive StackPC where
  | load | test | readNext | writeNext | exchange | pause | ret
  deriving DecidableEq, Repr, BEq

/-- `src/gc-pages.c:108-182`; `src/gc-stock.c:1365-1401,1458-1505,1516-1530`.
The continuations identify the C caller after a stack subroutine returns. -/
inductive PC where
  | idle
  | allocLazy | allocLazyResult | allocLazyCount
  | allocClean | allocCleanResult | allocFreed | allocFreedResult | allocResident
  | allocLock | allocLockedClean | allocLockedCleanResult | allocUnlock
  | allocMap | allocCommit | allocFailureMap | allocFailurePush
  | allocFailureResident | allocThrow | allocReturn
  | prePop | prePopResult | preMarked | preWeak | preQuick | preClassify
  | preTail | preCount | prePush | preSweep | preRestoreLoad | preRestoreNext
  | prePublish | preNextThread
  | workerEnter | workerScratch | workerNextThread | workerPop | workerPopResult
  | workerSweep | workerFound | workerCheck | workerCheckResult | workerDec
  | workerRequestDone | workerReturned
  | sweepMarked | sweepWeak | sweepClassify | sweepReuse | sweepDeadHeap | sweepDeadMap
  | sweepDeadPush | sweepDeadCount | sweepDone
  | freeWait | freeKeep | freePresent | freeCompute | freeLoop | freePopResult
  | freeMap | freeNeighbor | freeMadvise | freePush | freeIncrement | freeCount
  | collectorPublishScratch | collectorRequest | collectorClose | collectorCount
  | collectorPublish | collectorMerge | collectorTerminate | collectorFreeScratch
  | collectorKeep | collectorPost | collectorResume
  deriving DecidableEq, Repr, BEq

/-- `src/gc-stock.h:172-229`: locals and retry bound of a stack call. -/
structure StackCall (pages threads : Nat) where
  op : StackOp
  pool : Stack threads
  pc : StackPC := .load
  element : Option (Fin pages) := none
  old_back : Option (Fin pages) := none
  next : Option (Fin pages) := none
  attempts : Nat := 0
  continuation : PC

/-- `src/gc-stock.c:1354-1401,1458-1505,1516-1530`; `src/gc-pages.c:108-182`.
Each actor retains the values of its previous loads and the page it owns. -/
structure Local (pages threads : Nat) where
  pc : PC := .idle
  call : Option (StackCall pages threads) := none
  page : Option (Fin pages) := none
  origin : Stack threads := .lazy
  returnPC : PC := .idle
  workerContinuation : PC := .workerRequestDone
  target : Nat := 0
  tail : Option (Fin pages) := none
  should_scan : Bool := true
  reuse_page : Bool := true
  found_pg : Bool := false
  no_more_work : Bool := true
  scratch : Bool := false
  counted : Bool := false
  scan_count : Nat := 0
  keep : UInt64 := 0
  present : UInt64 := 0
  to_free : UInt64 := 0
  freed_count : UInt64 := 0
  neighbor : Nat := 0
  saved_bottom : Option (Fin pages) := none
  weak : Bool := false
  dependencies : List Nat := []

/-- `src/gc-stock.h:159-166`: a pop records the stack address, node, actor,
and GC epoch. `collector` distinguishes the two non-reinsertion promises. -/
structure Pop (pages threads : Nat) where
  pool : Stack threads
  page : Fin pages
  actor : Fin threads
  epoch : Nat
  collector : Bool

/-- `src/gc-stock.c:53-60,808-814,1508-1510`; `src/gc-pages.c:185-234`.
`physical` identifies pages sharing one OS page when GC_PAGE_SZ is smaller.
`allocations` records completed allocations until the next stopped-world sweep. -/
structure State (pages threads pools : Nat) where
  metadata : Fin pages → Metadata pages threads pools
  bottom : Stack threads → Option (Fin pages)
  alloc_map : Fin pages → MapState
  locals : Fin threads → Local pages threads
  allocations : Fin pages → List (Fin threads)
  collector : Fin threads → Bool
  tls_live : Fin threads → Bool
  physical : Fin pages → Nat
  address : Fin pages → UInt64
  pageBytes : UInt64
  osPageBytes : UInt64
  windows : Bool
  current_sweep_full : Bool
  prev_sweep_full : Bool
  gc_allocd_scratch : Bool
  gc_n_threads_sweeping_pools : UInt32
  gc_sweeps_requested : Fin threads → UInt64
  global_page_pool_lazily_freed_n : UInt64
  gc_free_pages_keep : UInt64
  gc_sweep_assists_needed : Nat
  gc_pages_lock : Option (Fin threads)
  gc_threads_lock : Option (Fin threads)
  epoch : Nat
  stopped : Bool
  merged : Bool
  scratch_alive : Bool
  published : Bool
  gcHeapSize : UInt64
  bytesResident : UInt64
  history : List (Pop pages threads)
  abaViolation : Bool
  mutatorViolation : Bool
  madvisedAllocated : Bool

/-- `src/gc-stock.h:174-224`; `src/gc-stock.c:1438,1450,1459,1491,1516-1517`:
every load can choose a value independently. The emitted candidate records
the C11 consistency constraints. -/
structure ReadChoice (pages : Nat) where
  pointer : Option (Option (Fin pages)) := none
  flag : Option Bool := none
  word32 : Option UInt32 := none
  word64 : Option UInt64 := none
  mapByte : Option MapState := none

/-- An unspecified choice selects the current store, a valid SC trace choice.
Source: `src/gc-stock.h:174-224`; `src/julia_atomics.h:105-165`. -/
def observed {α : Type} (choice : Option α) (current : α) : α := choice.getD current

/-- `src/gc-stock.h:100-144,174-224,355-366`; `src/gc-stock.c:53-60,1510`:
distinct C objects have distinct locations, including every linked-list next. -/
inductive Location (pages threads : Nat) where
  | bottom (pool : Stack threads)
  | next (page : Fin pages)
  | map (page : Fin pages)
  | marked (page : Fin pages)
  | weak (page : Fin pages)
  | active | scratch | lazyCount | keep | heapSize | resident
  | requested (thread : Fin threads)
  deriving DecidableEq, Repr

def declaredAccessClass : Location pages threads → Memory.AccessClass
  | .next _ | .map _ | .marked _ => .ordinary
  | _ => .atomic

/-- Typed scalar contents for the source locations above.
Source: `src/gc-stock.h:100-144,320-323`; `src/gc-tls-stock.h:50-60`. -/
inductive Value (pages : Nat) where
  | pointer (value : Option (Fin pages))
  | flag (value : Bool)
  | byte (value : MapState)
  | word32 (value : UInt32)
  | word64 (value : UInt64)
  deriving DecidableEq, Repr

def weakAccessTypingCandidate : Candidate (Location 1 1) (Value 1) :=
  ⟨#[
    { thread := 1, action := .init (.weak 0) (.flag false) },
    { thread := 0, action := .load (.weak 0) .relaxed (.flag false), readFrom := some 0 }
  ]⟩

theorem weak_access_uses_declared_atomic_class :
    weakAccessTypingCandidate.DeclaredAccessTyped declaredAccessClass := by
  unfold Candidate.DeclaredAccessTyped
  decide

/-- `src/gc-stock.h:100-144`; `src/gc-tls-stock.h:50-60`: conversion to
the shared C storage foundation, retaining exact integer widths and locations. -/
def storageConfig (p t : Nat) : JuliaLean.CRuntime.Config :=
  { objects := 0, pages := p, arrays := 0, threads := t, addresses := p, wordBits := 64 }

/-- `src/gc-stock.h:100-144`: finite-ID storage view. Address IDs are
labels, whose numeric 64-bit bases are supplied by `State.address`. This is
an address-preserving abstraction on `WellFormed` states, not a C byte-layout
or pointer-bit-pattern model. The weak flag remains an atomic field. -/
def metadataStorage {p t k : Nat} (s : State p t k) (q : Fin p) :
    JuliaLean.CRuntime.jl_gc_pagemeta_t (Location p t) (storageConfig p t) :=
  let m := s.metadata q
  { next := m.next, pool_n := BitVec.ofNat 8 m.pool_n.val, has_marked := BitVec.ofNat 8 (if m.has_marked then 1 else 0), has_young := BitVec.ofNat 8 (if m.has_young then 1 else 0), has_weak_processing := ⟨.weak q⟩, nold := BitVec.ofNat 16 m.nold.toNat, prev_nold := BitVec.ofNat 16 m.prev_nold.toNat, nfree := BitVec.ofNat 16 m.nfree.toNat, osize := BitVec.ofNat 16 m.osize.toNat, fl_begin_offset := BitVec.ofNat 16 m.fl_begin_offset.toNat, fl_end_offset := BitVec.ofNat 16 m.fl_end_offset.toNat, thread_n := BitVec.ofNat 16 m.thread_n.val, data := some m.data }

/-- Functional field assignment used by all mirrored C stores.
Source: `src/gc-stock.h:175-176,198,224`. -/
def put {α β : Type} [DecidableEq α] (f : α → β) (a : α) (v : β) : α → β :=
  fun b => if b = a then v else f b

/-- `src/gc-stock.h:102,174-176`: follow actual `next` pointers. The extra
step exposes a finite cycle. -/
def chain {p t k : Nat} (s : State p t k) : Nat → Option (Fin p) → List (Fin p)
  | 0, _ => []
  | _ + 1, none => []
  | n + 1, some q => q :: chain s n (s.metadata q).next

/-- `src/gc-stock.h:146-169`; `src/gc-tls-stock.h:50-60`: every real stack
address occurs once in this finite enumeration. -/
def stacks (t : Nat) : List (Stack t) :=
  [.lazy, .clean, .freed] ++ (List.finRange t).flatMap fun i =>
    [.allocated i, .scratch i, .temporary i]

/-- `src/gc-stock.h:146-169`; `src/gc-tls-stock.h:56`: the public page
stacks. Temporary roots can alias a transferred chain after a C struct copy. -/
def publicStacks (t : Nat) : List (Stack t) :=
  [.lazy, .clean, .freed] ++ (List.finRange t).map Stack.allocated

/-- `src/gc-stock.h:159-169`: count ownership claims without replacing
linked stacks by sets. The stack traversal still reads the actual next links. -/
def ownershipCount {p t k : Nat} (s : State p t k) (q : Fin p) : Nat :=
  let occurrences := ((publicStacks t).map fun pool =>
    ((chain s (p + 1) (s.bottom pool)).filter fun node => node == q).length).foldl (· + ·) 0
  let freeOccurrences := ([Stack.lazy, .clean, .freed].map fun pool =>
    ((chain s (p + 1) (s.bottom pool)).filter fun node => node == q).length).foldl (· + ·) 0
  max (s.allocations q).length occurrences + min (s.allocations q).length freeOccurrences

/-- `src/gc-stock.h:151-169`; `src/gc-pages.c:110-182`: externally allocated
pages and every stack node have at most one owner. In-flight popped pages are
held in the corresponding `Local.page`. -/
def UniqueOwnership {p t k : Nat} (s : State p t k) : Prop :=
  ∀ q, ownershipCount s q ≤ 1

/-- `src/gc-stock.h:355-367`; `src/gc-pages.c:110-182,185-234`: global
free-stack members have the allocation-map state required for that pool. -/
def MapMatches {p t k : Nat} (s : State p t k) : Prop :=
  (∀ q ∈ chain s (p + 1) (s.bottom .lazy), s.alloc_map q = .lazilyFreed) ∧
  (∀ q ∈ chain s (p + 1) (s.bottom .freed), s.alloc_map q = .freed) ∧
  (∀ q, s.allocations q ≠ [] → s.alloc_map q = .allocated) ∧
  (∀ q ∈ chain s (p + 1) (s.bottom .clean), s.alloc_map q = .unmapped) ∧
  (∀ thread, ∀ q ∈ chain s (p + 1) (s.bottom (.allocated thread)), s.alloc_map q = .allocated) ∧
  (∀ thread, ∀ q ∈ chain s (p + 1) (s.bottom (.scratch thread)), s.alloc_map q = .allocated)

/-- `src/gc-pages.c:152-153,188-202`: numeric address denoted by the
page metadata's finite data-address label. -/
def baseAddress {p t k : Nat} (s : State p t k) (q : Fin p) : Nat :=
  (s.address (s.metadata q).data).toNat

/-- `src/gc-stock.h:104,142`; `src/gc-pages.c:42-62,152`: finite IDs
represent valid pool/TLS indices and distinct aligned page base addresses.
No wrapping address interval is admitted. -/
def MetadataDomainValid {p t k : Nat} (s : State p t k) : Prop :=
  k ≤ 51 ∧ t ≤ 65536 ∧ 0 < s.pageBytes.toNat ∧
  Function.Injective s.address ∧
  (∀ q, 0 < baseAddress s q ∧ baseAddress s q % s.pageBytes.toNat = 0 ∧
    baseAddress s q + s.pageBytes.toNat ≤ 2 ^ 64)

/-- `src/gc-pages.c:192-203`: exact physical-page partition for the
small-GC-page branch. Every address visited by the C rounding/division loop
has exactly one represented page, since metadata addresses are injective.
The group labels agree exactly with the rounded OS-page bases. -/
def PhysicalPagePartition {p t k : Nat} (s : State p t k) : Prop :=
  MetadataDomainValid s ∧ s.pageBytes.toNat < s.osPageBytes.toNat ∧
  (s.pageBytes.toNat = 4096 ∨ s.pageBytes.toNat = 16384) ∧
  (∃ logSize : Fin 64, s.osPageBytes.toNat = 2 ^ logSize.val) ∧
  s.osPageBytes.toNat % s.pageBytes.toNat = 0 ∧
  (∀ q r, s.physical q = s.physical r ↔
    baseAddress s q / s.osPageBytes.toNat = baseAddress s r / s.osPageBytes.toNat) ∧
  (∀ q (slot : Fin (s.osPageBytes.toNat / s.pageBytes.toNat)), ∃ r,
    baseAddress s r = (baseAddress s q / s.osPageBytes.toNat) * s.osPageBytes.toNat +
      slot.val * s.pageBytes.toNat)

/-- `src/gc-stock.h:99-144,151-169,320-367`: arbitrary finite checkpoint
states have unique addresses, finite acyclic stacks, consistent pool IDs, and
allocation-map ownership. The no-ABA premise is a separate property. -/
def WellFormed {p t k : Nat} (s : State p t k) : Prop :=
  Function.Injective (fun q => (s.metadata q).data) ∧
  (∀ pool ∈ stacks t, (chain s (p + 1) (s.bottom pool)).Nodup) ∧
  UniqueOwnership s ∧ MapMatches s ∧ MetadataDomainValid s

/-- Finite checking of `src/gc-stock.h:151-169,320-367` checkpoints. -/
instance {p t k : Nat} (s : State p t k) : Decidable (UniqueOwnership s) := by
  unfold UniqueOwnership
  infer_instance

/-- Finite checking of `src/gc-stock.h:320-367` allocation-map invariants. -/
instance {p t k : Nat} (s : State p t k) : Decidable (MapMatches s) := by
  unfold MapMatches
  infer_instance

/-- Finite checking of `src/gc-stock.h:100-144` valid metadata. -/
instance {p t k : Nat} (s : State p t k) : Decidable (MetadataDomainValid s) := by
  unfold MetadataDomainValid Function.Injective
  infer_instance

/-- Finite checking of the physical-page loop in `src/gc-pages.c:192-203`. -/
instance {p t k : Nat} (s : State p t k) : Decidable (PhysicalPagePartition s) := by
  unfold PhysicalPagePartition
  infer_instance

/-- Finite checking of `src/gc-stock.h:99-169,320-367` checkpoints. -/
instance {p t k : Nat} (s : State p t k) : Decidable (WellFormed s) := by
  unfold WellFormed Function.Injective
  infer_instance

/-- `src/gc-stock.h:161-166`: exactly the documented premise, including
the stronger "never again" rule for pages popped by a GC thread. -/
def permittedReinsert {p t k : Nat} (s : State p t k)
    (pool : Stack t) (q : Fin p) : Bool :=
  !(s.history.any fun h => h.pool == pool && h.page == q &&
    (h.collector || h.epoch == s.epoch))

/-- `src/gc-stock.h:161-163`: the mutator rule alone. The GC-thread
forever rule is separate and is not the registered Windows claim. -/
def mutatorReinsert {p t k : Nat} (s : State p t k)
    (pool : Stack t) (q : Fin p) : Bool :=
  s.history.any fun h => h.pool == pool && h.page == q &&
    !h.collector && h.epoch == s.epoch

/-- `src/gc-stock.h:174,182,194,208,220`: relaxed bottom load. -/
def loadBottom {p t k : Nat} (s : State p t k) (c : StackCall p t)
    (choice : ReadChoice p) : StackCall p t :=
  { c with old_back := observed choice.pointer (s.bottom c.pool), pc := .test }

/-- `src/gc-stock.h:175,183`: the node's next pointer is a plain store.
The contract violation flag observes the source transition and never blocks it. -/
def storeNext {p t k : Nat} (s : State p t k) (c : StackCall p t) : State p t k :=
  match c.element with
  | none => s
  | some q => { s with metadata := put s.metadata q { (s.metadata q) with next := c.old_back } }

/-- `src/gc-stock.h:176,184,198,212,224`: successful publication or removal.
`jl_atomic_cmpswap` is seq_cst on success and failure (`julia_atomics.h:163-165`). -/
def publishBottom {p t k : Nat} (s : State p t k) (actor : Fin t)
    (c : StackCall p t) : State p t k :=
  if c.op = .push ∨ c.op = .pushNoSync then
    match c.element with
    | none => s
    | some q => { s with bottom := put s.bottom c.pool (some q), abaViolation := s.abaViolation || !permittedReinsert s c.pool q, mutatorViolation := s.mutatorViolation || mutatorReinsert s c.pool q }
  else
    let history := match c.old_back with
      | none => s.history
      | some q => s.history ++ [⟨c.pool, q, actor, s.epoch, s.collector actor⟩]
    { s with bottom := put s.bottom c.pool c.next, history := history }

/-- `src/gc-stock.h:172-229`: each load, next read/write, strong CAS,
pause, and return is one step. `try_pop` makes at most 1024 attempts. The
no-sync variants retain their actual relaxed bottom store. -/
def stackStep {p t k : Nat} (actor : Fin t) (s : State p t k)
    (c : StackCall p t) (choice : ReadChoice p) : State p t k × Option (StackCall p t) :=
  let l := s.locals actor
  let finish (s : State p t k) (result : Option (Fin p)) :=
    ({ s with locals := put s.locals actor { l with pc := c.continuation, call := none, page := result } }, none)
  match c.pc with
  | .load => (s, some (loadBottom s c choice))
  | .test =>
    if c.op = .push ∨ c.op = .pushNoSync then
      (s, some { c with pc := .writeNext })
    else if c.old_back = none then finish s none
    else (s, some { c with pc := .readNext })
  | .readNext =>
    let next := observed choice.pointer (c.old_back.bind fun q => (s.metadata q).next)
    (s, some { c with next := next, pc := .exchange })
  | .writeNext => (storeNext s c, some { c with pc := .exchange })
  | .exchange =>
    if c.op = .pushNoSync ∨ c.op = .popNoSync ∨ observed choice.pointer (s.bottom c.pool) = c.old_back then
      let s := publishBottom s actor c
      (s, some { c with pc := .ret })
    else (s, some { c with old_back := observed choice.pointer (s.bottom c.pool), pc := .pause })
  | .pause =>
    if c.op = .tryPop ∧ c.attempts + 1 ≥ 1024 then finish s none
    else (s, some { c with attempts := c.attempts + 1, pc := .load })
  | .ret => finish s (if c.op = .push ∨ c.op = .pushNoSync then c.element else c.old_back)

/-- `src/gc-pages.c:111,120,127,140,173`; `src/gc-stock.c:1366,1389,1472,1521,1526`:
call a real stack helper with its C continuation. -/
def callStack {p t k : Nat} (actor : Fin t) (s : State p t k) (op : StackOp)
    (pool : Stack t) (continuation : PC) : State p t k :=
  let l := s.locals actor
  { s with locals := put s.locals actor { l with call := some { op := op, pool := pool, element := l.page, continuation := continuation } } }

/-- `src/gc-stock.c:1172-1177,1356-1405,1465-1496`: finite TLS traversal. -/
def targetThread {p t : Nat} (l : Local p t) : Option (Fin t) :=
  if h : l.target < t then some ⟨l.target, h⟩ else none

/-- `src/gc-pages.c:111-182`: all reuse branches and the Windows failure
rollback. A fresh mapping enters this machine at `allocMap` after its metadata
block has been installed by the mapping transition below. -/
def allocatorStep {p t k : Nat} (actor : Fin t) (commitSucceeds : Bool)
    (choice : ReadChoice p) (s : State p t k) : State p t k :=
  let l := s.locals actor
  let pc (next : PC) := { s with locals := put s.locals actor { l with pc := next } }
  match l.pc with
  | .allocLazy => callStack actor s .pop .lazy .allocLazyResult
  | .allocLazyResult =>
    if l.page = none then pc .allocClean
    else { s with locals := put s.locals actor { l with pc := .allocLazyCount, origin := .lazy } }
  | .allocLazyCount => { pc .allocMap with global_page_pool_lazily_freed_n := observed choice.word64 s.global_page_pool_lazily_freed_n - 1 }
  | .allocClean => callStack actor s .pop .clean .allocCleanResult
  | .allocCleanResult =>
    if l.page = none then pc .allocFreed
    else { s with locals := put s.locals actor { l with pc := .allocMap, origin := .clean } }
  | .allocFreed => callStack actor s .pop .freed .allocFreedResult
  | .allocFreedResult =>
    if l.page = none then pc .allocLock
    else { s with locals := put s.locals actor { l with pc := .allocResident, origin := .freed } }
  | .allocResident => { pc .allocMap with bytesResident := observed choice.word64 s.bytesResident + s.pageBytes }
  | .allocMap =>
    match l.page with
    | none => s
    | some q => { pc (if l.origin = .lazy then .allocReturn else .allocCommit) with alloc_map := put s.alloc_map q .allocated }
  | .allocCommit =>
    if s.windows && !commitSucceeds then pc .allocFailureMap else pc .allocReturn
  | .allocFailureMap =>
    match l.page with
    | none => s
    | some q => { pc .allocFailurePush with alloc_map := put s.alloc_map q .freed }
  | .allocFailurePush => callStack actor s .push .freed .allocFailureResident
  | .allocFailureResident => { pc .allocThrow with bytesResident := observed choice.word64 s.bytesResident - s.pageBytes }
  | .allocThrow => pc .idle
  | .allocReturn =>
    match l.page with
    | none => s
    | some q => { pc .idle with allocations := put s.allocations q (s.allocations q ++ [actor]) }
  | .allocLock =>
    if s.gc_pages_lock = none then { pc .allocLockedClean with gc_pages_lock := some actor } else s
  | .allocLockedClean => callStack actor s .pop .clean .allocLockedCleanResult
  | .allocLockedCleanResult =>
    if l.page = none then s
    else { s with locals := put s.locals actor { l with pc := .allocUnlock, origin := .clean } }
  | .allocUnlock => { pc .allocMap with gc_pages_lock := none }
  | _ => s

/-- `src/gc-pages.c:148-161`: mapping a fresh block sets data identities,
creates zeroed allocation-map entries, marks the first page allocated, and
pushes later pages to the clean stack. Each page's individual helper steps
are represented by `callStack`, so this mapping boundary only admits pages
whose zeroed allocation-map entry already exists. -/
def freshMapPage {p t k : Nat} (s : State p t k) (q : Fin p) : State p t k :=
  { s with alloc_map := put s.alloc_map q .unmapped }

/-- `src/gc-stock.c:1110-1140,1370-1380`: exact page-level prescan decision.
The has_marked test in prescan intentionally precedes the weak-processing test. -/
def prescanNeedsScan {p t k : Nat} (s : State p t k) (q : Fin p) : Bool :=
  let m := s.metadata q
  m.has_marked && (s.current_sweep_full || m.has_young ||
    m.has_weak_processing || (s.prev_sweep_full && m.prev_nold != m.nold))

/-- `src/gc-stock.c:1350-1407`: the removed chain is built in `tmp`, its
tail is reconnected, then its bottom is assigned back. No worker is enabled
until `collectorPublishScratch`, after this prescan completes. -/
def prescanStep {p t k : Nat} (actor : Fin t) (choice : ReadChoice p)
    (s : State p t k) : State p t k :=
  let l := s.locals actor
  let pc (next : PC) := { s with locals := put s.locals actor { l with pc := next } }
  match l.pc with
  | .prePop =>
    match targetThread l with
    | none => pc .collectorPublishScratch
    | some target => callStack actor s .popNoSync (.allocated target) .prePopResult
  | .prePopResult => pc (if l.page = none then .preRestoreLoad else .preMarked)
  | .preMarked =>
    match l.page with
    | none => s
    | some q => { s with locals := put s.locals actor { l with pc := .preWeak, should_scan := (s.metadata q).has_marked } }
  | .preWeak =>
    match l.page with
    | none => s
    | some q => { s with locals := put s.locals actor { l with pc := .preQuick, weak := if s.current_sweep_full || (s.metadata q).has_young then false else observed choice.flag (s.metadata q).has_weak_processing } }
  | .preQuick =>
    match l.page with
    | none => s
    | some q => { s with locals := put s.locals actor { l with pc := .preClassify, should_scan := l.should_scan && (s.current_sweep_full || (s.metadata q).has_young || l.weak || (s.prev_sweep_full && (s.metadata q).prev_nold != (s.metadata q).nold)) } }
  | .preClassify => pc (if l.should_scan then .preTail else .preSweep)
  | .preTail => { s with locals := put s.locals actor { l with pc := .preCount, tail := if l.tail = none then l.page else l.tail } }
  | .preCount => { s with locals := put s.locals actor { l with pc := .prePush, scan_count := l.scan_count + 1 } }
  | .prePush =>
    match targetThread l with
    | none => s
    | some target => callStack actor s .pushNoSync (.temporary target) .prePop
  | .preSweep => { s with locals := put s.locals actor { l with pc := .sweepMarked, returnPC := .prePop } }
  | .preRestoreLoad =>
    match targetThread l with
    | none => s
    | some target => { s with locals := put s.locals actor { l with pc := .preRestoreNext, saved_bottom := observed choice.pointer (s.bottom (.allocated target)) } }
  | .preRestoreNext =>
    match l.tail with
    | none => pc .prePublish
    | some q => { pc .prePublish with metadata := put s.metadata q { (s.metadata q) with next := l.saved_bottom } }
  | .prePublish =>
    match targetThread l with
    | none => s
    | some target => { pc .preNextThread with bottom := put s.bottom (.allocated target) (s.bottom (.temporary target)) }
  | .preNextThread =>
    match targetThread l with
    | none => pc .collectorPublishScratch
    | some target => { s with bottom := put s.bottom (.temporary target) none, locals := put s.locals actor { l with pc := .prePop, target := l.target + 1, tail := none } }
  | _ => s

/-- `src/gc-stock.c:1103-1154`: page ownership transfers in `gc_sweep_page`.
The optional cell-scan result is a checkpoint input at :1137-1141; the
wholesale-dead branch still tests the actual weak-processing metadata flag. -/
def sweepPageStep {p t k : Nat} (actor : Fin t) (choice : ReadChoice p)
    (s : State p t k) : State p t k :=
  let l := s.locals actor
  let pc (next : PC) := { s with locals := put s.locals actor { l with pc := next } }
  match l.page with
  | none => s
  | some q =>
    match l.pc with
    | .sweepMarked => { s with locals := put s.locals actor { l with pc := .sweepWeak, reuse_page := (s.metadata q).has_marked } }
    | .sweepWeak => { s with locals := put s.locals actor { l with pc := .sweepClassify, reuse_page := l.reuse_page || observed choice.flag (s.metadata q).has_weak_processing } }
    | .sweepClassify => pc (if l.reuse_page then .sweepReuse else .sweepDeadHeap)
    | .sweepReuse => callStack actor s .push (.scratch (s.metadata q).thread_n) .sweepDone
    | .sweepDeadHeap => { pc .sweepDeadMap with gcHeapSize := observed choice.word64 s.gcHeapSize - s.pageBytes }
    | .sweepDeadMap => { pc .sweepDeadPush with alloc_map := put s.alloc_map q .lazilyFreed }
    | .sweepDeadPush => callStack actor s .push .lazy .sweepDeadCount
    | .sweepDeadCount => { pc .sweepDone with global_page_pool_lazily_freed_n := observed choice.word64 s.global_page_pool_lazily_freed_n + 1 }
    | .sweepDone => pc l.returnPC
    | _ => s

/-- `src/gc-stock.c:1458-1505,4068-4071`: worker counter entry precedes
the seq_cst scratch load. A late worker with NULL scratch skips all page work.
The active count and the outstanding request have separate lifetimes. -/
def workerStep {p t k : Nat} (actor : Fin t) (choice : ReadChoice p)
    (s : State p t k) : State p t k :=
  let l := s.locals actor
  let pc (next : PC) := { s with locals := put s.locals actor { l with pc := next } }
  match l.pc with
  | .workerEnter => { s with gc_n_threads_sweeping_pools := observed choice.word32 s.gc_n_threads_sweeping_pools + 1, locals := put s.locals actor { l with pc := .workerScratch, counted := true } }
  | .workerScratch => { s with locals := put s.locals actor { l with pc := if observed choice.flag s.gc_allocd_scratch then .workerNextThread else .workerDec, scratch := observed choice.flag s.gc_allocd_scratch, target := 0, found_pg := false } }
  | .workerNextThread =>
    match targetThread l with
    | none => { s with locals := put s.locals actor { l with pc := if l.found_pg then .workerNextThread else .workerCheck, target := 0, found_pg := false, no_more_work := true } }
    | some target =>
      if s.tls_live target then pc .workerPop
      else { s with locals := put s.locals actor { l with target := l.target + 1 } }
  | .workerPop =>
    match targetThread l with
    | none => s
    | some target => callStack actor s .tryPop (.allocated target) .workerPopResult
  | .workerPopResult =>
    if l.page = none then { s with locals := put s.locals actor { l with pc := .workerNextThread, target := l.target + 1 } }
    else pc .workerSweep
  | .workerSweep => { s with locals := put s.locals actor { l with pc := .sweepMarked, returnPC := .workerFound } }
  | .workerFound => { s with locals := put s.locals actor { l with pc := .workerNextThread, target := l.target + 1, found_pg := true } }
  | .workerCheck =>
    match targetThread l with
    | none => pc (if l.no_more_work then .workerDec else .workerNextThread)
    | some target =>
      if !s.tls_live target then { s with locals := put s.locals actor { l with target := l.target + 1 } }
      else { s with locals := put s.locals actor { l with pc := .workerCheckResult, saved_bottom := observed choice.pointer (s.bottom (.allocated target)) } }
  | .workerCheckResult =>
    if l.saved_bottom = none then { s with locals := put s.locals actor { l with pc := .workerCheck, target := l.target + 1 } }
    else { s with locals := put s.locals actor { l with pc := .workerNextThread, target := 0, no_more_work := false } }
  | .workerDec => { s with gc_n_threads_sweeping_pools := observed choice.word32 s.gc_n_threads_sweeping_pools - 1, locals := put s.locals actor { l with pc := l.workerContinuation, counted := false, scratch := false } }
  | .workerRequestDone => { pc .workerReturned with gc_sweeps_requested := put s.gc_sweeps_requested actor (observed choice.word64 (s.gc_sweeps_requested actor) - 1) }
  | _ => s

/-- `src/gc-pages.c:189-203`: the physical-page test emits one plain
allocation-map read per page. -/
def physicalAllocated {p t k : Nat} (s : State p t k) (q : Fin p) : Bool :=
  (List.finRange p).any fun r => s.physical r == s.physical q && s.alloc_map r == .allocated

/-- `src/gc-stock.c:1516-1530,4096-4099`; `src/gc-pages.c:188-233`:
the concurrent thread owns the page from its successful pop until publication
to the freed stack. A physical-neighbor scan can return early without madvise. -/
def freeStep {p t k : Nat} (actor : Fin t) (choice : ReadChoice p)
    (s : State p t k) : State p t k :=
  let l := s.locals actor
  let pc (next : PC) := { s with locals := put s.locals actor { l with pc := next } }
  match l.pc with
  | .freeWait =>
    if s.gc_sweep_assists_needed = 0 then s
    else { pc .freeKeep with gc_sweep_assists_needed := s.gc_sweep_assists_needed - 1 }
  | .freeKeep => { s with locals := put s.locals actor { l with pc := .freePresent, keep := observed choice.word64 s.gc_free_pages_keep } }
  | .freePresent => { s with locals := put s.locals actor { l with pc := .freeCompute, present := observed choice.word64 s.global_page_pool_lazily_freed_n } }
  | .freeCompute => { s with locals := put s.locals actor { l with pc := .freeLoop, to_free := if l.present > l.keep then l.present - l.keep else 0, freed_count := 0 } }
  | .freeLoop =>
    if l.freed_count < l.to_free then callStack actor s .pop .lazy .freePopResult
    else pc .freeCount
  | .freePopResult => pc (if l.page = none then .freeCount else .freeMap)
  | .freeMap =>
    match l.page with
    | none => s
    | some q => { s with alloc_map := put s.alloc_map q .freed, locals := put s.locals actor { l with pc := if s.pageBytes < s.osPageBytes then .freeNeighbor else .freeMadvise, neighbor := 0 } }
  | .freeNeighbor =>
    match l.page with
    | none => s
    | some q =>
      if h : l.neighbor < p then
        let r : Fin p := ⟨l.neighbor, h⟩
        if s.physical r = s.physical q && observed choice.mapByte (s.alloc_map r) = .allocated then pc .freePush
        else { s with locals := put s.locals actor { l with neighbor := l.neighbor + 1 } }
      else pc .freeMadvise
  | .freeMadvise =>
    match l.page with
    | none => s
    | some q => { pc .freePush with madvisedAllocated := s.madvisedAllocated || physicalAllocated s q, bytesResident := s.bytesResident - (if s.pageBytes < s.osPageBytes then s.osPageBytes else s.pageBytes) }
  | .freePush => callStack actor s .push .freed .freeIncrement
  | .freeIncrement => { s with locals := put s.locals actor { l with pc := .freeLoop, freed_count := l.freed_count + 1 } }
  | .freeCount =>
    if l.freed_count = 0 then pc .freeWait
    else { pc .freeWait with global_page_pool_lazily_freed_n := observed choice.word64 s.global_page_pool_lazily_freed_n - l.freed_count }
  | _ => s

/-- `src/gc-stock.c:1415-1443,1449-1452,1592-1653`: collector publication,
request counters, barrier, free-list merge, scratch reclamation, and wakeup.
Copying a scratch bottom at :1595 is internal while mutators are stopped;
the collector resumes mutators only after the merge and terminal NULL writes. -/
def collectorStep {p t k : Nat} (actor : Fin t) (choice : ReadChoice p)
    (s : State p t k) : State p t k :=
  let l := s.locals actor
  let pc (next : PC) := { s with locals := put s.locals actor { l with pc := next } }
  match l.pc with
  | .collectorPublishScratch => { pc .collectorRequest with gc_allocd_scratch := true }
  | .collectorRequest =>
    match targetThread l with
    | none => { s with locals := put s.locals actor { l with pc := .workerEnter, target := 0, workerContinuation := .collectorClose } }
    | some target => { s with gc_sweeps_requested := put s.gc_sweeps_requested target (observed choice.word64 (s.gc_sweeps_requested target) + 1), locals := put s.locals actor { l with target := l.target + 1 } }
  | .collectorClose => { pc .collectorCount with gc_allocd_scratch := false }
  | .collectorCount =>
    if observed choice.word32 s.gc_n_threads_sweeping_pools = 0 then { s with locals := put s.locals actor { l with pc := .collectorPublish, target := 0 } } else s
  | .collectorPublish =>
    match targetThread l with
    | none => { s with locals := put s.locals actor { l with pc := .collectorMerge, target := 0 } }
    | some target => { s with bottom := put s.bottom (.allocated target) (s.bottom (.scratch target)), locals := put s.locals actor { l with target := l.target + 1 } }
  | .collectorMerge =>
    match targetThread l with
    | none => pc .collectorTerminate
    | some _ => { s with locals := put s.locals actor { l with target := l.target + 1 } }
  | .collectorTerminate => { pc .collectorFreeScratch with merged := true }
  | .collectorFreeScratch => { pc .collectorKeep with scratch_alive := false }
  | .collectorKeep => { pc .collectorPost with gc_free_pages_keep := l.keep }
  | .collectorPost => { pc .collectorResume with gc_sweep_assists_needed := s.gc_sweep_assists_needed + 1 }
  | .collectorResume => { pc .idle with stopped := false, published := true }
  | _ => s

/-- `src/gc-stock.h:172-229`; `src/gc-stock.c:1350-1663,4068-4099`:
one actor performs one source operation; scheduler choices never batch a stack
load, next read, or compare-exchange into a single operation. -/
def sourceStep {p t k : Nat} (actor : Fin t) (commitSucceeds : Bool)
    (choice : ReadChoice p) (s : State p t k) : State p t k :=
  match (s.locals actor).call with
  | some c =>
    let (s', call) := stackStep actor s c choice
    match call with
    | none => s'
    | some c' => { s' with locals := put s'.locals actor { (s'.locals actor) with call := some c' } }
  | none =>
    match (s.locals actor).pc with
    | .allocLazy | .allocLazyResult | .allocLazyCount | .allocClean
    | .allocCleanResult | .allocFreed | .allocFreedResult | .allocResident
    | .allocLock | .allocLockedClean | .allocLockedCleanResult | .allocUnlock
    | .allocMap | .allocCommit | .allocFailureMap | .allocFailurePush
    | .allocFailureResident | .allocThrow | .allocReturn => allocatorStep actor commitSucceeds choice s
    | .prePop | .prePopResult | .preMarked | .preWeak | .preQuick | .preClassify
    | .preTail | .preCount | .prePush | .preSweep | .preRestoreLoad | .preRestoreNext
    | .prePublish | .preNextThread => prescanStep actor choice s
    | .sweepMarked | .sweepWeak | .sweepClassify | .sweepReuse | .sweepDeadHeap | .sweepDeadMap
    | .sweepDeadPush | .sweepDeadCount | .sweepDone => sweepPageStep actor choice s
    | .workerEnter | .workerScratch | .workerNextThread | .workerPop | .workerPopResult
    | .workerSweep | .workerFound | .workerCheck | .workerCheckResult | .workerDec
    | .workerRequestDone | .workerReturned => workerStep actor choice s
    | .freeWait | .freeKeep | .freePresent | .freeCompute | .freeLoop | .freePopResult
    | .freeMap | .freeNeighbor | .freeMadvise | .freePush | .freeIncrement | .freeCount => freeStep actor choice s
    | _ => collectorStep actor choice s

/-- Current-state read choices instantiate an ordinary interleaving.
Source: `src/gc-stock.h:172-229`; `src/gc-stock.c:1350-1663`. -/
def step {p t k : Nat} (actor : Fin t) (commitSucceeds : Bool)
    (s : State p t k) : State p t k := sourceStep actor commitSucceeds {} s

/-- `src/gc-stock.h:172-229`; finite schedules with arbitrary commit results.
All finite page and thread counts and all well-formed starting states are
quantified by the registered properties below. -/
def run {p t k : Nat} : List (Fin t × Bool) → State p t k → State p t k
  | [], s => s
  | (actor, commit) :: rest, s => run rest (step actor commit s)

/-- `src/gc-stock.h:174-224`: exact atomic orders, including the ordinary
node access that occurs before the CAS. The no-sync exchange is a relaxed
store; a failed strong CAS retains seq_cst failure order. -/
def stackAction {p t k : Nat} (s : State p t k) (c : StackCall p t)
    (choice : ReadChoice p) : Option (Action (Location p t) (Value p)) :=
  match c.pc with
  | .load => some (.load (.bottom c.pool) .relaxed
      (.pointer (observed choice.pointer (s.bottom c.pool))))
  | .readNext => c.old_back.map fun q => .plainLoad (.next q)
      (.pointer (observed choice.pointer (s.metadata q).next))
  | .writeNext => c.element.map fun q => .plainStore (.next q) (.pointer c.old_back)
  | .exchange =>
    let desired := if c.op = .push ∨ c.op = .pushNoSync then c.element else c.next
    if c.op = .pushNoSync ∨ c.op = .popNoSync then
      some (.store (.bottom c.pool) .relaxed (.pointer desired))
    else some (.cas (.bottom c.pool) .seqCst .seqCst (.pointer c.old_back)
      (.pointer desired) (.pointer (observed choice.pointer (s.bottom c.pool))))
  | _ => none

/-- `src/gc-pages.c:113-143,172-174,189-203`; `src/gc-stock.c:1151-1153,
1399,1415-1450,1458-1459,1491,1505,1516-1530,1648,4071`:
each ownership-relevant shared-memory access has its actual C memory order.
There are no thread fences in these source paths. -/
def sourceAction {p t k : Nat} (actor : Fin t) (choice : ReadChoice p)
    (s : State p t k) : Option (Action (Location p t) (Value p)) :=
  let l := s.locals actor
  match l.call with
  | some c => stackAction s c choice
  | none =>
    match l.pc with
    | .allocLazyCount => some (.rmw .lazyCount .relaxed
        (.word64 (observed choice.word64 s.global_page_pool_lazily_freed_n))
        (.word64 (observed choice.word64 s.global_page_pool_lazily_freed_n - 1)))
    | .allocResident => some (.rmw .resident .relaxed
        (.word64 (observed choice.word64 s.bytesResident))
        (.word64 (observed choice.word64 s.bytesResident + s.pageBytes)))
    | .allocMap => l.page.map fun q => .plainStore (.map q) (.byte .allocated)
    | .allocFailureMap | .freeMap => l.page.map fun q => .plainStore (.map q) (.byte .freed)
    | .allocFailureResident => some (.rmw .resident .relaxed
        (.word64 (observed choice.word64 s.bytesResident))
        (.word64 (observed choice.word64 s.bytesResident - s.pageBytes)))
    | .allocLock => if s.gc_pages_lock = none then some (.lock 0) else none
    | .allocUnlock => some (.unlock 0)
    | .preMarked | .sweepMarked => l.page.map fun q => .plainLoad (.marked q) (.flag (s.metadata q).has_marked)
    | .preWeak =>
      l.page.bind fun q =>
        if s.current_sweep_full || (s.metadata q).has_young then none
        else some (.load (.weak q) .relaxed (.flag (observed choice.flag (s.metadata q).has_weak_processing)))
    | .sweepWeak =>
      l.page.bind fun q => if l.reuse_page then none else
        some (.load (.weak q) .relaxed (.flag (observed choice.flag (s.metadata q).has_weak_processing)))
    | .preRestoreLoad => (targetThread l).map fun target =>
        .load (.bottom (.allocated target)) .relaxed (.pointer (observed choice.pointer (s.bottom (.allocated target))))
    | .preRestoreNext => l.tail.map fun q => .plainStore (.next q) (.pointer l.saved_bottom)
    | .prePublish => (targetThread l).map fun target => .store (.bottom (.allocated target)) .relaxed
        (.pointer (s.bottom (.temporary target)))
    | .sweepDeadHeap => some (.rmw .heapSize .relaxed (.word64 (observed choice.word64 s.gcHeapSize))
        (.word64 (observed choice.word64 s.gcHeapSize - s.pageBytes)))
    | .sweepDeadMap => l.page.map fun q => .plainStore (.map q) (.byte .lazilyFreed)
    | .sweepDeadCount => some (.rmw .lazyCount .relaxed
        (.word64 (observed choice.word64 s.global_page_pool_lazily_freed_n))
        (.word64 (observed choice.word64 s.global_page_pool_lazily_freed_n + 1)))
    | .workerEnter => some (.rmw .active .seqCst
        (.word32 (observed choice.word32 s.gc_n_threads_sweeping_pools))
        (.word32 (observed choice.word32 s.gc_n_threads_sweeping_pools + 1)))
    | .workerScratch => some (.load .scratch .seqCst (.flag (observed choice.flag s.gc_allocd_scratch)))
    | .workerCheck => (targetThread l).bind fun target =>
        if !s.tls_live target then none else some (.load (.bottom (.allocated target)) .relaxed
          (.pointer (observed choice.pointer (s.bottom (.allocated target)))))
    | .workerDec => some (.rmw .active .seqCst
        (.word32 (observed choice.word32 s.gc_n_threads_sweeping_pools))
        (.word32 (observed choice.word32 s.gc_n_threads_sweeping_pools - 1)))
    | .workerRequestDone => some (.rmw (.requested actor) .seqCst
        (.word64 (observed choice.word64 (s.gc_sweeps_requested actor)))
        (.word64 (observed choice.word64 (s.gc_sweeps_requested actor) - 1)))
    | .freeKeep => some (.load .keep .relaxed (.word64 (observed choice.word64 s.gc_free_pages_keep)))
    | .freePresent => some (.load .lazyCount .relaxed (.word64 (observed choice.word64 s.global_page_pool_lazily_freed_n)))
    | .freeNeighbor =>
      l.page.bind fun q =>
        if h : l.neighbor < p then
          let r : Fin p := ⟨l.neighbor, h⟩
          if s.physical r = s.physical q then some (.plainLoad (.map r) (.byte (observed choice.mapByte (s.alloc_map r))))
          else none
        else none
    | .freeCount => if l.freed_count = 0 then none else some (.rmw .lazyCount .relaxed
        (.word64 (observed choice.word64 s.global_page_pool_lazily_freed_n))
        (.word64 (observed choice.word64 s.global_page_pool_lazily_freed_n - l.freed_count)))
    | .collectorPublishScratch => some (.store .scratch .seqCst (.flag true))
    | .collectorRequest => (targetThread l).map fun target => .rmw (.requested target) .seqCst
        (.word64 (observed choice.word64 (s.gc_sweeps_requested target)))
        (.word64 (observed choice.word64 (s.gc_sweeps_requested target) + 1))
    | .collectorClose => some (.store .scratch .seqCst (.flag false))
    | .collectorCount => some (.load .active .acquire (.word32 (observed choice.word32 s.gc_n_threads_sweeping_pools)))
    | .collectorPublish => (targetThread l).map fun target => .store (.bottom (.allocated target)) .relaxed
        (.pointer (s.bottom (.scratch target)))
    | .collectorKeep => some (.store .keep .relaxed (.word64 l.keep))
    | _ => none

/-- `src/gc-stock.h:174-224`; `src/gc-stock.c:1449-1459`: a scheduling
choice includes arbitrary read values, read-from ID, modification rank and SC
rank. Read-from choices can refer to a later event in the candidate. -/
structure Scheduled (pages threads : Nat) where
  actor : Fin threads
  commit : Bool := true
  reads : ReadChoice pages := {}
  memory : Memory.Choice := {}
  dependencies : List Nat := []

/-- Pre-execution state initialization for scalar locations used by the page
machine. These `.init` events are not C accesses. In particular, later `next`
metadata accesses are consistently ordinary loads/stores.
Source: `src/gc-stock.h:100-144`; `src/gc-stock.c:53-60,808-814,1510`. -/
def initialEvents {p t k : Nat} (s : State p t k) : List (Event (Location p t) (Value p)) :=
  ((stacks t).map fun pool => { thread := t, action := .init (.bottom pool) (.pointer (s.bottom pool)) }) ++
  (List.finRange p).flatMap (fun q =>
    [{ thread := t, action := .init (.next q) (.pointer (s.metadata q).next) },
     { thread := t, action := .init (.map q) (.byte (s.alloc_map q)) },
     { thread := t, action := .init (.marked q) (.flag (s.metadata q).has_marked) },
     { thread := t, action := .init (.weak q) (.flag (s.metadata q).has_weak_processing) }]) ++
  [{ thread := t, action := .init .active (.word32 s.gc_n_threads_sweeping_pools) },
   { thread := t, action := .init .scratch (.flag s.gc_allocd_scratch) },
   { thread := t, action := .init .lazyCount (.word64 s.global_page_pool_lazily_freed_n) },
   { thread := t, action := .init .keep (.word64 s.gc_free_pages_keep) },
   { thread := t, action := .init .heapSize (.word64 s.gcHeapSize) },
   { thread := t, action := .init .resident (.word64 s.bytesResident) }] ++
  (List.finRange t).map fun actor =>
    { thread := t, action := .init (.requested actor) (.word64 (s.gc_sweeps_requested actor)) }

/-- `src/gc-stock.h:172-229`; `src/gc-stock.c:1350-1663`: every scheduled
source step appends its own memory operation. Non-memory branches append no
event. The independent candidate checker determines which choices are legal. -/
def execute {p t k : Nat} : List (Scheduled p t) → State p t k →
    List (Event (Location p t) (Value p)) → State p t k × List (Event (Location p t) (Value p))
  | [], s, events => (s, events)
  | action :: rest, s, events =>
    let a := sourceAction action.actor action.reads s
    let next := sourceStep action.actor action.commit action.reads s
    match a with
    | none => execute rest next events
    | some a =>
      let e := { (Event.emit action.actor.val a action.memory) with dependsOn := (s.locals action.actor).dependencies ++ action.dependencies }
      let next := if a.readValue.isSome then
          { next with locals := put next.locals action.actor { (next.locals action.actor) with dependencies := (next.locals action.actor).dependencies ++ [events.length] } }
        else next
      execute rest next (events ++ [e])

/-- `src/gc-stock.h:172-229`; `src/gc-stock.c:1350-1663`: legal atomic
read choices are supplied by `Memory.Candidate`, without replacing relaxed
or acquire loads by sequentially consistent accesses. -/
def candidate {p t k : Nat} (schedule : List (Scheduled p t)) (s : State p t k) :
    Candidate (Location p t) (Value p) :=
  ⟨(execute schedule s (initialEvents s)).2.toArray⟩

/-- `src/gc-pages.c:126-135`: a finite checkpoint after earlier collections
left an arbitrary freed-page chain. All four actors start at alloc_page entry. -/
def freedInitial {p : Nat} (root : Option (Fin p)) (links : Fin p → Option (Fin p)) :
    State p 4 1 where
  metadata q := { next := links q, pool_n := 0, has_marked := false, has_young := false, has_weak_processing := false, nold := 0, prev_nold := 0, nfree := 0, osize := 16, fl_begin_offset := 65535, fl_end_offset := 65535, thread_n := 0, data := q }
  bottom pool := if pool = .freed then root else none
  alloc_map _ := .freed
  locals _ := { pc := .allocLazy }
  allocations _ := []
  collector _ := false
  tls_live _ := true
  physical q := q.val
  address q := UInt64.ofNat ((q.val + 1) * 16384)
  pageBytes := 16384
  osPageBytes := 4096
  windows := true
  current_sweep_full := false
  prev_sweep_full := false
  gc_allocd_scratch := false
  gc_n_threads_sweeping_pools := 0
  gc_sweeps_requested _ := 0
  global_page_pool_lazily_freed_n := 0
  gc_free_pages_keep := 0
  gc_sweep_assists_needed := 0
  gc_pages_lock := none
  gc_threads_lock := none
  epoch := 0
  stopped := false
  merged := true
  scratch_alive := false
  published := true
  gcHeapSize := 0
  bytesResident := 0
  history := []
  abaViolation := false
  mutatorViolation := false
  madvisedAllocated := false

/-- `src/gc-stock.h:161-163`; `src/gc-pages.c:127,171-174`: two freed
pages A->B, with no repeated node, pending worker, or fabricated ownership. -/
def abaInitial : State 2 4 1 :=
  freedInitial (some 0) (fun q => if q = 0 then some 1 else none)

set_option maxRecDepth 20000 in
/-- The concrete checkpoint satisfies the general finite-state assumptions.
Source: `src/gc-stock.h:99-169,320-367`. -/
theorem abaInitial_wellFormed : WellFormed abaInitial := by decide

/-- `src/gc-pages.c:111-130,171-174`: one mutator pops A from freed,
marks it allocated, fails MEM_COMMIT, and pushes A back in the same epoch. -/
def rollbackSchedule : List (Fin 4 × Bool) :=
  List.replicate 17 (1, true) ++ [(1, false)] ++ List.replicate 9 (1, true)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- This trace violates the header's premise before any concurrent node read.
Source: `src/gc-stock.h:161-163`; `src/gc-pages.c:127,171-174`. -/
theorem windows_reinserts_same_epoch :
    (run rollbackSchedule abaInitial).mutatorViolation = true := by decide

/-- `src/gc-stock.h:161-163`: a node popped by a mutator is not
reinserted into the same stack in that GC epoch. The role bit is an explicit
environment classification; the Windows witness uses one known mutator. -/
def NoABAContract : Prop :=
  ∀ p t k (s : State p t k), WellFormed s → s.mutatorViolation = false →
    ∀ schedule, (run schedule s).mutatorViolation = false

/-- `src/gc-stock.h:161-163`; `src/gc-pages.c:127,171-174`. -/
theorem NoABAContract_refuted : ¬ NoABAContract := by
  intro h
  have bad := h 2 4 1 abaInitial abaInitial_wellFormed rfl rollbackSchedule
  rw [windows_reinserts_same_epoch] at bad
  contradiction

/-- `src/gc-pages.c:192-203`: four 4-KiB GC pages share one 16-KiB OS page.
A is lazy; B->C->D are freed; the concurrent thread has a pending assist. -/
def physicalInitial : State 4 4 1 :=
  let s := freedInitial (some 1) (fun q =>
    if q = 0 then none else if h : q.val + 1 < 4 then some ⟨q.val + 1, h⟩ else none)
  { s with bottom := fun pool => if pool = .lazy then some 0 else if pool = .freed then some 1 else none, alloc_map := fun q => if q = 0 then .lazilyFreed else .freed, locals := fun actor => if actor = 3 then { pc := .freeWait } else { pc := .allocLazy }, collector := fun actor => actor == 3, physical := fun _ => 0, address := fun q => UInt64.ofNat (16384 + q.val * 4096), pageBytes := 4096, osPageBytes := 16384, windows := false, global_page_pool_lazily_freed_n := 1, gc_sweep_assists_needed := 1 }

set_option maxRecDepth 20000 in
/-- `src/gc-stock.h:151-169,320-367`; `src/gc-pages.c:192-203`. -/
theorem physicalInitial_wellFormed : WellFormed physicalInitial := by decide

/-- `src/gc-stock.h:182-184,194-198,220-224`: next accesses together with
all head loads and CAS operations that could order the conflicting pair.
The rollback writer's map/accounting accesses are private to that writer in
this prefix. The reader pauses before its CAS, so no later acquire is used
to order its earlier plain read. -/
def nextAccessCandidate {p t : Nat} (reader writer : Fin t) (node : Fin p)
    (before after : Option (Fin p)) : Candidate (Location p t) (Value p) :=
  ⟨#[
    { thread := t, action := .init (.bottom .freed) (.pointer (some node)) },
    { thread := t, action := .init (.next node) (.pointer before) },
    { thread := reader.val, action := .load (.bottom .freed) .relaxed (.pointer (some node)), readFrom := some 0 },
    { thread := reader.val, action := .plainLoad (.next node) (.pointer before), readFrom := some 1, dependsOn := [2] },
    { thread := writer.val, action := .load (.bottom .freed) .relaxed (.pointer (some node)), readFrom := some 0 },
    { thread := writer.val, action := .plainLoad (.next node) (.pointer before), readFrom := some 1, dependsOn := [4] },
    { thread := writer.val, action := .cas (.bottom .freed) .seqCst .seqCst (.pointer (some node)) (.pointer before) (.pointer (some node)), readFrom := some 0, mo := 1, sc := 0, dependsOn := [4, 5] },
    { thread := writer.val, action := .load (.bottom .freed) .relaxed (.pointer after), readFrom := some 6, dependsOn := [4, 5, 6] },
    { thread := writer.val, action := .plainStore (.next node) (.pointer after), mo := 1, dependsOn := [4, 5, 6, 7] },
    { thread := writer.val, action := .cas (.bottom .freed) .seqCst .seqCst (.pointer after) (.pointer (some node)) (.pointer after), readFrom := some 6, mo := 2, sc := 1, dependsOn := [4, 5, 6, 7] }]⟩

/-- `src/gc-stock.h:183,198,224`; `src/gc-pages.c:127,171-174`:
the two accesses must occur on one source-interpreter prefix, before any
continuation after the conflicting write. The initial next value also matches. -/
def NextSliceMatches {p t k : Nat} (s : State p t k) (reader writer : Fin t)
    (beforeRead between : List (Fin t × Bool)) (node : Fin p)
    (before after : Option (Fin p)) : Prop :=
  (s.metadata node).next = before ∧
  sourceAction reader {} (run beforeRead s) = some (.plainLoad (.next node) (.pointer before)) ∧
  sourceAction writer {} (run (beforeRead ++ [(reader, true)] ++ between) s) =
    some (.plainStore (.next node) (.pointer after))

/-- Finite checking of the source operations in `src/gc-stock.h:183,224`. -/
instance {p t k : Nat} (s : State p t k) (reader writer : Fin t)
    (beforeRead between : List (Fin t × Bool)) (node : Fin p)
    (before after : Option (Fin p)) :
    Decidable (NextSliceMatches s reader writer beforeRead between node before after) := by
  unfold NextSliceMatches
  infer_instance

/-- `src/gc-stock.h:220-224`: T0 has loaded A and is about to read A.next. -/
def nextReadPrefix : List (Fin 4 × Bool) := List.replicate 11 (0, true)

/-- `src/gc-pages.c:127,171-174`; `src/gc-stock.h:182-183`: T1 pops A,
fails MEM_COMMIT and reaches the rollback's next store. Writing the same
pointer value still conflicts with T0's ordinary read. -/
def nextWriteBetween : List (Fin 4 × Bool) :=
  List.replicate 17 (1, true) ++ [(1, false)] ++ List.replicate 4 (1, true)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- `src/gc-stock.h:183,224`: both checked accesses are actual source PCs
on the same prefix. This stops before any stale CAS or overlapping allocation. -/
theorem next_accesses_match_source :
    NextSliceMatches abaInitial 0 1 nextReadPrefix nextWriteBetween 0
      (some 1) (some 1) := by decide

/-- `src/gc-stock.h:183,224`: typed projection of the matched source read/write. -/
def nextRace : Candidate (Location 2 4) (Value 2) :=
  nextAccessCandidate 0 1 0 (some 1) (some 1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `src/gc-stock.h:183,224`: atomic consistency and ordinary race
freedom are checked separately. The violation is the ordinary race itself. -/
theorem next_pointer_race_checked :
    nextRace.consistent = true ∧ nextRace.dataRaceFree = false := by decide

theorem next_pointer_access_typed :
    nextRace.DeclaredAccessTyped declaredAccessClass := by
  unfold Candidate.DeclaredAccessTyped
  decide

/-- `src/gc-stock.h:183,198,224`: the matched ordinary next accesses
admitted by the source slice must be data-race-free. This is a race-freedom
claim, with no claim about subsequent behavior after C undefined behavior. -/
def PageNextDataRaceFreedom : Prop :=
  ∀ p t k (s : State p t k), WellFormed s →
    ∀ reader writer beforeRead between node before after,
      reader ≠ writer →
      NextSliceMatches s reader writer beforeRead between node before after →
      (nextAccessCandidate reader writer node before after).consistent = true →
      (nextAccessCandidate reader writer node before after).dataRaceFree = true

/-- `src/gc-stock.h:183,224`; `src/gc-pages.c:127,171-174`. -/
theorem PageNextDataRaceFreedom_refuted : ¬ PageNextDataRaceFreedom := by
  intro h
  have bad := h 2 4 1 abaInitial abaInitial_wellFormed 0 1
    nextReadPrefix nextWriteBetween 0 (some 1) (some 1) (by decide)
    next_accesses_match_source next_pointer_race_checked.1
  rw [show (nextAccessCandidate (0 : Fin 4) 1 (0 : Fin 2) (some 1) (some 1)).dataRaceFree =
    false from next_pointer_race_checked.2] at bad
  contradiction

/-- `src/gc-pages.c:199,130`: ordinary allocation-map accesses at one
specific neighbor's page-table byte, not atomic accesses to a whole bitmap. -/
def neighborAccessCandidate {p t : Nat} (reader writer : Fin t) (node : Fin p)
    (before after : MapState) : Candidate (Location p t) (Value p) :=
  ⟨#[
    { thread := t, action := .init (.map node) (.byte before) },
    { thread := reader.val, action := .plainLoad (.map node) (.byte before), readFrom := some 0 },
    { thread := writer.val, action := .plainStore (.map node) (.byte after), mo := 1 }]⟩

/-- `src/gc-pages.c:192-203,127-130`: a real neighbor-loop read and an
allocator's map write on one source prefix. The partition is separately
required to represent exactly the addresses visited by the physical-page loop. -/
def NeighborSliceMatches {p t k : Nat} (s : State p t k) (reader writer : Fin t)
    (beforeRead between : List (Fin t × Bool)) (node : Fin p)
    (before after : MapState) : Prop :=
  s.alloc_map node = before ∧
  sourceAction reader {} (run beforeRead s) = some (.plainLoad (.map node) (.byte before)) ∧
  sourceAction writer {} (run (beforeRead ++ [(reader, true)] ++ between) s) =
    some (.plainStore (.map node) (.byte after))

/-- Finite checking of `src/gc-pages.c:199,130`. -/
instance {p t k : Nat} (s : State p t k) (reader writer : Fin t)
    (beforeRead between : List (Fin t × Bool)) (node : Fin p) (before after : MapState) :
    Decidable (NeighborSliceMatches s reader writer beforeRead between node before after) := by
  unfold NeighborSliceMatches
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- `src/gc-pages.c:192-203`: four aligned 4-KiB GC pages exactly
partition one aligned 16-KiB OS page, including every address the C loop reads. -/
theorem physicalInitial_partition : PhysicalPagePartition physicalInitial := by decide

/-- `src/gc-pages.c:189-203`: the freeing actor is about to check B. -/
def neighborReadPrefix : List (Fin 4 × Bool) := List.replicate 13 (3, true)

/-- `src/gc-pages.c:111-130`: the allocating actor reaches B's map write. -/
def neighborWriteBetween : List (Fin 4 × Bool) := List.replicate 16 (0, true)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- `src/gc-pages.c:199,130`: both ordinary byte accesses are actual
source PCs; the trace ends at the conflict and includes no later madvise claim. -/
theorem neighbor_accesses_match_source :
    NeighborSliceMatches physicalInitial 3 0 neighborReadPrefix
      neighborWriteBetween 1 .freed .allocated := by decide

/-- `src/gc-pages.c:199,130`: the matched neighbor-byte read/write slice. -/
def neighborMapRace : Candidate (Location 4 4) (Value 4) :=
  neighborAccessCandidate 3 0 1 .freed .allocated

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- `src/gc-pages.c:199,130`: the ordinary-access checker detects the
neighbor map race, independently of any undefined continuation afterward. -/
theorem neighbor_map_race_checked :
    neighborMapRace.consistent = true ∧ neighborMapRace.dataRaceFree = false := by decide

theorem neighbor_map_access_typed :
    neighborMapRace.DeclaredAccessTyped declaredAccessClass := by
  unfold Candidate.DeclaredAccessTyped
  decide

/-- `src/gc-pages.c:192-203,130`: conditional race freedom for the
small-GC-page physical-neighbor scan. A valid address partition is required. -/
def NeighborMapDataRaceFreedom : Prop :=
  ∀ p t k (s : State p t k), WellFormed s → PhysicalPagePartition s →
    ∀ reader writer beforeRead between node before after,
      reader ≠ writer →
      NeighborSliceMatches s reader writer beforeRead between node before after →
      (neighborAccessCandidate reader writer node before after).consistent = true →
      (neighborAccessCandidate reader writer node before after).dataRaceFree = true

/-- `src/gc-pages.c:192-203,130`: this theorem asserts the race only. -/
theorem NeighborMapDataRaceFreedom_refuted : ¬ NeighborMapDataRaceFreedom := by
  intro h
  have bad := h 4 4 1 physicalInitial physicalInitial_wellFormed
    physicalInitial_partition 3 0 neighborReadPrefix neighborWriteBetween 1
    .freed .allocated (by decide) neighbor_accesses_match_source neighbor_map_race_checked.1
  rw [show (neighborAccessCandidate (3 : Fin 4) 0 (1 : Fin 4) .freed .allocated).dataRaceFree =
    false from neighbor_map_race_checked.2] at bad
  contradiction

/-- `src/gc-stock.c:1458-1460,1505`: a worker increments before loading
the scratch pointer, retains it while sweeping, then decrements on return. -/
inductive WorkerPC where
  | enter | snapshot | sweeping | returned
  deriving DecidableEq, Repr

/-- `src/gc-stock.c:1449-1452`: the atomic checkpoint ends when the
collector accepts an acquire load of zero. Source copy/merge/free is outside
this two-location model. -/
inductive CollectorPC where
  | close | count | accepted
  deriving DecidableEq, Repr

/-- `src/gc-stock.c:53-55,1449-1460,1505`: atomic checkpoint with any
finite worker population. Bool scratch is the projection of one fixed
non-NULL array identity versus NULL; it models neither addressing within
that array nor dereferencing the retained pointer. -/
structure BarrierState (threads : Nat) where
  active : UInt32
  scratch : Bool
  collectorThread : Nat := threads
  workers : Fin threads → WorkerPC
  retained : Fin threads → Bool
  dependencies : Fin threads → List Nat
  collectorDependencies : List Nat
  collector : CollectorPC

/-- `src/gc-stock.c:1458-1459,1505,1449-1450`: arbitrary read values and
explicit C11 choices. `none` selects the collecting mutator, not a GC worker. -/
structure BarrierCommand (threads : Nat) where
  worker : Option (Fin threads)
  active : UInt32 := 0
  scratch : Bool := false
  finish : Bool := false
  memory : Memory.Choice := {}

/-- `src/gc-stock.c:53-55`: the two atomic locations relevant to the
scratch lifetime handshake, with distinct pointer and counter identities. -/
inductive BarrierLocation where
  | active | scratch
  deriving DecidableEq, Repr

def barrierDeclaredAccessClass (_ : BarrierLocation) : Memory.AccessClass := .atomic

/-- `src/gc-stock.c:1449-1459,1505`: source-ordered worker and collector
steps, with each load, store and RMW emitted separately at its actual order.
No new worker is assumed to see the latest counter or pointer modification. -/
def barrierStep {t : Nat} (command : BarrierCommand t) (s : BarrierState t)
    (events : List (Event BarrierLocation Nat)) :
    BarrierState t × List (Event BarrierLocation Nat) :=
  let emit (thread : Nat) (a : Action BarrierLocation Nat) (dependencies : List Nat) :=
    events ++ [{ (Event.emit thread a command.memory) with dependsOn := dependencies }]
  match command.worker with
  | some worker =>
    match s.workers worker with
    | .enter =>
      ({ s with active := command.active + 1, workers := put s.workers worker .snapshot, dependencies := put s.dependencies worker (s.dependencies worker ++ [events.length]) },
        emit worker.val (.rmw .active .seqCst command.active.toNat (command.active + 1).toNat)
          (s.dependencies worker))
    | .snapshot =>
      ({ s with workers := put s.workers worker .sweeping, retained := put s.retained worker command.scratch, dependencies := put s.dependencies worker (s.dependencies worker ++ [events.length]) },
        emit worker.val (.load .scratch .seqCst (if command.scratch then 1 else 0))
          (s.dependencies worker))
    | .sweeping =>
      if command.finish then
        ({ s with active := command.active - 1, workers := put s.workers worker .returned, retained := put s.retained worker false },
          emit worker.val (.rmw .active .seqCst command.active.toNat (command.active - 1).toNat)
            (s.dependencies worker))
      else (s, events)
    | .returned => (s, events)
  | none =>
    match s.collector with
    | .close =>
      ({ s with scratch := false, collector := .count },
        emit s.collectorThread (.store .scratch .seqCst 0) s.collectorDependencies)
    | .count =>
      ({ s with collector := if command.active = 0 then .accepted else .count, collectorDependencies := s.collectorDependencies ++ [events.length] },
        emit s.collectorThread (.load .active .acquire command.active.toNat)
          s.collectorDependencies)
    | .accepted => (s, events)

/-- `src/gc-stock.c:1458-1460,1505,1449-1452`: finite source schedules
parameterized by all load values and all C11 read-from/MO/SC choices. -/
def barrierRun {t : Nat} : List (BarrierCommand t) → BarrierState t →
    List (Event BarrierLocation Nat) → BarrierState t × List (Event BarrierLocation Nat)
  | [], s, events => (s, events)
  | command :: rest, s, events =>
    let (next, events) := barrierStep command s events
    barrierRun rest next events

/-- `src/gc-stock.c:53-55,1449-1459`: initialization of just the two
locations touched by this source slice. Unrelated initialized fields add no
cross-thread ordering edges to the candidate. -/
def barrierInits {t : Nat} (s : BarrierState t) : List (Event BarrierLocation Nat) :=
  [{ thread := t + 1, action := .init .active s.active.toNat },
   { thread := t + 1, action := .init .scratch (if s.scratch then 1 else 0) }]

/-- `src/gc-stock.c:1449-1459,1505`: completed candidate with its actual
ordinary source sequencing and explicitly chosen atomic histories. -/
def barrierCandidate {t : Nat} (schedule : List (BarrierCommand t))
    (s : BarrierState t) : Candidate BarrierLocation Nat :=
  ⟨(barrierRun schedule s (barrierInits s)).2.toArray⟩

/-- `src/gc-stock.c:1458-1460,1505`: a counted worker is between its
entry RMW and retirement RMW, including its scratch-load program counter. -/
def countedWorker : WorkerPC → Nat
  | .snapshot | .sweeping => 1
  | _ => 0

/-- `src/gc-stock.c:53-55,1449-1459`: arbitrary well-formed barrier
checkpoints accurately count every worker and begin before collector closure.
Workers may already hold scratch, provided the counter accounts for them. -/
def BarrierWellFormed {t : Nat} (s : BarrierState t) : Prop :=
  s.active.toNat = ((List.finRange t).map fun worker => countedWorker (s.workers worker)).foldl (· + ·) 0 ∧
  (∀ worker, s.retained worker = true → s.workers worker = .sweeping) ∧
  s.collector = .close ∧ s.scratch = true

/-- `src/gc-stock.c:1449-1452`: acceptance means the acquire load read
zero and execution advanced to metadata publication or a later source stage. -/
def barrierAccepted {t : Nat} (s : BarrierState t) : Prop :=
  s.collector = .accepted

/-- Finite checking of `src/gc-stock.c:53-55,1449-1459` checkpoints. -/
instance {t : Nat} (s : BarrierState t) : Decidable (BarrierWellFormed s) := by
  unfold BarrierWellFormed
  infer_instance

/-- Finite checking of the `src/gc-stock.c:1450` branch. -/
instance {t : Nat} (s : BarrierState t) : Decidable (barrierAccepted s) := by
  unfold barrierAccepted
  infer_instance

/-- `src/gc-stock.c:1458-1459,1449-1450`: one worker has not entered
yet; the collector is about to clear a currently non-NULL scratch pointer. -/
def barrierInitial : BarrierState 1 where
  active := 0
  scratch := true
  workers _ := .enter
  retained _ := false
  dependencies _ := []
  collectorDependencies := []
  collector := .close

/-- `src/gc-stock.c:1458,1459,1449,1450`: SC order is increment,
non-NULL scratch load, NULL scratch store. The subsequent acquire count load
chooses the initial zero; it is not itself in the SC order. -/
def staleZeroSchedule : List (BarrierCommand 1) :=
  [{ worker := some 0, active := 0, memory := { readFrom := some 0, mo := 1, sc := 0 } },
   { worker := some 0, scratch := true, memory := { readFrom := some 1, sc := 1 } },
   { worker := none, memory := { mo := 1, sc := 2 } },
   { worker := none, active := 0, memory := { readFrom := some 0 } }]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- `src/gc-stock.c:1449-1459`: the execution satisfies the shared C11
consistency checker, including coherence, SC and RMW atomicity. -/
theorem stale_zero_C11_consistent :
    (barrierCandidate staleZeroSchedule barrierInitial).consistent = true := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- `src/gc-stock.c:1449-1459`: the counterexample has only atomics,
so it does not rely on an ordinary-memory data race. -/
theorem stale_zero_data_race_free :
    (barrierCandidate staleZeroSchedule barrierInitial).dataRaceFree = true := by decide

theorem stale_zero_access_typed :
    (barrierCandidate staleZeroSchedule barrierInitial).DeclaredAccessTyped
      barrierDeclaredAccessClass := by
  unfold Candidate.DeclaredAccessTyped
  decide

/-- `src/gc-stock.c:1449-1452,1458-1460`: over every finite worker
population, well-formed checkpoint, schedule, and consistent C11 read choice,
an accepted acquire-zero checkpoint must exclude a retained non-NULL scratch
pointer. No later source copy, dereference, free or worker return is claimed.
A late worker that reads NULL is permitted. -/
def AcquireZeroCheckpointExcludesRetainedScratch : Prop :=
  ∀ t (s : BarrierState t), BarrierWellFormed s → ∀ schedule,
    (barrierCandidate schedule s).consistent = true →
    (barrierCandidate schedule s).dataRaceFree = true →
    barrierAccepted (barrierRun schedule s (barrierInits s)).1 →
    ∀ worker, (barrierRun schedule s (barrierInits s)).1.retained worker = false

set_option maxRecDepth 20000 in
/-- `src/gc-stock.c:1449-1452,1458-1460`: the accepted zero is stale
while a counted worker still holds non-NULL scratch. -/
theorem AcquireZeroCheckpointExcludesRetainedScratch_refuted :
    ¬ AcquireZeroCheckpointExcludesRetainedScratch := by
  intro h
  have bad := h 1 barrierInitial (by decide) staleZeroSchedule
    stale_zero_C11_consistent stale_zero_data_race_free (by decide) 0
  exact (by decide : (barrierRun staleZeroSchedule barrierInitial
    (barrierInits barrierInitial)).1.retained 0 ≠ false) bad

/-- `src/gc-stock.c:1458-1505`: the collecting thread completes its own
sweep call before a second worker enters and pauses before the sweep loop. -/
def lifetimeBarrierInitial : BarrierState 2 where
  active := 0
  scratch := true
  collectorThread := 0
  workers _ := .enter
  retained _ := false
  dependencies _ := []
  collectorDependencies := []
  collector := .close

/-- `src/gc-stock.c:1449-1459,1505`: the collecting thread's decrement
supplies the accepted zero; the later worker retains the non-NULL pointer. -/
def lifetimeBarrierSchedule : List (BarrierCommand 2) :=
  [{ worker := some 0, active := 0,
     memory := { readFrom := some 0, mo := 1, sc := 0 } },
   { worker := some 0, scratch := true,
     memory := { readFrom := some 1, sc := 1 } },
   { worker := some 0, active := 1, finish := true,
     memory := { readFrom := some 2, mo := 2, sc := 2 } },
   { worker := some 1, active := 0,
     memory := { readFrom := some 4, mo := 3, sc := 3 } },
   { worker := some 1, scratch := true,
     memory := { readFrom := some 1, sc := 4 } },
   { worker := none, memory := { mo := 1, sc := 5 } },
   { worker := none, active := 0, memory := { readFrom := some 4 } }]

/-- `src/gc-stock.c:1591-1635`: collector control states after the accepted
zero, through the empty copy, empty merge and scratch deallocation. -/
inductive ScratchCleanupPC where
  | copyStack | mergeLoad | mergeBranch | freeScratch | done
  deriving DecidableEq, Repr

/-- `src/gc-stock.c:1458-1505,1584-1635`: scratch allocation identity,
retained worker address and collector cleanup state. -/
structure ScratchLifetimeState where
  barrier : BarrierState 2
  events : List (Event BarrierLocation Nat)
  collector : ScratchCleanupPC
  scratchAllocation : Nat
  allocationBase : Nat
  allocationWords : Nat
  allocationLive : Bool
  workerLoadedAllocation : Option Nat
  workerLoadedAddress : Option Nat
  scratchHead : Option Nat
  installedHead : Option Nat
  mergeCursor : Option Nat

/-- Source statements `src/gc-stock.c:1449-1505,1595,1609-1610,1635`. -/
inductive ScratchLifetimeCommand where
  | barrier (command : BarrierCommand 2)
  | copyStack | mergeLoad | mergeBranch | freeScratch

/-- `src/gc-stock.c:1449-1505,1591-1635`: one worker or collector source
statement, including the concrete scratch allocation identity. -/
def scratchLifetimeStep (command : ScratchLifetimeCommand)
    (s : ScratchLifetimeState) : ScratchLifetimeState :=
  match command with
  | .barrier barrierCommand =>
      let (barrier, events) := barrierStep barrierCommand s.barrier s.events
      let next := { s with barrier := barrier }
      let next := { next with events := events }
      if barrierCommand.worker = some 1 ∧
          s.barrier.workers 1 = .snapshot ∧ barrierCommand.scratch = true then
        let next := { next with workerLoadedAllocation := some s.scratchAllocation }
        { next with workerLoadedAddress := some s.allocationBase }
      else
        next
  | .copyStack =>
      if s.barrier.collector = .accepted ∧ s.collector = .copyStack then
        { s with collector := .mergeLoad, installedHead := s.scratchHead }
      else s
  | .mergeLoad =>
      if s.collector = .mergeLoad then
        { s with collector := .mergeBranch, mergeCursor := s.installedHead }
      else s
  | .mergeBranch =>
      if s.collector = .mergeBranch ∧ s.mergeCursor.isNone then
        { s with collector := .freeScratch }
      else s
  | .freeScratch =>
      if s.collector = .freeScratch then
        { s with collector := .done, allocationLive := false }
      else s

def scratchLifetimeRun : List ScratchLifetimeCommand → ScratchLifetimeState →
    ScratchLifetimeState
  | [], s => s
  | command :: rest, s => scratchLifetimeRun rest (scratchLifetimeStep command s)

def scratchLifetimeInitial : ScratchLifetimeState where
  barrier := lifetimeBarrierInitial
  events := barrierInits lifetimeBarrierInitial
  collector := .copyStack
  scratchAllocation := 1
  allocationBase := 4096
  allocationWords := 64
  allocationLive := true
  workerLoadedAllocation := none
  workerLoadedAddress := none
  scratchHead := none
  installedHead := none
  mergeCursor := none

def scratchLifetimePrefix : List ScratchLifetimeCommand :=
  lifetimeBarrierSchedule.map ScratchLifetimeCommand.barrier

def scratchLifetimeSchedule : List ScratchLifetimeCommand :=
  scratchLifetimePrefix ++ [.copyStack, .mergeLoad, .mergeBranch, .freeScratch]

def scratchLifetimeCheckpoint : ScratchLifetimeState :=
  scratchLifetimeRun scratchLifetimePrefix scratchLifetimeInitial

def scratchLifetimeFinal : ScratchLifetimeState :=
  scratchLifetimeRun scratchLifetimeSchedule scratchLifetimeInitial

def lifetimeBarrierFinal : BarrierState 2 := scratchLifetimeCheckpoint.barrier

def scratchLifetimeCandidate (schedule : List ScratchLifetimeCommand) :
    Candidate BarrierLocation Nat :=
  ⟨(scratchLifetimeRun schedule scratchLifetimeInitial).events.toArray⟩

theorem scratch_cleanup_source_pcs :
    let copied := scratchLifetimeStep .copyStack scratchLifetimeCheckpoint
    let loaded := scratchLifetimeStep .mergeLoad copied
    let branched := scratchLifetimeStep .mergeBranch loaded
    let freed := scratchLifetimeStep .freeScratch branched
    copied.collector = .mergeLoad ∧ copied.installedHead = none ∧
    loaded.collector = .mergeBranch ∧ loaded.mergeCursor = none ∧
    branched.collector = .freeScratch ∧ branched.allocationLive = true ∧
    freed.collector = .done ∧ freed.allocationLive = false := by
  decide

theorem lifetime_barrier_source_actions :
    let events := scratchLifetimeCheckpoint.events
    events.length = 9 ∧
    (events[2]?).map Event.action = some (.rmw .active .seqCst 0 1) ∧
    (events[3]?).map Event.action = some (.load .scratch .seqCst 1) ∧
    (events[4]?).map Event.action = some (.rmw .active .seqCst 1 0) ∧
    (events[5]?).map Event.action = some (.rmw .active .seqCst 0 1) ∧
    (events[6]?).map Event.action = some (.load .scratch .seqCst 1) ∧
    (events[7]?).map Event.action = some (.store .scratch .seqCst 0) ∧
    (events[8]?).map Event.action = some (.load .active .acquire 0) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem lifetime_barrier_consistent :
    (scratchLifetimeCandidate scratchLifetimeSchedule).consistent = true := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem lifetime_barrier_race_free :
    (scratchLifetimeCandidate scratchLifetimeSchedule).dataRaceFree = true := by
  decide

theorem lifetime_barrier_read_from_typed :
    (scratchLifetimeCandidate scratchLifetimeSchedule).ReadFromTyped := by
  unfold Candidate.ReadFromTyped
  decide

theorem lifetime_barrier_access_typed :
    (scratchLifetimeCandidate scratchLifetimeSchedule).DeclaredAccessTyped
      barrierDeclaredAccessClass := by
  unfold Candidate.DeclaredAccessTyped
  decide

theorem lifetime_source_pcs :
    lifetimeBarrierFinal.workers 0 = .returned ∧
    lifetimeBarrierFinal.workers 1 = .sweeping ∧
    lifetimeBarrierFinal.collector = .accepted ∧
    lifetimeBarrierFinal.active = 1 ∧
    lifetimeBarrierFinal.retained 1 = true := by
  decide

theorem lifetime_ends_with_loaded_address_history :
    scratchLifetimeFinal.collector = .done ∧
    scratchLifetimeFinal.barrier.workers 1 = .sweeping ∧
    scratchLifetimeFinal.workerLoadedAllocation =
      some scratchLifetimeFinal.scratchAllocation ∧
    scratchLifetimeFinal.workerLoadedAddress = some 4096 ∧
    scratchLifetimeFinal.allocationLive = false ∧
    scratchLifetimeFinal.scratchHead = none ∧
    scratchLifetimeFinal.installedHead = none ∧
    scratchLifetimeFinal.mergeCursor = none ∧
    scratchLifetimeFinal.allocationBase ≤ 4096 ∧
    4096 < scratchLifetimeFinal.allocationBase + scratchLifetimeFinal.allocationWords := by
  decide

/-- `src/gc-stock.c:1458-1505,1584-1635`: cleanup preserves the allocation
when ghost history records a paused worker's earlier scratch-base load. -/
def LoadedScratchLifetimeSafety : Prop :=
  ∀ schedule address,
    let final := scratchLifetimeRun schedule scratchLifetimeInitial
    (scratchLifetimeCandidate schedule).consistent = true →
    (scratchLifetimeCandidate schedule).dataRaceFree = true →
    (scratchLifetimeCandidate schedule).ReadFromTyped →
    (scratchLifetimeCandidate schedule).DeclaredAccessTyped barrierDeclaredAccessClass →
    final.collector = .done →
    final.barrier.workers 1 = .sweeping →
    final.barrier.collector = .accepted →
    final.barrier.retained 1 = true →
    final.workerLoadedAllocation = some final.scratchAllocation →
    final.workerLoadedAddress = some address →
    final.allocationBase ≤ address →
    address < final.allocationBase + final.allocationWords →
    final.allocationLive = true

theorem LoadedScratchLifetimeSafety_refuted : ¬ LoadedScratchLifetimeSafety := by
  intro safe
  have live := safe scratchLifetimeSchedule 4096 lifetime_barrier_consistent
    lifetime_barrier_race_free lifetime_barrier_read_from_typed
    lifetime_barrier_access_typed (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact (by decide : scratchLifetimeFinal.allocationLive ≠ true) live

/-- `src/gc-stock.c:1449-1505,1584-1635`: accepted zero excludes both a
retained scratch pointer and cleanup ending its allocation lifetime. -/
def AcquireZeroExcludesRetainedScratch : Prop :=
  AcquireZeroCheckpointExcludesRetainedScratch ∧ LoadedScratchLifetimeSafety

theorem AcquireZeroExcludesRetainedScratch_refuted :
    ¬ AcquireZeroExcludesRetainedScratch := by
  intro safe
  exact LoadedScratchLifetimeSafety_refuted safe.2

/-- `src/gc-stock.h:102,194-224`: a ghost certificate for the actual
nullable head and metadata next links. The stack remains a linked structure. -/
def Linked {p : Nat} (links : Fin p → Option (Fin p)) :
    Option (Fin p) → List (Fin p) → Prop
  | head, [] => head = none
  | head, q :: rest => head = some q ∧ Linked links (links q) rest

/-- `src/gc-stock.h:193-201,219-227`: pop-helper local values. -/
structure EpochFrame (p : Nat) where
  pc : StackPC := .load
  old_back : Option (Fin p) := none
  next : Option (Fin p) := none

/-- `src/gc-stock.c:1471-1479`; `src/gc-stock.h:159-169,193-201`:
one allocated-page input stack during its parallel-pop epoch. Prescan has
finished, and no caller pushes onto this input stack. Sweeping may rewrite
removed nodes' next fields while pushing them onto distinct destination stacks.
`results` is the successful CAS return-value log, recorded at linearization. -/
structure PopEpoch (p t : Nat) where
  head : Option (Fin p)
  next : Fin p → Option (Fin p)
  frames : Fin t → EpochFrame p
  results : List (Fin p)

/-- `src/gc-stock.h:194-224`: actual atomic head and plain next locations. -/
inductive EpochLocation (p : Nat) where
  | head
  | next (q : Fin p)
  deriving DecidableEq, Repr

def epochDeclaredAccessClass : EpochLocation p → Memory.AccessClass
  | .head => .atomic
  | .next _ => .ordinary

/-- `src/gc-stock.h:194-224`: update one pop-helper's local registers. -/
def epochFrame {p t : Nat} (s : PopEpoch p t) (actor : Fin t)
    (f : EpochFrame p) : PopEpoch p t := { s with frames := put s.frames actor f }

/-- `src/gc-stock.h:193-201,219-227`; `src/gc-stock.c:1471-1479`:
source pop steps for an input stack with no incoming pushes. This is the
documented non-reinsertion premise for the parallel-sweep input stack, not a
condition on the result log. Relaxed head loads may choose stale values. Next
reads use the current plain field; race-free admission is required below.
Writes to removed metadata are allowed and never republish the input head. -/
inductive PopEpochStep {p t : Nat} : PopEpoch p t → Fin t →
    Option (Action (EpochLocation p) (Option (Fin p))) → PopEpoch p t → Prop where
  | load (s : PopEpoch p t) (a : Fin t) (seen : Option (Fin p))
      (pc : (s.frames a).pc = .load) :
      PopEpochStep s a (some (.load .head .relaxed seen))
        (epochFrame s a { (s.frames a) with pc := .test, old_back := seen })
  | empty (s : PopEpoch p t) (a : Fin t)
      (pc : (s.frames a).pc = .test) (old : (s.frames a).old_back = none) :
      PopEpochStep s a none (epochFrame s a { (s.frames a) with pc := .ret })
  | nonempty (s : PopEpoch p t) (a : Fin t) (q : Fin p)
      (pc : (s.frames a).pc = .test) (old : (s.frames a).old_back = some q) :
      PopEpochStep s a none (epochFrame s a { (s.frames a) with pc := .readNext })
  | readNext (s : PopEpoch p t) (a : Fin t) (q : Fin p)
      (pc : (s.frames a).pc = .readNext) (old : (s.frames a).old_back = some q) :
      PopEpochStep s a (some (.plainLoad (.next q) (s.next q)))
        (epochFrame s a { (s.frames a) with pc := .exchange, next := s.next q })
  | success (s : PopEpoch p t) (a : Fin t) (q : Fin p)
      (pc : (s.frames a).pc = .exchange) (old : (s.frames a).old_back = some q)
      (head : s.head = some q) :
      PopEpochStep s a
        (some (.cas .head .seqCst .seqCst (some q) (s.frames a).next (some q)))
        (epochFrame { s with head := (s.frames a).next, results := s.results ++ [q] }
          a { (s.frames a) with pc := .ret })
  | failure (s : PopEpoch p t) (a : Fin t)
      (pc : (s.frames a).pc = .exchange) (head : s.head ≠ (s.frames a).old_back) :
      PopEpochStep s a
        (some (.cas .head .seqCst .seqCst (s.frames a).old_back (s.frames a).next s.head))
        (epochFrame s a { (s.frames a) with pc := .pause, old_back := s.head })
  | pause (s : PopEpoch p t) (a : Fin t) (pc : (s.frames a).pc = .pause) :
      PopEpochStep s a none (epochFrame s a { (s.frames a) with pc := .load })
  | nextCall (s : PopEpoch p t) (a : Fin t) (pc : (s.frames a).pc = .ret) :
      PopEpochStep s a none (epochFrame s a { pc := .load })
  | rewriteRemoved (s : PopEpoch p t) (a : Fin t) (q : Fin p)
      (value : Option (Fin p)) (owned : q ∈ s.results) :
      PopEpochStep s a (some (.plainStore (.next q) value))
        { s with next := put s.next q value }

/-- `src/gc-stock.h:172-229`: all finite source interleavings and memory
choices for the input-stack epoch. Each memory event has the step's exact
thread, action and scalar values. C11 consistency and ordinary race freedom
remain independent conditions on the completed execution. -/
inductive PopEpochTrace {p t : Nat} : PopEpoch p t →
    List (Event (EpochLocation p) (Option (Fin p))) → PopEpoch p t → Prop where
  | nil (s : PopEpoch p t) : PopEpochTrace s [] s
  | control {s next final : PopEpoch p t} (a : Fin t)
      (step : PopEpochStep s a none next)
      (tail : PopEpochTrace next events final) : PopEpochTrace s events final
  | memory {s next final : PopEpoch p t} (a : Fin t)
      (action : Action (EpochLocation p) (Option (Fin p)))
      (step : PopEpochStep s a (some action) next)
      (choice : Memory.Choice) (dependencies : List Nat)
      (tail : PopEpochTrace next events final) :
      PopEpochTrace s ({ (Event.emit a.val action choice) with dependsOn := dependencies } :: events) final

/-- `src/gc-stock.h:194-224`: source checkpoint before any helper loads. -/
def epochInitial {p t : Nat} (head : Option (Fin p))
    (links : Fin p → Option (Fin p)) : PopEpoch p t :=
  { head := head, next := links, frames := fun _ => {}, results := [] }

/-- `src/gc-stock.h:102,194-224`: initial head and metadata fields.
Initialization represents the completed pre-execution publication checkpoint;
`.next` then has only ordinary non-init accesses in `PopEpochStep`. -/
def epochCandidate {p t : Nat} (initial : PopEpoch p t)
    (events : List (Event (EpochLocation p) (Option (Fin p)))) :
    Candidate (EpochLocation p) (Option (Fin p)) :=
  let headEvent : Event (EpochLocation p) (Option (Fin p)) :=
    { thread := t, action := .init .head initial.head }
  let nextEvents : List (Event (EpochLocation p) (Option (Fin p))) :=
    (List.finRange p).map fun q => { thread := t, action := .init (.next q) (initial.next q) }
  ⟨(headEvent :: (nextEvents ++ events)).toArray⟩

/-- `src/gc-stock.h:159-169,194-224`: a proof invariant tying actual head
and next fields to the remaining suffix. Cached successors need agree only
for nodes still in the input stack. Distinct successful results are derived
from this invariant and the initial acyclic chain, not assumed here. -/
def EpochInvariant {p t : Nat} (links : Fin p → Option (Fin p))
    (original remaining : List (Fin p)) (s : PopEpoch p t) : Prop :=
  original = s.results ++ remaining ∧ Linked links s.head remaining ∧
  (∀ q ∈ remaining, s.next q = links q) ∧
  (∀ a, (s.frames a).pc = .exchange → ∀ q,
    (s.frames a).old_back = some q → q ∈ remaining → (s.frames a).next = links q)

private theorem nodup_prefix {α : Type} {left right : List α}
    (h : (left ++ right).Nodup) : left.Nodup := by
  induction left with
  | nil => simp
  | cons q rest ih =>
    have hs := List.nodup_cons.mp h
    exact List.nodup_cons.mpr ⟨fun hq => hs.1 (List.mem_append.mpr (Or.inl hq)), ih hs.2⟩

private theorem nodup_separates {α : Type} {left right : List α}
    (h : (left ++ right).Nodup) : ∀ q ∈ left, q ∉ right := by
  induction left with
  | nil => simp
  | cons x rest ih =>
    have hs := List.nodup_cons.mp h
    intro q hq hr
    rcases List.mem_cons.mp hq with hx | hq
    · subst q
      exact hs.1 (List.mem_append.mpr (Or.inr hr))
    · exact ih hs.2 q hq hr

private theorem epoch_frame_preserves {p t : Nat} {links : Fin p → Option (Fin p)}
    {original remaining : List (Fin p)} {s : PopEpoch p t}
    (h : EpochInvariant links original remaining s) (a : Fin t) (f : EpochFrame p)
    (fresh : f.pc = .exchange → ∀ q, f.old_back = some q →
      q ∈ remaining → f.next = links q) :
    EpochInvariant links original remaining (epochFrame s a f) := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro b hb q hq hmem
  by_cases hba : b = a
  · subst b
    simp only [epochFrame, put] at hb hq ⊢
    exact fresh hb q hq hmem
  · simp only [epochFrame, put, hba] at hb hq ⊢
    exact h.2.2.2 b hb q hq hmem

private theorem epoch_noncas_preserves {p t : Nat} {links : Fin p → Option (Fin p)}
    {original remaining : List (Fin p)} {s : PopEpoch p t}
    (h : EpochInvariant links original remaining s) (a : Fin t) (f : EpochFrame p)
    (fresh : f.pc ≠ .exchange) :
    EpochInvariant links original remaining (epochFrame s a f) :=
  epoch_frame_preserves h a f (fun hp => False.elim (fresh hp))

/-- `src/gc-stock.h:183,194-224`: each actual source step preserves the
linked suffix invariant. Rewriting a removed node cannot alter a live link. -/
theorem pop_epoch_step_preserves {p t : Nat} {links : Fin p → Option (Fin p)}
    {original remaining : List (Fin p)} {s next : PopEpoch p t} {a action}
    (hn : original.Nodup) (h : EpochInvariant links original remaining s)
    (step : PopEpochStep s a action next) :
    ∃ remaining', EpochInvariant links original remaining' next := by
  cases step with
  | load seen pc =>
    exact ⟨remaining, epoch_noncas_preserves h a _ (by simp)⟩
  | empty pc old =>
    exact ⟨remaining, epoch_noncas_preserves h a _ (by simp)⟩
  | nonempty q pc old =>
    exact ⟨remaining, epoch_noncas_preserves h a _ (by simp)⟩
  | readNext q pc old =>
    refine ⟨remaining, epoch_frame_preserves h a _ ?_⟩
    intro _ r hr hmem
    have heq : q = r := Option.some.inj (old.symm.trans hr)
    subst r
    exact h.2.2.1 q hmem
  | success q pc old head =>
    cases remaining with
    | nil =>
      have hh : s.head = none := h.2.1
      rw [head] at hh
      contradiction
    | cons r rest =>
      have hh : s.head = some r := h.2.1.1
      have heq : q = r := Option.some.inj (head.symm.trans hh)
      subst r
      have saved : (s.frames a).next = links q := h.2.2.2 a pc q old (by simp)
      refine ⟨rest, epoch_noncas_preserves ?_ a _ (by simp)⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [List.append_assoc] using h.1
      · simpa [saved] using h.2.1.2
      · intro r hr
        exact h.2.2.1 r (List.mem_cons.mpr (Or.inr hr))
      · intro b hb r hold hr
        exact h.2.2.2 b hb r hold (List.mem_cons.mpr (Or.inr hr))
  | failure pc head =>
    exact ⟨remaining, epoch_noncas_preserves h a _ (by simp)⟩
  | pause pc =>
    exact ⟨remaining, epoch_noncas_preserves h a _ (by simp)⟩
  | nextCall pc =>
    exact ⟨remaining, epoch_noncas_preserves h a _ (by simp)⟩
  | rewriteRemoved q value owned =>
    refine ⟨remaining, h.1, h.2.1, ?_, h.2.2.2⟩
    intro r hr
    have hd : q ∉ remaining := nodup_separates (h.1 ▸ hn) q owned
    have hne : r ≠ q := fun heq => hd (heq ▸ hr)
    simpa [put, hne] using h.2.2.1 r hr

private theorem epoch_trace_preserves {p t : Nat} {links : Fin p → Option (Fin p)}
    {original remaining : List (Fin p)} {s final : PopEpoch p t} {events}
    (hn : original.Nodup) (h : EpochInvariant links original remaining s)
    (trace : PopEpochTrace s events final) :
    ∃ remaining', EpochInvariant links original remaining' final := by
  induction trace generalizing remaining with
  | nil => exact ⟨remaining, h⟩
  | control a step tail ih =>
    obtain ⟨rest, hi⟩ := pop_epoch_step_preserves hn h step
    exact ih hi
  | memory a action step choice dependencies tail ih =>
    obtain ⟨rest, hi⟩ := pop_epoch_step_preserves hn h step
    exact ih hi

private theorem linked_transport {p : Nat} {first second : Fin p → Option (Fin p)}
    {head : Option (Fin p)} {nodes : List (Fin p)} (h : Linked first head nodes)
    (same : ∀ q ∈ nodes, second q = first q) : Linked second head nodes := by
  induction nodes generalizing head with
  | nil => exact h
  | cons q rest ih =>
    refine ⟨h.1, ?_⟩
    have ht := ih h.2 (fun r hr => same r (List.mem_cons.mpr (Or.inr hr)))
    simpa [same q (by simp)] using ht

/-- `src/gc-stock.h:159-169,193-201,219-227`; `src/gc-stock.c:1471-1479`:
for every finite pop-only input-stack epoch, a valid initial linked chain and
the documented lack of reinsertion imply distinct successful pop results and
disjoint ownership of returned nodes versus the actual remaining chain.
The C interpretation additionally requires consistent and data-race-free
accesses. No uniqueness of the result log is assumed. -/
def PopEpochDistinctResults : Prop :=
  ∀ p t (links : Fin p → Option (Fin p)) head nodes,
    Linked links head nodes → nodes.Nodup →
    ∀ (final : PopEpoch p t) events,
      PopEpochTrace (epochInitial head links) events final →
      (epochCandidate (epochInitial head links : PopEpoch p t) events).defined = true →
      final.results.Nodup ∧ ∃ remaining,
        Linked final.next final.head remaining ∧
        ∀ q ∈ final.results, q ∉ remaining

/-- `src/gc-stock.h:159-169,193-201,219-227`; `src/gc-stock.c:1471-1479`. -/
theorem PopEpochDistinctResults_proven : PopEpochDistinctResults := by
  intro p t links head nodes hchain hn final events trace _
  have hi : EpochInvariant links nodes nodes (epochInitial head links : PopEpoch p t) := by
    refine ⟨by simp [epochInitial], hchain, ?_, ?_⟩
    · intro q _; rfl
    · intro a ha
      simp [epochInitial] at ha
  obtain ⟨remaining, hf⟩ := epoch_trace_preserves hn hi trace
  have hall : (final.results ++ remaining).Nodup := hf.1 ▸ hn
  exact ⟨nodup_prefix hall, remaining,
    linked_transport hf.2.1 hf.2.2.1, nodup_separates hall⟩

/-- Source-level claims at bbfa0ce4150. Race findings stop at the
conflicting ordinary accesses. The scratch-lifetime trace records only the
worker's pre-free load and stops before line 1471 pointer arithmetic,
dereference or decrement. -/
def entries : List JuliaLean.Registry.Entry := [
  { id := "c-runtime-page-no-aba-contract", juliaFile := "src/gc-pages.c", juliaFns := ["jl_gc_alloc_page: Windows MEM_COMMIT failure", "push_lf_back", "pop_lf_back"], statement := "A mutator-popped page is not reinserted into the same stack in the same GC epoch.", source := "bbfa0ce4150 src/gc-stock.h:161-163; src/gc-pages.c:127,171-174", status := .refuted, refutationEvidence := .modelCounterexample, prop := ``NoABAContract, thm := some ``NoABAContract_refuted, issue := "#64149 (open, duplicate); #62162, #62274 (merged, related); queries: MEM_COMMIT global_page_pool_freed; gc page pool ABA commit failure", notes := "One mutator pops a freed page, fails MEM_COMMIT and republishes that page to the freed stack before throwing. This defined single-thread source path refutes the mutator epoch rule. No claim is made about the separate GC-thread forever rule or Windows API internals." },
  { id := "c-runtime-page-next-data-race", juliaFile := "src/gc-stock.h", juliaFns := ["push_lf_back", "pop_lf_back", "jl_gc_alloc_page"], statement := "Source-matched ordinary metadata next reads and rollback next writes are data-race-free.", source := "bbfa0ce4150 src/gc-stock.h:183,198,224; src/gc-pages.c:127,171-174", status := .refuted, refutationEvidence := .modelCounterexample, prop := ``PageNextDataRaceFreedom, thm := some ``PageNextDataRaceFreedom_refuted, issue := "#64149 (open, duplicate); #62162, #62274 (merged, related); queries: MEM_COMMIT global_page_pool_freed; gc page pool ABA commit failure", notes := "The source-PC checks locate a plain next read and rollback write on one prefix. The typed memory slice is consistent and fails the ordinary-access race check. No ownership, duplicate-pop or allocation-map outcome after undefined behavior is registered." },
  { id := "c-runtime-page-neighbor-map-data-race", juliaFile := "src/gc-pages.c", juliaFns := ["jl_gc_free_page", "jl_gc_alloc_page", "gc_alloc_map_is_set", "gc_alloc_map_set"], statement := "With GC_PAGE_SZ < jl_page_size and a valid physical-page partition, source-matched neighbor-map reads and allocation-map writes are data-race-free.", source := "bbfa0ce4150 src/gc-pages.c:192-203,130; src/gc-stock.h:325-366", status := .refuted, refutationEvidence := .modelCounterexample, prop := ``NeighborMapDataRaceFreedom, thm := some ``NeighborMapDataRaceFreedom_refuted, issue := "none found (queries: gc_alloc_map jl_gc_free_page race)", notes := "The witness has four aligned 4-KiB GC pages exactly covering one 16-KiB OS page. Source-PC checks match one neighbor-byte read and its concurrent allocation write. The ordinary race is the result; no later madvise outcome for defined C is claimed." },
  { id := "c-runtime-page-acquire-zero-retained-scratch", juliaFile := "src/gc-stock.c", juliaFns := ["gc_sweep_pool_parallel", "gc_sweep_wait_for_all_pages", "gc_sweep_pool"], statement := "After an accepted acquire-zero counter read, no worker retains the previous non-NULL scratch pointer and cleanup does not end the scratch allocation while execution history records a still-paused worker's earlier non-NULL base load.", source := "bbfa0ce4150 src/gc-stock.c:1449-1505,1584-1635", status := .refuted, refutationEvidence := .modelCounterexample, prop := ``AcquireZeroExcludesRetainedScratch, thm := some ``AcquireZeroExcludesRetainedScratch_refuted, issue := "none found (queries: gc_n_threads_sweeping_pools gc_allocd_scratch; page sweep scratch stale counter)", notes := "The checkpoint prefix accepts zero while a worker retains the non-NULL scratch pointer. The lifetime trace adds the collecting thread's own +1/load/-1 call, a later worker +1 and concrete base load, the close and acquire-zero that reads the collecting thread's earlier decrement, empty copy and merge steps, and scratch deallocation. Its memory projection is C11-consistent, data-race-free, read-from typed and declaration typed. The loaded-address field is ghost history of the pre-free load while the worker remains paused. No post-free C pointer value is evaluated or asserted, and no line 1471 pointer arithmetic, dereference, use-after-free, crash or current hardware manifestation is modeled." },
  { id := "c-runtime-page-pop-epoch-distinct-results", juliaFile := "src/gc-stock.h", juliaFns := ["try_pop_lf_back", "pop_lf_back", "gc_sweep_pool_parallel"], statement := "In a pop-only parallel-sweep input-stack epoch, successful pop results are distinct and disjoint from the remaining linked stack.", source := "bbfa0ce4150 src/gc-stock.h:159-169,193-201,219-227; src/gc-stock.c:1471-1479", status := .proven, prop := ``PopEpochDistinctResults, thm := some ``PopEpochDistinctResults_proven, notes := "The theorem quantifies over arbitrary finite pages, workers, valid initial linked chains and source-step interleavings. Input-stack reinsertion is excluded for this documented phase; removed next fields may be rewritten for other destination stacks. C11 consistency and ordinary race freedom are explicit admission conditions. Result uniqueness follows from the invariant and is never a precondition." }
]

end JuliaLean.CRuntime.PagePool

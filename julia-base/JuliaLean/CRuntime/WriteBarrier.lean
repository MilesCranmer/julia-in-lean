import JuliaLean.CRuntime.WriteBarrier.Counterexamples

namespace JuliaLean.CRuntime.WriteBarrier

open JuliaLean.Registry

def entries : List Entry := [
  { id := "cruntime-writebarrier-quick-start-coverage"
    juliaFile := "src/gc-wb-stock.h"
    juliaFns := ["jl_svecset", "jl_gc_wb", "jl_gc_queue_root", "arraylist_push"]
    statement := "Every complete valid sequential scalar-write history preserves quick-start old-to-young coverage, including malloc/realloc failure."
    source := "bbfa0ce4150 src/support/arraylist.c:40-70; src/support/dtypes.h:129-130; src/gc-stock.c:1679-1682; src/julia.h:1372-1383"
    status := .refuted
    refutationEvidence := .modelCounterexample
    prop := ``QuickStartCoverage
    thm := some ``quickStartCoverage_refuted
    issue := "none found (queries: arraylist_push malloc failure; arraylist_grow NULL; remset allocation failure GC; arraylist OOM overwrite)"
    notes := "The 29-entry inline TLS checkpoint is reached from an empty initialized array by induction over 29 complete source invocations. On call 30, malloc returns NULL, arraylist_grow leaves len/max/items unchanged, and arraylist_push overwrites entry 28. The old owner 28 retains an unmarked strong child but loses its remembered entry after OLD was cleared. Every read follows the sequential source state. This is a model-level allocator-failure counterexample; no runtime Julia crash is claimed." },
  { id := "cruntime-writebarrier-allocation-success-coverage"
    juliaFile := "src/gc-wb-stock.h"
    juliaFns := ["jl_gc_wb", "jl_gc_wb_object", "jl_gc_multi_wb", "jl_gc_queue_root"]
    statement := "Compositionally, successful representable arraylist executions preserve quick-start coverage under the prior-generation invariant, private TLS cursor and observation contracts, completed stopped boundaries, stable mark headers, previousFull preservation, image-mutex publication, and LastWriterContract's coherent header and final-field observations."
    source := "bbfa0ce4150 src/gc-interface.h:315,323-345,355-366; src/gc-wb-stock.h:19-130; src/gc-stock.c:1671-1748,3383-3391; src/support/arraylist.c:40-70"
    status := .proven
    prop := ``AllocationSuccessfulQuickStartCoverage
    thm := some ``allocationSuccessfulQuickStartCoverage_proven
    notes := "SuccessfulProtocolPrefix restricts the source transition relation to successful malloc/realloc outcomes and representable new lengths. The proof composes source-PC invocation claims, private TLS publication and completed successful image-lock sections using the arraylist microprogram. It requires the prior generation invariant, valid completed no-safepoint callers, TLS observations, previousFull preservation and LastWriterContract's coherent header/final-field observations. Standard-C11 header race freedom and unconditional allocation-failure coverage are separately refuted." },
  { id := "cruntime-writebarrier-arraylist-allocation-outcomes"
    juliaFile := "src/support/arraylist.c"
    juliaFns := ["arraylist_grow", "arraylist_push", "jl_gc_queue_root", "gc_mark_push_remset"]
    statement := "The TLS, permanent-image and marker-rebuild callers retain both malloc/realloc success and failure, with the exact source continuation."
    source := "bbfa0ce4150 src/support/arraylist.c:40-70; src/support/dtypes.h:129-130; src/gc-stock.c:1681,1692,1820"
    status := .proven
    prop := ``ArrayListAllocationOutcomes
    thm := some ``arrayListAllocationOutcomes_proven
    notes := "Each caller uses arrayListInstruction. NULL returns directly to push's length/storage reloads; non-NULL reaches memcpy and storage/capacity publication for inline growth, or storage/capacity publication for realloc. The source transition relation also retains unsigned word wrapping and the zero-length invalid-access path. Allocation identity and byte addressing are external primitives." },
  { id := "cruntime-writebarrier-reachable-before-sweep"
    juliaFile := "src/gc-stock.c"
    juliaFns := ["gc_queue_remset", "gc_mark_outrefs", "gc_mark_loop", "_jl_gc_collect"]
    statement := "Every strongly reachable object is marked before a successful quick sweep, under the explicit source-scan and queue refinement contracts."
    source := "bbfa0ce4150 src/gc-stock.c:1906-2235,2475-2803,3092-3115,3383-3406,1015-1043"
    status := .proven
    prop := ``ReachableBeforeSweep
    thm := some ``reachableBeforeSweep_proven
    notes := "Compositional closure theorem. MarkQueueRefinement supplies TLS/image remset seeds, fresh work, root marking and a full ScanCertificate for each work owner, including tail-call work and all suffix chunks. MarkHeaderContract supplies coherent whole-header observations and persistent marks; fields are frozen. Symbols are always marked by the source invariant at src/gc-stock.c:2491-2492. Task, cancellation, wait-entry, genericmemory-owner and foreign-callback dispatches use supplied strong-edge certificates." },
  { id := "cruntime-writebarrier-queue-root-once"
    juliaFile := "src/gc-stock.c"
    juliaFns := ["jl_gc_queue_root"]
    statement := "At most one queue-root RMW acquires the remembered-set append duty for an object in a mutator epoch."
    source := "bbfa0ce4150 src/gc-stock.c:1675-1687; src/julia_atomics.h:139-140,227"
    status := .proven
    prop := ``QueueRootAtMostOnce
    thm := some ``queueRootAtMostOnce_proven
    notes := "Quantifies over all finite C11-consistent candidates and modification orders. Uses the immediate-predecessor rule for relaxed RMWs, including interposed image-remset RMWs. HeaderEpoch excludes collector old-bit resets; the statement concerns claim uniqueness, independently of ordinary-access race freedom." },
  { id := "cruntime-writebarrier-remset-drain-reset"
    juliaFile := "src/gc-stock.c"
    juliaFns := ["gc_queue_remset", "gc_mark_push_remset", "_jl_gc_collect"]
    statement := "Under a target contract where packed nptr fits uintptr_t and the current and resulting remset counters are nonnegative and INT_MAX-representable, drain, rebuild and quick/full reset execute their exact source stores and preserve the specified storage and counter fields."
    source := "bbfa0ce4150 src/gc-stock.c:1812-1826,3092-3104,3685-3700; src/gc-tls-stock.h:27-30"
    status := .proven
    prop := ``RemsetDrainReset
    thm := some ``remsetDrainReset_proven
    notes := "The actual collector PCs clear length then counter during drain and rebuild only when old and refyoung are set. RemsetCounterTargetContract requires packed nptr to fit the configured uintptr_t width and the current C int and addition result to be nonnegative and at most INT_MAX; remsetCounterResult_exact proves the assigned 32-bit value denotes that mathematical sum. Quick reset retains rebuilt entries and writes MARKED headers. Full reset clears length only and preserves remset_nptr. Counter INT_MAX++ in queue-root enters explicit undefinedArithmetic." },
  { id := "cruntime-writebarrier-bulk-copy-coverage"
    juliaFile := "src/gc-wb-stock.h"
    juliaFns := ["jl_gc_genericmemory_copy_boxed", "jl_gc_genericmemory_copy_ptr", "memmove_refs"]
    statement := "Conditional on a supplied finite C-entry memory/layout/address-to-slot model satisfying CallValid, TargetsCall and InvocationRun, a completed boxed or inline copy with equal source/destination datatype IDs, destination-derived owner and inline layout, valid spans/count, offset count equal to npointers, every pointer offset below stride, and each selected unmarked destination target supplied as a scanned slot paired with a copied source slot emits a queue-root claim before returning."
    source := "bbfa0ce4150 src/genericmemory.c:222-250; src/gc-wb-stock.h:78-130; src/julia.h:1426-1437; src/gc-interface.h:355-366"
    status := .proven
    prop := ``BulkCopyCoverage
    thm := some ``bulkCopyCoverage_proven
    notes := "GenericMemoryEntry is the supplied finite C-entry relation: its boxed and inline constructors require source/destination datatype identity as genericmemory.c:226-229 and fix call source object, destination owner, addresses and n from the two genericmemory IDs. Inline Call.copyLayout reads the supplied destination datatype table; GenericMemoryCallConstruction requires the table-wide pointerOffsets.length = npointers invariant and bounds both modeled spans. BulkCopyConstruction also requires every pointer offset to be below copyStride, and preserves the copy-before-scan PCs, memmove direction, relaxed pointer loads, release stores, four-pointer threshold, target-width n*stride and n*npointers wrapping, complete modeled address mappings and owner checks. CallPointerActionsTyped ties scalarAtomic and every multi/copy load, store and scan slot to the Config-supplied slotAtomic declaration. TargetsCall supplies the selected unmarked destination as a scanned slot paired with a copied source slot. The theorem does not prove Julia MemoryRef pointer provenance or alignment, does not derive these finite tables from runtime allocations, and does not claim actual Julia callers establish CallValid, TargetsCall or InvocationRun." },
  { id := "cruntime-writebarrier-header-data-race"
    juliaFile := "src/gc-wb-stock.h"
    juliaFns := ["jl_gc_wb_object", "jl_gc_queue_root"]
    statement := "Every atomic-memory-consistent replay of the modeled source PCs for valid concurrent whole-object write barriers is free of unordered conflicting accesses to a modeled GC header."
    source := "bbfa0ce4150 src/julia.h:171-187; src/gc-wb-stock.h:19-29; src/gc-stock.c:1675-1679"
    status := .refuted
    refutationEvidence := .modelCounterexample
    prop := ``HeaderAccessDataRaceFreedom
    thm := some ``headerAccessDataRaceFreedom_refuted
    issue := "#64205 (open, duplicate); queries: jl_gc_queue_root data race; GC header atomic bitfield race; write barrier header atomic"
    notes := "Concrete source-schedule replay: two threads read OLD_MARKED through ordinary bitfield accesses and then issue relaxed atomic whole-header fetch-and RMWs at the same location. Read-from typing and atomic-memory consistency hold, while dataRaceFree fails under C11 5.1.2.4p25. Independently, DeclaredAccessTyped fails because the modeled GC header is declared ordinary. The history ends before the winning append; no Defined execution or native crash is inferred." }
]

end JuliaLean.CRuntime.WriteBarrier

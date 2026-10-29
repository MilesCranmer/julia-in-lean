import JuliaLean.CRuntime.WriteBarrier.Collector

namespace JuliaLean.CRuntime.WriteBarrier

open JuliaLean.CRuntime.Memory

/-- `bbfa0ce4150 src/gc-stock.c:1928-1930,2061-2068,2136-2144,
2746-2800`: strong graph edges through actual layout offsets. -/
def Edge (c : Config) (h : Heap c) (parent child : ObjectId c) : Prop :=
  ∃ offset ∈ (c.layout parent).traceOffsets,
    ∃ slot, c.field parent offset = some slot ∧ h.pointers slot = some child

/-- `bbfa0ce4150 src/gc-stock.c:3393-3406,2475-2803`: arbitrary-length
strong reachability from the registered roots. -/
inductive Reachable (c : Config) (h : Heap c) : ObjectId c → Prop where
  | root {object} : object ∈ h.roots → Reachable c h object
  | edge {parent child} : Reachable c h parent → Edge c h parent child → Reachable c h child

/-- `bbfa0ce4150 src/gc-stock.c:3092-3104`: active remembered entries. -/
def InRemset (c : Config) (h : Heap c) (object : ObjectId c) : Prop :=
  ∃ tid index, index < (h.remset tid).len ∧ (h.remset tid).items index = some object

/-- `bbfa0ce4150 src/gc-stock.c:1686-1693,3107-3115`:
active permanent image-remset entries. -/
def InImageRemset (c : Config) (h : Heap c) (object : ObjectId c) : Prop :=
  h.imageRemset.contains object

/-- `bbfa0ce4150 src/gc-stock.c:3383-3391`: the next quick
collection drains TLS entries and, after a full collection, scans the
permanent image remset as well. -/
def RememberedForQuick (c : Config) (h : Heap c) (object : ObjectId c) : Prop :=
  InRemset c h object ∨ h.previousFull = true ∧ InImageRemset c h object

/-- `bbfa0ce4150 src/gc-stock.c:193-202,3092-3115,3383-3391`:
quick-start old-to-unmarked coverage. -/
def QuickStartCovered (c : Config) (h : Heap c) : Prop :=
  ∀ parent child, Edge c h parent child →
    (h.header parent).gc.markedBit = true →
    (h.header child).gc.markedBit = false → RememberedForQuick c h parent

/-- `bbfa0ce4150 src/gc-stock.c:193-202,3685-3696`: the generation
invariant supplied by the previous completed collection. It applies to all
allocated old objects, including objects a new root can make reachable. -/
def InitialGenerationInvariant (c : Config) (h : Heap c) : Prop :=
  ∀ parent child, Edge c h parent child →
    (h.header parent).gc.markedBit = true → (h.header child).gc.markedBit = false →
    RememberedForQuick c h parent

/-- `bbfa0ce4150 src/gc-interface.h:323-345,355-366`,
`src/julia.h:1426-1469`, `src/gc-wb-stock.h:19-130`: a final field
changed since collection entry has a last writer invocation. If the owner
was not initially covered by a TLS or required image entry and no owner
has claimed queueing, the header
and final-field observations satisfy
`BarrierObservation`. The invocation is complete before the stopping
boundary, and its actual emitted actions occur in the memory candidate.
The target slot is the final graph edge's actual destination; scalar and
copy contracts tie that destination to the invocation's slot or copy pair.
For bulk scans the destination load follows its own release store; C11
write/read coherence supplies the final-writer observation. -/
def LastWriterContract (c : Config) (before after : Heap c)
    (candidate : Candidate (Location c) (Value c)) : Prop :=
  ∀ parent child, Edge c after parent child → ¬ Edge c before parent child →
    (after.header parent).gc.markedBit = true → (after.header child).gc.markedBit = false →
    ¬ RememberedForQuick c before parent →
    ¬ Occurred candidate (ActionClaims parent) →
    ∃ (tid : ThreadId c) (call : Call c) (target : BarrierTarget c)
      (m : Mutator c) (actions : List (MemoryAction c)),
    call.parent = parent ∧ target.child = child ∧
      (∃ offset ∈ (c.layout parent).traceOffsets,
        c.field parent offset = some target.slot ∧ after.pointers target.slot = some child) ∧
      CallValid c call ∧ TargetsCall call target ∧
      InvocationRun c tid call target m actions ∧ m.pc = .outside ∧
      ∀ action ∈ actions, Occurred candidate (fun recorded => recorded = action)

/-- `bbfa0ce4150 src/gc-stock.c:193-202,1671-1748,3383-3387`:
old-to-young coverage for arbitrary finite source schedules. The premises
name the prior-generation invariant, private-TLS observations, stopping
boundary, successful allocation, and coherent header/final-field observations. -/
def AllocationSuccessfulQuickStartCoverage : Prop :=
  ∀ (c : Config) (initial stopped : ProtocolState c) (before after : Heap c),
    SuccessfulProtocolPrefix c initial stopped →
    (∀ tid, (initial.thread tid).cursor) →
    (∀ tid, (initial.thread tid).frame.pc = .outside) →
    (∀ parent, ¬ Occurred initial.memory (ActionClaims parent)) →
    (∀ tid, (stopped.thread tid).frame.pc = .outside) →
    stopped.memory.consistent = true →
    (∀ tid, before.remset tid = (initial.thread tid).array) →
    (∀ tid, after.remset tid = (stopped.thread tid).array) →
    ImageMutexBoundary stopped.memory before.imageRemset after.imageRemset →
    before.previousFull = after.previousFull →
    (∀ object, (before.header object).gc.markedBit = (after.header object).gc.markedBit) →
    InitialGenerationInvariant c before → LastWriterContract c before after stopped.memory →
    QuickStartCovered c after

theorem allocationSuccessfulQuickStartCoverage_proven : AllocationSuccessfulQuickStartCoverage := by
  intro c initial stopped before after history cursors initialBoundary noInitialClaims
    completed consistent beforeArrays afterArrays imageSections previousFull stable initialGeneration writers
  have preservesTLS : ∀ parent, InRemset c before parent → InRemset c after parent := by
    intro parent remembered
    obtain ⟨tid, index, bound, item⟩ := remembered
    have length := privateArray_boundary _ (cursors tid) (initialBoundary tid)
    have member : (initial.thread tid).contains parent :=
      ⟨index, by simpa [beforeArrays tid, length] using bound, by simpa [beforeArrays tid] using item⟩
    obtain ⟨index, bound, item⟩ := protocol_preserves_member history cursors parent tid member
    have length := privateArray_boundary _ (protocol_cursor history cursors tid) (completed tid)
    exact ⟨tid, index, by simpa [afterArrays tid, length] using bound, by simpa [afterArrays tid] using item⟩
  have preservesRemembered : ∀ parent,
      RememberedForQuick c before parent → RememberedForQuick c after parent := by
    intro parent remembered
    rcases remembered with remembered | ⟨full, image⟩
    · exact Or.inl (preservesTLS parent remembered)
    · exact Or.inr ⟨previousFull.symm.trans full,
        imageMutexBoundary_preserves imageSections parent image⟩
  intro parent child edge parentMarked childUnmarked
  by_cases remembered : RememberedForQuick c before parent
  · exact preservesRemembered parent remembered
  by_cases claimed : Occurred stopped.memory (ActionClaims parent)
  · obtain ⟨tid, index, bound, item⟩ :=
      protocol_claim_in_remset history cursors noInitialClaims completed parent claimed
    exact Or.inl ⟨tid, index, by simpa [afterArrays tid] using bound, by simpa [afterArrays tid] using item⟩
  · by_cases oldEdge : Edge c before parent child
    · have oldParent : (before.header parent).gc.markedBit = true := (stable parent).trans parentMarked
      have oldChild : (before.header child).gc.markedBit = false := (stable child).trans childUnmarked
      exact preservesRemembered parent (initialGeneration parent child oldEdge oldParent oldChild)
    · obtain ⟨tid, call, target, frame, actions, owner, childEq, targetField, valid, targeted, run, complete, included⟩ :=
        writers parent child edge oldEdge parentMarked childUnmarked remembered claimed
      obtain ⟨action, member, actionClaim⟩ := invocation_claims valid targeted run complete
      obtain ⟨event, recorded, actionEq⟩ := included action member
      exact False.elim (claimed ⟨event, recorded, by simpa [actionEq, owner] using actionClaim⟩)

/-- `bbfa0ce4150 src/gc-stock.c:1906-1917,2475-2803,3383-3406`:
root marking and closure under strong edges at the successful mark barrier. -/
def MarkedClosure (c : Config) (h : Heap c) : Prop :=
  (∀ root ∈ h.roots, (h.header root).gc.markedBit = true) ∧
  (∀ parent child, Edge c h parent child →
    (h.header parent).gc.markedBit = true → (h.header child).gc.markedBit = true)

/-- `bbfa0ce4150 src/gc-stock.c:245-265,1906-1917,2035-2039`:
source marking evidence is an observed set mark bit or a real header write
with its mark bit set. It does not assert graph reachability. -/
def MarkEvidence (c : Config) (candidate : Candidate (Location c) (Value c))
    (child : ObjectId c) : Prop :=
  ∃ event ∈ candidate.events.toList, event.action.location = some (.header child) ∧
    ∃ header, header.gc.markedBit = true ∧
      (event.action.readValue = some (.header header) ∨
       event.action.writeValue = some (.header header))

/-- `bbfa0ce4150 src/gc-stock.c:1906-2235,2475-2803`: a completed
source scan, including all suffix chunks, supplies marking evidence for
each strong outgoing field through the scanner/queue composition interface. -/
def ScanCertificate (c : Config) (heap : Heap c)
    (candidate : Candidate (Location c) (Value c)) (parent : ObjectId c) : Prop :=
  ∀ child, Edge c heap parent child → MarkEvidence c candidate child

/-- `bbfa0ce4150 src/gc-stock.c:242-265,3383-3406`: between the
collection's initial stopped snapshot and its mark barrier, no operation
clears a mark bit. Header observations follow the explicit coherent
whole-word interpretation required by the plain-header source accesses. -/
def MarkHeaderContract (c : Config) (before after : Heap c)
    (candidate : Candidate (Location c) (Value c)) : Prop :=
  (∀ object, (before.header object).gc.markedBit = true →
    (after.header object).gc.markedBit = true) ∧
  (∀ object, MarkEvidence c candidate object → (after.header object).gc.markedBit = true)

/-- `bbfa0ce4150 src/gc-stock.c:1906-1917,2475-2803,3092-3115,
3383-3406`: the actual mark-queue refinement must account for remset
seeds, newly marked work, tail-call work and every completed suffix chunk.
It supplies a full scan certificate for each work owner before termination.
This premise states the protocol boundary to the separate queue proof. -/
structure MarkQueueRefinement (c : Config) (before after : Heap c)
    (candidate : Candidate (Location c) (Value c)) where
  work : ObjectId c → Prop
  remsetSeed : ∀ parent, InRemset c before parent → work parent
  imageSeed : ∀ parent, before.previousFull = true → InImageRemset c before parent → work parent
  newMarkWork : ∀ parent, (before.header parent).gc.markedBit = false →
    (after.header parent).gc.markedBit = true → work parent
  allScanned : ∀ parent, work parent → ScanCertificate c after candidate parent
  rootEvidence : ∀ root ∈ after.roots, MarkEvidence c candidate root

/-- `bbfa0ce4150 src/gc-stock.c:3383-3406`: arbitrary graph closure
follows from quick-start coverage and the explicit actual-queue refinement
premises. Frozen fields follow the world-stop boundary; every new mark or
remembered parent has completed its source scan before queue termination. -/
theorem markedClosure_of_markQueue {c : Config} (before after : Heap c)
    (candidate : Candidate (Location c) (Value c))
    (coverage : QuickStartCovered c before)
    (frozen : ∀ parent child, Edge c after parent child → Edge c before parent child)
    (headers : MarkHeaderContract c before after candidate)
    (queues : MarkQueueRefinement c before after candidate) : MarkedClosure c after := by
  constructor
  · intro root member
    exact headers.2 root (queues.rootEvidence root member)
  · intro parent child edge marked
    by_cases oldMark : (before.header parent).gc.markedBit = true
    · by_cases childMark : (before.header child).gc.markedBit = true
      · exact headers.1 child childMark
      · have unmarked : (before.header child).gc.markedBit = false := by
          cases bit : (before.header child).gc.markedBit <;> simp_all
        have remembered := coverage parent child (frozen parent child edge) oldMark unmarked
        have work : queues.work parent := by
          rcases remembered with tls | ⟨full, image⟩
          · exact queues.remsetSeed parent tls
          · exact queues.imageSeed parent full image
        exact headers.2 child (queues.allScanned parent work child edge)
    · have unmarked : (before.header parent).gc.markedBit = false := by
        cases bit : (before.header parent).gc.markedBit <;> simp_all
      exact headers.2 child (queues.allScanned parent (queues.newMarkWork parent unmarked marked) child edge)

/-- `bbfa0ce4150 src/gc-stock.c:1906-2235,2475-2803,3383-3406,
1015-1043`: all reachable young objects are marked before a successful
quick sweep, conditional on the stated source-scan/mark-queue refinement. -/
def ReachableBeforeSweep : Prop :=
  ∀ (c : Config) (before after : Heap c) (candidate : Candidate (Location c) (Value c)),
    after.phase = .beforeSweep → after.full = false → candidate.consistent = true →
    QuickStartCovered c before →
    (∀ parent child, Edge c after parent child → Edge c before parent child) →
    MarkHeaderContract c before after candidate → MarkQueueRefinement c before after candidate →
    ∀ object, Reachable c after object → (after.header object).gc.markedBit = true

theorem reachableBeforeSweep_proven : ReachableBeforeSweep := by
  intro c before after candidate phase quick consistent coverage frozen headers queues
  have closed := markedClosure_of_markQueue before after candidate coverage frozen headers queues
  intro object reach
  induction reach with
  | root member => exact closed.1 _ member
  | edge _ edge ih => exact closed.2 _ _ edge ih

/-- `bbfa0ce4150 src/gc-stock.c:3393-3406,1015-1043`: closure suffices
to retain every reachable object, for arbitrary finite graphs and paths. -/
theorem reachable_marked_of_closure {c : Config} {h : Heap c}
    (closed : MarkedClosure c h) :
    ∀ object, Reachable c h object → (h.header object).gc.markedBit = true := by
  intro object reach
  induction reach with
  | root member => exact closed.1 _ member
  | edge _ edge ih => exact closed.2 _ _ edge ih

/-- `bbfa0ce4150 src/gc-stock.c:1679-1680`: the old bit stays clear
after the relaxed fetch-and, for every GC/tag/image combination. -/
theorem clearOld_oldBit (h : Header) : h.clearOld.gc.oldBit = false := by
  cases h with
  | mk gc image imageRemset tag => cases gc <;> rfl

/-- `bbfa0ce4150 src/gc-stock.c:1679`: queue-root preserves the mark. -/
theorem clearOld_markedBit (h : Header) : h.clearOld.gc.markedBit = h.gc.markedBit := by
  cases h with
  | mk gc image imageRemset tag => cases gc <;> rfl

/-- `bbfa0ce4150 src/gc-stock.c:1686-1687`: repeated image-bit RMWs. -/
theorem imageRemset_idempotent (h : Header) :
    h.setImageRemset.setImageRemset = h.setImageRemset := by rfl

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: projection of queue-root
RMWs in modification order, between collector old-bit resets. -/
def rootModificationHistory (initial : Header) : Nat → Header
  | 0 => initial
  | n + 1 => (rootModificationHistory initial n).clearOld

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: subsequent RMWs see old=0. -/
theorem rootModificationHistory_later (initial : Header) (index : Nat) :
    (rootModificationHistory initial (index + 1)).gc.oldBit = false := by
  exact clearOld_oldBit _

/-- `bbfa0ce4150 src/gc-stock.c:1675-1682`: at most one position in an
arbitrary queue-root modification history can acquire the append duty.
Relating candidate RMWs to this projection additionally requires the
shared `Memory.rmw_reads_immediate` lemma. -/
private def QueueRootHistoryAtMostOnce : Prop :=
  ∀ (initial : Header) (first second : Nat),
    (rootModificationHistory initial first).gc.oldBit = true →
    (rootModificationHistory initial second).gc.oldBit = true → first = second

private theorem queueRootHistoryAtMostOnce_proven : QueueRootHistoryAtMostOnce := by
  intro initial first second hf hs
  cases first with
  | zero =>
      cases second with
      | zero => rfl
      | succ n => simp [rootModificationHistory_later] at hs
  | succ n => simp [rootModificationHistory_later] at hf

/-- `bbfa0ce4150 src/gc-stock.c:1679,1686`: during a mutator epoch,
the only header modifications are queue-root's relaxed old-bit clear and
image-bit set. Collector stores that re-arm the old bit occur with the
world stopped, outside the epoch (`src/gc-stock.c:3098,3695`). -/
def HeaderEpoch {c : Config} (candidate : Candidate (Location c) (Value c))
    (object : ObjectId c) : Prop :=
  ∀ i : candidate.Id,
    (candidate.event i).action.location = some (.header object) →
    candidate.isWrite i = true →
    (∃ h, (candidate.event i).action = .init (.header object) (.header h)) ∨
    (∃ h, (candidate.event i).action =
      .rmw (.header object) .relaxed (.header h) (.header h.clearOld)) ∨
    (∃ h, (candidate.event i).action =
      .rmw (.header object) .relaxed (.header h) (.header h.setImageRemset))

private theorem rmw_location {c : Config} {candidate : Candidate (Location c) (Value c)}
    {object : ObjectId c} {read source : candidate.Id} {before after : Header}
    (hr : (candidate.event read).action =
      .rmw (.header object) .relaxed (.header before) (.header after))
    (same : candidate.sameLocation read source = true) :
    (candidate.event source).action.location = some (.header object) := by
  have eq : some (.header object) = (candidate.event source).action.location := by
    simpa [Candidate.sameLocation, hr, Action.location] using same
  exact eq.symm

/-- `bbfa0ce4150 src/gc-stock.c:1679,1686`: once one RMW clears the
old bit, every later header RMW observes it clear, including interposed
image-remset RMWs. This proof uses C11's immediate-predecessor RMW rule;
the scheduler's array order is irrelevant. -/
theorem oldBit_after_rootClaim {c : Config}
    (candidate : Candidate (Location c) (Value c)) (consistent : candidate.consistent = true)
    (object : ObjectId c) (epoch : HeaderEpoch candidate object)
    (first : candidate.Id) (firstHeader : Header)
    (firstAction : (candidate.event first).action =
      .rmw (.header object) .relaxed (.header firstHeader) (.header firstHeader.clearOld))
    (later : candidate.Id) (before after : Header)
    (laterAction : (candidate.event later).action =
      .rmw (.header object) .relaxed (.header before) (.header after))
    (ordered : (candidate.event first).mo < (candidate.event later).mo) :
    before.gc.oldBit = false := by
  have well := (of_decide_eq_true consistent : candidate.Consistent).1
  have firstAtomic : candidate.isAtomicWrite first = true := by
    simp [Candidate.isAtomicWrite, Candidate.isWrite, firstAction, Action.writeValue, Action.isPlain]
  have firstPositive : 0 < (candidate.event first).mo := by
    have nonzero := (well.2.2.2.1 first firstAtomic)
    simp [firstAction, Action.isInit] at nonzero
    omega
  have prove : ∀ rank, ∀ (later : candidate.Id) (before after : Header),
      (candidate.event later).mo = rank →
      (candidate.event later).action =
        .rmw (.header object) .relaxed (.header before) (.header after) →
      (candidate.event first).mo < (candidate.event later).mo → before.gc.oldBit = false := by
    intro rank
    refine Nat.strongRecOn rank ?_
    intro rank ih
    intro later before after rankEq action ordered
    have isRead : candidate.isRead later = true := by
      simp [Candidate.isRead, action, Action.readValue]
    obtain ⟨source, rf, sourceWrite, same, values⟩ := well.2.1 later isRead
    have sourceLoc := rmw_location action same
    have immediate := candidate.rmw_reads_immediate consistent later source
      (by simp [action, Action.isRMW]) rf
    have firstSame : candidate.sameLocation later first = true := by
      simp [Candidate.sameLocation, action, firstAction, Action.location]
    have afterFirst := immediate.2 first firstAtomic firstSame ordered
    by_cases sameRank : (candidate.event source).mo = (candidate.event first).mo
    · have sourceAtomic : candidate.isAtomicWrite source = true := by
        rcases epoch source sourceLoc sourceWrite with ⟨header, init⟩ | ⟨header, root⟩ | ⟨header, image⟩
        all_goals simp [Candidate.isAtomicWrite, Candidate.isWrite, Action.writeValue, Action.isPlain, *]
      have firstSourceSame : candidate.sameLocation source first = true := by
        unfold Candidate.sameLocation
        rw [sourceLoc, firstAction]
        simp [Action.location]
      have sourceEq := well.2.2.2.2.1 source first sourceAtomic firstAtomic firstSourceSame sameRank
      subst source
      have headers : before = firstHeader.clearOld := by
        simpa [action, firstAction, Action.readValue, Action.writeValue] using values
      rw [headers]
      exact clearOld_oldBit _
    · have earlier : (candidate.event first).mo < (candidate.event source).mo := by omega
      rcases epoch source sourceLoc sourceWrite with ⟨header, init⟩ | ⟨header, root⟩ | ⟨header, image⟩
      · have sourceAtomic : candidate.isAtomicWrite source = true := by
          simp [Candidate.isAtomicWrite, Candidate.isWrite, init, Action.writeValue, Action.isPlain]
        have sourceZero := (well.2.2.2.1 source sourceAtomic).1 (by simp [init, Action.isInit])
        omega
      · have headers : before = header.clearOld := by
          simpa [action, root, Action.readValue, Action.writeValue] using values
        rw [headers]
        exact clearOld_oldBit _
      · have headers : before = header.setImageRemset := by
          simpa [action, image, Action.readValue, Action.writeValue] using values
        have sourceOld : header.gc.oldBit = false :=
          ih (candidate.event source).mo (by omega) source header header.setImageRemset rfl image earlier
        simpa [headers, Header.setImageRemset] using sourceOld
  exact prove _ later before after rfl laterAction ordered

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: one source RMW acquires
the duty to append precisely when its observed old bit is set. -/
def QueueRootClaim {c : Config} (candidate : Candidate (Location c) (Value c))
    (object : ObjectId c) (i : candidate.Id) : Prop :=
  ∃ header, (candidate.event i).action =
    .rmw (.header object) .relaxed (.header header) (.header header.clearOld) ∧
    header.gc.oldBit = true

/-- `bbfa0ce4150 src/gc-stock.c:1675-1687`: at most one concurrent
barrier can acquire the append duty in a mutator epoch, for every finite
heap, thread count, schedule, read-from choice and modification order. -/
def QueueRootAtMostOnce : Prop :=
  ∀ (c : Config) (candidate : Candidate (Location c) (Value c)) (object : ObjectId c),
    candidate.consistent = true → HeaderEpoch candidate object →
    ∀ first second, QueueRootClaim candidate object first →
      QueueRootClaim candidate object second → first = second

theorem queueRootAtMostOnce_proven : QueueRootAtMostOnce := by
  intro c candidate object consistent epoch first second firstClaim secondClaim
  obtain ⟨firstHeader, firstAction, firstOld⟩ := firstClaim
  obtain ⟨secondHeader, secondAction, secondOld⟩ := secondClaim
  by_cases ranks : (candidate.event first).mo = (candidate.event second).mo
  · exact (of_decide_eq_true consistent : candidate.Consistent).1.2.2.2.2.1 first second
      (by simp [Candidate.isAtomicWrite, Candidate.isWrite, firstAction, Action.writeValue, Action.isPlain])
      (by simp [Candidate.isAtomicWrite, Candidate.isWrite, secondAction, Action.writeValue, Action.isPlain])
      (by simp [Candidate.sameLocation, firstAction, secondAction, Action.location]) ranks
  · by_cases ordered : (candidate.event first).mo < (candidate.event second).mo
    · have cleared := oldBit_after_rootClaim candidate consistent object epoch
        first firstHeader firstAction second secondHeader secondHeader.clearOld secondAction ordered
      simp [secondOld] at cleared
    · have ordered : (candidate.event second).mo < (candidate.event first).mo := by omega
      have cleared := oldBit_after_rootClaim candidate consistent object epoch
        second secondHeader secondAction first firstHeader firstHeader.clearOld firstAction ordered
      simp [firstOld] at cleared

/-- `bbfa0ce4150 src/gc-stock.c:3092-3104`: clear active length/counter. -/
def clearRemset {c : Config} (r : Remset c) : Remset c := { r with len := 0, nptr := 0 }

/-- `bbfa0ce4150 src/gc-stock.c:3092-3104`: backing storage survives drain. -/
theorem clearRemset_correct {c : Config} (r : Remset c) :
    (clearRemset r).len = 0 ∧ (clearRemset r).nptr = 0 ∧ (clearRemset r).items = r.items := by
  exact ⟨rfl, rfl, rfl⟩

/-- `bbfa0ce4150 src/gc-stock.c:1815-1824`: remset rebuild decision. -/
def markRemsetDecision (n : ScanCount) : Bool := n.old && n.refyoung

/-- `bbfa0ce4150 src/gc-stock.c:1815-1816`: all count/flag combinations. -/
theorem markRemsetDecision_correct (n : ScanCount) :
    markRemsetDecision n = true ↔ n.old = true ∧ n.refyoung = true := by
  cases n with
  | mk pointers old refyoung => cases old <;> cases refyoung <;> simp [markRemsetDecision]

/-- `bbfa0ce4150 src/gc-stock.c:1815-1816,1906-1917`:
the packed low two bits are the flags; shifting them away returns the
pointer-count contribution. -/
theorem scanCount_decoding (n : ScanCount) :
    n.packed / 4 = n.pointers ∧
    (n.packed % 4 = 3 ↔ n.old = true ∧ n.refyoung = true) := by
  cases n with
  | mk pointers old refyoung =>
      cases old <;> cases refyoung <;> simp [ScanCount.packed] <;> omega

/-- `bbfa0ce4150 src/gc-stock.c:3685-3700`: full reset clears length
only; quick reset retains the rebuilt array. -/
def postSweepRemset {c : Config} (full : Bool) (r : Remset c) : Remset c :=
  if full then { r with len := 0 } else r

/-- `bbfa0ce4150 src/gc-stock.c:3692-3700`: exact array reset effects. -/
theorem postSweepRemset_correct {c : Config} (full : Bool) (r : Remset c) :
    (postSweepRemset full r).len = (if full then 0 else r.len) ∧
    (postSweepRemset full r).nptr = r.nptr := by
  cases full <;> exact ⟨rfl, rfl⟩

/-- `bbfa0ce4150 src/gc-stock.c:1812-1826,3092-3104,3685-3700`,
`src/gc-tls-stock.h:27-30`:
the drain's final two stores clear length and counter, rebuilding adds the
decoded pointer count exactly when both flags are set and the C `int` target
conversion is representable. Post-sweep reset preserves the counter. A quick
reset changes remembered headers to MARKED; a full reset clears only length. -/
def RemsetDrainReset : Prop :=
  ∀ (c : Config) (tid : ThreadId c) (k : Collector c) (obs : Observation c) (r : Remset c),
    RemsetCounterTargetContract k →
    let drainLength := collectorInstruction c tid { k with pc := .drainClearLength } obs
    let drainCounter := collectorInstruction c tid drainLength.next obs
    (collectorInstruction c tid { k with pc := .drainStorage } obs).action =
      some (.plainLoad (.remsetStorage k.target) (.storage obs.storage)) ∧
    (collectorInstruction c tid { k with pc := .drainStorage } obs).next.pc = .drainLength ∧
    (collectorInstruction c tid { k with pc := .imageLength } obs).next.pc = .imageStorage ∧
    (collectorInstruction c tid { k with pc := .imageStorage } obs).action =
      some (.plainLoad .imageStorage (.storage obs.storage)) ∧
    (collectorInstruction c tid { k with pc := .scanRemsetLengthStore } obs).next.pc = .scanRemsetStorage ∧
    (collectorInstruction c tid { k with pc := .scanRemsetStorage } obs).action =
      some (.plainLoad (.remsetStorage tid) (.storage obs.storage)) ∧
    drainLength.action = some (.plainStore (.remsetLen k.target) (.number 0)) ∧
    drainLength.next.pc = .drainClearNptr ∧
    drainCounter.action = some (.plainStore (.remsetNptr k.target) (.counter 0)) ∧
    drainCounter.next.pc = .finished ∧
    (clearRemset r).len = 0 ∧ (clearRemset r).nptr = 0 ∧
    (clearRemset r).items = r.items ∧ (clearRemset r).capacity = r.capacity ∧
    (clearRemset r).storage = r.storage ∧
    (markRemsetDecision k.nptr = true ↔ k.nptr.old = true ∧ k.nptr.refyoung = true) ∧
    k.nptr.packed / 4 = k.nptr.pointers ∧
    (k.nptr.packed % 4 = 3 ↔ markRemsetDecision k.nptr = true) ∧
    (collectorInstruction c tid { k with pc := .scanRemsetTest } obs).next.pc =
      (if markRemsetDecision k.nptr then .scanRemsetNptrLoad else .returnTail) ∧
    (collectorInstruction c tid { k with pc := .scanRemsetNptrLoad } obs).action =
      some (.plainLoad (.remsetNptr tid) (.counter obs.counter)) ∧
    (collectorInstruction c tid { k with pc := .scanRemsetNptrLoad } obs).next.count = obs.counter ∧
    (collectorInstruction c tid { k with pc := .scanRemsetNptrStore } obs).action =
      some (.plainStore (.remsetNptr tid)
        (.counter (remsetCounterResult k))) ∧
    (remsetCounterResult k).toNat = k.count.toNat + k.nptr.pointers ∧
    (collectorInstruction c tid { k with pc := .scanRemsetNptrStore } obs).next.pc =
      .scanRemsetLength ∧
    (collectorInstruction c tid { k with pc := .resetMode } obs).next.pc =
      (if k.full then .fullClearLength else .resetLength) ∧
    (∀ parent, k.child = some parent →
      (collectorInstruction c tid { k with pc := .resetHeader } obs).action =
        some (.plainStore (.header parent) (.header { k.oldHeader with gc := .marked })) ∧
      (collectorInstruction c tid { k with pc := .resetHeader } obs).next.pc = .resetItem ∧
      (collectorInstruction c tid { k with pc := .resetHeader } obs).next.index = k.index + 1) ∧
    (collectorInstruction c tid { k with pc := .fullClearLength } obs).action =
      some (.plainStore (.remsetLen k.target) (.number 0)) ∧
    (collectorInstruction c tid { k with pc := .fullClearLength } obs).next.pc = .finished ∧
    (postSweepRemset k.full r).len = (if k.full then 0 else r.len) ∧
    (postSweepRemset k.full r).nptr = r.nptr ∧
    (postSweepRemset k.full r).items = r.items ∧
    (postSweepRemset k.full r).capacity = r.capacity ∧
    (postSweepRemset k.full r).storage = r.storage

theorem remsetDrainReset_proven : RemsetDrainReset := by
  intro c tid k obs r counterContract
  have pointers := (scanCount_decoding k.nptr).1
  have flags := (scanCount_decoding k.nptr).2
  have counterBound : k.count.toNat + k.nptr.pointers < 2 ^ 32 := by
    rcases counterContract with ⟨_, _, sum⟩
    omega
  cases full : k.full <;>
    simp [collectorInstruction, cemit, cadvance, clearRemset,
      markRemsetDecision, postSweepRemset, remsetCounterResult,
      pointers, flags, counterBound]
  all_goals intro parent child; simp [child]

/-- `bbfa0ce4150 src/gc-wb-stock.h:78-130`,
`src/julia.h:1426-1437`: every completed valid boxed or inline copy with a
selected unmarked destination field emits a queue-root claim. The source
address span, memmove direction, target-width pointer count and scan layout
are derived by `CallValid`; `InvocationRun` checks coherent observations. -/
def BulkCopyCoverage : Prop :=
  ∀ (c : Config) (tid : ThreadId c) (call : Call c) (target : BarrierTarget c)
      (m : Mutator c) (actions : List (MemoryAction c)),
    (call.kind = .copyBoxed ∨ call.kind = .copyInline) → CallValid c call →
    TargetsCall call target → InvocationRun c tid call target m actions →
    m.pc = .outside → ∃ action ∈ actions, ActionClaims call.parent action

theorem bulkCopyCoverage_proven : BulkCopyCoverage := by
  intro c tid call target m actions kind valid targeted run complete
  exact invocation_claims valid targeted run complete

end JuliaLean.CRuntime.WriteBarrier

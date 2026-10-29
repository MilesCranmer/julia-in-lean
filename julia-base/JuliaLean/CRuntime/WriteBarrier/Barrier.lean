import JuliaLean.CRuntime.WriteBarrier.Core

namespace JuliaLean.CRuntime.WriteBarrier

open JuliaLean.CRuntime.Memory

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1704-1748`: no targeted source invocation can finish
its barrier before queue-root, for every pointer count and layout index.
The step remains interleavable at every load and store. -/
theorem barrierPending_instruction {c : Config} (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) (target : BarrierTarget c)
    (valid : CallValid c m.call)
    (targeted : TargetsCall m.call target) (pending : BarrierPending m target)
    (observed : BarrierObservation m obs target) :
    InstructionClaims m (mutatorInstruction c tid m obs) ∨
      BarrierPending (mutatorInstruction c tid m obs).next target := by
  have sourcePresent : m.call.kind = .multi → m.call.source ≠ none := by
    intro kind
    obtain ⟨source, sourceEq, _, _, _⟩ := valid.2.2.1 kind
    simp [sourceEq]
  rcases observed with ⟨parent, source, scalar, slot, child, root⟩
  by_cases rootPC : m.pc = .rootFetchAnd
  · left
    refine ⟨obs.header, ?_, root rootPC⟩
    simp [mutatorInstruction, rootPC]
  cases kind : m.call.kind with
  | scalar =>
      simp only [BarrierPending, kind, List.mem_cons] at pending
      rcases pending with pc | pc | pc | pc | pc
      all_goals
        simp_all [TargetsCall, BarrierPending, mutatorInstruction, advance,
          readHeader, afterParentGC, InstructionClaims]
      all_goals try (repeat' (split <;> try simp_all))
      all_goals omega
  | object =>
      simp only [BarrierPending, kind, List.mem_cons] at pending
      rcases pending with pc | pc
      all_goals
        simp_all [TargetsCall, BarrierPending, mutatorInstruction,
          readHeader, InstructionClaims]
      all_goals try (repeat' (split <;> try simp_all))
      all_goals omega
  | multi =>
      simp only [BarrierPending, kind, List.mem_cons] at pending
      rcases pending with (pc | pc | pc | pc | pc | pc) | ⟨pc, index⟩ | ⟨pc, index, pointer⟩
      all_goals cases pointerState : m.pointer
      all_goals
        simp_all [TargetsCall, BarrierPending, mutatorInstruction, advance,
          readHeader, readPointer, afterParentGC, InstructionClaims]
      all_goals try (repeat' (split <;> try simp_all))
      all_goals omega
  | copyBoxed =>
      simp only [BarrierPending, kind, List.mem_cons] at pending
      rcases pending with (pc | pc | pc | pc | pc | pc | pc) | ⟨pc, index⟩ | ⟨pc, index, pointer⟩
      all_goals cases pointerState : m.pointer
      all_goals
        simp_all [TargetsCall, BarrierPending, mutatorInstruction, advance, emit,
          readHeader, readPointer, rootCall, InstructionClaims]
      all_goals try (repeat' (split <;> try simp_all))
      all_goals omega
  | copyInline =>
      simp only [BarrierPending, kind, List.mem_cons] at pending
      rcases pending with (pc | pc | pc | pc | pc | pc | pc) | ⟨pc, index⟩ | ⟨pc, index, pointer⟩
      all_goals cases pointerState : m.pointer
      all_goals
        simp_all [TargetsCall, BarrierPending, mutatorInstruction, advance, emit,
          readHeader, readPointer, rootCall, InstructionClaims]
      all_goals try (repeat' (split <;> try simp_all))
      all_goals omega
  | moduleUsings =>
      simp only [BarrierPending, kind, List.mem_cons] at pending
      rcases pending with pc | pc | pc | pc
      all_goals
        simp_all [TargetsCall, BarrierPending, mutatorInstruction,
          readHeader, afterParentGC, InstructionClaims]
      all_goals try (repeat' (split <;> try simp_all))
      all_goals omega

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`: every valid function entry
still owes queueing for a selected unmarked reference to an unchanged old
owner. -/
theorem barrierPending_entry {c : Config} (call : Call c) (target : BarrierTarget c)
    (_targeted : TargetsCall call target) :
    BarrierPending { call := call, pc := entryPC call.kind } target := by
  cases kind : call.kind <;> simp_all [BarrierPending, entryPC, TargetsCall]

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: a queue-root claim in
an emitted action, independent of the caller's local registers. -/
def ActionClaims {c : Config} (parent : ObjectId c) (action : MemoryAction c) : Prop :=
  ∃ header, action = .rmw (.header parent) .relaxed (.header header) (.header header.clearOld) ∧
    header.gc.oldBit = true

/-- `bbfa0ce4150 src/gc-stock.c:1681`: the item store that discharges
the claiming thread's append duty. -/
def ActionAppends {c : Config} (parent : ObjectId c) (action : MemoryAction c) : Prop :=
  ∃ tid index, action = .plainStore (.remsetItem tid index) (.pointer (some parent))

private theorem imageRmw_not_claim {c : Config} (parent owner : ObjectId c) (observed : Header) :
    ¬ ActionClaims parent
      (.rmw (.header owner) .relaxed (.header observed) (.header observed.setImageRemset)) := by
  rintro ⟨header, action, old⟩
  have before : observed = header := by
    simpa [Action.readValue] using congrArg Action.readValue action
  have after : observed.setImageRemset = header.clearOld := by
    simpa [Action.writeValue] using congrArg Action.writeValue action
  have cleared : header.clearOld.gc.oldBit = false := by
    cases header with
    | mk gc image imageRemset tag => cases gc <;> rfl
  have bits := congrArg (fun h : Header => h.gc.oldBit) after
  simp [before, Header.setImageRemset, cleared, old] at bits

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: the actual intermediate
PCs between the claiming RMW and its per-thread item store. -/
def AppendPending {c : Config} (m : Mutator c) (parent : ObjectId c) : Prop :=
  m.call.parent = parent ∧ m.oldHeader.gc.oldBit = true ∧
    (m.pc = .rootOldBranch ∨ m.pc = .undefinedAccess ∨
      inArrayCode m.pc = true ∧ m.arrayCall.target = .tls ∧
        m.pc = arrayMutatorPC .tls m.arrayCall.pc)

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: every source append step
either retains the duty or emits the actual remembered-set item store. -/
theorem appendPending_instruction {c : Config} (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) (parent : ObjectId c)
    (pending : AppendPending m parent) :
    (m.pc = .rootItemStore ∧
      ∃ action, (mutatorInstruction c tid m obs).action = some action ∧ ActionAppends parent action) ∨
      AppendPending (mutatorInstruction c tid m obs).next parent := by
  rcases pending with ⟨owner, old, branch | stuck | ⟨code, target, shape⟩⟩
  · right
    simp [mutatorInstruction, branch, old, advance, AppendPending, owner,
      inArrayCode, arrayMutatorPC]
  · right
    simp [mutatorInstruction, stuck, advance, AppendPending, owner, old]
  · rw [mutator_arrayInstruction tid m obs code]
    cases pc : m.arrayCall.pc <;> simp only [pc, arrayMutatorPC] at shape
    all_goals try (simp [shape, inArrayCode] at code)
    all_goals
      simp [arrayMutatorInstruction, arrayListInstruction, pc, target, shape,
        AppendPending, ActionAppends, arrayMutatorPC, inArrayCode, owner, old]
    all_goals repeat' (split at * <;> try simp_all)
    all_goals exact ⟨tid, m.arrayCall.pushLen - 1, rfl⟩

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682,1686`: only the old-bit
clear with an observed set bit can create an append duty. The image-bit
fetch-or cannot be mistaken for that transition. -/
theorem claimed_instruction_pending {c : Config} (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) (parent : ObjectId c) (action : MemoryAction c)
    (emitted : (mutatorInstruction c tid m obs).action = some action)
    (claimed : ActionClaims parent action) :
    AppendPending (mutatorInstruction c tid m obs).next parent := by
  by_cases imagePC : m.pc = .rootImageFetchOr
  · have imageAction : (.rmw (.header m.call.parent) .relaxed
        (.header obs.header) (.header obs.header.setImageRemset) : MemoryAction c) = action := by
      exact Option.some.inj (by simpa [mutatorInstruction, imagePC] using emitted)
    exact False.elim (imageRmw_not_claim parent m.call.parent obs.header (imageAction.symm ▸ claimed))
  obtain ⟨header, actionEq, old⟩ := claimed
  subst action
  by_cases code : inArrayCode m.pc = true
  · rw [mutator_arrayInstruction tid m obs code] at emitted
    cases pc : m.arrayCall.pc <;>
      simp [arrayMutatorInstruction, arrayListInstruction, pc] at emitted
    all_goals repeat' (split at * <;> try simp_all)
  cases branch : m.pc <;>
    simp_all [mutatorInstruction, advance, emit, readHeader, readPointer, rootCall,
      AppendPending, inArrayCode]
  all_goals repeat' (split at * <;> try simp_all)

/-- Source occurrence, `bbfa0ce4150 src/gc-stock.c:1679-1682`. -/
def Occurred {c : Config} (candidate : Candidate (Location c) (Value c))
    (predicate : MemoryAction c → Prop) : Prop :=
  ∃ event ∈ candidate.events.toList, predicate event.action

private theorem occurred_appendInstruction {c : Config}
    (candidate : Candidate (Location c) (Value c)) (tid : ThreadId c)
    (instruction : Instruction c) (choice : Choice) (support : List Nat)
    (predicate : MemoryAction c → Prop) :
    Occurred (appendInstruction candidate tid instruction choice support) predicate ↔
      Occurred candidate predicate ∨ ∃ action, instruction.action = some action ∧ predicate action := by
  cases action : instruction.action <;>
    simp [appendInstruction, action, Candidate.append, Occurred, Array.toList_push]

private theorem appendPending_thread {c : Config}
    (candidate : Candidate (Location c) (Value c)) (m : Mutator c)
    (instruction : Instruction c) (parent : ObjectId c) :
    AppendPending (instructionThread candidate m instruction) parent ↔ AppendPending instruction.next parent := by
  simp [instructionThread, AppendPending]

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: a claim can be outstanding
only while its owning thread is inside the source append PCs. -/
theorem source_claim_append_debt {c : Config}
    {initial : Candidate (Location c) (Value c)} {initialThreads : ThreadId c → Mutator c}
    {candidate : Candidate (Location c) (Value c)} {threads : ThreadId c → Mutator c}
    (history : MutatorPrefix c initial initialThreads candidate threads)
    (initialNoClaims : ∀ parent, ¬ Occurred initial (ActionClaims parent))
    (_initialEntries : ∀ tid, (initialThreads tid).pc = entryPC (initialThreads tid).call.kind) :
    ∀ parent, Occurred candidate (ActionClaims parent) →
      Occurred candidate (ActionAppends parent) ∨ ∃ tid, AppendPending (threads tid) parent := by
  induction history with
  | initial => intro parent claim; exact False.elim (initialNoClaims parent claim)
  | beginCall history tid call outside ih =>
      intro parent claim
      rcases ih parent claim with appended | ⟨pendingTid, pending⟩
      · exact Or.inl appended
      · right
        by_cases same : pendingTid = tid
        · subst pendingTid
          simp [AppendPending, outside, inArrayCode] at pending
        · exact ⟨pendingTid, by simpa [same] using pending⟩
  | @next previousCandidate previousThreads history tid obs choice ih =>
      intro parent claim
      have claimCases := (occurred_appendInstruction _ _ _ _ _ _).1 claim
      have liftAppend : Occurred previousCandidate (ActionAppends parent) →
          Occurred (appendInstruction previousCandidate tid (mutatorInstruction c tid (previousThreads tid) obs)
            choice (previousThreads tid).support) (ActionAppends parent) := by
        intro appended
        exact (occurred_appendInstruction _ _ _ _ _ _).2 (Or.inl appended)
      rcases claimCases with previous | ⟨action, emitted, newClaim⟩
      · rcases ih parent previous with appended | ⟨pendingTid, pending⟩
        · exact Or.inl (liftAppend appended)
        · by_cases same : pendingTid = tid
          · subst pendingTid
            rcases appendPending_instruction tid (previousThreads tid) obs parent pending with appended | remains
            · exact Or.inl ((occurred_appendInstruction _ _ _ _ _ _).2 (Or.inr appended.2))
            · exact Or.inr ⟨tid, by simp [appendPending_thread, remains]⟩
          · exact Or.inr ⟨pendingTid, by simpa [same] using pending⟩
      · have pending := claimed_instruction_pending tid (previousThreads tid) obs parent action emitted newClaim
        exact Or.inr ⟨tid, by simp [appendPending_thread, pending]⟩

/-- `bbfa0ce4150 src/gc-interface.h:315`,
`src/gc-stock.c:1679-1682,3383-3387`: once all callers can stop, every
claim has emitted its real remset item store. No fairness assumption is
needed for this safety statement about completed stopping boundaries. -/
theorem source_claim_appended_at_stop {c : Config}
    {initial : Candidate (Location c) (Value c)} {initialThreads : ThreadId c → Mutator c}
    {candidate : Candidate (Location c) (Value c)} {threads : ThreadId c → Mutator c}
    (history : MutatorPrefix c initial initialThreads candidate threads)
    (initialNoClaims : ∀ parent, ¬ Occurred initial (ActionClaims parent))
    (initialEntries : ∀ tid, (initialThreads tid).pc = entryPC (initialThreads tid).call.kind)
    (stopped : ∀ tid, (threads tid).pc = .outside) :
    ∀ parent, Occurred candidate (ActionClaims parent) → Occurred candidate (ActionAppends parent) := by
  intro parent claim
  rcases source_claim_append_debt history initialNoClaims initialEntries parent claim with appended | ⟨tid, pending⟩
  · exact appended
  · simp [AppendPending, stopped tid, inArrayCode] at pending

/-- `bbfa0ce4150 src/gc-stock.c:1681-1682`,
`src/support/arraylist.c:40-70`: private TLS array contents together with
its owning source frame. `published` excludes the transient slot after
arraylist increments length and before it writes the new item. -/
structure PrivateArray (c : Config) where
  frame : Mutator c
  array : Remset c
  published : Nat

/-- `bbfa0ce4150 src/support/arraylist.c:42-70`: a thread alone writes
its TLS remset in a mutator epoch. The pending item index is the old length;
only the length-write/item-write interval has one unpublished active slot. -/
def PrivateArray.cursor {c : Config} (s : PrivateArray c) : Prop :=
  (if inArrayCode s.frame.pc then
    s.frame.pc = arrayMutatorPC s.frame.arrayCall.target s.frame.arrayCall.pc ∧
      (if s.frame.arrayCall.target = .tls then
        ArrayCursor ⟨s.frame.arrayCall, s.array⟩ s.published else s.array.len = s.published)
  else s.array.len = s.published) ∧
  inArrayCode s.frame.returnPC = false

/-- `bbfa0ce4150 src/support/arraylist.c:42,44`,
`src/gc-stock.c:1682`: observations of the exclusively owned TLS array.
Length and counter follow ordinary-access visibility once collector entry
is excluded; length, capacity and backing-storage reads match the private array. -/
def PrivateArray.observes {c : Config} (s : PrivateArray c) (obs : Observation c) : Prop :=
  (inArrayCode s.frame.pc = true → s.frame.arrayCall.target = .tls →
    arrayObservation ⟨s.frame.arrayCall, s.array⟩ obs) ∧
  (s.frame.pc = .rootNptrLoad → obs.counter = s.array.nptr)

/-- `bbfa0ce4150 src/support/arraylist.c:64,70`,
`src/gc-stock.c:1682`: source store effects on the private array; header
and payload effects remain events in the C11 execution. Allocation growth
does not alter an existing item's logical index. -/
def PrivateArray.step {c : Config} (tid : ThreadId c) (s : PrivateArray c)
    (obs : Observation c) : PrivateArray c :=
  let instruction := mutatorInstruction c tid s.frame obs
  let array := if inArrayCode s.frame.pc && s.frame.arrayCall.target == .tls then
      arrayListEffect s.array s.frame.arrayCall s.frame.call.parent
    else if s.frame.pc = .rootNptrStore then
      if s.frame.count = 0x7fffffff then s.array else { s.array with nptr := s.frame.count + 1 }
    else s.array
  { frame := instruction.next, array := array
    published := if inArrayCode s.frame.pc && s.frame.arrayCall.target == .tls then
      arrayPublished s.frame.arrayCall s.published else s.published }

private theorem tlsArray_cursor {c : Config} (base : Mutator c) (frame : ArrayListState c)
    (array : Remset c) (published : Nat) (target : frame.target = .tls)
    (cursor : ArrayCursor ⟨frame, array⟩ published)
    (returned : inArrayCode base.returnPC = false) :
    PrivateArray.cursor ⟨{ base with
      arrayCall := frame
      pc := arrayMutatorPC frame.target frame.pc }, array, published⟩ := by
  cases pc : frame.pc <;>
    simp_all [PrivateArray.cursor, ArrayCursor, arrayMutatorPC, inArrayCode]

private theorem imageArray_cursor {c : Config} (base : Mutator c) (frame : ArrayListState c)
    (array : Remset c) (published : Nat) (target : frame.target = .image)
    (length : array.len = published)
    (returned : inArrayCode base.returnPC = false) :
    PrivateArray.cursor ⟨{ base with
      arrayCall := frame
      pc := arrayMutatorPC frame.target frame.pc }, array, published⟩ := by
  cases pc : frame.pc <;>
    simp_all [PrivateArray.cursor, arrayMutatorPC, inArrayCode]

private def FreshArrayEntry {c : Config} (m : Mutator c) : Prop :=
  (m.pc = .rootLengthLoad ∧ m.arrayCall = {}) ∨
  (m.pc = .imageLengthLoad ∧ m.arrayCall = { target := .image })

set_option maxHeartbeats 2000000 in
private theorem nonArray_instruction_fresh {c : Config} (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) (code : inArrayCode m.pc ≠ true)
    (returned : inArrayCode m.returnPC = false)
    (nextCode : inArrayCode (mutatorInstruction c tid m obs).next.pc = true) :
    FreshArrayEntry (mutatorInstruction c tid m obs).next := by
  cases pc : m.pc <;> simp [pc, inArrayCode] at code
  all_goals simp [FreshArrayEntry, pc, inArrayCode, mutatorInstruction,
    advance, emit, readHeader, readPointer, rootCall, afterBarrier, afterParentGC] at nextCode ⊢
  all_goals repeat' (split at * <;> try simp_all [inArrayCode])

set_option maxHeartbeats 2000000 in
private theorem nonArray_instruction_return {c : Config} (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) (code : inArrayCode m.pc ≠ true)
    (returned : inArrayCode m.returnPC = false) :
    inArrayCode (mutatorInstruction c tid m obs).next.returnPC = false := by
  cases pc : m.pc <;> simp [pc, inArrayCode] at code
  all_goals simp [pc, inArrayCode, mutatorInstruction, advance, emit, readHeader,
    readPointer, rootCall, afterBarrier, afterParentGC]
  all_goals repeat' (split at * <;> try simp_all [inArrayCode])

private theorem nonArray_instruction_cursor {c : Config} (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) (array : Remset c) (published : Nat)
    (code : inArrayCode m.pc ≠ true) (length : array.len = published)
    (returned : inArrayCode m.returnPC = false) :
    PrivateArray.cursor ⟨(mutatorInstruction c tid m obs).next, array, published⟩ := by
  refine ⟨?_, nonArray_instruction_return tid m obs code returned⟩
  by_cases nextCode : inArrayCode (mutatorInstruction c tid m obs).next.pc = true
  · rcases nonArray_instruction_fresh tid m obs code returned nextCode with
      ⟨pc, initial⟩ | ⟨pc, initial⟩
    all_goals simp [pc, initial, ArrayCursor,
      arrayMutatorPC, inArrayCode, length]
  · simp [nextCode, length]

/-- `bbfa0ce4150 src/support/arraylist.c:42-70`: each source instruction
preserves the private cursor, including the visible length/item gap. -/
theorem privateArray_cursor_step {c : Config} (tid : ThreadId c)
    (s : PrivateArray c) (obs : Observation c)
    (cursor : s.cursor) (observed : s.observes obs)
    (successful : s.frame.allocationSuccess obs) : (s.step tid obs).cursor := by
  by_cases code : inArrayCode s.frame.pc = true
  · have instruction := mutator_arrayInstruction tid s.frame obs code
    have shape := cursor.1
    simp only [code, ↓reduceIte] at shape
    have notCounter : s.frame.pc ≠ .rootNptrStore := by
      intro pc
      simp [pc, inArrayCode] at code
    cases target : s.frame.arrayCall.target with
    | tls =>
        have arrayCursor : ArrayCursor ⟨s.frame.arrayCall, s.array⟩ s.published := by simpa [target] using shape.2
        have advance := arrayCursor_step tid s.frame.call.parent ⟨s.frame.arrayCall, s.array⟩ obs s.published
          arrayCursor (observed.1 code target) (successful code)
        have lifted := tlsArray_cursor s.frame
          (arrayListInstruction c tid s.frame.call.parent s.frame.arrayCall obs).next
          (arrayListEffect s.array s.frame.arrayCall s.frame.call.parent)
          (arrayPublished s.frame.arrayCall s.published)
          ((arrayList_target _ _ _ _).trans target) advance cursor.2
        simpa [PrivateArray.step, instruction, arrayMutatorInstruction, code, target,
          PrivateArray.cursor] using lifted
    | image =>
        have length : s.array.len = s.published := by simpa [target] using shape.2
        have lifted := imageArray_cursor s.frame
          (arrayListInstruction c tid s.frame.call.parent s.frame.arrayCall obs).next
          s.array s.published ((arrayList_target _ _ _ _).trans target) length cursor.2
        simpa [PrivateArray.step, instruction, arrayMutatorInstruction, code, target,
          notCounter, PrivateArray.cursor] using lifted
  · have length : s.array.len = s.published := by simpa [PrivateArray.cursor, code] using cursor.1
    have noCode : inArrayCode s.frame.pc = false := by
      cases value : inArrayCode s.frame.pc <;> simp_all
    let array := if s.frame.pc = .rootNptrStore then
        if s.frame.count = 0x7fffffff then s.array else { s.array with nptr := s.frame.count + 1 }
      else s.array
    have nextLength : array.len = s.published := by
      by_cases counter : s.frame.pc = .rootNptrStore
      · simp only [array, counter, ite_true]
        split <;> simp [length]
      · simp [array, counter, length]
    have lifted := nonArray_instruction_cursor tid s.frame obs array s.published code nextLength cursor.2
    simpa [PrivateArray.step, noCode, array] using lifted

/-- `bbfa0ce4150 src/gc-stock.c:1681`,
`src/support/arraylist.c:70`: membership uses only published entries. -/
def PrivateArray.contains {c : Config} (s : PrivateArray c) (parent : ObjectId c) : Prop :=
  ∃ index, index < s.published ∧ s.array.items index = some parent

private theorem arrayEffect_preserves {c : Config} (array : Remset c) (s : ArrayListState c)
    (published : Nat) (appended parent : ObjectId c) (cursor : ArrayCursor ⟨s, array⟩ published)
    (member : ∃ index, index < published ∧ array.items index = some parent) :
    ∃ index, index < arrayPublished s published ∧
      (arrayListEffect array s appended).items index = some parent := by
  obtain ⟨index, bound, value⟩ := member
  by_cases store : s.pc = .pushItem
  · have current := cursor
    simp only [ArrayCursor, store] at current
    have push : s.pushLen = published + 1 := current.2.2.2.2
    have distinct : index ≠ published := by omega
    exact ⟨index, by simp [arrayPublished, store, push]; omega,
      by simpa [arrayListEffect, store, push, distinct] using value⟩
  · refine ⟨index, by simpa [arrayPublished, store] using bound, ?_⟩
    cases pc : s.pc <;> simp_all [arrayListEffect]
    all_goals split <;> simpa using value

/-- `bbfa0ce4150 src/support/arraylist.c:42-70`: a valid success cursor
preserves previously published entries. -/
theorem privateArray_contains_step {c : Config} (tid : ThreadId c)
    (s : PrivateArray c) (obs : Observation c) (parent : ObjectId c)
    (cursor : s.cursor) (member : s.contains parent) : (s.step tid obs).contains parent := by
  by_cases code : inArrayCode s.frame.pc = true
  · by_cases target : s.frame.arrayCall.target = .tls
    · have source : s.frame.pc = arrayMutatorPC s.frame.arrayCall.target s.frame.arrayCall.pc ∧
          ArrayCursor ⟨s.frame.arrayCall, s.array⟩ s.published := by
        simpa [PrivateArray.cursor, code, target] using cursor.1
      have current := source.2
      have survives := arrayEffect_preserves s.array s.frame.arrayCall s.published
        s.frame.call.parent parent current member
      simpa [PrivateArray.step, PrivateArray.contains, code, target] using survives
    · have notCounter : s.frame.pc ≠ .rootNptrStore := by
        intro pc
        simp [pc, inArrayCode] at code
      simpa [PrivateArray.step, PrivateArray.contains, code, target, notCounter] using member
  · cases pc : s.frame.pc <;> simp_all [PrivateArray.step, PrivateArray.contains, inArrayCode]
    all_goals split <;> simpa [PrivateArray.contains] using member

/-- `bbfa0ce4150 src/gc-stock.c:1681`: the actual item store publishes
its parent in the array, independently of header-read choices. -/
theorem privateArray_item_publishes {c : Config} (tid : ThreadId c)
    (s : PrivateArray c) (obs : Observation c) (store : s.frame.pc = .rootItemStore)
    (cursor : s.cursor) : (s.step tid obs).contains s.frame.call.parent := by
  have source := cursor.1
  simp only [store, inArrayCode, ↓reduceIte] at source
  have shape := (arrayItem_pc s.frame.arrayCall.target s.frame.arrayCall.pc).1 source.1.symm
  obtain ⟨target, pc⟩ := shape
  have current : ArrayCursor ⟨s.frame.arrayCall, s.array⟩ s.published := by simpa [target] using source.2
  simp only [ArrayCursor, pc] at current
  have push : s.frame.arrayCall.pushLen = s.published + 1 := current.2.2.2.2
  refine ⟨s.published, ?_, ?_⟩ <;>
    simp [PrivateArray.step, store, inArrayCode, target, pc,
      arrayPublished, arrayListEffect, push]

/-- `bbfa0ce4150 src/gc-interface.h:315`,
`src/gc-stock.c:1679-1682,3092-3104`: at a caller stopping boundary,
the logical publication length equals the C array length. -/
theorem privateArray_boundary {c : Config} (s : PrivateArray c)
    (cursor : s.cursor) (outside : s.frame.pc = .outside) : s.array.len = s.published := by
  simpa [PrivateArray.cursor, outside, inArrayCode] using cursor.1

/-- `bbfa0ce4150 src/gc-stock.c:1692`,
`src/support/arraylist.c:64,70`: active logical array entries. -/
def Remset.contains {c : Config} (array : Remset c) (parent : ObjectId c) : Prop :=
  ∃ index, index < array.len ∧ array.items index = some parent

/-- `src/support/arraylist.c:40-70`: successful arraylist executions
preserve previously published entries. -/
theorem replayArray_preserves {c : Config} (tid : ThreadId c) (appended parent : ObjectId c)
    (trace : List (Observation c)) (s : ArrayExecutionState c) (published : Nat)
    (cursor : ArrayCursor s published) (observed : arrayTraceObserves c tid appended trace s)
    (successful : arrayTraceSuccess c tid appended trace s)
    (member : ∃ index, index < published ∧ s.array.items index = some parent) :
    ∃ finalPublished, ArrayCursor (replayArray c tid appended trace s) finalPublished ∧
      ∃ index, index < finalPublished ∧
        (replayArray c tid appended trace s).array.items index = some parent := by
  induction trace generalizing s published with
  | nil => exact ⟨published, cursor, member⟩
  | cons obs rest ih =>
      have nextCursor := arrayCursor_step tid appended s obs published cursor observed.1 successful.1
      have nextMember := arrayEffect_preserves s.array s.frame published appended parent cursor member
      exact ih (arrayStep c tid appended s obs) (arrayPublished s.frame published)
        nextCursor observed.2 successful.2 nextMember

/-- `bbfa0ce4150 src/gc-stock.c:1691-1693`: the source image-lock
critical section, retaining each length/item instruction separately. -/
structure ImageSectionState (c : Config) where
  frame : Mutator c
  array : Remset c
  actions : List (MemoryAction c) := []

/-- `bbfa0ce4150 src/gc-stock.c:1691-1693`,
`src/support/arraylist.c:40-70`: a mutex section executes the same arraylist
microprogram as the TLS caller, including malloc/realloc returning NULL.
The lock and completed-section unlock surround its actual memory actions. -/
def executeImageSection {c : Config} (tid : ThreadId c) (frame : Mutator c)
    (array : Remset c) (observations : List (Observation c)) : ImageSectionState c :=
  let initial : ArrayExecutionState c := ⟨{ target := .image }, array⟩
  let result := replayArray c tid frame.call.parent observations initial
  { frame := { frame with
      arrayCall := result.frame
      pc := if result.frame.pc = .finished then frame.returnPC
        else arrayMutatorPC result.frame.target result.frame.pc }
    array := result.array
    actions := [.lock 0] ++ arrayTraceActions c tid frame.call.parent observations initial ++
      (if result.frame.pc = .finished then [.unlock 0] else []) }

/-- `bbfa0ce4150 src/gc-stock.c:1691-1693`: the actual source PCs
produce the logical append, finish with unlock, and preserve the return PC. -/
theorem executeImageSection_effects {c : Config} (tid : ThreadId c) (frame : Mutator c)
    (array : Remset c) (observations : List (Observation c))
    (finished : (replayArray c tid frame.call.parent observations
      ⟨{ target := .image }, array⟩).frame.pc = .finished) :
    (executeImageSection tid frame array observations).frame.pc = frame.returnPC ∧
    (executeImageSection tid frame array observations).actions =
      [.lock 0] ++ arrayTraceActions c tid frame.call.parent observations
        ⟨{ target := .image }, array⟩ ++ [.unlock 0] := by
  simp [executeImageSection, finished]

/-- `bbfa0ce4150 src/gc-stock.c:1691-1693`: a completed section
starts at the actual image-lock PC and retains its source invocation.
Its endpoint is computed by the source instructions. -/
structure ImageSourceSection (c : Config) where
  tid : ThreadId c
  frame : Mutator c
  before : Remset c
  after : Remset c
  observations : List (Observation c)
  entry : frame.pc = .imageLock
  returnPC : frame.returnPC ∈ [.returnBarrier, .outside]
  observed : arrayTraceObserves c tid frame.call.parent observations ⟨{ target := .image }, before⟩
  finished : (replayArray c tid frame.call.parent observations
    ⟨{ target := .image }, before⟩).frame.pc = .finished
  completed : after = (executeImageSection tid frame before observations).array

def ImageSourceSection.successful {c : Config} (critical : ImageSourceSection c) : Prop :=
  arrayTraceSuccess c critical.tid critical.frame.call.parent critical.observations
    ⟨{ target := .image }, critical.before⟩

def ImageSourceSection.actions {c : Config} (critical : ImageSourceSection c) :
    List (MemoryAction c) :=
  (executeImageSection critical.tid critical.frame critical.before critical.observations).actions

theorem imageSourceSection_preserves {c : Config} (critical : ImageSourceSection c)
    (successful : critical.successful)
    (parent : ObjectId c) (member : critical.before.contains parent) : critical.after.contains parent := by
  have cursor : ArrayCursor (⟨{ target := .image }, critical.before⟩ : ArrayExecutionState c)
      critical.before.len := by simp [ArrayCursor]
  obtain ⟨published, finalCursor, index, bound, value⟩ := replayArray_preserves critical.tid
    critical.frame.call.parent parent critical.observations _ critical.before.len cursor
    critical.observed successful member
  have length : (replayArray c critical.tid critical.frame.call.parent critical.observations
      ⟨{ target := .image }, critical.before⟩).array.len = published := by
    simpa [ArrayCursor, critical.finished] using finalCursor.2
  exact ⟨index, by simpa [critical.completed, executeImageSection, length] using bound,
    by simpa [critical.completed, executeImageSection] using value⟩

/-- `bbfa0ce4150 src/gc-stock.c:1691-1693`: the critical section's
actual actions occur in source order in the shared candidate. Successful
lock/unlock positions identify its mutex interval. -/
structure RecordedImageSection (c : Config) (candidate : Candidate (Location c) (Value c)) where
  source : ImageSourceSection c
  events : List candidate.Id
  lock : candidate.Id
  unlock : candidate.Id
  ordered : events.Pairwise (fun a b => a.val < b.val)
  first : events.head? = some lock
  last : events.getLast? = some unlock
  lockAction : (candidate.event lock).action = .lock 0
  unlockAction : (candidate.event unlock).action = .unlock 0
  actions : events.map (fun i => (candidate.event i).action) = source.actions
  threads : ∀ i ∈ events, (candidate.event i).thread = source.tid.val + 1

/-- `bbfa0ce4150 src/gc-stock.c:1691-1693`: arbitrary finite histories
of completed source sections. Each endpoint feeds the next exact length
read; permanent image entries have no source clear operation. -/
inductive ImagePublicationHistory (c : Config) (candidate : Candidate (Location c) (Value c))
    (initial : Remset c) : Remset c → List (RecordedImageSection c candidate) → Prop where
  | initial : ImagePublicationHistory c candidate initial initial []
  | next {array sections} : ImagePublicationHistory c candidate initial array sections →
      (critical : RecordedImageSection c candidate) → critical.source.before = array →
      ImagePublicationHistory c candidate initial critical.source.after (sections ++ [critical])

/-- `bbfa0ce4150 src/gc-stock.c:1691-1693`: all previously active
image entries survive every completed source section. -/
theorem imagePublicationHistory_preserves {c : Config}
    {candidate : Candidate (Location c) (Value c)} {initial after : Remset c}
    {sections : List (RecordedImageSection c candidate)}
    (history : ImagePublicationHistory c candidate initial after sections)
    (successful : ∀ critical ∈ sections, critical.source.successful)
    (parent : ObjectId c) (member : initial.contains parent) : after.contains parent := by
  induction history with
  | initial => exact member
  | next history critical previous ih =>
      have prior := ih (by intro interval contains; exact successful interval (List.mem_append_left _ contains))
      exact imageSourceSection_preserves critical.source (successful critical (by simp)) parent
        (by simpa [previous] using prior)

/-- `bbfa0ce4150 src/gc-stock.c:1691-1693,3383-3391`: the explicit
mutex/publication composition boundary. Completed real source sections
are nonoverlapping and account for every image length/item store before
the stopping boundary. Allocator effects retain their stated projection.
All image stores belong to those source sections. -/
def ImageMutexBoundary {c : Config} (candidate : Candidate (Location c) (Value c))
    (before after : Remset c) : Prop :=
  ∃ sections, ImagePublicationHistory c candidate before after sections ∧
    (∀ critical ∈ sections, critical.source.successful) ∧
    sections.Pairwise (fun a b => a.unlock.val < b.lock.val) ∧
    ∀ i : candidate.Id,
      ((∃ n, (candidate.event i).action = .plainStore .imageLen (.number n)) ∨
       ∃ index parent, (candidate.event i).action =
         .plainStore (.imageItem index) (.pointer (some parent))) →
      ∃ critical ∈ sections, i ∈ critical.events

theorem imageMutexBoundary_preserves {c : Config}
    {candidate : Candidate (Location c) (Value c)} {before after : Remset c}
    (boundary : ImageMutexBoundary candidate before after) (parent : ObjectId c)
    (member : before.contains parent) : after.contains parent := by
  obtain ⟨sections, history, successful, nonoverlap, stores⟩ := boundary
  exact imagePublicationHistory_preserves history successful parent member

/-- `bbfa0ce4150 src/gc-stock.c:1671-1702`: each mutator owns its
TLS remset array. The C11 event array is shared; source frames and array
cursors remain per-thread. -/
structure ProtocolState (c : Config) where
  memory : Candidate (Location c) (Value c)
  thread : ThreadId c → PrivateArray c

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: execute one real source
instruction and its TLS-array stores, with automatic dependencies. -/
def protocolInstruction {c : Config} (s : ProtocolState c) (tid : ThreadId c)
    (obs : Observation c) (choice : Choice) : ProtocolState c :=
  let threadState := s.thread tid
  let instruction := mutatorInstruction c tid threadState.frame obs
  { memory := appendInstruction s.memory tid instruction choice threadState.frame.support
    thread := fun other => if other = tid then
      { threadState.step tid obs with frame := instructionThread s.memory threadState.frame instruction }
      else s.thread other }

/-- `bbfa0ce4150 src/gc-interface.h:315,323-345,355-366`:
arbitrary source interleavings and arbitrarily many valid invocations per
thread. A new call starts only after the previous no-safepoint region ends. -/
inductive ProtocolPrefix (c : Config) (initial : ProtocolState c) : ProtocolState c → Prop where
  | initial : ProtocolPrefix c initial initial
  | instruction {s} : ProtocolPrefix c initial s →
      (tid : ThreadId c) → (obs : Observation c) → (choice : Choice) →
      (s.thread tid).observes obs → ProtocolPrefix c initial (protocolInstruction s tid obs choice)
  | beginCall {s} : ProtocolPrefix c initial s →
      (tid : ThreadId c) → (call : Call c) → CallValid c call →
      (s.thread tid).frame.pc = .outside →
      ProtocolPrefix c initial
        { s with thread := fun other => if other = tid then
            { s.thread tid with frame := { call := call, pc := entryPC call.kind } } else s.thread other }

/-- The allocation-success restriction is separate from the source execution
relation, which retains both allocator outcomes. -/
inductive SuccessfulProtocolPrefix (c : Config) (initial : ProtocolState c) : ProtocolState c → Prop where
  | initial : SuccessfulProtocolPrefix c initial initial
  | instruction {s} : SuccessfulProtocolPrefix c initial s →
      (tid : ThreadId c) → (obs : Observation c) → (choice : Choice) →
      (s.thread tid).observes obs → (s.thread tid).frame.allocationSuccess obs →
      SuccessfulProtocolPrefix c initial (protocolInstruction s tid obs choice)
  | beginCall {s} : SuccessfulProtocolPrefix c initial s →
      (tid : ThreadId c) → (call : Call c) → CallValid c call →
      (s.thread tid).frame.pc = .outside →
      SuccessfulProtocolPrefix c initial
        { s with thread := fun other => if other = tid then
            { s.thread tid with frame := { call := call, pc := entryPC call.kind } } else s.thread other }

theorem successfulProtocol_source {c : Config} {initial s : ProtocolState c}
    (history : SuccessfulProtocolPrefix c initial s) : ProtocolPrefix c initial s := by
  induction history with
  | initial => exact .initial
  | instruction history tid obs choice observed successful ih =>
      exact .instruction ih tid obs choice observed
  | beginCall history tid call valid outside ih => exact .beginCall ih tid call valid outside

private theorem protocolInstruction_cursor {c : Config} (s : ProtocolState c)
    (tid : ThreadId c) (obs : Observation c) (choice : Choice)
    (cursors : ∀ t, (s.thread t).cursor) (observed : (s.thread tid).observes obs)
    (successful : (s.thread tid).frame.allocationSuccess obs) :
    ∀ t, ((protocolInstruction s tid obs choice).thread t).cursor := by
  intro t
  by_cases same : t = tid
  · subst t
    simpa [protocolInstruction, instructionThread, PrivateArray.cursor, PrivateArray.step]
      using privateArray_cursor_step tid (s.thread tid) obs (cursors tid) observed successful
  · simpa [protocolInstruction, same] using cursors t

/-- `bbfa0ce4150 src/support/arraylist.c:42-70`: no interleaving can
invalidate the owning thread's append cursor before collector entry. -/
theorem protocol_cursor {c : Config} {initial s : ProtocolState c}
    (history : SuccessfulProtocolPrefix c initial s) (cursors : ∀ tid, (initial.thread tid).cursor) :
    ∀ tid, (s.thread tid).cursor := by
  induction history with
  | initial => exact cursors
  | instruction history tid obs choice observed successful ih =>
      exact protocolInstruction_cursor _ tid obs choice ih observed successful
  | beginCall history tid call valid outside ih =>
      intro t
      by_cases same : t = tid
      · subst t
        have length := privateArray_boundary _ (ih tid) outside
        cases kind : call.kind <;>
          simp_all [PrivateArray.cursor, entryPC, inArrayCode]
      · simpa [same] using ih t

private theorem protocolInstruction_contains {c : Config} (s : ProtocolState c)
    (tid : ThreadId c) (obs : Observation c) (choice : Choice)
    (cursors : ∀ t, (s.thread t).cursor) (parent : ObjectId c) (t : ThreadId c)
    (member : (s.thread t).contains parent) :
    ((protocolInstruction s tid obs choice).thread t).contains parent := by
  by_cases same : t = tid
  · subst t
    simpa [protocolInstruction, instructionThread, PrivateArray.contains]
      using privateArray_contains_step tid (s.thread tid) obs parent (cursors tid) member
  · simpa [protocolInstruction, same] using member

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: for every source history,
a claimed parent is already in a published TLS entry or its claiming
thread still owes the source item store. -/
theorem protocol_claim_coverage {c : Config} {initial s : ProtocolState c}
    (history : SuccessfulProtocolPrefix c initial s)
    (cursors : ∀ tid, (initial.thread tid).cursor)
    (noInitialClaims : ∀ parent, ¬ Occurred initial.memory (ActionClaims parent)) :
    ∀ parent, Occurred s.memory (ActionClaims parent) →
      (∃ tid, (s.thread tid).contains parent) ∨
      ∃ tid, AppendPending (s.thread tid).frame parent := by
  induction history with
  | initial => intro parent claim; exact False.elim (noInitialClaims parent claim)
  | beginCall history tid call valid outside ih =>
      intro parent claim
      rcases ih parent claim with ⟨t, member⟩ | ⟨t, pending⟩
      · exact Or.inl ⟨t, by by_cases same : t = tid <;> simp_all [PrivateArray.contains]⟩
      · by_cases same : t = tid
        · subst t
          simp [AppendPending, outside, inArrayCode] at pending
        · exact Or.inr ⟨t, by simpa [same] using pending⟩
  | @instruction state history tid obs choice observed successful ih =>
      intro parent claim
      have currentCursors := protocol_cursor history cursors
      have claimCases := (occurred_appendInstruction _ _ _ _ _ _).1 claim
      rcases claimCases with oldClaim | ⟨action, emitted, newClaim⟩
      · rcases ih parent oldClaim with ⟨t, member⟩ | ⟨t, pending⟩
        · exact Or.inl ⟨t, protocolInstruction_contains state tid obs choice currentCursors parent t member⟩
        · by_cases same : t = tid
          · subst t
            by_cases store : (state.thread tid).frame.pc = .rootItemStore
            · have member := privateArray_item_publishes tid (state.thread tid) obs store (currentCursors tid)
              have owner : (state.thread tid).frame.call.parent = parent := pending.1
              exact Or.inl ⟨tid, by simpa [protocolInstruction, PrivateArray.contains, owner] using member⟩
            · rcases appendPending_instruction tid (state.thread tid).frame obs parent pending with appended | remains
              · exact False.elim (store appended.1)
              · exact Or.inr ⟨tid, by simp [protocolInstruction, appendPending_thread, remains]⟩
          · exact Or.inr ⟨t, by simpa [protocolInstruction, same] using pending⟩
      · have pending := claimed_instruction_pending tid (state.thread tid).frame obs parent action emitted newClaim
        exact Or.inr ⟨tid, by simp [protocolInstruction, appendPending_thread, pending]⟩

/-- `bbfa0ce4150 src/gc-interface.h:315`,
`src/gc-stock.c:1679-1682,3383-3387`: a completed no-safepoint stopping
boundary contains every claimed parent in an active remembered-set entry. -/
theorem protocol_claim_in_remset {c : Config} {initial s : ProtocolState c}
    (history : SuccessfulProtocolPrefix c initial s) (cursors : ∀ tid, (initial.thread tid).cursor)
    (noInitialClaims : ∀ parent, ¬ Occurred initial.memory (ActionClaims parent))
    (stopped : ∀ tid, (s.thread tid).frame.pc = .outside) :
    ∀ parent, Occurred s.memory (ActionClaims parent) →
      ∃ tid index, index < (s.thread tid).array.len ∧ (s.thread tid).array.items index = some parent := by
  intro parent claim
  rcases protocol_claim_coverage history cursors noInitialClaims parent claim with ⟨tid, index, bound, value⟩ | ⟨tid, pending⟩
  · exact ⟨tid, index, by simpa [privateArray_boundary _ (protocol_cursor history cursors tid) (stopped tid)] using bound, value⟩
  · simp [AppendPending, stopped tid, inArrayCode] at pending

/-- `bbfa0ce4150 src/support/arraylist.c:42-70`: every initial
published TLS entry survives arbitrary intervening valid mutator calls. -/
theorem protocol_preserves_member {c : Config} {initial s : ProtocolState c}
    (history : SuccessfulProtocolPrefix c initial s) (cursors : ∀ tid, (initial.thread tid).cursor)
    (parent : ObjectId c) (tid : ThreadId c) (member : (initial.thread tid).contains parent) :
    (s.thread tid).contains parent := by
  induction history with
  | initial => exact member
  | @instruction state history selected obs choice observed successful ih =>
      exact protocolInstruction_contains state selected obs choice (protocol_cursor history cursors) parent tid ih
  | beginCall history selected call valid outside ih =>
      by_cases same : tid = selected <;> simp_all [PrivateArray.contains]

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1704-1748`: a single invocation's source projection.
Other threads may execute between any two of these steps. The list retains
its emitted actions, and the observation contract is checked at each PC. -/
inductive InvocationRun (c : Config) (tid : ThreadId c) (call : Call c)
    (target : BarrierTarget c) : Mutator c → List (MemoryAction c) → Prop where
  | initial : InvocationRun c tid call target { call := call, pc := entryPC call.kind } []
  | next {m actions} : InvocationRun c tid call target m actions →
      (obs : Observation c) → BarrierObservation m obs target →
      InvocationRun c tid call target (mutatorInstruction c tid m obs).next
        (actions ++ (mutatorInstruction c tid m obs).action.toList)

private theorem instruction_call {c : Config} (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) :
    (mutatorInstruction c tid m obs).next.call = m.call := by
  cases pc : m.pc <;>
    simp [mutatorInstruction, pc, advance, emit, readHeader, readPointer, rootCall,
      arrayMutatorInstruction]
  all_goals repeat' (split <;> try simp_all)

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`: source PCs never change
the invocation's owner, immutable source, copied spans or store value. -/
theorem invocation_call {c : Config} {tid : ThreadId c} {call : Call c}
    {target : BarrierTarget c} {m : Mutator c} {actions : List (MemoryAction c)}
    (run : InvocationRun c tid call target m actions) : m.call = call := by
  induction run with
  | initial => rfl
  | next run obs observed ih => exact (instruction_call _ _ _).trans ih

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1704-1748`: every complete invocation that can retain
the selected unmarked field emits a queue-root claim under the precise
header and copied-field observation contract. -/
theorem invocation_claims {c : Config} {tid : ThreadId c} {call : Call c}
    {target : BarrierTarget c} {m : Mutator c} {actions : List (MemoryAction c)}
    (valid : CallValid c call) (targeted : TargetsCall call target)
    (run : InvocationRun c tid call target m actions)
    (complete : m.pc = .outside) : ∃ action ∈ actions, ActionClaims call.parent action := by
  have invariant : ∀ {m actions}, InvocationRun c tid call target m actions →
      (∃ action ∈ actions, ActionClaims call.parent action) ∨ BarrierPending m target := by
    intro m actions run
    induction run with
    | initial => exact Or.inr (barrierPending_entry call target targeted)
    | @next before previous run obs observed ih =>
        rcases ih with ⟨action, member, claimed⟩ | pending
        · exact Or.inl ⟨action, List.mem_append_left _ member, claimed⟩
        · have callEq := invocation_call run
          have targets : TargetsCall before.call target := by simpa [callEq] using targeted
          have beforeValid : CallValid c before.call := by simpa [callEq] using valid
          rcases barrierPending_instruction tid before obs target beforeValid targets pending observed with claimed | remains
          · obtain ⟨header, emitted, old⟩ := claimed
            refine Or.inl ⟨.rmw (.header call.parent) .relaxed (.header header) (.header header.clearOld), ?_, header, rfl, old⟩
            apply List.mem_append_right
            simp [callEq] at emitted
            simp [emitted]
          · exact Or.inr remains
  rcases invariant run with claimed | pending
  · exact claimed
  · have callEq := invocation_call run
    cases kind : call.kind <;> simp_all [BarrierPending]

end JuliaLean.CRuntime.WriteBarrier

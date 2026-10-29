import JuliaLean.CRuntime.ParallelMark.Core

namespace JuliaLean.CRuntime.ParallelMark

open Memory

/-- Parameter instance of the same C queue algorithm, `bbfa0ce4150`,
`src/work-stealing-queue.h:24-105`. Three participants, three distinct
pointer publications and a two-slot circular buffer suffice for slot reuse. -/
def staleThiefConfig : Config :=
  { threads := 3, arrays := 1, items := 4, initiator := 0,
    firstCollector := 1, markThreads := 2, present := fun _ => true,
    initialPower := fun _ _ => 1 }

private def itemA : Payload := .pointer 0 1
private def itemB : Payload := .pointer 1 2
private def itemC : Payload := .pointer 2 3

/-- Checkpoint before two `gc_ptr_queue_steal_from` calls and an owner
scanner (`bbfa0ce4150`, `src/gc-stock.c:1830-1855,2840,2899`). The owner
published A. Both thieves have fresh registers. Array fields and slot bytes
have initialization events. -/
def staleThiefInitial : State :=
  { threads := fun tid =>
      if tid = 0 then { pc := 2840, processing := true, result := .pointer 3 4 }
      else {
        pc := 2900,
        call := some {
          operation := .steal, owner := 0, kind := .pointer,
          pc := 0, returnPC := 2900 } },
    arrays := fun _ =>
      { contents := { buffer := #[itemA, .zero], capacity := 2, mask := 1 },
        power := 1, headerLive := true },
    buffers := fun _ => { bytes := 16, live := true },
    reclaimSet := fun _ => [],
    execution := ⟨#[
      { thread := 0, action := .init (.top 0 .pointer) (.i64 0) },
      { thread := 0, action := .init (.bottom 0 .pointer) (.i64 1) },
      { thread := 0, action := .init (.array 0 .pointer) (.address 0) },
      { thread := 0, action := .init (.capacity 0) (.i32 2) },
      { thread := 0, action := .init (.mask 0) (.i32 1) },
      { thread := 0, action := .init (.slot 0 0) (.payload itemA) },
      { thread := 0, action := .init (.slot 0 1) (.payload .zero) },
      { thread := 0, action := .init (.buffer 0) (.address 0) }]⟩ }

private def read64 (value : Int64) (source : Nat) : Choice :=
  { i64 := value, memory := { readFrom := some source } }

private def read32 (value : Int32) (source : Nat) : Choice :=
  { i32 := value, memory := { readFrom := some source } }

private def readAddress (source : Nat) : Choice :=
  { address := 0, memory := { readFrom := some source } }

/-- Stops immediately before the memcpy at `bbfa0ce4150`,
`src/work-stealing-queue.h:101`. -/
private def stealPrefix (tid fenceRank : Nat) : List (Nat × Choice) :=
  [(tid, noChoice), (tid, read64 0 0),
    (tid, { memory := { sc := fenceRank } }),
    (tid, read64 1 1), (tid, noChoice), (tid, readAddress 2)]

/-- A complete non-resizing owner push (`bbfa0ce4150`,
`src/work-stealing-queue.h:54-70`, `src/gc-stock.c:1836-1840`). -/
private def ownerPush (value : Payload) (bottom : Int64)
    (bottomSource bottomRank : Nat) : List (Nat × Choice) :=
  [(0, { scannerPush := some (.pointer, value) }), (0, noChoice),
    (0, read64 bottom bottomSource), (0, read64 1 19),
    (0, readAddress 2), (0, noChoice),
    (0, read32 2 3), (0, noChoice),
    (0, read32 1 4), (0, readAddress 7),
    (0, noChoice), (0, noChoice), (0, { memory := { mo := bottomRank } }),
    (0, noChoice), (0, noChoice), (0, noChoice)]

/-- T1 saves t=0,b=1 and the array pointer. T2 steals A. The owner pushes
B at slot 1, then C at reused slot 0. T1 copies C, loses strong CAS, and
clears its result (`bbfa0ce4150`, `src/work-stealing-queue.h:54-105`).
All SC and modification ranks and read-from choices are part of the trace. -/
def staleThiefSchedule : List (Nat × Choice) :=
  stealPrefix 1 0 ++ stealPrefix 2 1 ++
  [(2, read32 1 4), (2, readAddress 7),
    (2, { payload := itemA, memory := { readFrom := some 5 } }),
    (2, { i64 := 0, memory := { readFrom := some 0, mo := 1, sc := 2 } }),
    (2, noChoice)] ++
  ownerPush itemB 1 1 1 ++ ownerPush itemC 2 28 2 ++
  [(1, read32 1 4), (1, readAddress 7),
    (1, { payload := itemC, memory := { readFrom := some 35 } }),
    (1, { i64 := 1, memory := { readFrom := some 19, sc := 3 } }),
    (1, noChoice), (1, noChoice)]

def staleThiefFinal : State := run staleThiefConfig staleThiefSchedule staleThiefInitial

def staleThiefCandidate : Execution := staleThiefFinal.execution

set_option maxRecDepth 20000 in
theorem staleThiefFinal_fault : staleThiefFinal.fault = false := by decide

set_option maxRecDepth 20000 in
theorem staleThiefCandidate_eventCount : staleThiefCandidate.events.size = 42 := by decide

set_option maxRecDepth 20000 in
theorem staleThiefFinal_results :
    (staleThiefFinal.threads 2).result = itemA ∧
    (staleThiefFinal.threads 1).result = Payload.zero := by decide

set_option maxRecDepth 20000 in
theorem staleThiefFinal_ownerResult :
    (staleThiefFinal.threads 0).result = .pointer 3 4 := by decide

set_option maxRecDepth 20000 in
theorem staleThiefCandidate_slotReuse :
    (staleThiefCandidate.events[35]?).map Event.action =
      some (.plainStore (.slot 0 0) (.payload itemC)) ∧
    (staleThiefCandidate.events[40]?).map Event.action =
      some (.plainLoad (.slot 0 0) (.payload itemC)) ∧
    (staleThiefCandidate.events[41]?).map Event.action =
      some (.cas (.top 0 .pointer) .seqCst .seqCst (.i64 0) (.i64 1) (.i64 1)) := by
  decide

private abbrev staleThiefTrace : Execution := ⟨#[
  { thread := 0, action := .init (.top 0 .pointer) (.i64 0) },
  { thread := 0, action := .init (.bottom 0 .pointer) (.i64 1) },
  { thread := 0, action := .init (.array 0 .pointer) (.address 0) },
  { thread := 0, action := .init (.capacity 0) (.i32 2) },
  { thread := 0, action := .init (.mask 0) (.i32 1) },
  { thread := 0, action := .init (.slot 0 0) (.payload itemA) },
  { thread := 0, action := .init (.slot 0 1) (.payload .zero) },
  { thread := 0, action := .init (.buffer 0) (.address 0) },
  { thread := 1, action := .load (.top 0 .pointer) .acquire (.i64 0), readFrom := some 0 },
  { thread := 1, action := .fence .seqCst },
  { thread := 1, action := .load (.bottom 0 .pointer) .acquire (.i64 1), readFrom := some 1 },
  { thread := 1, action := .load (.array 0 .pointer) .relaxed (.address 0),
    readFrom := some 2, dependsOn := [8, 10] },
  { thread := 2, action := .load (.top 0 .pointer) .acquire (.i64 0), readFrom := some 0 },
  { thread := 2, action := .fence .seqCst, sc := 1 },
  { thread := 2, action := .load (.bottom 0 .pointer) .acquire (.i64 1), readFrom := some 1 },
  { thread := 2, action := .load (.array 0 .pointer) .relaxed (.address 0),
    readFrom := some 2, dependsOn := [12, 14] },
  { thread := 2, action := .plainLoad (.mask 0) (.i32 1),
    readFrom := some 4, dependsOn := [12, 14, 15] },
  { thread := 2, action := .plainLoad (.buffer 0) (.address 0),
    readFrom := some 7, dependsOn := [12, 14, 15] },
  { thread := 2, action := .plainLoad (.slot 0 0) (.payload itemA),
    readFrom := some 5, dependsOn := [12, 14, 16, 17] },
  { thread := 2, action := .cas (.top 0 .pointer) .seqCst .seqCst (.i64 0) (.i64 1) (.i64 0),
    readFrom := some 0, mo := 1, sc := 2, dependsOn := [12, 14] },
  { thread := 0, action := .load (.bottom 0 .pointer) .relaxed (.i64 1), readFrom := some 1 },
  { thread := 0, action := .load (.top 0 .pointer) .acquire (.i64 1), readFrom := some 19 },
  { thread := 0, action := .load (.array 0 .pointer) .relaxed (.address 0), readFrom := some 2 },
  { thread := 0, action := .plainLoad (.capacity 0) (.i32 2),
    readFrom := some 3, dependsOn := [22] },
  { thread := 0, action := .plainLoad (.mask 0) (.i32 1),
    readFrom := some 4, dependsOn := [23, 20, 21, 22] },
  { thread := 0, action := .plainLoad (.buffer 0) (.address 0),
    readFrom := some 7, dependsOn := [23, 20, 21, 22] },
  { thread := 0, action := .plainStore (.slot 0 1) (.payload itemB),
    dependsOn := [23, 20, 21, 24, 25] },
  { thread := 0, action := .fence .release, dependsOn := [23, 20, 21] },
  { thread := 0, action := .store (.bottom 0 .pointer) .relaxed (.i64 2),
    mo := 1, dependsOn := [23, 20, 21] },
  { thread := 0, action := .load (.bottom 0 .pointer) .relaxed (.i64 2), readFrom := some 28 },
  { thread := 0, action := .load (.top 0 .pointer) .acquire (.i64 1), readFrom := some 19 },
  { thread := 0, action := .load (.array 0 .pointer) .relaxed (.address 0), readFrom := some 2 },
  { thread := 0, action := .plainLoad (.capacity 0) (.i32 2),
    readFrom := some 3, dependsOn := [31] },
  { thread := 0, action := .plainLoad (.mask 0) (.i32 1),
    readFrom := some 4, dependsOn := [32, 29, 30, 31] },
  { thread := 0, action := .plainLoad (.buffer 0) (.address 0),
    readFrom := some 7, dependsOn := [32, 29, 30, 31] },
  { thread := 0, action := .plainStore (.slot 0 0) (.payload itemC),
    dependsOn := [32, 29, 30, 33, 34] },
  { thread := 0, action := .fence .release, dependsOn := [32, 29, 30] },
  { thread := 0, action := .store (.bottom 0 .pointer) .relaxed (.i64 3),
    mo := 2, dependsOn := [32, 29, 30] },
  { thread := 1, action := .plainLoad (.mask 0) (.i32 1),
    readFrom := some 4, dependsOn := [8, 10, 11] },
  { thread := 1, action := .plainLoad (.buffer 0) (.address 0),
    readFrom := some 7, dependsOn := [8, 10, 11] },
  { thread := 1, action := .plainLoad (.slot 0 0) (.payload itemC),
    readFrom := some 35, dependsOn := [8, 10, 38, 39] },
  { thread := 1, action := .cas (.top 0 .pointer) .seqCst .seqCst (.i64 0) (.i64 1) (.i64 1),
    readFrom := some 19, sc := 3, dependsOn := [8, 10] }]⟩

set_option maxRecDepth 20000 in
private theorem staleThiefCandidate_trace : staleThiefCandidate = staleThiefTrace := by rfl

private def staleThiefSB (a b : Fin 42) : Bool :=
  decide (8 ≤ a.val ∧ a.val < b.val ∧
    (a.val ≤ 11 ∧ (b.val ≤ 11 ∨ 38 ≤ b.val) ∨ 38 ≤ a.val ∨
      12 ≤ a.val ∧ b.val ≤ 19 ∨ 20 ≤ a.val ∧ b.val ≤ 37))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
set_option synthInstance.maxSize 4096 in
private theorem staleThief_sequencedBefore (a b : staleThiefTrace.Id) :
    staleThiefTrace.sequencedBefore a b = staleThiefSB a b := by
  have all : ∀ i j : Fin 42, staleThiefTrace.sequencedBefore i j = staleThiefSB i j := by
    decide +kernel
  exact all a b

private def staleThiefHB (a b : Fin 42) : Bool :=
  staleThiefSB a b ||
    decide (a.val < 8 ∧ 8 ≤ b.val) ||
    decide (12 ≤ a.val ∧ a.val ≤ 19 ∧ (21 ≤ b.val ∧ b.val ≤ 37 ∨ b.val = 41))

private def staleThiefHBEdge (a b : Fin 42) : Bool :=
  staleThiefSB a b ||
    decide (a.val < 8 ∧ 8 ≤ b.val) ||
    decide ((a.val = 13 ∨ a.val = 19) ∧ (b.val = 21 ∨ b.val = 30 ∨ b.val = 41))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
set_option synthInstance.maxSize 4096 in
private theorem staleThief_hbEdge (a b : staleThiefTrace.Id) :
    staleThiefTrace.hbEdge a b = staleThiefHBEdge a b := by
  have all : ∀ i j : Fin 42, staleThiefTrace.hbEdge i j = staleThiefHBEdge i j := by
    unfold Candidate.hbEdge Candidate.synchronizesWith
      Candidate.releaseEndpoint Candidate.acquireEndpoint
    simp only [staleThief_sequencedBefore]
    decide +kernel
  exact all a b

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
set_option synthInstance.maxSize 4096 in
private theorem staleThief_happensBefore (a b : staleThiefTrace.Id) :
    staleThiefTrace.happensBefore a b = staleThiefHB a b := by
  have contains : ∀ i j : Fin 42,
      staleThiefHBEdge i j = true → staleThiefHB i j = true := by decide +kernel
  have transitive : ∀ i j k : Fin 42, staleThiefHB i j = true →
      staleThiefHB j k = true → staleThiefHB i k = true := by decide +kernel
  have paths : ∀ i j : Fin 42, staleThiefHB i j = true →
      staleThiefHBEdge i j = true ∨
      (staleThiefHBEdge i 19 = true ∧ staleThiefHBEdge 19 j = true) ∨
      (staleThiefHBEdge i 21 = true ∧ staleThiefHBEdge 21 j = true) ∨
      (staleThiefHBEdge i 19 = true ∧ staleThiefHBEdge 19 21 = true ∧
        staleThiefHBEdge 21 j = true) := by
    decide +kernel
  have sound : staleThiefTrace.happensBefore a b = true → staleThiefHB a b = true := by
    intro h
    apply Candidate.closure_induction (fun i j => staleThiefHB i j = true) ?_ transitive h
    intro i j hij
    rw [staleThief_hbEdge i j] at hij
    exact contains i j hij
  have edge (i j : Fin 42) (h : staleThiefHBEdge i j = true) :
      staleThiefTrace.happensBefore i j = true := by
    apply Candidate.happensBefore_of_hbEdge
    rwa [staleThief_hbEdge i j]
  have complete : staleThiefHB a b = true → staleThiefTrace.happensBefore a b = true := by
    intro h
    rcases paths a b h with direct | via19 | via21 | viaBoth
    · exact edge a b direct
    · exact Candidate.happensBefore_trans (edge a 19 via19.1) (edge 19 b via19.2)
    · exact Candidate.happensBefore_trans (edge a 21 via21.1) (edge 21 b via21.2)
    · exact Candidate.happensBefore_trans (edge a 19 viaBoth.1)
        (Candidate.happensBefore_trans (edge 19 21 viaBoth.2.1) (edge 21 b viaBoth.2.2))
  cases ha : staleThiefTrace.happensBefore a b with
  | false =>
    cases hb : staleThiefHB a b with
    | false => rfl
    | true =>
      have h := complete hb
      rw [ha] at h
      cases h
  | true => exact (sound ha).symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
private theorem staleThief_wellFormed : staleThiefTrace.WellFormed := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
set_option synthInstance.maxSize 4096 in
private theorem staleThief_coherent : staleThiefTrace.Coherent := by
  unfold Candidate.Coherent
  simp only [staleThief_happensBefore]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
set_option synthInstance.maxSize 4096 in
private theorem staleThief_rmwAtomicity : staleThiefTrace.RMWAtomicity := by
  unfold Candidate.RMWAtomicity
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
set_option synthInstance.maxSize 32768 in
private theorem staleThief_scConsistent : staleThiefTrace.SCConsistent := by
  unfold Candidate.SCConsistent
  simp only [staleThief_happensBefore]
  decide +kernel

set_option maxRecDepth 20000 in
private theorem staleThief_mutexValid : staleThiefTrace.MutexValid := by
  unfold Candidate.MutexValid
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
set_option synthInstance.maxSize 4096 in
private theorem staleThief_justified : staleThiefTrace.Justified := by
  apply Candidate.justified_of_forward
  unfold Candidate.justificationEdge
  simp only [staleThief_happensBefore]
  decide +kernel

theorem staleThiefCandidate_consistent : staleThiefCandidate.consistent = true := by
  simp only [Candidate.consistent, decide_eq_true_eq]
  rw [staleThiefCandidate_trace]
  exact ⟨staleThief_wellFormed, staleThief_coherent, staleThief_rmwAtomicity,
    staleThief_scConsistent, staleThief_mutexValid, staleThief_justified⟩

set_option maxRecDepth 20000 in
theorem staleThiefCandidate_not_raceFree : staleThiefCandidate.dataRaceFree = false := by
  rw [staleThiefCandidate_trace]
  let _ : Decidable staleThiefTrace.RaceFree := by
    unfold Candidate.RaceFree
    infer_instance
  change decide staleThiefTrace.RaceFree = false
  rw [decide_eq_false_iff_not]
  intro raceFree
  have pair := raceFree 35 40 (by decide) (by decide) (by decide) (by decide)
  rw [staleThief_happensBefore, staleThief_happensBefore] at pair
  have unordered : staleThiefHB 35 40 = false ∧ staleThiefHB 40 35 = false := by decide
  simp only [unordered.1, unordered.2, Bool.false_eq_true, or_self] at pair

end JuliaLean.CRuntime.ParallelMark

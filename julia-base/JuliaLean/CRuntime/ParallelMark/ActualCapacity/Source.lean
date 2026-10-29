import JuliaLean.CRuntime.ParallelMark.Core
import JuliaLean.CRuntime.ParallelMark.Bounds

namespace JuliaLean.CRuntime.ParallelMark

open Memory

namespace ActualCapacity

def pointerCapacity : Nat := 2^18

/-- `bbfa0ce4150`, `src/gc-stock.h:94-95,479-493`. -/
def configuration : Config :=
  { threads := 3, arrays := 6, items := pointerCapacity + 3,
    initiator := 0, firstCollector := 1, markThreads := 2,
    present := fun _ => true,
    initialPower := fun _ kind => match kind with | .pointer => 18 | .chunk => 14 }

theorem configuration_wellFormed : configuration.WellFormed := by
  unfold Config.WellFormed
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro tid kind _ _
  cases kind <;> decide +revert

theorem configuration_sourceInitial : configuration.SourceInitial := by
  refine ⟨configuration_wellFormed, by decide, ?_⟩
  intro tid _ _
  exact ⟨rfl, rfl⟩

def initial : State := canonicalInitial configuration

theorem initial_owner : initial.threads 0 = { pc := 3394, markLoopReturnPC := 3406 } := rfl

theorem initial_collectors (worker : Fin 2) :
    initial.threads (worker.val + 1) = { pc := 4055, markLoopReturnPC := 4063 } := by
  have all : ∀ worker : Fin 2,
      initial.threads (worker.val + 1) = { pc := 4055, markLoopReturnPC := 4063 } := by decide
  exact all worker

theorem initial_eventCount : initial.execution.events.size = 47 := by decide

def initialQueueBase (tid : Nat) (kind : QueueKind) : Nat :=
  2 + 15 * tid + match kind with | .chunk => 0 | .pointer => 6

theorem initial_queue_event (tid : Fin 3) (kind : QueueKind) (field : Fin 6) :
    initial.execution.events[initialQueueBase tid.val kind + field.val]? =
      (initialQueueEvents configuration tid.val kind)[field.val]? := by
  cases kind <;> decide +revert

theorem initial_global_events :
    (initial.execution.events[0]?).map Event.action = some (.init .nMarking (.i32 0)) ∧
    (initial.execution.events[1]?).map Event.action = some (.init .initiator (.i32 (-1))) := by
  decide

theorem initial_pointer_allocation :
    (initial.arrays 1).headerLive = true ∧ (initial.arrays 1).power = 18 ∧
    (initial.arrays 1).contents.buffer = #[] ∧ (initial.buffers 1).live = true ∧
    (initial.buffers 1).bytes = pointerCapacity * 8 := by decide

theorem initial_noSlotEvents (event : Fin 47) :
    ((initial.execution.events[event.val]?).bind (fun event => event.action.location)).any
      (fun location => match location with | .slot _ _ => true | _ => false) = false := by
  have all : ∀ event : Fin 47,
      ((initial.execution.events[event.val]?).bind (fun event => event.action.location)).any
        (fun location => match location with | .slot _ _ => true | _ => false) = false := by
    decide
  exact all event

/-- The parent root occupies one queue index before its scanner starts.
`bbfa0ce4150`, `src/work-stealing-queue.h:54-69,75-92`. -/
theorem shiftedMaskedIndex_wrap :
    maskedIndex (Int64.ofNat (pointerCapacity + 1))
      (Int32.ofNat (pointerCapacity - 1)) = 1 := by decide

theorem noResizeThroughShiftedCapacity (bottom : Int64)
    (bounded : bottom.toInt ≤ pointerCapacity + 1) :
    ¬ (bottom.toInt - (2 : Int64).toInt >
      (Int32.ofNat pointerCapacity).toInt - 1) := by
  change ¬ (bottom.toInt - 2 > (262144 : Int) - 1)
  change bottom.toInt ≤ (262144 : Int) + 1 at bounded
  omega

def indexedRead64 (value : Int64) (source : Nat) : Choice :=
  { i64 := value, memory := { readFrom := some source } }

def indexedRead32 (value : Int32) (source : Nat) : Choice :=
  { i32 := value, memory := { readFrom := some source } }

def indexedReadAddress (value source : Nat) : Choice :=
  { address := value, memory := { readFrom := some source } }

/-- A complete non-resizing owner publication,
`bbfa0ce4150`, `src/gc-stock.c:1830-1840,2840`,
`src/work-stealing-queue.h:54-70`. -/
def pushBlock (value : Payload) (bottom top : Int64)
    (bottomSource topSource arraySource capacitySource maskSource bufferSource base : Nat) :
    List (Nat × Choice) :=
  [(0, { scannerPush := some (.pointer, value) }), (0, noChoice),
    (0, indexedRead64 bottom bottomSource), (0, indexedRead64 top topSource),
    (0, indexedReadAddress 1 arraySource), (0, noChoice),
    (0, indexedRead32 (Int32.ofNat pointerCapacity) capacitySource), (0, noChoice),
    (0, indexedRead32 (Int32.ofNat (pointerCapacity - 1)) maskSource),
    (0, indexedReadAddress 1 bufferSource), (0, noChoice), (0, noChoice),
    (0, { memory := { mo := base + 9 } }),
    (0, noChoice), (0, noChoice), (0, noChoice)]

def pushEvents (control : List Nat) (value : Payload) (bottom top : Int64)
    (bottomSource topSource arraySource capacitySource maskSource bufferSource base : Nat) :
    List (Event Location Value) :=
  let beforeDeps (deps : List Nat) := (control ++ (control ++ deps)).eraseDups
  let afterDeps (deps : List Nat) :=
    (control ++ ((control ++ [base + 3, base, base + 1]) ++ deps)).eraseDups
  [
    { thread := 0, action := .load (.bottom 0 .pointer) .relaxed (.i64 bottom),
      readFrom := some bottomSource, dependsOn := beforeDeps [] },
    { thread := 0, action := .load (.top 0 .pointer) .acquire (.i64 top),
      readFrom := some topSource, dependsOn := beforeDeps [] },
    { thread := 0, action := .load (.array 0 .pointer) .relaxed (.address 1),
      readFrom := some arraySource, dependsOn := beforeDeps [] },
    { thread := 0, action := .plainLoad (.capacity 1) (.i32 (Int32.ofNat pointerCapacity)),
      readFrom := some capacitySource, dependsOn := beforeDeps [base + 2] },
    { thread := 0, action := .plainLoad (.mask 1) (.i32 (Int32.ofNat (pointerCapacity - 1))),
      readFrom := some maskSource, dependsOn := afterDeps [base + 2] },
    { thread := 0, action := .plainLoad (.buffer 1) (.address 1),
      readFrom := some bufferSource, dependsOn := afterDeps [base + 2] },
    { thread := 0, action := .plainStore
        (.slot 1 (maskedIndex bottom (Int32.ofNat (pointerCapacity - 1))).toInt.toNat)
        (.payload value), dependsOn := afterDeps [base, base + 4, base + 5] },
    { thread := 0, action := .fence .release, dependsOn := afterDeps [] },
    { thread := 0, action := .store (.bottom 0 .pointer) .relaxed (.i64 (bottom + 1)),
      mo := base + 9, dependsOn := afterDeps [base] }]

theorem validPointerSlot (s : State) (index : Int64)
    (live : (s.buffers 1).live = true)
    (bytes : (s.buffers 1).bytes = pointerCapacity * 8) :
    validSlot configuration s .pointer 1
      (maskedIndex index (Int32.ofNat (pointerCapacity - 1))) = true := by
  have bound := (maskedAccessAndResizeBounds_proven.1 18 (by decide) index 8 (Or.inl rfl))
  simp only [validSlot, configuration, elementBytes, live, bytes,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · decide
      · exact ⟨by decide, by simpa [pointerCapacity] using bound⟩

end ActualCapacity

end JuliaLean.CRuntime.ParallelMark

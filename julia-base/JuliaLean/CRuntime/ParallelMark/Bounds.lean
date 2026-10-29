import JuliaLean.CRuntime.ParallelMark.Core

namespace JuliaLean.CRuntime.ParallelMark

open Memory

@[simp] theorem initialQueueId_div (tid : Nat) (kind : QueueKind) :
    initialQueueId tid kind / 2 = tid := by
  cases kind <;> simp [initialQueueId] <;> omega

@[simp] theorem initialQueueId_kind (tid : Nat) (kind : QueueKind) :
    (if initialQueueId tid kind % 2 = 0 then QueueKind.chunk else .pointer) = kind := by
  cases kind <;> simp [initialQueueId, Nat.add_mod]

@[simp] theorem canonicalInitial_fault (c : Config) : (canonicalInitial c).fault = false := rfl

@[simp] theorem canonicalInitial_barrier (c : Config) :
    (canonicalInitial c).barrierPassed = false := rfl

@[simp] theorem canonicalInitial_call (c : Config) (tid : Nat) :
    ((canonicalInitial c).threads tid).call = none := by
  unfold canonicalInitial
  dsimp
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem canonicalInitial_header (c : Config) (tid : Nat) (kind : QueueKind)
    (valid : tid < c.threads) (present : c.present tid = true) :
    ((canonicalInitial c).arrays (initialQueueId tid kind)).headerLive = true := by
  simp [canonicalInitial, valid, present]

theorem canonicalInitial_buffer (c : Config) (tid : Nat) (kind : QueueKind)
    (valid : tid < c.threads) (present : c.present tid = true) :
    ((canonicalInitial c).buffers (initialQueueId tid kind)).live = true ∧
      ((canonicalInitial c).buffers (initialQueueId tid kind)).bytes =
        2 ^ c.initialPower tid kind * elementBytes c kind := by
  simp [canonicalInitial, valid, present]

/-- Applies to both resize-copy indices, `bbfa0ce4150`,
`src/work-stealing-queue.h:58-67`. -/
theorem circularIndex_lt (power : Nat) (index : Int64) :
    circularIndex power index < 2 ^ power := by
  exact (index.toBitVec.extractLsb' 0 power).isLt

/-- One full circular-buffer period returns to slot zero, `bbfa0ce4150`,
`src/work-stealing-queue.h:61,67,81,101`. -/
theorem circularIndex_wrap (power : Nat) (hpower : power ≤ 64) :
    circularIndex power (Int64.ofNat (2^power)) = 0 := by
  unfold circularIndex
  rw [Int64.toBitVec_ofNat', ← BitVec.setWidth_eq_extractLsb' hpower,
    BitVec.setWidth_ofNat_of_le hpower]
  simp

/-- Signed mask wrap for positive Int32 power-of-two capacities,
`bbfa0ce4150`, `src/work-stealing-queue.h:24-35,67`. -/
theorem maskedIndex_wrap (power : Nat) (hpower : power ≤ 30) :
    maskedIndex (Int64.ofNat (2^power)) (Int32.ofNat (2^power - 1)) = 0 := by
  have all : ∀ p : Fin 31,
      maskedIndex (Int64.ofNat (2^p.val)) (Int32.ofNat (2^p.val - 1)) = 0 := by
    decide
  exact all ⟨power, by omega⟩

/-- Both actual GC initial capacities reuse slot zero after one period,
`bbfa0ce4150`, `src/gc-stock.h:94-95`, `src/work-stealing-queue.h:67`. -/
theorem gcInitialMaskedIndex_wrap :
    maskedIndex (Int64.ofNat (2^14)) (Int32.ofNat (2^14 - 1)) = 0 ∧
    maskedIndex (Int64.ofNat (2^18)) (Int32.ofNat (2^18 - 1)) = 0 :=
  ⟨maskedIndex_wrap 14 (by decide), maskedIndex_wrap 18 (by decide)⟩

/-- After top advances to one, owner pushes through bottom=capacity do
not resize, `bbfa0ce4150`, `src/work-stealing-queue.h:54-59`. -/
theorem noResizeThroughCapacity (bottom : Int64) (capacity : Int32)
    (hbottom : bottom.toInt ≤ capacity.toInt) :
    ¬ (bottom.toInt - (1 : Int64).toInt > capacity.toInt - 1) := by
  change ¬ (bottom.toInt - 1 > capacity.toInt - 1)
  omega

def circularCopyWithinBuffer : Prop :=
  ∀ power index elementBytes byte,
    byte < elementBytes →
    byteOffset power index elementBytes byte < 2 ^ power * elementBytes

theorem circularCopyWithinBuffer_proven : circularCopyWithinBuffer := by
  intro power index elementBytes byte hbyte
  have hindex := Nat.succ_le_of_lt (circularIndex_lt power index)
  calc
    byteOffset power index elementBytes byte <
        circularIndex power index * elementBytes + elementBytes :=
      Nat.add_lt_add_left hbyte _
    _ = (circularIndex power index + 1) * elementBytes := by simp [Nat.add_mul]
    _ ≤ 2 ^ power * elementBytes := Nat.mul_le_mul_right elementBytes hindex

/-- The promoted signed mask selects a nonnegative index below capacity.
`bbfa0ce4150`, `src/work-stealing-queue.h:24-35,61,67,81,101`. -/
theorem maskedIndex_bounds (power : Nat) (hpower : power ≤ 30) (index : Int64) :
    0 ≤ (maskedIndex index (Int32.ofNat (2^power - 1))).toInt ∧
      (maskedIndex index (Int32.ofNat (2^power - 1))).toInt < (2^power : Nat) := by
  have maskNat :
      (Int64.ofInt (Int32.ofNat (2^power - 1)).toInt).toBitVec.toNat = 2^power - 1 := by
    have all : ∀ p : Fin 31,
        (Int64.ofInt (Int32.ofNat (2^p.val - 1)).toInt).toBitVec.toNat =
          2^p.val - 1 := by decide
    exact all ⟨power, by omega⟩
  let bits := index.toBitVec &&&
    (Int64.ofInt (Int32.ofNat (2^power - 1)).toInt).toBitVec
  have small : bits.toNat < 2^power := by
    dsimp [bits]
    rw [maskNat]
    exact Nat.and_lt_two_pow _ (by have := Nat.two_pow_pos power; omega)
  have capacityBound : 2^power ≤ 2^30 := Nat.pow_le_pow_right (by decide) hpower
  have signed : bits.toInt = (bits.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  change 0 ≤ bits.toInt ∧ bits.toInt < (2^power : Nat)
  rw [signed]
  exact ⟨by omega, by omega⟩

/-- Both actual GC element sizes fit in the source's signed byte-offset
expression for every positive representable power-of-two capacity. Doubling
2^30 overflows the signed int32 expression before conversion to size_t.
`bbfa0ce4150`, `src/work-stealing-queue.h:30,58-61,67,81,101`,
`src/gc-stock.c:1836,1846,1854,1861,1871,1902`. -/
def maskedAccessAndResizeBounds : Prop :=
  (∀ (power : Nat), power ≤ 30 → ∀ (index : Int64) (bytes : Nat),
    (bytes = 8 ∨ bytes = 64) →
    let slot := (maskedIndex index (Int32.ofNat (2^power - 1))).toInt
    fits64 (slot * bytes) = true ∧ 0 ≤ slot * bytes ∧
      slot * bytes + bytes ≤ ((2^power * bytes : Nat) : Int)) ∧
  (∀ (power : Nat), power ≤ 30 →
    (fits32 (2 * (Int32.ofNat (2^power)).toInt) = true ↔ power < 30))

theorem maskedAccessAndResizeBounds_proven : maskedAccessAndResizeBounds := by
  constructor
  · intro power hpower index bytes hbytes
    have bounds := maskedIndex_bounds power hpower index
    have capacityBound : 2^power ≤ 2^30 := Nat.pow_le_pow_right (by decide) hpower
    rcases hbytes with rfl | rfl <;>
      simp only [fits64, decide_eq_true_eq, Int.natCast_mul] <;> omega
  · intro power hpower
    have all : ∀ p : Fin 31,
        (fits32 (2 * (Int32.ofNat (2^p.val)).toInt) = true ↔ p.val < 30) := by
      decide
    exact all ⟨power, by omega⟩

namespace DequeRefinement

/-- Initial C control fields and queue-call continuations cannot enter
reclamation before `gc_mark_loop_barrier`, `bbfa0ce4150`,
`src/gc-stock.c:2817-3004,4055-4063`. Invalid PCs still fault in `step`. -/
def roundPC (pc : Nat) : Prop :=
  pc < 3009 ∨ pc ∈ [3394, 3395, 3396, 3397, 3400, 3401, 3404, 3406,
    28631, 28801, 28901, 4021, 4024, 4026, 4029, 4031,
    4055, 4056, 4057, 4058, 4060, 4061, 4062, 4063,
    40211, 40261, 40311, 40581]

def threadInRound (thread : Thread) : Prop :=
  roundPC thread.pc ∧ roundPC thread.markReturnPC ∧
  roundPC thread.markLoopReturnPC ∧
  ∀ call, thread.call = some call → roundPC call.returnPC

def RoundControl (state : State) : Prop :=
  state.barrierPassed = false → ∀ thread, threadInRound (state.threads thread)

theorem canonicalInitial_control (c : Config) : RoundControl (canonicalInitial c) := by
  intro _ tid
  unfold canonicalInitial
  dsimp
  split
  · split
    · simp [threadInRound, roundPC]
    · split <;> simp [threadInRound, roundPC]
  · simp [threadInRound, roundPC]

private theorem queueStep_barrier (c : Config) (s : State)
    (tid : Nat) (q : QueueCall) (ch : Choice) :
    (queueStep c s tid q ch).barrierPassed = s.barrierPassed := by
  unfold queueStep
  dsimp
  split <;>
    simp_all [checked, emit, setCall, updateThread, updateArray, updateBuffer,
      queueControl, returnQueue]
  all_goals split <;> simp_all

set_option maxHeartbeats 2000000 in
private theorem queueStep_control (c : Config) (s : State)
    (tid : Nat) (q : QueueCall) (ch : Choice)
    (control : ∀ thread, threadInRound (s.threads thread))
    (continuation : roundPC q.returnPC) :
    ∀ thread, threadInRound ((queueStep c s tid q ch).threads thread) := by
  intro thread
  have current := control thread
  have selected := control tid
  by_cases same : thread = tid <;>
  unfold queueStep <;>
  dsimp <;>
  split <;>
    simp_all [threadInRound, checked, emit, setCall, updateThread, updateArray,
      updateBuffer, queueControl, returnQueue]
  all_goals split <;> simp_all

private theorem queueStep_live (c : Config) (s : State)
    (tid : Nat) (q : QueueCall) (ch : Choice) (array buffer : Nat)
    (header : (s.arrays array).headerLive = true)
    (bytes : (s.buffers buffer).live = true) :
    ((queueStep c s tid q ch).arrays array).headerLive = true ∧
    ((queueStep c s tid q ch).buffers buffer).live = true := by
  unfold queueStep
  dsimp
  split <;>
    simp_all [checked, emit, setCall, updateThread, updateArray, updateBuffer,
      queueControl, returnQueue]
  all_goals split <;> simp_all

private theorem countStep_control (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (control : ∀ thread, threadInRound (s.threads thread)) :
    ∀ thread, threadInRound ((countStep c s tid ch).threads thread) := by
  intro thread
  have current := control thread
  have selected := control tid
  by_cases same : thread = tid <;>
  unfold countStep <;>
  dsimp <;>
  split <;> simp_all [threadInRound, checked, emit, updateThread]

theorem countStep_live (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (array buffer : Nat) :
    ((countStep c s tid ch).arrays array).headerLive = (s.arrays array).headerLive ∧
    ((countStep c s tid ch).buffers buffer).live = (s.buffers buffer).live ∧
    (countStep c s tid ch).barrierPassed = s.barrierPassed := by
  unfold countStep
  dsimp
  split <;> simp_all [checked, emit, updateThread]

set_option maxHeartbeats 2000000 in
private theorem markStep_barrier (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (passed : s.barrierPassed = true) : (markStep c s tid ch).barrierPassed = true := by
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact (countStep_live c s tid ch 0 0).2.2.trans passed
    | (simp_all [checked, emit, advance, beginQueue, setCall, threadControl,
        updateThread, updateArray, updateBuffer] <;> done)
    | split)

private theorem markStep_barrier_entry (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (pc : (s.threads tid).pc = 3003) :
    (markStep c s tid ch).barrierPassed = true := by
  simp [markStep, pc, emit, advance, updateThread]

private theorem markStep_broadcast_control (c : Config) (s : State)
    (tid : Nat) (ch : Choice)
    (control : ∀ thread, threadInRound (s.threads thread))
    (pc : (s.threads tid).pc = 2977) :
    ∀ thread, threadInRound ((markStep c s tid ch).threads thread) := by
  intro thread
  by_cases same : thread = tid
  · subst thread
    rcases control tid with ⟨currentPC, currentMark, currentLoop, currentCall⟩
    cases waiting : (s.threads tid).waiting <;>
      simp_all [markStep, checked, advance, updateThread, threadInRound, roundPC]
  · rcases control thread with ⟨currentPC, currentMark, currentLoop, currentCall⟩
    cases waiting : (s.threads thread).waiting <;>
      simp_all [markStep, checked, advance, updateThread, threadInRound, roundPC]

set_option maxHeartbeats 20000000 in
private theorem markStep_control_self (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (control : ∀ thread, threadInRound (s.threads thread))
    (before : s.barrierPassed = false)
    (after : (markStep c s tid ch).barrierPassed = false) :
    threadInRound ((markStep c s tid ch).threads tid) := by
  by_cases barrierPC : (s.threads tid).pc = 3003
  · have entered := markStep_barrier_entry c s tid ch barrierPC
    rw [after] at entered
    contradiction
  by_cases broadcastPC : (s.threads tid).pc = 2977
  · exact markStep_broadcast_control c s tid ch control broadcastPC tid
  rcases control tid with ⟨pcSafe, markSafe, loopSafe, callSafe⟩
  unfold threadInRound
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_control c s tid ch control tid
    | (simp_all [roundPC, checked, emit, advance,
        beginQueue, setCall, threadControl, updateThread]
        <;> done)
    | split)

set_option maxHeartbeats 20000000 in
private theorem markStep_control_other (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (control : ∀ thread, threadInRound (s.threads thread))
    (before : s.barrierPassed = false)
    (after : (markStep c s tid ch).barrierPassed = false)
    (thread : Nat) (different : thread ≠ tid) :
    threadInRound ((markStep c s tid ch).threads thread) := by
  by_cases barrierPC : (s.threads tid).pc = 3003
  · have entered := markStep_barrier_entry c s tid ch barrierPC
    rw [after] at entered
    contradiction
  by_cases broadcastPC : (s.threads tid).pc = 2977
  · exact markStep_broadcast_control c s tid ch control broadcastPC thread
  rcases control thread with ⟨currentPC, currentMark, currentLoop, currentCall⟩
  have selectedPC := (control tid).1
  unfold threadInRound
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_control c s tid ch control thread
    | (simp_all [roundPC, checked, emit, advance,
        beginQueue, setCall, threadControl, updateThread]
        <;> done)
    | split)

private theorem markStep_control (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (control : ∀ thread, threadInRound (s.threads thread))
    (before : s.barrierPassed = false)
    (after : (markStep c s tid ch).barrierPassed = false) :
    ∀ thread, threadInRound ((markStep c s tid ch).threads thread) := by
  intro thread
  by_cases same : thread = tid
  · subst thread
    exact markStep_control_self c s tid ch control before after
  · exact markStep_control_other c s tid ch control before after thread same

set_option maxHeartbeats 20000000 in
private theorem markStep_live (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (control : ∀ thread, threadInRound (s.threads thread))
    (before : s.barrierPassed = false)
    (_after : (markStep c s tid ch).barrierPassed = false)
    (array buffer : Nat) (header : (s.arrays array).headerLive = true)
    (bytes : (s.buffers buffer).live = true) :
    ((markStep c s tid ch).arrays array).headerLive = true ∧
    ((markStep c s tid ch).buffers buffer).live = true := by
  have selectedPC := (control tid).1
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact ⟨(countStep_live c s tid ch array buffer).1.trans header,
        (countStep_live c s tid ch array buffer).2.1.trans bytes⟩
    | (simp_all [roundPC, checked, emit, advance,
        beginQueue, setCall, threadControl, updateThread]
        <;> done)
    | split)

theorem step_barrier (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (passed : s.barrierPassed = true) : (step c tid ch s).barrierPassed = true := by
  cases fault : s.fault with
  | true => simp [step, fault, passed]
  | false =>
    by_cases valid : tid < c.threads
    · cases call : (s.threads tid).call with
      | none => simpa [step, fault, valid, call] using markStep_barrier c s tid ch passed
      | some q =>
        by_cases owner : q.operation ≠ .steal ∧ q.owner ≠ tid
        · simp [step, fault, valid, call, owner, passed]
        · simpa [step, fault, valid, call, owner, queueStep_barrier] using passed
    · simp [step, fault, valid, passed]

theorem step_control (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (control : RoundControl s) : RoundControl (step c tid ch s) := by
  intro after
  have before : s.barrierPassed = false := by
    cases hb : s.barrierPassed with
    | false => rfl
    | true => have h := step_barrier c s tid ch hb; simp [after] at h
  have initial := control before
  cases fault : s.fault with
  | true => simpa [step, fault] using initial
  | false =>
    by_cases valid : tid < c.threads
    · cases call : (s.threads tid).call with
      | none =>
        have markAfter : (markStep c s tid ch).barrierPassed = false := by
          simpa [step, fault, valid, call] using after
        simpa [step, fault, valid, call] using
          markStep_control c s tid ch initial before markAfter
      | some q =>
        by_cases owner : q.operation ≠ .steal ∧ q.owner ≠ tid
        · simpa [step, fault, valid, call, owner] using initial
        · have continuation : roundPC q.returnPC := (initial tid).2.2.2 q call
          simpa [step, fault, valid, call, owner] using
            queueStep_control c s tid q ch initial continuation
    · simpa [step, fault, valid] using initial

private theorem step_live (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (control : RoundControl s) (after : (step c tid ch s).barrierPassed = false)
    (array buffer : Nat) (header : (s.arrays array).headerLive = true)
    (bytes : (s.buffers buffer).live = true) :
    ((step c tid ch s).arrays array).headerLive = true ∧
    ((step c tid ch s).buffers buffer).live = true := by
  have before : s.barrierPassed = false := by
    cases hb : s.barrierPassed with
    | false => rfl
    | true => have h := step_barrier c s tid ch hb; simp [after] at h
  have initial := control before
  cases fault : s.fault with
  | true => simpa [step, fault] using And.intro header bytes
  | false =>
    by_cases valid : tid < c.threads
    · cases call : (s.threads tid).call with
      | none =>
        have markAfter : (markStep c s tid ch).barrierPassed = false := by
          simpa [step, fault, valid, call] using after
        simpa [step, fault, valid, call] using
          markStep_live c s tid ch initial before markAfter array buffer header bytes
      | some q =>
        by_cases owner : q.operation ≠ .steal ∧ q.owner ≠ tid
        · simpa [step, fault, valid, call, owner] using And.intro header bytes
        · simpa [step, fault, valid, call, owner] using
            queueStep_live c s tid q ch array buffer header bytes
    · simpa [step, fault, valid] using And.intro header bytes

theorem run_barrier (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (passed : s.barrierPassed = true) : (run c schedule s).barrierPassed = true := by
  induction schedule generalizing s with
  | nil => exact passed
  | cons scheduled rest ih => exact ih _ (step_barrier c s scheduled.1 scheduled.2 passed)

private theorem run_control (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (control : RoundControl s) : RoundControl (run c schedule s) := by
  induction schedule generalizing s with
  | nil => exact control
  | cons scheduled rest ih => exact ih _ (step_control c s scheduled.1 scheduled.2 control)

/-- Live array headers and separately allocated buffers remain live until
the source mark barrier, including arrays in either queue's `reclaim_set`.
`bbfa0ce4150`, `src/work-stealing-queue.h:30-36,64`,
`src/gc-stock.c:1838-1839,1863-1864,3000-3018`. -/
private def retiredArraysRemainLive : Prop :=
  ∀ (c : Config) (schedule : List (Nat × Choice)) (s : State),
    RoundControl s → (run c schedule s).barrierPassed = false →
    ∀ array buffer, (s.arrays array).headerLive = true → (s.buffers buffer).live = true →
      ((run c schedule s).arrays array).headerLive = true ∧
      ((run c schedule s).buffers buffer).live = true

private theorem retiredArraysRemainLive_proven : retiredArraysRemainLive := by
  intro c schedule
  induction schedule with
  | nil => intro s _ _ array buffer header bytes; exact ⟨header, bytes⟩
  | cons scheduled rest ih =>
    intro s control after array buffer header bytes
    have first : (step c scheduled.1 scheduled.2 s).barrierPassed = false := by
      cases hb : (step c scheduled.1 scheduled.2 s).barrierPassed with
      | false => rfl
      | true =>
        have h := run_barrier c rest (step c scheduled.1 scheduled.2 s) hb
        change (run c rest (step c scheduled.1 scheduled.2 s)).barrierPassed = false at after
        simp [after] at h
    have live := step_live c s scheduled.1 scheduled.2 control first array buffer header bytes
    exact ih _ (step_control c s scheduled.1 scheduled.2 control) after array buffer live.1 live.2

/-- Every array header and buffer live at a canonical source prefix stays
live throughout a suffix ending before the mark barrier.
`bbfa0ce4150`, `src/gc-stock.c:1838-1839,1863-1864,3000-3018`. -/
def sourceRetiredArraysRemainLive : Prop :=
  ∀ (c : Config) (front suffix : List (Nat × Choice)),
    let before := run c front (canonicalInitial c)
    let after := run c suffix before
    after.barrierPassed = false →
    ∀ array buffer, (before.arrays array).headerLive = true →
      (before.buffers buffer).live = true →
      (after.arrays array).headerLive = true ∧ (after.buffers buffer).live = true

theorem sourceRetiredArraysRemainLive_proven : sourceRetiredArraysRemainLive := by
  intro c front suffix before after barrier array buffer header live
  exact retiredArraysRemainLive_proven c suffix (run c front (canonicalInitial c))
    (run_control c front (canonicalInitial c) (canonicalInitial_control c))
    barrier array buffer header live

end DequeRefinement

end JuliaLean.CRuntime.ParallelMark

import JuliaLean.Channels.Props

namespace JuliaLean.Channels

/-- Program-counter lookup, including absence of the task. -/
def pcOf (s : St) (i : Nat) : Option Pc := s.tasks[i]?.map Task.pc

/-- A condition continuation belongs to its operation and channel size. -/
def ParkFits (sz : Nat) (op : Op) : Park → Prop
  | .putBuf v => op = .put v ∧ 0 < sz
  | .putUnb v => op = .put v ∧ sz = 0
  | .take false => op = .take ∧ 0 < sz
  | .take true => op = .iter ∧ 0 < sz
  | .takeUnb false => op = .take ∧ sz = 0
  | .takeUnb true => op = .iter ∧ sz = 0
  | .fetch => op = .fetch ∧ 0 < sz
  | .wait => op = .wait

/-- Every continuation belongs to the task's fixed operation. -/
def PcFits (sz : Nat) (op : Op) : Pc → Prop
  | .start | .done _ => True
  | .putLocked v => op = .put v
  | .takeLocked it => op = .iter ∧ it = true
  | .waitLocked => op = .wait
  | .parked k | .woken k _ => ParkFits sz op k
  | .handoff v _ => op = .put v ∧ sz = 0

/-- The operation list and capacity are fixed, and continuations fit operations.
The owner proves `fitInv_init : FitInv sz ops (init sz ops)` and
`fitInv_step : FitInv sz ops s → stepTask s i = some s' → FitInv sz ops s'`. -/
structure FitInv (sz : Nat) (ops : List Op) (s : St) : Prop where
  capacity : s.ch.sz = sz
  operations : s.tasks.map Task.op = ops
  fits : ∀ t ∈ s.tasks, PcFits sz t.op t.pc

/-- A pending put contributes one to `nAvail` until it commits or fails. -/
def pendingPut (t : Task) : Bool :=
  match t.pc with
  | .parked (.putBuf _) | .parked (.putUnb _)
  | .woken (.putBuf _) _ | .woken (.putUnb _) _ => true
  | _ => false

/-- Only unbuffered takers receive a value directly from the scheduler. -/
def WakeFits (k : Park) (w : Wake) : Prop :=
  match k, w with
  | .takeUnb _, .val _ | .takeUnb _, .err _ => True
  | .takeUnb _, .none => False
  | _, .none | _, .err _ => True
  | _, .val _ => False

/-- Members of the take condition are parked in its corresponding wait. -/
def TakeQueueKind (sz : Nat) (pc : Pc) : Prop :=
  if sz = 0 then ∃ it, pc = .parked (.takeUnb it)
  else (∃ it, pc = .parked (.take it)) ∨ pc = .parked .fetch ∨ pc = .parked .wait

/-- Members of the put condition are parked in its corresponding wait. -/
def PutQueueKind (sz : Nat) (pc : Pc) : Prop :=
  if sz = 0 then ∃ v, pc = .parked (.putUnb v)
  else ∃ v, pc = .parked (.putBuf v)

/-- Queue, availability, handoff, and wake-value invariants.
The owner proves `queueInv_init : QueueInv sz (init sz ops)` and
`queueInv_step : QueueInv sz s → FitInv sz ops s → stepTask s i = some s' → QueueInv sz s'`.
All fields concern the state before a step; neither lemma assumes reachability. -/
structure QueueInv (sz : Nat) (s : St) : Prop where
  closedQueues : s.ch.isOpen = false → s.ch.qTake = [] ∧ s.ch.qPut = [] ∧ s.ch.qWait = []
  availability : s.ch.nAvail = (s.ch.data.length : Int) + (s.tasks.countP pendingPut : Int)
  buffer : s.ch.data.length ≤ sz
  takeKinds : ∀ i ∈ s.ch.qTake, ∃ pc, pcOf s i = some pc ∧ TakeQueueKind sz pc
  putKinds : ∀ i ∈ s.ch.qPut, ∃ pc, pcOf s i = some pc ∧ PutQueueKind sz pc
  waitKinds : ∀ i ∈ s.ch.qWait, sz = 0 ∧ pcOf s i = some (.parked .wait)
  takeNodup : s.ch.qTake.Nodup
  putNodup : s.ch.qPut.Nodup
  waitNodup : s.ch.qWait.Nodup
  handoff : ∀ i v t, pcOf s i = some (.handoff v t) →
    (∃ it, pcOf s t = some (.parked (.takeUnb it))) ∧
    t ∉ s.ch.qTake ∧ t ∉ s.ch.qPut ∧ t ∉ s.ch.qWait ∧
    ∀ j v', pcOf s j = some (.handoff v' t) → j = i
  parkedCovered : ∀ i k, pcOf s i = some (.parked k) →
    i ∈ s.ch.qTake ∨ i ∈ s.ch.qPut ∨ i ∈ s.ch.qWait ∨
    ∃ j v, pcOf s j = some (.handoff v i)
  bufferedTake : 0 < sz → s.ch.qTake ≠ [] → s.ch.data = []
  bufferedPut : 0 < sz → s.ch.qPut ≠ [] → sz ≤ s.ch.data.length + wokenPutBuf s
  unbufferedPut : sz = 0 → s.ch.qPut ≠ [] → s.ch.qTake.length ≤ wokenPutUnb s
  unbufferedWait : sz = 0 → s.ch.qWait ≠ [] → s.ch.nAvail = 0
  wakeValues : ∀ i k w, pcOf s i = some (.woken k w) → WakeFits k w
  wakeError : ∀ i k e, pcOf s i = some (.woken k (.err e)) → s.ch.isOpen = false
  takeErrorEmpty : ∀ i it e, pcOf s i = some (.woken (.take it) (.err e)) → s.ch.data = []

/-- Per-task contribution to the conservation ledger for value `x`. -/
def ledgerCredit (x : Val) (t : Task) : Int :=
  (match t.op, t.pc with
    | .put v, .done (.ok _) => if v = x then 1 else 0
    | _, _ => 0) -
  (match t.op, t.pc with
    | .take, .done (.ok (some v)) | .iter, .done (.ok (some v)) => if v = x then 1 else 0
    | _, .woken (.takeUnb _) (.val v) => if v = x then 1 else 0
    | _, _ => 0)

/-- The value ledger balances completed puts against received and stored items.
The owner proves `ledgerInv_init : LedgerInv (init sz ops)` and
`ledgerInv_step : LedgerInv s → FitInv sz ops s → QueueInv sz s →
  stepTask s i = some s' → LedgerInv s'`, and
`ledgerInv_conservation : LedgerInv s → List.Perm (putsDone s)
  (received s ++ s.ch.data ++ s.dropped)`. -/
def LedgerInv (s : St) : Prop :=
  ∀ x, (s.tasks.map (ledgerCredit x)).sum =
    (s.ch.data.count x : Int) + (s.dropped.count x : Int)

/-- One inductive invariant, split into independently preserved conjuncts. -/
structure Inv (sz : Nat) (ops : List Op) (s : St) : Prop where
  fit : FitInv sz ops s
  queues : QueueInv sz s
  ledger : LedgerInv s

end JuliaLean.Channels

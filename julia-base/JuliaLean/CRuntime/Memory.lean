import Std

/-!
Finite C11 candidate executions for Julia master
`bbfa0ce4150ea33f2532198cabcf319a49399360`.

`src/julia_atomics.h:93-98,105-195,199-259` supplies the operations below.
The C11 `jl_fence` branch at `src/julia_atomics.h:95` is modeled; equivalence
of the x86 inline assembly at `src/julia_atomics.h:90-93` is outside this model.
Their semantics follows ISO C11 draft N1570, 5.1.2.4 and 7.17.3-4:
https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf.

An execution supplies per-location modification ranks, read-from event IDs,
and a separate total order of sequentially consistent operations. Array order
supplies sequencing within each thread, never an order between threads.
Read-from can point forward in the array. Thus the scheduler does not silently
strengthen relaxed atomics to loads of already executed writes. `Step` emits
all choices; `Candidate.consistent` checks the completed finite execution.

Included: strong CAS (including its failure order), RMW atomicity, C11 release
sequences, release/acquire and fence synchronization, all four coherence
conditions, C11's SC-load and SC-fence rules, mutex synchronization, and a
separate ordinary-access race check. Visibility uses happens-before and the
modification history.

Clients must record the actual data dependencies in `Event.dependsOn` and must
check the arithmetic and branch that produced each action. Acyclic evaluation
justification rejects circular read-from/data-dependency explanations. The
model does not provide C expression evaluation, byte addressing, allocation,
pointer alias analysis, mixed-size overlapping accesses, consume dependencies,
TSAN's consume substitution, signal delivery, OS page protection, or progress
and fairness. Signal fences impose sequencing within the issuing thread and
provide no inter-thread synchronization. Signal-handler effects require a
separate client protocol. IDs and values are parameters; no heap cardinality
or machine-integer width is fixed by this module.

`init` represents initialization before the concurrent execution. Atomic
locations require such an initialization. A newly allocated ordinary field
instead begins with its first sequenced `plainStore`; `OrdinaryVisible`
requires every ordinary load to read a write that happens before it, with no
intervening write. Allocation identity, freshness and object lifetime remain
client checks.
-/

namespace JuliaLean.CRuntime.Memory

private instance finiteForall (n : Nat) (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∀ i, p i) :=
  decidable_of_iff (∀ i ∈ List.finRange n, p i) (by simp)

private instance finiteExists (n : Nat) (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∃ i, p i) :=
  decidable_of_iff (∃ i ∈ List.finRange n, p i) (by simp)

/-- C11 labels used by `src/julia_atomics.h:93-98,115-195,199-259`
at `bbfa0ce4150`. Consume is used only by the excluded TSAN substitution. -/
inductive Order where
  | relaxed | acquire | release | acqRel | seqCst
  deriving DecidableEq, Repr, Inhabited

inductive AccessClass where
  | atomic | ordinary
  deriving DecidableEq, Repr

def Order.hasAcquire : Order → Bool
  | .acquire | .acqRel | .seqCst => true
  | _ => false

def Order.hasRelease : Order → Bool
  | .release | .acqRel | .seqCst => true
  | _ => false

/-- Operation shapes of `src/julia_atomics.h:93-98,105-195,199-259`
at `bbfa0ce4150`. `rmw` records the old and computed new values. Strong CAS
succeeds exactly when observed=expected. Ordinary accesses and mutex calls
are needed for the GC's published buffers and observer mutex. -/
inductive Action (Loc Val : Type) where
  | init (loc : Loc) (value : Val)
  | load (loc : Loc) (order : Order) (observed : Val)
  | store (loc : Loc) (order : Order) (value : Val)
  | rmw (loc : Loc) (order : Order) (before after : Val)
  | cas (loc : Loc) (successOrder failureOrder : Order)
      (expected desired observed : Val)
  | fence (order : Order)
  | signalFence (order : Order)
  | plainLoad (loc : Loc) (observed : Val)
  | plainStore (loc : Loc) (value : Val)
  | lock (mutex : Nat)
  | unlock (mutex : Nat)
  deriving DecidableEq, Repr

namespace Action

def location : Action Loc Val → Option Loc
  | .init l _ | .load l _ _ | .store l _ _ | .rmw l _ _ _
  | .cas l _ _ _ _ _ | .plainLoad l _ | .plainStore l _ => some l
  | _ => none

def readValue : Action Loc Val → Option Val
  | .load _ _ v | .rmw _ _ v _ | .cas _ _ _ _ _ v | .plainLoad _ v => some v
  | _ => none

def writeValue [DecidableEq Val] : Action Loc Val → Option Val
  | .init _ v | .store _ _ v | .rmw _ _ _ v | .plainStore _ v => some v
  | .cas _ _ _ expected desired observed =>
      if observed = expected then some desired else none
  | _ => none

def order [DecidableEq Val] : Action Loc Val → Order
  | .load _ o _ | .store _ o _ | .rmw _ o _ _ | .fence o | .signalFence o => o
  | .cas _ success failure expected _ observed =>
      if observed = expected then success else failure
  | _ => .relaxed

def isInit : Action Loc Val → Bool
  | .init .. => true
  | _ => false

def isPlain : Action Loc Val → Bool
  | .plainLoad .. | .plainStore .. => true
  | _ => false

def accessClass : Action Loc Val → Option AccessClass
  | .load .. | .store .. | .rmw .. | .cas .. => some .atomic
  | .plainLoad .. | .plainStore .. => some .ordinary
  | _ => none

def isRMW [DecidableEq Val] : Action Loc Val → Bool
  | .rmw .. => true
  | .cas _ _ _ expected _ observed => decide (observed = expected)
  | _ => false

def isFence : Action Loc Val → Bool
  | .fence _ => true
  | _ => false

def isSC [DecidableEq Val] (a : Action Loc Val) : Bool :=
  match a with
  | .load .. | .store .. | .rmw .. | .cas .. | .fence .. => a.order == .seqCst
  | _ => false

def isAcquire [DecidableEq Val] (a : Action Loc Val) : Bool :=
  a.readValue.isSome && !a.isPlain && a.order.hasAcquire

def isRelease [DecidableEq Val] (a : Action Loc Val) : Bool :=
  a.writeValue.isSome && !a.isPlain && a.order.hasRelease

/-- Valid C11 operation orders, including the distinct failure order in
`jl_atomic_cmpswap_acqrel/release`, `src/julia_atomics.h:172-182,211-218`
at `bbfa0ce4150`. -/
def validOrders : Action Loc Val → Bool
  | .load _ o _ => o == .relaxed || o == .acquire || o == .seqCst
  | .store _ o _ => o == .relaxed || o == .release || o == .seqCst
  | .cas _ success failure _ _ _ =>
      failure == .relaxed ||
      (failure == .acquire && success.hasAcquire) ||
      (failure == .seqCst && success == .seqCst)
  | _ => true

end Action

/-- Explicit memory choices. Modification ranks are local to each location;
SC ranks order only SC operations, `src/julia_atomics.h:105-259`
at `bbfa0ce4150`. -/
structure Choice where
  readFrom : Option Nat := none
  mo : Nat := 0
  sc : Nat := 0
  deriving DecidableEq, Repr

/-- An occurrence of an operation in `src/julia_atomics.h:93-259`
at `bbfa0ce4150`. `dependsOn` records event IDs used to compute this action's
written value, address, or controlling branch. Initializations precede the concurrent execution. -/
structure Event (Loc Val : Type) where
  thread : Nat
  action : Action Loc Val
  readFrom : Option Nat := none
  mo : Nat := 0
  sc : Nat := 0
  dependsOn : List Nat := []
  deriving DecidableEq, Repr

def Event.emit (thread : Nat) (action : Action Loc Val) (choice : Choice) : Event Loc Val :=
  { thread, action, readFrom := choice.readFrom, mo := choice.mo, sc := choice.sc }

/-- Finite execution witness for the atomics of `src/julia_atomics.h:93-259`
at `bbfa0ce4150`. A caller can use `Fin n` for either ID parameter. -/
structure Candidate (Loc Val : Type) where
  events : Array (Event Loc Val)
  deriving Repr

namespace Candidate

abbrev Id (c : Candidate Loc Val) := Fin c.events.size

def event (c : Candidate Loc Val) (i : c.Id) : Event Loc Val := c.events[i]

def ids (c : Candidate Loc Val) : List c.Id := List.finRange c.events.size

def append (c : Candidate Loc Val) (e : Event Loc Val) : Candidate Loc Val :=
  ⟨c.events.push e⟩

variable [DecidableEq Loc] [DecidableEq Val]

def sameLocation (c : Candidate Loc Val) (a b : c.Id) : Bool :=
  (c.event a).action.location.isSome &&
    (c.event a).action.location == (c.event b).action.location

def isWrite (c : Candidate Loc Val) (a : c.Id) : Bool :=
  (c.event a).action.writeValue.isSome

def isRead (c : Candidate Loc Val) (a : c.Id) : Bool :=
  (c.event a).action.readValue.isSome

def isAtomicWrite (c : Candidate Loc Val) (a : c.Id) : Bool :=
  c.isWrite a && !(c.event a).action.isPlain

def isAtomicRead (c : Candidate Loc Val) (a : c.Id) : Bool :=
  c.isRead a && !(c.event a).action.isPlain

def readSource (c : Candidate Loc Val) (read write : c.Id) : Bool :=
  (c.event read).readFrom == some write.val

/-- The per-location modification history represented by arbitrary distinct
ranks. `src/julia_atomics.h:105-259`, `bbfa0ce4150`; C11 5.1.2.4p7. -/
def history (c : Candidate Loc Val) (loc : Loc) : List c.Id :=
  (c.ids.filter fun i => c.isAtomicWrite i && (c.event i).action.location == some loc).mergeSort
    (fun a b => (c.event a).mo ≤ (c.event b).mo)

def modificationBefore (c : Candidate Loc Val) (a b : c.Id) : Bool :=
  c.isAtomicWrite a && c.isAtomicWrite b && c.sameLocation a b &&
    decide ((c.event a).mo < (c.event b).mo)

def sequencedBefore (c : Candidate Loc Val) (a b : c.Id) : Bool :=
  !(c.event a).action.isInit && !(c.event b).action.isInit &&
    (c.event a).thread == (c.event b).thread && decide (a.val < b.val)

/-- C11 release sequence, including same-thread relaxed stores and RMWs by
other threads. Used by `src/work-stealing-queue.h:63-69,96-102` and
`src/gc-stock.h:179-225`, `bbfa0ce4150`; C11 5.1.2.4p10. -/
def releaseSequence (c : Candidate Loc Val) (head last : c.Id) : Bool :=
  c.isAtomicWrite head && c.isAtomicWrite last && c.sameLocation head last &&
  decide ((c.event head).mo ≤ (c.event last).mo) &&
  c.ids.all (fun i =>
    !(c.isAtomicWrite i && c.sameLocation head i &&
      decide ((c.event head).mo < (c.event i).mo ∧ (c.event i).mo ≤ (c.event last).mo)) ||
    ((c.event i).thread == (c.event head).thread || (c.event i).action.isRMW))

def readsSequence (c : Candidate Loc Val) (head read : c.Id) : Bool :=
  c.isRead read && !(c.event read).action.isPlain &&
    c.ids.any (fun source => c.readSource read source && c.releaseSequence head source)

def releaseEndpoint (c : Candidate Loc Val) (a head : c.Id) : Bool :=
  (a == head && (c.event a).action.isRelease) ||
  ((c.event a).action.isFence && (c.event a).action.order.hasRelease &&
    c.sequencedBefore a head)

def acquireEndpoint (c : Candidate Loc Val) (read b : c.Id) : Bool :=
  (read == b && (c.event b).action.isAcquire) ||
  ((c.event b).action.isFence && (c.event b).action.order.hasAcquire &&
    c.sequencedBefore read b)

/-- Release/acquire, all three fence synchronization forms, and mutex
unlock/acquire. Source wrappers: `src/julia_atomics.h:93-98,115-195`,
`bbfa0ce4150`; C11 5.1.2.4p11, 7.17.4p2-4. -/
def synchronizesWith (c : Candidate Loc Val) (a b : c.Id) : Bool :=
  (c.ids.any fun head => c.releaseEndpoint a head &&
    c.ids.any (fun read => c.readsSequence head read && c.acquireEndpoint read b)) ||
  (match (c.event a).action, (c.event b).action with
   | .unlock m, .lock n => m == n && decide (a.val < b.val)
   | _, _ => false)

def hbEdge (c : Candidate Loc Val) (a b : c.Id) : Bool :=
  c.sequencedBefore a b || c.synchronizesWith a b ||
    ((c.event a).action.isInit && !(c.event b).action.isInit)

/-- Executable finite transitive closure. The list contains the permitted
intermediate vertices, so all paths are checked without a guessed fuel bound. -/
def closure {n : Nat} (edge : Fin n → Fin n → Bool)
    (vertices : List (Fin n)) (a b : Fin n) : Bool :=
  let initial : Array (Array Bool) := Array.ofFn fun i : Fin n =>
    Array.ofFn fun j : Fin n => edge i j
  let matrix := vertices.foldl (fun matrix k =>
    matrix.mapIdx fun i row => row.mapIdx fun j value =>
      value || (matrix[i]![k.val]! && matrix[k.val]![j]!)) initial
  matrix[a.val]![b.val]!

private def closeAt {n : Nat} (edge : Fin n → Fin n → Bool)
    (k : Fin n) (a b : Fin n) : Bool :=
  edge a b || (edge a k && edge k b)

private def referenceClosure {n : Nat} (edge : Fin n → Fin n → Bool) :
    List (Fin n) → Fin n → Fin n → Bool
  | [], a, b => edge a b
  | k :: ks, a, b => closeAt (referenceClosure edge ks) k a b

private def relationTable {n : Nat} (edge : Fin n → Fin n → Bool) : Array (Array Bool) :=
  Array.ofFn fun i : Fin n => Array.ofFn fun j : Fin n => edge i j

private def advanceTable {n : Nat} (table : Array (Array Bool)) (k : Fin n) :
    Array (Array Bool) :=
  table.mapIdx fun i row => row.mapIdx fun j value =>
    value || (table[i]![k.val]! && table[k.val]![j]!)

private theorem relationTable_lookup {n : Nat} (edge : Fin n → Fin n → Bool)
    (a b : Fin n) : (relationTable edge)[a.val]![b.val]! = edge a b := by
  simp [relationTable, a.isLt, b.isLt]

private theorem advanceTable_relationTable {n : Nat} (edge : Fin n → Fin n → Bool)
    (k : Fin n) : advanceTable (relationTable edge) k = relationTable (closeAt edge k) := by
  apply Array.ext (by simp [advanceTable, relationTable])
  intro i hi hi'
  have hiN : i < n := by simpa [advanceTable, relationTable] using hi
  simp only [advanceTable, Array.getElem_mapIdx, relationTable, Array.getElem_ofFn]
  apply Array.ext (by simp)
  intro j hj hj'
  have hjN : j < n := by simpa using hj'
  simp [closeAt, hiN, hjN, k.isLt]

private theorem referenceClosure_append_singleton {n : Nat}
    (edge : Fin n → Fin n → Bool) (vertices : List (Fin n)) (k : Fin n) :
    referenceClosure edge (vertices ++ [k]) = referenceClosure (closeAt edge k) vertices := by
  induction vertices with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.cons_append, referenceClosure]
    rw [ih]

private theorem fold_advanceTable {n : Nat} (edge : Fin n → Fin n → Bool)
    (vertices : List (Fin n)) :
    vertices.foldl advanceTable (relationTable edge) =
      relationTable (referenceClosure edge vertices.reverse) := by
  induction vertices generalizing edge with
  | nil => rfl
  | cons k ks ih =>
    rw [List.foldl_cons, advanceTable_relationTable, ih, List.reverse_cons,
      referenceClosure_append_singleton]

private theorem closure_eq_reference {n : Nat} (edge : Fin n → Fin n → Bool)
    (vertices : List (Fin n)) (a b : Fin n) :
    closure edge vertices a b = referenceClosure edge vertices.reverse a b := by
  change (vertices.foldl advanceTable (relationTable edge))[a.val]![b.val]! = _
  rw [fold_advanceTable, relationTable_lookup]

private theorem referenceClosure_of_edge {n : Nat} {edge : Fin n → Fin n → Bool}
    {a b : Fin n} (h : edge a b = true) (vertices : List (Fin n)) :
    referenceClosure edge vertices a b = true := by
  induction vertices with
  | nil => exact h
  | cons k ks ih =>
    exact Bool.or_eq_true_iff.mpr (Or.inl ih)

private theorem referenceClosure_induction {n : Nat} {edge : Fin n → Fin n → Bool}
    (R : Fin n → Fin n → Prop)
    (edgeCase : ∀ a b, edge a b = true → R a b)
    (transCase : ∀ a b d, R a b → R b d → R a d)
    (vertices : List (Fin n)) {a b : Fin n}
    (h : referenceClosure edge vertices a b = true) : R a b := by
  induction vertices generalizing a b with
  | nil => exact edgeCase a b h
  | cons k ks ih =>
    rcases Bool.or_eq_true_iff.mp h with hab | via
    · exact ih hab
    · exact transCase a k b (ih (Bool.and_eq_true_iff.mp via).1)
        (ih (Bool.and_eq_true_iff.mp via).2)

private theorem referenceClosure_trans {n : Nat} {edge : Fin n → Fin n → Bool}
    {vertices : List (Fin n)} {a b d : Fin n} (hb : b ∈ vertices)
    (hab : referenceClosure edge vertices a b = true)
    (hbd : referenceClosure edge vertices b d = true) :
    referenceClosure edge vertices a d = true := by
  induction vertices generalizing a b d with
  | nil => simp at hb
  | cons k ks ih =>
    simp only [referenceClosure, closeAt, Bool.or_eq_true, Bool.and_eq_true] at hab hbd ⊢
    rcases List.mem_cons.mp hb with hb | hb
    · subst b
      exact Or.inr ⟨hab.elim (fun h => h) (fun h => h.1),
        hbd.elim (fun h => h) (fun h => h.2)⟩
    · rcases hab with hab | ⟨hak, hkb⟩
      · rcases hbd with hbd | ⟨hbk, hkd⟩
        · exact Or.inl (ih hb hab hbd)
        · exact Or.inr ⟨ih hb hab hbk, hkd⟩
      · rcases hbd with hbd | ⟨hbk, hkd⟩
        · exact Or.inr ⟨hak, ih hb hkb hbd⟩
        · exact Or.inr ⟨hak, hkd⟩

/-- Every direct edge is retained by the executable matrix closure. -/
theorem closure_of_edge {n : Nat} {edge : Fin n → Fin n → Bool}
    {vertices : List (Fin n)} {a b : Fin n} (h : edge a b = true) :
    closure edge vertices a b = true := by
  rw [closure_eq_reference]
  exact referenceClosure_of_edge h _

/-- Closure is transitive through each included intermediate vertex. -/
theorem closure_trans {n : Nat} {edge : Fin n → Fin n → Bool}
    {vertices : List (Fin n)} {a b d : Fin n} (hb : b ∈ vertices)
    (hab : closure edge vertices a b = true) (hbd : closure edge vertices b d = true) :
    closure edge vertices a d = true := by
  rw [closure_eq_reference] at hab hbd ⊢
  exact referenceClosure_trans (by simpa using hb) hab hbd

/-- Any transitive relation containing the edges also contains their closure. -/
theorem closure_induction {n : Nat} {edge : Fin n → Fin n → Bool}
    {vertices : List (Fin n)} {a b : Fin n} (R : Fin n → Fin n → Prop)
    (edgeCase : ∀ x y, edge x y = true → R x y)
    (transCase : ∀ x y z, R x y → R y z → R x z)
    (h : closure edge vertices a b = true) : R a b := by
  rw [closure_eq_reference] at h
  exact referenceClosure_induction R edgeCase transCase _ h

/-- A predicate preserved by every edge is preserved by every closure path. -/
theorem closure_preserves {n : Nat} {edge : Fin n → Fin n → Bool}
    {vertices : List (Fin n)} {a b : Fin n} (P : Fin n → Prop)
    (edgeCase : ∀ x y, edge x y = true → P x → P y)
    (h : closure edge vertices a b = true) (ha : P a) : P b :=
  closure_induction (fun x y => P x → P y) edgeCase
    (fun _ _ _ hxy hyz hx => hyz (hxy hx)) h ha

/-- Strictly increasing edge ranks increase along every closure path. -/
theorem closure_rank {n : Nat} {edge : Fin n → Fin n → Bool}
    {vertices : List (Fin n)} {a b : Fin n} (rank : Fin n → Nat)
    (edgeCase : ∀ x y, edge x y = true → rank x < rank y)
    (h : closure edge vertices a b = true) : rank a < rank b :=
  closure_induction (fun x y => rank x < rank y) edgeCase
    (fun _ _ _ hxy hyz => Nat.lt_trans hxy hyz) h

/-- Strictly increasing edge ranks exclude every closure cycle. -/
theorem closure_irrefl_of_rank {n : Nat} {edge : Fin n → Fin n → Bool}
    {vertices : List (Fin n)} (rank : Fin n → Nat)
    (edgeCase : ∀ x y, edge x y = true → rank x < rank y) (a : Fin n) :
    closure edge vertices a a = false := by
  cases h : closure edge vertices a a with
  | false => rfl
  | true => exact False.elim (Nat.lt_irrefl _ (closure_rank rank edgeCase h))

def happensBefore (c : Candidate Loc Val) (a b : c.Id) : Bool :=
  closure c.hbEdge c.ids a b

theorem happensBefore_of_hbEdge {c : Candidate Loc Val} {a b : c.Id}
    (h : c.hbEdge a b = true) : c.happensBefore a b = true :=
  closure_of_edge h

theorem happensBefore_trans {c : Candidate Loc Val} {a b d : c.Id}
    (hab : c.happensBefore a b = true) (hbd : c.happensBefore b d = true) :
    c.happensBefore a d = true :=
  closure_trans (by simp [ids]) hab hbd

theorem happensBefore_of_sequencedBefore {c : Candidate Loc Val} {a b : c.Id}
    (h : c.sequencedBefore a b = true) : c.happensBefore a b = true := by
  apply happensBefore_of_hbEdge
  simp [hbEdge, h]

theorem happensBefore_of_synchronizesWith {c : Candidate Loc Val} {a b : c.Id}
    (h : c.synchronizesWith a b = true) : c.happensBefore a b = true := by
  apply happensBefore_of_hbEdge
  simp [hbEdge, h]

/-- Release-store/acquire-load synchronization, `src/julia_atomics.h:116,128`,
`bbfa0ce4150`; C11 5.1.2.4p11. -/
theorem release_store_acquire_load_sync {c : Candidate Loc Val} {write read : c.Id}
    {loc : Loc} {stored observed : Val}
    (hstore : (c.event write).action = .store loc .release stored)
    (hload : (c.event read).action = .load loc .acquire observed)
    (hrf : c.readSource read write = true) : c.synchronizesWith write read = true := by
  have emptyInterval (i : c.Id) :
      decide ((c.event write).mo < (c.event i).mo ∧
        (c.event i).mo ≤ (c.event write).mo) = false := by
    have h : ¬((c.event write).mo < (c.event i).mo ∧
        (c.event i).mo ≤ (c.event write).mo) := by omega
    simp [h]
  have hself : c.releaseSequence write write = true := by
    simp [releaseSequence, isAtomicWrite, isWrite, sameLocation, hstore,
      Action.writeValue, Action.isPlain, Action.location, emptyInterval]
  have hreads : c.readsSequence write read = true := by
    unfold readsSequence
    apply Bool.and_eq_true_iff.mpr
    constructor
    · simp [isRead, hload, Action.readValue, Action.isPlain]
    · exact List.any_eq_true.mpr ⟨write, by simp [ids],
        Bool.and_eq_true_iff.mpr ⟨hrf, hself⟩⟩
  have hrelease : c.releaseEndpoint write write = true := by
    simp [releaseEndpoint, hstore, Action.isRelease, Action.writeValue,
      Action.isPlain, Action.order, Order.hasRelease]
  have hacquire : c.acquireEndpoint read read = true := by
    simp [acquireEndpoint, hload, Action.isAcquire, Action.readValue,
      Action.isPlain, Action.order, Order.hasAcquire]
  unfold synchronizesWith
  apply Bool.or_eq_true_iff.mpr
  left
  exact List.any_eq_true.mpr ⟨write, by simp [ids],
    Bool.and_eq_true_iff.mpr ⟨hrelease, List.any_eq_true.mpr ⟨read, by simp [ids],
      Bool.and_eq_true_iff.mpr ⟨hreads, hacquire⟩⟩⟩⟩

/-- The release/acquire read-from edge is a happens-before edge. -/
theorem release_store_acquire_load_happensBefore {c : Candidate Loc Val}
    {write read : c.Id} {loc : Loc} {stored observed : Val}
    (hstore : (c.event write).action = .store loc .release stored)
    (hload : (c.event read).action = .load loc .acquire observed)
    (hrf : c.readSource read write = true) : c.happensBefore write read = true :=
  happensBefore_of_synchronizesWith (release_store_acquire_load_sync hstore hload hrf)

/-- Per-read visibility. A write that happens before this read excludes all
older modifications; a write after this read cannot supply its value.
Source: `src/julia_atomics.h:105-116,247-259`, `bbfa0ce4150`;
C11 5.1.2.4p19-22. -/
def visibleWrites (c : Candidate Loc Val) (read : c.Id) : List c.Id :=
  c.ids.filter fun write => c.isAtomicWrite write && c.sameLocation write read &&
    !c.happensBefore read write &&
    c.ids.all (fun before =>
      !(c.isAtomicWrite before && c.sameLocation before read && c.happensBefore before read) ||
        decide ((c.event before).mo ≤ (c.event write).mo))

/-- Protocol-supplied C object declarations classify every non-init access at
its concrete location as atomic or ordinary. -/
def DeclaredAccessTyped (c : Candidate Loc Val) (declared : Loc → AccessClass) : Prop :=
  ∀ event : c.Id, ∀ location,
    (c.event event).action.location = some location →
    (c.event event).action.isInit = false →
      (c.event event).action.accessClass = some (declared location)

/-- A non-init read-from source has the read's access class. `.init` is a
neutral pre-execution seed and is checked separately by protocol declarations. -/
def ReadFromTyped (c : Candidate Loc Val) : Prop :=
  ∀ read source : c.Id, c.isRead read = true → c.readSource read source = true →
    (c.event source).action.isInit = true ∨
      (c.event source).action.accessClass = (c.event read).action.accessClass

def WellFormed (c : Candidate Loc Val) : Prop :=
  (∀ i : c.Id, (c.event i).action.validOrders = true) ∧
  (∀ i : c.Id, c.isRead i = true → ∃ source : c.Id,
    c.readSource i source = true ∧ c.isWrite source = true ∧
    c.sameLocation i source = true ∧
    (c.event i).action.readValue = (c.event source).action.writeValue) ∧
  (∀ i : c.Id, c.isRead i = false → (c.event i).readFrom = none) ∧
  (∀ i : c.Id, c.isAtomicWrite i = true →
    ((c.event i).action.isInit = true ↔ (c.event i).mo = 0)) ∧
  (∀ i j : c.Id, c.isAtomicWrite i = true → c.isAtomicWrite j = true →
    c.sameLocation i j = true → (c.event i).mo = (c.event j).mo → i = j) ∧
  (∀ i : c.Id, (c.isAtomicRead i = true ∨ c.isAtomicWrite i = true) →
    ∃ init : c.Id, (c.event init).action.isInit = true ∧ c.sameLocation i init = true) ∧
  (∀ i j : c.Id, (c.event i).action.isSC = true → (c.event j).action.isSC = true →
    (c.event i).sc = (c.event j).sc → i = j) ∧
  (∀ i : c.Id, ∀ d ∈ (c.event i).dependsOn, d < c.events.size) ∧
  c.ReadFromTyped

theorem WellFormed.readFromTyped {c : Candidate Loc Val} (h : c.WellFormed) : c.ReadFromTyped := by
  rcases h with ⟨_, _, _, _, _, _, _, _, typed⟩
  exact typed

/-- Ordinary allocation does not remove the initialization requirement for
any location accessed atomically. -/
theorem atomic_initialized {c : Candidate Loc Val} (h : c.WellFormed) (i : c.Id)
    (hi : c.isAtomicRead i = true ∨ c.isAtomicWrite i = true) :
    ∃ init : c.Id, (c.event init).action.isInit = true ∧ c.sameLocation i init = true :=
  h.2.2.2.2.2.1 i hi

def Coherent (c : Candidate Loc Val) : Prop :=
  (∀ i : c.Id, c.happensBefore i i = false) ∧
  (∀ a : c.Id, c.isAtomicWrite a = true → ∀ b : c.Id,
    c.isAtomicWrite b = true → c.sameLocation a b = true →
    c.modificationBefore a b = false →
    c.happensBefore a b = false) ∧
  (∀ write : c.Id, c.isAtomicWrite write = true → ∀ read : c.Id, c.isAtomicRead read = true →
    c.sameLocation write read = true → c.happensBefore write read = true →
    ∀ source : c.Id, c.readSource read source = true →
      (c.event write).mo ≤ (c.event source).mo) ∧
  (∀ read : c.Id, c.isAtomicRead read = true → ∀ write : c.Id, c.isAtomicWrite write = true →
    c.sameLocation read write = true → c.happensBefore read write = true →
    ∀ source : c.Id, c.readSource read source = true →
      (c.event source).mo < (c.event write).mo) ∧
  (∀ a : c.Id, c.isAtomicRead a = true → ∀ b : c.Id, c.isAtomicRead b = true →
    c.sameLocation a b = true → c.happensBefore a b = true →
    ∀ x : c.Id, c.readSource a x = true → ∀ y : c.Id, c.readSource b y = true →
      (c.event x).mo ≤ (c.event y).mo) ∧
  (∀ read : c.Id, c.isAtomicRead read = true → ∀ source : c.Id,
    c.readSource read source = true → c.happensBefore read source = false)

/-- `src/julia_atomics.h:130-195,199-227`, `bbfa0ce4150`;
C11 7.17.3p12: a successful RMW reads its immediate MO predecessor. -/
def RMWAtomicity (c : Candidate Loc Val) : Prop :=
  ∀ rmw : c.Id, (c.event rmw).action.isRMW = true →
    ∀ source : c.Id, c.readSource rmw source = true →
    (c.event source).mo < (c.event rmw).mo ∧
    ∀ other : c.Id, c.isAtomicWrite other = true → c.sameLocation rmw other = true →
      (c.event other).mo < (c.event rmw).mo → (c.event other).mo ≤ (c.event source).mo

def SCConsistent (c : Candidate Loc Val) : Prop :=
  (∀ a : c.Id, (c.event a).action.isSC = true →
    ∀ b : c.Id, (c.event b).action.isSC = true →
    (c.happensBefore a b = true ∨ c.modificationBefore a b = true) →
      (c.event a).sc < (c.event b).sc) ∧
  (∀ read : c.Id, (c.event read).action.isSC = true → c.isAtomicRead read = true →
    ∀ source : c.Id, c.readSource read source = true →
      (if (c.event source).action.isSC then
        (c.event source).sc < (c.event read).sc ∧
        ∀ a : c.Id, c.isAtomicWrite a = true → (c.event a).action.isSC = true →
          c.sameLocation a read = true → (c.event a).sc < (c.event read).sc →
            (c.event a).sc ≤ (c.event source).sc
       else ∀ a : c.Id, c.isAtomicWrite a = true → (c.event a).action.isSC = true →
         c.sameLocation a read = true → (c.event a).sc < (c.event read).sc →
           c.happensBefore source a = false)) ∧
  (∀ a : c.Id, c.isAtomicWrite a = true → (c.event a).action.isSC = true →
    ∀ read : c.Id, c.isAtomicRead read = true → c.sameLocation a read = true →
    ∀ source : c.Id, c.readSource read source = true →
    ∀ x : c.Id, (c.event x).action.isFence = true → (c.event x).action.isSC = true →
      (c.event a).sc < (c.event x).sc → c.sequencedBefore x read = true →
        (c.event a).mo ≤ (c.event source).mo) ∧
  (∀ read : c.Id, c.isAtomicRead read = true → (c.event read).action.isSC = true →
    ∀ a : c.Id, c.isAtomicWrite a = true → c.sameLocation a read = true →
    ∀ source : c.Id, c.readSource read source = true →
    ∀ x : c.Id, (c.event x).action.isFence = true → (c.event x).action.isSC = true →
      c.sequencedBefore a x = true → (c.event x).sc < (c.event read).sc →
        (c.event a).mo ≤ (c.event source).mo) ∧
  (∀ a : c.Id, c.isAtomicWrite a = true →
    ∀ read : c.Id, c.isAtomicRead read = true → c.sameLocation a read = true →
    ∀ source : c.Id, c.readSource read source = true →
    ∀ x : c.Id, (c.event x).action.isFence = true → (c.event x).action.isSC = true →
      c.sequencedBefore a x = true →
    ∀ y : c.Id, (c.event y).action.isFence = true → (c.event y).action.isSC = true →
      c.sequencedBefore y read = true → (c.event x).sc < (c.event y).sc →
        (c.event a).mo ≤ (c.event source).mo)

def RaceFree (c : Candidate Loc Val) : Prop :=
  ∀ a b : c.Id, a ≠ b → c.sameLocation a b = true →
    ((c.event a).action.isPlain = true ∨ (c.event b).action.isPlain = true) →
    (c.isWrite a = true ∨ c.isWrite b = true) →
    c.happensBefore a b = true ∨ c.happensBefore b a = true

abbrev DataRaceFree (c : Candidate Loc Val) : Prop := c.RaceFree

def dataRaceFree (c : Candidate Loc Val) : Bool := by
  let _ : Decidable c.RaceFree := by unfold RaceFree; infer_instance
  exact decide c.RaceFree

/-- Ordinary loads take their visible side effect, C11 5.1.2.4p19-21.
Their writes have no modification-order ranks. This check belongs to defined
executions, so an atomic candidate can still witness an ordinary data race. -/
def OrdinaryVisible (c : Candidate Loc Val) : Prop :=
  ∀ read source : c.Id, (c.event read).action.isPlain = true → c.isRead read = true →
    c.readSource read source = true → c.happensBefore source read = true ∧
      ∀ other : c.Id, c.isWrite other = true → c.sameLocation read other = true →
        ¬(c.happensBefore source other = true ∧ c.happensBefore other read = true)

/-- Mutex calls are already successful lock/unlock operations. The trace must
alternate them for each mutex and the unlocking thread must own that mutex.
Julia's observer mutex is `src/gc-stock.c:49-50`, `bbfa0ce4150`. -/
def MutexEventValid (c : Candidate Loc Val) (i : c.Id) : Prop :=
  match (c.event i).action with
    | .lock m =>
      ∀ j : c.Id, j.val < i.val → (c.event j).action = .lock m →
        ∃ k : c.Id, j.val < k.val ∧ k.val < i.val ∧
          (c.event k).action = .unlock m ∧ (c.event k).thread = (c.event j).thread
    | .unlock m =>
      ∃ j : c.Id, j.val < i.val ∧ (c.event j).action = .lock m ∧
        (c.event j).thread = (c.event i).thread ∧
        ∀ k : c.Id, j.val < k.val → k.val < i.val →
          (c.event k).action ≠ .unlock m
    | _ => True

private instance (c : Candidate Loc Val) (i : c.Id) : Decidable (c.MutexEventValid i) := by
  unfold MutexEventValid
  split <;> infer_instance

def MutexValid (c : Candidate Loc Val) : Prop := ∀ i : c.Id, c.MutexEventValid i

def justificationEdge (c : Candidate Loc Val) (a b : c.Id) : Bool :=
  c.readSource b a || decide (a.val ∈ (c.event b).dependsOn) ||
    (c.isWrite a && c.isWrite b && c.sameLocation a b && c.happensBefore a b)

def Justified (c : Candidate Loc Val) : Prop :=
  ∀ i : c.Id, closure c.justificationEdge c.ids i i = false

/-- Forward justification edges imply acyclicity without evaluating the table. -/
theorem justified_of_forward (c : Candidate Loc Val)
    (h : ∀ a b : c.Id, c.justificationEdge a b = true → a.val < b.val) : c.Justified := by
  intro i
  exact closure_irrefl_of_rank (fun j : c.Id => j.val) h i

/-- Executable acceptance condition for all explicit memory choices. No
condition requires a read-from source to occur earlier in the scheduler. -/
def Consistent (c : Candidate Loc Val) : Prop :=
  c.WellFormed ∧ c.Coherent ∧ c.RMWAtomicity ∧ c.SCConsistent ∧
    c.MutexValid ∧ c.Justified

set_option synthInstance.maxSize 4096 in
private instance (c : Candidate Loc Val) : Decidable c.WellFormed := by
  unfold WellFormed ReadFromTyped
  infer_instance

set_option synthInstance.maxSize 4096 in
private instance (c : Candidate Loc Val) : Decidable c.Coherent := by
  unfold Coherent
  infer_instance

set_option synthInstance.maxSize 32768 in
private instance (c : Candidate Loc Val) : Decidable c.SCConsistent := by
  unfold SCConsistent
  infer_instance

set_option synthInstance.maxSize 4096 in
instance (c : Candidate Loc Val) : Decidable c.Consistent := by
  unfold Consistent RMWAtomicity MutexValid Justified
  infer_instance

def consistent (c : Candidate Loc Val) : Bool := decide c.Consistent

/-- A defined execution has legal memory choices, no C11 5.1.2.4p25 ordinary
data race, and valid ordinary read visibility. Protocol source typing is a
separate `DeclaredAccessTyped` obligation against the actual C declaration. -/
def Defined (c : Candidate Loc Val) : Prop := c.Consistent ∧ c.RaceFree ∧ c.OrdinaryVisible

def defined (c : Candidate Loc Val) : Bool :=
  let _ : Decidable c.OrdinaryVisible := by unfold OrdinaryVisible; infer_instance
  c.consistent && c.dataRaceFree && decide c.OrdinaryVisible

theorem rmw_reads_immediate {c : Candidate Loc Val} (h : c.consistent = true)
    (rmw source : c.Id) (hr : (c.event rmw).action.isRMW = true)
    (hs : c.readSource rmw source = true) :
    (c.event source).mo < (c.event rmw).mo ∧
    ∀ other : c.Id, c.isAtomicWrite other = true → c.sameLocation rmw other = true →
      (c.event other).mo < (c.event rmw).mo → (c.event other).mo ≤ (c.event source).mo :=
  (of_decide_eq_true h : c.Consistent).2.2.1 rmw hr source hs

theorem write_read_coherent {c : Candidate Loc Val} (h : c.consistent = true)
    (write read source : c.Id) (hw : c.isAtomicWrite write = true)
    (hr : c.isAtomicRead read = true)
    (hl : c.sameLocation write read = true) (hh : c.happensBefore write read = true)
    (hs : c.readSource read source = true) : (c.event write).mo ≤ (c.event source).mo :=
  (of_decide_eq_true h : c.Consistent).2.1.2.2.1 write hw read hr hl hh source hs

end Candidate

/-- One source operation with arbitrary explicit C11 choices. Final acceptance
uses `Candidate.consistent`; prefixes may refer to a later write. -/
inductive Step : Candidate Loc Val → Event Loc Val → Candidate Loc Val → Prop where
  | emit (c : Candidate Loc Val) (e : Event Loc Val) : Step c e (c.append e)

def run (events : List (Event Loc Val)) : Candidate Loc Val := ⟨events.toArray⟩

/-- `src/julia_atomics.h:115,127,258-259`, `bbfa0ce4150`:
a relaxed reader can choose either concurrent modification. -/
def relaxedExample (newValue : Bool) : Candidate Nat Nat := ⟨#[
  { thread := 0, action := .init 0 0 },
  { thread := 1, action := .store 0 .relaxed 7, mo := 1 },
  { thread := 2, action := .load 0 .relaxed (if newValue then 7 else 0),
    readFrom := some (if newValue then 1 else 0) }]⟩

example : (relaxedExample false).consistent = true := by decide
example : (relaxedExample true).consistent = true := by decide

/-- `src/julia_atomics.h:116,128`, `bbfa0ce4150`: acquire publication
makes the earlier ordinary store visible. Reading the old payload is rejected. -/
def publicationExample (newValue : Bool) : Candidate Nat Nat := ⟨#[
  { thread := 0, action := .init 0 0 },
  { thread := 0, action := .init 1 0 },
  { thread := 1, action := .plainStore 0 7, mo := 1 },
  { thread := 1, action := .store 1 .release 1, mo := 1 },
  { thread := 2, action := .load 1 .acquire 1, readFrom := some 3 },
  { thread := 2, action := .plainLoad 0 (if newValue then 7 else 0),
    readFrom := some (if newValue then 2 else 0) }]⟩

example : (publicationExample true).defined = true := by decide
example : (publicationExample false).defined = false := by decide

/-- Unqualified fetch-add and CAS are SC,
`src/julia_atomics.h:130-133,163-166,201-218`, `bbfa0ce4150`. -/
def seqCstRMWExample : Candidate Nat Nat := ⟨#[
  { thread := 0, action := .init 0 0 },
  { thread := 1, action := .rmw 0 .seqCst 0 1, readFrom := some 0, mo := 1, sc := 0 },
  { thread := 2, action := .cas 0 .seqCst .seqCst 1 2 1,
    readFrom := some 1, mo := 2, sc := 1 }]⟩

example : seqCstRMWExample.consistent = true := by decide

/-- Relaxed read-from is independent of the chosen thread interleaving,
`src/julia_atomics.h:115,127,258-259`, `bbfa0ce4150`. -/
def forwardRFExample : Candidate Nat Nat := ⟨#[
  { thread := 0, action := .init 0 0 },
  { thread := 2, action := .load 0 .relaxed 7, readFrom := some 2 },
  { thread := 1, action := .store 0 .relaxed 7, mo := 1 }]⟩

example : forwardRFExample.consistent = true := by decide

/-- The release-fence/relaxed-store publication pattern in
`src/work-stealing-queue.h:68-69,98`, `bbfa0ce4150`. -/
def releaseFenceExample : Candidate Nat Nat := ⟨#[
  { thread := 0, action := .init 0 0 },
  { thread := 1, action := .fence .release },
  { thread := 1, action := .store 0 .relaxed 1, mo := 1 },
  { thread := 2, action := .load 0 .acquire 1, readFrom := some 2 }]⟩

example : releaseFenceExample.synchronizesWith (1 : Fin 4) (3 : Fin 4) = true := by decide
example : releaseFenceExample.consistent = true := by decide

/-- Malloc-created metadata and payload start with ordinary stores, as in
`src/work-stealing-queue.h:30-36,67`, `bbfa0ce4150`. Release/acquire publication
orders both fields without assigning them a global initialization event. -/
def mallocPublicationExample : Candidate Nat Nat := ⟨#[
  { thread := 0, action := .init 0 0 },
  { thread := 1, action := .plainStore 1 2 },
  { thread := 1, action := .plainStore 2 7 },
  { thread := 1, action := .store 0 .release 1, mo := 1 },
  { thread := 2, action := .load 0 .acquire 1, readFrom := some 3 },
  { thread := 2, action := .plainLoad 1 2, readFrom := some 1, dependsOn := [4] },
  { thread := 2, action := .plainLoad 2 7, readFrom := some 2, dependsOn := [4] }]⟩

example : mallocPublicationExample.defined = true := by decide

/-- A future same-thread ordinary store cannot initialize an earlier load. -/
def loadBeforePlainStoreExample : Candidate Nat Nat := ⟨#[
  { thread := 1, action := .plainLoad 1 7, readFrom := some 1 },
  { thread := 1, action := .plainStore 1 7 }]⟩

example : loadBeforePlainStoreExample.defined = false := by decide

/-- Atomic accesses still require an explicit initialization. -/
example : (run [{ thread := 1, action := .store (0 : Nat) .relaxed (7 : Nat), mo := 1 }]).consistent =
    false := by decide

end JuliaLean.CRuntime.Memory

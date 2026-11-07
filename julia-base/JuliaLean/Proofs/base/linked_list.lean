import JuliaLean.base.linked_list
import JuliaLean.Registry.Types

/-!
# Specifications of `base/linked_list.jl`

The registry properties use the linked-list methods in `JuliaLean.base.linked_list`; node identity,
link fields, list endpoints, and wait-entry owner slots remain explicit in the heap.
-/

/-!
PROPOSAL: mechanical migration of existing unapproved legacy callers only.
All original registry IDs/statuses are retained; none is approved by this file.
Existing callback-law, assumed-success, private-subject, detached-list identity,
generic type and error-state defects remain. Native count comparisons now use
the Int64 residue of the mathematical reference count, matching the repaired
counter type instead of imposing an artificial heap-size bound. The two finite
observation collectors keep their original Except signatures. These legacy
formulas are not new public property drafts; see the separate disposition table.
-/

namespace JuliaLean.Proofs.base.linked_list

open JuliaLean.base.linked_list JuliaLean.Registry

inductive ListAction where
  | push (node : NodeId)
  | pushfirst (node : NodeId)
  | pop
  | popfirst
  | delete (node : NodeId)
  deriving Repr, DecidableEq

def runIntrusiveActions {α : Type} (h : Heap α) (q : InvasiveLinkedList α) :
    List ListAction → Option (Except ListFailure (Heap α × InvasiveLinkedList α))
  | [] => some (.ok (h, q))
  | action :: rest =>
      let step : Option (Except ListFailure (Heap α × InvasiveLinkedList α)) :=
        match action with
        | .push node => some (pushIntrusive h q node)
        | .pushfirst node => some (pushfirstIntrusive h q node)
        | .pop =>
            match popIntrusive h q with
            | none => none
            | some (.error e) => some (.error e)
            | some (.ok (h, q, _)) => some (.ok (h, q))
        | .popfirst =>
            match popfirstIntrusive h q with
            | none => none
            | some (.error e) => some (.error e)
            | some (.ok (h, q, _)) => some (.ok (h, q))
        | .delete node => listDeleteFirstIntrusive h q node
      match step with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (h, q)) => runIntrusiveActions h q rest

private def clearLinksAndOwner {α : Type} (h : Heap α) (id : NodeId) : Prop :=
  ∃ node, h.node? id = some node ∧ node.next = none ∧ node.queue = none


private def eraseFirstBy {α : Type} (same : α → α → Bool) (value : α) : List α → List α
  | [] => []
  | first :: rest => if same first value then rest else first :: eraseFirstBy same value rest

private def otherOwnersPreserved {α : Type} (h h' : Heap α) (owner : OwnerId) : Prop :=
  ∀ id node node', h.node? id = some node → h'.node? id = some node' →
    node'.slots.length = node.slots.length ∧
      ∀ index slot, slotAt node.slots index = some slot →
        slot.owner.isSome → slot.owner ≠ some owner →
          slotAt node'.slots index = some slot

private def waitingEntryArmed {α : Type} (h : Heap α) (id : NodeId) : Bool :=
  match h.node? id with
  | none => false
  | some node =>
      match node.task with
      | none => false
      | some task => Heap.lookupTask h.tasksWaitingOn task == some (some id)

/-- Every successful sequence of intrusive pushes, pops and identity deletions preserves the unique chain, endpoints and node ownership. -/
def LinkedListWellFormed : Prop :=
  ∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (actions : List ListAction)
    (h' : Heap α) (q' : InvasiveLinkedList α),
    intrusiveWellFormed h q →
    runIntrusiveActions h q actions = some (.ok (h', q')) →
    intrusiveWellFormed h' q' ∧
      ∀ (other : InvasiveLinkedList α), other.id ≠ q'.id → intrusiveWellFormed h' other →
        ∀ id, id ∈ intrusiveNodes h' q' → id ∉ intrusiveNodes h' other

/-- A fresh list is empty, satisfies the chain and owner invariant, and has no first iterator item. -/
def IntrusiveConstructorSpec : Prop :=
  ∀ {α : Type} (h : Heap α),
    (h.nodes.map (fun entry => entry.1)).Nodup →
    (∀ id node, (id, node) ∈ h.nodes → node.queue ≠ some h.nextList) →
    let (h', q) := newIntrusiveLinkedList h
    h'.nextList = h.nextList + 1 ∧ h'.nodes = h.nodes ∧ q.id = h.nextList ∧
      q.head = none ∧ q.tail = none ∧ isemptyIntrusive q = true ∧
      intrusiveWellFormed h' q ∧ iterateIntrusiveStart q = none ∧
      intrusiveIteration h' q = .ok []

/-- Intrusive iteration yields every node identity once, in its `next` order. -/
def IntrusiveIterationSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    intrusiveWellFormed h q → intrusiveIteration h q = .ok (intrusiveNodes h q)

/-- `isempty` agrees with the chain, and the `ILLRef` forwarding method gives the same result. -/
def IntrusiveIsEmptySpec : Prop :=
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    intrusiveWellFormed h q →
      isemptyIntrusive q = decide (intrusiveNodes h q = [])) ∧
  (∀ {α : Type} (qr : ILLRef α),
    isemptyILLRef qr = isemptyIntrusive qr.list)

/-- Intrusive length counts the linked nodes, and the `ILLRef` overload forwards that count. -/
def IntrusiveLengthSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    intrusiveWellFormed h q →
      lengthIntrusive h q = some (.ok (JuliaLean.JInt.wrap .i64 (Int.ofNat (intrusiveNodes h q).length)))) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α),
    lengthILLRef h qr = lengthIntrusive h qr.list)

/-- The native counter wraps for arbitrary finite chains and is exact whenever
the reachable-node count fits the return type. -/
def IntrusiveLengthSourceSpec : Prop :=
  IntrusiveLengthSpec ∧
  ∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    intrusiveWellFormed h q →
    (Int.ofNat (intrusiveNodes h q).length ≤ JuliaLean.IntTy.max .i64) →
    ∃ count, lengthIntrusive h q = some (.ok count) ∧
      count.val = Int.ofNat (intrusiveNodes h q).length

/-- Appending a distinct list concatenates its identities in order, empties the source list,
and transfers each source node's queue owner; appending a list to itself raises an error. -/
def IntrusiveAppendSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (q q2 : InvasiveLinkedList α),
    q.id ≠ q2.id → intrusiveWellFormed h q → intrusiveWellFormed h q2 →
    match appendIntrusive h q q2 with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q', q2')) =>
        intrusiveWellFormed h' q' ∧ intrusiveWellFormed h' q2' ∧
          intrusiveNodes h' q' = intrusiveNodes h q ++ intrusiveNodes h q2 ∧
          q2'.head = none ∧ q2'.tail = none ∧
          ∀ id ∈ intrusiveNodes h q2,
            ∃ node, h'.node? id = some node ∧ node.queue = some q.id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    appendIntrusive h q q = some (.error .sameListAppend))

/-- Both intrusive push overloads append one detached node, set its queue owner, and preserve the
chain; inserting a node whose queue is already occupied raises the documented error. -/
def IntrusivePushSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId),
    intrusiveWellFormedFor h qr.list qr.waitee → detachedNode h id →
    match pushILLRef h qr id with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormedFor h' q' qr.waitee ∧
          intrusiveNodes h' q' = intrusiveNodes h qr.list ++ [id] ∧
          (∃ node, h'.node? id = some node ∧ node.queue = some qr.waitee ∧ node.next = none)) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId),
    intrusiveWellFormed h q → detachedNode h id →
    match pushIntrusive h q id with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormed h' q' ∧ intrusiveNodes h' q' = intrusiveNodes h q ++ [id] ∧
          (∃ node, h'.node? id = some node ∧ node.queue = some q.id ∧ node.next = none)) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId) (node : HeapNode α),
    h.node? id = some node → node.queue.isSome →
      pushILLRef h qr id = .error .alreadyQueued) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId) (node : HeapNode α),
    h.node? id = some node → node.queue.isSome →
      pushIntrusive h q id = .error .alreadyQueued)

/-- Both intrusive prepend overloads put one detached node before the old head, update ownership,
and reject a node already owned by a list. -/
def IntrusivePushFirstSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId),
    intrusiveWellFormedFor h qr.list qr.waitee → detachedNode h id →
    match pushfirstILLRef h qr id with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormedFor h' q' qr.waitee ∧
          intrusiveNodes h' q' = id :: intrusiveNodes h qr.list ∧
          (∃ node, h'.node? id = some node ∧ node.queue = some qr.waitee)) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId),
    intrusiveWellFormed h q → detachedNode h id →
    match pushfirstIntrusive h q id with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormed h' q' ∧ intrusiveNodes h' q' = id :: intrusiveNodes h q ∧
          (∃ node, h'.node? id = some node ∧ node.queue = some q.id)) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId) (node : HeapNode α),
    h.node? id = some node → node.queue.isSome →
      pushfirstILLRef h qr id = .error .alreadyQueued) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId) (node : HeapNode α),
    h.node? id = some node → node.queue.isSome →
      pushfirstIntrusive h q id = .error .alreadyQueued)

/-- Tail pops return the former tail and detach it. Popping either an empty `ILLRef` or empty
intrusive list raises an error. -/
def IntrusivePopSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (ids : List NodeId) (id : NodeId),
    intrusiveWellFormedFor h qr.list qr.waitee → intrusiveNodes h qr.list = ids ++ [id] →
    match popILLRef h qr with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q', popped)) =>
        popped = id ∧ intrusiveWellFormedFor h' q' qr.waitee ∧
          intrusiveNodes h' q' = ids ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (ids : List NodeId) (id : NodeId),
    intrusiveWellFormed h q → intrusiveNodes h q = ids ++ [id] →
    match popIntrusive h q with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q', popped)) =>
        popped = id ∧ intrusiveWellFormed h' q' ∧
          intrusiveNodes h' q' = ids ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α),
    qr.list.head = none → qr.list.tail = none → popILLRef h qr = some (.error .typeError)) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    q.head = none → q.tail = none → popIntrusive h q = some (.error .typeError))

/-- Head pops return the former head and detach it. Popping either an empty `ILLRef` or empty
intrusive list raises an error. -/
def IntrusivePopFirstSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId) (rest : List NodeId),
    intrusiveWellFormedFor h qr.list qr.waitee → intrusiveNodes h qr.list = id :: rest →
    match popfirstILLRef h qr with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q', popped)) =>
        popped = id ∧ intrusiveWellFormedFor h' q' qr.waitee ∧
          intrusiveNodes h' q' = rest ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId) (rest : List NodeId),
    intrusiveWellFormed h q → intrusiveNodes h q = id :: rest →
    match popfirstIntrusive h q with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q', popped)) =>
        popped = id ∧ intrusiveWellFormed h' q' ∧
          intrusiveNodes h' q' = rest ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α),
    qr.list.head = none → qr.list.tail = none → popfirstILLRef h qr = some (.error .typeError)) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    q.head = none → q.tail = none → popfirstIntrusive h q = some (.error .typeError))

/-- Identity deletion removes exactly the selected node and clears its links. `ILLRef` deletion is
a no-op precisely when the node's `queue` does not name that reference's waitee. -/
def IntrusiveDeleteSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId) (node : HeapNode α),
    h.node? id = some node → node.queue ≠ some qr.waitee →
      listDeleteFirstILLRef h qr id = some (.ok (h, qr.list))) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId),
    intrusiveWellFormedFor h qr.list qr.waitee → id ∈ intrusiveNodes h qr.list →
    match listDeleteFirstILLRef h qr id with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q')) =>
        intrusiveWellFormedFor h' q' qr.waitee ∧
          intrusiveNodes h' q' = (intrusiveNodes h qr.list).erase id ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId),
    intrusiveWellFormed h q → id ∈ intrusiveNodes h q →
    match listDeleteFirstIntrusive h q id with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q')) =>
        intrusiveWellFormed h' q' ∧ intrusiveNodes h' q' = (intrusiveNodes h q).erase id ∧
          clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId),
    intrusiveWellFormed h q → id ∈ intrusiveNodes h q →
    match deleteFirstIntrusive h q id with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q')) =>
        intrusiveWellFormed h' q' ∧ intrusiveNodes h' q' = (intrusiveNodes h q).erase id ∧
          clearLinksAndOwner h' id)

/-- The generic registry property retains the method-wide invariant through the per-operation
specifications. -/
def LinkedGenericBodies : Prop :=
  IntrusiveConstructorSpec ∧ IntrusiveIterationSpec ∧
    IntrusiveIsEmptySpec ∧ IntrusiveLengthSpec ∧ IntrusiveAppendSpec ∧ IntrusivePushSpec ∧
    IntrusivePushFirstSpec ∧ IntrusivePopSpec ∧ IntrusivePopFirstSpec ∧ IntrusiveDeleteSpec

/-- `LinkedListItem` allocates one fresh detached node carrying its input value. -/
def LinkedItemConstructionSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (value : α),
    h.node? h.nextNode = none →
    let (h', item) := newLinkedListItem h value
    h'.nodes.length = h.nodes.length + 1 ∧
      ∃ node, h'.node? item.id = some node ∧ node.value = value ∧
        node.next = none ∧ node.queue = none


/-- Boxed iteration yields each stored value in node order. -/
def LinkedIterationSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α),
    intrusiveWellFormed h q → linkedValues h q = some (.ok values) → linkedIteration h q = .ok values

/-- The generic empty and length methods agree with the boxed value sequence. -/
def LinkedIsEmptySpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α),
    intrusiveWellFormed h q → linkedValues h q = some (.ok values) →
      isemptyIntrusive q = decide (values = [])

def LinkedLengthSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α),
    intrusiveWellFormed h q → linkedValues h q = some (.ok values) →
      lengthIntrusive h q = some (.ok (JuliaLean.JInt.wrap .i64 (Int.ofNat values.length)))

def LinkedLengthSourceSpec : Prop :=
  LinkedLengthSpec ∧
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α),
    intrusiveWellFormed h q → linkedValues h q = some (.ok values) →
    (Int.ofNat values.length ≤ JuliaLean.IntTy.max .i64) →
    ∃ count, lengthIntrusive h q = some (.ok count) ∧ count.val = Int.ofNat values.length

/-- Appending two boxed lists preserves their value order and empties the source list. -/
def LinkedAppendSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q q2 : LinkedList α) (values values2 : List α),
    q.id ≠ q2.id → intrusiveWellFormed h q → intrusiveWellFormed h q2 →
    linkedValues h q = some (.ok values) → linkedValues h q2 = some (.ok values2) →
    match appendIntrusive h q q2 with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q', q2')) =>
        intrusiveWellFormed h' q' ∧ linkedValues h' q' = some (.ok (values ++ values2)) ∧
          q2'.head = none ∧ q2'.tail = none ∧
          ∀ id ∈ intrusiveNodes h q2,
            ∃ node, h'.node? id = some node ∧ node.queue = some q.id

/-- Boxed `push!` allocates one fresh item node and appends its value and owner link. -/
def LinkedPushSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α) (value : α),
    intrusiveWellFormed h q → linkedValues h q = some (.ok values) → h.node? h.nextNode = none →
    match pushLinked h q value with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormed h' q' ∧ linkedValues h' q' = some (.ok (values ++ [value])) ∧
          intrusiveNodes h' q' = intrusiveNodes h q ++ [h.nextNode] ∧
          h'.nodes.length = h.nodes.length + 1 ∧
          (∃ node, h'.node? h.nextNode = some node ∧ node.value = value ∧
            node.queue = some q.id ∧ node.next = none)

/-- Boxed `pushfirst!` allocates one fresh item node and prepends its value and owner link. -/
def LinkedPushFirstSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α) (value : α),
    intrusiveWellFormed h q → linkedValues h q = some (.ok values) → h.node? h.nextNode = none →
    match pushfirstLinked h q value with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormed h' q' ∧ linkedValues h' q' = some (.ok (value :: values)) ∧
          intrusiveNodes h' q' = h.nextNode :: intrusiveNodes h q ∧
          h'.nodes.length = h.nodes.length + 1 ∧
          (∃ node, h'.node? h.nextNode = some node ∧ node.value = value ∧
            node.queue = some q.id)

/-- Boxed tail pop returns and removes the final value, and errors on an empty list. -/
def LinkedPopSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (q : LinkedList α) (values rest : List α) (last : α),
    intrusiveWellFormed h q → linkedValues h q = some (.ok values) → values = rest ++ [last] →
    match popLinked h q with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q', value)) =>
        value = last ∧ intrusiveWellFormed h' q' ∧ linkedValues h' q' = some (.ok rest) ∧
          ∃ id node, q.tail = some id ∧ h'.node? id = some node ∧
            node.next = none ∧ node.queue = none) ∧
  (∀ {α : Type} (h : Heap α) (q : LinkedList α),
    q.head = none → q.tail = none → popLinked h q = some (.error .typeError))

/-- Boxed head pop returns and removes the first value, and errors on an empty list. -/
def LinkedPopFirstSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (q : LinkedList α) (first : α) (rest : List α),
    intrusiveWellFormed h q → linkedValues h q = some (.ok (first :: rest)) →
    match popfirstLinked h q with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q', value)) =>
        value = first ∧ intrusiveWellFormed h' q' ∧ linkedValues h' q' = some (.ok rest) ∧
          ∃ id node, q.head = some id ∧ h'.node? id = some node ∧
            node.next = none ∧ node.queue = none) ∧
  (∀ {α : Type} (h : Heap α) (q : LinkedList α),
    q.head = none → q.tail = none → popfirstLinked h q = some (.error .typeError))

/-- Boxed value deletion removes only the first value accepted by Julia's `isequal` predicate. -/
def LinkedDeleteSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α)
    (same : α → α → Bool) (value : α),
    intrusiveWellFormed h q → linkedValues h q = some (.ok values) →
    match listDeleteFirstLinked h q same value with
    | none => False
    | some (.error _) => False
    | some (.ok (h', q')) =>
        intrusiveWellFormed h' q' ∧ linkedValues h' q' = some (.ok (eraseFirstBy same value values))

/-- The old boxed registry property keeps allocation, iteration, end-pop, and first-match deletion
promises, with fresh identity required for allocating pushes. -/
def LinkedBoxedBodies : Prop :=
  LinkedItemConstructionSpec ∧ LinkedIterationSpec ∧ LinkedIsEmptySpec ∧
    LinkedLengthSpec ∧ LinkedAppendSpec ∧ LinkedPushSpec ∧ LinkedPushFirstSpec ∧
    LinkedPopSpec ∧ LinkedPopFirstSpec ∧ LinkedDeleteSpec

/-- Interface laws for the fixed owner/next/aux slots supplied by `base/cancellation.jl`.
Allocation uses an existing free slot, and release clears that slot without removing it. -/
structure WaitEntryOpsLaws {α : Type} (ops : WaitEntryOps α) : Prop where
  findSlot_zero :
    ∀ (h : Heap α) (id : NodeId) (owner : OwnerId) (node : HeapNode α),
      h.node? id = some node →
      (ops.findSlot h id owner = 0 ↔ ∀ slot ∈ node.slots, slot.owner ≠ some owner)
  findSlot_hit :
    ∀ (h : Heap α) (id : NodeId) (owner : OwnerId) (node : HeapNode α),
      h.node? id = some node → ops.findSlot h id owner ≠ 0 →
      ∃ slot, slotAt node.slots (ops.findSlot h id owner) = some slot ∧ slot.owner = some owner
  slotNext_read :
    ∀ (h : Heap α) (id : NodeId) (index : Nat) (node : HeapNode α) (slot : WaitSlot),
      h.node? id = some node →
      slotAt node.slots index = some slot → ops.slotNext h id index = slot.next
  setSlotNext_write :
    ∀ (h : Heap α) (id : NodeId) (index : Nat) (node : HeapNode α)
      (slot : WaitSlot) (next : Option NodeId) (slots : List WaitSlot),
      h.node? id = some node →
      slotAt node.slots index = some slot →
      setSlotAt node.slots index { slot with next := next } = some slots →
      ops.setSlotNext h id index next = h.setNode id { node with slots := slots }
  nextOn_read :
    ∀ (h : Heap α) (id : NodeId) (owner : OwnerId), ops.nextOn h id owner =
      if ops.findSlot h id owner == 0 then none
      else ops.slotNext h id (ops.findSlot h id owner)
  acquireSlot_full :
    ∀ (h : Heap α) (id : NodeId) (owner : OwnerId) (node : HeapNode α),
      h.node? id = some node → ops.findSlot h id owner = 0 →
      (∀ slot ∈ node.slots, slot.owner ≠ none) →
      ops.acquireSlot h id owner = .error .slotOverflow
  acquireSlot_free :
    ∀ (h : Heap α) (id : NodeId) (owner : OwnerId) (node : HeapNode α)
      (index : Nat) (slot : WaitSlot) (slots : List WaitSlot), h.node? id = some node →
      ops.findSlot h id owner = 0 → slotAt node.slots index = some slot → slot.owner = none →
      (∀ earlier, 0 < earlier → earlier < index →
        ∀ earlierSlot, slotAt node.slots earlier = some earlierSlot → earlierSlot.owner ≠ none) →
      setSlotAt node.slots index { slot with owner := some owner } = some slots →
      ops.acquireSlot h id owner = .ok (h.setNode id { node with slots := slots }, index)
  releaseSlot_clear :
    ∀ (h : Heap α) (id : NodeId) (index : Nat) (node : HeapNode α)
      (slot : WaitSlot) (slots : List WaitSlot), h.node? id = some node →
      slotAt node.slots index = some slot →
      setSlotAt node.slots index { owner := none, next := none, aux := 0 } = some slots →
      ops.releaseSlot h id index = h.setNode id { node with slots := slots }

private def releasedWaitSlot {α : Type} (ops : WaitEntryOps α) (h h' : Heap α)
    (id : NodeId) (owner : OwnerId) : Prop :=
  ∃ node node', h.node? id = some node ∧ h'.node? id = some node' ∧
    node'.slots.length = node.slots.length ∧
      slotAt node'.slots (ops.findSlot h id owner) =
        some { owner := none, next := none, aux := 0 }

/-- Wait-entry list operations preserve each owner's independent chain and fixed slots, reject
duplicate registration, propagate slot overflow, and detect tasks still waiting on an entry. -/
def LinkedWaitEntryBodies : Prop :=
  ∀ (α : Type) (ops : WaitEntryOps α), WaitEntryOpsLaws ops →
  (∀ (h : Heap α) (qr : ILLRef α) (id : NodeId) (node : HeapNode α),
    waitEntryWellFormed ops h qr.list qr.waitee → h.node? id = some node →
    ops.findSlot h id qr.waitee = 0 → (∃ slot ∈ node.slots, slot.owner = none) →
      match pushWaitEntry ops h qr id with
      | .error _ => False
      | .ok (h', q') =>
          waitEntryWellFormed ops h' q' qr.waitee ∧
            waitEntryNodes ops h' q' qr.waitee = waitEntryNodes ops h qr.list qr.waitee ++ [id] ∧
            ops.findSlot h' id qr.waitee ≠ 0 ∧ otherOwnersPreserved h h' qr.waitee) ∧
  (∀ (h : Heap α) (qr : ILLRef α) (id : NodeId) (node : HeapNode α),
    waitEntryWellFormed ops h qr.list qr.waitee → h.node? id = some node →
    ops.findSlot h id qr.waitee = 0 → (∃ slot ∈ node.slots, slot.owner = none) →
      match pushfirstWaitEntry ops h qr id with
      | .error _ => False
      | .ok (h', q') =>
          waitEntryWellFormed ops h' q' qr.waitee ∧
            waitEntryNodes ops h' q' qr.waitee = id :: waitEntryNodes ops h qr.list qr.waitee ∧
            ops.findSlot h' id qr.waitee ≠ 0 ∧ otherOwnersPreserved h h' qr.waitee) ∧
  (∀ (h : Heap α) (qr : ILLRef α) (id : NodeId),
    ops.findSlot h id qr.waitee ≠ 0 →
      pushWaitEntry ops h qr id = .error .alreadyInWaitList ∧
        pushfirstWaitEntry ops h qr id = .error .alreadyInWaitList) ∧
  (∀ (h : Heap α) (qr : ILLRef α) (id : NodeId) (node : HeapNode α),
    h.node? id = some node → ops.findSlot h id qr.waitee = 0 →
    (∀ slot ∈ node.slots, slot.owner ≠ none) →
      pushWaitEntry ops h qr id = .error .slotOverflow ∧
        pushfirstWaitEntry ops h qr id = .error .slotOverflow) ∧
  (∀ (h : Heap α) (qr : ILLRef α) (id : NodeId) (rest : List NodeId),
    waitEntryWellFormed ops h qr.list qr.waitee →
    waitEntryNodes ops h qr.list qr.waitee = id :: rest →
      match popfirstWaitEntry ops h qr with
      | .error _ => False
      | .ok (h', q', popped) =>
          popped = id ∧ waitEntryWellFormed ops h' q' qr.waitee ∧
            waitEntryNodes ops h' q' qr.waitee = rest ∧ ops.findSlot h' id qr.waitee = 0 ∧
            releasedWaitSlot ops h h' id qr.waitee ∧ otherOwnersPreserved h h' qr.waitee) ∧
  (∀ (h : Heap α) (qr : ILLRef α),
    qr.list.head = none → popfirstWaitEntry ops h qr = .error .typeError) ∧
  (∀ (h : Heap α) (qr : ILLRef α) (ids : List NodeId) (id : NodeId),
    waitEntryWellFormed ops h qr.list qr.waitee →
    waitEntryNodes ops h qr.list qr.waitee = ids ++ [id] →
      match popWaitEntry ops h qr with
      | none => False
      | some (.error _) => False
      | some (.ok (h', q', popped)) =>
          popped = id ∧ waitEntryWellFormed ops h' q' qr.waitee ∧
            waitEntryNodes ops h' q' qr.waitee = ids ∧ ops.findSlot h' id qr.waitee = 0 ∧
            releasedWaitSlot ops h h' id qr.waitee ∧ otherOwnersPreserved h h' qr.waitee) ∧
  (∀ (h : Heap α) (qr : ILLRef α),
    qr.list.tail = none → popWaitEntry ops h qr = some (.error .typeError)) ∧
  (∀ (h : Heap α) (qr : ILLRef α) (id : NodeId),
    waitEntryWellFormed ops h qr.list qr.waitee → id ∈ waitEntryNodes ops h qr.list qr.waitee →
      match deleteWaitEntry ops h qr id with
      | none => False
      | some (.error _) => False
      | some (.ok (h', q')) =>
          waitEntryWellFormed ops h' q' qr.waitee ∧
            waitEntryNodes ops h' q' qr.waitee = (waitEntryNodes ops h qr.list qr.waitee).erase id ∧
            ops.findSlot h' id qr.waitee = 0 ∧ releasedWaitSlot ops h h' id qr.waitee ∧
            otherOwnersPreserved h h' qr.waitee) ∧
  (∀ (h : Heap α) (qr : ILLRef α) (id : NodeId),
    ops.findSlot h id qr.waitee = 0 → deleteWaitEntry ops h qr id = some (.ok (h, qr.list))) ∧
  (∀ (h : Heap α) (qr : ILLRef α),
    waitEntryWellFormed ops h qr.list qr.waitee →
      lengthWaitEntry ops h qr = some (.ok (JuliaLean.JInt.wrap .i64 (Int.ofNat (waitEntryNodes ops h qr.list qr.waitee).length))) ∧
      waitQueueIsEmpty ops h qr =
        some (.ok (!(waitEntryNodes ops h qr.list qr.waitee).any (waitingEntryArmed h))))

theorem intrusiveIsEmptySpec_proven : IntrusiveIsEmptySpec := by
  constructor
  · intro α h q _
    unfold isemptyIntrusive
    unfold intrusiveNodes
    cases q.head <;> rfl
  · intro α qr
    rfl

theorem linkedItemConstructionSpec_proven : LinkedItemConstructionSpec := by
  intro α h value fresh
  have hfind : h.nodes.find? (fun entry => entry.1 == h.nextNode) = none := by
    simpa [Heap.node?] using fresh
  have hfilter : h.nodes.filter (fun entry => entry.1 != h.nextNode) = h.nodes := by
    apply List.filter_eq_self.2
    intro entry he
    have hneq : (entry.1 == h.nextNode) = false := by
      cases hbeq : (entry.1 == h.nextNode) with
      | false => rfl
      | true =>
          exact False.elim ((List.find?_eq_none.mp hfind) entry he hbeq)
    have hne : entry.1 ≠ h.nextNode := by
      intro heq
      have hbeq : (entry.1 == h.nextNode) = true := by simp [heq]
      rw [hbeq] at hneq
      contradiction
    simpa using hne
  simp [newLinkedListItem, Heap.allocateNode, Heap.setNode, Heap.node?,
    List.find?_append, hfilter, hfind]

/-! Nothing to promise:
waitqueue@17: this declares a generic function; concrete waitee types supply methods elsewhere.
eltype@22: the concrete type or Any result is its complete behavior and is mirrored directly.
eltype@162: the concrete type or Any result is its complete behavior and is mirrored directly.
-/

end JuliaLean.Proofs.base.linked_list


/-! Group 24: checked linked-list results and reusable finite-chain facts. -/
namespace JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean.base.linked_list JuliaLean.Proofs.base.linked_list
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


/-- Resolve a private model declaration by its existing kernel name. -/
macro "llPrivateConst% " id:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.linked_list id.getId))

abbrev llNodeLinks {α : Type} : Heap α → Option NodeId → Nat → List NodeId :=
  llPrivateConst% JuliaLean.base.linked_list.nodeLinks
abbrev llLookup {α : Type} : Heap α → NodeId → Except ListFailure (HeapNode α) :=
  llPrivateConst% JuliaLean.base.linked_list.lookupNode
abbrev llNodeNext {α : Type} : Heap α → NodeId → Option NodeId :=
  llPrivateConst% JuliaLean.base.linked_list.nodeNext
abbrev llLengthLoop {α : Type} : Heap α → JuliaLean.JInt .i64 → Option NodeId →
    ExceptT ListFailure Option (JuliaLean.JInt .i64) :=
  llPrivateConst% JuliaLean.base.linked_list.lengthIntrusiveLoop
abbrev llValuesLoop {α : Type} : Heap α → Option NodeId → List α →
    ExceptT ListFailure Option (List α) :=
  llPrivateConst% JuliaLean.base.linked_list.linkedValuesLoop
abbrev llIterationLoop {α : Type} : Heap α → InvasiveLinkedList α → Nat →
    Option NodeId → Except ListFailure (List NodeId) :=
  llPrivateConst% JuliaLean.base.linked_list.intrusiveIterationLoop
abbrev llBoxedIterationLoop {α : Type} : Heap α → LinkedList α → Nat →
    Option NodeId → Except ListFailure (List α) :=
  llPrivateConst% JuliaLean.base.linked_list.linkedIterationLoop

theorem llLookup_eq {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) : llLookup h id = .ok node := by
  change (match h.node? id with | some n => Except.ok n | none => Except.error ListFailure.missingNode) = Except.ok node
  rw [lookup]

theorem llNodeNext_eq {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) : llNodeNext h id = node.next := by
  change ((h.node? id).map HeapNode.next).join = _
  rw [lookup]
  rfl

theorem llNodeLinks_zero {α : Type} (h : Heap α) (head : Option NodeId) :
    llNodeLinks h head 0 = [] := rfl

theorem llNodeLinks_none {α : Type} (h : Heap α) (fuel : Nat) :
    llNodeLinks h none fuel = [] := by cases fuel <;> rfl

theorem llNodeLinks_some {α : Type} (h : Heap α) (id : NodeId) (fuel : Nat) :
    llNodeLinks h (some id) (fuel + 1) = id :: llNodeLinks h (llNodeNext h id) fuel := rfl

/-- A finite chain records the actual heap lookup at every link. -/
inductive LLChain {α : Type} (h : Heap α) : Option NodeId → List NodeId → Prop
  | nil : LLChain h none []
  | cons {id : NodeId} {node : HeapNode α} {ids : List NodeId}
      (lookup : h.node? id = some node) (rest : LLChain h node.next ids) :
      LLChain h (some id) (id :: ids)

/-- Every identity in a certified finite chain has a heap node. -/
theorem llChain_lookup {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} (chain : LLChain h head ids) :
    ∀ id ∈ ids, ∃ node, h.node? id = some node := by
  induction chain with
  | nil => intro id member; cases member
  | @cons id node ids lookup rest ih =>
      intro target member
      rcases List.mem_cons.mp member with equal | member
      · subst target
        exact ⟨node, lookup⟩
      · exact ih target member

/-- Two finite chains beginning at the same heap link agree. -/
theorem llChain_unique {α : Type} {h : Heap α} {head : Option NodeId}
    {ids other : List NodeId} (chain : LLChain h head ids)
    (otherChain : LLChain h head other) : ids = other := by
  induction chain generalizing other with
  | nil => cases otherChain; rfl
  | @cons id node ids lookup rest ih =>
      cases otherChain with
      | cons lookup' rest' =>
          have equal := Option.some.inj (lookup.symm.trans lookup')
          subst equal
          exact congrArg (List.cons id) (ih rest')

/-- No two differently owned well-formed lists share an identity. -/
theorem llDistinctOwnersDisjoint {α : Type} {h : Heap α}
    {q r : InvasiveLinkedList α} (different : q.id ≠ r.id)
    (wellQ : intrusiveWellFormed h q) (wellR : intrusiveWellFormed h r) :
    ∀ id, id ∈ intrusiveNodes h q → id ∉ intrusiveNodes h r := by
  intro id inQ inR
  rcases wellQ.2.2.2.2.1 id inQ with ⟨node, lookup, owner⟩
  rcases wellR.2.2.2.2.1 id inR with ⟨other, lookup', owner'⟩
  have equal := Option.some.inj (lookup.symm.trans lookup')
  subst other
  exact different (Option.some.inj (owner.symm.trans owner'))

/-- A present heap identity occurs in the heap's key sequence. -/
theorem llLookup_keyMember {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) : id ∈ h.nodes.map Prod.fst := by
  unfold Heap.node? at lookup
  cases found : h.nodes.find? (fun entry => entry.1 == id) with
  | none => simp only [found, Option.map_none] at lookup; contradiction
  | some pair =>
      have member := List.mem_of_find?_eq_some found
      have key := List.find?_some found
      have equal : pair.1 = id := by simpa only [beq_iff_eq] using key
      exact List.mem_map.mpr ⟨pair, member, equal⟩

/-- A unique sequence of present identities is no longer than the heap. -/
theorem llIdentityLengthBound {α : Type} {h : Heap α} {ids : List NodeId}
    (unique : ids.Nodup) (present : ∀ id ∈ ids, ∃ node, h.node? id = some node) :
    ids.length ≤ h.nodes.length := by
  have bound := unique.length_le_of_subset (l₂ := h.nodes.map Prod.fst) (by
    intro id member
    rcases present id member with ⟨node, lookup⟩
    exact llLookup_keyMember lookup)
  simpa only [List.length_map] using bound

/-- A bounded traversal with spare fuel certifies a full finite chain. -/
theorem llNodeLinks_chain {α : Type} (h : Heap α) (head : Option NodeId) (fuel : Nat)
    (short : (llNodeLinks h head fuel).length < fuel)
    (present : ∀ id ∈ llNodeLinks h head fuel, ∃ node, h.node? id = some node) :
    LLChain h head (llNodeLinks h head fuel) := by
  induction fuel generalizing head with
  | zero => omega
  | succ fuel ih =>
      cases head with
      | none => simpa only [llNodeLinks_none] using LLChain.nil (h := h)
      | some id =>
          rw [llNodeLinks_some] at short present ⊢
          obtain ⟨node, lookup⟩ := present id (by simp only [List.mem_cons, true_or])
          rw [llNodeNext_eq lookup] at short present ⊢
          apply LLChain.cons lookup
          apply ih
          · simpa only [List.length_cons, Nat.add_lt_add_iff_right] using short
          · intro other member
            exact present other (List.mem_cons_of_mem id member)

/-- Well-formedness gives a terminating chain of all observed identities. -/
theorem llWellFormed_chain {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} (well : intrusiveWellFormedFor h q owner) :
    LLChain h q.head (intrusiveNodes h q) := by
  have present : ∀ id ∈ intrusiveNodes h q, ∃ node, h.node? id = some node := by
    intro id member
    obtain ⟨node, lookup, _⟩ := well.2.2.2.2.1 id member
    exact ⟨node, lookup⟩
  apply llNodeLinks_chain
  · have bound := llIdentityLengthBound well.2.2.1 present
    exact Nat.lt_succ_of_le bound
  · exact present

/-- The observed identity sequence of a well-formed list fits in the heap. -/
theorem llWellFormed_length {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} (well : intrusiveWellFormedFor h q owner) :
    (intrusiveNodes h q).length ≤ h.nodes.length :=
  llIdentityLengthBound well.2.2.1 (llChain_lookup (llWellFormed_chain well))


abbrev llIntrusiveItem {α : Type} (h : Heap α) (q : InvasiveLinkedList α)
    (state : Option NodeId) : Except ListFailure (Option (NodeId × NodeId)) :=
  match state with
  | none => pure (iterateIntrusiveStart q)
  | some id => iterateIntrusiveNext h id

theorem llIterationLoop_succ {α : Type} (h : Heap α) (q : InvasiveLinkedList α)
    (fuel : Nat) (state : Option NodeId) :
    llIterationLoop h q (fuel + 1) state = (do
      let item ← llIntrusiveItem h q state
      match item with
      | none => pure []
      | some (value, nextState) =>
          let rest ← llIterationLoop h q fuel (some nextState)
          pure (value :: rest)) := by
  cases state with
  | none => exact (llPrivateConst% JuliaLean.base.linked_list.intrusiveIterationLoop.eq_def) h q (fuel + 1) none
  | some id => exact (llPrivateConst% JuliaLean.base.linked_list.intrusiveIterationLoop.eq_def) h q (fuel + 1) (some id)

/-- A finite heap chain is enumerated by the installed iterator in link order. -/
theorem llIteration_chain {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} (chain : LLChain h head ids) (q : InvasiveLinkedList α)
    (fuel : Nat) (state : Option NodeId) (enough : ids.length < fuel)
    (item : llIntrusiveItem h q state = .ok (head.map (fun id => (id, id)))) :
    llIterationLoop h q fuel state = .ok ids := by
  induction chain generalizing fuel state with
  | nil =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [llIterationLoop_succ, item]
          rfl
  | @cons id node ids lookup rest ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have nextItem : llIntrusiveItem h q (some id) =
              .ok (node.next.map (fun id => (id, id))) := by
            change iterateIntrusiveNext h id = _
            change (llLookup h id).bind (fun current =>
              Except.ok (current.next.map (fun next => (next, next)))) = _
            rw [llLookup_eq lookup]
            rfl
          have nextRun := ih fuel (some id) (by simpa only [List.length_cons,
            Nat.add_lt_add_iff_right] using enough) nextItem
          rw [llIterationLoop_succ, item]
          simp only [Option.map_some, bind, Except.bind, pure, Except.pure, nextRun]

theorem LinkedListIntrusiveIterate : JuliaLean.Proofs.base.linked_list.IntrusiveIterationSpec := by
  intro α h q well
  apply llIteration_chain (llWellFormed_chain well) q (h.nodes.length + 1) none
  · exact Nat.lt_succ_of_le (llWellFormed_length well)
  · change Except.ok (iterateIntrusiveStart q) = _
    unfold iterateIntrusiveStart
    cases q.head <;> rfl



/-- Enough traversal fuel reproduces any finite certified chain. -/
theorem llChain_nodeLinks {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} (chain : LLChain h head ids) (fuel : Nat) (enough : ids.length ≤ fuel) :
    llNodeLinks h head fuel = ids := by
  induction chain generalizing fuel with
  | nil => exact llNodeLinks_none h fuel
  | @cons id node ids lookup rest ih =>
      cases fuel with
      | zero => simp only [List.length_cons] at enough; omega
      | succ fuel =>
          rw [llNodeLinks_some, llNodeNext_eq lookup]
          exact congrArg (List.cons id) (ih fuel (by simpa only [List.length_cons,
            Nat.add_le_add_iff_right] using enough))

theorem llChain_observed {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {ids : List NodeId} (chain : LLChain h q.head ids) (unique : ids.Nodup) :
    intrusiveNodes h q = ids := by
  apply llChain_nodeLinks chain
  have bound := llIdentityLengthBound unique (llChain_lookup chain)
  exact Nat.le_trans bound (Nat.le_succ _)

/-- Updating one heap entry leaves every other lookup unchanged. -/
theorem llSetNode_other {α : Type} (h : Heap α) (id other : NodeId) (node : HeapNode α)
    (different : other ≠ id) : (h.setNode id node).node? other = h.node? other := by
  have predicate : (fun entry : NodeId × HeapNode α => decide ((entry.1 != id) = true ∧ (entry.1 == other) = true)) =
      (fun entry : NodeId × HeapNode α => entry.1 == other) := by
    funext entry
    by_cases equal : entry.1 = other
    · simp [equal, different]
    · simp [equal]
  simp only [Heap.node?, Heap.setNode, List.find?_append, List.find?_filter]
  rw [predicate]
  simp [different, Ne.symm different]

theorem llSetNode_self {α : Type} (h : Heap α) (id : NodeId) (node : HeapNode α) :
    (h.setNode id node).node? id = some node := by
  have predicate : (fun entry : NodeId × HeapNode α => decide ((entry.1 != id) = true ∧ (entry.1 == id) = true)) =
      (fun _ : NodeId × HeapNode α => false) := by
    funext entry
    simp
  simp only [Heap.node?, Heap.setNode, List.find?_append, List.find?_filter]
  rw [predicate]
  have noFind : h.nodes.find? (fun _ => false) = none := by
    apply List.find?_eq_none.mpr
    intro entry member
    simp
  simp [noFind]

theorem llSetNode_keys {α : Type} (h : Heap α) (id : NodeId) (node : HeapNode α) :
    (h.setNode id node).nodes.map Prod.fst =
      (h.nodes.map Prod.fst).filter (fun other => other != id) ++ [id] := by
  simp only [Heap.setNode, List.map_append, List.map_cons, List.map_nil, List.filter_map,
    Function.comp_def]

theorem llSetNode_unique {α : Type} {h : Heap α}
    (unique : (h.nodes.map Prod.fst).Nodup) (id : NodeId) (node : HeapNode α) :
    ((h.setNode id node).nodes.map Prod.fst).Nodup := by
  rw [llSetNode_keys, List.nodup_append]
  refine ⟨List.Pairwise.filter _ unique, by simp, ?_⟩
  intro left leftMember right rightMember
  have rightEqual : right = id := by simpa only [List.mem_singleton] using rightMember
  subst right
  simpa only [bne_iff_ne] using (List.mem_filter.mp leftMember).2

/-- A chain is preserved by any heap change preserving its node lookups. -/
theorem llChain_transport {α : Type} {h h' : Heap α} {head : Option NodeId}
    {ids : List NodeId} (chain : LLChain h head ids)
    (preserved : ∀ id ∈ ids, h'.node? id = h.node? id) : LLChain h' head ids := by
  induction chain with
  | nil => exact .nil
  | @cons id node ids lookup rest ih =>
      apply LLChain.cons ((preserved id (List.mem_cons_self ..)).trans lookup)
      exact ih (fun other member => preserved other (List.mem_cons_of_mem id member))

/-- The detached node is absent from a well-formed owned chain. -/
theorem llDetached_notMember {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} (well : intrusiveWellFormedFor h q owner) {id : NodeId}
    (detached : detachedNode h id) : id ∉ intrusiveNodes h q := by
  intro member
  obtain ⟨node, lookup, _, noOwner⟩ := detached
  obtain ⟨owned, lookup', ownerEq⟩ := well.2.2.2.2.1 id member
  have equal := Option.some.inj (lookup.symm.trans lookup')
  subst owned
  rw [noOwner] at ownerEq
  contradiction

/-- A finite owned chain and the heap owner correspondence give the installed invariant. -/
theorem llBuildWellFormed {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} {ids : List NodeId}
    (heapUnique : (h.nodes.map Prod.fst).Nodup)
    (endpoints : q.head.isNone ↔ q.tail.isNone)
    (chain : LLChain h q.head ids) (unique : ids.Nodup) (last : ids.getLast? = q.tail)
    (owners : ∀ id ∈ ids, ∃ node, h.node? id = some node ∧ node.queue = some owner)
    (allOwners : ∀ id node, (id, node) ∈ h.nodes → node.queue = some owner → id ∈ ids) :
    intrusiveWellFormedFor h q owner := by
  have observed := llChain_observed chain unique
  unfold intrusiveWellFormedFor
  rw [observed]
  exact ⟨heapUnique, endpoints, unique, last, owners, allOwners⟩


/-- Small witness for the missing detached-next premise in the action-sequence statement. -/
def llStaleNextHeap : Heap Unit :=
  ⟨[(0, ⟨some 1, none, (), [], none⟩), (1, ⟨none, some 1, (), [], none⟩)], 2, 2, []⟩

def llStaleNextList : InvasiveLinkedList Unit := ⟨0, none, none⟩

def llStaleNextHeapAfter : Heap Unit :=
  ⟨[(1, ⟨none, some 1, (), [], none⟩), (0, ⟨some 1, some 0, (), [], none⟩)], 2, 2, []⟩

def llStaleNextListAfter : InvasiveLinkedList Unit := ⟨0, some 0, some 0⟩

theorem llStaleNext_initial : intrusiveWellFormed llStaleNextHeap llStaleNextList := by
  refine ⟨by decide, by decide, by decide, rfl, ?_, ?_⟩
  · intro id member
    have empty : intrusiveNodes llStaleNextHeap llStaleNextList = [] := rfl
    rw [empty] at member
    cases member
  · intro id node member owned
    simp only [llStaleNextHeap, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with equal | equal
    · cases equal
      contradiction
    · cases equal
      contradiction

theorem llStaleNext_action :
    runIntrusiveActions llStaleNextHeap llStaleNextList [.push 0] =
      some (.ok (llStaleNextHeapAfter, llStaleNextListAfter)) := rfl

theorem llStaleNext_tailMismatch :
    (intrusiveNodes llStaleNextHeapAfter llStaleNextListAfter).getLast? ≠
      llStaleNextListAfter.tail := by decide


abbrev llSetNodeField {α : Type} : Heap α → NodeId → (HeapNode α → HeapNode α) →
    Except ListFailure (Heap α) :=
  llPrivateConst% JuliaLean.base.linked_list.setNodeField

theorem llSetNodeField_eq {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) (update : HeapNode α → HeapNode α) :
    llSetNodeField h id update = .ok (h.setNode id (update node)) := by
  change (llLookup h id).bind (fun current => Except.ok (h.setNode id (update current))) = _
  rw [llLookup_eq lookup]
  rfl

theorem llSetNode_overwrite {α : Type} (h : Heap α) (id : NodeId) (first last : HeapNode α) :
    (h.setNode id first).setNode id last = h.setNode id last := by
  simp [Heap.setNode, List.filter_append, List.filter_filter]

abbrev llPrependHeap {α : Type} (h : Heap α) (q : InvasiveLinkedList α)
    (owner : OwnerId) (id : NodeId) (node : HeapNode α) : Heap α :=
  h.setNode id { node with next := q.head, queue := some owner }

abbrev llPrependList {α : Type} (q : InvasiveLinkedList α) (id : NodeId) : InvasiveLinkedList α :=
  { q with head := some id, tail := if q.head.isNone then some id else q.tail }

/-- The source prepend executes as one update of the inserted node and the endpoints. -/
theorem llPushfirst_run {α : Type} {h : Heap α} (qr : ILLRef α) {id : NodeId}
    {node : HeapNode α} (lookup : h.node? id = some node)
    (noNext : node.next = none) (noOwner : node.queue = none) :
    pushfirstILLRef h qr id =
      .ok (llPrependHeap h qr.list qr.waitee id node, llPrependList qr.list id) := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  cases head : qr.list.head with
  | none =>
      simp [pushfirstILLRef, lookup', noOwner, head, llPrependHeap, llPrependList, noNext,
        bind, Except.bind, pure, Except.pure]
  | some first =>
      have update := llSetNodeField_eq
        (llSetNode_self h id {node with queue := some qr.waitee})
        (fun current => {current with next := some first})
      simp only [llSetNodeField] at update
      simp [pushfirstILLRef, lookup', noOwner, head, update,
        llPrependHeap, llPrependList, llSetNode_overwrite, bind, Except.bind, pure, Except.pure,
        Functor.map, Except.map]

/-- Heap entries after one update either predate it or are the new entry. -/
theorem llSetNode_member {α : Type} {h : Heap α} {key id : NodeId} {node changed : HeapNode α}
    (member : (key, node) ∈ (h.setNode id changed).nodes) :
    ((key, node) ∈ h.nodes ∧ key ≠ id) ∨ (key = id ∧ node = changed) := by
  simp only [Heap.setNode, List.mem_append, List.mem_filter, List.mem_singleton,
    bne_iff_ne, Prod.mk.injEq] at member
  exact member

/-- Prepending a detached node preserves the complete owned-chain invariant. -/
theorem llPrepend_wellFormed {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} {id : NodeId} {node : HeapNode α}
    (well : intrusiveWellFormedFor h q owner) (lookup : h.node? id = some node)
    (noNext : node.next = none) (noOwner : node.queue = none) :
    intrusiveWellFormedFor (llPrependHeap h q owner id node) (llPrependList q id) owner ∧
      intrusiveNodes (llPrependHeap h q owner id node) (llPrependList q id) =
        id :: intrusiveNodes h q := by
  let ids := intrusiveNodes h q
  have detached : detachedNode h id := ⟨node, lookup, noNext, noOwner⟩
  have absent : id ∉ ids := llDetached_notMember well detached
  have unique : (id :: ids).Nodup := List.nodup_cons.mpr ⟨absent, well.2.2.1⟩
  have oldChain : LLChain (llPrependHeap h q owner id node) q.head ids := by
    apply llChain_transport (llWellFormed_chain well)
    intro other member
    apply llSetNode_other
    intro equal
    exact absent (equal ▸ member)
  have chain : LLChain (llPrependHeap h q owner id node)
      (llPrependList q id).head (id :: ids) :=
    .cons (llSetNode_self h id {node with next := q.head, queue := some owner}) oldChain
  have observed := llChain_observed chain unique
  refine ⟨?_, observed⟩
  apply llBuildWellFormed (llSetNode_unique well.1 id _) ?_ chain unique ?_ ?_ ?_
  · simp only [llPrependList, Option.isNone_some, Bool.false_eq_true]
    cases head : q.head with
    | none => simp [head]
    | some first =>
        have tailNonempty : q.tail.isNone = false := by
          have link := well.2.1
          simpa only [head, Option.isNone_some, Bool.false_eq_true, false_iff,
            Bool.not_eq_true] using link
        simp [head, tailNonempty]
  · change (id :: ids).getLast? = if q.head.isNone then some id else q.tail
    cases head : q.head with
    | none =>
        have empty : ids = [] := by
          change llNodeLinks h q.head (h.nodes.length + 1) = []
          rw [head, llNodeLinks_none]
        simp [empty, head]
    | some first =>
        have nonempty : ids ≠ [] := by
          change llNodeLinks h q.head (h.nodes.length + 1) ≠ []
          rw [head, llNodeLinks_some]
          exact List.cons_ne_nil _ _
        simpa only [head, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
          List.getLast?_cons_of_ne_nil nonempty] using well.2.2.2.1
  · intro other member
    rcases List.mem_cons.mp member with equal | member
    · subst other
      exact ⟨_, llSetNode_self h id _, rfl⟩
    · obtain ⟨old, lookupOld, ownerOld⟩ := well.2.2.2.2.1 other member
      refine ⟨old, ?_, ownerOld⟩
      rw [llSetNode_other]
      · exact lookupOld
      · intro equal
        exact absent (equal ▸ member)
  · intro other current member owns
    rcases llSetNode_member member with ⟨oldMember, _⟩ | ⟨equal, _⟩
    · exact List.mem_cons_of_mem id (well.2.2.2.2.2 other current oldMember owns)
    · exact List.mem_cons.mpr (Or.inl equal)

/-- Int64 residue equality determines the wrapped integer. -/
theorem llWrapCongr64 {a b : Int}
    (congruent : a % (18446744073709551616 : Int) = b % 18446744073709551616) :
    JuliaLean.wrapInt .i64 a = JuliaLean.wrapInt .i64 b := by
  simp only [JuliaLean.wrapInt, JuliaLean.IntTy.signed, JuliaLean.IntTy.bits] at *
  simp at *
  omega

theorem llWrapMod64 (a : Int) :
    JuliaLean.wrapInt .i64 a % (18446744073709551616 : Int) = a % 18446744073709551616 := by
  simp only [JuliaLean.wrapInt, JuliaLean.IntTy.signed, JuliaLean.IntTy.bits]
  simp

theorem llWrapAddLeft64 (a b : Int) :
    JuliaLean.wrapInt .i64 (JuliaLean.wrapInt .i64 a + b) = JuliaLean.wrapInt .i64 (a + b) := by
  apply llWrapCongr64
  rw [Int.add_emod, llWrapMod64, ← Int.add_emod]

theorem llWrapAddRight64 (a b : Int) :
    JuliaLean.wrapInt .i64 (a + JuliaLean.wrapInt .i64 b) = JuliaLean.wrapInt .i64 (a + b) := by
  apply llWrapCongr64
  rw [Int.add_emod, llWrapMod64, ← Int.add_emod]

theorem llToJInt_ofInt64 (a : Int) :
    (JuliaLean.C.toJInt .i64 (BitVec.ofInt 64 a)).val = JuliaLean.wrapInt .i64 a := by
  change JuliaLean.wrapInt .i64 (BitVec.ofInt 64 a).toInt = JuliaLean.wrapInt .i64 a
  apply llWrapCongr64
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_emod

theorem llAddWrapped64 (a b : Int) :
    JuliaLean.base.int.add (JuliaLean.JInt.wrap .i64 a) (JuliaLean.JInt.wrap .i64 b) =
      JuliaLean.JInt.wrap .i64 (a + b) := by
  apply Subtype.ext
  simp only [JuliaLean.base.int.add, JuliaLean.base.int.add_int,
    JuliaLean.C.jlAddInt, JuliaLean.C.fromJInt]
  rw [← BitVec.ofInt_add]
  change (JuliaLean.C.toJInt .i64 (BitVec.ofInt 64
    (JuliaLean.wrapInt .i64 a + JuliaLean.wrapInt .i64 b))).val = JuliaLean.wrapInt .i64 (a + b)
  rw [llToJInt_ofInt64]
  exact (llWrapAddLeft64 a (JuliaLean.wrapInt .i64 b)).trans (llWrapAddRight64 a b)

theorem llLengthLoop_none {α : Type} (h : Heap α) (count : JuliaLean.JInt .i64) :
    llLengthLoop h count none = some (.ok count) :=
  (llPrivateConst% JuliaLean.base.linked_list.lengthIntrusiveLoop.eq_1) h count

theorem llLengthLoop_some {α : Type} {h : Heap α} {id : NodeId}
    {node : HeapNode α} (lookup : h.node? id = some node) (count : JuliaLean.JInt .i64) :
    llLengthLoop h count (some id) =
      llLengthLoop h (JuliaLean.base.int.add count (JuliaLean.JInt.wrap .i64 1)) node.next := by
  have equation := (llPrivateConst% JuliaLean.base.linked_list.lengthIntrusiveLoop.eq_def)
    h count (some id)
  change llLengthLoop h count (some id) =
    (ExceptT.mk (some (llLookup h id)) >>= fun current =>
      llLengthLoop h (JuliaLean.base.int.add count (JuliaLean.JInt.wrap .i64 1)) current.next) at equation
  rw [llLookup_eq lookup] at equation
  exact equation

/-- The source's unbounded loop terminates on a finite chain and counts modulo Int64. -/
theorem llLength_chain {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} (chain : LLChain h head ids) (count : Int) :
    llLengthLoop h (JuliaLean.JInt.wrap .i64 count) head =
      some (.ok (JuliaLean.JInt.wrap .i64 (count + Int.ofNat ids.length))) := by
  induction chain generalizing count with
  | nil => simpa only [List.length_nil, Int.ofNat_eq_natCast, Int.natCast_zero, Int.add_zero] using
      llLengthLoop_none h (JuliaLean.JInt.wrap .i64 count)
  | @cons id node ids lookup rest ih =>
      rw [llLengthLoop_some lookup, llAddWrapped64, ih]
      congr 3
      simp only [List.length_cons, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
      omega

theorem LinkedListIntrusiveLength : JuliaLean.Proofs.base.linked_list.IntrusiveLengthSpec := by
  constructor
  · intro α h q well
    simpa only [Int.zero_add, lengthIntrusive, llLengthLoop] using
      llLength_chain (llWellFormed_chain well) 0
  · intro α h qr
    rfl


/-- A finite chain with its payload observations. -/
inductive LLValueChain {α : Type} (h : Heap α) : Option NodeId → List NodeId → List α → Prop
  | nil : LLValueChain h none [] []
  | cons {id : NodeId} {node : HeapNode α} {ids : List NodeId} {values : List α}
      (lookup : h.node? id = some node) (rest : LLValueChain h node.next ids values) :
      LLValueChain h (some id) (id :: ids) (node.value :: values)

theorem llChain_hasValues {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} (chain : LLChain h head ids) :
    ∃ values, LLValueChain h head ids values := by
  induction chain with
  | nil => exact ⟨[], .nil⟩
  | cons lookup rest ih =>
      obtain ⟨values, valueChain⟩ := ih
      exact ⟨_, .cons lookup valueChain⟩

theorem llValueChain_length {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} {values : List α} (chain : LLValueChain h head ids values) :
    values.length = ids.length := by
  induction chain with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem llValuesLoop_none {α : Type} (h : Heap α) (reversed : List α) :
    llValuesLoop h none reversed = some (.ok reversed.reverse) :=
  (llPrivateConst% JuliaLean.base.linked_list.linkedValuesLoop.eq_1) h reversed

theorem llValuesLoop_some {α : Type} {h : Heap α} {id : NodeId}
    {node : HeapNode α} (lookup : h.node? id = some node) (reversed : List α) :
    llValuesLoop h (some id) reversed = llValuesLoop h node.next (node.value :: reversed) := by
  have equation := (llPrivateConst% JuliaLean.base.linked_list.linkedValuesLoop.eq_def)
    h (some id) reversed
  change llValuesLoop h (some id) reversed =
    (ExceptT.mk (some (llLookup h id)) >>= fun current =>
      llValuesLoop h current.next (current.value :: reversed)) at equation
  rw [llLookup_eq lookup] at equation
  exact equation

/-- The unbounded value collector agrees with the finite chain. -/
theorem llValues_chain {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} {values : List α} (chain : LLValueChain h head ids values)
    (reversed : List α) :
    llValuesLoop h head reversed = some (.ok (reversed.reverse ++ values)) := by
  induction chain generalizing reversed with
  | nil => simpa only [List.append_nil] using llValuesLoop_none h reversed
  | cons lookup rest ih =>
      rw [llValuesLoop_some lookup, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Successful boxed observations have exactly one value per identity. -/
theorem llLinkedValues_length {α : Type} {h : Heap α} {q : LinkedList α}
    {values : List α} (well : intrusiveWellFormed h q)
    (observed : linkedValues h q = some (.ok values)) :
    values.length = (intrusiveNodes h q).length := by
  obtain ⟨chainValues, chain⟩ := llChain_hasValues (llWellFormed_chain well)
  have run : linkedValues h q = some (.ok chainValues) := by
    simpa only [linkedValues, llValuesLoop, List.reverse_nil, List.nil_append] using llValues_chain chain []
  have equal : values = chainValues := Except.ok.inj (Option.some.inj (observed.symm.trans run))
  rw [equal]
  exact llValueChain_length chain

theorem LinkedListBoxedIsempty : JuliaLean.Proofs.base.linked_list.LinkedIsEmptySpec := by
  intro α h q values well observed
  rw [intrusiveIsEmptySpec_proven.1 h q well]
  have lengthEqual := llLinkedValues_length well observed
  simp only [← List.length_eq_zero_iff, lengthEqual]

theorem LinkedListBoxedLength : JuliaLean.Proofs.base.linked_list.LinkedLengthSpec := by
  intro α h q values well observed
  rw [llLinkedValues_length well observed]
  exact LinkedListIntrusiveLength.1 h q well

theorem listCountWrap_exact (n : Nat) (fits : Int.ofNat n ≤ JuliaLean.IntTy.max .i64) :
    (JuliaLean.JInt.wrap .i64 (Int.ofNat n)).val = Int.ofNat n := by
  exact JuliaLean.wrapInt_of_inRange .i64 (Int.ofNat n)
    ⟨Int.le_trans (by decide : JuliaLean.IntTy.min .i64 ≤ 0) (Int.ofNat_nonneg n), fits⟩

theorem intrusiveLengthSourceSpec_proven :
    JuliaLean.Proofs.base.linked_list.IntrusiveLengthSourceSpec := by
  refine ⟨LinkedListIntrusiveLength, ?_⟩
  intro α h q well fits
  exact ⟨_, LinkedListIntrusiveLength.1 h q well, listCountWrap_exact _ fits⟩

theorem linkedLengthSourceSpec_proven :
    JuliaLean.Proofs.base.linked_list.LinkedLengthSourceSpec := by
  refine ⟨LinkedListBoxedLength, ?_⟩
  intro α h q values well observed fits
  exact ⟨_, LinkedListBoxedLength h q values well observed, listCountWrap_exact _ fits⟩


/-- Already owned nodes are rejected before any intrusive append. -/
theorem llPushQueued {α : Type} {h : Heap α} (qr : ILLRef α) {id : NodeId}
    {node : HeapNode α} (lookup : h.node? id = some node) (queued : node.queue.isSome) :
    pushILLRef h qr id = .error .alreadyQueued := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  simp [pushILLRef, lookup', queued, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw]

theorem llPushIntrusiveQueued {α : Type} {h : Heap α} (q : InvasiveLinkedList α) {id : NodeId}
    {node : HeapNode α} (lookup : h.node? id = some node) (queued : node.queue.isSome) :
    pushIntrusive h q id = .error .alreadyQueued := by
  simp only [pushIntrusive, llPushQueued ⟨q, q.id⟩ lookup queued]

/-- Already owned nodes are rejected before any intrusive prepend. -/
theorem llPushfirstQueued {α : Type} {h : Heap α} (qr : ILLRef α) {id : NodeId}
    {node : HeapNode α} (lookup : h.node? id = some node) (queued : node.queue.isSome) :
    pushfirstILLRef h qr id = .error .alreadyQueued := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  simp [pushfirstILLRef, lookup', queued, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw]

theorem llPushfirstIntrusiveQueued {α : Type} {h : Heap α} (q : InvasiveLinkedList α) {id : NodeId}
    {node : HeapNode α} (lookup : h.node? id = some node) (queued : node.queue.isSome) :
    pushfirstIntrusive h q id = .error .alreadyQueued := by
  simp only [pushfirstIntrusive, llPushfirstQueued ⟨q, q.id⟩ lookup queued]

theorem llPopEmpty {α : Type} (h : Heap α) (qr : ILLRef α) (empty : qr.list.tail = none) :
    popILLRef h qr = some (.error .typeError) := by
  simp only [popILLRef, empty]
  rfl

theorem llPopfirstEmpty {α : Type} (h : Heap α) (qr : ILLRef α) (empty : qr.list.head = none) :
    popfirstILLRef h qr = some (.error .typeError) := by
  simp only [popfirstILLRef, empty]
  rfl

theorem llPopLinkedEmpty {α : Type} (h : Heap α) (q : LinkedList α) (empty : q.tail = none) :
    popLinked h q = some (.error .typeError) := by
  simp only [popLinked, popIntrusive, llPopEmpty h ⟨q, q.id⟩ empty]
  rfl

theorem llPopfirstLinkedEmpty {α : Type} (h : Heap α) (q : LinkedList α) (empty : q.head = none) :
    popfirstLinked h q = some (.error .typeError) := by
  simp only [popfirstLinked, popfirstIntrusive, llPopfirstEmpty h ⟨q, q.id⟩ empty]
  rfl


abbrev llHeadObservation {α : Type} (h : Heap α) (head : Option NodeId) :
    Except ListFailure (Option (α × NodeId)) :=
  match head with
  | none => pure none
  | some id => do
      let node ← llLookup h id
      pure (some (node.value, id))

abbrev llBoxedItem {α : Type} (h : Heap α) (q : LinkedList α)
    (state : Option NodeId) : Except ListFailure (Option (α × NodeId)) :=
  match state with
  | none => iterateLinkedStart h q
  | some id => iterateLinkedNext h id

theorem llBoxedHead_some {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) :
    llHeadObservation h (some id) = .ok (some (node.value, id)) := by
  change (llLookup h id).bind (fun current => Except.ok (some (current.value, id))) = _
  rw [llLookup_eq lookup]
  rfl

theorem llBoxedNext_eq {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) :
    iterateLinkedNext h id = llHeadObservation h node.next := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  simp only [iterateLinkedNext, lookup', bind, Except.bind, llHeadObservation, llLookup]
  cases node.next <;> rfl

theorem llBoxedIterationLoop_succ {α : Type} (h : Heap α) (q : LinkedList α)
    (fuel : Nat) (state : Option NodeId) :
    llBoxedIterationLoop h q (fuel + 1) state = (do
      let item ← llBoxedItem h q state
      match item with
      | none => pure []
      | some (value, nextState) =>
          let rest ← llBoxedIterationLoop h q fuel (some nextState)
          pure (value :: rest)) := by
  cases state with
  | none => exact (llPrivateConst% JuliaLean.base.linked_list.linkedIterationLoop.eq_def) h q (fuel + 1) none
  | some id => exact (llPrivateConst% JuliaLean.base.linked_list.linkedIterationLoop.eq_def) h q (fuel + 1) (some id)

/-- Boxed iteration yields the finite chain's payloads in the same order. -/
theorem llBoxedIteration_chain {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} {values : List α} (chain : LLValueChain h head ids values)
    (q : LinkedList α) (fuel : Nat) (state : Option NodeId) (enough : ids.length < fuel)
    (item : llBoxedItem h q state = llHeadObservation h head) :
    llBoxedIterationLoop h q fuel state = .ok values := by
  induction chain generalizing fuel state with
  | nil =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [llBoxedIterationLoop_succ, item]
          rfl
  | @cons id node ids values lookup rest ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have nextItem : llBoxedItem h q (some id) = llHeadObservation h node.next :=
            llBoxedNext_eq lookup
          have nextRun := ih fuel (some id) (by simpa only [List.length_cons,
            Nat.add_lt_add_iff_right] using enough) nextItem
          rw [llBoxedIterationLoop_succ, item, llBoxedHead_some lookup]
          simp only [bind, Except.bind, pure, Except.pure, nextRun]

theorem LinkedListBoxedIterate : JuliaLean.Proofs.base.linked_list.LinkedIterationSpec := by
  intro α h q values well observed
  obtain ⟨chainValues, chain⟩ := llChain_hasValues (llWellFormed_chain well)
  have run : linkedValues h q = some (.ok chainValues) := by
    simpa only [linkedValues, llValuesLoop, List.reverse_nil, List.nil_append] using llValues_chain chain []
  have equal : values = chainValues := Except.ok.inj (Option.some.inj (observed.symm.trans run))
  rw [equal]
  apply llBoxedIteration_chain chain q (h.nodes.length + 1) none
  · exact Nat.lt_succ_of_le (llWellFormed_length well)
  · change iterateLinkedStart h q = llHeadObservation h q.head
    unfold iterateLinkedStart llHeadObservation llLookup
    cases q.head <;> rfl


theorem LinkedListIntrusivePushfirst : JuliaLean.Proofs.base.linked_list.IntrusivePushFirstSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α h qr id well detached
    obtain ⟨node, lookup, noNext, noOwner⟩ := detached
    rw [llPushfirst_run qr lookup noNext noOwner]
    have result := llPrepend_wellFormed well lookup noNext noOwner
    exact ⟨result.1, result.2, ⟨_, llSetNode_self h id _, rfl⟩⟩
  · intro α h q id well detached
    obtain ⟨node, lookup, noNext, noOwner⟩ := detached
    unfold pushfirstIntrusive
    rw [llPushfirst_run ⟨q, q.id⟩ lookup noNext noOwner]
    have result := llPrepend_wellFormed well lookup noNext noOwner
    exact ⟨result.1, result.2, ⟨_, llSetNode_self h id _, rfl⟩⟩
  · intro α h qr id node lookup queued
    exact llPushfirstQueued qr lookup queued
  · intro α h q id node lookup queued
    exact llPushfirstIntrusiveQueued q lookup queued


theorem llSetNode_length_present {α : Type} {h : Heap α}
    (unique : (h.nodes.map Prod.fst).Nodup) {id : NodeId} {old : HeapNode α}
    (lookup : h.node? id = some old) (node : HeapNode α) :
    (h.setNode id node).nodes.length = h.nodes.length := by
  have member := llLookup_keyMember lookup
  have keyLength : (h.nodes.map Prod.fst).length = h.nodes.length := List.length_map _
  have outputLength : ((h.setNode id node).nodes.map Prod.fst).length =
      (h.setNode id node).nodes.length := List.length_map _
  rw [llSetNode_keys, List.length_append, List.length_singleton,
    ← unique.erase_eq_filter id, List.length_erase_of_mem member, keyLength] at outputLength
  have positive := List.length_pos_of_mem member
  rw [keyLength] at positive
  omega

theorem llValueChain_transport {α : Type} {h h' : Heap α} {head : Option NodeId}
    {ids : List NodeId} {values : List α} (chain : LLValueChain h head ids values)
    (preserved : ∀ id ∈ ids, h'.node? id = h.node? id) :
    LLValueChain h' head ids values := by
  induction chain with
  | nil => exact .nil
  | @cons id node ids values lookup rest ih =>
      apply LLValueChain.cons ((preserved id (List.mem_cons_self ..)).trans lookup)
      exact ih (fun other member => preserved other (List.mem_cons_of_mem id member))

theorem llObservedValueChain {α : Type} {h : Heap α} {q : LinkedList α}
    {values : List α} (well : intrusiveWellFormed h q)
    (observed : linkedValues h q = some (.ok values)) :
    LLValueChain h q.head (intrusiveNodes h q) values := by
  obtain ⟨chainValues, chain⟩ := llChain_hasValues (llWellFormed_chain well)
  have run : linkedValues h q = some (.ok chainValues) := by
    simpa only [linkedValues, llValuesLoop, List.reverse_nil, List.nil_append] using llValues_chain chain []
  have equal : values = chainValues := Except.ok.inj (Option.some.inj (observed.symm.trans run))
  rw [equal]
  exact chain

theorem llValueChain_observed {α : Type} {h : Heap α} {q : LinkedList α}
    {ids : List NodeId} {values : List α} (chain : LLValueChain h q.head ids values) :
    linkedValues h q = some (.ok values) := by
  simpa only [linkedValues, llValuesLoop, List.reverse_nil, List.nil_append] using llValues_chain chain []

abbrev llAllocatedHeap {α : Type} (h : Heap α) (value : α) : Heap α :=
  { (h.setNode h.nextNode ⟨none, none, value, [], none⟩) with nextNode := h.nextNode + 1 }

theorem llAllocate_lookup {α : Type} (h : Heap α) (value : α) :
    (llAllocatedHeap h value).node? h.nextNode = some ⟨none, none, value, [], none⟩ :=
  llSetNode_self h h.nextNode _

theorem llAllocate_other {α : Type} (h : Heap α) (value : α) (id : NodeId)
    (different : id ≠ h.nextNode) : (llAllocatedHeap h value).node? id = h.node? id :=
  llSetNode_other h h.nextNode id _ different

theorem llAllocate_wellFormed {α : Type} {h : Heap α} {q : LinkedList α} (value : α)
    (well : intrusiveWellFormed h q) (fresh : h.node? h.nextNode = none) :
    intrusiveWellFormed (llAllocatedHeap h value) q ∧
      intrusiveNodes (llAllocatedHeap h value) q = intrusiveNodes h q := by
  have freshNotMember : h.nextNode ∉ intrusiveNodes h q := by
    intro member
    obtain ⟨node, lookup⟩ := llChain_lookup (llWellFormed_chain well) h.nextNode member
    rw [fresh] at lookup
    contradiction
  have chain : LLChain (llAllocatedHeap h value) q.head (intrusiveNodes h q) := by
    apply llChain_transport (llWellFormed_chain well)
    intro id member
    apply llAllocate_other
    intro equal
    exact freshNotMember (equal ▸ member)
  have observed := llChain_observed chain well.2.2.1
  refine ⟨?_, observed⟩
  apply llBuildWellFormed (h := llAllocatedHeap h value) (q := q) (owner := q.id)
    (llSetNode_unique well.1 h.nextNode _) well.2.1 chain well.2.2.1 well.2.2.2.1
  · intro id member
    obtain ⟨node, lookup, owner⟩ := well.2.2.2.2.1 id member
    refine ⟨node, ?_, owner⟩
    rw [llAllocate_other]
    · exact lookup
    · intro equal
      exact freshNotMember (equal ▸ member)
  · intro id node member owner
    rcases llSetNode_member member with ⟨oldMember, _⟩ | ⟨_, equal⟩
    · exact well.2.2.2.2.2 id node oldMember owner
    · subst node
      contradiction

theorem llAllocate_length {α : Type} (h : Heap α) (value : α)
    (fresh : h.node? h.nextNode = none) :
    (llAllocatedHeap h value).nodes.length = h.nodes.length + 1 :=
  (linkedItemConstructionSpec_proven h value fresh).1


theorem llPushfirstLinked_run {α : Type} (h : Heap α) (q : LinkedList α) (value : α) :
    pushfirstLinked h q value = .ok
      (llPrependHeap (llAllocatedHeap h value) q q.id h.nextNode ⟨none, none, value, [], none⟩,
        llPrependList q h.nextNode) := by
  unfold pushfirstLinked newLinkedListItem Heap.allocateNode
  change pushfirstIntrusive (llAllocatedHeap h value) q h.nextNode = _
  unfold pushfirstIntrusive
  rw [llPushfirst_run ⟨q, q.id⟩ (llAllocate_lookup h value) rfl rfl]

theorem LinkedListBoxedPushfirst : JuliaLean.Proofs.base.linked_list.LinkedPushFirstSpec := by
  intro α h q values value well observed fresh
  rw [llPushfirstLinked_run]
  have allocated := llAllocate_wellFormed value well fresh
  have prepended := llPrepend_wellFormed allocated.1 (llAllocate_lookup h value) rfl rfl
  have valueChain := llObservedValueChain well observed
  have noFresh : h.nextNode ∉ intrusiveNodes h q := by
    intro member
    obtain ⟨node, lookup⟩ := llChain_lookup (llWellFormed_chain well) h.nextNode member
    rw [fresh] at lookup
    contradiction
  have oldValues : LLValueChain
      (llPrependHeap (llAllocatedHeap h value) q q.id h.nextNode ⟨none, none, value, [], none⟩)
      q.head (intrusiveNodes h q) values := by
    apply llValueChain_transport valueChain
    intro id member
    have different : id ≠ h.nextNode := by
      intro equal
      exact noFresh (equal ▸ member)
    change ((llAllocatedHeap h value).setNode h.nextNode
      ⟨q.head, some q.id, value, [], none⟩).node? id = h.node? id
    rw [llSetNode_other _ _ _ _ different, llAllocate_other h value id different]
  have newValues : LLValueChain
      (llPrependHeap (llAllocatedHeap h value) q q.id h.nextNode ⟨none, none, value, [], none⟩)
      (llPrependList q h.nextNode).head (h.nextNode :: intrusiveNodes h q) (value :: values) :=
    .cons (llSetNode_self (llAllocatedHeap h value) h.nextNode _) oldValues
  refine ⟨prepended.1, llValueChain_observed newValues, ?_, ?_, ?_⟩
  · rw [prepended.2, allocated.2]
  · exact (llSetNode_length_present allocated.1.1 (llAllocate_lookup h value) _).trans
      (llAllocate_length h value fresh)
  · exact ⟨_, llSetNode_self (llAllocatedHeap h value) h.nextNode _, rfl, rfl⟩


theorem llChain_headNone {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} (chain : LLChain h head ids) : head = none ↔ ids = [] := by
  cases chain <;> simp

theorem llBuildWellFormed_autoEndpoints {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} {ids : List NodeId}
    (heapUnique : (h.nodes.map Prod.fst).Nodup)
    (chain : LLChain h q.head ids) (unique : ids.Nodup) (last : ids.getLast? = q.tail)
    (owners : ∀ id ∈ ids, ∃ node, h.node? id = some node ∧ node.queue = some owner)
    (allOwners : ∀ id node, (id, node) ∈ h.nodes → node.queue = some owner → id ∈ ids) :
    intrusiveWellFormedFor h q owner := by
  apply llBuildWellFormed heapUnique ?_ chain unique last owners allOwners
  simp only [Option.isNone_iff_eq_none, ← last, List.getLast?_eq_none_iff]
  exact llChain_headNone chain

abbrev llClearedHeap {α : Type} (h : Heap α) (id : NodeId) (node : HeapNode α) : Heap α :=
  h.setNode id {node with next := none, queue := none}

/-- Clearing the two fields is the final source step of every successful deletion. -/
theorem llClearFields {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) :
    (do
      let nextHeap ← llSetNodeField h id (fun current => {current with next := none})
      llSetNodeField nextHeap id (fun current => {current with queue := none})) =
      Except.ok (llClearedHeap h id node) := by
  rw [llSetNodeField_eq lookup]
  change llSetNodeField (h.setNode id {node with next := none}) id
      (fun current => {current with queue := none}) = _
  rw [llSetNodeField_eq (llSetNode_self h id _), llSetNode_overwrite]

/-- Deleting a singleton head follows the source endpoint-clearing branch. -/
theorem llDeleteSingleton_run {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {id : NodeId} {node : HeapNode α} (lookup : h.node? id = some node)
    (head : q.head = some id) (tail : q.tail = some id) :
    deleteFirstIntrusive h q id =
      some (.ok (llClearedHeap h id node, {q with head := none, tail := none})) := by
  have firstUpdate := llSetNodeField_eq lookup (fun current => {current with next := none})
  have secondUpdate := llSetNodeField_eq (llSetNode_self h id {node with next := none})
    (fun current => {current with queue := none})
  simp only [llSetNodeField] at firstUpdate secondUpdate
  simp [deleteFirstIntrusive, head, tail, firstUpdate, secondUpdate,
    llClearedHeap, llSetNode_overwrite, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, pure,
    Option.bind, Functor.map, ExceptT.map, ExceptT.mk]

/-- Deleting a nonsingleton head follows its next link before clearing it. -/
theorem llDeleteHead_run {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {id next tailId : NodeId} {node : HeapNode α} (lookup : h.node? id = some node)
    (head : q.head = some id) (tail : q.tail = some tailId)
    (different : tailId ≠ id) (nextLink : node.next = some next) :
    deleteFirstIntrusive h q id =
      some (.ok (llClearedHeap h id node, {q with head := some next})) := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  have firstUpdate := llSetNodeField_eq lookup (fun current => {current with next := none})
  have secondUpdate := llSetNodeField_eq (llSetNode_self h id {node with next := none})
    (fun current => {current with queue := none})
  simp only [llSetNodeField] at firstUpdate secondUpdate
  simp [deleteFirstIntrusive, head, tail, different, lookup', nextLink, firstUpdate,
    secondUpdate, llClearedHeap, llSetNode_overwrite, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    pure, Option.bind, Functor.map, ExceptT.map, ExceptT.mk]

/-- Removing the head preserves all remaining nodes and their owner correspondence. -/
theorem llRemoveHead_wellFormed {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} {id : NodeId} {node : HeapNode α} {rest : List NodeId}
    (well : intrusiveWellFormedFor h q owner) (lookup : h.node? id = some node)
    (observed : intrusiveNodes h q = id :: rest) (chain : LLChain h node.next rest) :
    intrusiveWellFormedFor (llClearedHeap h id node)
      {q with head := node.next, tail := rest.getLast?} owner ∧
    intrusiveNodes (llClearedHeap h id node) {q with head := node.next, tail := rest.getLast?} = rest := by
  have unique : (id :: rest).Nodup := observed ▸ well.2.2.1
  have absent := (List.nodup_cons.mp unique).1
  have restUnique := (List.nodup_cons.mp unique).2
  have restChain : LLChain (llClearedHeap h id node) node.next rest := by
    apply llChain_transport chain
    intro other member
    apply llSetNode_other
    intro equal
    exact absent (equal ▸ member)
  have result := llChain_observed (q := {q with head := node.next, tail := rest.getLast?})
    restChain restUnique
  refine ⟨?_, result⟩
  apply llBuildWellFormed_autoEndpoints (llSetNode_unique well.1 id _)
    restChain restUnique rfl
  · intro other member
    have memberOld : other ∈ intrusiveNodes h q := by
      rw [observed]
      exact List.mem_cons_of_mem id member
    obtain ⟨current, lookup', owner'⟩ := well.2.2.2.2.1 other memberOld
    refine ⟨current, ?_, owner'⟩
    change (h.setNode id {node with next := none, queue := none}).node? other = _
    rw [llSetNode_other]
    · exact lookup'
    · intro equal
      exact absent (equal ▸ member)
  · intro other current member owner'
    rcases llSetNode_member member with ⟨oldMember, different⟩ | ⟨_, equal⟩
    · have oldMember' := well.2.2.2.2.2 other current oldMember owner'
      rw [observed] at oldMember'
      exact (List.mem_cons.mp oldMember').resolve_left different
    · subst current
      contradiction


theorem llChain_cons_inv {α : Type} {h : Heap α} {head : Option NodeId}
    {id : NodeId} {rest : List NodeId} (chain : LLChain h head (id :: rest)) :
    ∃ node, head = some id ∧ h.node? id = some node ∧ LLChain h node.next rest := by
  cases chain with
  | cons lookup rest => exact ⟨_, rfl, lookup, rest⟩

/-- For a valid nonempty chain, the source head deletion returns the certified remainder. -/
theorem llDeleteHeadFromChain {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} {id : NodeId} {node : HeapNode α} {rest : List NodeId}
    (well : intrusiveWellFormedFor h q owner) (observed : intrusiveNodes h q = id :: rest)
    (head : q.head = some id) (lookup : h.node? id = some node) (chain : LLChain h node.next rest) :
    deleteFirstIntrusive h q id =
      some (.ok (llClearedHeap h id node, {q with head := node.next, tail := rest.getLast?})) := by
  have last : (id :: rest).getLast? = q.tail := by
    rw [← observed]
    exact well.2.2.2.1
  cases rest with
  | nil =>
      have nextNone : node.next = none := (llChain_headNone chain).mpr rfl
      have tail : q.tail = some id := by simpa only [List.getLast?_singleton] using last.symm
      simpa only [nextNone, List.getLast?_nil] using llDeleteSingleton_run lookup head tail
  | cons first rest =>
      obtain ⟨nextNode, nextLink, _, _⟩ := llChain_cons_inv chain
      have restLast : (first :: rest).getLast? = q.tail := by
        simpa only [List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)] using last
      obtain ⟨tailId, tail⟩ : ∃ tailId, q.tail = some tailId := by
        cases tail : q.tail with
        | none =>
            have empty := List.getLast?_eq_none_iff.mp (restLast.trans tail)
            contradiction
        | some tailId => exact ⟨tailId, rfl⟩
      have different : tailId ≠ id := by
        intro equal
        have member : id ∈ first :: rest := List.mem_of_getLast? (restLast.trans (equal ▸ tail))
        have unique : (id :: first :: rest).Nodup := observed ▸ well.2.2.1
        exact (List.nodup_cons.mp unique).1 member
      simpa only [nextLink, restLast] using llDeleteHead_run lookup head tail different nextLink

/-- All successful components of an intrusive head pop, before packaging its public statement. -/
theorem llPopfirst_complete {α : Type} {h : Heap α} (qr : ILLRef α)
    {id : NodeId} {rest : List NodeId} (well : intrusiveWellFormedFor h qr.list qr.waitee)
    (observed : intrusiveNodes h qr.list = id :: rest) :
    ∃ node, h.node? id = some node ∧ qr.list.head = some id ∧
      popfirstILLRef h qr = some (.ok
        (llClearedHeap h id node, {qr.list with head := node.next, tail := rest.getLast?}, id)) ∧
      intrusiveWellFormedFor (llClearedHeap h id node)
        {qr.list with head := node.next, tail := rest.getLast?} qr.waitee ∧
      intrusiveNodes (llClearedHeap h id node)
        {qr.list with head := node.next, tail := rest.getLast?} = rest := by
  have chain := llWellFormed_chain well
  rw [observed] at chain
  obtain ⟨node, head, lookup, restChain⟩ := llChain_cons_inv chain
  have deleted := llDeleteHeadFromChain well observed head lookup restChain
  have after := llRemoveHead_wellFormed well lookup observed restChain
  refine ⟨node, lookup, head, ?_, after.1, after.2⟩
  simp [popfirstILLRef, head, deleted, bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, pure, Option.bind, ExceptT.mk]

theorem LinkedListIntrusivePopfirst : JuliaLean.Proofs.base.linked_list.IntrusivePopFirstSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α h qr id rest well observed
    obtain ⟨node, _, _, run, after, nodes⟩ := llPopfirst_complete qr well observed
    rw [run]
    exact ⟨rfl, after, nodes, ⟨_, llSetNode_self h id _, rfl, rfl⟩⟩
  · intro α h q id rest well observed
    obtain ⟨node, _, _, run, after, nodes⟩ := llPopfirst_complete ⟨q, q.id⟩ well observed
    unfold popfirstIntrusive
    rw [run]
    exact ⟨rfl, after, nodes, ⟨_, llSetNode_self h id _, rfl, rfl⟩⟩
  · intro α h qr head _
    exact llPopfirstEmpty h qr head
  · intro α h q head _
    exact llPopfirstEmpty h ⟨q, q.id⟩ head


theorem llValueChain_cons_inv {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} {first : α} {rest : List α}
    (chain : LLValueChain h head ids (first :: rest)) :
    ∃ id node remaining, ids = id :: remaining ∧ head = some id ∧
      h.node? id = some node ∧ node.value = first ∧ LLValueChain h node.next remaining rest := by
  cases chain with
  | cons lookup rest => exact ⟨_, _, _, rfl, rfl, lookup, rfl, rest⟩

theorem llPopfirstLinked_of_run {α : Type} {h h' : Heap α} {q q' : LinkedList α}
    {id : NodeId} {node : HeapNode α}
    (run : popfirstILLRef h ⟨q, q.id⟩ = some (.ok (h', q', id)))
    (lookup : h'.node? id = some node) :
    popfirstLinked h q = some (.ok (h', q', node.value)) := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  simp [popfirstLinked, popfirstIntrusive, run, lookup', bind, ExceptT.bind,
    ExceptT.bindCont, ExceptT.pure, pure, Option.bind, ExceptT.mk]

theorem LinkedListBoxedPopfirst : JuliaLean.Proofs.base.linked_list.LinkedPopFirstSpec := by
  constructor
  · intro α h q first rest well observed
    have chain := llObservedValueChain well observed
    obtain ⟨id, node, remaining, ids, head, lookup, value, restChain⟩ := llValueChain_cons_inv chain
    obtain ⟨poppedNode, poppedLookup, _, run, after, nodes⟩ :=
      llPopfirst_complete ⟨q, q.id⟩ well ids
    have equal : node = poppedNode := Option.some.inj (lookup.symm.trans poppedLookup)
    subst poppedNode
    have boxedRun := llPopfirstLinked_of_run run (llSetNode_self h id
      {node with next := none, queue := none})
    change popfirstLinked h q = some (.ok
      (llClearedHeap h id node, {q with head := node.next, tail := remaining.getLast?}, node.value)) at boxedRun
    rw [boxedRun]
    have unique : (id :: remaining).Nodup := ids ▸ well.2.2.1
    have absent := (List.nodup_cons.mp unique).1
    have finalChain : LLValueChain (llClearedHeap h id node) node.next remaining rest := by
      apply llValueChain_transport restChain
      intro other member
      apply llSetNode_other
      intro equal
      exact absent (equal ▸ member)
    exact ⟨value, after, llValueChain_observed finalChain,
      ⟨id, _, head, llSetNode_self h id _, rfl, rfl⟩⟩
  · intro α h q head _
    exact llPopfirstLinkedEmpty h q head


theorem llValueChain_forget {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} {values : List α} (chain : LLValueChain h head ids values) :
    LLChain h head ids := by
  induction chain with
  | nil => exact .nil
  | cons lookup rest ih => exact .cons lookup ih

/-- Extending the last next link appends one new payload to the same finite chain. -/
theorem llValueChain_appendLast {α : Type} {h h' : Heap α} {head : Option NodeId}
    {ids : List NodeId} {values : List α} (chain : LLValueChain h head ids values)
    (unique : ids.Nodup) {tail fresh : NodeId} {freshNode : HeapNode α}
    (last : ids.getLast? = some tail)
    (newLookup : h'.node? fresh = some freshNode) (newNext : freshNode.next = none)
    (updated : ∀ old, h.node? tail = some old →
      h'.node? tail = some {old with next := some fresh})
    (preserved : ∀ id ∈ ids, id ≠ tail → h'.node? id = h.node? id) :
    LLValueChain h' head (ids ++ [fresh]) (values ++ [freshNode.value]) := by
  have newChain : LLValueChain h' (some fresh) [fresh] [freshNode.value] := by
    apply LLValueChain.cons newLookup
    rw [newNext]
    exact .nil
  induction chain generalizing tail with
  | nil => cases last
  | @cons id node ids values lookup rest ih =>
      cases ids with
      | nil =>
          have equal : id = tail := by simpa only [List.getLast?_singleton, Option.some.injEq] using last
          have emptyValues : values = [] := List.length_eq_zero_iff.mp (llValueChain_length rest)
          subst values
          subst tail
          exact LLValueChain.cons (node := {node with next := some fresh})
            (updated node lookup) newChain
      | cons next remaining =>
          have lastRest : (next :: remaining).getLast? = some tail := by
            simpa only [List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)] using last
          have different : id ≠ tail := by
            intro equal
            have member : tail ∈ next :: remaining := List.mem_of_getLast? lastRest
            apply (List.nodup_cons.mp unique).1
            simpa only [equal] using member
          apply LLValueChain.cons ((preserved id (List.mem_cons_self ..) different).trans lookup)
          apply ih (List.nodup_cons.mp unique).2 lastRest updated
          intro other member notTail
          exact preserved other (List.mem_cons_of_mem id member) notTail

/-- The source tail append on a nonempty list, with the concrete two heap updates exposed. -/
theorem llPushNonempty_run {α : Type} {h : Heap α} (qr : ILLRef α)
    {id tail : NodeId} {node lastNode : HeapNode α}
    (lookup : h.node? id = some node) (noOwner : node.queue = none)
    (tailEq : qr.list.tail = some tail) (tailLookup : h.node? tail = some lastNode)
    (different : tail ≠ id) :
    pushILLRef h qr id = .ok
      (((h.setNode id {node with queue := some qr.waitee}).setNode tail
        {lastNode with next := some id}), {qr.list with tail := some id}) := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  have tailLookup' : (h.setNode id {node with queue := some qr.waitee}).node? tail = some lastNode := by
    rw [llSetNode_other _ _ _ _ different]
    exact tailLookup
  have update := llSetNodeField_eq tailLookup' (fun current => {current with next := some id})
  simp only [llSetNodeField] at update
  simp [pushILLRef, lookup', noOwner, tailEq, update, bind, Except.bind, pure, Except.pure]

theorem llPushEmpty_run {α : Type} {h : Heap α} (qr : ILLRef α)
    {id : NodeId} {node : HeapNode α} (lookup : h.node? id = some node)
    (noOwner : node.queue = none) (tailEq : qr.list.tail = none) :
    pushILLRef h qr id = .ok
      (h.setNode id {node with queue := some qr.waitee}, {qr.list with head := some id, tail := some id}) := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  simp [pushILLRef, lookup', noOwner, tailEq, bind, Except.bind, pure, Except.pure]


/-- An intrusive append's full result, including payload preservation for boxed callers. -/
theorem llPush_complete {α : Type} {h : Heap α} (qr : ILLRef α)
    {id : NodeId} {node : HeapNode α}
    (well : intrusiveWellFormedFor h qr.list qr.waitee) (lookup : h.node? id = some node)
    (noNext : node.next = none) (noOwner : node.queue = none) :
    ∃ h' q', pushILLRef h qr id = .ok (h', q') ∧ q'.id = qr.list.id ∧
      intrusiveWellFormedFor h' q' qr.waitee ∧
      intrusiveNodes h' q' = intrusiveNodes h qr.list ++ [id] ∧
      h'.node? id = some {node with queue := some qr.waitee} ∧
      h'.nodes.length = h.nodes.length ∧
      ∀ values, LLValueChain h qr.list.head (intrusiveNodes h qr.list) values →
        LLValueChain h' q'.head (intrusiveNodes h qr.list ++ [id]) (values ++ [node.value]) := by
  have absent : id ∉ intrusiveNodes h qr.list :=
    llDetached_notMember well ⟨node, lookup, noNext, noOwner⟩
  cases tail : qr.list.tail with
  | none =>
      have head : qr.list.head = none := Option.isNone_iff_eq_none.mp
        (well.2.1.mpr (by simp [tail]))
      have oldEmpty : intrusiveNodes h qr.list = [] := by
        change llNodeLinks h qr.list.head (h.nodes.length + 1) = []
        rw [head, llNodeLinks_none]
      have prepended := llPrepend_wellFormed well lookup noNext noOwner
      have heapEq : llPrependHeap h qr.list qr.waitee id node =
          h.setNode id {node with queue := some qr.waitee} := by
        simp [llPrependHeap, head, noNext]
      have listEq : llPrependList qr.list id = {qr.list with head := some id, tail := some id} := by
        simp [llPrependList, head]
      rw [heapEq, listEq] at prepended
      refine ⟨h.setNode id {node with queue := some qr.waitee},
        {qr.list with head := some id, tail := some id},
        llPushEmpty_run qr lookup noOwner tail, rfl, prepended.1, ?_,
        llSetNode_self h id _, llSetNode_length_present well.1 lookup _, ?_⟩
      · simpa only [oldEmpty, List.nil_append] using prepended.2
      · intro values valueChain
        rw [head, oldEmpty] at valueChain
        cases valueChain
        rw [oldEmpty]
        apply LLValueChain.cons (node := {node with queue := some qr.waitee}) (llSetNode_self h id _)
        rw [noNext]
        exact .nil
  | some last =>
      have memberLast : last ∈ intrusiveNodes h qr.list :=
        List.mem_of_getLast? (well.2.2.2.1.trans tail)
      have different : last ≠ id := by
        intro equal
        exact absent (equal ▸ memberLast)
      obtain ⟨lastNode, lastLookup, lastOwner⟩ := well.2.2.2.2.1 last memberLast
      let h1 := h.setNode id {node with queue := some qr.waitee}
      let h2 := h1.setNode last {lastNode with next := some id}
      let q2 : InvasiveLinkedList α := {qr.list with tail := some id}
      have newLookup : h2.node? id = some {node with queue := some qr.waitee} := by
        change (h1.setNode last _).node? id = _
        rw [llSetNode_other _ _ _ _ (Ne.symm different)]
        exact llSetNode_self h id _
      have oldPreserved : ∀ other ∈ intrusiveNodes h qr.list,
          other ≠ last → h2.node? other = h.node? other := by
        intro other member notLast
        have notNew : other ≠ id := by
          intro equal
          exact absent (equal ▸ member)
        change (h1.setNode last _).node? other = _
        rw [llSetNode_other _ _ _ _ notLast]
        exact llSetNode_other h id other _ notNew
      have lastUpdated : ∀ old, h.node? last = some old →
          h2.node? last = some {old with next := some id} := by
        intro old oldLookup
        have equal := Option.some.inj (lastLookup.symm.trans oldLookup)
        subst old
        exact llSetNode_self h1 last _
      have valueExtension : ∀ values, LLValueChain h qr.list.head (intrusiveNodes h qr.list) values →
          LLValueChain h2 q2.head (intrusiveNodes h qr.list ++ [id]) (values ++ [node.value]) := by
        intro values valueChain
        exact llValueChain_appendLast (freshNode := {node with queue := some qr.waitee})
          valueChain well.2.2.1 (well.2.2.2.1.trans tail) newLookup noNext lastUpdated oldPreserved
      obtain ⟨oldValues, oldValueChain⟩ := llChain_hasValues (llWellFormed_chain well)
      have chain := llValueChain_forget (valueExtension oldValues oldValueChain)
      have unique : (intrusiveNodes h qr.list ++ [id]).Nodup := by
        rw [List.nodup_append]
        refine ⟨well.2.2.1, by simp, ?_⟩
        intro left leftMember right rightMember
        have rightEq : right = id := by simpa only [List.mem_singleton] using rightMember
        subst right
        intro equal
        exact absent (equal ▸ leftMember)
      have lastEq : (intrusiveNodes h qr.list ++ [id]).getLast? = q2.tail := by simp [q2]
      have wellAfter : intrusiveWellFormedFor h2 q2 qr.waitee := by
        apply llBuildWellFormed_autoEndpoints
          (llSetNode_unique (llSetNode_unique well.1 id _) last _) chain unique lastEq
        · intro other member
          rcases List.mem_append.mp member with oldMember | newMember
          · obtain ⟨old, oldLookup, oldOwner⟩ := well.2.2.2.2.1 other oldMember
            by_cases sameLast : other = last
            · subst other
              have equal := Option.some.inj (lastLookup.symm.trans oldLookup)
              subst old
              exact ⟨_, llSetNode_self h1 last _, lastOwner⟩
            · exact ⟨old, (oldPreserved other oldMember sameLast).trans oldLookup, oldOwner⟩
          · have equal : other = id := by simpa only [List.mem_singleton] using newMember
            subst other
            exact ⟨_, newLookup, rfl⟩
        · intro other current member owner
          rcases llSetNode_member member with ⟨h1Member, _⟩ | ⟨equal, _⟩
          · rcases llSetNode_member h1Member with ⟨oldMember, _⟩ | ⟨equal, _⟩
            · exact List.mem_append.mpr (Or.inl (well.2.2.2.2.2 other current oldMember owner))
            · exact List.mem_append.mpr (Or.inr (by simpa only [List.mem_singleton] using equal))
          · exact List.mem_append.mpr (Or.inl (equal.symm ▸ memberLast))
      have h1Last : h1.node? last = some lastNode := by
        rw [llSetNode_other _ _ _ _ different]
        exact lastLookup
      have lengthAfter : h2.nodes.length = h.nodes.length :=
        (llSetNode_length_present (llSetNode_unique well.1 id _) h1Last _).trans
          (llSetNode_length_present well.1 lookup _)
      exact ⟨h2, q2, llPushNonempty_run qr lookup noOwner tail lastLookup different,
        rfl, wellAfter, llChain_observed chain unique, newLookup, lengthAfter, valueExtension⟩

theorem LinkedListIntrusivePush : JuliaLean.Proofs.base.linked_list.IntrusivePushSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α h qr id well detached
    obtain ⟨node, lookup, noNext, noOwner⟩ := detached
    obtain ⟨h', q', run, _, after, nodes, newLookup, _, _⟩ := llPush_complete qr well lookup noNext noOwner
    rw [run]
    exact ⟨after, nodes, ⟨_, newLookup, rfl, noNext⟩⟩
  · intro α h q id well detached
    obtain ⟨node, lookup, noNext, noOwner⟩ := detached
    obtain ⟨h', q', run, idEq, after, nodes, newLookup, _, _⟩ := llPush_complete ⟨q, q.id⟩ well lookup noNext noOwner
    unfold pushIntrusive
    rw [run]
    have after' : intrusiveWellFormed h' q' := by
      change intrusiveWellFormedFor h' q' q'.id
      rw [idEq]
      exact after
    exact ⟨after', nodes, ⟨_, newLookup, rfl, noNext⟩⟩
  · intro α h qr id node lookup queued
    exact llPushQueued qr lookup queued
  · intro α h q id node lookup queued
    exact llPushIntrusiveQueued q lookup queued

theorem LinkedListBoxedPush : JuliaLean.Proofs.base.linked_list.LinkedPushSpec := by
  intro α h q values value well observed fresh
  have allocated := llAllocate_wellFormed value well fresh
  obtain ⟨h', q', run, idEq, after, nodes, newLookup, lengthSame, extension⟩ :=
    llPush_complete ⟨q, q.id⟩ allocated.1 (llAllocate_lookup h value) rfl rfl
  have actualRun : pushLinked h q value = .ok (h', q') := by
    unfold pushLinked newLinkedListItem Heap.allocateNode
    change pushIntrusive (llAllocatedHeap h value) q h.nextNode = _
    unfold pushIntrusive
    rw [run]
  rw [actualRun]
  have oldValueChain := llObservedValueChain well observed
  have newValueChain : LLValueChain (llAllocatedHeap h value) q.head
      (intrusiveNodes (llAllocatedHeap h value) q) values := by
    rw [allocated.2]
    apply llValueChain_transport oldValueChain
    intro id member
    apply llAllocate_other
    intro equal
    obtain ⟨node, lookup⟩ := llChain_lookup (llWellFormed_chain well) id member
    rw [equal, fresh] at lookup
    contradiction
  have after' : intrusiveWellFormed h' q' := by
    change intrusiveWellFormedFor h' q' q'.id
    rw [idEq]
    exact after
  exact ⟨after', llValueChain_observed (extension values newValueChain),
    by simpa only [allocated.2] using nodes,
    lengthSame.trans (llAllocate_length h value fresh),
    ⟨_, newLookup, rfl, rfl, rfl⟩⟩


/-- The fresh intrusive constructor satisfies its complete legacy invariant. -/
theorem llIntrusiveConstructor : JuliaLean.Proofs.base.linked_list.IntrusiveConstructorSpec := by
  intro α h unique unowned
  let h0 := {h with nextList := h.nextList + 1}
  let q0 : InvasiveLinkedList α := ⟨h.nextList, none, none⟩
  have well : intrusiveWellFormed h0 q0 := by
    apply llBuildWellFormed_autoEndpoints unique LLChain.nil (by simp) rfl
    · intro id member
      cases member
    · intro id node member owned
      exact False.elim (unowned id node member owned)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, well, rfl, ?_⟩
  exact LinkedListIntrusiveIterate h0 q0 well

/-- Self-append takes the error branch before inspecting either endpoint. -/
theorem llAppendSelf {α : Type} (h : Heap α) (q : InvasiveLinkedList α) :
    appendIntrusive h q q = some (.error .sameListAppend) := by
  simp [appendIntrusive, bind, ExceptT.bind, ExceptT.bindCont, pure, ExceptT.pure,
    throw, throwThe, MonadExceptOf.throw, Option.bind, ExceptT.mk]

/-- Identity deletion is a no-op when the node belongs to another owner. -/
theorem llDeleteOtherOwner {α : Type} {h : Heap α} (qr : ILLRef α) {id : NodeId}
    {node : HeapNode α} (lookup : h.node? id = some node)
    (different : node.queue ≠ some qr.waitee) :
    listDeleteFirstILLRef h qr id = some (.ok (h, qr.list)) := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  simp [listDeleteFirstILLRef, lookup', different, bind, ExceptT.bind,
    ExceptT.bindCont, pure, ExceptT.pure, Option.bind, ExceptT.mk]


/-- Heap membership determines lookup when keys are unique. -/
theorem llLookupList_ofMember {α : Type} {nodes : List (NodeId × HeapNode α)}
    (unique : (nodes.map Prod.fst).Nodup) {id : NodeId} {node : HeapNode α}
    (member : (id, node) ∈ nodes) :
    (nodes.find? (fun entry => entry.1 == id)).map Prod.snd = some node := by
  induction nodes with
  | nil => cases member
  | cons first rest ih =>
      have unique' := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with equal | member
      · subst first
        simp
      · have different : first.1 ≠ id := by
          intro equal
          apply unique'.1
          exact List.mem_map.mpr ⟨(id, node), member, equal.symm⟩
        have notEq : (first.1 == id) = false := by simp [different]
        simp only [List.find?_cons, notEq]
        exact ih unique'.2 member

theorem llLookup_ofMember {α : Type} {h : Heap α}
    (unique : (h.nodes.map Prod.fst).Nodup) {id : NodeId} {node : HeapNode α}
    (member : (id, node) ∈ h.nodes) : h.node? id = some node :=
  llLookupList_ofMember unique member

theorem llLookup_entryMember {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) : (id, node) ∈ h.nodes := by
  unfold Heap.node? at lookup
  cases found : h.nodes.find? (fun entry => entry.1 == id) with
  | none => simp only [found, Option.map_none] at lookup; contradiction
  | some pair =>
      have member := List.mem_of_find?_eq_some found
      have key : pair.1 = id := by simpa only [beq_iff_eq] using List.find?_some found
      have payload : pair.2 = node := by simpa only [found, Option.map_some, Option.some.injEq] using lookup
      have equal : pair = (id, node) := Prod.ext key payload
      exact equal ▸ member

theorem llSetNode_lookup {α : Type} (h : Heap α) (id query : NodeId) (node : HeapNode α) :
    (h.setNode id node).node? query = if query = id then some node else h.node? query := by
  by_cases equal : query = id
  · subst query
    simp only [↓reduceIte, llSetNode_self]
  · simp only [equal, ↓reduceIte, llSetNode_other h id query node equal]

/-- Queue-only changes preserve the identity chain. -/
theorem llChain_queueTransport {α : Type} {h h' : Heap α} {head : Option NodeId}
    {ids : List NodeId} (chain : LLChain h head ids)
    (changed : ∀ id ∈ ids, ∀ node, h.node? id = some node →
      ∃ owner, h'.node? id = some {node with queue := owner}) : LLChain h' head ids := by
  induction chain with
  | nil => exact .nil
  | @cons id node ids lookup rest ih =>
      obtain ⟨owner, lookup'⟩ := changed id (List.mem_cons_self ..) node lookup
      apply LLChain.cons lookup'
      exact ih (fun other member old oldLookup => changed other
        (List.mem_cons_of_mem id member) old oldLookup)

abbrev llSetQueueAlong {α : Type} : Heap α → Option NodeId → OwnerId →
    ExceptT ListFailure Option (Heap α) :=
  llPrivateConst% JuliaLean.base.linked_list.setQueueAlong

theorem llSetQueueAlong_none {α : Type} (h : Heap α) (owner : OwnerId) :
    llSetQueueAlong h none owner = some (.ok h) :=
  (llPrivateConst% JuliaLean.base.linked_list.setQueueAlong.eq_1) h owner

theorem llSetQueueAlong_some {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) (owner : OwnerId) :
    llSetQueueAlong h (some id) owner =
      llSetQueueAlong (h.setNode id {node with queue := some owner}) node.next owner := by
  have equation := (llPrivateConst% JuliaLean.base.linked_list.setQueueAlong.eq_def)
    h (some id) owner
  change llSetQueueAlong h (some id) owner =
    (ExceptT.mk (some (llLookup h id)) >>= fun current =>
      llSetQueueAlong (h.setNode id {current with queue := some owner}) current.next owner) at equation
  rw [llLookup_eq lookup] at equation
  exact equation

/-- The unbounded owner traversal terminates on a finite unique chain and updates precisely it. -/
theorem llSetQueueAlong_chain {α : Type} (h : Heap α) (head : Option NodeId)
    (ids : List NodeId) (owner : OwnerId) (chain : LLChain h head ids)
    (heapUnique : (h.nodes.map Prod.fst).Nodup) (unique : ids.Nodup) :
    ∃ h', llSetQueueAlong h head owner = some (.ok h') ∧
      (h'.nodes.map Prod.fst).Nodup ∧ h'.nodes.length = h.nodes.length ∧
      ∀ query, h'.node? query = (h.node? query).map (fun node =>
        if query ∈ ids then {node with queue := some owner} else node) := by
  induction ids generalizing h head with
  | nil =>
      have empty : head = none := (llChain_headNone chain).mpr rfl
      subst head
      refine ⟨h, llSetQueueAlong_none h owner, heapUnique, rfl, ?_⟩
      intro query
      simp
  | cons id ids ih =>
      obtain ⟨node, headEq, lookup, restChain⟩ := llChain_cons_inv chain
      subst head
      have noRepeat := (List.nodup_cons.mp unique).1
      let h1 := h.setNode id {node with queue := some owner}
      have afterChain : LLChain h1 node.next ids := by
        apply llChain_transport restChain
        intro query member
        apply llSetNode_other
        intro equal
        exact noRepeat (equal ▸ member)
      obtain ⟨h2, run, finalUnique, lengthSame, lookupFinal⟩ :=
        ih h1 node.next afterChain (llSetNode_unique heapUnique id _) (List.nodup_cons.mp unique).2
      refine ⟨h2, ?_, finalUnique, lengthSame.trans (llSetNode_length_present heapUnique lookup _), ?_⟩
      · rw [llSetQueueAlong_some lookup]
        exact run
      · intro query
        rw [lookupFinal]
        by_cases equal : query = id
        · subst query
          change ((h.setNode id _).node? id).map _ = _
          rw [llSetNode_self, lookup]
          simp [noRepeat]
        · change ((h.setNode id _).node? query).map _ = _
          rw [llSetNode_other _ _ _ _ equal]
          simp only [List.mem_cons, equal, false_or]



end JuliaLean.ChatGPT.Batch4.Group24

namespace JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean.base.linked_list JuliaLean.Proofs.base.linked_list

/-- Replacing one node without changing its queue preserves all owner observations. -/
theorem llSetNode_queueView {α : Type} {h : Heap α} {id : NodeId}
    {old changed : HeapNode α} (lookup : h.node? id = some old)
    (sameQueue : changed.queue = old.queue) (query : NodeId) :
    ((h.setNode id changed).node? query).map HeapNode.queue =
      (h.node? query).map HeapNode.queue := by
  by_cases equal : query = id
  · subst query
    rw [llSetNode_self, lookup]
    exact congrArg some sameQueue
  · rw [llSetNode_other _ _ _ _ equal]

/-- Equal queue observations transfer an existing node together with its owner. -/
theorem llQueueView_lookup {α : Type} {h h' : Heap α}
    (same : ∀ query, (h'.node? query).map HeapNode.queue = (h.node? query).map HeapNode.queue)
    {id : NodeId} {node : HeapNode α} (lookup : h.node? id = some node) :
    ∃ current, h'.node? id = some current ∧ current.queue = node.queue := by
  have image := same id
  rw [lookup] at image
  cases found : h'.node? id with
  | none => simp only [found, Option.map_none, Option.map_some] at image; contradiction
  | some current =>
      refine ⟨current, rfl, ?_⟩
      simpa only [found, Option.map_some, Option.some.injEq] using image

/-- Reconnecting the final link concatenates two finite chains. -/
theorem llChain_joinLast {α : Type} {h h' : Heap α} {head secondHead : Option NodeId}
    {ids secondIds : List NodeId} (chain : LLChain h head ids)
    (unique : ids.Nodup) {tail : NodeId} (last : ids.getLast? = some tail)
    (second : LLChain h' secondHead secondIds)
    (updated : ∀ old, h.node? tail = some old →
      h'.node? tail = some {old with next := secondHead})
    (preserved : ∀ id ∈ ids, id ≠ tail → h'.node? id = h.node? id) :
    LLChain h' head (ids ++ secondIds) := by
  induction chain generalizing tail with
  | nil => cases last
  | @cons id node ids lookup rest ih =>
      cases ids with
      | nil =>
          have equal : id = tail := by simpa only [List.getLast?_singleton, Option.some.injEq] using last
          subst tail
          exact LLChain.cons (node := {node with next := secondHead}) (updated node lookup) second
      | cons next remaining =>
          have lastRest : (next :: remaining).getLast? = some tail := by
            simpa only [List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)] using last
          have different : id ≠ tail := by
            intro equal
            have member : tail ∈ next :: remaining := List.mem_of_getLast? lastRest
            apply (List.nodup_cons.mp unique).1
            simpa only [equal] using member
          apply LLChain.cons ((preserved id (List.mem_cons_self ..) different).trans lookup)
          apply ih (List.nodup_cons.mp unique).2 lastRest updated
          intro other member notTail
          exact preserved other (List.mem_cons_of_mem id member) notTail

/-- The append source body when the destination has no final node to reconnect. -/
theorem llAppendEmptyDestination_run {α : Type} (h : Heap α) (q source : InvasiveLinkedList α)
    (different : q.id ≠ source.id) {first last : NodeId}
    (head : source.head = some first) (tail : source.tail = some last) (empty : q.tail = none) :
    appendIntrusive h q source = (do
      let final ← llSetQueueAlong h (some first) q.id
      pure (final, {q with head := some first, tail := some last},
        {source with head := none, tail := none})) := by
  simp [appendIntrusive, different, head, tail, empty, bind, ExceptT.bind,
    ExceptT.bindCont, pure, ExceptT.pure, Option.bind, ExceptT.mk, llSetQueueAlong]

/-- The append source body after reconnecting the destination's previous final node. -/
theorem llAppendNonemptyDestination_run {α : Type} {h : Heap α} (q source : InvasiveLinkedList α)
    (different : q.id ≠ source.id) {first last previous : NodeId} {old : HeapNode α}
    (head : source.head = some first) (tail : source.tail = some last)
    (previousTail : q.tail = some previous) (lookup : h.node? previous = some old) :
    appendIntrusive h q source = (do
      let final ← llSetQueueAlong (h.setNode previous {old with next := some first})
        (some first) q.id
      pure (final, {q with tail := some last}, {source with head := none, tail := none})) := by
  have update := llSetNodeField_eq lookup (fun current => {current with next := some first})
  simp only [llSetNodeField] at update
  simp [appendIntrusive, different, head, tail, previousTail, update, bind, ExceptT.bind,
    ExceptT.bindCont, pure, ExceptT.pure, Option.bind, ExceptT.mk, llSetQueueAlong]


/-- Complete append once the source's links have been connected; owner traversal is proved, not assumed. -/
theorem llAppend_finish {α : Type} {h preparedHeap : Heap α}
    {q source prepared : InvasiveLinkedList α}
    (different : q.id ≠ source.id) (well : intrusiveWellFormed h q)
    (sourceWell : intrusiveWellFormed h source)
    (heapUnique : (preparedHeap.nodes.map Prod.fst).Nodup)
    (preparedId : prepared.id = q.id)
    (joined : LLChain preparedHeap prepared.head (intrusiveNodes h q ++ intrusiveNodes h source))
    (sourceChain : LLChain preparedHeap source.head (intrusiveNodes h source))
    (last : (intrusiveNodes h q ++ intrusiveNodes h source).getLast? = prepared.tail)
    (queueSame : ∀ query, (preparedHeap.node? query).map HeapNode.queue =
      (h.node? query).map HeapNode.queue)
    (setup : appendIntrusive h q source = (do
      let final ← llSetQueueAlong preparedHeap source.head q.id
      pure (final, prepared, {source with head := none, tail := none}))) :
    ∃ final, appendIntrusive h q source =
        some (.ok (final, prepared, {source with head := none, tail := none})) ∧
      intrusiveWellFormed final prepared ∧
      intrusiveWellFormed final {source with head := none, tail := none} ∧
      intrusiveNodes final prepared = intrusiveNodes h q ++ intrusiveNodes h source ∧
      ∀ id ∈ intrusiveNodes h source,
        ∃ node, final.node? id = some node ∧ node.queue = some q.id := by
  obtain ⟨final, run, finalUnique, _, lookupFinal⟩ :=
    llSetQueueAlong_chain preparedHeap source.head (intrusiveNodes h source) q.id
      sourceChain heapUnique sourceWell.2.2.1
  have disjoint := llDistinctOwnersDisjoint different well sourceWell
  have unique : (intrusiveNodes h q ++ intrusiveNodes h source).Nodup := by
    rw [List.nodup_append]
    refine ⟨well.2.2.1, sourceWell.2.2.1, ?_⟩
    intro left leftMember right rightMember equal
    apply disjoint left leftMember
    simpa only [equal] using rightMember
  have finalChain : LLChain final prepared.head (intrusiveNodes h q ++ intrusiveNodes h source) := by
    apply llChain_queueTransport joined
    intro id _ node lookup
    by_cases member : id ∈ intrusiveNodes h source
    · exact ⟨some q.id, by rw [lookupFinal, lookup]; simp [member]⟩
    · exact ⟨node.queue, by rw [lookupFinal, lookup]; simp [member]⟩
  have sourceOwners : ∀ id ∈ intrusiveNodes h source,
      ∃ node, final.node? id = some node ∧ node.queue = some q.id := by
    intro id member
    obtain ⟨old, oldLookup, _⟩ := sourceWell.2.2.2.2.1 id member
    obtain ⟨current, currentLookup, _⟩ := llQueueView_lookup queueSame oldLookup
    refine ⟨{current with queue := some q.id}, ?_, rfl⟩
    rw [lookupFinal, currentLookup]
    simp [member]
  have outside : ∀ id current, id ∉ intrusiveNodes h source → final.node? id = some current →
      ∃ old, h.node? id = some old ∧ old.queue = current.queue := by
    intro id current notSource lookup
    have image := lookupFinal id
    rw [lookup] at image
    cases intermediate : preparedHeap.node? id with
    | none => simp only [intermediate, Option.map_none] at image; contradiction
    | some mid =>
        have equal : current = mid := by
          simpa only [intermediate, Option.map_some, if_neg notSource, Option.some.injEq] using image
        subst current
        exact llQueueView_lookup (fun query => (queueSame query).symm) intermediate
  have destinationWell : intrusiveWellFormed final prepared := by
    change intrusiveWellFormedFor final prepared prepared.id
    rw [preparedId]
    apply llBuildWellFormed_autoEndpoints finalUnique finalChain unique last
    · intro id member
      rcases List.mem_append.mp member with destMember | sourceMember
      · obtain ⟨old, oldLookup, oldOwner⟩ := well.2.2.2.2.1 id destMember
        obtain ⟨current, currentLookup, currentQueue⟩ := llQueueView_lookup queueSame oldLookup
        by_cases fromSource : id ∈ intrusiveNodes h source
        · exact sourceOwners id fromSource
        · refine ⟨current, ?_, currentQueue.trans oldOwner⟩
          rw [lookupFinal, currentLookup]
          simp [fromSource]
      · exact sourceOwners id sourceMember
    · intro id current member owner
      by_cases fromSource : id ∈ intrusiveNodes h source
      · exact List.mem_append.mpr (Or.inr fromSource)
      · obtain ⟨old, oldLookup, oldQueue⟩ := outside id current fromSource
          (llLookup_ofMember finalUnique member)
        exact List.mem_append.mpr (Or.inl
          (well.2.2.2.2.2 id old (llLookup_entryMember oldLookup) (oldQueue.trans owner)))
  have emptyWell : intrusiveWellFormed final {source with head := none, tail := none} := by
    apply llBuildWellFormed_autoEndpoints finalUnique LLChain.nil (by simp) rfl
    · intro id member
      cases member
    · intro id current member owner
      have lookup := llLookup_ofMember finalUnique member
      by_cases fromSource : id ∈ intrusiveNodes h source
      · obtain ⟨newNode, newLookup, newOwner⟩ := sourceOwners id fromSource
        have equal := Option.some.inj (lookup.symm.trans newLookup)
        subst newNode
        exact False.elim (different (Option.some.inj (newOwner.symm.trans owner)))
      · obtain ⟨old, oldLookup, oldQueue⟩ := outside id current fromSource lookup
        exact False.elim (fromSource
          (sourceWell.2.2.2.2.2 id old (llLookup_entryMember oldLookup) (oldQueue.trans owner)))
  refine ⟨final, ?_, destinationWell, emptyWell, llChain_observed finalChain unique, sourceOwners⟩
  rw [setup, run]
  rfl


/-- Distinct-list append preserves both invariants and transfers each source owner. -/
theorem llIntrusiveAppend : JuliaLean.Proofs.base.linked_list.IntrusiveAppendSpec := by
  constructor
  · intro α h q source different well sourceWell
    cases sourceHead : source.head with
    | none =>
        have sourceTail : source.tail = none := Option.isNone_iff_eq_none.mp
          (sourceWell.2.1.mp (by simp [sourceHead]))
        have sourceEmpty : intrusiveNodes h source = [] := by
          change llNodeLinks h source.head (h.nodes.length + 1) = []
          rw [sourceHead, llNodeLinks_none]
        have run : appendIntrusive h q source = some (.ok (h, q, source)) := by
          simp [appendIntrusive, different, sourceHead, bind, ExceptT.bind,
            ExceptT.bindCont, pure, ExceptT.pure, Option.bind, ExceptT.mk]
        rw [run]
        refine ⟨well, sourceWell, ?_, sourceHead, sourceTail, ?_⟩
        · simp only [sourceEmpty, List.append_nil]
        · intro id member
          rw [sourceEmpty] at member
          cases member
    | some first =>
        cases sourceTail : source.tail with
        | none =>
            have endpoints := sourceWell.2.1
            simp [sourceHead, sourceTail] at endpoints
        | some last =>
            cases tail : q.tail with
            | none =>
                have head : q.head = none := Option.isNone_iff_eq_none.mp
                  (well.2.1.mpr (by simp [tail]))
                have empty : intrusiveNodes h q = [] := by
                  change llNodeLinks h q.head (h.nodes.length + 1) = []
                  rw [head, llNodeLinks_none]
                let prepared : InvasiveLinkedList α := {q with head := some first, tail := some last}
                have joined : LLChain h prepared.head (intrusiveNodes h q ++ intrusiveNodes h source) := by
                  simpa only [prepared, sourceHead, empty, List.nil_append] using llWellFormed_chain sourceWell
                have lastEq : (intrusiveNodes h q ++ intrusiveNodes h source).getLast? = prepared.tail := by
                  simpa only [prepared, empty, List.nil_append] using sourceWell.2.2.2.1.trans sourceTail
                have setup : appendIntrusive h q source = (do
                    let final ← llSetQueueAlong h source.head q.id
                    pure (final, prepared, {source with head := none, tail := none})) := by
                  simpa only [sourceHead, prepared] using
                    llAppendEmptyDestination_run h q source different sourceHead sourceTail tail
                obtain ⟨final, run, after, sourceAfter, nodes, owners⟩ :=
                  llAppend_finish (preparedHeap := h) (prepared := prepared)
                    different well sourceWell well.1 rfl joined
                    (llWellFormed_chain sourceWell) lastEq (fun _ => rfl) setup
                rw [run]
                exact ⟨after, sourceAfter, nodes, rfl, rfl, owners⟩
            | some previous =>
                have previousMember : previous ∈ intrusiveNodes h q :=
                  List.mem_of_getLast? (well.2.2.2.1.trans tail)
                obtain ⟨old, lookup, _⟩ := well.2.2.2.2.1 previous previousMember
                let hp := h.setNode previous {old with next := some first}
                let prepared : InvasiveLinkedList α := {q with tail := some last}
                have disjoint := llDistinctOwnersDisjoint different well sourceWell
                have sourceChain : LLChain hp source.head (intrusiveNodes h source) := by
                  apply llChain_transport (llWellFormed_chain sourceWell)
                  intro id member
                  apply llSetNode_other
                  intro equal
                  exact disjoint previous previousMember (equal ▸ member)
                have updated : ∀ current, h.node? previous = some current →
                    hp.node? previous = some {current with next := source.head} := by
                  intro current currentLookup
                  have equal := Option.some.inj (lookup.symm.trans currentLookup)
                  subst current
                  rw [sourceHead]
                  exact llSetNode_self h previous _
                have joined : LLChain hp prepared.head (intrusiveNodes h q ++ intrusiveNodes h source) := by
                  apply llChain_joinLast (llWellFormed_chain well) well.2.2.1
                    (well.2.2.2.1.trans tail) sourceChain updated
                  intro id _ differentId
                  exact llSetNode_other h previous id _ differentId
                have lastEq : (intrusiveNodes h q ++ intrusiveNodes h source).getLast? = prepared.tail := by
                  rw [List.getLast?_append, sourceWell.2.2.2.1, sourceTail]
                  rfl
                have queueSame : ∀ query, (hp.node? query).map HeapNode.queue =
                    (h.node? query).map HeapNode.queue :=
                  llSetNode_queueView lookup rfl
                have setup : appendIntrusive h q source = (do
                    let final ← llSetQueueAlong hp source.head q.id
                    pure (final, prepared, {source with head := none, tail := none})) := by
                  simpa only [hp, prepared, sourceHead] using
                    llAppendNonemptyDestination_run q source different sourceHead sourceTail tail lookup
                obtain ⟨final, run, after, sourceAfter, nodes, owners⟩ :=
                  llAppend_finish (preparedHeap := hp) (prepared := prepared)
                    different well sourceWell (llSetNode_unique well.1 previous _)
                    rfl joined sourceChain lastEq queueSame setup
                rw [run]
                exact ⟨after, sourceAfter, nodes, rfl, rfl, owners⟩
  · intro α h q
    exact llAppendSelf h q

end JuliaLean.ChatGPT.Batch4.Group24

namespace JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean.base.linked_list JuliaLean.Proofs.base.linked_list

abbrev llDeleteSearch {α : Type} : Heap α → NodeId → NodeId → NodeId →
    ExceptT ListFailure Option NodeId :=
  llPrivateConst% JuliaLean.base.linked_list.deleteSearchLoop

theorem llDeleteSearch_found {α : Type} (h : Heap α) (id previous : NodeId) :
    llDeleteSearch h id previous id = some (.ok previous) := by
  have equation := (llPrivateConst% JuliaLean.base.linked_list.deleteSearchLoop.eq_def)
    h id previous id
  simpa [llDeleteSearch, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, pure,
    Option.bind, ExceptT.mk] using equation

theorem llDeleteSearch_step {α : Type} {h : Heap α} {id previous current next : NodeId}
    {node : HeapNode α} (different : current ≠ id)
    (lookup : h.node? current = some node) (nextLink : node.next = some next) :
    llDeleteSearch h id previous current = llDeleteSearch h id current next := by
  have equation := (llPrivateConst% JuliaLean.base.linked_list.deleteSearchLoop.eq_def)
    h id previous current
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  simpa [llDeleteSearch, different, lookup', nextLink, bind, ExceptT.bind,
    ExceptT.bindCont, ExceptT.pure, pure, Option.bind, ExceptT.mk] using equation

theorem llChain_suffix {α : Type} {h : Heap α} {head : Option NodeId}
    {pre suffix : List NodeId} {id : NodeId}
    (chain : LLChain h head (pre ++ id :: suffix)) :
    ∃ node, h.node? id = some node ∧ LLChain h node.next suffix := by
  induction pre generalizing head with
  | nil =>
      obtain ⟨node, _, lookup, rest⟩ := llChain_cons_inv chain
      exact ⟨node, lookup, rest⟩
  | cons first pre ih =>
      obtain ⟨node, _, _, rest⟩ := llChain_cons_inv chain
      exact ih rest

abbrev llBypassHeap {α : Type} (h : Heap α) (previous : NodeId) (previousNode : HeapNode α)
    (id : NodeId) (node : HeapNode α) : Heap α :=
  llClearedHeap (h.setNode previous {previousNode with next := node.next}) id node

theorem llBypassHeap_other {α : Type} (h : Heap α) (previous : NodeId)
    (previousNode : HeapNode α) (id : NodeId) (node : HeapNode α) (other : NodeId)
    (notPrevious : other ≠ previous) (notId : other ≠ id) :
    (llBypassHeap h previous previousNode id node).node? other = h.node? other := by
  unfold llBypassHeap llClearedHeap
  rw [llSetNode_other _ _ _ _ notId, llSetNode_other _ _ _ _ notPrevious]

theorem llBypassHeap_previous {α : Type} (h : Heap α) (previous : NodeId)
    (previousNode : HeapNode α) (id : NodeId) (node : HeapNode α)
    (different : previous ≠ id) :
    (llBypassHeap h previous previousNode id node).node? previous =
      some {previousNode with next := node.next} := by
  unfold llBypassHeap llClearedHeap
  rw [llSetNode_other _ _ _ _ different, llSetNode_self]

theorem llBypassHeap_target {α : Type} (h : Heap α) (previous : NodeId)
    (previousNode : HeapNode α) (id : NodeId) (node : HeapNode α) :
    (llBypassHeap h previous previousNode id node).node? id =
      some {node with next := none, queue := none} := llSetNode_self _ _ _

/-- The source search finds the unique predecessor; rewiring and clearing splice the finite chain. -/
theorem llDeleteSearch_chain {α : Type} {h : Heap α} {id : NodeId}
    {node : HeapNode α} {suffix : List NodeId}
    (targetLookup : h.node? id = some node) (targetChain : LLChain h node.next suffix)
    (middle : List NodeId) {previous current : NodeId} {previousNode : HeapNode α}
    (previousLookup : h.node? previous = some previousNode)
    (nextLink : previousNode.next = some current)
    (chain : LLChain h (some current) (middle ++ id :: suffix))
    (unique : (previous :: (middle ++ id :: suffix)).Nodup) :
    ∃ predecessor predecessorNode,
      predecessor ∈ previous :: middle ∧
      (previous :: middle).getLast? = some predecessor ∧
      h.node? predecessor = some predecessorNode ∧ predecessorNode.next = some id ∧
      llDeleteSearch h id previous current = some (.ok predecessor) ∧
      LLChain (llBypassHeap h predecessor predecessorNode id node) (some previous)
        ((previous :: middle) ++ suffix) := by
  induction middle generalizing previous current previousNode with
  | nil =>
      obtain ⟨currentNode, head, currentLookup, _⟩ := llChain_cons_inv chain
      have currentEq : current = id := Option.some.inj head
      subst current
      have previousAbsent := (List.nodup_cons.mp unique).1
      have idAbsent := (List.nodup_cons.mp (List.nodup_cons.mp unique).2).1
      have different : previous ≠ id := by
        intro equal
        apply previousAbsent
        simp [equal]
      refine ⟨previous, previousNode, by simp, by simp, previousLookup, nextLink,
        llDeleteSearch_found h id previous, ?_⟩
      apply LLChain.cons (llBypassHeap_previous h previous previousNode id node different)
      apply llChain_transport targetChain
      intro other member
      apply llBypassHeap_other
      · intro equal
        exact previousAbsent (List.mem_cons_of_mem id (equal ▸ member))
      · intro equal
        exact idAbsent (equal ▸ member)
  | cons first middle ih =>
      obtain ⟨currentNode, head, currentLookup, restChain⟩ := llChain_cons_inv chain
      have currentEq : current = first := Option.some.inj head
      subst current
      have previousAbsent := (List.nodup_cons.mp unique).1
      have tailUnique := (List.nodup_cons.mp unique).2
      have firstAbsent := (List.nodup_cons.mp tailUnique).1
      have restNonempty : middle ++ id :: suffix ≠ [] := by simp
      obtain ⟨next, nextEq⟩ : ∃ next, currentNode.next = some next := by
        cases nextEq : currentNode.next with
        | none => exact False.elim (restNonempty ((llChain_headNone restChain).mp nextEq))
        | some next => exact ⟨next, rfl⟩
      have chain' : LLChain h (some next) (middle ++ id :: suffix) := nextEq ▸ restChain
      obtain ⟨predecessor, predecessorNode, predecessorMember, last, predecessorLookup,
        predecessorNext, searchRun, afterChain⟩ :=
        ih currentLookup nextEq chain' tailUnique
      have different : first ≠ id := by
        intro equal
        apply firstAbsent
        simp [equal]
      have previousNotPred : previous ≠ predecessor := by
        intro equal
        apply previousAbsent
        rw [equal]
        exact List.mem_append_left (id :: suffix) predecessorMember
      have previousNotId : previous ≠ id := by
        intro equal
        apply previousAbsent
        simp [equal]
      refine ⟨predecessor, predecessorNode, List.mem_cons_of_mem previous predecessorMember,
        ?_, predecessorLookup, predecessorNext, ?_, ?_⟩
      · simpa only [List.getLast?_cons_of_ne_nil (List.cons_ne_nil first middle)] using last
      · rw [llDeleteSearch_step different currentLookup nextEq]
        exact searchRun
      · apply LLChain.cons ((llBypassHeap_other h predecessor predecessorNode id node previous
          previousNotPred previousNotId).trans previousLookup)
        simpa only [nextLink, List.append_eq, List.cons_append] using afterChain

theorem llDeleteNonheadTail_run {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {first current previous id : NodeId} {firstNode previousNode node : HeapNode α}
    (head : q.head = some first) (firstLookup : h.node? first = some firstNode)
    (firstNext : firstNode.next = some current) (firstDifferent : first ≠ id)
    (search : llDeleteSearch h id first current = some (.ok previous))
    (previousLookup : h.node? previous = some previousNode) (previousDifferent : previous ≠ id)
    (lookup : h.node? id = some node) (tail : q.tail = some id) (nextNone : node.next = none) :
    deleteFirstIntrusive h q id =
      some (.ok (llBypassHeap h previous previousNode id node, {q with tail := some previous})) := by
  have firstLookup' := llLookup_eq firstLookup
  have firstUpdate := llSetNodeField_eq previousLookup (fun current => {current with next := none})
  have targetLookup : (h.setNode previous {previousNode with next := none}).node? id = some node := by
    rw [llSetNode_other _ _ _ _ (Ne.symm previousDifferent)]
    exact lookup
  have nextUpdate := llSetNodeField_eq targetLookup (fun current => {current with next := none})
  have queueUpdate := llSetNodeField_eq
    (llSetNode_self (h.setNode previous {previousNode with next := none}) id {node with next := none})
    (fun current => {current with queue := none})
  simp only [llLookup] at firstLookup'
  simp only [llDeleteSearch] at search
  simp only [llSetNodeField] at firstUpdate nextUpdate queueUpdate
  simp [deleteFirstIntrusive, head, firstLookup', firstNext, firstDifferent, search, tail,
    firstUpdate, nextUpdate, queueUpdate, llBypassHeap, llClearedHeap, nextNone,
    llSetNode_overwrite, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, pure,
    Option.bind, Functor.map, ExceptT.map, ExceptT.mk]

theorem llDeleteNonheadMiddle_run {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {first current previous id tailId next : NodeId} {firstNode previousNode node : HeapNode α}
    (head : q.head = some first) (firstLookup : h.node? first = some firstNode)
    (firstNext : firstNode.next = some current) (firstDifferent : first ≠ id)
    (search : llDeleteSearch h id first current = some (.ok previous))
    (previousLookup : h.node? previous = some previousNode) (previousDifferent : previous ≠ id)
    (lookup : h.node? id = some node) (tail : q.tail = some tailId)
    (tailDifferent : tailId ≠ id) (nextLink : node.next = some next) :
    deleteFirstIntrusive h q id = some (.ok (llBypassHeap h previous previousNode id node, q)) := by
  have firstLookup' := llLookup_eq firstLookup
  have lookup' := llLookup_eq lookup
  have firstUpdate := llSetNodeField_eq previousLookup (fun current => {current with next := some next})
  have targetLookup : (h.setNode previous {previousNode with next := some next}).node? id = some node := by
    rw [llSetNode_other _ _ _ _ (Ne.symm previousDifferent)]
    exact lookup
  have nextUpdate := llSetNodeField_eq targetLookup (fun current => {current with next := none})
  have queueUpdate := llSetNodeField_eq
    (llSetNode_self (h.setNode previous {previousNode with next := some next}) id {node with next := none})
    (fun current => {current with queue := none})
  simp only [llLookup] at firstLookup' lookup'
  simp only [llDeleteSearch] at search
  simp only [llSetNodeField] at firstUpdate nextUpdate queueUpdate
  simp [deleteFirstIntrusive, head, firstLookup', firstNext, firstDifferent, search, tail,
    tailDifferent, lookup', nextLink, firstUpdate, nextUpdate, queueUpdate, llBypassHeap,
    llClearedHeap, llSetNode_overwrite, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, pure,
    Option.bind, Functor.map, ExceptT.map, ExceptT.mk]

theorem llBypass_wellFormed {α : Type} {h : Heap α} {q q' : InvasiveLinkedList α}
    {owner : OwnerId} {pre suffix : List NodeId} {id previous : NodeId}
    {previousNode node : HeapNode α}
    (well : intrusiveWellFormedFor h q owner)
    (observed : intrusiveNodes h q = pre ++ id :: suffix)
    (previousMember : previous ∈ pre) (previousLookup : h.node? previous = some previousNode)
    (chain : LLChain (llBypassHeap h previous previousNode id node) q'.head (pre ++ suffix))
    (last : (pre ++ suffix).getLast? = q'.tail) :
    intrusiveWellFormedFor (llBypassHeap h previous previousNode id node) q' owner ∧
      intrusiveNodes (llBypassHeap h previous previousNode id node) q' = pre ++ suffix := by
  have unique : (pre ++ id :: suffix).Nodup := observed ▸ well.2.2.1
  have parts := List.nodup_append.mp unique
  have suffixParts := List.nodup_cons.mp parts.2.1
  have remainingUnique : (pre ++ suffix).Nodup :=
    List.nodup_append.mpr ⟨parts.1, suffixParts.2,
      fun left leftMember right rightMember =>
        parts.2.2 left leftMember right (List.mem_cons_of_mem id rightMember)⟩
  have noId : id ∉ pre ++ suffix := by
    intro member
    rcases List.mem_append.mp member with member | member
    · exact parts.2.2 id member id (List.mem_cons_self ..) rfl
    · exact suffixParts.1 member
  have previousDifferent : previous ≠ id := by
    intro equal
    exact noId (List.mem_append_left suffix (equal ▸ previousMember))
  refine ⟨?_, llChain_observed chain remainingUnique⟩
  apply llBuildWellFormed_autoEndpoints
    (llSetNode_unique (llSetNode_unique well.1 previous _) id _) chain remainingUnique last
  · intro other member
    have oldMember : other ∈ intrusiveNodes h q := by
      rw [observed]
      rcases List.mem_append.mp member with member | member
      · exact List.mem_append_left _ member
      · exact List.mem_append_right _ (List.mem_cons_of_mem id member)
    obtain ⟨current, lookup, queue⟩ := well.2.2.2.2.1 other oldMember
    by_cases equal : other = previous
    · subst other
      have same : current = previousNode := Option.some.inj (lookup.symm.trans previousLookup)
      subst current
      exact ⟨_, llBypassHeap_previous h previous previousNode id node previousDifferent, queue⟩
    · refine ⟨current, ?_, queue⟩
      rw [llBypassHeap_other h previous previousNode id node other equal]
      · exact lookup
      · intro equalId
        exact noId (equalId ▸ member)
  · intro other current member queue
    rcases llSetNode_member member with ⟨middleMember, different⟩ | ⟨_, same⟩
    · rcases llSetNode_member middleMember with ⟨oldMember, _⟩ | ⟨equal, _⟩
      · have memberOld := well.2.2.2.2.2 other current oldMember queue
        rw [observed] at memberOld
        rcases List.mem_append.mp memberOld with memberOld | memberOld
        · exact List.mem_append_left suffix memberOld
        · exact List.mem_append_right pre ((List.mem_cons.mp memberOld).resolve_left different)
      · subst other
        exact List.mem_append_left suffix previousMember
    · subst current
      contradiction

/-- Changes to links and ownership preserve the stored payload at every identity. -/
theorem llSetNode_value {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) (changed : HeapNode α) (same : changed.value = node.value)
    (other : NodeId) :
    ((h.setNode id changed).node? other).map HeapNode.value = (h.node? other).map HeapNode.value := by
  by_cases equal : other = id
  · subst other
    rw [llSetNode_self, lookup]
    exact congrArg some same
  · rw [llSetNode_other _ _ _ _ equal]

theorem llClearedHeap_value {α : Type} {h : Heap α} {id : NodeId} {node : HeapNode α}
    (lookup : h.node? id = some node) (other : NodeId) :
    ((llClearedHeap h id node).node? other).map HeapNode.value =
      (h.node? other).map HeapNode.value :=
        llSetNode_value lookup {node with next := none, queue := none} rfl other

theorem llBypassHeap_value {α : Type} {h : Heap α} {previous id : NodeId}
    {previousNode node : HeapNode α} (previousLookup : h.node? previous = some previousNode)
    (lookup : h.node? id = some node) (different : previous ≠ id) (other : NodeId) :
    ((llBypassHeap h previous previousNode id node).node? other).map HeapNode.value =
      (h.node? other).map HeapNode.value := by
  have targetLookup : (h.setNode previous {previousNode with next := node.next}).node? id = some node := by
    rw [llSetNode_other _ _ _ _ (Ne.symm different)]
    exact lookup
  exact (llClearedHeap_value targetLookup other).trans
    (llSetNode_value previousLookup {previousNode with next := node.next} rfl other)

theorem llGetLast_append_nonempty {α : Type} (pre : List α) {suffix : List α}
    (nonempty : suffix ≠ []) : (pre ++ suffix).getLast? = suffix.getLast? := by
  rw [List.getLast?_append]
  cases last : suffix.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp last))
  | some id => rfl

/-- Deletion of a selected position returns precisely the pre and suffix around it. -/
theorem llDelete_split {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} {id : NodeId} {pre suffix : List NodeId}
    (well : intrusiveWellFormedFor h q owner)
    (observed : intrusiveNodes h q = pre ++ id :: suffix) :
    ∃ h' q' node,
      h.node? id = some node ∧
      deleteFirstIntrusive h q id = some (.ok (h', q')) ∧
      intrusiveWellFormedFor h' q' owner ∧ intrusiveNodes h' q' = pre ++ suffix ∧
      q'.id = q.id ∧ h'.node? id = some {node with next := none, queue := none} ∧
      ∀ other, (h'.node? other).map HeapNode.value = (h.node? other).map HeapNode.value := by
  have chain := llWellFormed_chain well
  rw [observed] at chain
  have unique : (pre ++ id :: suffix).Nodup := observed ▸ well.2.2.1
  obtain ⟨node, lookup, targetChain⟩ := llChain_suffix chain
  cases pre with
  | nil =>
      obtain ⟨headNode, head, headLookup, restChain⟩ := llChain_cons_inv chain
      have same : headNode = node := Option.some.inj (headLookup.symm.trans lookup)
      subst headNode
      have run := llDeleteHeadFromChain well observed head lookup restChain
      have after := llRemoveHead_wellFormed well lookup observed restChain
      exact ⟨_, _, node, lookup, run, after.1, after.2, rfl,
        llSetNode_self h id _, llClearedHeap_value lookup⟩
  | cons first middle =>
      obtain ⟨firstNode, head, firstLookup, restChain⟩ := llChain_cons_inv chain
      have remainingNonempty : middle ++ id :: suffix ≠ [] := by simp
      obtain ⟨current, firstNext⟩ : ∃ current, firstNode.next = some current := by
        cases nextEq : firstNode.next with
        | none => exact False.elim (remainingNonempty ((llChain_headNone restChain).mp nextEq))
        | some current => exact ⟨current, rfl⟩
      have restChain' : LLChain h (some current) (middle ++ id :: suffix) := firstNext ▸ restChain
      obtain ⟨previous, previousNode, previousMember, previousLast, previousLookup,
        previousNext, search, afterChain⟩ :=
        llDeleteSearch_chain lookup targetChain middle firstLookup firstNext restChain' unique
      have firstAbsent := (List.nodup_cons.mp unique).1
      have firstDifferent : first ≠ id := by
        intro equal
        apply firstAbsent
        simp [equal]
      have parts := List.nodup_append.mp unique
      have previousDifferent : previous ≠ id :=
        parts.2.2 previous previousMember id (List.mem_cons_self ..)
      let q' : InvasiveLinkedList α := {q with tail := ((first :: middle) ++ suffix).getLast?}
      have finalChain : LLChain (llBypassHeap h previous previousNode id node) q'.head
          ((first :: middle) ++ suffix) := by
        simpa only [q', head] using afterChain
      have after := llBypass_wellFormed (q' := q') well observed previousMember
        previousLookup finalChain rfl
      have lastOld : ((first :: middle) ++ id :: suffix).getLast? = q.tail := by
        rw [← observed]
        exact well.2.2.2.1
      have run : deleteFirstIntrusive h q id =
          some (.ok (llBypassHeap h previous previousNode id node, q')) := by
        cases suffix with
        | nil =>
            have tail : q.tail = some id := by
              rw [List.getLast?_append] at lastOld
              exact lastOld.symm
            have nextNone := (llChain_headNone targetChain).mpr rfl
            have q'Eq : q' = {q with tail := some previous} := by
              simp only [q', List.append_nil, previousLast]
            rw [q'Eq]
            exact llDeleteNonheadTail_run head firstLookup firstNext firstDifferent search
              previousLookup previousDifferent lookup tail nextNone
        | cons next rest =>
            obtain ⟨nextNode, nextLink, _, _⟩ := llChain_cons_inv targetChain
            have suffixLast : (next :: rest).getLast? = q.tail := by
              simpa only [llGetLast_append_nonempty (first :: middle) (List.cons_ne_nil id (next :: rest)),
                List.getLast?_cons_of_ne_nil (List.cons_ne_nil next rest)] using lastOld
            obtain ⟨tailId, tail⟩ : ∃ tailId, q.tail = some tailId := by
              cases tail : q.tail with
              | none =>
                  have empty := List.getLast?_eq_none_iff.mp (suffixLast.trans tail)
                  contradiction
              | some tailId => exact ⟨tailId, rfl⟩
            have tailDifferent : tailId ≠ id := by
              intro equal
              have member : id ∈ next :: rest := List.mem_of_getLast?
                (suffixLast.trans (equal ▸ tail))
              exact (List.nodup_cons.mp parts.2.1).1 member
            have q'Eq : q' = q := by
              have lastEq : ((first :: middle) ++ next :: rest).getLast? = q.tail := by
                rw [llGetLast_append_nonempty (first :: middle) (List.cons_ne_nil next rest)]
                exact suffixLast
              simp only [q', lastEq]
            rw [q'Eq]
            exact llDeleteNonheadMiddle_run head firstLookup firstNext firstDifferent search
              previousLookup previousDifferent lookup tail tailDifferent nextLink
      exact ⟨_, q', node, lookup, run, after.1, after.2, rfl,
        llBypassHeap_target h previous previousNode id node,
        llBypassHeap_value previousLookup lookup previousDifferent⟩

/-- A member can be deleted, preserving the invariant, payloads, and list identity. -/
theorem llDelete_complete {α : Type} {h : Heap α} {q : InvasiveLinkedList α}
    {owner : OwnerId} {id : NodeId} (well : intrusiveWellFormedFor h q owner)
    (member : id ∈ intrusiveNodes h q) :
    ∃ h' q' node,
      h.node? id = some node ∧
      deleteFirstIntrusive h q id = some (.ok (h', q')) ∧
      intrusiveWellFormedFor h' q' owner ∧ intrusiveNodes h' q' = (intrusiveNodes h q).erase id ∧
      q'.id = q.id ∧ h'.node? id = some {node with next := none, queue := none} ∧
      ∀ other, (h'.node? other).map HeapNode.value = (h.node? other).map HeapNode.value := by
  obtain ⟨pre, suffix, observed, absent⟩ := List.eq_append_cons_of_mem member
  have unique : (pre ++ id :: suffix).Nodup := observed ▸ well.2.2.1
  obtain ⟨h', q', node, lookup, run, after, nodes, sameId, cleared, values⟩ :=
    llDelete_split well observed
  refine ⟨h', q', node, lookup, run, after, ?_, sameId, cleared, values⟩
  rw [observed, List.erase_append_right _ absent, List.erase_cons_head]
  exact nodes

theorem llDeleteOwned_run {α : Type} {h : Heap α} {qr : ILLRef α}
    {id : NodeId} {node : HeapNode α} (lookup : h.node? id = some node)
    (owner : node.queue = some qr.waitee) :
    listDeleteFirstILLRef h qr id = deleteFirstIntrusive h qr.list id := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  simp [listDeleteFirstILLRef, lookup', owner, bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, pure, Option.bind, ExceptT.mk]

theorem llIntrusiveDeleteSpec : JuliaLean.Proofs.base.linked_list.IntrusiveDeleteSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α h qr id node lookup owner
    have lookup' := llLookup_eq lookup
    simp only [llLookup] at lookup'
    simp [listDeleteFirstILLRef, lookup', owner, bind, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, pure, Option.bind, ExceptT.mk]
  · intro α h qr id well member
    obtain ⟨h', q', node, lookup, run, after, nodes, sameId, cleared, values⟩ :=
      llDelete_complete well member
    obtain ⟨ownedNode, ownedLookup, owner⟩ := well.2.2.2.2.1 id member
    have same : ownedNode = node := Option.some.inj (ownedLookup.symm.trans lookup)
    subst ownedNode
    rw [llDeleteOwned_run (qr := qr) lookup owner, run]
    exact ⟨after, nodes, ⟨_, cleared, rfl, rfl⟩⟩
  · intro α h q id well member
    obtain ⟨h', q', node, lookup, run, after, nodes, sameId, cleared, values⟩ :=
      llDelete_complete well member
    obtain ⟨ownedNode, ownedLookup, owner⟩ := well.2.2.2.2.1 id member
    have same : ownedNode = node := Option.some.inj (ownedLookup.symm.trans lookup)
    subst ownedNode
    change (match listDeleteFirstILLRef h ⟨q, q.id⟩ id with
      | none => False | some (.error _) => False
      | some (.ok (h', q')) => intrusiveWellFormed h' q' ∧
        intrusiveNodes h' q' = (intrusiveNodes h q).erase id ∧
        ∃ node, h'.node? id = some node ∧ node.next = none ∧ node.queue = none)
    rw [llDeleteOwned_run (qr := ⟨q, q.id⟩) lookup owner, run]
    refine ⟨?_, nodes, ⟨_, cleared, rfl, rfl⟩⟩
    change intrusiveWellFormedFor h' q' q'.id
    rw [sameId]
    exact after
  · intro α h q id well member
    obtain ⟨h', q', node, lookup, run, after, nodes, sameId, cleared, values⟩ :=
      llDelete_complete well member
    rw [run]
    refine ⟨?_, nodes, ⟨_, cleared, rfl, rfl⟩⟩
    change intrusiveWellFormedFor h' q' q'.id
    rw [sameId]
    exact after

/-- Tail pop is deletion at the last certified identity, retaining all preceding payloads. -/
theorem llPop_complete {α : Type} {h : Heap α} (qr : ILLRef α)
    {ids : List NodeId} {id : NodeId} (well : intrusiveWellFormedFor h qr.list qr.waitee)
    (observed : intrusiveNodes h qr.list = ids ++ [id]) :
    ∃ h' q' node,
      h.node? id = some node ∧ qr.list.tail = some id ∧
      popILLRef h qr = some (.ok (h', q', id)) ∧
      intrusiveWellFormedFor h' q' qr.waitee ∧ intrusiveNodes h' q' = ids ∧
      q'.id = qr.list.id ∧ h'.node? id = some {node with next := none, queue := none} ∧
      ∀ other, (h'.node? other).map HeapNode.value = (h.node? other).map HeapNode.value := by
  obtain ⟨h', q', node, lookup, run, after, nodes, sameId, cleared, values⟩ :=
    llDelete_split well observed
  have tail : qr.list.tail = some id := by
    have last := well.2.2.2.1
    rw [observed] at last
    simpa using last.symm
  refine ⟨h', q', node, lookup, tail, ?_, after, ?_, sameId, cleared, values⟩
  · simp [popILLRef, tail, run, bind, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, pure, Option.bind, ExceptT.mk]
  · simpa only [List.append_nil] using nodes

theorem llValueChain_filterMap {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} {values : List α} (chain : LLValueChain h head ids values) :
    ids.filterMap (fun id => (h.node? id).map HeapNode.value) = values := by
  induction chain with
  | nil => rfl
  | @cons id node ids values lookup rest ih =>
      simp only [List.filterMap_cons, lookup, Option.map_some, ih]

theorem llPopLinked_of_run {α : Type} {h h' : Heap α} {q q' : LinkedList α}
    {id : NodeId} {node : HeapNode α}
    (run : popILLRef h ⟨q, q.id⟩ = some (.ok (h', q', id)))
    (lookup : h'.node? id = some node) :
    popLinked h q = some (.ok (h', q', node.value)) := by
  have lookup' := llLookup_eq lookup
  simp only [llLookup] at lookup'
  simp [popLinked, popIntrusive, run, lookup', bind, ExceptT.bind,
    ExceptT.bindCont, ExceptT.pure, pure, Option.bind, ExceptT.mk]

end JuliaLean.ChatGPT.Batch4.Group24

/-! Completed batch 9 group 17 linked-list properties. -/

namespace JuliaLean.ChatGPT.Batch9.Group17
open JuliaLean.base.linked_list JuliaLean.Proofs.base.linked_list
open JuliaLean.ChatGPT.Batch4.Group24

/-- linked-list-intrusive-pop: Tail removal returns and detaches the tail. -/
theorem LinkedListIntrusivePop_proven : JuliaLean.Proofs.base.linked_list.IntrusivePopSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α h qr ids id well observed
    obtain ⟨h', q', node, lookup, tail, run, after, nodes, sameId, cleared, values⟩ :=
      llPop_complete qr well observed
    rw [run]
    exact ⟨rfl, after, nodes, ⟨_, cleared, rfl, rfl⟩⟩
  · intro α h q ids id well observed
    obtain ⟨h', q', node, lookup, tail, run, after, nodes, sameId, cleared, values⟩ :=
      llPop_complete ⟨q, q.id⟩ well observed
    unfold popIntrusive
    rw [run]
    refine ⟨rfl, ?_, nodes, ⟨_, cleared, rfl, rfl⟩⟩
    change intrusiveWellFormedFor h' q' q'.id
    rw [sameId]
    exact after
  · intro α h qr _ tail
    exact llPopEmpty h qr tail
  · intro α h q _ tail
    exact llPopEmpty h ⟨q, q.id⟩ tail

/-- tasks-coverage-linked-generic: Assemble the checked method specifications. -/
theorem TasksCoverageLinkedGeneric_proven : JuliaLean.Proofs.base.linked_list.LinkedGenericBodies := by
  exact ⟨llIntrusiveConstructor, LinkedListIntrusiveIterate, intrusiveIsEmptySpec_proven,
    LinkedListIntrusiveLength, llIntrusiveAppend, LinkedListIntrusivePush,
    LinkedListIntrusivePushfirst, LinkedListIntrusivePop_proven,
    LinkedListIntrusivePopfirst, llIntrusiveDeleteSpec⟩

/-- Split a finite value chain at its final payload. -/
theorem linkedValueChain_last {α : Type} {h : Heap α} {head : Option NodeId}
    {ids : List NodeId} {rest : List α} {last : α}
    (chain : LLValueChain h head ids (rest ++ [last])) :
    ∃ pre id node, ids = pre ++ [id] ∧ h.node? id = some node ∧ node.value = last ∧
      pre.filterMap (fun key => (h.node? key).map HeapNode.value) = rest := by
  induction rest generalizing head ids with
  | nil =>
      cases chain with
      | @cons id node remaining tailValues lookup tail =>
          have empty : remaining = [] := List.eq_nil_of_length_eq_zero
            (llValueChain_length tail).symm
          subst remaining
          exact ⟨[], id, node, rfl, lookup, rfl, rfl⟩
  | cons first rest ih =>
      cases chain with
      | @cons firstId firstNode remaining tailValues lookup tail =>
          obtain ⟨pre, id, node, identities, present, value, filtered⟩ := ih tail
          refine ⟨firstId :: pre, id, node, ?_, present, value, ?_⟩
          · simp only [identities, List.cons_append]
          · simp only [List.filterMap_cons, lookup, Option.map_some, filtered]

/-- linked-list-boxed-pop: Tail removal preserves precisely the preceding payloads. -/
theorem LinkedListBoxedPop_proven : JuliaLean.Proofs.base.linked_list.LinkedPopSpec := by
  constructor
  · intro α h q values rest last well observed splitValues
    have valueChain := llObservedValueChain well observed
    rw [splitValues] at valueChain
    obtain ⟨ids, id, node, splitIds, lookup, lastValue, prefixValues⟩ :=
      linkedValueChain_last valueChain
    obtain ⟨h', q', removed, oldLookup, tail, run, after, nodes, sameId, cleared, preserved⟩ :=
      llPop_complete ⟨q, q.id⟩ well splitIds
    have sameNode : removed = node := Option.some.inj (oldLookup.symm.trans lookup)
    subst removed
    have boxedRun := llPopLinked_of_run run cleared
    rw [boxedRun]
    have after' : intrusiveWellFormed h' q' := by
      change intrusiveWellFormedFor h' q' q'.id
      rw [sameId]
      exact after
    obtain ⟨remainingValues, remainingChain⟩ := llChain_hasValues (llWellFormed_chain after')
    have filtered := llValueChain_filterMap remainingChain
    rw [nodes] at filtered
    have mapPreserved : ids.filterMap (fun key => (h'.node? key).map HeapNode.value) =
        ids.filterMap (fun key => (h.node? key).map HeapNode.value) := by
      apply congrArg (fun f => ids.filterMap f)
      exact funext preserved
    have remainingEqual : remainingValues = rest :=
      filtered.symm.trans (mapPreserved.trans prefixValues)
    rw [remainingEqual] at remainingChain
    exact ⟨lastValue, after', llValueChain_observed remainingChain,
      ⟨id, _, tail, cleared, rfl, rfl⟩⟩
  · intro α h q _ tail
    exact llPopLinkedEmpty h q tail

end JuliaLean.ChatGPT.Batch9.Group17

namespace JuliaLean.Proofs.base.linked_list

open JuliaLean.Registry
def entries : List Entry := [
  { id := "tasks-linked-list-wellformed", juliaFile := "base/linked_list.jl"
    juliaFns := ["push!(::ILLRef)", "pushfirst!(::ILLRef)", "pop!(::ILLRef)",
      "popfirst!(::ILLRef)", "list_deletefirst!(::ILLRef)", "_list_deletefirst!"]
    statement := "Every successful sequence of intrusive pushes, pops and identity deletions preserves a unique chain, matching head and tail, consistent next and queue links, and membership in at most one list."
    source := "base/linked_list.jl:3-13,64-142; queue ownership and endpoint invariants"
    status := .todo, prop := ``LinkedListWellFormed, thm := none, notes := "Prop allows a successful push to retain a stale successor on an unqueued node; its input conditions do not exclude the resulting malformed list." },
  { id := "tasks-coverage-linked-generic", juliaFile := "base/linked_list.jl"
    juliaFns := ["IntrusiveLinkedList", "iterate", "isempty", "length", "list_append!!",
      "push!", "pushfirst!", "pop!", "popfirst!", "list_deletefirst!", "_list_deletefirst!"]
    statement := "The intrusive constructor, iteration, emptiness, length, insertion, removal, identity deletion and append preserve their specified head-to-tail node-chain behavior; self-append and duplicate insertion raise errors."
    source := "base/linked_list.jl:3-143; identity order, queue ownership, and self-append error"
    status := .proven, prop := ``LinkedGenericBodies, thm := some ``JuliaLean.ChatGPT.Batch9.Group17.TasksCoverageLinkedGeneric_proven },
  { id := "linked-list-intrusive-iterate", juliaFile := "base/linked_list.jl"
    juliaFns := ["iterate(q::IntrusiveLinkedList)", "iterate(q::IntrusiveLinkedList{T}, v::T) where {T}"]
    statement := "Iteration returns every inserted node identity exactly once in next-link order and then stops."
    source := "base/linked_list.jl:24-25"
    status := .proven, prop := ``IntrusiveIterationSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.LinkedListIntrusiveIterate },
  { id := "linked-list-intrusive-isempty", juliaFile := "base/linked_list.jl"
    juliaFns := ["isempty(q::IntrusiveLinkedList)", "isempty(qr::ILLRef)"]
    statement := "An intrusive list and its ILLRef report empty exactly when their node chain is empty."
    source := "base/linked_list.jl:27,61"
    status := .proven, prop := ``IntrusiveIsEmptySpec, thm := some ``intrusiveIsEmptySpec_proven },
  { id := "linked-list-intrusive-length", juliaFile := "base/linked_list.jl"
    juliaFns := ["length(q::IntrusiveLinkedList)", "length(qr::ILLRef)"]
    statement := "Intrusive list length counts every reachable node with the source's Int64 counter, equal to the node count when representable and using Int64 wrapping otherwise; ILLRef forwards that count."
    source := "base/linked_list.jl:29-37,62"
    status := .proven, prop := ``IntrusiveLengthSourceSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.intrusiveLengthSourceSpec_proven },
  { id := "linked-list-intrusive-push", juliaFile := "base/linked_list.jl"
    juliaFns := ["push!(qr::ILLRef{T}, val::T) where T", "push!(q::IntrusiveLinkedList{T}, val::T) where T"]
    statement := "push! appends a detached node, sets its queue owner, and preserves the chain; pushing an already queued node errors."
    source := "base/linked_list.jl:64-76,112"
    status := .proven, prop := ``IntrusivePushSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.LinkedListIntrusivePush },
  { id := "linked-list-intrusive-pushfirst", juliaFile := "base/linked_list.jl"
    juliaFns := ["pushfirst!(qr::ILLRef{T}, val::T) where T", "pushfirst!(q::IntrusiveLinkedList{T}, val::T) where T"]
    statement := "pushfirst! prepends a detached node, sets its queue owner, and preserves the chain; pushing an already queued node errors."
    source := "base/linked_list.jl:78-90,113"
    status := .proven, prop := ``IntrusivePushFirstSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.LinkedListIntrusivePushfirst },
  { id := "linked-list-intrusive-pop", juliaFile := "base/linked_list.jl"
    juliaFns := ["pop!(qr::ILLRef{T}) where {T}", "pop!(q::IntrusiveLinkedList{T}) where T"]
    statement := "pop! returns and detaches the tail node while preserving the remaining chain, and errors on an empty list."
    source := "base/linked_list.jl:92-96,114"
    status := .proven, prop := ``IntrusivePopSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group17.LinkedListIntrusivePop_proven },
  { id := "linked-list-intrusive-popfirst", juliaFile := "base/linked_list.jl"
    juliaFns := ["popfirst!(qr::ILLRef{T}) where {T}", "popfirst!(q::IntrusiveLinkedList{T}) where T"]
    statement := "popfirst! returns and detaches the head node while preserving the remaining chain, and errors on an empty list."
    source := "base/linked_list.jl:98-102,115"
    status := .proven, prop := ``IntrusivePopFirstSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.LinkedListIntrusivePopfirst },
  { id := "linked-list-boxed-iterate", juliaFile := "base/linked_list.jl"
    juliaFns := ["iterate(q::LinkedList)",
      "iterate(q::IntrusiveLinkedList{LLT}, v::LLT) where {LLT<:LinkedListItem}"]
    statement := "LinkedList iteration returns every inserted value once in node order and then stops."
    source := "base/linked_list.jl:163-164"
    status := .proven, prop := ``LinkedIterationSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.LinkedListBoxedIterate },
  { id := "linked-list-boxed-isempty", juliaFile := "base/linked_list.jl"
    juliaFns := ["isempty(q::IntrusiveLinkedList)"]
    statement := "A LinkedList reports empty exactly when its value sequence is empty."
    source := "base/linked_list.jl:27"
    status := .proven, prop := ``LinkedIsEmptySpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.LinkedListBoxedIsempty },
  { id := "linked-list-boxed-length", juliaFile := "base/linked_list.jl"
    juliaFns := ["length(q::IntrusiveLinkedList)"]
    statement := "LinkedList length counts every iterated value with the source's Int64 counter, equal to the value count when representable and using Int64 wrapping otherwise."
    source := "base/linked_list.jl:29-37"
    status := .proven, prop := ``LinkedLengthSourceSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.linkedLengthSourceSpec_proven },
  { id := "linked-list-boxed-push", juliaFile := "base/linked_list.jl"
    juliaFns := ["push!(q::LinkedList{T}, val::T) where {T}"]
    statement := "LinkedList push! allocates one fresh item node and appends the value with the correct queue owner."
    source := "base/linked_list.jl:165"
    status := .proven, prop := ``LinkedPushSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.LinkedListBoxedPush },
  { id := "linked-list-boxed-pushfirst", juliaFile := "base/linked_list.jl"
    juliaFns := ["pushfirst!(q::LinkedList{T}, val::T) where {T}"]
    statement := "LinkedList pushfirst! allocates one fresh item node and prepends the value with the correct queue owner."
    source := "base/linked_list.jl:166"
    status := .proven, prop := ``LinkedPushFirstSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.LinkedListBoxedPushfirst },
  { id := "linked-list-boxed-pop", juliaFile := "base/linked_list.jl"
    juliaFns := ["pop!(q::LinkedList)"]
    statement := "LinkedList pop! returns and removes the final value, clears its node links, and errors on an empty list."
    source := "base/linked_list.jl:167"
    status := .proven, prop := ``LinkedPopSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group17.LinkedListBoxedPop_proven },
  { id := "linked-list-boxed-popfirst", juliaFile := "base/linked_list.jl"
    juliaFns := ["popfirst!(q::LinkedList)"]
    statement := "LinkedList popfirst! returns and removes the first value, clears its node links, and errors on an empty list."
    source := "base/linked_list.jl:168"
    status := .proven, prop := ``LinkedPopFirstSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.LinkedListBoxedPopfirst },
]

end JuliaLean.Proofs.base.linked_list

import JuliaLean.base.linked_list
import JuliaLean.Registry.Types

/-!
# Specifications of `base/linked_list.jl`

The registry properties use the linked-list methods in `JuliaLean.base.linked_list`; node identity,
link fields, list endpoints, and wait-entry owner slots remain explicit in the heap.
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
    List ListAction → Except ListFailure (Heap α × InvasiveLinkedList α)
  | [] => .ok (h, q)
  | action :: rest => do
      let (h, q) ← match action with
        | .push node => pushIntrusive h q node
        | .pushfirst node => pushfirstIntrusive h q node
        | .pop => do
            let (h, q, _) ← popIntrusive h q
            pure (h, q)
        | .popfirst => do
            let (h, q, _) ← popfirstIntrusive h q
            pure (h, q)
        | .delete node => listDeleteFirstIntrusive h q node
      runIntrusiveActions h q rest

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
    runIntrusiveActions h q actions = .ok (h', q') →
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
      lengthIntrusive h q = .ok (intrusiveNodes h q).length) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α),
    lengthILLRef h qr = lengthIntrusive h qr.list)

/-- Appending a distinct list concatenates its identities in order, empties the source list,
and transfers each source node's queue owner; appending a list to itself raises an error. -/
def IntrusiveAppendSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (q q2 : InvasiveLinkedList α),
    q.id ≠ q2.id → intrusiveWellFormed h q → intrusiveWellFormed h q2 →
    match appendIntrusive h q q2 with
    | .error _ => False
    | .ok (h', q', q2') =>
        intrusiveWellFormed h' q' ∧ intrusiveWellFormed h' q2' ∧
          intrusiveNodes h' q' = intrusiveNodes h q ++ intrusiveNodes h q2 ∧
          q2'.head = none ∧ q2'.tail = none ∧
          ∀ id ∈ intrusiveNodes h q2,
            ∃ node, h'.node? id = some node ∧ node.queue = some q.id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    appendIntrusive h q q = .error .sameListAppend)

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
    | .error _ => False
    | .ok (h', q', popped) =>
        popped = id ∧ intrusiveWellFormedFor h' q' qr.waitee ∧
          intrusiveNodes h' q' = ids ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (ids : List NodeId) (id : NodeId),
    intrusiveWellFormed h q → intrusiveNodes h q = ids ++ [id] →
    match popIntrusive h q with
    | .error _ => False
    | .ok (h', q', popped) =>
        popped = id ∧ intrusiveWellFormed h' q' ∧
          intrusiveNodes h' q' = ids ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α),
    qr.list.head = none → qr.list.tail = none → popILLRef h qr = .error .typeError) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    q.head = none → q.tail = none → popIntrusive h q = .error .typeError)

/-- Head pops return the former head and detach it. Popping either an empty `ILLRef` or empty
intrusive list raises an error. -/
def IntrusivePopFirstSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId) (rest : List NodeId),
    intrusiveWellFormedFor h qr.list qr.waitee → intrusiveNodes h qr.list = id :: rest →
    match popfirstILLRef h qr with
    | .error _ => False
    | .ok (h', q', popped) =>
        popped = id ∧ intrusiveWellFormedFor h' q' qr.waitee ∧
          intrusiveNodes h' q' = rest ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId) (rest : List NodeId),
    intrusiveWellFormed h q → intrusiveNodes h q = id :: rest →
    match popfirstIntrusive h q with
    | .error _ => False
    | .ok (h', q', popped) =>
        popped = id ∧ intrusiveWellFormed h' q' ∧
          intrusiveNodes h' q' = rest ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α),
    qr.list.head = none → qr.list.tail = none → popfirstILLRef h qr = .error .typeError) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α),
    q.head = none → q.tail = none → popfirstIntrusive h q = .error .typeError)

/-- Identity deletion removes exactly the selected node and clears its links. `ILLRef` deletion is
a no-op precisely when the node's `queue` does not name that reference's waitee. -/
def IntrusiveDeleteSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId) (node : HeapNode α),
    h.node? id = some node → node.queue ≠ some qr.waitee →
      listDeleteFirstILLRef h qr id = .ok (h, qr.list)) ∧
  (∀ {α : Type} (h : Heap α) (qr : ILLRef α) (id : NodeId),
    intrusiveWellFormedFor h qr.list qr.waitee → id ∈ intrusiveNodes h qr.list →
    match listDeleteFirstILLRef h qr id with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormedFor h' q' qr.waitee ∧
          intrusiveNodes h' q' = (intrusiveNodes h qr.list).erase id ∧ clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId),
    intrusiveWellFormed h q → id ∈ intrusiveNodes h q →
    match listDeleteFirstIntrusive h q id with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormed h' q' ∧ intrusiveNodes h' q' = (intrusiveNodes h q).erase id ∧
          clearLinksAndOwner h' id) ∧
  (∀ {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (id : NodeId),
    intrusiveWellFormed h q → id ∈ intrusiveNodes h q →
    match deleteFirstIntrusive h q id with
    | .error _ => False
    | .ok (h', q') =>
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
    intrusiveWellFormed h q → linkedValues h q = .ok values → linkedIteration h q = .ok values

/-- The generic empty and length methods agree with the boxed value sequence. -/
def LinkedIsEmptySpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α),
    intrusiveWellFormed h q → linkedValues h q = .ok values →
      isemptyIntrusive q = decide (values = [])

def LinkedLengthSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α),
    intrusiveWellFormed h q → linkedValues h q = .ok values →
      lengthIntrusive h q = .ok values.length

/-- Appending two boxed lists preserves their value order and empties the source list. -/
def LinkedAppendSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q q2 : LinkedList α) (values values2 : List α),
    q.id ≠ q2.id → intrusiveWellFormed h q → intrusiveWellFormed h q2 →
    linkedValues h q = .ok values → linkedValues h q2 = .ok values2 →
    match appendIntrusive h q q2 with
    | .error _ => False
    | .ok (h', q', q2') =>
        intrusiveWellFormed h' q' ∧ linkedValues h' q' = .ok (values ++ values2) ∧
          q2'.head = none ∧ q2'.tail = none ∧
          ∀ id ∈ intrusiveNodes h q2,
            ∃ node, h'.node? id = some node ∧ node.queue = some q.id

/-- Boxed `push!` allocates one fresh item node and appends its value and owner link. -/
def LinkedPushSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α) (value : α),
    intrusiveWellFormed h q → linkedValues h q = .ok values → h.node? h.nextNode = none →
    match pushLinked h q value with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormed h' q' ∧ linkedValues h' q' = .ok (values ++ [value]) ∧
          intrusiveNodes h' q' = intrusiveNodes h q ++ [h.nextNode] ∧
          h'.nodes.length = h.nodes.length + 1 ∧
          (∃ node, h'.node? h.nextNode = some node ∧ node.value = value ∧
            node.queue = some q.id ∧ node.next = none)

/-- Boxed `pushfirst!` allocates one fresh item node and prepends its value and owner link. -/
def LinkedPushFirstSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α) (value : α),
    intrusiveWellFormed h q → linkedValues h q = .ok values → h.node? h.nextNode = none →
    match pushfirstLinked h q value with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormed h' q' ∧ linkedValues h' q' = .ok (value :: values) ∧
          intrusiveNodes h' q' = h.nextNode :: intrusiveNodes h q ∧
          h'.nodes.length = h.nodes.length + 1 ∧
          (∃ node, h'.node? h.nextNode = some node ∧ node.value = value ∧
            node.queue = some q.id)

/-- Boxed tail pop returns and removes the final value, and errors on an empty list. -/
def LinkedPopSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (q : LinkedList α) (values rest : List α) (last : α),
    intrusiveWellFormed h q → linkedValues h q = .ok values → values = rest ++ [last] →
    match popLinked h q with
    | .error _ => False
    | .ok (h', q', value) =>
        value = last ∧ intrusiveWellFormed h' q' ∧ linkedValues h' q' = .ok rest ∧
          ∃ id node, q.tail = some id ∧ h'.node? id = some node ∧
            node.next = none ∧ node.queue = none) ∧
  (∀ {α : Type} (h : Heap α) (q : LinkedList α),
    q.head = none → q.tail = none → popLinked h q = .error .typeError)

/-- Boxed head pop returns and removes the first value, and errors on an empty list. -/
def LinkedPopFirstSpec : Prop :=
  (∀ {α : Type} (h : Heap α) (q : LinkedList α) (first : α) (rest : List α),
    intrusiveWellFormed h q → linkedValues h q = .ok (first :: rest) →
    match popfirstLinked h q with
    | .error _ => False
    | .ok (h', q', value) =>
        value = first ∧ intrusiveWellFormed h' q' ∧ linkedValues h' q' = .ok rest ∧
          ∃ id node, q.head = some id ∧ h'.node? id = some node ∧
            node.next = none ∧ node.queue = none) ∧
  (∀ {α : Type} (h : Heap α) (q : LinkedList α),
    q.head = none → q.tail = none → popfirstLinked h q = .error .typeError)

/-- Boxed value deletion removes only the first value accepted by Julia's `isequal` predicate. -/
def LinkedDeleteSpec : Prop :=
  ∀ {α : Type} (h : Heap α) (q : LinkedList α) (values : List α)
    (same : α → α → Bool) (value : α),
    intrusiveWellFormed h q → linkedValues h q = .ok values →
    match listDeleteFirstLinked h q same value with
    | .error _ => False
    | .ok (h', q') =>
        intrusiveWellFormed h' q' ∧ linkedValues h' q' = .ok (eraseFirstBy same value values)

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
      | .error _ => False
      | .ok (h', q', popped) =>
          popped = id ∧ waitEntryWellFormed ops h' q' qr.waitee ∧
            waitEntryNodes ops h' q' qr.waitee = ids ∧ ops.findSlot h' id qr.waitee = 0 ∧
            releasedWaitSlot ops h h' id qr.waitee ∧ otherOwnersPreserved h h' qr.waitee) ∧
  (∀ (h : Heap α) (qr : ILLRef α),
    qr.list.tail = none → popWaitEntry ops h qr = .error .typeError) ∧
  (∀ (h : Heap α) (qr : ILLRef α) (id : NodeId),
    waitEntryWellFormed ops h qr.list qr.waitee → id ∈ waitEntryNodes ops h qr.list qr.waitee →
      match deleteWaitEntry ops h qr id with
      | .error _ => False
      | .ok (h', q') =>
          waitEntryWellFormed ops h' q' qr.waitee ∧
            waitEntryNodes ops h' q' qr.waitee = (waitEntryNodes ops h qr.list qr.waitee).erase id ∧
            ops.findSlot h' id qr.waitee = 0 ∧ releasedWaitSlot ops h h' id qr.waitee ∧
            otherOwnersPreserved h h' qr.waitee) ∧
  (∀ (h : Heap α) (qr : ILLRef α) (id : NodeId),
    ops.findSlot h id qr.waitee = 0 → deleteWaitEntry ops h qr id = .ok (h, qr.list)) ∧
  (∀ (h : Heap α) (qr : ILLRef α),
    waitEntryWellFormed ops h qr.list qr.waitee →
      lengthWaitEntry ops h qr = .ok (waitEntryNodes ops h qr.list qr.waitee).length ∧
      waitQueueIsEmpty ops h qr =
        .ok (!(waitEntryNodes ops h qr.list qr.waitee).any (waitingEntryArmed h)))

/-! Nothing to promise:
waitqueue@17: this declares a generic function; concrete waitee types supply methods elsewhere.
eltype@22: the concrete type or Any result is its complete behavior and is mirrored directly.
eltype@162: the concrete type or Any result is its complete behavior and is mirrored directly.
-/

def entries : List Entry := [
  { id := "tasks-linked-list-wellformed", juliaFile := "base/linked_list.jl"
    juliaFns := ["push!(::ILLRef)", "pushfirst!(::ILLRef)", "pop!(::ILLRef)",
      "popfirst!(::ILLRef)", "list_deletefirst!(::ILLRef)", "_list_deletefirst!"]
    statement := "Every successful sequence of intrusive pushes, pops and identity deletions preserves a unique chain, matching head and tail, consistent next and queue links, and membership in at most one list."
    source := "base/linked_list.jl:3-13,64-142; queue ownership and endpoint invariants"
    status := .todo, prop := ``LinkedListWellFormed, thm := none },
  { id := "tasks-coverage-linked-generic", juliaFile := "base/linked_list.jl"
    juliaFns := ["IntrusiveLinkedList", "iterate", "isempty", "length", "list_append!!",
      "push!", "pushfirst!", "pop!", "popfirst!", "list_deletefirst!", "_list_deletefirst!"]
    statement := "The intrusive constructor, iteration, emptiness, length, insertion, removal, identity deletion and append preserve their specified head-to-tail node-chain behavior; self-append and duplicate insertion raise errors."
    source := "base/linked_list.jl:3-143; identity order, queue ownership, and self-append error"
    status := .todo, prop := ``LinkedGenericBodies, thm := none },
  { id := "tasks-coverage-linked-boxed", juliaFile := "base/linked_list.jl"
    juliaFns := ["LinkedListItem", "LinkedList iterate", "LinkedList push!",
      "LinkedList pushfirst!", "LinkedList pop!", "LinkedList popfirst!", "LinkedList list_deletefirst!"]
    statement := "LinkedList insertion allocates one fresh node per value, iteration follows node order, end pops return and remove the corresponding value, and deletion removes only the first isequal value."
    source := "base/linked_list.jl:152-179; adapter and first-isequal deletion behavior"
    status := .todo, prop := ``LinkedBoxedBodies, thm := none },
  { id := "tasks-coverage-linked-waitentry", juliaFile := "base/linked_list.jl"
    juliaFns := ["WaitEntry push!", "WaitEntry pushfirst!", "WaitEntry pop!", "WaitEntry popfirst!",
      "WaitEntry list_deletefirst!", "WaitEntry length", "_waitq_isempty"]
    statement := "For external cancellation slot operations satisfying their fixed-slot laws, WaitEntry methods preserve each owner's chain, propagate slot overflow, raise TypeError on an empty-list pop, clear released owner/next/aux fields in place, and report whether a linked task is still waiting."
    source := "base/linked_list.jl:181-293; owner-specific slot and armed-task invariants"
    status := .todo, prop := ``LinkedWaitEntryBodies, thm := none },
  { id := "linked-list-intrusive-constructor", juliaFile := "base/linked_list.jl"
    juliaFns := ["IntrusiveLinkedList{T}() where {T}"]
    statement := "A newly constructed intrusive list is empty, satisfies the chain and owner invariant, and has no iterator item."
    source := "base/linked_list.jl:3-8"
    status := .todo, prop := ``IntrusiveConstructorSpec, thm := none },
  { id := "linked-list-intrusive-iterate", juliaFile := "base/linked_list.jl"
    juliaFns := ["iterate(q::IntrusiveLinkedList)", "iterate(q::IntrusiveLinkedList{T}, v::T) where {T}"]
    statement := "Iteration returns every inserted node identity exactly once in next-link order and then stops."
    source := "base/linked_list.jl:24-25"
    status := .todo, prop := ``IntrusiveIterationSpec, thm := none },
  { id := "linked-list-intrusive-isempty", juliaFile := "base/linked_list.jl"
    juliaFns := ["isempty(q::IntrusiveLinkedList)", "isempty(qr::ILLRef)"]
    statement := "An intrusive list and its ILLRef report empty exactly when their node chain is empty."
    source := "base/linked_list.jl:27,61"
    status := .todo, prop := ``IntrusiveIsEmptySpec, thm := none },
  { id := "linked-list-intrusive-length", juliaFile := "base/linked_list.jl"
    juliaFns := ["length(q::IntrusiveLinkedList)", "length(qr::ILLRef)"]
    statement := "Intrusive list length equals the number of nodes reachable from its head, and ILLRef length forwards that count."
    source := "base/linked_list.jl:29-37,62"
    status := .todo, prop := ``IntrusiveLengthSpec, thm := none },
  { id := "linked-list-intrusive-append", juliaFile := "base/linked_list.jl"
    juliaFns := ["list_append!!(q::IntrusiveLinkedList{T}, q2::IntrusiveLinkedList{T}) where T"]
    statement := "Appending a distinct list concatenates node order, empties the source, and transfers source nodes to the destination queue; self-append errors."
    source := "base/linked_list.jl:39-59"
    status := .todo, prop := ``IntrusiveAppendSpec, thm := none },
  { id := "linked-list-intrusive-push", juliaFile := "base/linked_list.jl"
    juliaFns := ["push!(qr::ILLRef{T}, val::T) where T", "push!(q::IntrusiveLinkedList{T}, val::T) where T"]
    statement := "push! appends a detached node, sets its queue owner, and preserves the chain; pushing an already queued node errors."
    source := "base/linked_list.jl:64-76,112"
    status := .todo, prop := ``IntrusivePushSpec, thm := none },
  { id := "linked-list-intrusive-pushfirst", juliaFile := "base/linked_list.jl"
    juliaFns := ["pushfirst!(qr::ILLRef{T}, val::T) where T", "pushfirst!(q::IntrusiveLinkedList{T}, val::T) where T"]
    statement := "pushfirst! prepends a detached node, sets its queue owner, and preserves the chain; pushing an already queued node errors."
    source := "base/linked_list.jl:78-90,113"
    status := .todo, prop := ``IntrusivePushFirstSpec, thm := none },
  { id := "linked-list-intrusive-pop", juliaFile := "base/linked_list.jl"
    juliaFns := ["pop!(qr::ILLRef{T}) where {T}", "pop!(q::IntrusiveLinkedList{T}) where T"]
    statement := "pop! returns and detaches the tail node while preserving the remaining chain, and errors on an empty list."
    source := "base/linked_list.jl:92-96,114"
    status := .todo, prop := ``IntrusivePopSpec, thm := none },
  { id := "linked-list-intrusive-popfirst", juliaFile := "base/linked_list.jl"
    juliaFns := ["popfirst!(qr::ILLRef{T}) where {T}", "popfirst!(q::IntrusiveLinkedList{T}) where T"]
    statement := "popfirst! returns and detaches the head node while preserving the remaining chain, and errors on an empty list."
    source := "base/linked_list.jl:98-102,115"
    status := .todo, prop := ``IntrusivePopFirstSpec, thm := none },
  { id := "linked-list-intrusive-delete", juliaFile := "base/linked_list.jl"
    juliaFns := ["list_deletefirst!(qr::ILLRef{T}, val::T) where T",
      "list_deletefirst!(q::IntrusiveLinkedList{T}, val::T) where T", "_list_deletefirst!"]
    statement := "Identity deletion removes the selected node, reconnects its neighbors and clears its next and queue fields; an ILLRef with a different owner is a no-op."
    source := "base/linked_list.jl:104-110,116-143"
    status := .todo, prop := ``IntrusiveDeleteSpec, thm := none },
  { id := "linked-list-boxed-constructor", juliaFile := "base/linked_list.jl"
    juliaFns := ["LinkedListItem{T}(value::T) where {T}"]
    statement := "LinkedListItem construction allocates one fresh node with the input value and empty next and queue links."
    source := "base/linked_list.jl:152-158"
    status := .todo, prop := ``LinkedItemConstructionSpec, thm := none },
  { id := "linked-list-boxed-iterate", juliaFile := "base/linked_list.jl"
    juliaFns := ["iterate(q::LinkedList)",
      "iterate(q::IntrusiveLinkedList{LLT}, v::LLT) where {LLT<:LinkedListItem}"]
    statement := "LinkedList iteration returns every inserted value once in node order and then stops."
    source := "base/linked_list.jl:163-164"
    status := .todo, prop := ``LinkedIterationSpec, thm := none },
  { id := "linked-list-boxed-isempty", juliaFile := "base/linked_list.jl"
    juliaFns := ["isempty(q::IntrusiveLinkedList)"]
    statement := "A LinkedList reports empty exactly when its value sequence is empty."
    source := "base/linked_list.jl:27"
    status := .todo, prop := ``LinkedIsEmptySpec, thm := none },
  { id := "linked-list-boxed-length", juliaFile := "base/linked_list.jl"
    juliaFns := ["length(q::IntrusiveLinkedList)"]
    statement := "A LinkedList length equals the number of values yielded by iteration."
    source := "base/linked_list.jl:29-37"
    status := .todo, prop := ``LinkedLengthSpec, thm := none },
  { id := "linked-list-boxed-append", juliaFile := "base/linked_list.jl"
    juliaFns := ["list_append!!(q::IntrusiveLinkedList{LinkedListItem{T}}, q2::IntrusiveLinkedList{LinkedListItem{T}}) where T"]
    statement := "Appending one LinkedList to another concatenates their values in order and empties the source list."
    source := "base/linked_list.jl:39-59,152-159"
    status := .todo, prop := ``LinkedAppendSpec, thm := none },
  { id := "linked-list-boxed-push", juliaFile := "base/linked_list.jl"
    juliaFns := ["push!(q::LinkedList{T}, val::T) where {T}"]
    statement := "LinkedList push! allocates one fresh item node and appends the value with the correct queue owner."
    source := "base/linked_list.jl:165"
    status := .todo, prop := ``LinkedPushSpec, thm := none },
  { id := "linked-list-boxed-pushfirst", juliaFile := "base/linked_list.jl"
    juliaFns := ["pushfirst!(q::LinkedList{T}, val::T) where {T}"]
    statement := "LinkedList pushfirst! allocates one fresh item node and prepends the value with the correct queue owner."
    source := "base/linked_list.jl:166"
    status := .todo, prop := ``LinkedPushFirstSpec, thm := none },
  { id := "linked-list-boxed-pop", juliaFile := "base/linked_list.jl"
    juliaFns := ["pop!(q::LinkedList)"]
    statement := "LinkedList pop! returns and removes the final value, clears its node links, and errors on an empty list."
    source := "base/linked_list.jl:167"
    status := .todo, prop := ``LinkedPopSpec, thm := none },
  { id := "linked-list-boxed-popfirst", juliaFile := "base/linked_list.jl"
    juliaFns := ["popfirst!(q::LinkedList)"]
    statement := "LinkedList popfirst! returns and removes the first value, clears its node links, and errors on an empty list."
    source := "base/linked_list.jl:168"
    status := .todo, prop := ``LinkedPopFirstSpec, thm := none },
  { id := "linked-list-boxed-delete", juliaFile := "base/linked_list.jl"
    juliaFns := ["list_deletefirst!(q::LinkedList{T}, val::T) where T"]
    statement := "LinkedList deletion removes only the first value for which isequal is true and preserves the remaining order."
    source := "base/linked_list.jl:169-179"
    status := .todo, prop := ``LinkedDeleteSpec, thm := none }
]

end JuliaLean.Proofs.base.linked_list

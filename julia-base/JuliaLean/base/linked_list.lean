import JuliaLean.Core

/-!
# Model of `base/linked_list.jl`

List and node mutation is represented by threading an explicit heap through each call. Node
identities are `Nat`; the heap stores each node's payload, `next` link, single-list `queue` owner,
and owner-specific wait-entry slots. List handles retain Julia's object identity and mutable head
and tail fields.
-/

namespace JuliaLean.base.linked_list

abbrev NodeId := Nat
abbrev ListId := Nat
abbrev OwnerId := Nat
abbrev TaskId := Nat
inductive JuliaTypeDescriptor : Type 1 where
  | any
  | concrete (element : Type)


inductive ListFailure where
  | missingNode
  | typeError
  | alreadyQueued
  | alreadyInWaitList
  | missingSlot
  /-- `ConcurrencyViolationError` from cancellation.jl's `_slot_overflow_error`. -/
  | slotOverflow
  | sameListAppend
  deriving Repr, DecidableEq

structure WaitSlot where
  owner : Option OwnerId
  next : Option NodeId
  aux : BitVec 64
  deriving Repr, DecidableEq

structure HeapNode (α : Type) where
  next : Option NodeId
  queue : Option OwnerId
  value : α
  slots : List WaitSlot
  task : Option TaskId

structure Heap (α : Type) where
  nodes : List (NodeId × HeapNode α)
  nextNode : NodeId
  nextList : ListId
  tasksWaitingOn : List (TaskId × Option NodeId)

/-- Callees from `base/cancellation.jl`; each entry's slot count stays fixed. -/
structure WaitEntryOps (α : Type) where
  findSlot : Heap α → NodeId → OwnerId → Nat
  acquireSlot : Heap α → NodeId → OwnerId → Except ListFailure (Heap α × Nat)
  releaseSlot : Heap α → NodeId → Nat → Heap α
  slotNext : Heap α → NodeId → Nat → Option NodeId
  setSlotNext : Heap α → NodeId → Nat → Option NodeId → Heap α
  nextOn : Heap α → NodeId → OwnerId → Option NodeId

namespace Heap

def empty : Heap α := ⟨[], 0, 0, []⟩

def node? (h : Heap α) (id : NodeId) : Option (HeapNode α) :=
  (h.nodes.find? (fun entry => entry.1 == id)).map Prod.snd

def setNode (h : Heap α) (id : NodeId) (node : HeapNode α) : Heap α :=
  let nodes := h.nodes.filter (fun entry => entry.1 != id)
  { h with nodes := nodes ++ [(id, node)] }

def lookupTask (tasks : List (TaskId × Option NodeId)) (id : TaskId) : Option (Option NodeId) :=
  (tasks.find? (fun entry => entry.1 == id)).map Prod.snd

def setTask (h : Heap α) (id : TaskId) (waitingOn : Option NodeId) : Heap α :=
  let tasks := h.tasksWaitingOn.filter (fun entry => entry.1 != id)
  { h with tasksWaitingOn := tasks ++ [(id, waitingOn)] }

def allocateNode (h : Heap α) (value : α) : Heap α × NodeId :=
  let id := h.nextNode
  let node : HeapNode α := ⟨none, none, value, [], none⟩
  ({ (setNode h id node) with nextNode := id + 1 }, id)

end Heap

structure InvasiveLinkedList (α : Type) where
  id : ListId
  head : Option NodeId
  tail : Option NodeId

structure LinkedListItem (α : Type) where
  id : NodeId
  deriving Repr, DecidableEq
/--
Julia source: base/linked_list.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const LinkedList{T} = IntrusiveLinkedList{LinkedListItem{T}}
```
-/
abbrev LinkedList (α : Type) := InvasiveLinkedList α


structure ILLRef (α : Type) where
  list : InvasiveLinkedList α
  waitee : OwnerId

private def lookupNode {α : Type} (h : Heap α) (id : NodeId) : Except ListFailure (HeapNode α) :=
  match h.node? id with
  | some node => .ok node
  | none => .error .missingNode

private def setNodeField {α : Type} (h : Heap α) (id : NodeId)
    (f : HeapNode α → HeapNode α) : Except ListFailure (Heap α) := do
  let node ← lookupNode h id
  pure (h.setNode id (f node))

private def nodeNext {α : Type} (h : Heap α) (id : NodeId) : Option NodeId :=
  ((h.node? id).map HeapNode.next).join


def slotAt : List WaitSlot → Nat → Option WaitSlot
  | _, 0 => none
  | [], _ => none
  | slot :: _, 1 => some slot
  | _ :: rest, index + 1 => slotAt rest index

def setSlotAt : List WaitSlot → Nat → WaitSlot → Option (List WaitSlot)
  | _, 0, _ => none
  | [], _, _ => none
  | _ :: rest, 1, slot => some (slot :: rest)
  | first :: rest, index + 1, slot =>
      (setSlotAt rest index slot).map (fun changed => first :: changed)

private def ownerLinks {α : Type} (ops : WaitEntryOps α) (h : Heap α) :
    Option NodeId → OwnerId → Nat → List NodeId
  | _, _, 0 => []
  | none, _, _ => []
  | some id, owner, fuel + 1 => id :: ownerLinks ops h (ops.nextOn h id owner) owner fuel

private def nodeLinks {α : Type} (h : Heap α) : Option NodeId → Nat → List NodeId
  | _, 0 => []
  | none, _ => []
  | some id, fuel + 1 => id :: nodeLinks h (nodeNext h id) fuel

def intrusiveNodes {α : Type} (h : Heap α) (q : InvasiveLinkedList α) : List NodeId :=
  nodeLinks h q.head (h.nodes.length + 1)

def waitEntryNodes {α : Type} (ops : WaitEntryOps α) (h : Heap α)
    (q : InvasiveLinkedList α) (owner : OwnerId) : List NodeId :=
  ownerLinks ops h q.head owner (h.nodes.length + 1)

def intrusiveWellFormedFor {α : Type} (h : Heap α) (q : InvasiveLinkedList α)
    (owner : OwnerId) : Prop :=
  (h.nodes.map (fun entry => entry.1)).Nodup ∧
  (q.head.isNone ↔ q.tail.isNone) ∧
    let ids := intrusiveNodes h q
    ids.Nodup ∧ ids.getLast? = q.tail ∧
      (∀ id ∈ ids, ∃ node, h.node? id = some node ∧ node.queue = some owner) ∧
      (∀ id node, (id, node) ∈ h.nodes → node.queue = some owner → id ∈ ids)

def intrusiveWellFormed {α : Type} (h : Heap α) (q : InvasiveLinkedList α) : Prop :=
  intrusiveWellFormedFor h q q.id

def detachedNode {α : Type} (h : Heap α) (id : NodeId) : Prop :=
  ∃ node, h.node? id = some node ∧ node.next = none ∧ node.queue = none

def waitEntryHeapWellFormed {α : Type} (h : Heap α) : Prop :=
  (h.nodes.map (fun entry => entry.1)).Nodup ∧
    ∀ id node, (id, node) ∈ h.nodes →
      (node.slots.filterMap WaitSlot.owner).Nodup ∧
        ∀ slot ∈ node.slots, slot.owner = none → slot.next = none ∧ slot.aux = 0

def waitEntryWellFormed {α : Type} (ops : WaitEntryOps α) (h : Heap α)
    (q : InvasiveLinkedList α) (owner : OwnerId) : Prop :=
  waitEntryHeapWellFormed h ∧
  (q.head.isNone ↔ q.tail.isNone) ∧
    let ids := waitEntryNodes ops h q owner
    ids.Nodup ∧ ids.getLast? = q.tail ∧
      (∀ id ∈ ids, ∃ node, h.node? id = some node ∧ ops.findSlot h id owner ≠ 0) ∧
      (∀ id node, (id, node) ∈ h.nodes → ops.findSlot h id owner ≠ 0 → id ∈ ids)


private partial def setQueueAlong {α : Type} (h : Heap α) (head : Option NodeId)
    (owner : OwnerId) : Except ListFailure (Heap α) := do
  match head with
  | none => pure h
  | some id =>
      let node ← lookupNode h id
      let h := h.setNode id { node with queue := some owner }
      setQueueAlong h node.next owner

/--
Julia source: base/linked_list.jl:3-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct IntrusiveLinkedList{T}
    # Invasive list requires that T have a field `.next >: U{T, Nothing}` and `.queue::Any`
    head::Union{T, Nothing}
    tail::Union{T, Nothing}
    IntrusiveLinkedList{T}() where {T} = new{T}(nothing, nothing)
end
```
-/
def newIntrusiveLinkedList {α : Type} (h : Heap α) : Heap α × InvasiveLinkedList α :=
  let id := h.nextList
  ({ h with nextList := id + 1 }, ⟨id, none, none⟩)

/--
Julia source: base/linked_list.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:IntrusiveLinkedList{T}}) where {T} = @isdefined(T) ? T : Any
```
-/
def intrusiveElementType (elementType : Option Type) : JuliaTypeDescriptor :=
  match elementType with
  | some α => .concrete α
  | none => .any

/--
Julia source: base/linked_list.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(q::IntrusiveLinkedList) = (h = q.head; h === nothing ? nothing : (h, h))
```
-/
def iterateIntrusiveStart {α : Type} (q : InvasiveLinkedList α) : Option (NodeId × NodeId) :=
  match q.head with
  | none => none
  | some head => some (head, head)

/--
Julia source: base/linked_list.jl:25-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(q::IntrusiveLinkedList{T}, v::T) where {T} = (h = v.next; h === nothing ? nothing : (h, h))
```
-/
def iterateIntrusiveNext {α : Type} (h : Heap α) (v : NodeId) :
    Except ListFailure (Option (NodeId × NodeId)) := do
  let node ← lookupNode h v
  pure (node.next.map (fun next => (next, next)))

/--
Julia source: base/linked_list.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(q::IntrusiveLinkedList) = (q.head === nothing)
```
-/
def isemptyIntrusive {α : Type} (q : InvasiveLinkedList α) : Bool := q.head.isNone

/--
Julia source: base/linked_list.jl:29-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(q::IntrusiveLinkedList)
    i = 0
    head = q.head
    while head !== nothing
        i += 1
        head = head.next
    end
    return i
end
```
-/
partial def lengthIntrusive {α : Type} (h : Heap α) (q : InvasiveLinkedList α) :
    Except ListFailure Nat := do
  let mut i := 0
  let mut head := q.head
  while head.isSome do
    let id := head.get!
    let node ← lookupNode h id
    i := i + 1
    head := node.next
  pure i

/--
Julia source: base/linked_list.jl:39-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function list_append!!(q::IntrusiveLinkedList{T}, q2::IntrusiveLinkedList{T}) where T
    q === q2 && error("can't append list to itself")
    head2 = q2.head
    if head2 !== nothing
        tail2 = q2.tail::T
        q2.head = nothing
        q2.tail = nothing
        tail = q.tail
        q.tail = tail2
        if tail === nothing
            q.head = head2
        else
            tail.next = head2
        end
        while head2 !== nothing
            head2.queue = q
            head2 = head2.next
        end
    end
    return q
end
```
-/
def appendIntrusive {α : Type} (h : Heap α) (q q2 : InvasiveLinkedList α) :
    Except ListFailure (Heap α × InvasiveLinkedList α × InvasiveLinkedList α) := do
  if q.id == q2.id then throw .sameListAppend
  match q2.head with
  | none => pure (h, q, q2)
  | some head2 =>
      let tail2 ← match q2.tail with
        | none => throw .typeError
        | some tail2 => pure tail2
      let q2 := { q2 with head := none, tail := none }
      let tail := q.tail
      let q := { q with tail := some tail2 }
      let (h, q) ← match tail with
        | none => pure (h, { q with head := some head2 })
        | some tail => do
            let h ← setNodeField h tail (fun node => { node with next := some head2 })
            pure (h, q)
      let h ← setQueueAlong h (some head2) q.id
      pure (h, q, q2)

/--
Julia source: base/linked_list.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(qr::ILLRef) = isempty(qr.list)
```
-/
def isemptyILLRef {α : Type} (qr : ILLRef α) : Bool := isemptyIntrusive qr.list

/--
Julia source: base/linked_list.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(qr::ILLRef) = length(qr.list)
```
-/
partial def lengthILLRef {α : Type} (h : Heap α) (qr : ILLRef α) : Except ListFailure Nat :=
  lengthIntrusive h qr.list

/--
Julia source: base/linked_list.jl:64-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(qr::ILLRef{T}, val::T) where T
    val.queue === nothing || error("val already in a list")
    val.queue = qr.waitee
    q = qr.list
    tail = q.tail
    if tail === nothing
        q.head = q.tail = val
    else
        tail.next = val
        q.tail = val
    end
    return q
end
```
-/
def pushILLRef {α : Type} (h : Heap α) (qr : ILLRef α) (val : NodeId) :
    Except ListFailure (Heap α × InvasiveLinkedList α) := do
  let node ← lookupNode h val
  if node.queue.isSome then throw .alreadyQueued
  let h := h.setNode val { node with queue := some qr.waitee }
  let q := qr.list
  let tail := q.tail
  match tail with
  | none => pure (h, { q with head := some val, tail := some val })
  | some tail =>
      let h ← setNodeField h tail (fun node => { node with next := some val })
      pure (h, { q with tail := some val })

/--
Julia source: base/linked_list.jl:78-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pushfirst!(qr::ILLRef{T}, val::T) where T
    val.queue === nothing || error("val already in a list")
    val.queue = qr.waitee
    q = qr.list
    head = q.head
    if head === nothing
        q.head = q.tail = val
    else
        val.next = head
        q.head = val
    end
    return q
end
```
-/
def pushfirstILLRef {α : Type} (h : Heap α) (qr : ILLRef α) (val : NodeId) :
    Except ListFailure (Heap α × InvasiveLinkedList α) := do
  let node ← lookupNode h val
  if node.queue.isSome then throw .alreadyQueued
  let h := h.setNode val { node with queue := some qr.waitee }
  let q := qr.list
  let head := q.head
  match head with
  | none => pure (h, { q with head := some val, tail := some val })
  | some head => do
      let h ← setNodeField h val (fun node => { node with next := some head })
      pure (h, { q with head := some val })

/--
Julia source: base/linked_list.jl:118-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# this function assumes `val` is found in `q`
function _list_deletefirst!(q::IntrusiveLinkedList{T}, val::T) where T
    head = q.head::T
    if head === val
        if q.tail::T === val
            q.head = q.tail = nothing
        else
            q.head = val.next::T
        end
    else
        head_next = head.next::T
        while head_next !== val
            head = head_next
            head_next = head.next::T
        end
        if q.tail::T === val
            head.next = nothing
            q.tail = head
        else
            head.next = val.next::T
        end
    end
    val.next = nothing
    val.queue = nothing
    return q
end
```
-/
partial def deleteFirstIntrusive {α : Type} (h : Heap α) (q : InvasiveLinkedList α)
    (val : NodeId) : Except ListFailure (Heap α × InvasiveLinkedList α) := do
  let mut heap := h
  let mut list := q
  let mut head ← match list.head with
    | none => throw .typeError
    | some head => pure head
  if head == val then
    let tail ← match list.tail with
      | none => throw .typeError
      | some tail => pure tail
    if tail == val then
      list := { list with head := none, tail := none }
    else
      let node ← lookupNode heap val
      let next ← match node.next with
        | none => throw .typeError
        | some next => pure next
      list := { list with head := some next }
  else
    let node ← lookupNode heap head
    let mut headNext ← match node.next with
      | none => throw .typeError
      | some next => pure next
    while headNext != val do
      head := headNext
      let node ← lookupNode heap head
      let next ← match node.next with
        | none => throw .typeError
        | some next => pure next
      headNext := next
    let tail ← match list.tail with
      | none => throw .typeError
      | some tail => pure tail
    if tail == val then
      let changed ← setNodeField heap head (fun node => { node with next := none })
      heap := changed
      list := { list with tail := some head }
    else
      let node ← lookupNode heap val
      let next ← match node.next with
        | none => throw .typeError
        | some next => pure next
      let changed ← setNodeField heap head (fun node => { node with next := some next })
      heap := changed
  let heapAfterNext ← setNodeField heap val (fun node => { node with next := none })
  let heapAfterQueue ← setNodeField heapAfterNext val (fun node => { node with queue := none })
  pure (heapAfterQueue, list)

/--
Julia source: base/linked_list.jl:92-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(qr::ILLRef{T}) where {T}
    val = qr.list.tail::T
    _list_deletefirst!(qr.list, val) # expensive!
    return val
end
```
-/
def popILLRef {α : Type} (h : Heap α) (qr : ILLRef α) :
    Except ListFailure (Heap α × InvasiveLinkedList α × NodeId) := do
  let val ← match qr.list.tail with
    | none => throw .typeError
    | some val => pure val
  let (h, q) ← deleteFirstIntrusive h qr.list val
  pure (h, q, val)

/--
Julia source: base/linked_list.jl:98-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function popfirst!(qr::ILLRef{T}) where {T}
    val = qr.list.head::T
    _list_deletefirst!(qr.list, val) # cheap
    return val
end
```
-/
def popfirstILLRef {α : Type} (h : Heap α) (qr : ILLRef α) :
    Except ListFailure (Heap α × InvasiveLinkedList α × NodeId) := do
  let val ← match qr.list.head with
    | none => throw .typeError
    | some val => pure val
  let (h, q) ← deleteFirstIntrusive h qr.list val
  pure (h, q, val)

/--
Julia source: base/linked_list.jl:104-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Delete `val` from the list, but only if it is actually in it, as witnessed by
# `val.queue` holding the ILLRef's waitee. This makes deletion a no-op if `val`
# was concurrently popped, which various cleanup paths rely upon.
function list_deletefirst!(qr::ILLRef{T}, val::T) where T
    val.queue === qr.waitee || return qr.list
    return _list_deletefirst!(qr.list, val)
end
```
-/
def listDeleteFirstILLRef {α : Type} (h : Heap α) (qr : ILLRef α) (val : NodeId) :
    Except ListFailure (Heap α × InvasiveLinkedList α) := do
  let node ← lookupNode h val
  if node.queue != some qr.waitee then pure (h, qr.list)
  else deleteFirstIntrusive h qr.list val

/--
Julia source: base/linked_list.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(q::IntrusiveLinkedList{T}, val::T) where T = push!(ILLRef(q, q), val)
```
-/
def pushIntrusive {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (val : NodeId) :
    Except ListFailure (Heap α × InvasiveLinkedList α) :=
  match pushILLRef h ⟨q, q.id⟩ val with
  | .ok (h, q) => .ok (h, q)
  | .error error => .error error

/--
Julia source: base/linked_list.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pushfirst!(q::IntrusiveLinkedList{T}, val::T) where T = pushfirst!(ILLRef(q, q), val)
```
-/
def pushfirstIntrusive {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (val : NodeId) :
    Except ListFailure (Heap α × InvasiveLinkedList α) :=
  match pushfirstILLRef h ⟨q, q.id⟩ val with
  | .ok (h, q) => .ok (h, q)
  | .error error => .error error

/--
Julia source: base/linked_list.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pop!(q::IntrusiveLinkedList{T}) where T = pop!(ILLRef(q, q))
```
-/
def popIntrusive {α : Type} (h : Heap α) (q : InvasiveLinkedList α) :
    Except ListFailure (Heap α × InvasiveLinkedList α × NodeId) :=
  popILLRef h ⟨q, q.id⟩

/--
Julia source: base/linked_list.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
popfirst!(q::IntrusiveLinkedList{T}) where T = popfirst!(ILLRef(q, q))
```
-/
def popfirstIntrusive {α : Type} (h : Heap α) (q : InvasiveLinkedList α) :
    Except ListFailure (Heap α × InvasiveLinkedList α × NodeId) :=
  popfirstILLRef h ⟨q, q.id⟩

/--
Julia source: base/linked_list.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
list_deletefirst!(q::IntrusiveLinkedList{T}, val::T) where T = list_deletefirst!(ILLRef(q, q), val)
```
-/
def listDeleteFirstIntrusive {α : Type} (h : Heap α) (q : InvasiveLinkedList α) (val : NodeId) :
    Except ListFailure (Heap α × InvasiveLinkedList α) :=
  listDeleteFirstILLRef h ⟨q, q.id⟩ val


/--
Julia source: base/linked_list.jl:152-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct LinkedListItem{T}
    # Adapter class to use any `T` in a LinkedList
    next::Union{LinkedListItem{T}, Nothing}
    queue::Union{IntrusiveLinkedList{LinkedListItem{T}}, Nothing}
    value::T
    LinkedListItem{T}(value::T) where {T} = new{T}(nothing, nothing, value)
end
```
-/
def newLinkedListItem {α : Type} (h : Heap α) (value : α) : Heap α × LinkedListItem α :=
  let (h, id) := h.allocateNode value
  (h, ⟨id⟩)

/--
Julia source: base/linked_list.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:LinkedList{T}}) where {T} = @isdefined(T) ? T : Any
```
-/
def linkedEltype (elementType : Option Type) : JuliaTypeDescriptor :=
  match elementType with
  | some α => .concrete α
  | none => .any

/--
Julia source: base/linked_list.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(q::LinkedList) = (h = q.head; h === nothing ? nothing : (h.value, h))
```
-/
def iterateLinkedStart {α : Type} (h : Heap α) (q : LinkedList α) :
    Except ListFailure (Option (α × NodeId)) := do
  match q.head with
  | none => pure none
  | some head =>
      let node ← lookupNode h head
      pure (some (node.value, head))

/--
Julia source: base/linked_list.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(q::IntrusiveLinkedList{LLT}, v::LLT) where {LLT<:LinkedListItem} = (h = v.next; h === nothing ? nothing : (h.value, h))
```
-/
def iterateLinkedNext {α : Type} (h : Heap α) (v : NodeId) :
    Except ListFailure (Option (α × NodeId)) := do
  let node ← lookupNode h v
  match node.next with
  | none => pure none
  | some next =>
      let nextNode ← lookupNode h next
      pure (some (nextNode.value, next))

/--
Julia source: base/linked_list.jl:165-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(q::LinkedList{T}, val::T) where {T} = push!(q, LinkedListItem{T}(val))
```
-/
def pushLinked {α : Type} (h : Heap α) (q : LinkedList α) (value : α) :
    Except ListFailure (Heap α × LinkedList α) := do
  let (h, item) := newLinkedListItem h value
  pushIntrusive h q item.id

/--
Julia source: base/linked_list.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pushfirst!(q::LinkedList{T}, val::T) where {T} = pushfirst!(q, LinkedListItem{T}(val))
```
-/
def pushfirstLinked {α : Type} (h : Heap α) (q : LinkedList α) (value : α) :
    Except ListFailure (Heap α × LinkedList α) := do
  let (h, item) := newLinkedListItem h value
  pushfirstIntrusive h q item.id

/--
Julia source: base/linked_list.jl:167-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pop!(q::LinkedList) = invoke(pop!, Tuple{IntrusiveLinkedList,}, q).value
```
-/
def popLinked {α : Type} (h : Heap α) (q : LinkedList α) :
    Except ListFailure (Heap α × LinkedList α × α) := do
  let (h, q, item) ← popIntrusive h q
  let node ← lookupNode h item
  pure (h, q, node.value)

/--
Julia source: base/linked_list.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
popfirst!(q::LinkedList) = invoke(popfirst!, Tuple{IntrusiveLinkedList,}, q).value
```
-/
def popfirstLinked {α : Type} (h : Heap α) (q : LinkedList α) :
    Except ListFailure (Heap α × LinkedList α × α) := do
  let (h, q, item) ← popfirstIntrusive h q
  let node ← lookupNode h item
  pure (h, q, node.value)

private def removeFirstBy {α : Type} (same : α → α → Bool) (value : α) : List α → List α
  | [] => []
  | first :: rest => if same first value then rest else first :: removeFirstBy same value rest

private partial def findValueNode {α : Type} (h : Heap α) (same : α → α → Bool)
    (value : α) : Option NodeId → Except ListFailure (Option NodeId)
  | none => .ok none
  | some id => do
      let node ← lookupNode h id
      if same node.value value then pure (some id)
      else findValueNode h same value node.next

/--
Julia source: base/linked_list.jl:169-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function list_deletefirst!(q::LinkedList{T}, val::T) where T
    h = q.head
    while h !== nothing
        if isequal(h.value, val)
            list_deletefirst!(q, h)
            break
        end
        h = h.next
    end
    return q
end
```
-/
def listDeleteFirstLinked {α : Type} (h : Heap α) (q : LinkedList α) (same : α → α → Bool)
    (value : α) : Except ListFailure (Heap α × LinkedList α) := do
  match ← findValueNode h same value q.head with
  | none => pure (h, q)
  | some id => listDeleteFirstIntrusive h q id

private partial def linkedValuesLoop {α : Type} (h : Heap α) : Option NodeId → Except ListFailure (List α)
  | none => .ok []
  | some id => do
      let node ← lookupNode h id
      let rest ← linkedValuesLoop h node.next
      pure (node.value :: rest)

def linkedValues {α : Type} (h : Heap α) (q : LinkedList α) : Except ListFailure (List α) :=
  linkedValuesLoop h q.head

private partial def intrusiveIterationLoop {α : Type} (h : Heap α) (q : InvasiveLinkedList α)
    (fuel : Nat) (state : Option NodeId) : Except ListFailure (List NodeId) := do
  match fuel with
  | 0 => pure []
  | fuel + 1 =>
      let item ← match state with
        | none => pure (iterateIntrusiveStart q)
        | some id => iterateIntrusiveNext h id
      match item with
      | none => pure []
      | some (value, nextState) =>
          let rest ← intrusiveIterationLoop h q fuel (some nextState)
          pure (value :: rest)

def intrusiveIteration {α : Type} (h : Heap α) (q : InvasiveLinkedList α) :
    Except ListFailure (List NodeId) :=
  intrusiveIterationLoop h q (h.nodes.length + 1) none

private partial def linkedIterationLoop {α : Type} (h : Heap α) (q : LinkedList α)
    (fuel : Nat) (state : Option NodeId) : Except ListFailure (List α) := do
  match fuel with
  | 0 => pure []
  | fuel + 1 =>
      let item ← match state with
        | none => iterateLinkedStart h q
        | some id => iterateLinkedNext h id
      match item with
      | none => pure []
      | some (value, nextState) =>
          let rest ← linkedIterationLoop h q fuel (some nextState)
          pure (value :: rest)

def linkedIteration {α : Type} (h : Heap α) (q : LinkedList α) :
    Except ListFailure (List α) :=
  linkedIterationLoop h q (h.nodes.length + 1) none


/--
Julia source: base/linked_list.jl:190-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(qr::ILLRef{WaitEntry}, val::WaitEntry)
    _find_slot(val, qr.waitee) == 0 || error("val already in this list")
    _acquire_slot!(val, qr.waitee)
    q = qr.list
    tail = q.tail
    if tail === nothing
        q.head = q.tail = val
    else
        tail = tail::WaitEntry
        _set_slot_next!(tail, _find_slot(tail, qr.waitee), val)
        q.tail = val
    end
    return q
end
```
-/
def pushWaitEntry {α : Type} (ops : WaitEntryOps α) (h : Heap α) (qr : ILLRef α)
    (val : NodeId) : Except ListFailure (Heap α × InvasiveLinkedList α) := do
  if ops.findSlot h val qr.waitee != 0 then throw .alreadyInWaitList
  let (h, _) ← ops.acquireSlot h val qr.waitee
  let q := qr.list
  let tail := q.tail
  match tail with
  | none => pure (h, { q with head := some val, tail := some val })
  | some tail =>
      let _ ← lookupNode h tail
      let h := ops.setSlotNext h tail (ops.findSlot h tail qr.waitee) (some val)
      pure (h, { q with tail := some val })

/--
Julia source: base/linked_list.jl:205-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pushfirst!(qr::ILLRef{WaitEntry}, val::WaitEntry)
    _find_slot(val, qr.waitee) == 0 || error("val already in this list")
    i = _acquire_slot!(val, qr.waitee)
    q = qr.list
    head = q.head
    if head === nothing
        q.head = q.tail = val
    else
        _set_slot_next!(val, i, head)
        q.head = val
    end
    return q
end
```
-/
def pushfirstWaitEntry {α : Type} (ops : WaitEntryOps α) (h : Heap α) (qr : ILLRef α)
    (val : NodeId) : Except ListFailure (Heap α × InvasiveLinkedList α) := do
  if ops.findSlot h val qr.waitee != 0 then throw .alreadyInWaitList
  let (h, index) ← ops.acquireSlot h val qr.waitee
  let q := qr.list
  let head := q.head
  match head with
  | none => pure (h, { q with head := some val, tail := some val })
  | some head =>
      let h := ops.setSlotNext h val index (some head)
      pure (h, { q with head := some val })

/--
Julia source: base/linked_list.jl:219-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function popfirst!(qr::ILLRef{WaitEntry})
    q = qr.list
    val = q.head::WaitEntry
    i = _find_slot(val, qr.waitee)
    vnext = _slot_next(val, i)
    q.head = vnext
    vnext === nothing && (q.tail = nothing)
    _release_slot!(val, i)
    return val
end
```
-/
def popfirstWaitEntry {α : Type} (ops : WaitEntryOps α) (h : Heap α) (qr : ILLRef α) :
    Except ListFailure (Heap α × InvasiveLinkedList α × NodeId) := do
  let q := qr.list
  let val ← match q.head with
    | none => throw .typeError
    | some val => pure val
  let _ ← lookupNode h val
  let index := ops.findSlot h val qr.waitee
  let vnext := ops.slotNext h val index
  let q := { q with head := vnext }
  let q := if vnext.isNone then { q with tail := none } else q
  let h := ops.releaseSlot h val index
  pure (h, q, val)


private partial def waitDeleteLoop {α : Type} (ops : WaitEntryOps α) (h : Heap α)
    (q : InvasiveLinkedList α) (owner : OwnerId) (target targetIndex previous : NodeId) :
    Except ListFailure (Heap α × InvasiveLinkedList α × Bool) := do
  let index := ops.findSlot h previous owner
  if index == 0 then pure (h, q, false)
  else
    let node ← lookupNode h previous
    let slot ← match slotAt node.slots index with
      | none => throw .missingSlot
      | some slot => pure slot
    match slot.next with
    | none => pure (h, q, false)
    | some current =>
        let _ ← lookupNode h current
        if current == target then
          let next := ops.slotNext h target targetIndex
          let h := ops.setSlotNext h previous index next
          let q := if next.isNone then { q with tail := some previous } else q
          pure (h, q, true)
        else waitDeleteLoop ops h q owner target targetIndex current

/--
Julia source: base/linked_list.jl:236-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Delete `val` from the list, but only if it is actually in it, as witnessed
# by its slot for this list's identity. This makes deletion a no-op if `val`
# was concurrently popped, which various cleanup paths rely upon.
function list_deletefirst!(qr::ILLRef{WaitEntry}, val::WaitEntry)
    vi = _find_slot(val, qr.waitee)
    vi == 0 && return qr.list
    q = qr.list
    o = qr.waitee
    head = q.head
    if head === val
        vnext = _slot_next(val, vi)
        q.head = vnext
        vnext === nothing && (q.tail = nothing)
    else
        head === nothing && return q
        prev = head::WaitEntry
        while true
            previ = _find_slot(prev, o)
            previ == 0 && return q
            prevslot = slots(prev)[previ]
            cur = prevslot.next
            cur === nothing && return q
            cur = cur::WaitEntry
            if cur === val
                vnext = _slot_next(val, vi)
                prevslot.next = vnext
                vnext === nothing && (q.tail = prev)
                break
            end
            prev = cur
        end
    end
    _release_slot!(val, vi)
    return q
end
```
-/
def deleteWaitEntry {α : Type} (ops : WaitEntryOps α) (h : Heap α) (qr : ILLRef α)
    (val : NodeId) : Except ListFailure (Heap α × InvasiveLinkedList α) := do
  let vi := ops.findSlot h val qr.waitee
  if vi == 0 then pure (h, qr.list)
  else
    let q := qr.list
    let owner := qr.waitee
    match q.head with
    | some head =>
        if head == val then
          let vnext := ops.slotNext h val vi
          let q := { q with head := vnext }
          let q := if vnext.isNone then { q with tail := none } else q
          let h := ops.releaseSlot h val vi
          pure (h, q)
        else do
          let _ ← lookupNode h head
          let (h, q, found) ← waitDeleteLoop ops h q owner val vi head
          if !found then pure (h, q)
          else pure (ops.releaseSlot h val vi, q)
    | none => pure (h, q)
/--
Julia source: base/linked_list.jl:230-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(qr::ILLRef{WaitEntry})
    val = qr.list.tail::WaitEntry
    list_deletefirst!(qr, val) # expensive!
    return val
end
```
-/
def popWaitEntry {α : Type} (ops : WaitEntryOps α) (h : Heap α) (qr : ILLRef α) :
    Except ListFailure (Heap α × InvasiveLinkedList α × NodeId) := do
  let val ← match qr.list.tail with
    | none => throw .typeError
    | some val => pure val
  let _ ← lookupNode h val
  let (h, q) ← deleteWaitEntry ops h qr val
  pure (h, q, val)

/--
Julia source: base/linked_list.jl:272-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(qr::ILLRef{WaitEntry})
    n = 0
    w = qr.list.head
    while w !== nothing
        n += 1
        w = _next_on(w::WaitEntry, qr.waitee)
    end
    return n
end
```
-/
partial def lengthWaitEntry {α : Type} (ops : WaitEntryOps α) (h : Heap α) (qr : ILLRef α) :
    Except ListFailure Nat := do
  let mut n := 0
  let mut w := qr.list.head
  while w.isSome do
    n := n + 1
    let id := w.get!
    let _ ← lookupNode h id
    w := ops.nextOn h id qr.waitee
  pure n

-- In this sequential heap model, a monotonic load returns the field's current value.
def atomicLoadMonotonic {α β : Type} (h : Heap α) (field : Heap α → β) : β := field h

/--
Julia source: base/linked_list.jl:282-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Whether any entry on the list is still armed (the emptiness that matters
# to waiters-pending queries; claimed corpses linger until popped).
function _waitq_isempty(qr::ILLRef{WaitEntry})
    w = qr.list.head
    while w !== nothing
        w = w::WaitEntry
        t = @atomic :monotonic w.task
        t isa Task && (@atomic t.waiting_on) === w && return false
        w = _next_on(w, qr.waitee)
    end
    return true
end
```
-/
partial def waitQueueIsEmpty {α : Type} (ops : WaitEntryOps α) (h : Heap α) (qr : ILLRef α) :
    Except ListFailure Bool := do
  let mut w := qr.list.head
  while w.isSome do
    let id := w.get!
    let _ ← lookupNode h id
    let task := atomicLoadMonotonic h (fun state => ((state.node? id).map HeapNode.task).join)
    match task with
    | some task =>
        if atomicLoadMonotonic h
            (fun state => (Heap.lookupTask state.tasksWaitingOn task).join) == some id then
          return false
    | none => pure ()
    w := ops.nextOn h id qr.waitee
  return true

end JuliaLean.base.linked_list

import JuliaLean.Tasks.AsyncMap
import JuliaLean.Tasks.LinkedList
import JuliaLean.Tasks.ScopedValues
import JuliaLean.Tasks.Atomics

/-! Source-body models for `base/asyncmap.jl`, `base/linked_list.jl`,
`base/scopedvalues.jl`, and `base/atomics.jl`. -/

namespace JuliaLean.Tasks

/-! ## base/asyncmap.jl:76-152, public result shaping and validation -/

inductive AsyncShape where | tuple | array (dimensions : List Nat) | linear
  deriving Repr, DecidableEq

def asyncResultShape (shape : AsyncShape) (values : List Nat) : Nat × List Nat :=
  match shape with
  | .tuple => (values.length, values)
  | .array dimensions => (dimensions.foldl (· * ·) 1, values)
  | .linear => (values.length, values)

def verifyBatchSizeBody : Option Int → Except Unit (Option Nat)
  | none => .ok none
  | some size => if size < 1 then .error () else .ok (some size.toNat)

inductive NTasksArgument where | constant (count : Int) | dynamic (initial : Int)
  deriving Repr, DecidableEq

def verifyNTasksBody (length : Option Nat) : NTasksArgument → Except Unit Nat
  | .constant count =>
      if count < 0 then .error ()
      else if count == 0 then .ok (max 1 (min 100 (length.getD 100)))
      else .ok count.toNat
  | .dynamic initial => .ok (if initial == 0 then 1 else initial.toNat)

def asyncStringResult (characters : List Nat) : List Nat := characters

def AsyncMapPublicBodies : Prop := ∀ (_shape : AsyncShape) (values : List Nat)
    (length : Option Nat) (count : Int),
  (asyncResultShape .tuple values).2 = values ∧
  verifyBatchSizeBody none = .ok none ∧
  (count < 0 → verifyNTasksBody length (.constant count) = .error ()) ∧
  verifyNTasksBody length (.dynamic 0) = .ok 1 ∧
  asyncStringResult values = values

theorem asyncMapPublicBodies_proven : AsyncMapPublicBodies := by
  unfold AsyncMapPublicBodies
  intro shape values length count
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  · intro negative; simp [verifyNTasksBody, negative]

/-! ## base/asyncmap.jl:154-291, workers and AsyncCollector -/

structure CollectorState where
  pending : List (Nat × Nat)
  results : Nat → Option Nat
  workers : Nat

def collectorStart (jobs : List (Nat × Nat)) (workers : Nat) : CollectorState :=
  ⟨jobs, fun _ => none, workers⟩

def collectorComplete (f : Nat → Nat) (state : CollectorState) (index value : Nat) :
    CollectorState :=
  { state with results := fun i => if i == index then some (f value) else state.results i }

def collectorGrow (state : CollectorState) (requested : Nat) : CollectorState :=
  if state.workers < requested then { state with workers := state.workers + 1 } else state

def AsyncCollectorBodies : Prop := ∀ (f : Nat → Nat) (state : CollectorState)
    (index value requested : Nat),
  (collectorComplete f state index value).results index = some (f value) ∧
  (collectorGrow state requested).workers =
    (if state.workers < requested then state.workers + 1 else state.workers)

theorem asyncCollectorBodies_proven : AsyncCollectorBodies := by
  intro f state index value requested
  constructor
  · simp [collectorComplete]
  · simp [collectorGrow]
    split <;> rfl

/-! ## base/asyncmap.jl:306-356, AsyncGenerator and asyncmap! -/

structure GeneratorState where
  nextIndex : Nat := 1
  done : Bool := false
  results : Nat → Option Nat := fun _ => none

inductive GeneratorStep where | value (value : Nat) | blocked | finished
  deriving Repr, DecidableEq

def generatorStep (state : GeneratorState) : GeneratorStep × GeneratorState :=
  if state.done && state.results state.nextIndex == none then (.finished, state)
  else
    match state.results state.nextIndex with
    | some value => (.value value, { state with nextIndex := state.nextIndex + 1 })
    | none => (.blocked, state)

def asyncmapBangBody (result : List Nat) : List Nat := result

def AsyncGeneratorBodies : Prop := ∀ (state : GeneratorState) (result : List Nat),
  asyncmapBangBody result = result ∧
  (state.done = true → state.results state.nextIndex = none →
    (generatorStep state).1 = .finished)

theorem asyncGeneratorBodies_proven : AsyncGeneratorBodies := by
  intro state result
  constructor
  · rfl
  · intro done missing
    simp [generatorStep, done, missing]

/-! ## base/linked_list.jl:3-143, generic intrusive lists -/

def linkedAppend (left right : List Nat) : Except Unit (List Nat × List Nat) :=
  if left = right && left ≠ [] then .error () else .ok (left ++ right, [])

def linkedPushFirst (nodes : List Nat) (node : Nat) : Except Unit (List Nat) :=
  if node ∈ nodes then .error () else .ok (node :: nodes)

def linkedPopFirst : List Nat → Except Unit (Nat × List Nat)
  | [] => .error ()
  | node :: nodes => .ok (node, nodes)

def linkedPopLast (nodes : List Nat) : Except Unit (Nat × List Nat) :=
  match nodes.getLast? with
  | none => .error ()
  | some node => .ok (node, removeLast nodes)

def LinkedGenericBodies : Prop := ∀ (nodes : List Nat) (node : Nat),
  (node ∉ nodes → linkedPushFirst nodes node = .ok (node :: nodes)) ∧
  (linkedPopFirst (node :: nodes) = .ok (node, nodes)) ∧
  (linkedListStep (.delete node) nodes = nodes.erase node) ∧
  (linkedAppend nodes [] = .ok (nodes, []))

theorem linkedGenericBodies_proven : LinkedGenericBodies := by
  intro nodes node
  constructor
  · intro fresh; simp [linkedPushFirst, fresh]
  exact ⟨rfl, rfl, by simp [linkedAppend]⟩

/-! ## base/linked_list.jl:152-179, boxed LinkedList wrappers -/

structure BoxedNode where
  id : Nat
  value : Nat
  deriving Repr, DecidableEq

def boxedPush (nodes : List BoxedNode) (freshId value : Nat) : List BoxedNode :=
  nodes ++ [⟨freshId, value⟩]

def boxedValues (nodes : List BoxedNode) : List Nat := nodes.map (·.value)

def boxedDeleteValue (nodes : List BoxedNode) (value : Nat) : List BoxedNode :=
  match nodes.find? (fun node => node.value == value) with
  | none => nodes
  | some found => nodes.erase found

def LinkedBoxedBodies : Prop := ∀ (nodes : List BoxedNode) (freshId value : Nat),
  boxedValues (boxedPush nodes freshId value) = boxedValues nodes ++ [value] ∧
  (boxedDeleteValue nodes value).length ≤ nodes.length

theorem linkedBoxedBodies_proven : LinkedBoxedBodies := by
  intro nodes freshId value
  constructor
  · simp [boxedPush, boxedValues]
  · simp only [boxedDeleteValue]
    split <;> simp [List.length_erase_le]

/-! ## base/linked_list.jl:181-293, multi-owner WaitEntry lists -/

structure MultiListEntry where
  id : Nat
  owners : List Nat
  deriving Repr, DecidableEq

def multiListPush (queue : List MultiListEntry) (owner : Nat) (entry : MultiListEntry) :
    Except Unit (List MultiListEntry) :=
  if owner ∈ entry.owners then .error ()
  else .ok (queue ++ [{ entry with owners := owner :: entry.owners }])

def multiListDelete (queue : List MultiListEntry) (owner id : Nat) : List MultiListEntry :=
  queue.filterMap fun entry =>
    if entry.id == id && owner ∈ entry.owners then
      let owners := entry.owners.erase owner
      if owners.isEmpty then none else some { entry with owners := owners }
    else some entry

def waitQueueHasArmed (queue : List (Nat × Bool)) : Bool := queue.any (·.2)

def LinkedWaitEntryBodies : Prop := ∀ (queue : List MultiListEntry) (owner : Nat)
    (entry : MultiListEntry) (armed : List (Nat × Bool)),
  (owner ∉ entry.owners →
    match multiListPush queue owner entry with
    | .ok result => result.length = queue.length + 1
    | .error _ => False) ∧
  waitQueueHasArmed armed = armed.any (·.2) ∧
  (multiListDelete queue owner entry.id).length ≤ queue.length

theorem linkedWaitEntryBodies_proven : LinkedWaitEntryBodies := by
  intro queue owner entry armed
  constructor
  · intro fresh
    simp [multiListPush, fresh]
  constructor
  · rfl
  · unfold multiListDelete
    exact List.length_filterMap_le _ _

/-! ## base/scopedvalues.jl:79-201, defaults, lookup, and display decisions -/

structure ScopedCell where
  hasDefault : Bool
  defaultValue : Int := 0
  deriving Repr, DecidableEq

def scopedDefault (cell : ScopedCell) : Option Int :=
  if cell.hasDefault then some cell.defaultValue else none

def scopedGet (scope : Scope) (cell : ScopedCell) (key : Nat) : Option Int :=
  match scope key with
  | some value => some value
  | none => scopedDefault cell

def scopedAssigned (scope : Scope) (cell : ScopedCell) (key : Nat) : Bool :=
  cell.hasDefault || (scope key).isSome

def ScopedAccessBodies : Prop := ∀ (scope : Scope) (cell : ScopedCell) (key : Nat),
  scopedAssigned scope cell key = (cell.hasDefault || (scope key).isSome) ∧
  (cell.hasDefault → scopedDefault cell = some cell.defaultValue)

theorem scopedAccessBodies_proven : ScopedAccessBodies := by
  intro scope cell key
  constructor
  · rfl
  · intro hasDefault
    simp [scopedDefault, hasDefault]

/-! ## base/scopedvalues.jl:231-308, dynamic scope and ScopedThunk -/

structure CoverageScopedThunk where
  captured : Scope
  result : Nat

def scopedThunkCall (thunk : CoverageScopedThunk) : Nat × Scope :=
  (thunk.result, thunk.captured)

def ScopedDynamicBodies : Prop := ∀ (parent : Scope) (bindings : Bindings)
    (body : Scope → Except Nat Nat) (result : Nat),
  (withScope parent bindings body).2 = parent ∧
  (scopedThunkCall ⟨enterScope parent bindings, result⟩).2 = enterScope parent bindings

theorem scopedDynamicBodies_proven : ScopedDynamicBodies := by
  unfold ScopedDynamicBodies
  intros
  exact ⟨rfl, rfl⟩

/-! ## base/atomics.jl:66-361, storage and index/RMW wrappers -/

structure CoverageAtomic where
  value : AtomicInt
  initialized : Bool := true
  deriving Repr, DecidableEq

def atomicDefault : CoverageAtomic := ⟨0, true⟩
def atomicLoad (cell : CoverageAtomic) : AtomicInt := cell.value
def atomicStore (cell : CoverageAtomic) (value : AtomicInt) : AtomicInt × CoverageAtomic :=
  (value, { cell with value := value })
def atomicSwap (cell : CoverageAtomic) (value : AtomicInt) : AtomicInt × CoverageAtomic :=
  (cell.value, { cell with value := value })
def atomicReplace (cell : CoverageAtomic) (expected desired : AtomicInt) :
    AtomicInt × Bool × CoverageAtomic :=
  if cell.value == expected then (cell.value, true, { cell with value := desired })
  else (cell.value, false, cell)
def atomicSetOnce (cell : CoverageAtomic) (value : AtomicInt) : Bool × CoverageAtomic :=
  if cell.initialized then (false, cell) else (true, ⟨value, true⟩)

def AtomicStorageBodies : Prop := ∀ (cell : CoverageAtomic) (value expected desired : AtomicInt),
  atomicDefault.value = 0 ∧
  atomicLoad cell = cell.value ∧
  (atomicSwap cell value).1 = cell.value ∧
  (atomicReplace cell expected desired).1 = cell.value ∧
  (atomicStep (.exchange value) cell.value).1 = cell.value

theorem atomicStorageBodies_proven : AtomicStorageBodies := by
  unfold AtomicStorageBodies
  intros
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  simp [atomicReplace]
  split <;> rfl

/-! ## base/atomics.jl:378-402, fences -/

inductive FenceKind where | system | light | heavy
  deriving Repr, DecidableEq

def fenceBody : FenceKind → String
  | .system => "sequentially_consistent:system"
  | .light => "sequentially_consistent:singlethread"
  | .heavy => "jl_membarrier"

def AtomicFenceBodies : Prop := ∀ kind : FenceKind, !(fenceBody kind).isEmpty

theorem atomicFenceBodies_proven : AtomicFenceBodies := by intro kind; cases kind <;> decide

end JuliaLean.Tasks

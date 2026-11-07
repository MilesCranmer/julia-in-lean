import JuliaLean.base.hamt
import JuliaLean.base.hashing
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.hamt

open JuliaLean.Registry JuliaLean.base.hamt

/-! Finite maps are read from the explicit mutable heap. `HashingLawful` captures
    reflexive identity and the object-identity consistency used by Julia’s `===`. -/

def HashingLawful (same : K → K → Bool) (ops : HamtObjectIdRuntime K) : Prop :=
  (∀ key, same key key = true) ∧
  (∀ a b, same a b = true → same b a = true) ∧
  (∀ a b c, same a b = true → same b c = true → same a c = true) ∧
  (∀ a b, same a b = true → ops.objectid a = ops.objectid b)

def finiteLookup {K V : Type} (same : K → K → Bool) (key : K) : List (K × V) → Option V
  | [] => none
  | (storedKey, value) :: rest => if same storedKey key then some value else finiteLookup same key rest

def allDistinctFrom {K V : Type} (same : K → K → Bool) (key : K) :
    List (K × V) → Prop
  | [] => True
  | (other, _) :: rest => same key other = false ∧ allDistinctFrom same key rest

def finiteMapUnique {K V : Type} (same : K → K → Bool) : List (K × V) → Prop
  | [] => True
  | (key, _) :: rest => allDistinctFrom same key rest ∧ finiteMapUnique same rest

mutual
  def heapMap (heap : HamtHeap K V) (trie : HAMT K V) :
      Option (Except HamtError (List (K × V))) :=
    match heap.nodes[trie]? with
    | none => some (.error .bounds)
    | some node =>
      match heap.vectors[node.data]? with
      | none => some (.error .bounds)
      | some slots => heapEntriesMap heap slots
  partial_fixpoint

  def heapEntriesMap (heap : HamtHeap K V) :
      List (Option (Entry K V)) → Option (Except HamtError (List (K × V)))
    | [] => some (.ok [])
    | none :: _ => some (.error .undefinedReference)
    | some (.leaf leaf) :: rest => do
      let result ← heapEntriesMap heap rest
      pure <| match result with
        | .error error => .error error
        | .ok pairs => .ok ((leaf.key, leaf.val) :: pairs)
    | some (.trie child) :: rest => do
      let childResult ← heapMap heap child
      match childResult with
      | .error error => pure (.error error)
      | .ok childPairs => do
        let restResult ← heapEntriesMap heap rest
        pure <| match restResult with
          | .error error => .error error
          | .ok restPairs => .ok (childPairs ++ restPairs)
  partial_fixpoint
end

def readMap (heap : HamtHeap K V) (trie : HAMT K V) :
    Option (Except HamtError (List (K × V))) :=
  heapMap heap trie

def runPathValue (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (trie : HAMT K V) (key : K) : Option V :=
  let (outcome, _) := runHamt (do
    let result ← path heapVectorOps same ops trie (HashState.fromKey ops key)
    PathResult.value? heapVectorOps result) heap
  match outcome with
  | .ok (some value) => some value
  | _ => none

mutual
  inductive heapInvariant (heap : HamtHeap K V) : HAMT K V → Prop where
    | node {trie : HAMT K V} {node : HAMTNode K V} {slots : List (Option (Entry K V))}
        (hnode : heap.nodes[trie]? = some node)
        (hslots : heap.vectors[node.data]? = some slots)
        (hbitmap : node.bitmap < 2 ^ 32)
        (hcount : countOnes 32 node.bitmap = slots.length)
        (hentries : heapEntriesInvariant heap slots) :
        heapInvariant heap trie

  inductive heapEntriesInvariant (heap : HamtHeap K V) :
      List (Option (Entry K V)) → Prop where
    | nil : heapEntriesInvariant heap []
    | leaf {leaf : Leaf K V} {rest : List (Option (Entry K V))}
        (hrest : heapEntriesInvariant heap rest) :
        heapEntriesInvariant heap (some (.leaf leaf) :: rest)
    | trie {child : HAMT K V} {rest : List (Option (Entry K V))}
        (hchild : heapInvariant heap child)
        (hrest : heapEntriesInvariant heap rest) :
        heapEntriesInvariant heap (some (.trie child) :: rest)
end

def HeapPrefixFrame {K V : Type} (heap heap' : HamtHeap K V) : Prop :=
  (∀ i, i < heap.nodes.length → heap.nodes[i]? = heap'.nodes[i]?) ∧
  (∀ i, i < heap.vectors.length → heap.vectors[i]? = heap'.vectors[i]?)

private theorem heapPrefixFrame_trans {K V : Type} {base middle final : HamtHeap K V}
    (hfirst : HeapPrefixFrame base middle) (hsecond : HeapPrefixFrame middle final)
    (hnodes : base.nodes.length ≤ middle.nodes.length)
    (hvectors : base.vectors.length ≤ middle.vectors.length) :
    HeapPrefixFrame base final := by
  constructor
  · intro i hi
    exact (hfirst.1 i hi).trans (hsecond.1 i (Nat.lt_of_lt_of_le hi hnodes))
  · intro i hi
    exact (hfirst.2 i hi).trans (hsecond.2 i (Nat.lt_of_lt_of_le hi hvectors))

private def HeapLengthsExtend {K V : Type} (base heap : HamtHeap K V) : Prop :=
  base.nodes.length ≤ heap.nodes.length ∧ base.vectors.length ≤ heap.vectors.length

private theorem heapPrefixFrame_nodeAppend {K V : Type}
    {base heap : HamtHeap K V} (hframe : HeapPrefixFrame base heap)
    (hextend : HeapLengthsExtend base heap) (node : HAMTNode K V) :
    HeapPrefixFrame base {heap with nodes := heap.nodes ++ [node]} := by
  constructor
  · intro i hi
    have hi' : i < heap.nodes.length := Nat.lt_of_lt_of_le hi hextend.1
    rw [hframe.1 i hi]
    simp [List.getElem?_append, hi']
  · intro i hi
    exact hframe.2 i hi

private theorem heapPrefixFrame_vectorSet {K V : Type}
    {base heap : HamtHeap K V} (hframe : HeapPrefixFrame base heap)
    (data : Nat) (slots : List (Option (Entry K V)))
    (hdata : base.vectors.length ≤ data) :
    HeapPrefixFrame base {heap with vectors := heap.vectors.set data slots} := by
  constructor
  · intro i hi
    exact hframe.1 i hi
  · intro i hi
    have hne : i ≠ data := by omega
    simpa [List.getElem?_set, Ne.symm hne] using hframe.2 i hi

private theorem heapLengthsExtend_vectorAppend {K V : Type}
    {base heap : HamtHeap K V} (hextend : HeapLengthsExtend base heap)
    (slots : List (Option (Entry K V))) :
    HeapLengthsExtend base {heap with vectors := heap.vectors ++ [slots]} := by
  rcases hextend with ⟨hnodes, hvectors⟩
  constructor
  · exact hnodes
  · simp
    omega

private theorem heapLengthsExtend_nodeAppend {K V : Type}
    {base heap : HamtHeap K V} (hextend : HeapLengthsExtend base heap)
    (node : HAMTNode K V) :
    HeapLengthsExtend base {heap with nodes := heap.nodes ++ [node]} := by
  rcases hextend with ⟨hnodes, hvectors⟩
  constructor
  · simp
    omega
  · exact hvectors

theorem heapMap_prefixFrame {K V : Type} (heap heap' : HamtHeap K V)
    (trie : HAMT K V) (hinv : heapInvariant heap trie)
    (hframe : HeapPrefixFrame heap heap') :
    readMap heap trie = readMap heap' trie := by
  change heapMap heap trie = heapMap heap' trie
  let motiveNode : (trie : HAMT K V) → heapInvariant heap trie → Prop :=
    fun trie _ => heapMap heap trie = heapMap heap' trie
  let motiveEntries : (slots : List (Option (Entry K V))) →
      heapEntriesInvariant heap slots → Prop :=
    fun slots _ => heapEntriesMap heap slots = heapEntriesMap heap' slots
  have hrec : motiveNode trie hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro current node slots hnode hslots hbitmap hcount hentries ihEntries
      change heapMap heap current = heapMap heap' current
      have hnodeLt : current < heap.nodes.length :=
        (List.getElem?_eq_some_iff.mp hnode).1
      have hdataLt : node.data < heap.vectors.length :=
        (List.getElem?_eq_some_iff.mp hslots).1
      have hnodeNew : heap'.nodes[current]? = some node :=
        (hframe.1 current hnodeLt).symm.trans hnode
      have hslotsNew : heap'.vectors[node.data]? = some slots :=
        (hframe.2 node.data hdataLt).symm.trans hslots
      simpa only [heapMap.eq_1, hnode, hslots, hnodeNew, hslotsNew] using ihEntries
    · change heapEntriesMap heap [] = heapEntriesMap heap' []
      rw [heapEntriesMap.eq_1, heapEntriesMap.eq_1]
    · intro leaf rest hrest ihRest
      change heapEntriesMap heap (some (.leaf leaf) :: rest) =
        heapEntriesMap heap' (some (.leaf leaf) :: rest)
      rw [heapEntriesMap.eq_3, heapEntriesMap.eq_3]
      rw [ihRest]
    · intro child rest hchild hrest ihChild ihRest
      change heapEntriesMap heap (some (.trie child) :: rest) =
        heapEntriesMap heap' (some (.trie child) :: rest)
      rw [heapEntriesMap.eq_4, heapEntriesMap.eq_4]
      rw [ihChild, ihRest]
  exact hrec


private theorem heapEntriesMap_prefixFrame {K V : Type}
    {base heap : HamtHeap K V} (hframe : HeapPrefixFrame base heap)
    {slots : List (Option (Entry K V))}
    (hinv : heapEntriesInvariant base slots) :
    heapEntriesMap base slots = heapEntriesMap heap slots := by
  let motiveNode : (trie : HAMT K V) → heapInvariant base trie → Prop :=
    fun _ _ => True
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant base slots → Prop :=
    fun slots _ => heapEntriesMap base slots = heapEntriesMap heap slots
  have hrec : motiveEntries slots hinv := by
    refine heapEntriesInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro current node currentSlots hnode hslots hbitmap hcount hentries ihEntries
      trivial
    · change heapEntriesMap base [] = heapEntriesMap heap []
      rw [heapEntriesMap.eq_1, heapEntriesMap.eq_1]
    · intro leaf rest hrest ihRest
      change heapEntriesMap base (some (.leaf leaf) :: rest) =
        heapEntriesMap heap (some (.leaf leaf) :: rest)
      rw [heapEntriesMap.eq_3, heapEntriesMap.eq_3, ihRest]
    · intro child rest hchild hrest ihChild ihRest
      change heapEntriesMap base (some (.trie child) :: rest) =
        heapEntriesMap heap (some (.trie child) :: rest)
      rw [heapEntriesMap.eq_4, heapEntriesMap.eq_4]
      have hchildMap : heapMap base child = heapMap heap child := by
        change readMap base child = readMap heap child
        exact heapMap_prefixFrame base heap child hchild hframe
      rw [hchildMap, ihRest]
  exact hrec

private theorem heapEntriesMap_replaceTrie {K V : Type}
    {base heap : HamtHeap K V} (hframe : HeapPrefixFrame base heap)
    {slots : List (Option (Entry K V))}
    (hinv : heapEntriesInvariant base slots) (index : Nat)
    (oldChild newChild : HAMT K V)
    (hslot : slots[index]? = some (some (.trie oldChild)))
    (hchildMap : heapMap base oldChild = heapMap heap newChild) :
    heapEntriesMap base slots =
      heapEntriesMap heap (slots.set index (some (.trie newChild))) := by
  let motiveNode : (trie : HAMT K V) → heapInvariant base trie → Prop :=
    fun _ _ => True
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant base slots → Prop :=
    fun slots _ => ∀ index oldChild newChild,
      slots[index]? = some (some (.trie oldChild)) →
      heapMap base oldChild = heapMap heap newChild →
      heapEntriesMap base slots =
        heapEntriesMap heap (slots.set index (some (.trie newChild)))
  have hrec : motiveEntries slots hinv := by
    refine heapEntriesInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro current node currentSlots hnode hslots hbitmap hcount hentries ihEntries
      trivial
    · intro index oldChild newChild hslot hchildMap
      simp at hslot
    · intro leaf rest hrest ihRest index oldChild newChild hslot hchildMap
      cases index with
      | zero => simp at hslot
      | succ index =>
          have hslotRest : rest[index]? = some (some (.trie oldChild)) := by
            simpa using hslot
          simp only [List.set, heapEntriesMap.eq_3]
          rw [ihRest index oldChild newChild hslotRest hchildMap]
    · intro child rest hchild hrest ihChild ihRest index oldChild newChild hslot hchildMap
      cases index with
      | zero =>
          have hchildEq : child = oldChild := by
            simpa using hslot
          subst oldChild
          simp only [List.set, heapEntriesMap.eq_4]
          rw [hchildMap, heapEntriesMap_prefixFrame hframe hrest]
      | succ index =>
          have hslotRest : rest[index]? = some (some (.trie oldChild)) := by
            simpa using hslot
          simp only [List.set, heapEntriesMap.eq_4]
          have hheadMap : heapMap base child = heapMap heap child := by
            change readMap base child = readMap heap child
            exact heapMap_prefixFrame base heap child hchild hframe
          rw [hheadMap, ihRest index oldChild newChild hslotRest hchildMap]
  exact hrec index oldChild newChild hslot hchildMap


private theorem heapVectorAllocatePrefixFrame {K V : Type}
    (heap : HamtHeap K V) (slots : List (Option (Entry K V))) :
    HeapPrefixFrame heap { heap with vectors := heap.vectors ++ [slots] } := by
  constructor
  · intro i hi
    rfl
  · intro i hi
    simp [List.getElem?_append, hi]

private theorem heapInvariant_prefixFrame {K V : Type} {base heap : HamtHeap K V}
    (hframe : HeapPrefixFrame base heap) :
    ∀ {trie}, heapInvariant base trie → heapInvariant heap trie := by
  intro trie hinv
  let motiveNode : (trie : HAMT K V) → heapInvariant base trie → Prop :=
    fun trie _ => heapInvariant heap trie
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant base slots → Prop :=
    fun slots _ => heapEntriesInvariant heap slots
  have hrec : motiveNode trie hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro current node slots hnode hslots hbitmap hcount hentries ihEntries
      have hnodeLt : current < base.nodes.length :=
        (List.getElem?_eq_some_iff.mp hnode).1
      have hdataLt : node.data < base.vectors.length :=
        (List.getElem?_eq_some_iff.mp hslots).1
      have hnodeNew : heap.nodes[current]? = some node :=
        (hframe.1 current hnodeLt).symm.trans hnode
      have hslotsNew : heap.vectors[node.data]? = some slots :=
        (hframe.2 node.data hdataLt).symm.trans hslots
      exact .node hnodeNew hslotsNew hbitmap hcount ihEntries
    · exact .nil
    · intro leaf rest hrest ihRest
      exact .leaf ihRest
    · intro child rest hchild hrest ihChild ihRest
      exact .trie ihChild ihRest
  exact hrec

private theorem heapEntriesInvariant_prefixFrame {K V : Type} {base heap : HamtHeap K V}
    (hframe : HeapPrefixFrame base heap) {slots : List (Option (Entry K V))}
    (hinv : heapEntriesInvariant base slots) :
    heapEntriesInvariant heap slots := by
  let motiveNode : (trie : HAMT K V) → heapInvariant base trie → Prop :=
    fun trie _ => heapInvariant heap trie
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant base slots → Prop :=
    fun slots _ => heapEntriesInvariant heap slots
  have hrec : motiveEntries slots hinv := by
    refine heapEntriesInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro current node slots hnode hslots hbitmap hcount hentries ihEntries
      have hnodeLt : current < base.nodes.length :=
        (List.getElem?_eq_some_iff.mp hnode).1
      have hdataLt : node.data < base.vectors.length :=
        (List.getElem?_eq_some_iff.mp hslots).1
      have hnodeNew : heap.nodes[current]? = some node :=
        (hframe.1 current hnodeLt).symm.trans hnode
      have hslotsNew : heap.vectors[node.data]? = some slots :=
        (hframe.2 node.data hdataLt).symm.trans hslots
      exact .node hnodeNew hslotsNew hbitmap hcount ihEntries
    · exact .nil
    · intro leaf rest hrest ihRest
      exact .leaf ihRest
    · intro child rest hchild hrest ihChild ihRest
      exact .trie ihChild ihRest
  exact hrec

def advanceHash (ops : HamtObjectIdRuntime K) : Nat → HashState K → HashState K
  | 0, state => state
  | n + 1, state => advanceHash ops n (next ops state)

def HamtHashChunksMatch {K : Type} (ops : HamtObjectIdRuntime K) (key : K)
    (chunks : List Nat) : Prop :=
  ∀ level chunk, chunks[level]? = some chunk →
    (BitmapIndex.fromHash (advanceHash ops level (HashState.fromKey ops key))).x = chunk

inductive HamtStoredLeafPath {K V : Type} (heap : HamtHeap K V) :
    HAMT K V → List Nat → Leaf K V → Prop where
  | leaf {trie node slots index bit leaf}
      (hnode : heap.nodes[trie]? = some node)
      (hslots : heap.vectors[node.data]? = some slots)
      (hbit : bit < 32)
      (hset : Nat.testBit node.bitmap bit = true)
      (hrank : index = countOnes 32 (Nat.land node.bitmap (shiftLeftNat 1 bit - 1)) + 1)
      (hentry : slots[index - 1]? = some (some (.leaf leaf))) :
      HamtStoredLeafPath heap trie [bit] leaf
  | child {trie node slots index bit child suffix leaf}
      (hnode : heap.nodes[trie]? = some node)
      (hslots : heap.vectors[node.data]? = some slots)
      (hbit : bit < 32)
      (hset : Nat.testBit node.bitmap bit = true)
      (hrank : index = countOnes 32 (Nat.land node.bitmap (shiftLeftNat 1 bit - 1)) + 1)
      (hentry : slots[index - 1]? = some (some (.trie child)))
      (hchild : HamtStoredLeafPath heap child suffix leaf) :
      HamtStoredLeafPath heap trie (bit :: suffix) leaf

def HamtHashCoherent {K V : Type} (ops : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (trie : HAMT K V) : Prop :=
  ∀ path leaf, HamtStoredLeafPath heap trie path leaf →
    HamtHashChunksMatch ops leaf.key path

def HamtInnerSharesVector : Prop :=
  ∀ (K V : Type) (heap : HamtHeap K V) (data : Nat) (bitmap : BITMAP)
    (index : Nat) (entry : Entry K V) (slots : List (Option (Entry K V)))
    (trie : HAMT K V) (heap1 heap2 : HamtHeap K V),
    heap.vectors[data]? = some slots → 1 ≤ index → index ≤ slots.length →
    runHamt (HAMT.inner data bitmap) heap = (.ok trie, heap1) →
    runHamt (heapVectorOps.set data index entry) heap1 = (.ok (), heap2) →
      ∃ node updatedSlots, heap2.nodes[trie]? = some node ∧ node.data = data ∧
        heap2.vectors[data]? = some updatedSlots ∧ updatedSlots[index - 1]? = some (some entry)

def HamtEmptyAllocatesIndependently : Prop :=
  ∀ (K V : Type) (heap heap1 heap2 heap3 : HamtHeap K V)
    (first second : HAMT K V) (bit : BitmapIndex) (bitmap : BITMAP),
    runHamt (HAMT.emptyConstructor heapVectorOps) heap = (.ok first, heap1) →
    runHamt (HAMT.emptyConstructor heapVectorOps) heap1 = (.ok second, heap2) →
    runHamt (set! first bit) heap2 = (.ok bitmap, heap3) →
      first ≠ second ∧
      ∃ firstNode secondNode secondAfter firstSlots secondSlots secondAfterSlots,
        heap2.nodes[first]? = some firstNode ∧ firstNode.bitmap = 0 ∧
        heap2.vectors[firstNode.data]? = some firstSlots ∧ firstSlots.length = 0 ∧
        heap2.nodes[second]? = some secondNode ∧ secondNode.bitmap = 0 ∧
        heap2.vectors[secondNode.data]? = some secondSlots ∧ secondSlots.length = 0 ∧
        firstNode.data ≠ secondNode.data ∧
        (runHamt (islevel_empty second) heap3).1 = .ok true ∧
        heap3.nodes[second]? = some secondAfter ∧ secondAfter.bitmap = 0 ∧
        secondAfter.data = secondNode.data ∧
        heap3.vectors[secondAfter.data]? = some secondAfterSlots ∧
        secondAfterSlots.length = 0 ∧ secondAfterSlots = secondSlots

def HamtInitSingleIsolated : Prop :=
  ∀ (K V : Type) (heap heap1 heap2 : HamtHeap K V)
    (key1 key2 : K) (value1 value2 : V) (trie1 trie2 : HAMT K V),
    runHamt (init_hamt heapVectorOps key1 value1) heap = (.ok trie1, heap1) →
    runHamt (init_hamt heapVectorOps key2 value2) heap1 = (.ok trie2, heap2) →
      trie1 ≠ trie2 ∧ readMap heap2 trie1 = some (.ok [(key1, value1)]) ∧
        readMap heap2 trie2 = some (.ok [(key2, value2)]) ∧
        ∃ n1 n2 slots1 slots2,
          heap2.nodes[trie1]? = some n1 ∧ n1.bitmap = 0 ∧
          heap2.vectors[n1.data]? = some slots1 ∧ slots1.length = 1 ∧
          slots1 = [some (.leaf ⟨key1, value1⟩)] ∧
          heap2.nodes[trie2]? = some n2 ∧ n2.bitmap = 0 ∧
          heap2.vectors[n2.data]? = some slots2 ∧ slots2.length = 1 ∧
          slots2 = [some (.leaf ⟨key2, value2⟩)] ∧
          n1.data ≠ n2.data

def HamtTypedPairSemantics : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (key : K) (value : V) (trie : HAMT K V) (heap : HamtHeap K V),
    HashingLawful same ops →
    runHamt (HAMT.typedPairConstructor heapVectorOps ops (key, value)) HamtHeap.empty = (.ok trie, heap) →
      runPathValue same ops heap trie key = some value

def HamtConvertingPairSemantics : Prop :=
  ∀ (K V Q : Type) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (convert : Q → K × V) (input : Q) (key : K) (value : V)
    (trie : HAMT K V) (heap : HamtHeap K V),
    convert input = (key, value) → HashingLawful same ops →
    runHamt (HAMT.convertPair heapVectorOps ops convert input) HamtHeap.empty = (.ok trie, heap) →
      runPathValue same ops heap trie key = some value

def HamtInferredPairSemantics : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (key : K) (value : V) (trie : HAMT K V) (heap : HamtHeap K V),
    HashingLawful same ops →
    runHamt (HAMT.inferPair heapVectorOps ops (key, value)) HamtHeap.empty = (.ok trie, heap) →
      runPathValue same ops heap trie key = some value

def HamtDepthAlignment : Prop :=
  ∀ (K Q : Type) (ops : HamtObjectIdRuntime K) (other : HashState Q) (key : K),
    let state := HashState.fromOtherAtDepth ops other key
    state.key = key ∧ state.depth = other.depth

def HamtHashProgress : Prop :=
  ∀ (K : Type) (ops : HamtObjectIdRuntime K) (key : K),
    let initial := HashState.fromKey ops key
    let state := advanceHash ops 12 initial
    initial.hash = ops.objectid key ∧ initial.shift = 0 ∧
      (∀ n, n ≤ 11 →
        let level := advanceHash ops n initial
        level.depth = n ∧ level.shift = n * BITS_PER_LEVEL ∧ level.hash = initial.hash) ∧
      state.depth = 12 ∧ state.shift = 0 ∧
        state.hash = JuliaLean.base.hashing.hashUInt64 (ops.objectid key) (JInt.wrap .u64 2)

def HamtSlotRank : Prop :=
  ∀ (K V : Type) (heap : HamtHeap K V) (trie : HAMT K V)
    (bi : BitmapIndex) (data : Nat) (bitmap : BITMAP) (slots : List (Option (Entry K V)))
    (index : Nat),
    heap.nodes[trie]? = some ⟨data, bitmap⟩ → heap.vectors[data]? = some slots →
    heapInvariant heap trie →
      (runHamt (isset trie bi) heap).1 = .ok (Nat.testBit bitmap bi.x) ∧
        (Nat.testBit bitmap bi.x = true →
          (runHamt (entry_index trie bi) heap).1 = .ok index →
            index = countOnes 32 (Nat.land bitmap (shiftLeftNat 1 bi.x - 1)) + 1 ∧
              1 ≤ index ∧ index ≤ slots.length) ∧
        (∀ state : HashState K,
          (BitmapIndex.fromHash state).x =
            Nat.land (shiftRightNat state.hash.val.toNat state.shift) LEVEL_MASK)

def HamtSetBitmapInvariant : Prop :=
  ∀ (K V : Type) (heap heap' : HamtHeap K V) (trie : HAMT K V)
    (bi : BitmapIndex) (node node' : HAMTNode K V) (slots : List (Option (Entry K V)))
    (newBitmap : BITMAP),
    heap.nodes[trie]? = some node → heap.vectors[node.data]? = some slots →
    bi.x < 32 → node.bitmap < 2 ^ 32 →
    (runHamt (isset trie bi) heap).1 = .ok false →
    slots.length = countOnes 32 node.bitmap + 1 →
    runHamt (set! trie bi) heap = (.ok newBitmap, heap') →
    heap'.nodes[trie]? = some node' →
      node'.bitmap = newBitmap ∧ countOnes 32 newBitmap = slots.length ∧
        (∀ bit, bit ≠ bi.x → Nat.testBit newBitmap bit = Nat.testBit node.bitmap bit)

def HamtUnsetBitmapInvariant : Prop :=
  ∀ (K V : Type) (heap heap' : HamtHeap K V) (trie : HAMT K V)
    (bi : BitmapIndex) (node node' : HAMTNode K V) (slots : List (Option (Entry K V)))
    (newBitmap : BITMAP),
    heap.nodes[trie]? = some node → heap.vectors[node.data]? = some slots →
    bi.x < 32 → node.bitmap < 2 ^ 32 →
    (runHamt (isset trie bi) heap).1 = .ok true →
    slots.length + 1 = countOnes 32 node.bitmap →
    runHamt (unset! trie bi) heap = (.ok newBitmap, heap') →
    heap'.nodes[trie]? = some node' →
      node'.bitmap = newBitmap ∧ countOnes 32 newBitmap = slots.length ∧
        (∀ bit, bit ≠ bi.x → Nat.testBit newBitmap bit = Nat.testBit node.bitmap bit)

def HamtPathCopyPreservesMap : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (heap heap1 heap2 : HamtHeap K V) (trie : HAMT K V) (key : K) (value : V)
    (result : PathResult K V) (inserted : Option BITMAP) (before : List (K × V)),
    HashingLawful same ops → heapInvariant heap trie → HamtHashCoherent ops heap trie →
    readMap heap trie = some (.ok before) →
    finiteMapUnique same before →
    runHamt (path heapVectorOps same ops trie (HashState.fromKey ops key) true) heap = (.ok result, heap1) →
    runPartialHamt (insert! heapVectorOps ops result.found result.present result.trie
      result.index result.bi result.hash value) heap1 = some (.ok inserted, heap2) →
    readMap heap2 trie = some (.ok before) ∧
      ∃ after : List (K × V),
        readMap heap2 result.top = some (.ok after) ∧
        finiteLookup same key after = some value

def HamtInsertMapLaws : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (heap heap' : HamtHeap K V) (trie updated : HAMT K V) (key : K) (value : V)
    (before after : List (K × V)),
    HashingLawful same ops → heapInvariant heap trie → HamtHashCoherent ops heap trie →
    readMap heap trie = some (.ok before) →
    finiteMapUnique same before →
    runPartialHamt (persistentInsert heapVectorOps same ops trie key value) heap = some (.ok updated, heap') →
    readMap heap' updated = some (.ok after) →
      finiteLookup same key after = some value ∧
        (∀ other, same other key = false →
          finiteLookup same other after = finiteLookup same other before)

def HamtCopyOnWritePreservesOld : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (heap heap' : HamtHeap K V) (trie updated : HAMT K V) (key : K) (value : V)
    (before after : List (K × V)),
    HashingLawful same ops → heapInvariant heap trie → HamtHashCoherent ops heap trie →
    readMap heap trie = some (.ok before) →
    finiteMapUnique same before →
    runPartialHamt (persistentInsert heapVectorOps same ops trie key value) heap = some (.ok updated, heap') →
    readMap heap' updated = some (.ok after) →
      readMap heap' trie = some (.ok before) ∧ finiteLookup same key after = some value ∧
        (∀ other, same other key = false →
          finiteLookup same other after = finiteLookup same other before)
def HamtInsertReplacesExisting : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (heap heap1 heap2 : HamtHeap K V) (trie : HAMT K V) (key : K) (oldValue value : V)
    (before : List (K × V)) (result : PathResult K V) (inserted : Option BITMAP),
    HashingLawful same ops → heapInvariant heap trie → readMap heap trie = some (.ok before) →
    finiteMapUnique same before →
    runHamt (path heapVectorOps same ops trie (HashState.fromKey ops key)) heap = (.ok result, heap1) →
    result.found = true → result.present = true →
    (runHamt (PathResult.value? heapVectorOps result) heap1).1 = .ok (some oldValue) →
    runPartialHamt (insert! heapVectorOps ops result.found result.present result.trie
      result.index result.bi result.hash value) heap1 = some (.ok inserted, heap2) →
      runPathValue same ops heap2 trie key = some value

def HamtInsertCollisionGrowth : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (heap heap' : HamtHeap K V) (trie updated : HAMT K V)
    (existingKey key : K) (oldValue value : V) (depth : Nat)
    (before after : List (K × V)),
    ops.objectid existingKey ≠ ops.objectid key →
    HashingLawful same ops → same existingKey key = false → 0 < depth →
    (∀ level, level < depth →
      (BitmapIndex.fromHash (advanceHash ops level (HashState.fromKey ops existingKey))).x =
      (BitmapIndex.fromHash (advanceHash ops level (HashState.fromKey ops key))).x) →
    (BitmapIndex.fromHash (advanceHash ops depth (HashState.fromKey ops existingKey))).x ≠
      (BitmapIndex.fromHash (advanceHash ops depth (HashState.fromKey ops key))).x →
    heapInvariant heap trie → HamtHashCoherent ops heap trie →
    readMap heap trie = some (.ok before) →
    finiteLookup same existingKey before = some oldValue →
    finiteMapUnique same before →
    runPathValue same ops heap trie existingKey = some oldValue →
    runPathValue same ops heap trie key = none →
    runPartialHamt (persistentInsert heapVectorOps same ops trie key value) heap = some (.ok updated, heap') →
    readMap heap' updated = some (.ok after) →
      finiteLookup same existingKey after = some oldValue ∧
        finiteLookup same key after = some value

def HamtInsertPreservesBitmapInvariant : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (heap heap' : HamtHeap K V) (trie updated : HAMT K V) (key : K) (value : V),
    HashingLawful same ops → heapInvariant heap trie →
    runPartialHamt (persistentInsert heapVectorOps same ops trie key value) heap = some (.ok updated, heap') →
      heapInvariant heap' updated

namespace Round4

/-- HAMT length returns the wrapping native integer count of leaves across every child node,
regardless of tree depth (`base/hamt.jl:243`). The finite leaf-pair list is bounded below 2^62
entries so the native count does not wrap. -/
def HamtLengthCountsLeavesBounded : Prop :=
  ∀ (K V : Type) (heap : HamtHeap K V) (trie : HAMT K V)
    (length : JuliaLean.JInt .i64) (pairs : List (K × V)),
    heapInvariant heap trie → readMap heap trie = some (.ok pairs) →
    pairs.length < 2 ^ 62 →
    runPartialHamt (lengthHAMT heapVectorOps trie) heap = some (.ok length, heap) →
      length = JuliaLean.JInt.lit .i64 (Int.ofNat pairs.length)

/-- Every valid finite HAMT evaluation returns the leaf count modulo the
native integer width and leaves the store unchanged, without a size limit. -/
def HamtLengthCountsLeaves : Prop :=
  (∀ (K V : Type) (leaf : Leaf K V), lengthLeaf leaf = 1) ∧
  ∀ (K V : Type) (heap : HamtHeap K V) (trie : HAMT K V) (pairs : List (K × V)),
    heapInvariant heap trie → readMap heap trie = some (.ok pairs) →
      runPartialHamt (lengthHAMT heapVectorOps trie) heap =
        some (.ok (JuliaLean.JInt.lit .i64 (Int.ofNat pairs.length)), heap)

end Round4

def HamtEmptyExactlyNoLeaves : Prop :=
  ∀ (K V : Type) (heap : HamtHeap K V) (trie : HAMT K V)
    (empty : Bool) (pairs : List (K × V)),
    heapInvariant heap trie → readMap heap trie = some (.ok pairs) →
    runPartialHamt (isemptyHAMT heapVectorOps trie) heap = some (.ok empty, heap) →
      empty = pairs.isEmpty ∧
        (∀ node, heap.nodes[trie]? = some node →
          (runHamt (islevel_empty trie) heap).1 = .ok (node.bitmap == 0)) ∧
        (∀ leaf : Leaf K V, islevel_empty_leaf leaf = false)

partial def iteratorSequence (heap : HamtHeap K V) (trie : HAMT K V)
    (state : Option (IterState K V) := none) : Except HamtError (List (K × V)) :=
  match runHamt (iterate heapVectorOps trie state) heap with
  | (.error error, _) => .error error
  | (.ok none, _) => .ok []
  | (.ok (some (pair, nextState)), heap') => do
      let rest ← iteratorSequence heap' trie (some nextState)
      pure (pair :: rest)

def HamtIterationExact : Prop :=
  ∀ (K V : Type) (heap : HamtHeap K V) (trie : HAMT K V),
    heapInvariant heap trie → some (iteratorSequence heap trie) = readMap heap trie

private theorem advanceHashBeforeRehash {K : Type} (ops : HamtObjectIdRuntime K) :
    ∀ (n : Nat) (state : HashState K),
      state.shift = state.depth * BITS_PER_LEVEL →
      state.depth + n ≤ 11 →
      (advanceHash ops n state).depth = state.depth + n ∧
        (advanceHash ops n state).shift = (state.depth + n) * BITS_PER_LEVEL ∧
        (advanceHash ops n state).hash = state.hash := by
  intro n
  induction n with
  | zero =>
      intro state hshift hbound
      constructor
      · simp [advanceHash]
      constructor
      · exact hshift
      · rfl
  | succ n ih =>
      intro state hshift hbound
      have hshift5 : state.shift = state.depth * 5 := by
        simpa [BITS_PER_LEVEL] using hshift
      have hno : ¬ state.shift + 5 > 55 := by
        rw [hshift5]
        omega
      have hnext : next ops state =
          ⟨state.key, state.hash, state.depth + 1, state.shift + BITS_PER_LEVEL⟩ := by
        simp [next, BITS_PER_LEVEL, MAX_SHIFT, hno]
      have hnextShift : (next ops state).shift =
          (next ops state).depth * BITS_PER_LEVEL := by
        rw [hnext]
        simp [hshift, BITS_PER_LEVEL]
        omega
      have hnextBound : (next ops state).depth + n ≤ 11 := by
        rw [hnext]
        simp
        omega
      have hstep := ih (next ops state) hnextShift hnextBound
      simp only [advanceHash]
      rcases hstep with ⟨hdepth, ⟨hshift', hhash⟩⟩
      constructor
      · rw [hdepth, hnext]
        simp
        omega
      constructor
      · rw [hshift', hnext]
        simp [BITS_PER_LEVEL]
        omega
      · rw [hhash, hnext]

theorem HamtHashProgress_proven : HamtHashProgress := by
  intro K ops key
  dsimp only
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro n hn
    have hshift : (HashState.fromKey ops key).shift =
        (HashState.fromKey ops key).depth * BITS_PER_LEVEL := by
      simp [HashState.fromKey, BITS_PER_LEVEL]
    have hbound : (HashState.fromKey ops key).depth + n ≤ 11 := by
      simpa [HashState.fromKey] using hn
    have h := advanceHashBeforeRehash ops n (HashState.fromKey ops key) hshift hbound
    simpa [HashState.fromKey, BITS_PER_LEVEL] using h
  constructor
  · rfl
  constructor
  · rfl
  · simp [advanceHash, next, HashState.fromKey, BITS_PER_LEVEL, MAX_SHIFT]

/-! Nothing to promise: HashState(other::HashState,key)@101 forwards to the typed alignment constructor.
Nothing to promise: Base.:(<<)(v,bi::BitmapIndex)@124 and Base.:(>>)(v,bi::BitmapIndex)@125 forward to generic bit-shift operators. -/

private theorem countOnes_or_pow (n x i : Nat) (hi : i < n)
    (hbit : Nat.testBit x i = false) :
    countOnes n (x ||| 2 ^ i) = countOnes n x + 1 := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero =>
          have hx0 : x % 2 = 0 := by
            rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx1
            · exact hx0
            · simp [Nat.testBit_zero, hx1] at hbit
          have hlow : (x ||| 1) % 2 = 1 := by
            rw [Nat.or_mod_two_eq_one]
            simp [hx0]
          have hdiv : (x ||| 1) / 2 = x / 2 := by
            rw [Nat.or_div_two]
            simp
          simp only [countOnes]
          rw [hlow, hdiv, hx0]
          omega
      | succ i =>
          have hbit' : Nat.testBit (x / 2) i = false := by
            simpa only [Nat.testBit_succ] using hbit
          have hpowMod : (2 ^ (i + 1)) % 2 = 0 := by
            rw [Nat.pow_succ]
            simp [Nat.mul_mod]
          have hlow : (x ||| 2 ^ (i + 1)) % 2 = x % 2 := by
            change (x ||| 2 ^ (i + 1)) % 2 ^ 1 = x % 2 ^ 1
            rw [Nat.or_mod_two_pow]
            simp [hpowMod]
          have hpowDiv : (2 ^ (i + 1)) / 2 = 2 ^ i := by
            rw [Nat.pow_succ]
            simp
          have hdiv : (x ||| 2 ^ (i + 1)) / 2 = x / 2 ||| 2 ^ i := by
            rw [Nat.or_div_two, hpowDiv]
          simp only [countOnes, hlow, hdiv]
          have htail := ih (x / 2) i (by omega) hbit'
          omega

theorem HamtSetBitmapInvariant_proven : HamtSetBitmapInvariant := by
  intro K V heap heap' trie bi node node' slots newBitmap hnode hslots hbit hbound hisset hlength hrun hnode'
  have hpow : 2 ^ bi.x < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hbit
  have hor : node.bitmap ||| 2 ^ bi.x < 2 ^ 32 := Nat.or_lt_two_pow hbound hpow
  have hu32 : u32 (node.bitmap ||| 2 ^ bi.x) = node.bitmap ||| 2 ^ bi.x := by
    change (node.bitmap ||| 2 ^ bi.x) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt hor
  have hnotMod : node.bitmap / 2 ^ bi.x % 2 = 0 := by
    simpa [runHamt, isset, nodeBitmap, readNode, shiftRightNat, hnode,
      MonadState.get, MonadStateOf.get, StateT.run_map, StateT.map,
      Functor.map, Except.map, getThe, liftM, monadLift, MonadLift.monadLift,
      ExceptT.lift, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
      ExceptT.bindCont, StateT.run, StateT.bind, StateT.pure, StateT.get,
      StateT.set, Bind.bind, Pure.pure] using hisset
  have hnot : Nat.testBit node.bitmap bi.x = false := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp [hnotMod]
  have hnewU32 : u32 (node.bitmap ||| 2 ^ bi.x) = newBitmap := by
    simpa [runHamt, set!, nodeBitmap, readNode, u32, shiftLeftNat, hnode,
      MonadState.get, MonadState.set, MonadStateOf.get, MonadStateOf.set,
      StateT.run_map, StateT.map, Functor.map, Except.map, getThe, liftM,
      monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.run, ExceptT.bind,
      ExceptT.pure, ExceptT.mk, ExceptT.bindCont, StateT.run, StateT.bind,
      StateT.pure, StateT.get, StateT.set, Bind.bind, Pure.pure] using
      congrArg Prod.fst hrun
  have hnew : newBitmap = node.bitmap ||| 2 ^ bi.x :=
    hnewU32.symm.trans hu32
  have hheap : heap' =
      {heap with nodes := heap.nodes.set trie {node with bitmap := node.bitmap ||| 2 ^ bi.x}} := by
    simpa [runHamt, set!, nodeBitmap, readNode, shiftLeftNat, hnode, hu32,
      MonadState.get, MonadState.set, MonadStateOf.get, MonadStateOf.set,
      StateT.run_map, StateT.map, Functor.map, Except.map, getThe, liftM,
      monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.run, ExceptT.bind,
      ExceptT.pure, ExceptT.mk, ExceptT.bindCont, StateT.run, StateT.bind,
      StateT.pure, StateT.get, StateT.set, Bind.bind, Pure.pure] using
      (congrArg Prod.snd hrun).symm
  have hindex : trie < heap.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hnodeAfter :
      heap'.nodes[trie]? = some {node with bitmap := node.bitmap ||| 2 ^ bi.x} := by
    rw [hheap]
    simp [hindex]
  have hnodeValue : node' = {node with bitmap := node.bitmap ||| 2 ^ bi.x} :=
    Option.some.inj (hnode'.symm.trans hnodeAfter)
  have hbitmap : node'.bitmap = newBitmap := by
    rw [hnodeValue]
    simp [hnew]
  have hcount : countOnes 32 newBitmap = slots.length := by
    rw [hnew, countOnes_or_pow 32 node.bitmap bi.x hbit hnot]
    exact hlength.symm
  have hpreserve : ∀ bit, bit ≠ bi.x →
      Nat.testBit newBitmap bit = Nat.testBit node.bitmap bit := by
    intro bit hne
    rw [hnew]
    have hbitne : bi.x ≠ bit := fun heq => hne heq.symm
    simp [Nat.testBit_or, Nat.testBit_two_pow, hbitne]
  exact ⟨hbitmap, hcount, hpreserve⟩

theorem HamtUnsetBitmapInvariant_proven : HamtUnsetBitmapInvariant := by
  intro K V heap heap' trie bi node node' slots newBitmap hnode hslots hbit hbound hisset hlength hrun hnode'
  let cleared := node.bitmap &&& (MASK32 ^^^ 2 ^ bi.x)
  have hsetMod : node.bitmap / 2 ^ bi.x % 2 = 1 := by
    simpa [runHamt, isset, nodeBitmap, readNode, shiftRightNat, hnode,
      MonadState.get, MonadStateOf.get, StateT.run_map, StateT.map,
      Functor.map, Except.map, getThe, liftM, monadLift, MonadLift.monadLift,
      ExceptT.lift, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
      ExceptT.bindCont, StateT.run, StateT.bind, StateT.pure, StateT.get,
      StateT.set, Bind.bind, Pure.pure] using hisset
  have hbitSet : Nat.testBit node.bitmap bi.x = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp [hsetMod]
  have hmaskAt : Nat.testBit MASK32 bi.x = true := by
    change Nat.testBit (2 ^ 32 - 1) bi.x = true
    simpa [hbit] using Nat.testBit_two_pow_sub_one 32 bi.x
  have hclearBit : Nat.testBit cleared bi.x = false := by
    simp [cleared, Nat.testBit_and, Nat.testBit_xor, hmaskAt, hbitSet]
  have hrestore : node.bitmap = cleared ||| 2 ^ bi.x := by
    apply Nat.eq_of_testBit_eq
    intro bit
    by_cases hxi : bit = bi.x
    · subst bit
      simp [cleared, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
        hmaskAt, hbitSet]
    · have hpowne : bi.x ≠ bit := fun heq => hxi heq.symm
      by_cases hlow : bit < 32
      · have hmaskBit : Nat.testBit MASK32 bit = true := by
          change Nat.testBit (2 ^ 32 - 1) bit = true
          simpa [hlow] using Nat.testBit_two_pow_sub_one 32 bit
        simp [cleared, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
          Nat.testBit_two_pow, hmaskBit, hpowne]
      · have hmaskBit : Nat.testBit MASK32 bit = false := by
          change Nat.testBit (2 ^ 32 - 1) bit = false
          simpa [hlow] using Nat.testBit_two_pow_sub_one 32 bit
        have hpowBound : 2 ^ 32 ≤ 2 ^ bit :=
          Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
        have hbitmapBound : node.bitmap < 2 ^ bit :=
          Nat.lt_of_lt_of_le hbound hpowBound
        have hbitmapBit : Nat.testBit node.bitmap bit = false :=
          Nat.testBit_lt_two_pow hbitmapBound
        simp [cleared, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
          Nat.testBit_two_pow, hmaskBit, hpowne, hbitmapBit]
  have hnewRaw : cleared = newBitmap := by
    simpa [runHamt, unset!, nodeBitmap, readNode, MASK32, shiftLeftNat,
      cleared, hnode, MonadState.get, MonadState.set, MonadStateOf.get,
      MonadStateOf.set, StateT.run_map, StateT.map, Functor.map, Except.map,
      getThe, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
      ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.set,
      Bind.bind, Pure.pure] using congrArg Prod.fst hrun
  have hnew : newBitmap = cleared := hnewRaw.symm
  have hheap : heap' =
      {heap with nodes := heap.nodes.set trie {node with bitmap := cleared}} := by
    simpa [runHamt, unset!, nodeBitmap, readNode, MASK32, shiftLeftNat,
      cleared, hnode, MonadState.get, MonadState.set, MonadStateOf.get,
      MonadStateOf.set, StateT.run_map, StateT.map, Functor.map, Except.map,
      getThe, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
      ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.set,
      Bind.bind, Pure.pure] using (congrArg Prod.snd hrun).symm
  have hindex : trie < heap.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hnodeAfter : heap'.nodes[trie]? = some {node with bitmap := cleared} := by
    rw [hheap]
    simp [hindex]
  have hnodeValue : node' = {node with bitmap := cleared} :=
    Option.some.inj (hnode'.symm.trans hnodeAfter)
  have hbitmap : node'.bitmap = newBitmap := by
    rw [hnodeValue]
    simp [hnew]
  have hcountDrop : countOnes 32 node.bitmap = countOnes 32 cleared + 1 := by
    rw [hrestore]
    exact countOnes_or_pow 32 cleared bi.x hbit hclearBit
  have hlen : slots.length = countOnes 32 cleared := by omega
  have hcount : countOnes 32 newBitmap = slots.length := by
    rw [hnew]
    exact hlen.symm
  have hpreserve : ∀ bit, bit ≠ bi.x →
      Nat.testBit newBitmap bit = Nat.testBit node.bitmap bit := by
    intro bit hne
    rw [hnew]
    have hpowne : bi.x ≠ bit := fun heq => hne heq.symm
    have hbitEq : Nat.testBit node.bitmap bit = Nat.testBit cleared bit := by
      rw [hrestore]
      simp [Nat.testBit_or, Nat.testBit_two_pow, hpowne]
    exact hbitEq.symm
  exact ⟨hbitmap, hcount, hpreserve⟩

private def runToDepthStep {K : Type} (ops : HamtObjectIdRuntime K) (target : Nat) :
    Unit → HashState K → Id (ForInStep (HashState K)) :=
  fun _ current =>
    if current.depth = target then pure (ForInStep.done current)
    else pure (ForInStep.yield (next ops current))

private def runToDepth {K : Type} (ops : HamtObjectIdRuntime K) (target : Nat)
    (state : HashState K) : HashState K :=
  Lean.Loop.forIn (m := Id) (β := HashState K) (⟨⟩ : Lean.Loop) state
    (runToDepthStep ops target)

private theorem runToDepth_key_depth {K : Type} (ops : HamtObjectIdRuntime K) (target : Nat) :
    ∀ state : HashState K, state.depth ≤ target →
      (runToDepth ops target state).key = state.key ∧
      (runToDepth ops target state).depth = target := by
  have aux : ∀ rem, ∀ state : HashState K, target - state.depth = rem →
      state.depth ≤ target →
        (runToDepth ops target state).key = state.key ∧
        (runToDepth ops target state).depth = target := by
    intro rem
    induction rem using Nat.strongRecOn with
    | ind rem ih =>
      intro state hrem hle
      by_cases hdone : state.depth = target
      · have hloop : runToDepth ops target state = state := by
          change Lean.Loop.forIn (m := Id) (β := HashState K) (⟨⟩ : Lean.Loop) state
            (runToDepthStep ops target) = _
          rw [Lean.Loop.forIn_eq_of_monadTail]
          simp [runToDepthStep, hdone] <;> rfl
        rw [hloop]
        exact ⟨rfl, hdone⟩
      · have hlt : state.depth < target := by omega
        have hnextDepth : (next ops state).depth = state.depth + 1 := by
          unfold next
          dsimp
          split <;> rfl
        have hnextKey : (next ops state).key = state.key := by
          unfold next
          dsimp
          split <;> rfl
        have hnextBound : (next ops state).depth ≤ target := by omega
        have hnextRem : target - (next ops state).depth < rem := by
          rw [hnextDepth]
          omega
        have hnext := ih (target - (next ops state).depth) hnextRem
          (next ops state) rfl hnextBound
        have hloop : runToDepth ops target state = runToDepth ops target (next ops state) := by
          change Lean.Loop.forIn (m := Id) (β := HashState K) (⟨⟩ : Lean.Loop) state
            (runToDepthStep ops target) = _
          rw [Lean.Loop.forIn_eq_of_monadTail]
          simp [runToDepthStep, hdone] <;> rfl
        rw [hloop]
        exact ⟨by simpa [hnextKey] using hnext.1, hnext.2⟩
  intro state hle
  exact aux (target - state.depth) state rfl hle

theorem HamtDepthAlignment_proven : HamtDepthAlignment := by
  intro K Q ops other key
  dsimp only
  have h := runToDepth_key_depth ops other.depth (HashState.fromKey ops key) (by simp [HashState.fromKey])
  simpa [HashState.fromOtherAtDepth, HashState.fromKey, runToDepth, runToDepthStep,
    ForIn.forIn, Lean.Loop.forIn, Id.run] using h

theorem hamtGetRun {K V : Type} (heap : HamtHeap K V) :
    (get : HamtM K V (HamtHeap K V)).run heap = (.ok heap, heap) := rfl

theorem hamtSetRun {K V : Type} (heap heap' : HamtHeap K V) :
    (set heap' : HamtM K V Unit).run heap = (.ok (), heap') := rfl

private theorem hamtInnerRun {K V : Type} (heap : HamtHeap K V) (data bitmap : Nat) :
    runHamt (HAMT.inner data bitmap) heap =
      (.ok heap.nodes.length, {heap with nodes := heap.nodes ++ [⟨data, bitmap⟩]}) := rfl

private theorem hamtBindRun {K V α β : Type} (action : HamtM K V α)
    (next : α → HamtM K V β) (heap : HamtHeap K V) :
    (action >>= next).run heap =
      match action.run heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok value, heap') => (next value).run heap' := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : action heap with
  | mk result after => cases result <;> rfl

private theorem heapVectorSetRun {K V : Type} (heap : HamtHeap K V) (data index : Nat)
    (entry : Entry K V) (slots : List (Option (Entry K V)))
    (hslots : heap.vectors[data]? = some slots) (hlo : 1 ≤ index) (hhi : index ≤ slots.length) :
    runHamt (heapVectorOps.set data index entry) heap =
      (.ok (), {heap with vectors := heap.vectors.set data (slots.set (index - 1) (some entry))}) := by
  change (heapVectorSet data index entry).run heap = _
  unfold heapVectorSet
  rw [hamtBindRun, hamtGetRun]
  have hbound : ¬ (index = 0 ∨ slots.length < index) := by omega
  simp [hslots, hbound, hamtSetRun]

theorem HamtInnerSharesVector_proven : HamtInnerSharesVector := by
  intro K V heap data bitmap index entry slots trie heap1 heap2 hslots hlo hhi hinner hset
  have hindex : index - 1 < slots.length := by omega
  rw [hamtInnerRun] at hinner
  simp only [Prod.mk.injEq, Except.ok.injEq] at hinner
  rcases hinner with ⟨rfl, hheap1⟩
  have hslots1 : heap1.vectors[data]? = some slots := by
    rw [← hheap1]
    exact hslots
  have hsetRun := heapVectorSetRun heap1 data index entry slots hslots1 hlo hhi
  rw [hsetRun] at hset
  simp only [Prod.mk.injEq, Except.ok.injEq] at hset
  rcases hset with ⟨_, rfl⟩
  subst heap1
  have hdata : data < heap.vectors.length := (List.getElem?_eq_some_iff.mp hslots).1
  refine ⟨⟨data, bitmap⟩, slots.set (index - 1) (some entry), ?_⟩
  constructor
  · simp
  constructor
  · rfl
  constructor
  · exact List.getElem?_set_self hdata
  · exact List.getElem?_set_self hindex
private theorem runHamtBind {K V α β : Type} (action : HamtM K V α)
    (next : α → HamtM K V β) (heap : HamtHeap K V) :
    runHamt (action >>= next) heap =
      match action.run heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok value, heap') => (next value).run heap' := by
  change (action >>= next).run heap = _
  exact hamtBindRun action next heap

private theorem heapVectorAllocateRun {K V : Type} (heap : HamtHeap K V)
    (slots : List (Option (Entry K V))) :
    (heapVectorAllocate slots).run heap =
      (.ok heap.vectors.length, {heap with vectors := heap.vectors ++ [slots]}) := rfl
private theorem emptyHamtRun {K V : Type} (heap : HamtHeap K V) :
    runHamt (HAMT.emptyConstructor heapVectorOps) heap =
      (.ok heap.nodes.length,
        { heap with
          vectors := heap.vectors ++ [[]]
          nodes := heap.nodes ++ [⟨heap.vectors.length, 0⟩] }) := by
  simp only [HAMT.emptyConstructor, heapVectorOps, runHamtBind, heapVectorAllocateRun,
    hamtBindRun, hamtGetRun, hamtSetRun]
  rfl

theorem HamtEmptyAllocatesIndependently_proven : HamtEmptyAllocatesIndependently := by
  intro K V heap heap1 heap2 heap3 first second bit bitmap h1 h2 h3
  have h1' : heap.nodes.length = first ∧
      { heap with
          vectors := heap.vectors ++ [[]]
          nodes := heap.nodes ++ [⟨heap.vectors.length, 0⟩] } = heap1 := by
    simpa [emptyHamtRun] using h1
  rcases h1' with ⟨hfirst, hheap1⟩
  have h2' : heap1.nodes.length = second ∧
      { heap1 with
          vectors := heap1.vectors ++ [[]]
          nodes := heap1.nodes ++ [⟨heap1.vectors.length, 0⟩] } = heap2 := by
    simpa [emptyHamtRun] using h2
  rcases h2' with ⟨hsecond, hheap2⟩
  have hfirstIndex : first = heap.nodes.length := hfirst.symm
  have h3'' := h3
  rw [← hheap2, ← hheap1] at h3''
  have h3' : u32 (Nat.lor 0 (shiftLeftNat 1 bit.x)) = bitmap ∧
      HamtHeap.mk heap2.vectors
        (List.set heap2.nodes heap.nodes.length
          (HAMTNode.mk heap.vectors.length
            (u32 (Nat.lor 0 (shiftLeftNat 1 bit.x))))) = heap3 := by
    rw [← hheap2, ← hheap1]
    simpa [hfirstIndex, runHamt, set!, readNode, heapVectorOps,
      MonadState.get, MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
      MonadState.set, MonadStateOf.set,
      hamtBindRun, hamtGetRun, hamtSetRun,
      StateT.run_map, StateT.map, Functor.map, ExceptT.map, Except.map,
      ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.set,
      Bind.bind, Pure.pure, List.append_assoc] using h3''
  rcases h3' with ⟨_, hheap3⟩
  have hsecondIndex : second = heap.nodes.length + 1 := by
    calc
      second = heap1.nodes.length := hsecond.symm
      _ = heap.nodes.length + 1 := by
        rw [← hheap1]
        simp [List.length_append]
  have hdistinct : first ≠ second := by
    intro h
    have hlen : heap.nodes.length = heap.nodes.length + 1 :=
      hfirstIndex.symm.trans (h.trans hsecondIndex)
    omega
  clear hfirst hsecond
  subst first
  subst second
  subst heap3
  subst heap2
  subst heap1
  refine ⟨hdistinct, ?_⟩
  refine ⟨⟨heap.vectors.length, 0⟩,
    ⟨heap.vectors.length + 1, 0⟩,
    ⟨heap.vectors.length + 1, 0⟩,
    [], [], [], ?_⟩
  simp [runHamt, islevel_empty, nodeBitmap, readNode, heapVectorOps,
    MonadState.get, MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
    hamtBindRun, hamtGetRun, hamtSetRun,
    StateT.run_map, StateT.map, Functor.map, ExceptT.map, Except.map,
    ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
    ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.set,
    Bind.bind, Pure.pure, List.append_assoc, List.length_append]
private theorem initTryGetRun {K V : Type} (heap : HamtHeap K V) :
    (get : HamtM K V (HamtHeap K V)).run heap = (.ok heap, heap) := rfl

private theorem initTrySetRun {K V : Type} (heap heap' : HamtHeap K V) :
    (set heap' : HamtM K V Unit).run heap = (.ok (), heap') := rfl

private theorem initTryBindRun {K V α β : Type} (action : HamtM K V α)
    (next : α → HamtM K V β) (heap : HamtHeap K V) :
    (action >>= next).run heap =
      match action.run heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok value, heap') => (next value).run heap' := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : action heap with
  | mk result after => cases result <;> rfl

private theorem initTryRunHamtBind {K V α β : Type} (action : HamtM K V α)
    (next : α → HamtM K V β) (heap : HamtHeap K V) :
    runHamt (action >>= next) heap =
      match action.run heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok value, heap') => (next value).run heap' := by
  change (action >>= next).run heap = _
  exact initTryBindRun action next heap

private theorem initTryHeapVectorAllocateRun {K V : Type} (heap : HamtHeap K V)
    (slots : List (Option (Entry K V))) :
    (heapVectorAllocate slots).run heap =
      (.ok heap.vectors.length, {heap with vectors := heap.vectors ++ [slots]}) := by
  rfl

private theorem initTryHeapVectorSetRun {K V : Type} (heap : HamtHeap K V) (data index : Nat)
    (entry : Entry K V) (slots : List (Option (Entry K V)))
    (hslots : heap.vectors[data]? = some slots) (hlo : 1 ≤ index) (hhi : index ≤ slots.length) :
    (heapVectorSet data index entry).run heap =
      (.ok (), {heap with vectors := heap.vectors.set data (slots.set (index - 1) (some entry))}) := by
  change (heapVectorSet data index entry).run heap = _
  unfold heapVectorSet
  rw [initTryBindRun, initTryGetRun]
  have hbound : ¬ (index = 0 ∨ slots.length < index) := by omega
  simp [hslots, hbound, initTrySetRun]

private theorem initTryInitHamtRun {K V : Type} (heap : HamtHeap K V) (key : K) (value : V) :
    runHamt (init_hamt heapVectorOps key value) heap =
      (.ok heap.nodes.length,
        { heap with
          vectors := heap.vectors ++ [[some (.leaf ⟨key, value⟩)]]
          nodes := heap.nodes ++ [⟨heap.vectors.length, 0⟩] }) := by
  simp only [init_hamt, heapVectorOps, initTryRunHamtBind, initTryHeapVectorAllocateRun,
    initTryBindRun, initTryGetRun, initTrySetRun]
  let nodeHeap : HamtHeap K V :=
    { vectors := heap.vectors ++ [[none]]
      nodes := heap.nodes ++ [⟨heap.vectors.length, 0⟩] }
  have hslots : nodeHeap.vectors[heap.vectors.length]? = some [none] := by
    simp [nodeHeap]
  have hset := initTryHeapVectorSetRun nodeHeap heap.vectors.length 1
    (.leaf ⟨key, value⟩) [none] hslots (by omega) (by simp)
  rw [hset]
  simp [ExceptT.run, ExceptT.pure, StateT.pure, nodeHeap,
    List.set_append_right, List.append_assoc] <;> rfl

theorem HamtInitSingleIsolated_proven : HamtInitSingleIsolated := by
  intro K V heap heap1 heap2 key1 key2 value1 value2 trie1 trie2 h1 h2
  have h1' : heap.nodes.length = trie1 ∧
      { heap with
        vectors := heap.vectors ++ [[some (.leaf ⟨key1, value1⟩)]]
        nodes := heap.nodes ++ [⟨heap.vectors.length, 0⟩] } = heap1 := by
    simpa [initTryInitHamtRun] using h1
  rcases h1' with ⟨htrie1, hheap1⟩
  have h2' : heap1.nodes.length = trie2 ∧
      { heap1 with
        vectors := heap1.vectors ++ [[some (.leaf ⟨key2, value2⟩)]]
        nodes := heap1.nodes ++ [⟨heap1.vectors.length, 0⟩] } = heap2 := by
    simpa [initTryInitHamtRun] using h2
  rcases h2' with ⟨htrie2, hheap2⟩
  have htrie1Index : trie1 = heap.nodes.length := htrie1.symm
  have htrie2Index : trie2 = heap.nodes.length + 1 := by
    calc
      trie2 = heap1.nodes.length := htrie2.symm
      _ = heap.nodes.length + 1 := by
        rw [← hheap1]
        simp [List.length_append]
  have hneq : trie1 ≠ trie2 := by
    intro h
    have hlen : heap.nodes.length = heap.nodes.length + 1 :=
      htrie1Index.symm.trans (h.trans htrie2Index)
    omega
  clear htrie1 htrie2
  subst trie1
  subst trie2
  subst heap2
  subst heap1
  refine ⟨hneq, ?_, ?_, ?_⟩
  · simp [readMap, heapMap, heapEntriesMap, List.append_assoc]
  · simp [readMap, heapMap, heapEntriesMap, List.append_assoc]
  · refine ⟨⟨heap.vectors.length, 0⟩,
      ⟨heap.vectors.length + 1, 0⟩,
      [some (.leaf ⟨key1, value1⟩)], [some (.leaf ⟨key2, value2⟩)], ?_⟩
    simp [readMap, heapMap, heapEntriesMap, List.append_assoc, List.length_append] <;> omega

private theorem countOnes_zero : ∀ n, countOnes n 0 = 0
  | 0 => rfl
  | n + 1 => by simp [countOnes, countOnes_zero n]

private theorem natBeqEq (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

private theorem countOnesPrefixLe : ∀ (n x i : Nat),
    i < n → Nat.testBit x i = true →
      countOnes n (x &&& (2 ^ i - 1)) + 1 ≤ countOnes n x := by
  intro n
  induction n with
  | zero =>
      intro x i hi
      omega
  | succ n ih =>
      intro x i hi hbit
      cases i with
      | zero =>
          have hx : x % 2 = 1 := by simpa using hbit
          simp [countOnes, countOnes_zero, hx]
      | succ i =>
          have hbit' : Nat.testBit (x / 2) i = true := by
            simpa only [Nat.testBit_succ] using hbit
          have hi' : i < n := by omega
          have hmaskOdd : (2 ^ (i + 1) - 1) % 2 = 1 := by
            simpa using Nat.two_pow_sub_one_mod_two (i + 1)
          have hlow : (x &&& (2 ^ (i + 1) - 1)) % 2 = x % 2 := by
            rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx1
            · have hnotOne : (x &&& (2 ^ (i + 1) - 1)) % 2 ≠ 1 := by
                intro h
                have hboth := Nat.and_mod_two_eq_one.mp h
                omega
              rcases Nat.mod_two_eq_zero_or_one (x &&& (2 ^ (i + 1) - 1)) with hzero | hone
              · omega
              · exact (hnotOne hone).elim
            · have hland := Nat.and_mod_two_eq_one.mpr ⟨hx1, hmaskOdd⟩
              omega
          have hmaskDiv : (2 ^ (i + 1) - 1) / 2 = 2 ^ i - 1 := by
            rw [Nat.pow_succ]
            omega
          have hquot :
              (x &&& (2 ^ (i + 1) - 1)) / 2 = (x / 2) &&& (2 ^ i - 1) := by
            rw [Nat.and_div_two, hmaskDiv]
          simp only [countOnes, hlow, hquot]
          have htail := ih (x / 2) i hi' hbit'
          omega

theorem HamtSlotRank_proven : HamtSlotRank := by
  intro K V heap trie bi data bitmap slots index hnode hslots hinv
  have hinv' : bitmap < 2 ^ 32 ∧ countOnes 32 bitmap = slots.length := by
    cases hinv with
    | node hnodeInv hslotsInv hbitmap hcount hentries =>
      cases Option.some.inj (hnodeInv.symm.trans hnode)
      cases Option.some.inj (hslotsInv.symm.trans hslots)
      exact ⟨hbitmap, hcount⟩
  have hset :
      (runHamt (isset trie bi) heap).1 = .ok (Nat.testBit bitmap bi.x) := by
    simp [runHamt, isset, nodeBitmap, readNode, hnode, shiftRightNat,
      Nat.testBit_eq_decide_div_mod_eq, natBeqEq, MonadState.get,
      MonadStateOf.get, StateT.run_map, StateT.map, Functor.map, Except.map,
      getThe, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.run,
      ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, StateT.run,
      StateT.bind, StateT.pure, StateT.get, StateT.set, Bind.bind, Pure.pure]
  have hentry : (runHamt (entry_index trie bi) heap).1 =
      .ok (countOnes 32 (bitmap &&& (2 ^ bi.x - 1)) + 1) := by
    simp [runHamt, entry_index, nodeBitmap, readNode, hnode, shiftLeftNat,
      MonadState.get, MonadStateOf.get, StateT.run_map, StateT.map,
      Functor.map, Except.map, getThe, liftM, monadLift, MonadLift.monadLift,
      ExceptT.lift, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
      ExceptT.bindCont, StateT.run, StateT.bind, StateT.pure, StateT.get,
      StateT.set, Bind.bind, Pure.pure]
  constructor
  · exact hset
  constructor
  · intro hbit hrun
    have hindexRaw : index = countOnes 32 (bitmap &&& (2 ^ bi.x - 1)) + 1 :=
      Except.ok.inj (hrun.symm.trans hentry)
    have hindex :
        index = countOnes 32 (Nat.land bitmap (shiftLeftNat 1 bi.x - 1)) + 1 := by
      simpa [shiftLeftNat] using hindexRaw
    have hbi : bi.x < 32 := by
      by_cases h : bi.x < 32
      · exact h
      · have hpow : 2 ^ 32 ≤ 2 ^ bi.x :=
          Nat.pow_le_pow_right Nat.zero_lt_two (Nat.not_lt.mp h)
        have hge := Nat.ge_two_pow_of_testBit hbit
        have hbound := hinv'.1
        have hpowlt : 2 ^ bi.x < 2 ^ 32 := Nat.lt_of_le_of_lt hge hbound
        exact False.elim ((Nat.not_lt_of_ge hpow) hpowlt)
    have hrank := countOnesPrefixLe 32 bitmap bi.x hbi hbit
    have hrankSlots : countOnes 32 (bitmap &&& (2 ^ bi.x - 1)) + 1 ≤ slots.length := by
      rw [← hinv'.2]
      exact hrank
    constructor
    · exact hindex
    constructor
    · rw [hindex]
      omega
    · rw [hindex]
      simpa [shiftLeftNat] using hrankSlots
  · intro state
    rfl
set_option maxHeartbeats 1000000

private theorem runHamtBindEq {K V α β : Type} (action : HamtM K V α)
    (next : α → HamtM K V β) (heap : HamtHeap K V) :
    runHamt (action >>= next) heap =
      match runHamt action heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok value, heap') => runHamt (next value) heap' := by
  change Id.run ((action >>= next).run heap) =
    match Id.run (action.run heap) with
    | (.error error, heap') => (.error error, heap')
    | (.ok value, heap') => Id.run ((next value).run heap')
  exact congrArg Id.run (hamtBindRun action next heap)

private theorem heapVectorCopyRun {K V : Type} (heap : HamtHeap K V)
    (handle : Nat) (slots : List (Option (Entry K V)))
    (hslots : heap.vectors[handle]? = some slots) :
    runHamt (heapVectorCopy handle) heap =
      (.ok heap.vectors.length, {heap with vectors := heap.vectors ++ [slots]}) := by
  change runHamt (heapVectorSlots handle >>= heapVectorAllocate) heap = _
  rw [runHamtBindEq]
  have hget : runHamt (get : HamtM K V (HamtHeap K V)) heap = (.ok heap, heap) := rfl
  have hread : runHamt (heapVectorSlots handle) heap = (.ok slots, heap) := by
    unfold heapVectorSlots
    rw [runHamtBindEq, hget]
    simp [runHamt, hslots, ExceptT.pure, StateT.pure, StateT.run, Pure.pure]
  rw [hread]
  change (heapVectorAllocate slots).run heap = _
  exact heapVectorAllocateRun heap slots
private theorem readNode_frame {K V : Type} (heap : HamtHeap K V)
    (written read : HAMT K V) (node : HAMTNode K V) (hne : read ≠ written) :
    (runHamt (readNode read) { heap with nodes := heap.nodes.set written node }).1 =
      (runHamt (readNode read) heap).1 := by
  have hne' : written ≠ read := Ne.symm hne
  cases hread : heap.nodes[read]? <;>
    simp [runHamt, readNode, hread, hne', List.getElem?_set,
      MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
      MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run,
      ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.lift,
      StateT.run, StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure,
      throw, throwThe, MonadExceptOf.throw]


private theorem readNode_setFrame {K V : Type} (heap : HamtHeap K V)
    (written read : HAMT K V) (node : HAMTNode K V) (bi : BitmapIndex)
    (hne : read ≠ written)
    (hnode : heap.nodes[written]? = some node)
    (bitmap : BITMAP) (heap' : HamtHeap K V)
    (hset : runHamt (set! written bi) heap = (.ok bitmap, heap')) :
    (runHamt (readNode read) heap').1 = (runHamt (readNode read) heap).1 := by
  let node' : HAMTNode K V :=
    { node with bitmap := u32 (Nat.lor node.bitmap (shiftLeftNat 1 bi.x)) }
  have hshape : runHamt (set! written bi) heap =
      (.ok node'.bitmap, { heap with nodes := heap.nodes.set written node' }) := by
    simp [runHamt, set!, readNode, node', hnode, MonadState.get, MonadStateOf.get,
      getThe, liftM, monadLift, MonadLift.monadLift, StateT.map, Functor.map,
      ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.set,
      MonadStateOf.set, set, Bind.bind, Pure.pure]
  have hheap : heap' = { heap with nodes := heap.nodes.set written node' } := by
    exact congrArg Prod.snd (hset.symm.trans hshape)
  subst heap'
  exact readNode_frame heap written read node' hne

private theorem heapDataDiffAtParentSlot {K V : Type} (heap : HamtHeap K V)
    {child : HAMT K V} (hinv : heapInvariant heap child)
    (parentData : Nat) (parentSlots : List (Option (Entry K V)))
    (hparentSlots : heap.vectors[parentData]? = some parentSlots)
    (i : Nat) (hslot : parentSlots[i]? = some (some (.trie child)))
    (childNode : HAMTNode K V) (hchildNode : heap.nodes[child]? = some childNode) :
    childNode.data ≠ parentData := by
  let motiveNode : (child : HAMT K V) → heapInvariant heap child → Prop :=
    fun child _ =>
      ∀ (parentData : Nat) (parentSlots : List (Option (Entry K V))),
        heap.vectors[parentData]? = some parentSlots →
        ∀ (i : Nat), parentSlots[i]? = some (some (Entry.trie child)) →
        ∀ childNode, heap.nodes[child]? = some childNode →
          childNode.data ≠ parentData
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant heap slots → Prop :=
    fun slots _ =>
      ∀ (parentData : Nat) (wholeSlots pre : List (Option (Entry K V))),
        heap.vectors[parentData]? = some wholeSlots →
        wholeSlots = pre ++ slots →
        ∀ (i : Nat) target, slots[i]? = some (some (Entry.trie target)) →
        ∀ targetNode, heap.nodes[target]? = some targetNode →
          targetNode.data ≠ parentData
  have hrec : motiveNode child hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro trie node slots hnode hslots hbitmap hcount hentries ihEntries
        parentData parentSlots hparentSlots i hparentSlot node' hnode'
      intro hdata
      have hnodeEq : node' = node := Option.some.inj (hnode'.symm.trans hnode)
      have hdataEq : node.data = parentData := by
        calc
          node.data = node'.data := (congrArg HAMTNode.data hnodeEq).symm
          _ = parentData := hdata
      have hslotsParent : heap.vectors[parentData]? = some slots := by
        simpa [hdataEq] using hslots
      have hslotsEq : parentSlots = slots :=
        Option.some.inj (hparentSlots.symm.trans hslotsParent)
      have hself : slots[i]? = some (some (.trie trie)) := by
        simpa [hslotsEq] using hparentSlot
      have hnotSelf := ihEntries node.data slots [] hslots (by simp) i trie hself node hnode
      exact hnotSelf rfl
    · intro parentData wholeSlots pre hparentSlots hwhole i target hslot targetNode htargetNode
      cases i <;> simp at hslot
    · intro leaf rest hrest ihRest parentData wholeSlots pre hparentSlots hwhole i target hslot targetNode htargetNode
      cases i with
      | zero => simp at hslot
      | succ i =>
          have hslot' : rest[i]? = some (some (.trie target)) := by simpa using hslot
          have hwhole' : wholeSlots = (pre ++ [some (.leaf leaf)]) ++ rest := by
            simpa [List.append_assoc] using hwhole
          exact ihRest parentData wholeSlots (pre ++ [some (.leaf leaf)])
            hparentSlots hwhole' i target hslot' targetNode htargetNode
    · intro child rest hchild hrest ihChild ihRest parentData wholeSlots pre hparentSlots hwhole i target hslot targetNode htargetNode
      cases i with
      | zero =>
          have hchildEq : child = target := by simpa using hslot
          subst target
          have hslotWhole : wholeSlots[pre.length]? = some (some (.trie child)) := by
            rw [hwhole]
            simp
          exact ihChild parentData wholeSlots hparentSlots pre.length hslotWhole
            targetNode htargetNode
      | succ i =>
          have hslot' : rest[i]? = some (some (.trie target)) := by simpa using hslot
          have hwhole' : wholeSlots = (pre ++ [some (.trie child)]) ++ rest := by
            simpa [List.append_assoc] using hwhole
          exact ihRest parentData wholeSlots (pre ++ [some (.trie child)])
            hparentSlots hwhole' i target hslot' targetNode htargetNode
  exact hrec parentData parentSlots hparentSlots i hslot childNode hchildNode

private def heapChildEdge {K V : Type} (heap : HamtHeap K V)
    (child parent : HAMT K V) : Prop :=
  ∃ (node : HAMTNode K V) (slots : List (Option (Entry K V))) (i : Nat),
    heap.nodes[parent]? = some node ∧
    heap.vectors[node.data]? = some slots ∧
    slots[i]? = some (some (Entry.trie child))

private theorem heapInvariantAcc {K V : Type} (heap : HamtHeap K V)
    {trie : HAMT K V} (hinv : heapInvariant heap trie) :
    Acc (heapChildEdge heap) trie := by
  let motiveNode : (trie : HAMT K V) → heapInvariant heap trie → Prop :=
    fun trie _ => Acc (heapChildEdge heap) trie
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant heap slots → Prop :=
    fun slots _ =>
      ∀ (parent : HAMT K V) (node : HAMTNode K V)
        (wholeSlots pre : List (Option (Entry K V))),
        heap.nodes[parent]? = some node →
        heap.vectors[node.data]? = some wholeSlots →
        wholeSlots = pre ++ slots →
        ∀ (i : Nat) child, slots[i]? = some (some (Entry.trie child)) →
          Acc (heapChildEdge heap) child
  have hrec : motiveNode trie hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro trie node slots hnode hslots hbitmap hcount hentries ihEntries
      apply Acc.intro
      intro child hedge
      rcases hedge with ⟨node', wholeSlots, i, hnode', hslots', hslot⟩
      have hnodeEq : node' = node := Option.some.inj (hnode'.symm.trans hnode)
      have hwhole : heap.vectors[node.data]? = some wholeSlots := by
        simpa [hnodeEq] using hslots'
      have hslotsEq : wholeSlots = slots :=
        Option.some.inj (hwhole.symm.trans hslots)
      have hslot' : slots[i]? = some (some (Entry.trie child)) := by
        simpa [hslotsEq] using hslot
      exact ihEntries trie node slots [] hnode hslots (by simp) i child hslot'
    · intro parent node wholeSlots pre hnode hslots hwhole i child hslot
      cases i <;> simp at hslot
    · intro leaf rest hrest ihRest parent node wholeSlots pre hnode hslots hwhole i child hslot
      cases i with
      | zero => simp at hslot
      | succ i =>
          have hslot' : rest[i]? = some (some (Entry.trie child)) := by simpa using hslot
          have hwhole' : wholeSlots = (pre ++ [some (.leaf leaf)]) ++ rest := by
            simpa [List.append_assoc] using hwhole
          exact ihRest parent node wholeSlots (pre ++ [some (.leaf leaf)])
            hnode hslots hwhole' i child hslot'
    · intro child rest hchild hrest ihChild ihRest parent node wholeSlots pre hnode hslots hwhole i target hslot
      cases i with
      | zero =>
          have hchildEq : child = target := by simpa using hslot
          subst target
          exact ihChild
      | succ i =>
          have hslot' : rest[i]? = some (some (Entry.trie target)) := by simpa using hslot
          have hwhole' : wholeSlots = (pre ++ [some (.trie child)]) ++ rest := by
            simpa [List.append_assoc] using hwhole
          exact ihRest parent node wholeSlots (pre ++ [some (.trie child)])
            hnode hslots hwhole' i target hslot'
  exact hrec

private inductive heapChildPathPlus {K V : Type} (heap : HamtHeap K V) :
    HAMT K V → HAMT K V → Prop where
  | one {parent child} :
      heapChildEdge heap child parent → heapChildPathPlus heap parent child
  | cons {parent child target} :
      heapChildEdge heap child parent → heapChildPathPlus heap child target →
      heapChildPathPlus heap parent target

private theorem heapChildPathPlus_snoc {K V : Type} (heap : HamtHeap K V)
    {first last target : HAMT K V}
    (path : heapChildPathPlus heap first last)
    (edge : heapChildEdge heap target last) :
    heapChildPathPlus heap first target := by
  induction path with
  | one hfirst => exact .cons hfirst (.one edge)
  | cons hfirst rest ih => exact .cons hfirst (ih edge)

private theorem heapChildAcc_noCycle {K V : Type} (heap : HamtHeap K V)
    {trie : HAMT K V} (hacc : Acc (heapChildEdge heap) trie) :
    ¬ heapChildPathPlus heap trie trie := by
  induction hacc with
  | intro trie hnext ih =>
      intro path
      cases path with
      | one hedge => exact ih trie hedge (.one hedge)
      | cons hedge rest =>
          exact ih _ hedge (heapChildPathPlus_snoc heap rest hedge)

private theorem heapChildEdge_reuseVector {K V : Type} (heap : HamtHeap K V)
    {parent child target : HAMT K V}
    (edge : heapChildEdge heap child parent)
    (parentNode targetNode : HAMTNode K V)
    (hparentNode : heap.nodes[parent]? = some parentNode)
    (parentSlots targetSlots : List (Option (Entry K V)))
    (hparentSlots : heap.vectors[parentNode.data]? = some parentSlots)
    (htargetNode : heap.nodes[target]? = some targetNode)
    (htargetSlots : heap.vectors[targetNode.data]? = some targetSlots)
    (hdata : parentNode.data = targetNode.data) :
    heapChildEdge heap child target := by
  rcases edge with ⟨node, slots, i, hnode, hslots, hentry⟩
  have hnodeEq : node = parentNode := Option.some.inj (hnode.symm.trans hparentNode)
  have hslotsParent : heap.vectors[parentNode.data]? = some slots := by
    simpa [hnodeEq] using hslots
  have hslotsEq : slots = parentSlots :=
    Option.some.inj (hslotsParent.symm.trans hparentSlots)
  have htargetSlotsAtParent : heap.vectors[parentNode.data]? = some targetSlots := by
    simpa [hdata.symm] using htargetSlots
  have hparentTargetEq : parentSlots = targetSlots :=
    Option.some.inj (hparentSlots.symm.trans htargetSlotsAtParent)
  have hentry' : targetSlots[i]? = some (some (Entry.trie child)) := by
    simpa [hslotsEq, hparentTargetEq] using hentry
  exact ⟨targetNode, targetSlots, i, htargetNode, htargetSlots, hentry'⟩

private theorem heapDataDiffAlongChildPath {K V : Type} (heap : HamtHeap K V)
    {root target : HAMT K V} (hinv : heapInvariant heap root)
    (path : heapChildPathPlus heap root target)
    (rootNode targetNode : HAMTNode K V)
    (hrootNode : heap.nodes[root]? = some rootNode)
    (rootSlots targetSlots : List (Option (Entry K V)))
    (hrootSlots : heap.vectors[rootNode.data]? = some rootSlots)
    (htargetNode : heap.nodes[target]? = some targetNode)
    (htargetSlots : heap.vectors[targetNode.data]? = some targetSlots) :
    rootNode.data ≠ targetNode.data := by
  intro hdata
  have haccRoot := heapInvariantAcc heap hinv
  cases path with
  | one edge =>
      have hback := heapChildEdge_reuseVector heap edge rootNode targetNode
        hrootNode rootSlots targetSlots hrootSlots htargetNode htargetSlots hdata
      have haccTarget : Acc (heapChildEdge heap) target := by
        exact Acc.inv haccRoot edge
      exact heapChildAcc_noCycle heap haccTarget (.one hback)
  | cons edge rest =>
      rename_i middle
      have hback := heapChildEdge_reuseVector heap edge rootNode targetNode
        hrootNode rootSlots targetSlots hrootSlots htargetNode htargetSlots hdata
      have haccMiddle : Acc (heapChildEdge heap) middle := by
        exact Acc.inv haccRoot edge
      exact heapChildAcc_noCycle heap haccMiddle
        (heapChildPathPlus_snoc heap rest hback)


private inductive HamtLoopTrace {K V β : Type}
    (step : Unit → β → HamtM K V (ForInStep β)) :
    β → HamtHeap K V → β → HamtHeap K V → Prop where
  | done {state heap result heap'}
      (hstep : runHamt (step () state) heap = (.ok (.done result), heap')) :
      HamtLoopTrace step state heap result heap'
  | yield {state heap next heap1 result heap'}
      (hstep : runHamt (step () state) heap = (.ok (.yield next), heap1))
      (rest : HamtLoopTrace step next heap1 result heap') :
      HamtLoopTrace step state heap result heap'

private def pathStepNoCopy {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (top : HAMT K V) :
    Unit → (HAMT K V × HashState K × Option (PathResult K V)) →
      HamtM K V (ForInStep (HAMT K V × HashState K × Option (PathResult K V))) :=
  fun x state => do
    if state.2.2.isNone = true then
      let bi := BitmapIndex.fromHash state.2.1
      let i ← entry_index state.1 bi
      let present ← isset state.1 bi
      if present = true then do
        let node ← readNode state.1
        let entry ← heapVectorOps.get node.data i
        match entry with
        | .leaf leaf =>
            pure (ForInStep.yield
              (state.1, state.2.1,
                some ⟨same leaf.key state.2.1.key, true, state.1, i, bi, top, state.2.1⟩))
        | .trie child =>
            let nextTrie ← pure child
            pure (ForInStep.yield (nextTrie, next ops state.2.1, state.2.2))
      else
        pure (ForInStep.yield
          (state.1, state.2.1,
            some ⟨true, false, state.1, i, bi, top, state.2.1⟩))
    else pure (ForInStep.done (state.1, state.2.1, state.2.2))

private def pathStepCopy {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (top : HAMT K V) :
    Unit → (HAMT K V × HashState K × Option (PathResult K V)) →
      HamtM K V (ForInStep (HAMT K V × HashState K × Option (PathResult K V))) :=
  fun _ state => do
    if state.2.2.isNone = true then
      let i ← entry_index state.1 (BitmapIndex.fromHash state.2.1)
      if ← isset state.1 (BitmapIndex.fromHash state.2.1) then
        let node ← readNode state.1
        match ← heapVectorOps.get node.data i with
        | .leaf leaf =>
            pure (ForInStep.yield
              (state.1, state.2.1,
                some ⟨same leaf.key state.2.1.key, true, state.1, i,
                  BitmapIndex.fromHash state.2.1, top, state.2.1⟩))
        | .trie child =>
            let nextTrie ← do
              let childNode ← readNode child
              let childData ← heapVectorOps.copy childNode.data
              let childCopy ← HAMT.inner childData childNode.bitmap
              let parentData ← nodeData state.1
              let _ ← heapVectorOps.set parentData i (.trie childCopy)
              pure childCopy
            pure (ForInStep.yield (nextTrie, next ops state.2.1, state.2.2))
      else
        pure (ForInStep.yield
          (state.1, state.2.1,
            some ⟨true, false, state.1, i, BitmapIndex.fromHash state.2.1, top, state.2.1⟩))
    else
      pure (ForInStep.done (state.1, state.2.1, state.2.2))

private def pathCopyForInBody {K V : Type}
    (same : K → K → Bool) (ops : HamtObjectIdRuntime K) (top : HAMT K V) :
    Unit → (HAMT K V × HashState K × Option (PathResult K V)) →
      HamtM K V (ForInStep (HAMT K V × HashState K × Option (PathResult K V))) :=
  fun _ __s => do
    if __s.2.2.isNone = true then
      let i ← entry_index __s.1 (BitmapIndex.fromHash __s.2.1)
      if ← isset __s.1 (BitmapIndex.fromHash __s.2.1) then
        let node ← readNode __s.1
        match ← heapVectorOps.get node.data i with
        | .leaf leaf =>
            pure (ForInStep.yield
              (__s.1, __s.2.1,
                some ⟨same leaf.key __s.2.1.key, true, __s.1, i,
                  BitmapIndex.fromHash __s.2.1, top, __s.2.1⟩))
        | .trie child =>
            let nextTrie ← do
              let childNode ← readNode child
              let childData ← heapVectorOps.copy childNode.data
              let childCopy ← HAMT.inner childData childNode.bitmap
              let parentData ← nodeData __s.1
              let _ ← heapVectorOps.set parentData i (.trie childCopy)
              pure childCopy
            pure (ForInStep.yield (nextTrie, next ops __s.2.1, __s.2.2))
      else
        pure (ForInStep.yield
          (__s.1, __s.2.1,
            some ⟨true, false, __s.1, i, BitmapIndex.fromHash __s.2.1, top,
              __s.2.1⟩))
    else
      pure (ForInStep.done (__s.1, __s.2.1, __s.2.2))

private theorem pathCopyForInBody_eq_pathStepCopy {K V : Type}
    (same : K → K → Bool) (ops : HamtObjectIdRuntime K) (top : HAMT K V) :
    pathCopyForInBody same ops top = pathStepCopy same ops top := by
  funext x __s
  cases __s with
  | mk current rest =>
      cases rest with
      | mk hash result =>
          simp only [pathCopyForInBody, pathStepCopy]

private theorem heapEntriesInvariant_get {K V : Type} {heap : HamtHeap K V} :
    ∀ {slots : List (Option (Entry K V))},
      heapEntriesInvariant heap slots →
      ∀ i, i < slots.length → ∃ entry, slots[i]? = some (some entry) := by
  intro slots
  induction slots with
  | nil =>
      intro _ i hi
      cases hi
  | cons slot rest ih =>
      intro hinv i hi
      cases hinv with
      | leaf hrest =>
          rename_i leaf
          cases i with
          | zero => exact ⟨.leaf leaf, rfl⟩
          | succ i =>
              have hi' : i < rest.length := by simpa using hi
              obtain ⟨entry, hentry⟩ := ih hrest i hi'
              exact ⟨entry, by simpa using hentry⟩
      | trie hchild hrest =>
          rename_i child
          cases i with
          | zero => exact ⟨.trie child, rfl⟩
          | succ i =>
              have hi' : i < rest.length := by simpa using hi
              obtain ⟨entry, hentry⟩ := ih hrest i hi'
              exact ⟨entry, by simpa using hentry⟩


private def pathStepIndex {K V : Type} (node : HAMTNode K V) (hash : HashState K) : Nat :=
  countOnes 32 (node.bitmap &&& (shiftLeftNat 1 (BitmapIndex.fromHash hash).x - 1)) + 1

private def pathCopyChildHeap {K V : Type} (heap : HamtHeap K V)
    (node : HAMTNode K V) (index : Nat) (slots : List (Option (Entry K V)))
    (childNode : HAMTNode K V) (childSlots : List (Option (Entry K V))) :
    HamtHeap K V :=
  { heap with
    vectors := (heap.vectors ++ [childSlots]).set node.data
      (slots.set (index - 1) (some (.trie heap.nodes.length))),
    nodes := heap.nodes ++ [⟨heap.vectors.length, childNode.bitmap⟩] }

private def pathStepCopyShape {K V : Type} (heap : HamtHeap K V)
    (same : K → K → Bool) (ops : HamtObjectIdRuntime K) (top current : HAMT K V)
    (hash : HashState K) (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (nextState : HAMT K V × HashState K × Option (PathResult K V))
    (heapAfter : HamtHeap K V) : Prop :=
  (∃ result, nextState = (current, hash, some result) ∧ heapAfter = heap ∧
    result.trie = current ∧
      ((∃ leaf, result =
          ⟨same leaf.key hash.key, true, current, pathStepIndex node hash,
            BitmapIndex.fromHash hash, top, hash⟩ ∧
          slots[pathStepIndex node hash - 1]? = some (some (.leaf leaf)) ∧
          Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true) ∨
        (result =
          ⟨true, false, current, pathStepIndex node hash,
            BitmapIndex.fromHash hash, top, hash⟩ ∧
          Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = false))) ∨
  (∃ child childNode childSlots,
    nextState = (heap.nodes.length, next ops hash, none) ∧
    slots[pathStepIndex node hash - 1]? = some (some (.trie child)) ∧
    Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true ∧
    heap.nodes[child]? = some childNode ∧
    heap.vectors[childNode.data]? = some childSlots ∧
    heapAfter = pathCopyChildHeap heap node (pathStepIndex node hash)
      slots childNode childSlots)

private def pathStepNoCopyShape {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (top current : HAMT K V) (hash : HashState K)
    (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (nextState : HAMT K V × HashState K × Option (PathResult K V)) : Prop :=
  (∃ result, nextState = (current, hash, some result) ∧ result.trie = current ∧
    ((∃ leaf, result =
        ⟨same leaf.key hash.key, true, current, pathStepIndex node hash,
          BitmapIndex.fromHash hash, top, hash⟩ ∧
        slots[pathStepIndex node hash - 1]? = some (some (.leaf leaf)) ∧
        Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true) ∨
      (result =
        ⟨true, false, current, pathStepIndex node hash,
          BitmapIndex.fromHash hash, top, hash⟩ ∧
        Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = false)))
  ∨
  (∃ child, nextState = (child, next ops hash, none) ∧
    slots[pathStepIndex node hash - 1]? = some (some (.trie child)) ∧
    Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true)

private theorem pathStepNoCopy_yields {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current : HAMT K V)
    (hash : HashState K) (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hnode : heap.nodes[current]? = some node)
    (hslots : heap.vectors[node.data]? = some slots)
    (hbitmap : node.bitmap < 2 ^ 32)
    (hcount : countOnes 32 node.bitmap = slots.length)
    (hentries : heapEntriesInvariant heap slots) :
    ∃ nextState,
      runHamt (pathStepNoCopy same ops top () (current, hash, none)) heap =
        (.ok (.yield nextState), heap) ∧
      pathStepNoCopyShape same ops top current hash node slots nextState := by
  let bi := BitmapIndex.fromHash hash
  let index := countOnes 32 (node.bitmap &&& (shiftLeftNat 1 bi.x - 1)) + 1
  have hinv' : heapInvariant heap current :=
    .node hnode hslots hbitmap hcount hentries
  have hindex :
      runHamt (entry_index current bi) heap = (.ok index, heap) := by
    simp [runHamt, entry_index, nodeBitmap, readNode, hnode,
      shiftLeftNat, MonadState.get, MonadStateOf.get, getThe, liftM,
      monadLift, MonadLift.monadLift, StateT.map, Functor.map,
      ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
      ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind,
      StateT.pure, StateT.get, Bind.bind, Pure.pure, index, bi]
  have hset :
      runHamt (isset current bi) heap =
        (.ok (Nat.testBit node.bitmap bi.x), heap) := by
    simp [runHamt, isset, nodeBitmap, readNode, hnode, shiftRightNat,
      Nat.testBit_eq_decide_div_mod_eq, natBeqEq, MonadState.get,
      MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
      StateT.map, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure,
      ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run,
      StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure]
  have hindexStep :
      runHamt (entry_index current (BitmapIndex.fromHash hash)) heap =
        (.ok index, heap) := by
    simpa [bi] using hindex
  have hsetStep :
      runHamt (isset current (BitmapIndex.fromHash hash)) heap =
        (.ok (Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x), heap) := by
    simpa [bi] using hset
  by_cases hbit : Nat.testBit node.bitmap bi.x
  · have hbit' : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true := by
      simpa [bi] using hbit
    have hindexFirst : (runHamt (entry_index current bi) heap).1 = .ok index := by
      simp [hindex]
    have hrank := HamtSlotRank_proven K V heap current bi node.data
      node.bitmap slots index hnode hslots hinv'
    have hbounds := hrank.2.1 hbit hindexFirst
    rcases hbounds with ⟨_, hlo, hhi⟩
    have hslotIndex : index - 1 < slots.length := by omega
    obtain ⟨entry, hslot⟩ :=
      heapEntriesInvariant_get hentries (index - 1) hslotIndex
    have hread : runHamt (readNode current) heap = (.ok node, heap) := by
      simp [runHamt, readNode, hnode, MonadState.get, MonadStateOf.get,
        getThe, liftM, monadLift, MonadLift.monadLift, StateT.map,
        Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure,
        ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run,
        StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure]
    have hget :
        runHamt (heapVectorGet node.data index) heap = (.ok entry, heap) := by
      simp [runHamt, heapVectorGet, heapVectorSlots, hslots, hslot,
        MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
        MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run,
        ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
        ExceptT.lift, StateT.run, StateT.bind, StateT.pure,
        StateT.get, Bind.bind, Pure.pure]
    cases entry with
    | leaf leaf =>
        refine ⟨(current, hash, some ⟨same leaf.key hash.key, true,
          current, index, bi, top, hash⟩), ?_,
          Or.inl ⟨⟨same leaf.key hash.key, true, current, index, bi, top, hash⟩,
            rfl, rfl, Or.inl ⟨leaf, rfl, hslot, hbit'⟩⟩⟩
        dsimp [pathStepNoCopy]
        rw [runHamtBindEq, hindexStep]
        simp only
        rw [runHamtBindEq, hsetStep]
        simp only [hbit', ite_true]
        rw [runHamtBindEq, hread]
        simp only
        dsimp [heapVectorOps]
        rw [runHamtBindEq, hget]
        simp [runHamt, ExceptT.pure, StateT.pure, StateT.run, Pure.pure, bi]
    | trie child =>
        refine ⟨(child, next ops hash, none), ?_,
          Or.inr ⟨child, rfl, hslot, hbit'⟩⟩
        dsimp [pathStepNoCopy]
        rw [runHamtBindEq, hindexStep]
        simp only
        rw [runHamtBindEq, hsetStep]
        simp only [hbit', ite_true]
        rw [runHamtBindEq, hread]
        simp only
        dsimp [heapVectorOps]
        rw [runHamtBindEq, hget]
        simp [runHamt, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
          StateT.run, StateT.bind, StateT.pure, ExceptT.bindCont,
          Bind.bind, Pure.pure]
  · have hbitFalse : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = false := by
      cases hval : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x with
      | false => rfl
      | true =>
          apply False.elim
          apply hbit
          simpa [bi] using hval
    refine ⟨(current, hash, some ⟨true, false, current, index, bi, top, hash⟩), ?_,
      Or.inl ⟨⟨true, false, current, index, bi, top, hash⟩,
        rfl, rfl, Or.inr ⟨rfl, hbitFalse⟩⟩⟩
    dsimp [pathStepNoCopy]
    rw [runHamtBindEq, hindexStep]
    simp only
    rw [runHamtBindEq, hsetStep]
    simp only [hbitFalse, ite_false]
    simp [bi, runHamt, ExceptT.pure, StateT.pure, StateT.run, Pure.pure]

private theorem pathStepNoCopy_done {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (top current : HAMT K V) (hash : HashState K)
    (result : PathResult K V) (heap : HamtHeap K V) :
    runHamt (pathStepNoCopy same ops top () (current, hash, some result)) heap =
      (.ok (.done (current, hash, some result)), heap) := by
  simp [pathStepNoCopy, runHamt, ExceptT.run, ExceptT.pure, ExceptT.mk,
    StateT.run, StateT.pure, Bind.bind, Pure.pure]
private inductive heapChildPath {K V : Type} (heap : HamtHeap K V) :
    HAMT K V → HAMT K V → Prop where
  | refl {trie} : heapChildPath heap trie trie
  | step {parent child target} :
      heapChildEdge heap child parent → heapChildPath heap child target →
      heapChildPath heap parent target

private theorem heapChildPath_snoc {K V : Type} (heap : HamtHeap K V)
    {first last target : HAMT K V}
    (path : heapChildPath heap first last)
    (edge : heapChildEdge heap target last) :
    heapChildPathPlus heap first target := by
  induction path with
  | refl => exact .one edge
  | step hfirst rest ih => exact .cons hfirst (ih edge)
private def heapChildPathPlus_of_edge {K V : Type} (heap : HamtHeap K V) :
    ∀ {parent child target : HAMT K V},
      heapChildEdge heap child parent → heapChildPath heap child target →
        heapChildPathPlus heap parent target
  | _, _, _, edge, .refl => .one edge
  | _, _, _, edge, .step edge' rest =>
      .cons edge (heapChildPathPlus_of_edge heap edge' rest)

private theorem heapChildPath_self_eq_refl {K V : Type} (heap : HamtHeap K V)
    {trie : HAMT K V} (hinv : heapInvariant heap trie)
    (path : heapChildPath heap trie trie) : path = .refl := by
  cases path with
  | refl => rfl
  | @step parent child target edge rest =>
      have hacc := heapInvariantAcc heap hinv
      have haccChild : Acc (heapChildEdge heap) child := Acc.inv hacc edge
      exact False.elim
        (heapChildAcc_noCycle heap haccChild (heapChildPath_snoc heap rest edge))

private theorem heapDataEqualAlongPath_imp_sameIndex {K V : Type}
    (heap : HamtHeap K V) {root target : HAMT K V}
    (hinv : heapInvariant heap root) (path : heapChildPath heap root target)
    (rootNode targetNode : HAMTNode K V)
    (hrootNode : heap.nodes[root]? = some rootNode)
    (rootSlots targetSlots : List (Option (Entry K V)))
    (hrootSlots : heap.vectors[rootNode.data]? = some rootSlots)
    (htargetNode : heap.nodes[target]? = some targetNode)
    (htargetSlots : heap.vectors[targetNode.data]? = some targetSlots)
    (hdata : rootNode.data = targetNode.data) :
    root = target := by
  cases path with
  | refl => rfl
  | step edge rest =>
      have hback := heapChildEdge_reuseVector heap edge rootNode targetNode
        hrootNode rootSlots targetSlots hrootSlots htargetNode htargetSlots hdata
      have haccRoot := heapInvariantAcc heap hinv
      have haccChild : Acc (heapChildEdge heap) _ := Acc.inv haccRoot edge
      exact False.elim
        (heapChildAcc_noCycle heap haccChild (heapChildPath_snoc heap rest hback))

private theorem pathLoopTraceWithChildPath {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top : HAMT K V) :
    ∀ {trie : HAMT K V}, heapInvariant heap trie → ∀ hash,
      ∃ finalTrie finalHash result,
        HamtLoopTrace (pathStepNoCopy same ops top) (trie, hash, none) heap
          (finalTrie, finalHash, some result) heap ∧
        heapChildPath heap trie result.trie ∧
        (result.present = true →
          ∃ node slots leaf,
            heap.nodes[result.trie]? = some node ∧
            heap.vectors[node.data]? = some slots ∧
            result.hash = finalHash ∧ result.bi = BitmapIndex.fromHash finalHash ∧
            result.index = pathStepIndex node finalHash ∧
            slots[result.index - 1]? = some (some (.leaf leaf)) ∧
            Nat.testBit node.bitmap result.bi.x = true) := by
  let motiveNode : (trie : HAMT K V) → heapInvariant heap trie → Prop :=
    fun trie _ => ∀ hash, ∃ finalTrie finalHash result,
      HamtLoopTrace (pathStepNoCopy same ops top) (trie, hash, none) heap
        (finalTrie, finalHash, some result) heap ∧
      heapChildPath heap trie result.trie ∧
      (result.present = true →
        ∃ node slots leaf,
          heap.nodes[result.trie]? = some node ∧
          heap.vectors[node.data]? = some slots ∧
          result.hash = finalHash ∧ result.bi = BitmapIndex.fromHash finalHash ∧
          result.index = pathStepIndex node finalHash ∧
          slots[result.index - 1]? = some (some (.leaf leaf)) ∧
          Nat.testBit node.bitmap result.bi.x = true)
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant heap slots → Prop :=
    fun slots _ => ∀ (i : Nat) (child : HAMT K V),
      slots[i]? = some (some (Entry.trie child)) →
      ∀ hash, ∃ finalTrie finalHash result,
        HamtLoopTrace (pathStepNoCopy same ops top) (child, hash, none) heap
          (finalTrie, finalHash, some result) heap ∧
        heapChildPath heap child result.trie ∧
        (result.present = true →
          ∃ node childSlots leaf,
            heap.nodes[result.trie]? = some node ∧
            heap.vectors[node.data]? = some childSlots ∧
            result.hash = finalHash ∧ result.bi = BitmapIndex.fromHash finalHash ∧
            result.index = pathStepIndex node finalHash ∧
            childSlots[result.index - 1]? = some (some (.leaf leaf)) ∧
            Nat.testBit node.bitmap result.bi.x = true)
  intro trie hinv hash
  have hrec : motiveNode trie hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro trie node slots hnode hslots hbitmap hcount hentries ihEntries hash
      obtain ⟨nextState, hstep, hcase⟩ :=
        pathStepNoCopy_yields same ops heap top trie hash node slots
          hnode hslots hbitmap hcount hentries
      rcases hcase with ⟨result, hresult, hresultTrie, hdetail⟩ |
        ⟨child, hchildState, hslot, _⟩
      · rcases nextState with ⟨nextTrie, nextHash, nextResult⟩
        have hstate : (nextTrie, nextHash, nextResult) = (trie, hash, some result) :=
          hresult
        have hnextTrie : nextTrie = trie := congrArg Prod.fst hstate
        have hnextRest : (nextHash, nextResult) = (hash, some result) :=
          congrArg Prod.snd hstate
        have hnextHash : nextHash = hash := congrArg Prod.fst hnextRest
        have hnextResult : nextResult = some result := congrArg Prod.snd hnextRest
        subst nextTrie
        subst nextHash
        subst nextResult
        have hterminal : result.present = true →
            ∃ terminalNode terminalSlots leaf,
              heap.nodes[result.trie]? = some terminalNode ∧
              heap.vectors[terminalNode.data]? = some terminalSlots ∧
              result.hash = hash ∧ result.bi = BitmapIndex.fromHash hash ∧
              result.index = pathStepIndex terminalNode hash ∧
              terminalSlots[result.index - 1]? = some (some (.leaf leaf)) ∧
              Nat.testBit terminalNode.bitmap result.bi.x = true := by
          intro hpresent
          rcases hdetail with ⟨leaf, hresultEq, hslot, hbit⟩ | hempty
          · subst result
            exact ⟨node, slots, leaf, hnode, hslots, rfl, rfl, rfl, hslot, hbit⟩
          · rcases hempty with ⟨hempty, _⟩
            simp [hempty] at hpresent
        have hroute : heapChildPath heap trie result.trie := by
          rw [hresultTrie]
          exact .refl
        exact ⟨trie, hash, result,
          HamtLoopTrace.yield hstep (HamtLoopTrace.done
            (pathStepNoCopy_done same ops top trie hash result heap)), hroute,
          hterminal⟩
      · rcases nextState with ⟨nextTrie, nextHash, nextResult⟩
        have hstate : (nextTrie, nextHash, nextResult) = (child, next ops hash, none) :=
          hchildState
        have hnextTrie : nextTrie = child := congrArg Prod.fst hstate
        have hnextRest : (nextHash, nextResult) = (next ops hash, none) :=
          congrArg Prod.snd hstate
        have hnextHash : nextHash = next ops hash := congrArg Prod.fst hnextRest
        have hnextResult : nextResult = none := congrArg Prod.snd hnextRest
        subst nextTrie
        subst nextHash
        subst nextResult
        let i := pathStepIndex node hash - 1
        have hslot' : slots[i]? = some (some (Entry.trie child)) := by
          simpa [i] using hslot
        obtain ⟨finalTrie, finalHash, result, restTrace, restPath, restTerminal⟩ :=
          ihEntries i child hslot' (next ops hash)
        have edge : heapChildEdge heap child trie :=
          ⟨node, slots, i, hnode, hslots, hslot'⟩
        exact ⟨finalTrie, finalHash, result,
          HamtLoopTrace.yield hstep restTrace, .step edge restPath, restTerminal⟩
    · intro i child hslot hash
      cases i <;> simp at hslot
    · intro leaf rest hrest ihRest i child hslot hash
      cases i with
      | zero => simp at hslot
      | succ i =>
          exact ihRest i child (by simpa using hslot) hash
    · intro child rest hchild hrest ihChild ihRest i target hslot hash
      cases i with
      | zero =>
          have heq : child = target := by simpa using hslot
          subst target
          exact ihChild hash
      | succ i =>
          exact ihRest i target (by simpa using hslot) hash
  exact hrec hash

private theorem classForInRunEquation {K V β : Type} (state : β)
    (step : Unit → β → HamtM K V (ForInStep β)) (heap : HamtHeap K V) :
    runHamt (forIn (m := HamtM K V) (β := β) ({} : Lean.Loop) state step) heap =
      match runHamt (step () state) heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok (.done result), heap') => (.ok result, heap')
      | (.ok (.yield next), heap') =>
          runHamt (forIn (m := HamtM K V) (β := β) ({} : Lean.Loop) next step) heap' := by
  cases h : runHamt (step () state) heap with
  | mk out heap' =>
      have hrunAction : StateT.run (ExceptT.run (step () state)) heap = (out, heap') := by
        simpa [runHamt] using h
      unfold Lean.instForInLoopUnitOfMonad
      change runHamt (Lean.Loop.forIn (m := HamtM K V) (β := β)
        ({} : Lean.Loop) state step) heap = _
      rw [Lean.Loop.forIn_eq_of_monadTail]
      unfold runHamt
      rw [ExceptT.run_bind]
      rw [StateT.run_bind]
      rw [hrunAction]
      cases out with
      | error error => rfl
      | ok stepResult => cases stepResult <;> rfl

private theorem classForInRunOfTrace {K V β : Type} (state : β)
    (heap : HamtHeap K V) (step : Unit → β → HamtM K V (ForInStep β))
    (result : β) (heap' : HamtHeap K V)
    (trace : HamtLoopTrace step state heap result heap') :
    runHamt (forIn (m := HamtM K V) (β := β) ({} : Lean.Loop) state step) heap =
      (.ok result, heap') := by
  induction trace with
  | done hstep =>
      rw [classForInRunEquation, hstep]
  | yield hstep rest ih =>
      rw [classForInRunEquation, hstep]
      exact ih

private theorem pathNoCopy_runOfTrace {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (trie : HAMT K V) (hash : HashState K)
    (heap : HamtHeap K V) (finalTrie : HAMT K V) (finalHash : HashState K)
    (result : PathResult K V)
    (trace : HamtLoopTrace (pathStepNoCopy same ops trie)
      (trie, hash, none) heap (finalTrie, finalHash, some result) heap) :
    runHamt (path heapVectorOps same ops trie hash false) heap =
      (.ok result, heap) := by
  rw [path.eq_1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hloop := classForInRunOfTrace (trie, hash, none) heap
    (pathStepNoCopy same ops trie) (finalTrie, finalHash, some result) heap trace
  change runHamt
    ((forIn (m := HamtM K V) (β := HAMT K V × HashState K × Option (PathResult K V))
      ({} : Lean.Loop) (trie, hash, none) (pathStepNoCopy same ops trie)) >>= fun state =>
      match state.2.2 with
      | some value => pure value
      | none => throw HamtError.bounds) heap = _
  rw [runHamtBindEq]
  simp only [hloop]
  simp [runHamt, ExceptT.pure, StateT.pure, StateT.run, Pure.pure]

private theorem pathNoCopy_childPath {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap : HamtHeap K V) (root : HAMT K V)
    (hash : HashState K) (hinv : heapInvariant heap root)
    (result : PathResult K V)
    (hpath : runHamt (path heapVectorOps same ops root hash false) heap =
      (.ok result, heap)) :
    heapChildPath heap root result.trie := by
  let hExists := pathLoopTraceWithChildPath same ops heap root hinv hash
  let finalTrie := Classical.choose hExists
  have hFinalTrie := Classical.choose_spec hExists
  let finalHash := Classical.choose hFinalTrie
  have hResult := Classical.choose_spec hFinalTrie
  let result' := Classical.choose hResult
  have hTraceAndRoute := Classical.choose_spec hResult
  have hrunTrace := pathNoCopy_runOfTrace same ops root hash heap
    finalTrie finalHash result' hTraceAndRoute.1
  have hresult : result' = result := by
    have hEq : (Except.ok result', heap) = (Except.ok result, heap) :=
      hrunTrace.symm.trans hpath
    have hEq' : Except.ok result' = Except.ok result := congrArg Prod.fst hEq
    injection hEq' with hresult
  exact (congrArg PathResult.trie hresult) ▸ hTraceAndRoute.2.1

private theorem pathNoCopy_terminalLeaf {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap : HamtHeap K V) (root : HAMT K V)
    (hash : HashState K) (hinv : heapInvariant heap root)
    (result : PathResult K V)
    (hpath : runHamt (path heapVectorOps same ops root hash false) heap =
      (.ok result, heap))
    (hpresent : result.present = true) :
    ∃ node slots leaf,
      heap.nodes[result.trie]? = some node ∧
      heap.vectors[node.data]? = some slots ∧
      result.bi = BitmapIndex.fromHash result.hash ∧
      result.index = pathStepIndex node result.hash ∧
      slots[result.index - 1]? = some (some (.leaf leaf)) ∧
      Nat.testBit node.bitmap result.bi.x = true := by
  let hExists := pathLoopTraceWithChildPath same ops heap root hinv hash
  let finalTrie := Classical.choose hExists
  have hFinalTrie := Classical.choose_spec hExists
  let finalHash := Classical.choose hFinalTrie
  have hResult := Classical.choose_spec hFinalTrie
  let result' := Classical.choose hResult
  have hTraceAndRoute := Classical.choose_spec hResult
  have hrunTrace := pathNoCopy_runOfTrace same ops root hash heap
    finalTrie finalHash result' hTraceAndRoute.1
  have hresult : result' = result := by
    have hEq : (Except.ok result', heap) = (Except.ok result, heap) :=
      hrunTrace.symm.trans hpath
    have hEq' : Except.ok result' = Except.ok result := congrArg Prod.fst hEq
    injection hEq' with hresult
  have hpresent' : result'.present = true := by simpa [hresult] using hpresent
  obtain ⟨node, slots, leaf, hnode, hslots, hhash, hbi, hindex, hslot, hbit⟩ :=
    hTraceAndRoute.2.2 hpresent'
  have hresultTrie : result'.trie = result.trie := congrArg PathResult.trie hresult
  have hresultHash : result'.hash = result.hash := congrArg PathResult.hash hresult
  have hresultBi : result'.bi = result.bi := congrArg PathResult.bi hresult
  have hresultIndex : result'.index = result.index := congrArg PathResult.index hresult
  have hfinalHash : finalHash = result.hash := hhash.symm.trans hresultHash
  have hbi' : result.bi = BitmapIndex.fromHash result.hash := by
    calc
      result.bi = result'.bi := hresultBi.symm
      _ = BitmapIndex.fromHash finalHash := hbi
      _ = BitmapIndex.fromHash result.hash := by rw [hfinalHash]
  have hindex' : result.index = pathStepIndex node result.hash := by
    calc
      result.index = result'.index := hresultIndex.symm
      _ = pathStepIndex node finalHash := hindex
      _ = pathStepIndex node result.hash := by rw [hfinalHash]
  refine ⟨node, slots, leaf, ?_, hslots, hbi', hindex', ?_, ?_⟩
  · rw [← hresultTrie]
    exact hnode
  · rw [← hresultIndex]
    exact hslot
  · rw [← hresultBi]
    exact hbit

private theorem vectorLookupAfterSetOther {K V : Type}
    (heap : HamtHeap K V) (written read : Nat)
    (slots : List (Option (Entry K V))) (hne : read ≠ written) :
    (heap.vectors.set written slots)[read]? = heap.vectors[read]? := by
  simp [List.getElem?_set, Ne.symm hne]

private theorem heapVectorGet_frame {K V : Type} (heap : HamtHeap K V)
    (written read index : Nat) (slots : List (Option (Entry K V)))
    (hne : read ≠ written) :
    (runHamt (heapVectorGet read index)
      { heap with vectors := heap.vectors.set written slots }).1 =
      (runHamt (heapVectorGet read index) heap).1 := by
  have hreadNew :
      ({ heap with vectors := heap.vectors.set written slots }).vectors[read]? =
        heap.vectors[read]? := by
    exact vectorLookupAfterSetOther heap written read slots hne
  cases hread : heap.vectors[read]? with
  | none =>
      simp [runHamt, heapVectorGet, heapVectorSlots, hread, hreadNew,
        MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
        MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run,
        ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
        ExceptT.lift, StateT.run, StateT.bind, StateT.pure,
        StateT.get, Bind.bind, Pure.pure, throw, throwThe,
        MonadExceptOf.throw]
  | some val =>
      by_cases hzero : index = 0
      · simp [runHamt, heapVectorGet, heapVectorSlots, hread, hreadNew,
          hzero, MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
          MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run,
          ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
          ExceptT.lift, StateT.run, StateT.bind, StateT.pure,
          StateT.get, Bind.bind, Pure.pure, throw, throwThe,
          MonadExceptOf.throw]
      · cases hslot : val[index - 1]? with
        | none =>
            simp [runHamt, heapVectorGet, heapVectorSlots, hread, hreadNew,
              hzero, hslot, MonadState.get, MonadStateOf.get, getThe, liftM,
              monadLift, MonadLift.monadLift, StateT.map, Functor.map,
              ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
              ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind,
              StateT.pure, StateT.get, Bind.bind, Pure.pure, throw,
              throwThe, MonadExceptOf.throw]
        | some slot =>
            cases slot with
            | none =>
                simp [runHamt, heapVectorGet, heapVectorSlots, hread, hreadNew,
                  hzero, hslot, MonadState.get, MonadStateOf.get, getThe, liftM,
                  monadLift, MonadLift.monadLift, StateT.map, Functor.map,
                  ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
                  ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind,
                  StateT.pure, StateT.get, Bind.bind, Pure.pure, throw,
                  throwThe, MonadExceptOf.throw]
            | some entry =>
                simp [runHamt, heapVectorGet, heapVectorSlots, hread, hreadNew,
                  hzero, hslot, MonadState.get, MonadStateOf.get, getThe, liftM,
                  monadLift, MonadLift.monadLift, StateT.map, Functor.map,
                  ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
                  ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind,
                  StateT.pure, StateT.get, Bind.bind, Pure.pure, throw,
                  throwThe, MonadExceptOf.throw]
private theorem heapEntriesInvariant_child {K V : Type} {heap : HamtHeap K V} :
    ∀ {slots : List (Option (Entry K V))},
      heapEntriesInvariant heap slots →
      ∀ (i : Nat) (child : HAMT K V),
        slots[i]? = some (some (Entry.trie child)) → heapInvariant heap child := by
  intro slots
  induction slots with
  | nil =>
      intro hinv i child hslot
      cases i <;> simp at hslot
  | cons slot rest ih =>
      intro hinv i child hslot
      cases hinv with
      | leaf hrest =>
          cases i with
          | zero => simp at hslot
          | succ i =>
              exact ih hrest i child (by simpa using hslot)
      | trie hchild hrest =>
          rename_i child'
          cases i with
          | zero =>
              have heq : child' = child := by simpa using hslot
              subst child'
              exact hchild
          | succ i =>
              exact ih hrest i child (by simpa using hslot)

private theorem heapChildEdge_childInvariant {K V : Type} (heap : HamtHeap K V)
    {parent child : HAMT K V} (hinv : heapInvariant heap parent)
    (edge : heapChildEdge heap child parent) : heapInvariant heap child := by
  cases hinv with
  | node hnode hslots hbitmap hcount hentries =>
      rename_i node slots
      rcases edge with ⟨node', slots', i, hnode', hslots', hslot⟩
      have hnodeEq : node' = node := Option.some.inj (hnode'.symm.trans hnode)
      have hslotsAtNode : heap.vectors[node.data]? = some slots' := by
        simpa [hnodeEq] using hslots'
      have hslotsEq : slots' = slots := Option.some.inj (hslotsAtNode.symm.trans hslots)
      subst slots'
      exact heapEntriesInvariant_child hentries i child (by simpa using hslot)

private theorem heapInvariantAlongChildPath {K V : Type} (heap : HamtHeap K V)
    {root target : HAMT K V} (hinv : heapInvariant heap root)
    (path : heapChildPath heap root target) : heapInvariant heap target := by
  induction path with
  | refl => exact hinv
  | step edge rest ih =>
      exact ih (heapChildEdge_childInvariant heap hinv edge)
private def replaceEntryAt {K V : Type} (slots : List (Option (Entry K V)))
    (i : Nat) (entry : Option (Entry K V)) : List (Option (Entry K V)) :=
  slots.set i entry

private theorem replaceEntryAt_length {K V : Type}
    (slots : List (Option (Entry K V))) (i : Nat) (entry : Option (Entry K V)) :
    (replaceEntryAt slots i entry).length = slots.length := by
  simp [replaceEntryAt]

private theorem heapInvariant_replaceLeaf {K V : Type} (heap : HamtHeap K V)
    (targetData index : Nat) (targetSlots : List (Option (Entry K V)))
    (oldLeaf newLeaf : Leaf K V)
    (htargetSlots : heap.vectors[targetData]? = some targetSlots)
    (htargetEntry : targetSlots[index]? = some (some (.leaf oldLeaf)))
    {trie : HAMT K V} (hinv : heapInvariant heap trie) :
    heapInvariant ({ heap with vectors := (heap.vectors.set targetData
        (replaceEntryAt targetSlots index (some (.leaf newLeaf)))) }) trie := by
  let updatedHeap : HamtHeap K V :=
    { heap with vectors := (heap.vectors.set targetData
        (replaceEntryAt targetSlots index (some (.leaf newLeaf)))) }
  let motiveNode : (trie : HAMT K V) → heapInvariant heap trie → Prop :=
    fun trie _ => heapInvariant updatedHeap trie
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant heap slots → Prop :=
    fun slots _ =>
      ∀ (i : Nat) (replace : Bool),
        (replace = true → slots[i]? = some (some (.leaf oldLeaf))) →
        heapEntriesInvariant updatedHeap
          (if replace then replaceEntryAt slots i (some (.leaf newLeaf)) else slots)
  have hrec : motiveNode trie hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro current node slots hnode hslots hbitmap hcount hentries ihEntries
      have hnode' : updatedHeap.nodes[current]? = some node := by
        simpa [updatedHeap] using hnode
      by_cases hdata : node.data = targetData
      · have hslotsAtTarget : heap.vectors[targetData]? = some slots := by
          simpa [hdata] using hslots
        have hslotsEq : slots = targetSlots :=
          Option.some.inj (hslotsAtTarget.symm.trans htargetSlots)
        have htargetDataLt : targetData < heap.vectors.length :=
          (List.getElem?_eq_some_iff.mp htargetSlots).1
        have hleaf : slots[index]? = some (some (.leaf oldLeaf)) := by
          simpa [hslotsEq] using htargetEntry
        have hslots' :
            updatedHeap.vectors[node.data]? =
              some (replaceEntryAt slots index (some (.leaf newLeaf))) := by
          simp only [updatedHeap, hdata]
          rw [List.getElem?_set_self htargetDataLt]
          simpa [hslotsEq]
        have hcount' :
            countOnes 32 node.bitmap =
              (replaceEntryAt slots index (some (.leaf newLeaf))).length := by
          rw [replaceEntryAt_length]
          exact hcount
        have hentries' := ihEntries index true (by intro _; exact hleaf)
        exact .node hnode' hslots' hbitmap hcount' (by simpa using hentries')
      · have hslots' : updatedHeap.vectors[node.data]? = some slots := by
          have hread := vectorLookupAfterSetOther heap targetData node.data
            (replaceEntryAt targetSlots index (some (.leaf newLeaf))) hdata
          simpa [updatedHeap] using hread.trans hslots
        have hentries' := ihEntries index false (by intro h; cases h)
        exact .node hnode' hslots' hbitmap hcount (by simpa using hentries')
    · intro i replace hslot
      cases replace with
      | false => exact .nil
      | true => simp at hslot
    · intro leaf rest hrest ihRest i replace hslot
      cases replace with
      | false =>
          simpa [replaceEntryAt] using
            (heapEntriesInvariant.leaf (ihRest i false (by intro h; cases h)))
      | true =>
          cases i with
          | zero =>
              exact .leaf (ihRest 0 false (by intro h; cases h))
          | succ i =>
              have hslot' : rest[i]? = some (some (.leaf oldLeaf)) := by
                simpa using hslot rfl
              exact .leaf (ihRest i true (by intro _; exact hslot'))
    · intro child rest hchild hrest ihChild ihRest i replace hslot
      cases replace with
      | false =>
          simpa [replaceEntryAt] using
            (heapEntriesInvariant.trie ihChild (ihRest i false (by intro h; cases h)))
      | true =>
          cases i with
          | zero => simp at hslot
          | succ i =>
              have hslot' : rest[i]? = some (some (.leaf oldLeaf)) := by
                simpa using hslot rfl
              exact .trie ihChild (ihRest i true (by intro _; exact hslot'))
  exact hrec

private theorem setRun_existingBit {K V : Type} (heap : HamtHeap K V)
    (trie : HAMT K V) (bi : BitmapIndex) (node : HAMTNode K V)
    (hnode : heap.nodes[trie]? = some node) (hbound : node.bitmap < 2 ^ 32)
    (hbit : Nat.testBit node.bitmap bi.x = true) :
    runHamt (set! trie bi) heap = (.ok node.bitmap, heap) := by
  have hor : Nat.lor node.bitmap (2 ^ bi.x) = node.bitmap := by
    apply Nat.eq_of_testBit_eq
    intro bit
    change Nat.testBit (node.bitmap ||| 2 ^ bi.x) bit =
      Nat.testBit node.bitmap bit
    rw [Nat.testBit_or]
    by_cases heq : bit = bi.x
    · subst bit
      simp [Nat.testBit_two_pow, hbit]
    · have hne : bi.x ≠ bit := fun h => heq h.symm
      simp [Nat.testBit_two_pow, hne]
  have hu32 : u32 (Nat.lor node.bitmap (2 ^ bi.x)) = node.bitmap := by
    change (Nat.lor node.bitmap (2 ^ bi.x)) % 2 ^ 32 = node.bitmap
    rw [hor]
    exact Nat.mod_eq_of_lt hbound
  obtain ⟨hindex, hget⟩ := List.getElem?_eq_some_iff.mp hnode
  have hnodesSame : heap.nodes.set trie node = heap.nodes := by
    rw [← hget]
    exact List.set_getElem_self hindex
  have hbitmapSet : u32 (node.bitmap ||| shiftLeftNat 1 bi.x) = node.bitmap := by
    simpa [shiftLeftNat] using hu32
  have hnodeSet : {node with bitmap := u32 (node.bitmap ||| shiftLeftNat 1 bi.x)} = node := by
    cases node
    simp [hbitmapSet]
  have hnodesSet :
      heap.nodes.set trie {node with bitmap := u32 (node.bitmap ||| shiftLeftNat 1 bi.x)} =
        heap.nodes := by
    rw [hnodeSet, hnodesSame]
  have hnodesSetNat :
      heap.nodes.set trie {node with bitmap := u32 (node.bitmap ||| 2 ^ bi.x)} =
        heap.nodes := by
    simpa [shiftLeftNat] using hnodesSet
  have hbitmapSetNat : u32 (node.bitmap ||| 2 ^ bi.x) = node.bitmap := by
    simpa [shiftLeftNat] using hbitmapSet
  have hnodesSameBitmap :
      heap.nodes.set trie {node with bitmap := node.bitmap} = heap.nodes := by
    have hnodeSame : {node with bitmap := node.bitmap} = node := by
      cases node
      rfl
    rw [hnodeSame]
    exact hnodesSame
  have hheapSame :
      {heap with nodes := heap.nodes.set trie {node with bitmap := node.bitmap}} = heap := by
    cases heap
    simp [hnodesSameBitmap]
  simpa [runHamt, set!, nodeBitmap, readNode, shiftLeftNat, hnode,
    hbitmapSetNat, hheapSame, MonadState.get, MonadState.set,
    MonadStateOf.get, MonadStateOf.set, StateT.run_map, StateT.map,
    Functor.map, Except.map, getThe, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
    ExceptT.bindCont, StateT.run, StateT.bind, StateT.pure, StateT.get,
    StateT.set, Bind.bind, Pure.pure]

private theorem runHamtBindLocal {K V α β : Type} (action : HamtM K V α)
    (next : α → HamtM K V β) (heap : HamtHeap K V) :
    (action >>= next).run heap =
      match action.run heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok value, heap') => (next value).run heap' := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : action heap with
  | mk result after => cases result <;> rfl

private theorem runHamtGetLocal {K V : Type} (heap : HamtHeap K V) :
    (get : HamtM K V (HamtHeap K V)).run heap = (.ok heap, heap) := rfl

private theorem runHamtSetLocal {K V : Type} (heap heap' : HamtHeap K V) :
    (set heap' : HamtM K V Unit).run heap = (.ok (), heap') := rfl

private theorem heapVectorSetRunLocal {K V : Type} (heap : HamtHeap K V)
    (data index : Nat) (entry : Entry K V) (slots : List (Option (Entry K V)))
    (hslots : heap.vectors[data]? = some slots) (hlo : 1 ≤ index)
    (hhi : index ≤ slots.length) :
    runHamt (heapVectorOps.set data index entry) heap =
      (.ok (), {heap with vectors := (heap.vectors.set data
        (slots.set (index - 1) (some entry)))}) := by
  change (heapVectorSet data index entry).run heap = _
  unfold heapVectorSet
  rw [runHamtBindLocal, runHamtGetLocal]
  have hbound : ¬ (index = 0 ∨ slots.length < index) := by omega
  simp [hslots, hbound, runHamtSetLocal]

private theorem nodeDataRunLocal {K V : Type} (heap : HamtHeap K V)
    (trie : HAMT K V) (node : HAMTNode K V)
    (hnode : heap.nodes[trie]? = some node) :
    runHamt (nodeData trie) heap = (.ok node.data, heap) := by
  simp [runHamt, nodeData, readNode, hnode, MonadState.get,
    MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
    StateT.map, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure,
    ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind,
    StateT.pure, StateT.get, Bind.bind, Pure.pure]

private theorem insertExistingRunLocal {K V : Type} (heap : HamtHeap K V)
    (ops : HamtObjectIdRuntime K) (trie index : Nat) (bi : BitmapIndex)
    (hash : HashState K) (value : V)
    (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hnode : heap.nodes[trie]? = some node)
    (hslots : heap.vectors[node.data]? = some slots) (hlo : 1 ≤ index)
    (hhi : index ≤ slots.length) (hbound : node.bitmap < 2 ^ 32)
    (hbit : Nat.testBit node.bitmap bi.x = true) :
    runPartialHamt (insert! heapVectorOps ops true true trie index bi hash value) heap =
      some (.ok (some node.bitmap),
        {heap with vectors := (heap.vectors.set node.data
          (slots.set (index - 1) (some (.leaf ⟨hash.key, value⟩))) )}) := by
  change some (runHamt _ heap) = some _
  apply congrArg some
  let heap1 : HamtHeap K V :=
    {heap with vectors := (heap.vectors.set node.data
      (slots.set (index - 1) (some (.leaf ⟨hash.key, value⟩))))}
  have hdata := nodeDataRunLocal heap trie node hnode
  have hvector : runHamt (heapVectorOps.set node.data index
      (.leaf ⟨hash.key, value⟩)) heap = (.ok (), heap1) := by
    simpa [heap1] using heapVectorSetRunLocal heap node.data index
      (.leaf ⟨hash.key, value⟩) slots hslots hlo hhi
  have hnode1 : heap1.nodes[trie]? = some node := by
    simpa [heap1] using hnode
  have hset := setRun_existingBit heap1 trie bi node hnode1 hbound hbit
  simp only [insert!, if_true]
  rw [runHamtBindEq, hdata]
  simp only [hdata]
  rw [runHamtBindEq, hvector]
  simp only [hvector]
  rw [runHamtBindEq, hset]
  simp [runHamt, heap1, ExceptT.pure, StateT.pure, StateT.run, Pure.pure]
private theorem heapEntriesInvariant_childAt {K V : Type} {heap : HamtHeap K V}
    {slots : List (Option (Entry K V))}
    (hentries : heapEntriesInvariant heap slots) :
    ∀ (i : Nat) (child : HAMT K V),
      slots[i]? = some (some (Entry.trie child)) → heapInvariant heap child := by
  let motiveNode : (trie : HAMT K V) → heapInvariant heap trie → Prop :=
    fun _ _ => True
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant heap slots → Prop :=
    fun (slots : List (Option (Entry K V))) (_ : heapEntriesInvariant heap slots) =>
      ∀ (i : Nat) (child : HAMT K V),
        slots[i]? = some (some (Entry.trie child)) → heapInvariant heap child
  have hrec : motiveEntries slots hentries := by
    refine heapEntriesInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hentries
    · intro trie node slots hnode hslots hbitmap hcount hentries ihEntries
      trivial
    · intro i child hslot
      simp at hslot
    · intro leaf rest hrest ihRest i child hslot
      cases i with
      | zero => simp at hslot
      | succ i => exact ihRest i child (by simpa using hslot)
    · intro storedChild rest hchild hrest ihChild ihRest i child hslot
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at hslot
          injection hslot with hslot
          injection hslot with hslot
          injection hslot with hchildEq
          cases hchildEq
          exact hchild
      | succ i => exact ihRest i child (by simpa using hslot)
  exact hrec

private theorem pathStepCopy_yields {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current : HAMT K V)
    (hash : HashState K) (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hnode : heap.nodes[current]? = some node)
    (hslots : heap.vectors[node.data]? = some slots)
    (hbitmap : node.bitmap < 2 ^ 32)
    (hcount : countOnes 32 node.bitmap = slots.length)
    (hentries : heapEntriesInvariant heap slots) :
    ∃ nextState heapAfter,
      runHamt (pathStepCopy same ops top () (current, hash, none)) heap =
        (.ok (.yield nextState), heapAfter) ∧
      pathStepCopyShape heap same ops top current hash node slots nextState heapAfter := by
  let bi := BitmapIndex.fromHash hash
  let index := countOnes 32 (node.bitmap &&& (shiftLeftNat 1 bi.x - 1)) + 1
  have hinv : heapInvariant heap current := .node hnode hslots hbitmap hcount hentries
  have hindex : runHamt (entry_index current bi) heap = (.ok index, heap) := by
    simp [runHamt, entry_index, nodeBitmap, readNode, hnode, shiftLeftNat,
      MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
      MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run,
      ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.lift,
      StateT.run, StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure, index, bi]
  have hset : runHamt (isset current bi) heap =
      (.ok (Nat.testBit node.bitmap bi.x), heap) := by
    simp [runHamt, isset, nodeBitmap, readNode, hnode, shiftRightNat,
      Nat.testBit_eq_decide_div_mod_eq, natBeqEq, MonadState.get,
      MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
      StateT.map, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure,
      ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind,
      StateT.pure, StateT.get, Bind.bind, Pure.pure]
  have hindexStep : runHamt (entry_index current (BitmapIndex.fromHash hash)) heap =
      (.ok index, heap) := by simpa [bi] using hindex
  have hsetStep :
      runHamt (isset current (BitmapIndex.fromHash hash)) heap =
        (.ok (Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x), heap) := by
    simpa [bi] using hset
  by_cases hbit : Nat.testBit node.bitmap bi.x
  · have hbit' : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true := by
      simpa [bi] using hbit
    have hindexFirst : (runHamt (entry_index current bi) heap).1 = .ok index := by
      simp [hindex]
    have hrank := HamtSlotRank_proven K V heap current bi node.data
      node.bitmap slots index hnode hslots hinv
    rcases hrank.2.1 hbit hindexFirst with ⟨hrank, hlo, hhi⟩
    have hslotIndex : index - 1 < slots.length := by omega
    obtain ⟨entry, hentry⟩ := heapEntriesInvariant_get hentries (index - 1) hslotIndex
    have hread : runHamt (readNode current) heap = (.ok node, heap) := by
      simp [runHamt, readNode, hnode, MonadState.get, MonadStateOf.get,
        getThe, liftM, monadLift, MonadLift.monadLift, StateT.map, Functor.map,
        ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
        ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure]
    have hget : runHamt (heapVectorGet node.data index) heap = (.ok entry, heap) := by
      simp [runHamt, heapVectorGet, heapVectorSlots, hslots, hentry,
        MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
        MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run,
        ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
        ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure]

    have hgetOp : runHamt (heapVectorOps.get node.data index) heap = (.ok entry, heap) := by
      simpa [heapVectorOps] using hget
    cases entry with
    | leaf leaf =>
        refine ⟨(current, hash, some ⟨same leaf.key hash.key, true, current,
          index, bi, top, hash⟩), heap, ?_,
          Or.inl ⟨⟨same leaf.key hash.key, true, current, index, bi, top, hash⟩,
            rfl, rfl, rfl, Or.inl ⟨leaf, rfl, hentry, hbit'⟩⟩⟩
        dsimp [pathStepCopy]
        rw [runHamtBindEq, hindexStep]
        simp only
        rw [runHamtBindEq, hsetStep]
        simp only [hbit', ite_true]
        rw [runHamtBindEq, hread]
        simp only
        dsimp [heapVectorOps]
        rw [runHamtBindEq, hget]
        simp [runHamt, ExceptT.pure, StateT.pure, StateT.run, Pure.pure, bi]
    | trie child =>
        have hslot : slots[index - 1]? = some (some (.trie child)) := hentry
        have hchildInv := heapEntriesInvariant_childAt hentries (index - 1) child hslot
        cases hchildInv with
        | node hchildNode hchildSlots hchildBitmap hchildCount hchildEntries =>
            rename_i childNode childSlots
            let childData := heap.vectors.length
            let childCopy := heap.nodes.length
            let heapCopy : HamtHeap K V :=
              {heap with vectors := heap.vectors ++ [childSlots]}
            let heapInner : HamtHeap K V :=
              {heapCopy with nodes := heapCopy.nodes ++ [⟨childData, childNode.bitmap⟩]}
            let heapAfter := pathCopyChildHeap heap node index slots childNode childSlots
            have hchildRead : runHamt (readNode child) heap = (.ok childNode, heap) := by
              simp [runHamt, readNode, hchildNode, MonadState.get, MonadStateOf.get,
                getThe, liftM, monadLift, MonadLift.monadLift, StateT.map, Functor.map,
                ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
                ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure]
            have hcopy : runHamt (heapVectorOps.copy childNode.data) heap =
                (.ok childData, heapCopy) := by
              simpa [heapVectorOps, childData, heapCopy] using
                heapVectorCopyRun heap childNode.data childSlots hchildSlots
            have hinner : runHamt (HAMT.inner childData childNode.bitmap) heapCopy =
                (.ok childCopy, heapInner) := by
              simpa [childCopy, heapInner, heapCopy] using
                hamtInnerRun heapCopy childData childNode.bitmap
            have hcurrentLt : current < heap.nodes.length :=
              (List.getElem?_eq_some_iff.mp hnode).1
            have hnodeVal : heap.nodes[current]'hcurrentLt = node :=
              (List.getElem?_eq_some_iff.mp hnode).2
            have hnodeInner : heapInner.nodes[current]? = some node := by
              simp [heapInner, heapCopy, List.getElem?_append, hcurrentLt, hnodeVal]
            have hparentData : runHamt (nodeData current) heapInner = (.ok node.data, heapInner) :=
              nodeDataRunLocal heapInner current node hnodeInner
            have hdataLt : node.data < heap.vectors.length :=
              (List.getElem?_eq_some_iff.mp hslots).1
            have hslotsVal : heap.vectors[node.data]'hdataLt = slots :=
              (List.getElem?_eq_some_iff.mp hslots).2
            have hparentSlots : heapInner.vectors[node.data]? = some slots := by
              simp [heapInner, heapCopy, List.getElem?_append, hdataLt, hslotsVal]
            have hsetChild := heapVectorSetRunLocal heapInner node.data index
              (.trie childCopy) slots hparentSlots hlo hhi
            have hsetShape : runHamt (heapVectorOps.set node.data index
                (.trie childCopy)) heapInner = (.ok (), heapAfter) := by
              simpa [heapVectorOps, heapAfter, pathCopyChildHeap, heapInner, heapCopy,
                childData, childCopy] using hsetChild
            refine ⟨(childCopy, next ops hash, none), heapAfter, ?_,
              Or.inr ⟨child, childNode, childSlots, rfl, hslot, hbit',
                hchildNode, hchildSlots, rfl⟩⟩
            dsimp [pathStepCopy]
            rw [runHamtBindEq, hindexStep]
            simp only
            rw [runHamtBindEq, hsetStep]
            simp only [hbit', ite_true]
            rw [runHamtBindEq, hread]
            simp only
            rw [runHamtBindEq, hgetOp]
            simp only
            rw [runHamtBindEq, hchildRead]
            simp only
            rw [runHamtBindEq, hcopy]
            simp only
            rw [runHamtBindEq, hinner]
            simp only
            rw [runHamtBindEq, hparentData]
            simp only
            rw [runHamtBindEq, hsetShape]
            simp [runHamt, ExceptT.run, ExceptT.bind, ExceptT.bindCont,
              ExceptT.pure, ExceptT.mk, StateT.run, StateT.bind,
              StateT.pure, Bind.bind, Pure.pure]
  · have hbitFalse : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = false := by
      cases hval : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x with
      | false => rfl
      | true =>
          apply False.elim
          apply hbit
          simpa [bi] using hval
    refine ⟨(current, hash, some ⟨true, false, current, index, bi, top, hash⟩),
      heap, ?_, Or.inl ⟨⟨true, false, current, index, bi, top, hash⟩,
        rfl, rfl, rfl, Or.inr ⟨rfl, hbitFalse⟩⟩⟩
    dsimp [pathStepCopy]
    rw [runHamtBindEq, hindexStep]
    simp only
    rw [runHamtBindEq, hsetStep]
    simp only [hbitFalse, ite_false]
    simp [bi, runHamt, ExceptT.pure, StateT.pure, StateT.run, Pure.pure]

private theorem pathStepCopyPrefixFrame {K V : Type}
    {base heap heapAfter : HamtHeap K V}
    (same : K → K → Bool) (ops : HamtObjectIdRuntime K) (top current : HAMT K V)
    (hash : HashState K) (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (nextState : HAMT K V × HashState K × Option (PathResult K V))
    (hframe : HeapPrefixFrame base heap) (hextend : HeapLengthsExtend base heap)
    (hdataFresh : base.vectors.length ≤ node.data)
    (hshape : pathStepCopyShape heap same ops top current hash node slots nextState heapAfter) :
    HeapPrefixFrame base heapAfter ∧ HeapLengthsExtend base heapAfter := by
  rcases hshape with ⟨result, _, hheap, _, _⟩ | ⟨child, childNode, childSlots,
    _, _, _, _, _, hheapAfter⟩
  · cases hheap
    exact ⟨hframe, hextend⟩
  · subst heapAfter
    let heapCopy : HamtHeap K V := {heap with vectors := heap.vectors ++ [childSlots]}
    let heapInner : HamtHeap K V :=
      {heapCopy with nodes := heapCopy.nodes ++ [⟨heap.vectors.length, childNode.bitmap⟩]}
    have hframeCopy : HeapPrefixFrame base heapCopy := by
      simpa [heapCopy] using
        heapPrefixFrame_trans hframe (heapVectorAllocatePrefixFrame heap childSlots)
          hextend.1 hextend.2
    have hextendCopy : HeapLengthsExtend base heapCopy := by
      simpa [heapCopy] using heapLengthsExtend_vectorAppend hextend childSlots
    have hframeInner : HeapPrefixFrame base heapInner := by
      simpa [heapInner, heapCopy] using
        heapPrefixFrame_nodeAppend hframeCopy hextendCopy
          ⟨heap.vectors.length, childNode.bitmap⟩
    have hextendInner : HeapLengthsExtend base heapInner := by
      simpa [heapInner, heapCopy] using
        heapLengthsExtend_nodeAppend hextendCopy
          ⟨heap.vectors.length, childNode.bitmap⟩
    have hframeAfter : HeapPrefixFrame base
        {heapInner with vectors := (heapInner.vectors.set node.data
          (slots.set (pathStepIndex node hash - 1) (some (.trie heap.nodes.length))))} :=
      heapPrefixFrame_vectorSet hframeInner node.data _ hdataFresh
    have hextendAfter : HeapLengthsExtend base
        (pathCopyChildHeap heap node (pathStepIndex node hash) slots childNode childSlots) := by
      rcases hextendInner with ⟨hnodes, hvectors⟩
      constructor
      · simpa [pathCopyChildHeap, heapInner, heapCopy] using hnodes
      · simpa [pathCopyChildHeap, heapInner, heapCopy] using hvectors
    constructor
    · simpa [pathCopyChildHeap, heapInner, heapCopy] using hframeAfter
    · exact hextendAfter

private def HamtNodeCopyOf {K V : Type} (base : HamtHeap K V)
    (source : HAMT K V) (heap : HamtHeap K V) (copy : HAMT K V) : Prop :=
  ∃ sourceNode sourceSlots copyNode,
    base.nodes[source]? = some sourceNode ∧
    base.vectors[sourceNode.data]? = some sourceSlots ∧
    heap.nodes[copy]? = some copyNode ∧
    heap.vectors[copyNode.data]? = some sourceSlots ∧
    copyNode.bitmap = sourceNode.bitmap ∧
    base.nodes.length ≤ copy ∧ base.vectors.length ≤ copyNode.data

private theorem heapInvariant_nodeCopy {K V : Type} {base heap : HamtHeap K V}
    (hframe : HeapPrefixFrame base heap) {source copy : HAMT K V}
    (hcopy : HamtNodeCopyOf base source heap copy)
    (hinv : heapInvariant base source) :
    heapInvariant heap copy := by
  rcases hcopy with ⟨sourceNode, sourceSlots, copyNode,
    hsourceNode, hsourceSlots, hcopyNode, hcopySlots, hbitmapEq, _, _⟩
  cases hinv with
  | node hnode hslots hbitmap hcount hentries =>
      rename_i node slots
      have hnodeEq : node = sourceNode :=
        Option.some.inj (hnode.symm.trans hsourceNode)
      subst node
      have hsourceSlotsEq : slots = sourceSlots :=
        Option.some.inj (hslots.symm.trans hsourceSlots)
      have hentriesSource : heapEntriesInvariant base sourceSlots := by
        rw [← hsourceSlotsEq]
        exact hentries
      have hentriesCopy := heapEntriesInvariant_prefixFrame hframe hentriesSource
      have hcopyBound : copyNode.bitmap < 2 ^ 32 := by
        rw [hbitmapEq]
        exact hbitmap
      have hcopyCount : countOnes 32 copyNode.bitmap = sourceSlots.length := by
        rw [hbitmapEq, ← hsourceSlotsEq]
        exact hcount
      exact .node hcopyNode hcopySlots hcopyBound hcopyCount hentriesCopy

private theorem heapMap_nodeCopy {K V : Type} {base heap : HamtHeap K V}
    {source copy : HAMT K V} (hcopy : HamtNodeCopyOf base source heap copy)
    (hinv : heapInvariant base source) (hframe : HeapPrefixFrame base heap) :
    readMap base source = readMap heap copy := by
  rcases hcopy with ⟨sourceNode, sourceSlots, copyNode,
    hsourceNode, hsourceSlots, hcopyNode, hcopySlots, hbitmapEq, _, _⟩
  cases hinv with
  | node hnode hslots hbitmap hcount hentries =>
      rename_i node slots
      have hnodeEq : sourceNode = node :=
        Option.some.inj (hsourceNode.symm.trans hnode)
      subst sourceNode
      have hslotsEq : sourceSlots = slots :=
        Option.some.inj (hsourceSlots.symm.trans hslots)
      subst sourceSlots
      change heapMap base source = heapMap heap copy
      simp only [heapMap.eq_1, hnode, hslots, hcopyNode, hcopySlots]
      exact heapEntriesMap_prefixFrame hframe hentries

private theorem pathStepCopy_done {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (top current : HAMT K V) (hash : HashState K)
    (result : PathResult K V) (heap : HamtHeap K V) :
    runHamt (pathStepCopy same ops top () (current, hash, some result)) heap =
      (.ok (.done (current, hash, some result)), heap) := by
  simp [pathStepCopy, runHamt, ExceptT.run, ExceptT.pure, ExceptT.mk,
    StateT.run, StateT.pure, Bind.bind, Pure.pure]

private def HamtCopyPathTraceProperty {K V : Type} (base : HamtHeap K V)
    (same : K → K → Bool) (ops : HamtObjectIdRuntime K) (top : HAMT K V)
    (heap : HamtHeap K V) (current : HAMT K V) : Prop :=
  ∀ hash, ∃ finalTrie finalHash result heapFinal,
    HamtLoopTrace (pathStepCopy same ops top)
      (current, hash, none) heap (finalTrie, finalHash, some result) heapFinal ∧
    HeapPrefixFrame base heapFinal ∧ HeapLengthsExtend base heapFinal

private theorem pathCopyLoopTraceWithFrame {K V : Type}
    (same : K → K → Bool) (ops : HamtObjectIdRuntime K) (base : HamtHeap K V)
    (top : HAMT K V) :
    ∀ {source : HAMT K V}, heapInvariant base source →
    ∀ {heap : HamtHeap K V} {current : HAMT K V},
      HamtNodeCopyOf base source heap current →
      HeapPrefixFrame base heap → HeapLengthsExtend base heap →
      HamtCopyPathTraceProperty base same ops top heap current := by
  intro source hinv
  let motiveNode : (source : HAMT K V) → heapInvariant base source → Prop :=
    fun source _ =>
      ∀ {heap : HamtHeap K V} {current : HAMT K V},
        HamtNodeCopyOf base source heap current →
        HeapPrefixFrame base heap → HeapLengthsExtend base heap →
        HamtCopyPathTraceProperty base same ops top heap current
  let motiveEntries :
      (slots : List (Option (Entry K V))) → heapEntriesInvariant base slots → Prop :=
    fun slots _ =>
      ∀ (i : Nat) (child : HAMT K V),
        slots[i]? = some (some (.trie child)) →
        ∀ {heap : HamtHeap K V} {current : HAMT K V},
          HamtNodeCopyOf base child heap current →
          HeapPrefixFrame base heap → HeapLengthsExtend base heap →
          HamtCopyPathTraceProperty base same ops top heap current
  have hrec : motiveNode source hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro sourceTrie sourceNode sourceSlots hsourceNode hsourceSlots
        hsourceBitmap hsourceCount hsourceEntries ihEntries
      intro heap current hcopy hframe hextend
      rcases hcopy with ⟨copySourceNode, copySourceSlots, currentNode,
        hcopySourceNode, hcopySourceSlots, hcopyNode, hcopySlots, hbitmapEq,
        hfreshNode, hfreshData⟩
      have hsourceNodeEq : copySourceNode = sourceNode :=
        Option.some.inj (hcopySourceNode.symm.trans hsourceNode)
      subst copySourceNode
      have hsourceSlotsEq : sourceSlots = copySourceSlots :=
        Option.some.inj (hsourceSlots.symm.trans hcopySourceSlots)
      have hcopySlots' : heap.vectors[currentNode.data]? = some sourceSlots := by
        simpa [hsourceSlotsEq] using hcopySlots
      have hcopyBound : currentNode.bitmap < 2 ^ 32 := by
        rw [hbitmapEq]
        exact hsourceBitmap
      have hcopyCount : countOnes 32 currentNode.bitmap = sourceSlots.length := by
        rw [hbitmapEq]
        exact hsourceCount
      have hentriesCopy := heapEntriesInvariant_prefixFrame hframe hsourceEntries
      intro hash
      obtain ⟨nextState, heapAfter, hstep, hshape⟩ :=
        pathStepCopy_yields same ops heap top current hash currentNode sourceSlots
          hcopyNode hcopySlots' hcopyBound hcopyCount hentriesCopy
      obtain ⟨hframeAfter, hextendAfter⟩ :=
        pathStepCopyPrefixFrame same ops top current hash currentNode sourceSlots
          nextState hframe hextend hfreshData hshape
      rcases hshape with
        ⟨result, hstate, hheapEq, _, _⟩ |
        ⟨child, childNode, childSlots, hstate, hslot, _, hchildNode, hchildSlots, hheapEq⟩
      · have hstep' : runHamt (pathStepCopy same ops top () (current, hash, none)) heap =
          (.ok (.yield nextState), heap) := by
          simpa [hheapEq] using hstep
        have hrest : HamtLoopTrace (pathStepCopy same ops top) nextState heap
            (current, hash, some result) heap := by
          rw [hstate]
          exact .done (pathStepCopy_done same ops top current hash result heap)
        exact ⟨current, hash, result, heap, .yield hstep' hrest, hframe, hextend⟩
      · have hchildSourceInv :=
          heapEntriesInvariant_childAt hsourceEntries (pathStepIndex currentNode hash - 1)
            child hslot
        cases hchildSourceInv with
        | node hchildNodeBase hchildSlotsBase hchildBitmap hchildCount hchildEntries =>
            rename_i sourceChildNode sourceChildSlots
            have hchildNodeLt : child < base.nodes.length :=
              (List.getElem?_eq_some_iff.mp hchildNodeBase).1
            have hchildNodeInHeap : heap.nodes[child]? = some sourceChildNode :=
              (hframe.1 child hchildNodeLt).symm.trans hchildNodeBase
            have hchildNodeEq : childNode = sourceChildNode :=
              Option.some.inj (hchildNode.symm.trans hchildNodeInHeap)
            subst childNode
            have hchildDataLt : sourceChildNode.data < base.vectors.length :=
              (List.getElem?_eq_some_iff.mp hchildSlotsBase).1
            have hchildSlotsInHeap :
                heap.vectors[sourceChildNode.data]? = some sourceChildSlots :=
              (hframe.2 sourceChildNode.data hchildDataLt).symm.trans hchildSlotsBase
            have hchildSlotsEq : childSlots = sourceChildSlots :=
              Option.some.inj (hchildSlots.symm.trans hchildSlotsInHeap)
            have hparentDataLt : currentNode.data < heap.vectors.length :=
              (List.getElem?_eq_some_iff.mp hcopySlots').1
            have hparentDataNe : currentNode.data ≠ heap.vectors.length := by omega
            let childCopyNode : HAMTNode K V :=
              ⟨heap.vectors.length, sourceChildNode.bitmap⟩
            have hcopyNodeNew :
                heapAfter.nodes[heap.nodes.length]? = some childCopyNode := by
              rw [hheapEq]
              simp [pathCopyChildHeap, childCopyNode]
            have hcopySlotsNew :
                heapAfter.vectors[childCopyNode.data]? = some sourceChildSlots := by
              rw [hheapEq]
              simp [pathCopyChildHeap, childCopyNode, List.getElem?_set,
                List.getElem?_append, hparentDataNe, hchildSlotsEq]
            have hcopyChild : HamtNodeCopyOf base child heapAfter heap.nodes.length :=
              ⟨sourceChildNode, sourceChildSlots, childCopyNode,
                hchildNodeBase, hchildSlotsBase, hcopyNodeNew, hcopySlotsNew, rfl,
                hextend.1, by simpa [childCopyNode] using hextend.2⟩
            obtain ⟨finalTrie, finalHash, result, heapFinal, hrest, hframeFinal,
              hextendFinal⟩ :=
              ihEntries (pathStepIndex currentNode hash - 1) child hslot hcopyChild
                hframeAfter hextendAfter (next ops hash)
            have hrest' : HamtLoopTrace (pathStepCopy same ops top) nextState heapAfter
                (finalTrie, finalHash, some result) heapFinal := by
              rw [hstate]
              exact hrest
            exact ⟨finalTrie, finalHash, result, heapFinal,
              .yield hstep hrest', hframeFinal, hextendFinal⟩
    · intro i child hslot
      cases i <;> simp at hslot
    · intro leaf rest hrest ihRest i child hslot
      cases i with
      | zero => simp at hslot
      | succ i =>
          intro heap current hcopy hframe hextend hash
          exact ihRest i child (by simpa using hslot) hcopy hframe hextend hash
    · intro storedChild rest hchild hrest ihChild ihRest i child hslot
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at hslot
          injection hslot with hslot
          injection hslot with hchildEq
          cases hchildEq
          intro heap current hcopy hframe hextend hash
          exact ihChild hcopy hframe hextend hash
      | succ i =>
          intro heap current hcopy hframe hextend hash
          exact ihRest i child (by simpa using hslot) hcopy hframe hextend hash
  intro heap current hcopy hframe hextend
  exact hrec hcopy hframe hextend

private theorem heapPrefixFrame_nodeSet {K V : Type}
    {base heap : HamtHeap K V} (hframe : HeapPrefixFrame base heap)
    (trie : Nat) (node : HAMTNode K V) (hfresh : base.nodes.length ≤ trie) :
    HeapPrefixFrame base {heap with nodes := heap.nodes.set trie node} := by
  constructor
  · intro i hi
    have hne : trie ≠ i := by omega
    simpa [List.getElem?_set, hne] using hframe.1 i hi
  · exact hframe.2

private theorem heapVectorInsertRunLocal {K V : Type} (heap : HamtHeap K V)
    (data index : Nat) (entry : JuliaLean.base.hamt.Entry K V)
    (slots : List (Option (JuliaLean.base.hamt.Entry K V)))
    (hslots : heap.vectors[data]? = some slots)
    (hlo : 1 ≤ index) (hhi : index ≤ slots.length + 1) :
    runHamt (heapVectorOps.insert data index entry) heap =
      (.ok (), {heap with vectors := (heap.vectors.set data
        (slots.insertIdx (index - 1) (some entry)))}) := by
  change (heapVectorInsert data index entry).run heap = _
  unfold heapVectorInsert
  rw [runHamtBindLocal, runHamtGetLocal]
  have hbound : ¬ (index = 0 ∨ slots.length + 1 < index) := by omega
  simp [hslots, hbound, runHamtSetLocal]

private theorem setRunLocal {K V : Type} (heap : HamtHeap K V)
    (trie : Nat) (node : HAMTNode K V) (bi : BitmapIndex)
    (hnode : heap.nodes[trie]? = some node) :
    runHamt (set! trie bi) heap =
      (.ok (u32 (node.bitmap ||| shiftLeftNat 1 bi.x)),
        {heap with nodes := (heap.nodes.set trie
          {node with bitmap := u32 (node.bitmap ||| shiftLeftNat 1 bi.x)})}) := by
  simp [runHamt, set!, readNode, hnode, MonadState.get, MonadState.set,
    MonadStateOf.get, MonadStateOf.set, getThe, liftM, monadLift,
    MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run, ExceptT.bind,
    ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run,
    StateT.bind, StateT.pure, StateT.get, StateT.set, Bind.bind, Pure.pure]

private theorem insertFoundBounds {K V : Type}
    (heap heapAfter : HamtHeap K V) (ops : HamtObjectIdRuntime K)
    (trie index : Nat) (bi : BitmapIndex) (hash : HashState K)
    (value : V) (present : Bool) (inserted : Option BITMAP)
    (node : HAMTNode K V) (hnode : heap.nodes[trie]? = some node)
    (hrun : runPartialHamt (insert! heapVectorOps ops true present trie index bi hash value) heap =
      some (.ok inserted, heapAfter)) :
    ∃ slots, heap.vectors[node.data]? = some slots ∧ 1 ≤ index ∧
      index ≤ slots.length + if present then 0 else 1 := by
  change some (runHamt _ heap) = some _ at hrun
  replace hrun := Option.some.inj hrun
  have hdata := nodeDataRunLocal heap trie node hnode
  rw [runHamtBindEq, hdata] at hrun
  simp only at hrun
  cases hslots : heap.vectors[node.data]? with
  | none =>
      cases present <;>
        simp [runHamt, heapVectorOps, heapVectorSet, heapVectorInsert, hslots,
          MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
          MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run, ExceptT.bind,
          ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run,
          StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure,
          throw, throwThe, MonadExceptOf.throw] at hrun
  | some slots =>
      refine ⟨slots, rfl, ?_⟩
      by_cases hbad : index = 0 ∨ slots.length + (if present then 0 else 1) < index
      · cases present <;>
          simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at hbad <;>
          simp [runHamt, heapVectorOps, heapVectorSet, heapVectorInsert, hslots,
            hbad, MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
            MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run, ExceptT.bind,
            ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run,
            StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure,
            throw, throwThe, MonadExceptOf.throw] at hrun
      · constructor <;> omega

private theorem insertFoundPrefixFrame {K V : Type}
    (base heap heapAfter : HamtHeap K V) (ops : HamtObjectIdRuntime K)
    (trie index : Nat) (bi : BitmapIndex) (hash : HashState K)
    (value : V) (present : Bool) (inserted : Option BITMAP)
    (node : HAMTNode K V) (slots : List (Option (JuliaLean.base.hamt.Entry K V)))
    (hframe : HeapPrefixFrame base heap)
    (hnode : heap.nodes[trie]? = some node) (hslots : heap.vectors[node.data]? = some slots)
    (hfreshNode : base.nodes.length ≤ trie) (hfreshData : base.vectors.length ≤ node.data)
    (hlo : 1 ≤ index) (hhi : index ≤ slots.length + if present then 0 else 1)
    (hrun : runPartialHamt (insert! heapVectorOps ops true present trie index bi hash value) heap =
      some (.ok inserted, heapAfter)) :
    HeapPrefixFrame base heapAfter := by
  change some (runHamt _ heap) = some _ at hrun
  replace hrun := Option.some.inj hrun
  have hdata := nodeDataRunLocal heap trie node hnode
  cases present with
  | false =>
      let middle : HamtHeap K V := {heap with vectors := (heap.vectors.set node.data
        (slots.insertIdx (index - 1) (some (.leaf ⟨hash.key, value⟩))))}
      have hvector : runHamt (heapVectorOps.insert node.data index (.leaf ⟨hash.key, value⟩)) heap =
          (.ok (), middle) :=
        heapVectorInsertRunLocal heap node.data index _ slots hslots hlo (by simpa using hhi)
      have hnodeMiddle : middle.nodes[trie]? = some node := hnode
      have hset := setRunLocal middle trie node bi hnodeMiddle
      rw [runHamtBindEq, hdata] at hrun
      simp only [Bool.false_eq_true, ite_false] at hrun
      rw [runHamtBindEq, hvector] at hrun
      simp only at hrun
      rw [runHamtBindEq, hset] at hrun
      have hheap := congrArg Prod.snd hrun
      simp only [runHamt, ExceptT.run, ExceptT.pure, ExceptT.mk, StateT.run,
        StateT.pure, Pure.pure] at hheap
      rw [← hheap]
      exact heapPrefixFrame_nodeSet
        (heapPrefixFrame_vectorSet hframe node.data _ hfreshData) trie _ hfreshNode
  | true =>
      let middle : HamtHeap K V := {heap with vectors := (heap.vectors.set node.data
        (slots.set (index - 1) (some (.leaf ⟨hash.key, value⟩))))}
      have hvector : runHamt (heapVectorOps.set node.data index (.leaf ⟨hash.key, value⟩)) heap =
          (.ok (), middle) :=
        heapVectorSetRunLocal heap node.data index _ slots hslots hlo (by simpa using hhi)
      have hnodeMiddle : middle.nodes[trie]? = some node := hnode
      have hset := setRunLocal middle trie node bi hnodeMiddle
      rw [runHamtBindEq, hdata] at hrun
      simp only [ite_true] at hrun
      rw [runHamtBindEq, hvector] at hrun
      simp only at hrun
      rw [runHamtBindEq, hset] at hrun
      have hheap := congrArg Prod.snd hrun
      simp only [runHamt, ExceptT.run, ExceptT.pure, ExceptT.mk, StateT.run,
        StateT.pure, Pure.pure] at hheap
      rw [← hheap]
      exact heapPrefixFrame_nodeSet
        (heapPrefixFrame_vectorSet hframe node.data _ hfreshData) trie _ hfreshNode

private theorem heapEntriesInvariant_replaceTrie {K V : Type}
    {base heap : HamtHeap K V} (hframe : HeapPrefixFrame base heap)
    {slots : List (Option (JuliaLean.base.hamt.Entry K V))}
    (hinv : heapEntriesInvariant base slots) (index : Nat)
    (oldChild newChild : HAMT K V)
    (hslot : slots[index]? = some (some (.trie oldChild)))
    (hnew : heapInvariant heap newChild) :
    heapEntriesInvariant heap (slots.set index (some (.trie newChild))) := by
  induction slots generalizing index with
  | nil => simp at hslot
  | cons entry rest ih =>
      cases hinv with
      | leaf hrest =>
          cases index with
          | zero => simp at hslot
          | succ index =>
              exact .leaf (ih hrest index (by simpa using hslot))
      | trie hchild hrest =>
          rename_i child
          cases index with
          | zero =>
              have heq : child = oldChild := by simpa using hslot
              exact .trie hnew (heapEntriesInvariant_prefixFrame hframe hrest)
          | succ index =>
              exact .trie (heapInvariant_prefixFrame hframe hchild)
                (ih hrest index (by simpa using hslot))

private theorem heapEntriesInvariant_setLeaf {K V : Type}
    {heap : HamtHeap K V} {slots : List (Option (JuliaLean.base.hamt.Entry K V))}
    (hinv : heapEntriesInvariant heap slots) (index : Nat) (leaf : Leaf K V) :
    heapEntriesInvariant heap (slots.set index (some (.leaf leaf))) := by
  induction slots generalizing index with
  | nil => cases index <;> exact .nil
  | cons entry rest ih =>
      cases hinv with
      | leaf hrest =>
          cases index with
          | zero => exact .leaf hrest
          | succ index => exact .leaf (ih hrest index)
      | trie hchild hrest =>
          cases index with
          | zero => exact .leaf hrest
          | succ index => exact .trie hchild (ih hrest index)

private theorem heapEntriesInvariant_insertLeaf {K V : Type}
    {heap : HamtHeap K V} {slots : List (Option (JuliaLean.base.hamt.Entry K V))}
    (hinv : heapEntriesInvariant heap slots) (index : Nat) (leaf : Leaf K V) :
    heapEntriesInvariant heap (slots.insertIdx index (some (.leaf leaf))) := by
  induction slots generalizing index with
  | nil =>
      cases index with
      | zero => exact .leaf .nil
      | succ index => exact .nil
  | cons entry rest ih =>
      cases index with
      | zero => exact .leaf hinv
      | succ index =>
          cases hinv with
          | leaf hrest => exact .leaf (ih hrest index)
          | trie hchild hrest => exact .trie hchild (ih hrest index)

private theorem listLength_insertIdx {A : Type} (slots : List A) (index : Nat) (value : A)
    (hindex : index ≤ slots.length) :
    (slots.insertIdx index value).length = slots.length + 1 := by
  induction slots generalizing index with
  | nil => cases index with
    | zero => rfl
    | succ index => simp at hindex
  | cons entry rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have hi : index ≤ rest.length := by simpa using hindex
          simpa [List.insertIdx] using congrArg Nat.succ (ih index hi)

private theorem insertFoundRunLocal {K V : Type}
    (heap : HamtHeap K V) (ops : HamtObjectIdRuntime K) (trie index : Nat)
    (bi : BitmapIndex) (hash : HashState K) (value : V) (present : Bool)
    (node : HAMTNode K V) (slots : List (Option (JuliaLean.base.hamt.Entry K V)))
    (hnode : heap.nodes[trie]? = some node) (hslots : heap.vectors[node.data]? = some slots)
    (hlo : 1 ≤ index) (hhi : index ≤ slots.length + if present then 0 else 1) :
    runPartialHamt (insert! heapVectorOps ops true present trie index bi hash value) heap =
      some (.ok (some (u32 (node.bitmap ||| shiftLeftNat 1 bi.x))),
        {heap with
          vectors := (heap.vectors.set node.data (if present then
            slots.set (index - 1) (some (.leaf ⟨hash.key, value⟩)) else
            slots.insertIdx (index - 1) (some (.leaf ⟨hash.key, value⟩))))
          nodes := (heap.nodes.set trie
            {node with bitmap := u32 (node.bitmap ||| shiftLeftNat 1 bi.x)})}) := by
  change some (runHamt _ heap) = some _
  apply congrArg some
  have hdata := nodeDataRunLocal heap trie node hnode
  cases present with
  | false =>
      let middle : HamtHeap K V := {heap with vectors := (heap.vectors.set node.data
        (slots.insertIdx (index - 1) (some (.leaf ⟨hash.key, value⟩))))}
      have hv : runHamt (heapVectorOps.insert node.data index (.leaf ⟨hash.key, value⟩)) heap =
          (.ok (), middle) :=
        heapVectorInsertRunLocal heap node.data index _ slots hslots hlo (by simpa using hhi)
      have hn : middle.nodes[trie]? = some node := hnode
      have hs := setRunLocal middle trie node bi hn
      rw [runHamtBindEq, hdata]
      simp only [Bool.false_eq_true, ite_false]
      rw [runHamtBindEq, hv]
      simp only
      rw [runHamtBindEq, hs]
      rfl
  | true =>
      let middle : HamtHeap K V := {heap with vectors := (heap.vectors.set node.data
        (slots.set (index - 1) (some (.leaf ⟨hash.key, value⟩))))}
      have hv : runHamt (heapVectorOps.set node.data index (.leaf ⟨hash.key, value⟩)) heap =
          (.ok (), middle) :=
        heapVectorSetRunLocal heap node.data index _ slots hslots hlo (by simpa using hhi)
      have hn : middle.nodes[trie]? = some node := hnode
      have hs := setRunLocal middle trie node bi hn
      rw [runHamtBindEq, hdata]
      simp only [ite_true]
      rw [runHamtBindEq, hv]
      simp only
      rw [runHamtBindEq, hs]
      rfl

private theorem insertFoundLocalInvariant {K V : Type}
    (base heap heapAfter : HamtHeap K V) (ops : HamtObjectIdRuntime K)
    (trie index : Nat) (bi : BitmapIndex) (hash : HashState K)
    (value : V) (present : Bool) (inserted : Option BITMAP)
    (node : HAMTNode K V) (slots : List (Option (JuliaLean.base.hamt.Entry K V)))
    (hframe : HeapPrefixFrame base heap)
    (hnode : heap.nodes[trie]? = some node) (hslots : heap.vectors[node.data]? = some slots)
    (hbound : node.bitmap < 2 ^ 32) (hcount : countOnes 32 node.bitmap = slots.length)
    (hentries : heapEntriesInvariant base slots)
    (hfreshNode : base.nodes.length ≤ trie) (hfreshData : base.vectors.length ≤ node.data)
    (hbi : bi.x < 32) (hbit : Nat.testBit node.bitmap bi.x = present)
    (hrun : runPartialHamt (insert! heapVectorOps ops true present trie index bi hash value) heap =
      some (.ok inserted, heapAfter)) :
    HeapPrefixFrame base heapAfter ∧ heapInvariant heapAfter trie := by
  obtain ⟨slots', hslots', hlo, hhi⟩ :=
    insertFoundBounds heap heapAfter ops trie index bi hash value present inserted node hnode hrun
  have heq : slots' = slots := Option.some.inj (hslots'.symm.trans hslots)
  subst slots'
  have hframeAfter := insertFoundPrefixFrame base heap heapAfter ops trie index bi hash value
    present inserted node slots hframe hnode hslots hfreshNode hfreshData hlo hhi hrun
  have hmodel := insertFoundRunLocal heap ops trie index bi hash value present node slots
    hnode hslots hlo hhi
  have hheap := congrArg Prod.snd (Option.some.inj (hmodel.symm.trans hrun))
  dsimp only at hheap
  let newSlots := if present then slots.set (index - 1) (some (.leaf ⟨hash.key, value⟩))
    else slots.insertIdx (index - 1) (some (.leaf ⟨hash.key, value⟩))
  let bitmap := u32 (node.bitmap ||| shiftLeftNat 1 bi.x)
  have hnodeLt := (List.getElem?_eq_some_iff.mp hnode).1
  have hdataLt := (List.getElem?_eq_some_iff.mp hslots).1
  have hnodeAfter : heapAfter.nodes[trie]? = some {node with bitmap := bitmap} := by
    rw [← hheap]
    simp [bitmap, List.getElem?_set_self hnodeLt]
  have hslotsAfter : heapAfter.vectors[node.data]? = some newSlots := by
    rw [← hheap]
    simp [newSlots, List.getElem?_set_self hdataLt]
  have hentriesAfter := heapEntriesInvariant_prefixFrame hframeAfter hentries
  have hentriesNew : heapEntriesInvariant heapAfter newSlots := by
    cases present with
    | false => exact heapEntriesInvariant_insertLeaf hentriesAfter (index - 1) _
    | true => exact heapEntriesInvariant_setLeaf hentriesAfter (index - 1) _
  have hbitmapBound : bitmap < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hnewCount : countOnes 32 bitmap = newSlots.length := by
    cases present with
    | false =>
        have hpow : 2 ^ bi.x < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hbi
        have hor : node.bitmap ||| 2 ^ bi.x < 2 ^ 32 := Nat.or_lt_two_pow hbound hpow
        have hlen := listLength_insertIdx slots (index - 1)
          (some (.leaf ⟨hash.key, value⟩)) (by simp only [Bool.false_eq_true, ite_false] at hhi; omega)
        have hbitmapEq : bitmap = node.bitmap ||| 2 ^ bi.x := by
          change (node.bitmap ||| shiftLeftNat 1 bi.x) % 2 ^ 32 = _
          simpa only [shiftLeftNat, Nat.one_mul] using Nat.mod_eq_of_lt hor
        change countOnes 32 bitmap =
          (slots.insertIdx (index - 1) (some (.leaf ⟨hash.key, value⟩))).length
        rw [hbitmapEq, countOnes_or_pow 32 node.bitmap bi.x hbi hbit, hcount, hlen]
    | true =>
        have heqBitmap : bitmap = node.bitmap := by
          have heqRuns := (setRunLocal heap trie node bi hnode).symm.trans
            (setRun_existingBit heap trie bi node hnode hbound hbit)
          exact Except.ok.inj (congrArg Prod.fst heqRuns)
        change countOnes 32 bitmap =
          (slots.set (index - 1) (some (.leaf ⟨hash.key, value⟩))).length
        rw [heqBitmap]
        simpa only [List.length_set] using hcount
  exact ⟨hframeAfter, .node hnodeAfter hslotsAfter hbitmapBound hnewCount hentriesNew⟩

private def FoundInsertionContinuation {K V : Type}
    (base heap : HamtHeap K V) (root : HAMT K V) (result : PathResult K V)
    (ops : HamtObjectIdRuntime K) : Prop :=
  ∀ value inserted heapAfter, result.found = true →
    runPartialHamt (insert! heapVectorOps ops result.found result.present result.trie
      result.index result.bi result.hash value) heap = some (.ok inserted, heapAfter) →
    HeapPrefixFrame base heapAfter ∧ heapInvariant heapAfter root

private def HamtCopyPathMapProperty {K V : Type} (base : HamtHeap K V)
    (source : HAMT K V) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (top : HAMT K V) (heap : HamtHeap K V) (current : HAMT K V) : Prop :=
  ∀ hash, ∃ finalTrie finalHash result heapFinal,
    HamtLoopTrace (pathStepCopy same ops top)
      (current, hash, none) heap (finalTrie, finalHash, some result) heapFinal ∧
    HeapPrefixFrame base heapFinal ∧ HeapLengthsExtend base heapFinal ∧
    readMap base source = readMap heapFinal current ∧ heapInvariant heapFinal current ∧
    FoundInsertionContinuation base heapFinal current result ops ∧
    result.top = top ∧
    ∃ terminalNode, heapFinal.nodes[result.trie]? = some terminalNode ∧
      base.nodes.length ≤ result.trie ∧ base.vectors.length ≤ terminalNode.data

private theorem pathCopyLoopTraceMap {K V : Type}
    (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (sourceBase : HamtHeap K V) (top : HAMT K V) :
    ∀ {source : HAMT K V}, heapInvariant sourceBase source →
    ∀ {base heap : HamtHeap K V} {current : HAMT K V},
      heapInvariant base source → HeapPrefixFrame sourceBase base →
      HeapLengthsExtend sourceBase base → HamtNodeCopyOf base source heap current →
      HeapPrefixFrame base heap → HeapLengthsExtend base heap →
      HamtCopyPathMapProperty base source same ops top heap current := by
  intro source hinv
  let motiveNode : (source : HAMT K V) → heapInvariant sourceBase source → Prop :=
    fun source _ =>
      ∀ {base heap : HamtHeap K V} {current : HAMT K V},
        heapInvariant base source → HeapPrefixFrame sourceBase base →
        HeapLengthsExtend sourceBase base → HamtNodeCopyOf base source heap current →
        HeapPrefixFrame base heap → HeapLengthsExtend base heap →
        HamtCopyPathMapProperty base source same ops top heap current
  let motiveEntries :
      (slots : List (Option (Entry K V))) →
        heapEntriesInvariant sourceBase slots → Prop :=
    fun slots _ =>
      ∀ (i : Nat) (child : HAMT K V),
        slots[i]? = some (some (.trie child)) →
      ∀ {base heap : HamtHeap K V} {current : HAMT K V},
        heapInvariant base child → HeapPrefixFrame sourceBase base →
        HeapLengthsExtend sourceBase base → HamtNodeCopyOf base child heap current →
        HeapPrefixFrame base heap → HeapLengthsExtend base heap →
        HamtCopyPathMapProperty base child same ops top heap current
  have hrec : motiveNode source hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro sourceTrie sourceNode sourceSlots hsourceNode hsourceSlots
        hsourceBitmap hsourceCount hsourceEntries ihEntries
      intro base heap current hinvBase hbaseFrame hbaseExtend hcopy hframe hextend
      rcases hcopy with ⟨copySourceNode, copySourceSlots, currentNode,
        hcopySourceNode, hcopySourceSlots, hcopyNode, hcopySlots, hbitmapEq,
        hfreshNode, hfreshData⟩
      have hsourceNodeLt : sourceTrie < sourceBase.nodes.length :=
        (List.getElem?_eq_some_iff.mp hsourceNode).1
      have hbaseSourceNode : base.nodes[sourceTrie]? = some sourceNode :=
        (hbaseFrame.1 sourceTrie hsourceNodeLt).symm.trans hsourceNode
      have hsourceDataLt : sourceNode.data < sourceBase.vectors.length :=
        (List.getElem?_eq_some_iff.mp hsourceSlots).1
      have hbaseSourceSlots : base.vectors[sourceNode.data]? = some sourceSlots :=
        (hbaseFrame.2 sourceNode.data hsourceDataLt).symm.trans hsourceSlots
      have hsourceNodeEq : copySourceNode = sourceNode :=
        Option.some.inj (hcopySourceNode.symm.trans hbaseSourceNode)
      subst copySourceNode
      have hsourceSlotsEq : sourceSlots = copySourceSlots :=
        Option.some.inj (hbaseSourceSlots.symm.trans hcopySourceSlots)
      have hcopySlots' : heap.vectors[currentNode.data]? = some sourceSlots := by
        simpa [hsourceSlotsEq] using hcopySlots
      have hcopyBound : currentNode.bitmap < 2 ^ 32 := by
        rw [hbitmapEq]
        exact hsourceBitmap
      have hcopyCount : countOnes 32 currentNode.bitmap = sourceSlots.length := by
        rw [hbitmapEq]
        exact hsourceCount
      have hentriesBase := heapEntriesInvariant_prefixFrame hbaseFrame hsourceEntries
      have hentriesCopy := heapEntriesInvariant_prefixFrame hframe hentriesBase
      have hcopyCurrent : HamtNodeCopyOf base sourceTrie heap current :=
        ⟨sourceNode, sourceSlots, currentNode, hbaseSourceNode, hbaseSourceSlots,
          hcopyNode, hcopySlots', hbitmapEq, hfreshNode, hfreshData⟩
      intro hash
      obtain ⟨nextState, heapAfter, hstep, hshape⟩ :=
        pathStepCopy_yields same ops heap top current hash currentNode sourceSlots
          hcopyNode hcopySlots' hcopyBound hcopyCount hentriesCopy
      obtain ⟨hframeAfter, hextendAfter⟩ :=
        pathStepCopyPrefixFrame same ops top current hash currentNode sourceSlots
          nextState hframe hextend hfreshData hshape
      rcases hshape with
        ⟨result, hstate, hheapEq, hresultTrie, hterminal⟩ |
        ⟨child, childNode, childSlots, hstate, hslot, _, hchildNode, hchildSlots, hheapEq⟩
      · have hstep' : runHamt (pathStepCopy same ops top () (current, hash, none)) heap =
          (.ok (.yield nextState), heap) := by
          simpa [hheapEq] using hstep
        have hrest : HamtLoopTrace (pathStepCopy same ops top) nextState heap
            (current, hash, some result) heap := by
          rw [hstate]
          exact .done (pathStepCopy_done same ops top current hash result heap)
        have hmap := heapMap_nodeCopy hcopyCurrent hinvBase hframe
        have htop : result.top = top := by
          rcases hterminal with ⟨leaf, rfl, _, _⟩ | ⟨rfl, _⟩ <;> rfl
        have hcontinue : FoundInsertionContinuation base heap current result ops := by
          intro value inserted heapAfter hfound hinsert
          rw [hfound] at hinsert
          have hbi : (BitmapIndex.fromHash hash).x < 32 := by
            simpa [BitmapIndex.fromHash] using Nat.and_lt_two_pow
              (shiftRightNat hash.hash.val.toNat hash.shift) (show LEVEL_MASK < 2 ^ 5 by decide)
          rcases hterminal with ⟨leaf, hresult, _, hbit⟩ | ⟨hresult, hbit⟩
          · subst result
            exact insertFoundLocalInvariant base heap heapAfter ops current
              (pathStepIndex currentNode hash) (BitmapIndex.fromHash hash) hash value true
              inserted currentNode sourceSlots hframe hcopyNode hcopySlots' hcopyBound
              hcopyCount hentriesBase hfreshNode hfreshData hbi hbit hinsert
          · subst result
            exact insertFoundLocalInvariant base heap heapAfter ops current
              (pathStepIndex currentNode hash) (BitmapIndex.fromHash hash) hash value false
              inserted currentNode sourceSlots hframe hcopyNode hcopySlots' hcopyBound
              hcopyCount hentriesBase hfreshNode hfreshData hbi hbit hinsert
        refine ⟨current, hash, result, heap, .yield hstep' hrest, hframe, hextend,
          hmap, .node hcopyNode hcopySlots' hcopyBound hcopyCount hentriesCopy,
          hcontinue, htop, currentNode, ?_, ?_, hfreshData⟩
        · simpa [hresultTrie] using hcopyNode
        · simpa [hresultTrie] using hfreshNode
      · have hchildSourceInv :=
          heapEntriesInvariant_childAt hentriesBase (pathStepIndex currentNode hash - 1)
            child hslot
        cases hchildSourceInv with
        | node hchildNodeBase hchildSlotsBase hchildBitmap hchildCount hchildEntries =>
            rename_i sourceChildNode sourceChildSlots
            have hchildNodeLt : child < base.nodes.length :=
              (List.getElem?_eq_some_iff.mp hchildNodeBase).1
            have hchildNodeInHeap : heap.nodes[child]? = some sourceChildNode :=
              (hframe.1 child hchildNodeLt).symm.trans hchildNodeBase
            have hchildNodeEq : childNode = sourceChildNode :=
              Option.some.inj (hchildNode.symm.trans hchildNodeInHeap)
            subst childNode
            have hchildDataLt : sourceChildNode.data < base.vectors.length :=
              (List.getElem?_eq_some_iff.mp hchildSlotsBase).1
            have hchildSlotsInHeap :
                heap.vectors[sourceChildNode.data]? = some sourceChildSlots :=
              (hframe.2 sourceChildNode.data hchildDataLt).symm.trans hchildSlotsBase
            have hchildSlotsEq : childSlots = sourceChildSlots :=
              Option.some.inj (hchildSlots.symm.trans hchildSlotsInHeap)
            have hparentDataLt : currentNode.data < heap.vectors.length :=
              (List.getElem?_eq_some_iff.mp hcopySlots').1
            have hparentDataNe : currentNode.data ≠ heap.vectors.length := by omega
            let childCopyNode : HAMTNode K V :=
              ⟨heap.vectors.length, sourceChildNode.bitmap⟩
            have hcopyNodeNew :
                heapAfter.nodes[heap.nodes.length]? = some childCopyNode := by
              rw [hheapEq]
              simp [pathCopyChildHeap, childCopyNode]
            have hcopySlotsNew :
                heapAfter.vectors[childCopyNode.data]? = some sourceChildSlots := by
              rw [hheapEq]
              simp [pathCopyChildHeap, childCopyNode, List.getElem?_set,
                List.getElem?_append, hparentDataNe, hchildSlotsEq]
            let parentHeap : HamtHeap K V := {heap with vectors := (heap.vectors.set
              currentNode.data (sourceSlots.set (pathStepIndex currentNode hash - 1)
                (some (.trie heap.nodes.length))))}
            have hparentFrame : HeapPrefixFrame base parentHeap :=
              heapPrefixFrame_vectorSet hframe currentNode.data _ hfreshData
            have hparentExtend : HeapLengthsExtend base parentHeap := by
              simpa [HeapLengthsExtend, parentHeap] using hextend
            have hsourceParentFrame : HeapPrefixFrame sourceBase parentHeap :=
              heapPrefixFrame_trans hbaseFrame hparentFrame hbaseExtend.1 hbaseExtend.2
            have hsourceParentExtend : HeapLengthsExtend sourceBase parentHeap :=
              ⟨Nat.le_trans hbaseExtend.1 hparentExtend.1,
                Nat.le_trans hbaseExtend.2 hparentExtend.2⟩
            have hparentAfterFrame : HeapPrefixFrame parentHeap heapAfter := by
              rw [hheapEq]
              constructor
              · intro i hi
                have hi' : i < heap.nodes.length := hi
                simp [parentHeap, pathCopyChildHeap, List.getElem?_append, hi']
              · intro i hi
                have hi' : i < heap.vectors.length := by simpa [parentHeap] using hi
                change (heap.vectors.set currentNode.data _)[i]? =
                  ((heap.vectors ++ [childSlots]).set currentNode.data _)[i]?
                simp only [List.getElem?_set]
                by_cases heq : currentNode.data = i
                · have hlarge : i < heap.vectors.length + 1 := by omega
                  simp [heq, hi', hlarge]
                · simp [heq, List.getElem?_append, hi']
            have hparentAfterExtend : HeapLengthsExtend parentHeap heapAfter := by
              rw [hheapEq]
              simp [HeapLengthsExtend, parentHeap, pathCopyChildHeap]
            have hchildParentInv : heapInvariant parentHeap child :=
              heapInvariant_prefixFrame hparentFrame
                (.node hchildNodeBase hchildSlotsBase hchildBitmap hchildCount hchildEntries)
            have hcopyChild : HamtNodeCopyOf parentHeap child heapAfter heap.nodes.length :=
              ⟨sourceChildNode, sourceChildSlots, childCopyNode,
                (hparentFrame.1 child hchildNodeLt).symm.trans hchildNodeBase,
                (hparentFrame.2 sourceChildNode.data hchildDataLt).symm.trans hchildSlotsBase,
                hcopyNodeNew, hcopySlotsNew, rfl,
                by simp [parentHeap], by simp [parentHeap, childCopyNode]⟩
            obtain ⟨finalTrie, finalHash, result, heapFinal, hrest, hframeFinal,
              hextendFinal, hchildMap, hchildInvariant, hchildContinue, htop, terminalNode, hterminalNode,
              hfreshTerminal, hfreshTerminalData⟩ :=
              ihEntries (pathStepIndex currentNode hash - 1) child hslot hchildParentInv
                hsourceParentFrame hsourceParentExtend hcopyChild
                hparentAfterFrame hparentAfterExtend (next ops hash)
            have hrest' : HamtLoopTrace (pathStepCopy same ops top) nextState heapAfter
                (finalTrie, finalHash, some result) heapFinal := by
              rw [hstate]
              exact hrest
            have hbaseFinalFrame : HeapPrefixFrame base heapFinal :=
              heapPrefixFrame_trans hparentFrame hframeFinal hparentExtend.1 hparentExtend.2
            have hbaseFinalExtend : HeapLengthsExtend base heapFinal :=
              ⟨Nat.le_trans hparentExtend.1 hextendFinal.1,
                Nat.le_trans hparentExtend.2 hextendFinal.2⟩
            have hcurrentLt : current < parentHeap.nodes.length := by
              simpa [parentHeap] using (List.getElem?_eq_some_iff.mp hcopyNode).1
            have hparentDataLt' : currentNode.data < parentHeap.vectors.length := by
              simpa [parentHeap] using hparentDataLt
            have hnodeFinal : heapFinal.nodes[current]? = some currentNode :=
              (hframeFinal.1 current hcurrentLt).symm.trans hcopyNode
            have hslotsParent : parentHeap.vectors[currentNode.data]? =
                some (sourceSlots.set (pathStepIndex currentNode hash - 1)
                  (some (.trie heap.nodes.length))) := by
              simp [parentHeap, List.getElem?_set_self hparentDataLt]
            have hslotsFinal := (hframeFinal.2 currentNode.data hparentDataLt').symm.trans hslotsParent
            have hchildMapBase : heapMap base child = heapMap heapFinal heap.nodes.length := by
              change readMap base child = readMap heapFinal heap.nodes.length
              exact (heapMap_prefixFrame base parentHeap child
                (.node hchildNodeBase hchildSlotsBase hchildBitmap hchildCount hchildEntries)
                hparentFrame).trans hchildMap
            have hmap : readMap base sourceTrie = readMap heapFinal current := by
              change heapMap base sourceTrie = heapMap heapFinal current
              simp only [heapMap.eq_1, hbaseSourceNode, hbaseSourceSlots,
                hnodeFinal, hslotsFinal]
              exact heapEntriesMap_replaceTrie hbaseFinalFrame hentriesBase
                (pathStepIndex currentNode hash - 1) child heap.nodes.length hslot hchildMapBase
            have hentriesFinal := heapEntriesInvariant_replaceTrie hbaseFinalFrame hentriesBase
              (pathStepIndex currentNode hash - 1) child heap.nodes.length hslot hchildInvariant
            have hcountFinal : countOnes 32 currentNode.bitmap =
                (sourceSlots.set (pathStepIndex currentNode hash - 1)
                  (some (.trie heap.nodes.length))).length := by
              simpa using hcopyCount
            have hinvariantFinal : heapInvariant heapFinal current :=
              .node hnodeFinal hslotsFinal hcopyBound hcountFinal hentriesFinal
            have hcontinue : FoundInsertionContinuation base heapFinal current result ops := by
              intro value inserted heapAfter hfound hinsert
              obtain ⟨hparentFrameAfter, hchildInvariantAfter⟩ :=
                hchildContinue value inserted heapAfter hfound hinsert
              have hbaseFrameAfter : HeapPrefixFrame base heapAfter :=
                heapPrefixFrame_trans hparentFrame hparentFrameAfter
                  hparentExtend.1 hparentExtend.2
              have hnodeAfter : heapAfter.nodes[current]? = some currentNode :=
                (hparentFrameAfter.1 current hcurrentLt).symm.trans hcopyNode
              have hslotsAfter := (hparentFrameAfter.2 currentNode.data hparentDataLt').symm.trans
                hslotsParent
              have hentriesAfter := heapEntriesInvariant_replaceTrie hbaseFrameAfter hentriesBase
                (pathStepIndex currentNode hash - 1) child heap.nodes.length hslot hchildInvariantAfter
              exact ⟨hbaseFrameAfter,
                .node hnodeAfter hslotsAfter hcopyBound hcountFinal hentriesAfter⟩
            exact ⟨finalTrie, finalHash, result, heapFinal,
              .yield hstep hrest', hbaseFinalFrame, hbaseFinalExtend, hmap, hinvariantFinal, hcontinue, htop,
              terminalNode, hterminalNode, Nat.le_trans hparentExtend.1 hfreshTerminal,
              Nat.le_trans hparentExtend.2 hfreshTerminalData⟩
    · intro i child hslot
      cases i <;> simp at hslot
    · intro leaf rest hrest ihRest i child hslot
      cases i with
      | zero => simp at hslot
      | succ i =>
          intro base heap current hinvBase hbaseFrame hbaseExtend hcopy hframe hextend hash
          exact ihRest i child (by simpa using hslot) hinvBase hbaseFrame hbaseExtend
            hcopy hframe hextend hash
    · intro storedChild rest hchild hrest ihChild ihRest i child hslot
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at hslot
          injection hslot with hslot
          injection hslot with hchildEq
          cases hchildEq
          intro base heap current hinvBase hbaseFrame hbaseExtend hcopy hframe hextend hash
          exact ihChild hinvBase hbaseFrame hbaseExtend hcopy hframe hextend hash
      | succ i =>
          intro base heap current hinvBase hbaseFrame hbaseExtend hcopy hframe hextend hash
          exact ihRest i child (by simpa using hslot) hinvBase hbaseFrame hbaseExtend
            hcopy hframe hextend hash
  intro base heap current hinvBase hbaseFrame hbaseExtend hcopy hframe hextend
  exact hrec hinvBase hbaseFrame hbaseExtend hcopy hframe hextend

private theorem pathCopyInitialRoot {K V : Type} {heap : HamtHeap K V}
    {trie : HAMT K V} (hinv : heapInvariant heap trie) :
    ∃ copy heapAfter,
      runHamt (readNode trie >>= fun node =>
        heapVectorOps.copy node.data >>= fun data =>
        HAMT.inner data node.bitmap) heap = (.ok copy, heapAfter) ∧
      HamtNodeCopyOf heap trie heapAfter copy ∧
      HeapPrefixFrame heap heapAfter ∧ HeapLengthsExtend heap heapAfter := by
  cases hinv with
  | node hnode hslots hbitmap hcount hentries =>
      rename_i node slots
      let data := heap.vectors.length
      let copy := heap.nodes.length
      let heapCopy : HamtHeap K V := { heap with vectors := heap.vectors ++ [slots] }
      let heapAfter : HamtHeap K V :=
        { heapCopy with nodes := heapCopy.nodes ++ [⟨data, node.bitmap⟩] }
      have hread : runHamt (readNode trie) heap = (.ok node, heap) := by
        simp [runHamt, readNode, hnode, MonadState.get, MonadStateOf.get,
          getThe, liftM, monadLift, MonadLift.monadLift, StateT.map, Functor.map,
          ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
          ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get,
          Bind.bind, Pure.pure]
      have hcopyRun : runHamt (heapVectorOps.copy node.data) heap =
          (.ok data, heapCopy) := by
        simpa [heapVectorOps, data, heapCopy] using
          heapVectorCopyRun heap node.data slots hslots
      have hinnerRun : runHamt (HAMT.inner data node.bitmap) heapCopy =
          (.ok copy, heapAfter) := by
        simpa [heapAfter, heapCopy, copy, data] using
          hamtInnerRun heapCopy data node.bitmap
      have hrootRun :
          runHamt (readNode trie >>= fun node =>
            heapVectorOps.copy node.data >>= fun data =>
            HAMT.inner data node.bitmap) heap = (.ok copy, heapAfter) := by
        rw [runHamtBindEq]
        simp only [hread]
        rw [runHamtBindEq]
        simp only [hcopyRun]
        exact hinnerRun
      have hframeCopy : HeapPrefixFrame heap heapCopy :=
        heapVectorAllocatePrefixFrame heap slots
      have hextendCopy : HeapLengthsExtend heap heapCopy := by
        constructor <;> simp [HeapLengthsExtend, heapCopy]
      have hframeAfter : HeapPrefixFrame heap heapAfter := by
        simpa [heapAfter, heapCopy] using
          heapPrefixFrame_nodeAppend hframeCopy hextendCopy ⟨data, node.bitmap⟩
      have hextendAfter : HeapLengthsExtend heap heapAfter := by
        constructor <;> simp [HeapLengthsExtend, heapAfter, heapCopy]
      have hcopyNode :
          heapAfter.nodes[copy]? = some (⟨data, node.bitmap⟩ : HAMTNode K V) := by
        simp [heapAfter, heapCopy, copy, data]
      have hcopySlots :
          heapAfter.vectors[data]? = some slots := by
        simp [heapAfter, heapCopy, data]
      refine ⟨copy, heapAfter, hrootRun, ?_, hframeAfter, hextendAfter⟩
      exact ⟨node, slots, ⟨data, node.bitmap⟩, hnode, hslots, hcopyNode,
        hcopySlots, rfl, by simp [copy], by simp [data]⟩

private theorem pathCopyLoopTraceFromRoot {K V : Type}
    (same : K → K → Bool) (ops : HamtObjectIdRuntime K) (heap : HamtHeap K V) :
    ∀ {trie : HAMT K V}, heapInvariant heap trie → ∀ hash : HashState K,
      ∃ copy heapAfter finalTrie finalHash result heapFinal,
        runHamt (readNode trie >>= fun node =>
          heapVectorOps.copy node.data >>= fun data =>
          HAMT.inner data node.bitmap) heap = (.ok copy, heapAfter) ∧
        HamtLoopTrace (pathStepCopy same ops copy)
          (copy, hash, none) heapAfter (finalTrie, finalHash, some result) heapFinal ∧
        HeapPrefixFrame heap heapFinal ∧ HeapLengthsExtend heap heapFinal := by
  intro trie hinv hash
  obtain ⟨copy, heapAfter, hroot, hcopy, hframe, hextend⟩ :=
    pathCopyInitialRoot hinv
  obtain ⟨finalTrie, finalHash, result, heapFinal, htrace, hframeFinal,
    hextendFinal⟩ :=
    (pathCopyLoopTraceWithFrame same ops heap copy hinv hcopy hframe hextend) hash
  exact ⟨copy, heapAfter, finalTrie, finalHash, result, heapFinal,
    hroot, htrace, hframeFinal, hextendFinal⟩

private theorem pathCopy_runOfTrace {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (trie : HAMT K V) (hash : HashState K)
    (heap : HamtHeap K V) (node : HAMTNode K V)
    (slots : List (Option (Entry K V))) (finalTrie : HAMT K V)
    (finalHash : HashState K) (result : PathResult K V) (heapFinal : HamtHeap K V)
    (hnode : heap.nodes[trie]? = some node)
    (hslots : heap.vectors[node.data]? = some slots)
    (trace : HamtLoopTrace (pathStepCopy same ops heap.nodes.length)
      (heap.nodes.length, hash, none)
      { heap with
        vectors := heap.vectors ++ [slots]
        nodes := heap.nodes ++ [⟨heap.vectors.length, node.bitmap⟩] }
      (finalTrie, finalHash, some result) heapFinal) :
    runHamt (path heapVectorOps same ops trie hash true) heap =
      (.ok result, heapFinal) := by
  rw [path.eq_1]
  simp only [↓reduceIte]
  let copyData := heap.vectors.length
  let heapCopy : HamtHeap K V := { heap with vectors := heap.vectors ++ [slots] }
  let heapWithTop : HamtHeap K V :=
    { heapCopy with nodes := heapCopy.nodes ++ [⟨copyData, node.bitmap⟩] }
  let top := heap.nodes.length
  have hread : runHamt (readNode trie) heap = (.ok node, heap) := by
    simp [runHamt, readNode, hnode, MonadState.get, MonadStateOf.get,
      getThe, liftM, monadLift, MonadLift.monadLift, StateT.map, Functor.map,
      ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get,
      Bind.bind, Pure.pure]
  have hcopyRun : runHamt (heapVectorOps.copy node.data) heap =
      (.ok copyData, heapCopy) := by
    simpa [heapVectorOps, copyData, heapCopy] using
      heapVectorCopyRun heap node.data slots hslots
  have hinnerRun : runHamt (HAMT.inner copyData node.bitmap) heapCopy =
      (.ok top, heapWithTop) := by
    simpa [heapWithTop, heapCopy, top, copyData] using
      hamtInnerRun heapCopy copyData node.bitmap
  have htraceBody : HamtLoopTrace (pathCopyForInBody same ops top)
      (top, hash, none) heapWithTop (finalTrie, finalHash, some result) heapFinal := by
    rw [pathCopyForInBody_eq_pathStepCopy]
    exact trace
  have hloop := classForInRunOfTrace (top, hash, none) heapWithTop
    (pathCopyForInBody same ops top) (finalTrie, finalHash, some result) heapFinal htraceBody
  rw [runHamtBindEq]
  simp only [hread]
  rw [runHamtBindEq]
  simp only [hcopyRun]
  rw [runHamtBindEq]
  simp only [hinnerRun]
  change runHamt
    ((forIn (m := HamtM K V)
      (β := HAMT K V × HashState K × Option (PathResult K V))
      ({} : Lean.Loop) (top, hash, none) (pathCopyForInBody same ops top)) >>= fun state =>
        match state.2.2 with
        | some value => pure value
        | none => throw HamtError.bounds) heapWithTop = _
  rw [runHamtBindEq]
  simp only [hloop]
  simp [runHamt, ExceptT.run, ExceptT.pure, ExceptT.mk,
    StateT.run, StateT.pure, Pure.pure]

private theorem pathCopy_readMapFresh {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap : HamtHeap K V) (trie : HAMT K V)
    (hash : HashState K) (hinv : heapInvariant heap trie) :
    ∃ result heapFinal,
      runHamt (path heapVectorOps same ops trie hash true) heap = (.ok result, heapFinal) ∧
      HeapPrefixFrame heap heapFinal ∧
      readMap heap trie = readMap heapFinal result.top ∧
      heapInvariant heapFinal result.top ∧
      FoundInsertionContinuation heap heapFinal result.top result ops ∧
      ∃ terminalNode, heapFinal.nodes[result.trie]? = some terminalNode ∧
        heap.nodes.length ≤ result.trie ∧ heap.vectors.length ≤ terminalNode.data := by
  cases hinv with
  | node hnode hslots hbitmap hcount hentries =>
      rename_i node slots
      have hinv : heapInvariant heap trie := .node hnode hslots hbitmap hcount hentries
      let copyHeap : HamtHeap K V := {heap with
        vectors := heap.vectors ++ [slots]
        nodes := heap.nodes ++ [⟨heap.vectors.length, node.bitmap⟩]}
      have hcopy : HamtNodeCopyOf heap trie copyHeap heap.nodes.length :=
        ⟨node, slots, ⟨heap.vectors.length, node.bitmap⟩, hnode, hslots,
          by simp [copyHeap], by simp [copyHeap], rfl, Nat.le_refl _, Nat.le_refl _⟩
      have hframe : HeapPrefixFrame heap copyHeap := by
        constructor
        · intro i hi
          simp [copyHeap, List.getElem?_append, hi]
        · intro i hi
          simp [copyHeap, List.getElem?_append, hi]
      have hextend : HeapLengthsExtend heap copyHeap := by
        simp [HeapLengthsExtend, copyHeap]
      have hrefl : HeapPrefixFrame heap heap := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      have hlength : HeapLengthsExtend heap heap := ⟨Nat.le_refl _, Nat.le_refl _⟩
      obtain ⟨finalTrie, finalHash, result, heapFinal, htrace, hframeFinal,
        hextendFinal, hmap, hinvariant, hcontinue, htop, hfresh⟩ :=
        pathCopyLoopTraceMap same ops heap heap.nodes.length hinv hinv hrefl hlength
          hcopy hframe hextend hash
      have hrun := pathCopy_runOfTrace same ops trie hash heap node slots
        finalTrie finalHash result heapFinal hnode hslots htrace
      exact ⟨result, heapFinal, hrun, hframeFinal, by simpa [htop] using hmap,
        by simpa [htop] using hinvariant, by simpa [htop] using hcontinue, hfresh⟩

theorem pathCopy_readMap {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap : HamtHeap K V) (trie : HAMT K V)
    (hash : HashState K) (hinv : heapInvariant heap trie) :
    ∃ result heapFinal,
      runHamt (path heapVectorOps same ops trie hash true) heap = (.ok result, heapFinal) ∧
      HeapPrefixFrame heap heapFinal ∧
      readMap heap trie = readMap heapFinal result.top := by
  obtain ⟨result, heapFinal, hrun, hframe, hmap, _, _, _⟩ :=
    pathCopy_readMapFresh same ops heap trie hash hinv
  exact ⟨result, heapFinal, hrun, hframe, hmap⟩

theorem pathCopy_runProperties {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap heapFinal : HamtHeap K V) (trie : HAMT K V)
    (hash : HashState K) (result : PathResult K V) (hinv : heapInvariant heap trie)
    (hrun : runHamt (path heapVectorOps same ops trie hash true) heap = (.ok result, heapFinal)) :
    HeapPrefixFrame heap heapFinal ∧
      readMap heap trie = readMap heapFinal result.top ∧
      heapInvariant heapFinal result.top ∧
      ∃ terminalNode, heapFinal.nodes[result.trie]? = some terminalNode ∧
        heap.nodes.length ≤ result.trie ∧ heap.vectors.length ≤ terminalNode.data := by
  obtain ⟨result', heapFinal', hrun', hframe, hmap, hinvariant, _, hfresh⟩ :=
    pathCopy_readMapFresh same ops heap trie hash hinv
  have heq := hrun'.symm.trans hrun
  have heqHeap : heapFinal' = heapFinal := congrArg Prod.snd heq
  have heqResult : result' = result := Except.ok.inj (congrArg Prod.fst heq)
  subst heapFinal'
  subst result'
  exact ⟨hframe, hmap, hinvariant, hfresh⟩

theorem pathCopy_insertFound_preservesOld {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap heap1 heap2 : HamtHeap K V)
    (trie : HAMT K V) (hash : HashState K) (value : V)
    (result : PathResult K V) (inserted : Option BITMAP) (before : List (K × V))
    (hinv : heapInvariant heap trie) (hread : readMap heap trie = some (.ok before))
    (hpath : runHamt (path heapVectorOps same ops trie hash true) heap = (.ok result, heap1))
    (hfound : result.found = true)
    (hinsert : runPartialHamt (insert! heapVectorOps ops result.found result.present result.trie
      result.index result.bi result.hash value) heap1 = some (.ok inserted, heap2)) :
    readMap heap2 trie = some (.ok before) := by
  obtain ⟨hframe, _, _, node, hnode, hfreshNode, hfreshData⟩ :=
    pathCopy_runProperties same ops heap heap1 trie hash result hinv hpath
  rw [hfound] at hinsert
  obtain ⟨slots, hslots, hlo, hhi⟩ :=
    insertFoundBounds heap1 heap2 ops result.trie result.index result.bi result.hash value
      result.present inserted node hnode hinsert
  have hframeAfter := insertFoundPrefixFrame heap heap1 heap2 ops result.trie result.index
    result.bi result.hash value result.present inserted node slots hframe hnode hslots
    hfreshNode hfreshData hlo hhi hinsert
  exact (heapMap_prefixFrame heap heap2 trie hinv hframeAfter).symm.trans hread

theorem pathCopy_preservesInvariant {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap heapFinal : HamtHeap K V) (trie : HAMT K V)
    (hash : HashState K) (result : PathResult K V) (hinv : heapInvariant heap trie)
    (hrun : runHamt (path heapVectorOps same ops trie hash true) heap = (.ok result, heapFinal)) :
    heapInvariant heapFinal result.top :=
  (pathCopy_runProperties same ops heap heapFinal trie hash result hinv hrun).2.2.1

theorem insertExisting_preservesInvariant {K V : Type}
    (heap heapAfter : HamtHeap K V) (ops : HamtObjectIdRuntime K)
    (root trie index : Nat) (bi : BitmapIndex) (hash : HashState K)
    (value : V) (inserted : Option BITMAP)
    (node : HAMTNode K V) (slots : List (Option (JuliaLean.base.hamt.Entry K V)))
    (oldLeaf : Leaf K V) (hinv : heapInvariant heap root)
    (hnode : heap.nodes[trie]? = some node) (hslots : heap.vectors[node.data]? = some slots)
    (hslot : slots[index - 1]? = some (some (.leaf oldLeaf)))
    (hbound : node.bitmap < 2 ^ 32) (hbit : Nat.testBit node.bitmap bi.x = true)
    (hrun : runPartialHamt (insert! heapVectorOps ops true true trie index bi hash value) heap =
      some (.ok inserted, heapAfter)) :
    heapInvariant heapAfter root := by
  obtain ⟨slots', hslots', hlo, hhi⟩ :=
    insertFoundBounds heap heapAfter ops trie index bi hash value true inserted node hnode hrun
  have heqSlots : slots' = slots := Option.some.inj (hslots'.symm.trans hslots)
  subst slots'
  have hmodel := insertExistingRunLocal heap ops trie index bi hash value node slots
    hnode hslots hlo (by simpa using hhi) hbound hbit
  have hheap := congrArg Prod.snd (Option.some.inj (hmodel.symm.trans hrun))
  dsimp only at hheap
  rw [← hheap]
  simpa [replaceEntryAt] using
    heapInvariant_replaceLeaf heap node.data (index - 1) slots oldLeaf
      ⟨hash.key, value⟩ hslots hslot hinv

theorem pathCopy_insertFound_preservesInvariant {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap heap1 heap2 : HamtHeap K V)
    (trie : HAMT K V) (hash : HashState K) (value : V)
    (result : PathResult K V) (inserted : Option BITMAP)
    (hinv : heapInvariant heap trie)
    (hpath : runHamt (path heapVectorOps same ops trie hash true) heap = (.ok result, heap1))
    (hfound : result.found = true)
    (hinsert : runPartialHamt (insert! heapVectorOps ops result.found result.present result.trie
      result.index result.bi result.hash value) heap1 = some (.ok inserted, heap2)) :
    heapInvariant heap2 result.top := by
  obtain ⟨result', heap1', hpath', _, _, _, hcontinue, _⟩ :=
    pathCopy_readMapFresh same ops heap trie hash hinv
  have heq := hpath'.symm.trans hpath
  have heqHeap : heap1' = heap1 := congrArg Prod.snd heq
  have heqResult : result' = result := Except.ok.inj (congrArg Prod.fst heq)
  subst heap1'
  subst result'
  exact (hcontinue value inserted heap2 hfound hinsert).2

theorem heapInvariant_readMap {K V : Type} (heap : HamtHeap K V) (trie : HAMT K V)
    (hinv : heapInvariant heap trie) :
    ∃ pairs, readMap heap trie = some (.ok pairs) := by
  let motiveNode : (trie : HAMT K V) → heapInvariant heap trie → Prop :=
    fun trie _ => ∃ pairs, heapMap heap trie = some (.ok pairs)
  let motiveEntries : (slots : List (Option (JuliaLean.base.hamt.Entry K V))) →
      heapEntriesInvariant heap slots → Prop :=
    fun slots _ => ∃ pairs, heapEntriesMap heap slots = some (.ok pairs)
  have hrec : motiveNode trie hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro current node slots hnode hslots hbitmap hcount hentries ihEntries
      obtain ⟨pairs, hmap⟩ := ihEntries
      refine ⟨pairs, ?_⟩
      simpa only [heapMap.eq_1, hnode, hslots] using hmap
    · exact ⟨[], heapEntriesMap.eq_1 _⟩
    · intro leaf rest hrest ihRest
      obtain ⟨pairs, hmap⟩ := ihRest
      refine ⟨(leaf.key, leaf.val) :: pairs, ?_⟩
      rw [heapEntriesMap.eq_3, hmap]
      rfl
    · intro child rest hchild hrest ihChild ihRest
      obtain ⟨childPairs, hchildMap⟩ := ihChild
      obtain ⟨restPairs, hrestMap⟩ := ihRest
      refine ⟨childPairs ++ restPairs, ?_⟩
      rw [heapEntriesMap.eq_4, hchildMap]
      rw [hrestMap]
      rfl
  exact hrec

private theorem pathLoopTraceWithReplacement {K V : Type}
    (same : K → K → Bool) (ops : HamtObjectIdRuntime K) (heap : HamtHeap K V)
    (top : HAMT K V) (value : V)
    (hreflexive : ∀ key, same key key = true) :
    ∀ {trie : HAMT K V}, heapInvariant heap trie → ∀ hash : HashState K,
      ∃ finalTrie finalHash result,
        HamtLoopTrace (pathStepNoCopy same ops top)
          (trie, hash, none) heap (finalTrie, finalHash, some result) heap ∧
        heapChildPath heap trie result.trie ∧
        (result.found = true → result.present = true →
          ∃ targetNode targetSlots targetIndex oldLeaf updatedHeap,
            heap.nodes[result.trie]? = some targetNode ∧
            heap.vectors[targetNode.data]? = some targetSlots ∧
            targetSlots[targetIndex]? = some (some (.leaf oldLeaf)) ∧
            result.hash = finalHash ∧ result.index = targetIndex + 1 ∧
            updatedHeap = {heap with vectors := (heap.vectors.set targetNode.data
              (targetSlots.set targetIndex (some (.leaf ⟨finalHash.key, value⟩))))} ∧
            HamtLoopTrace (pathStepNoCopy same ops top)
              (trie, hash, none) updatedHeap
              (finalTrie, finalHash, some result) updatedHeap) := by
  intro trie hinv hash
  let motiveNode : (trie : HAMT K V) → heapInvariant heap trie → Prop :=
    fun trie _ =>
      ∀ hash,
        ∃ finalTrie finalHash result,
          HamtLoopTrace (pathStepNoCopy same ops top)
            (trie, hash, none) heap (finalTrie, finalHash, some result) heap ∧
          heapChildPath heap trie result.trie ∧
          (result.found = true → result.present = true →
            ∃ targetNode targetSlots targetIndex oldLeaf updatedHeap,
              heap.nodes[result.trie]? = some targetNode ∧
              heap.vectors[targetNode.data]? = some targetSlots ∧
              targetSlots[targetIndex]? = some (some (.leaf oldLeaf)) ∧
              result.hash = finalHash ∧ result.index = targetIndex + 1 ∧
              updatedHeap = {heap with vectors := (heap.vectors.set targetNode.data
                (targetSlots.set targetIndex (some (.leaf ⟨finalHash.key, value⟩))))} ∧
              HamtLoopTrace (pathStepNoCopy same ops top)
                (trie, hash, none) updatedHeap
                (finalTrie, finalHash, some result) updatedHeap)
  let motiveEntries :
      (slots : List (Option (Entry K V))) →
        heapEntriesInvariant heap slots → Prop :=
    fun slots _ =>
      ∀ (i : Nat) (child : HAMT K V),
        slots[i]? = some (some (Entry.trie child)) →
      ∀ hash,
        ∃ finalTrie finalHash result,
          HamtLoopTrace (pathStepNoCopy same ops top)
            (child, hash, none) heap (finalTrie, finalHash, some result) heap ∧
          heapChildPath heap child result.trie ∧
          (result.found = true → result.present = true →
            ∃ targetNode targetSlots targetIndex oldLeaf updatedHeap,
              heap.nodes[result.trie]? = some targetNode ∧
              heap.vectors[targetNode.data]? = some targetSlots ∧
              targetSlots[targetIndex]? = some (some (.leaf oldLeaf)) ∧
              result.hash = finalHash ∧ result.index = targetIndex + 1 ∧
              updatedHeap = {heap with vectors := (heap.vectors.set targetNode.data
                (targetSlots.set targetIndex (some (.leaf ⟨finalHash.key, value⟩))))} ∧
              HamtLoopTrace (pathStepNoCopy same ops top)
                (child, hash, none) updatedHeap
                (finalTrie, finalHash, some result) updatedHeap)
  have hrec : motiveNode trie hinv := by
    refine heapInvariant.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hinv
    · intro trie node slots hnode hslots hbitmap hcount hentries ihEntries hash
      obtain ⟨nextState, hstep, hcase⟩ :=
        pathStepNoCopy_yields same ops heap top trie hash node slots
          hnode hslots hbitmap hcount hentries
      rcases hcase with ⟨result, hstate, hresultTrie, hdetail⟩ |
        ⟨child, hstate, hslot, hbit⟩
      · have hdone := pathStepNoCopy_done same ops top trie hash result heap
        have hrestTrace :
            HamtLoopTrace (pathStepNoCopy same ops top) nextState heap
              (trie, hash, some result) heap := by
          rw [hstate]
          exact .done hdone
        have htrace :
            HamtLoopTrace (pathStepNoCopy same ops top)
              (trie, hash, none) heap (trie, hash, some result) heap :=
          .yield hstep hrestTrace
        have hroute : heapChildPath heap trie result.trie := by
          rw [hresultTrie]
          exact .refl
        have hupdate :
            result.found = true → result.present = true →
              ∃ targetNode targetSlots targetIndex oldLeaf updatedHeap,
                heap.nodes[result.trie]? = some targetNode ∧
                heap.vectors[targetNode.data]? = some targetSlots ∧
                targetSlots[targetIndex]? = some (some (.leaf oldLeaf)) ∧
                result.hash = hash ∧ result.index = targetIndex + 1 ∧
                updatedHeap = {heap with vectors := (heap.vectors.set targetNode.data
                  (targetSlots.set targetIndex (some (.leaf ⟨hash.key, value⟩))))} ∧
                HamtLoopTrace (pathStepNoCopy same ops top)
                  (trie, hash, none) updatedHeap
                  (trie, hash, some result) updatedHeap := by
          intro hfound hpresent
          rcases hdetail with
            ⟨leaf, hresultEq, hslot, hbit⟩ | ⟨hempty, hbitFalse⟩
          · have hfoundOld : same leaf.key hash.key = true := by
              simpa [hresultEq] using hfound
            let targetIndex := pathStepIndex node hash - 1
            let newLeaf : Leaf K V := ⟨hash.key, value⟩
            let updatedHeap : HamtHeap K V :=
              {heap with vectors := (heap.vectors.set node.data
                (slots.set targetIndex (some (.leaf newLeaf))))}
            have htargetIndexLt : targetIndex < slots.length := by
              have hlt := (List.getElem?_eq_some_iff.mp hslot).1
              simpa [targetIndex] using hlt
            have hslotSet :
                (slots.set targetIndex (some (.leaf newLeaf)))[targetIndex]? =
                  some (some (.leaf newLeaf)) := by
              exact List.getElem?_set_self htargetIndexLt
            have hinvUpdated :
                heapInvariant updatedHeap trie := by
              simpa [updatedHeap, replaceEntryAt] using
                heapInvariant_replaceLeaf heap node.data targetIndex slots leaf newLeaf
                  hslots hslot (.node hnode hslots hbitmap hcount hentries)
            cases hinvUpdated with
            | node hnodeNew hslotsNew hbitmapNew hcountNew hentriesNew =>
              rename_i nodeNew slotsNew
              have hnodeNew' : heap.nodes[trie]? = some nodeNew := by
                simpa [updatedHeap] using hnodeNew
              have hnodeEq : nodeNew = node :=
                Option.some.inj (hnodeNew'.symm.trans hnode)
              subst nodeNew
              have hnodeDataLt : node.data < heap.vectors.length :=
                (List.getElem?_eq_some_iff.mp hslots).1
              have hslotsAt :
                  updatedHeap.vectors[node.data]? =
                    some (slots.set targetIndex (some (.leaf newLeaf))) := by
                simpa [updatedHeap, List.getElem?_set_self hnodeDataLt]
              have hslotsEq : slotsNew = slots.set targetIndex (some (.leaf newLeaf)) :=
                Option.some.inj (hslotsNew.symm.trans hslotsAt)
              subst slotsNew
              obtain ⟨nextStateNew, hstepNew, hshapeNew⟩ :=
                pathStepNoCopy_yields same ops updatedHeap top trie hash node
                  (slots.set targetIndex (some (.leaf newLeaf)))
                  hnodeNew hslotsNew hbitmapNew hcountNew hentriesNew
              rcases hshapeNew with
                ⟨resultNew, hstateNew, htrieNew, hdetailNew⟩ |
                ⟨childNew, hstateNew, hslotNew, hbitNew⟩
              · rcases hdetailNew with
                  ⟨newLeafObserved, hresultEqNew, hslotObserved, hbitObserved⟩ |
                  ⟨hresultEqNew, hbitFalseNew⟩
                · have hslotObservedAt :
                      (slots.set targetIndex (some (.leaf newLeaf)))[targetIndex]? =
                        some (some (.leaf newLeafObserved)) := by
                    simpa [targetIndex] using hslotObserved
                  have hleafEq : newLeafObserved = newLeaf := by
                    have hEq := hslotObservedAt.symm.trans hslotSet
                    have hOptionEq := Option.some.inj hEq
                    have hEntryEq := Option.some.inj hOptionEq
                    exact Entry.leaf.inj hEntryEq
                  have hresultNewEq : resultNew = result := by
                    calc
                      resultNew =
                          ⟨same newLeafObserved.key hash.key, true, trie,
                            pathStepIndex node hash, BitmapIndex.fromHash hash,
                            top, hash⟩ := hresultEqNew
                      _ =
                          ⟨same leaf.key hash.key, true, trie,
                            pathStepIndex node hash, BitmapIndex.fromHash hash,
                            top, hash⟩ := by
                              cases hleafEq
                              dsimp [newLeaf]
                              rw [hreflexive hash.key, hfoundOld]
                      _ = result := hresultEq.symm
                  have hstateNewEq :
                      nextStateNew = (trie, hash, some result) := by
                    rw [hstateNew, hresultNewEq]
                  have hnewRest :
                      HamtLoopTrace (pathStepNoCopy same ops top) nextStateNew
                        updatedHeap (trie, hash, some result) updatedHeap := by
                    rw [hstateNewEq]
                    exact .done
                      (pathStepNoCopy_done same ops top trie hash result updatedHeap)
                  have htraceNew :
                      HamtLoopTrace (pathStepNoCopy same ops top)
                        (trie, hash, none) updatedHeap
                        (trie, hash, some result) updatedHeap :=
                    .yield hstepNew hnewRest
                  refine ⟨node, slots, targetIndex, leaf, updatedHeap,
                    (by simpa [hresultTrie] using hnode), hslots,
                    (by simpa [targetIndex] using hslot),
                    (by rw [hresultEq]),
                    (by
                      have hpos : 1 ≤ pathStepIndex node hash := by
                        dsimp [pathStepIndex]
                        omega
                      rw [hresultEq]
                      simpa [targetIndex] using (Nat.sub_add_cancel hpos).symm),
                    rfl, htraceNew⟩
                · have hfalse : false = true := hbitFalseNew.symm.trans hbit
                  cases hfalse
              · have hslotNewAt :
                    (slots.set targetIndex (some (.leaf newLeaf)))[targetIndex]? =
                      some (some (Entry.trie childNew)) := by
                  simpa [targetIndex] using hslotNew
                rw [List.getElem?_set_self htargetIndexLt] at hslotNewAt
                have hentryEq : Entry.leaf newLeaf = Entry.trie childNew :=
                  Option.some.inj (Option.some.inj hslotNewAt)
                cases hentryEq
          · simp [hempty] at hpresent
        exact ⟨trie, hash, result, htrace, hroute, hupdate⟩
      · let i := pathStepIndex node hash - 1
        have hslot' : slots[i]? = some (some (Entry.trie child)) := by
          simpa [i] using hslot
        obtain ⟨finalTrie, finalHash, result, restTrace, restPath, hupdateRest⟩ :=
          ihEntries i child hslot' (next ops hash)
        have edge : heapChildEdge heap child trie :=
          ⟨node, slots, i, hnode, hslots, hslot'⟩
        have hrestTraceParent :
            HamtLoopTrace (pathStepNoCopy same ops top) nextState heap
              (finalTrie, finalHash, some result) heap := by
          rw [hstate]
          exact restTrace
        have htrace :
            HamtLoopTrace (pathStepNoCopy same ops top)
              (trie, hash, none) heap (finalTrie, finalHash, some result) heap :=
          .yield hstep hrestTraceParent
        have hroute : heapChildPath heap trie result.trie :=
          .step edge restPath
        have hupdate :
            result.found = true → result.present = true →
              ∃ targetNode targetSlots targetIndex oldLeaf updatedHeap,
                heap.nodes[result.trie]? = some targetNode ∧
                heap.vectors[targetNode.data]? = some targetSlots ∧
                targetSlots[targetIndex]? = some (some (.leaf oldLeaf)) ∧
                result.hash = finalHash ∧ result.index = targetIndex + 1 ∧
                updatedHeap = {heap with vectors := (heap.vectors.set targetNode.data
                  (targetSlots.set targetIndex
                    (some (.leaf ⟨finalHash.key, value⟩))))} ∧
                HamtLoopTrace (pathStepNoCopy same ops top)
                  (trie, hash, none) updatedHeap
                  (finalTrie, finalHash, some result) updatedHeap := by
          intro hfound hpresent
          obtain ⟨targetNode, targetSlots, targetIndex, oldLeaf, updatedHeap,
            htargetNode, htargetSlots, htargetEntry, hresultHash, hresultIndex,
            hheapEq, hrestUpdatedTrace⟩ :=
            hupdateRest hfound hpresent
          let newLeaf : Leaf K V := ⟨finalHash.key, value⟩
          have hplus : heapChildPathPlus heap trie result.trie :=
            heapChildPathPlus_of_edge heap edge restPath
          have hdataNe : node.data ≠ targetNode.data :=
            heapDataDiffAlongChildPath heap (.node hnode hslots hbitmap hcount hentries)
              hplus node targetNode hnode slots targetSlots hslots htargetNode htargetSlots
          have hinvUpdated0 :=
            heapInvariant_replaceLeaf heap targetNode.data targetIndex targetSlots
              oldLeaf newLeaf htargetSlots htargetEntry
              (.node hnode hslots hbitmap hcount hentries)
          have hinvUpdated : heapInvariant updatedHeap trie := by
            simpa [hheapEq, newLeaf, replaceEntryAt] using hinvUpdated0
          have hslotsUpdated :
              updatedHeap.vectors[node.data]? = some slots := by
            rw [hheapEq]
            have hframe := vectorLookupAfterSetOther heap targetNode.data node.data
              (targetSlots.set targetIndex (some (.leaf newLeaf))) hdataNe
            exact hframe.trans hslots
          cases hinvUpdated with
          | node hnodeNew hslotsNew hbitmapNew hcountNew hentriesNew =>
            rename_i nodeNew slotsNew
            have hnodeNew' : heap.nodes[trie]? = some nodeNew := by
              simpa [hheapEq] using hnodeNew
            have hnodeEq : nodeNew = node :=
              Option.some.inj (hnodeNew'.symm.trans hnode)
            subst nodeNew
            have hslotsEq : slotsNew = slots :=
              Option.some.inj (hslotsNew.symm.trans hslotsUpdated)
            subst slotsNew
            obtain ⟨nextStateNew, hstepNew, hshapeNew⟩ :=
              pathStepNoCopy_yields same ops updatedHeap top trie hash node slots
                hnodeNew hslotsNew hbitmapNew hcountNew hentriesNew
            rcases hshapeNew with
              ⟨resultNew, hstateNew, htrieNew, hdetailNew⟩ |
              ⟨childNew, hstateNew, hslotNew, hbitNew⟩
            · rcases hdetailNew with
                ⟨leafNew, hresultEqNew, hslotLeaf, hbitLeaf⟩ |
                ⟨hresultEqNew, hbitFalseNew⟩
              · have hslotLeafAt :
                    slots[pathStepIndex node hash - 1]? =
                      some (some (.leaf leafNew)) := by
                  simpa [hresultEqNew] using hslotLeaf
                have hslotClash :
                    some (some (Entry.trie child)) =
                      some (some (Entry.leaf leafNew)) :=
                  hslot.symm.trans hslotLeafAt
                have houter := Option.some.inj hslotClash
                have hinner := Option.some.inj houter
                cases hinner
              · have : false = true := hbitFalseNew.symm.trans hbit
                cases this
            · have hslotClash :
                  slots[pathStepIndex node hash - 1]? =
                    some (some (Entry.trie childNew)) := by
                simpa using hslotNew
              have hchildEq : childNew = child := by
                have hEq := hslot.symm.trans hslotClash
                have houter := Option.some.inj hEq
                have hinner := Option.some.inj houter
                exact (Entry.trie.inj hinner).symm
              have hstateNewEq :
                  nextStateNew = (child, next ops hash, none) := by
                rw [hstateNew, hchildEq]
              have hnewTrace :
                  HamtLoopTrace (pathStepNoCopy same ops top)
                    nextStateNew updatedHeap (finalTrie, finalHash, some result)
                    updatedHeap := by
                rw [hstateNewEq]
                exact hrestUpdatedTrace
              have htraceNew :
                  HamtLoopTrace (pathStepNoCopy same ops top)
                    (trie, hash, none) updatedHeap
                    (finalTrie, finalHash, some result) updatedHeap :=
                .yield hstepNew hnewTrace
              exact ⟨targetNode, targetSlots, targetIndex, oldLeaf, updatedHeap,
                htargetNode, htargetSlots, htargetEntry, hresultHash, hresultIndex,
                hheapEq, htraceNew⟩
        exact ⟨finalTrie, finalHash, result, htrace, hroute, hupdate⟩
    · intro i child hslot hash
      cases i <;> simp at hslot
    · intro leaf rest hrest ihRest i child hslot hash
      cases i with
      | zero => simp at hslot
      | succ i => exact ihRest i child (by simpa using hslot) hash
    · intro child rest hchild hrest ihChild ihRest i target hslot hash
      cases i with
      | zero =>
          have heq : child = target := by simpa using hslot
          subst target
          exact ihChild hash
      | succ i => exact ihRest i target (by simpa using hslot) hash
  exact hrec hash
theorem HamtInsertReplacesExisting_proven : HamtInsertReplacesExisting := by
  intro K V same ops heap heap1 heap2 trie key oldValue value before result inserted
  intro hlaw hinv hreadMap hunique hpath hfound hpresent hvalue hinsert
  obtain ⟨finalTrie, finalHash, pathResult, htrace, hroute, hupdate⟩ :=
    pathLoopTraceWithReplacement same ops heap trie value hlaw.1 hinv
      (HashState.fromKey ops key)
  have hpathTrace := pathNoCopy_runOfTrace same ops trie
    (HashState.fromKey ops key) heap finalTrie finalHash pathResult htrace
  have hpathEq : (Except.ok pathResult, heap) = (Except.ok result, heap1) :=
    hpathTrace.symm.trans hpath
  have hresultEq : pathResult = result := by
    have hresultOut := congrArg Prod.fst hpathEq
    injection hresultOut with hresultEq
  have hheap1Eq : heap = heap1 := congrArg Prod.snd hpathEq
  subst pathResult
  subst heap1
  obtain ⟨targetNode, targetSlots, targetIndex, oldLeaf, updatedHeap,
    htargetNode, htargetSlots, htargetEntry, hresultHash, hresultIndex,
    hheapEq, htraceUpdated⟩ := hupdate hfound hpresent
  obtain ⟨pathNode, pathSlots, oldLeafAtPath, hpathNode, hpathSlots,
    _hbiEq, _hpathIndex, _hpathSlot, hbit⟩ :=
    pathNoCopy_terminalLeaf same ops heap trie (HashState.fromKey ops key)
      hinv result hpath hpresent
  have hpathNodeEq : pathNode = targetNode :=
    Option.some.inj (hpathNode.symm.trans htargetNode)
  subst pathNode
  have hinvResult := heapInvariantAlongChildPath heap hinv hroute
  cases hinvResult with
  | node hnodeResult hslotsResult hbitmapResult hcountResult hentriesResult =>
      rename_i nodeResult slotsResult
      have hnodeResultEq : nodeResult = targetNode :=
        Option.some.inj (hnodeResult.symm.trans htargetNode)
      subst nodeResult
      have htargetIndexLt : targetIndex < targetSlots.length :=
        (List.getElem?_eq_some_iff.mp htargetEntry).1
      have hlo : 1 ≤ result.index := by
        rw [hresultIndex]
        omega
      have hhi : result.index ≤ targetSlots.length := by
        rw [hresultIndex]
        omega
      have hinsertModel := insertExistingRunLocal heap ops result.trie result.index
        result.bi result.hash value targetNode targetSlots htargetNode htargetSlots
        hlo hhi hbitmapResult hbit
      have hindexSub : result.index - 1 = targetIndex := by
        rw [hresultIndex]
        omega
      have hmodel :
          runPartialHamt (insert! heapVectorOps ops true true result.trie result.index
            result.bi result.hash value) heap =
              some (.ok (some targetNode.bitmap), updatedHeap) := by
        simpa [hheapEq, hindexSub, hresultHash] using hinsertModel
      have hactual := hinsert
      rw [hfound, hpresent] at hactual
      have hrunEq := hmodel.symm.trans hactual
      have hheap2Eq : heap2 = updatedHeap :=
        (congrArg Prod.snd (Option.some.inj hrunEq)).symm
      subst heap2
      have hslotsUpdated :
          updatedHeap.vectors[targetNode.data]? =
            some (targetSlots.set targetIndex
              (some (.leaf ⟨finalHash.key, value⟩))) := by
        rw [hheapEq]
        have hdataLt : targetNode.data < heap.vectors.length :=
          (List.getElem?_eq_some_iff.mp htargetSlots).1
        simp [List.getElem?_set_self hdataLt]
      have hnewSlot :
          (targetSlots.set targetIndex
            (some (.leaf ⟨finalHash.key, value⟩)))[result.index - 1]? =
              some (some (.leaf ⟨finalHash.key, value⟩)) := by
        rw [hindexSub]
        exact List.getElem?_set_self htargetIndexLt
      have hnodeUpdated : updatedHeap.nodes[result.trie]? = some targetNode := by
        rw [hheapEq]
        simpa using htargetNode
      have hreadNode :
          runHamt (readNode result.trie) updatedHeap = (.ok targetNode, updatedHeap) := by
        simp [runHamt, readNode, hnodeUpdated, MonadState.get, MonadStateOf.get,
          getThe, liftM, monadLift, MonadLift.monadLift, StateT.map, Functor.map,
          ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
          ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get,
          Bind.bind, Pure.pure]
      have hindexPositive : 0 < result.index := by
        rw [hresultIndex]
        omega
      have hindexNe : result.index ≠ 0 := Nat.ne_of_gt hindexPositive
      have hget :
          runHamt (heapVectorGet targetNode.data result.index) updatedHeap =
            (.ok (.leaf ⟨finalHash.key, value⟩), updatedHeap) := by
        simp [runHamt, heapVectorGet, heapVectorSlots, hslotsUpdated, hnewSlot,
          hindexNe, MonadState.get, MonadStateOf.get, getThe, liftM,
          monadLift, MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run,
          ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.lift,
          StateT.run, StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure]
      have hvalueUpdated :
          runHamt (PathResult.value? heapVectorOps result) updatedHeap =
            (.ok (some value), updatedHeap) := by
        dsimp [PathResult.value?]
        simp only [hfound, hpresent, Bool.true_and, if_true]
        rw [runHamtBindEq]
        rw [hreadNode]
        simp only
        dsimp [heapVectorOps]
        rw [runHamtBindEq, hget]
        simp [runHamt, ExceptT.pure, StateT.pure, StateT.run, Pure.pure]
      have hpathUpdated := pathNoCopy_runOfTrace same ops trie
        (HashState.fromKey ops key) updatedHeap finalTrie finalHash result htraceUpdated
      have houter : runHamt (do
          let pathResult ← path heapVectorOps same ops trie (HashState.fromKey ops key)
          PathResult.value? heapVectorOps pathResult) updatedHeap =
            (.ok (some value), updatedHeap) := by
        rw [runHamtBindEq, hpathUpdated]
        simp only
        exact hvalueUpdated
      unfold runPathValue
      rw [houter]

private theorem forInRunEquation {K V β : Type} (state : β)
    (step : Unit → β → HamtM K V (ForInStep β)) (heap : HamtHeap K V) :
    runHamt (Lean.Loop.forIn (m := HamtM K V) (β := β) ({} : Lean.Loop) state step) heap =
      match runHamt (step () state) heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok (.done result), heap') => (.ok result, heap')
      | (.ok (.yield next), heap') =>
          runHamt (Lean.Loop.forIn (m := HamtM K V) (β := β) ({} : Lean.Loop) next step) heap' := by
  cases h : runHamt (step () state) heap with
  | mk out heap' =>
    have hrunAction : StateT.run (ExceptT.run (step () state)) heap = (out, heap') := by
      simpa [runHamt] using h
    rw [Lean.Loop.forIn_eq_of_monadTail]
    unfold runHamt
    rw [ExceptT.run_bind]
    rw [StateT.run_bind]
    rw [hrunAction]
    cases out with
    | error error => rfl
    | ok stepResult =>
      cases stepResult with
      | done result => rfl
      | yield next => rfl

private def typedPairPathStep {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (top : HAMT K V) :
    Unit → (HAMT K V × HashState K × Option (PathResult K V)) →
      HamtM K V (ForInStep (HAMT K V × HashState K × Option (PathResult K V))) :=
  fun _ state => do
    let current := state.1
    let h := state.2.1
    let result := state.2.2
    if result.isNone then
      let bi := BitmapIndex.fromHash h
      let i ← entry_index current bi
      if ← isset current bi then
        let node ← readNode current
        match ← heapVectorOps.get node.data i with
        | .leaf leaf =>
            pure (ForInStep.yield
              (current, h, some ⟨same leaf.key h.key, true, current, i, bi, top, h⟩))
        | .trie child => pure (ForInStep.yield (child, next ops h, result))
      else
        pure (ForInStep.yield (current, h, some ⟨true, false, current, i, bi, top, h⟩))
    else pure (ForInStep.done (current, h, result))

private theorem typedPairRun {K V : Type} (ops : HamtObjectIdRuntime K) (key : K) (value : V) :
    runHamt (HAMT.typedPairConstructor heapVectorOps ops (key, value)) HamtHeap.empty =
      (.ok 0, { vectors := [[some (.leaf ⟨key, value⟩)]],
                nodes := [⟨0, u32 (2 ^ Nat.land (ops.objectid key).val.toNat LEVEL_MASK)⟩] }) := by
  simp_all [runHamt, HAMT.typedPairConstructor, init_hamt, HashState.fromKey,
    BitmapIndex.fromHash, set!, heapVectorOps, heapVectorAllocate, heapVectorSet,
    readNode, shiftLeftNat, shiftRightNat, HamtHeap.empty,
    MonadState.get, MonadStateOf.get, MonadStateOf.set,
    StateT.map, Functor.map, getThe, liftM,
    monadLift, MonadLift.monadLift, ExceptT.run, ExceptT.bind, ExceptT.pure,
    ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind,
    StateT.pure, StateT.get, StateT.set, Bind.bind, Pure.pure]

theorem HamtTypedPairSemantics_proven : HamtTypedPairSemantics := by
  intro K V same ops key value trie heap hlaw hrun
  have hself : same key key = true := hlaw.1 key
  have hresult := hrun.symm.trans (typedPairRun ops key value)
  rcases Prod.mk.inj hresult with ⟨htrie, hheap⟩
  have htrie' : trie = 0 := Except.ok.inj htrie
  subst trie
  subst heap
  let x := Nat.land (ops.objectid key).val.toNat LEVEL_MASK
  have hbi : x < 32 := by
    have hlevel : LEVEL_MASK < 2 ^ 5 := by simp [LEVEL_MASK]
    simpa [x] using Nat.and_lt_two_pow _ hlevel
  have hpow : 2 ^ x < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hbi
  have hu32 : u32 (2 ^ x) = 2 ^ x := by
    change (2 ^ x) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt hpow
  have hprefix : Nat.land (u32 (2 ^ x)) (shiftLeftNat 1 x - 1) = 0 := by
    rw [hu32]
    simp [shiftLeftNat, Nat.and_two_pow_sub_one_eq_mod]
  let heap0 : HamtHeap K V :=
    { vectors := [[some (.leaf ⟨key, value⟩)]]
      nodes := [⟨0, u32 (2 ^ x)⟩] }
  have hnode : heap0.nodes[0]? = some ⟨0, u32 (2 ^ x)⟩ := by
    simp [heap0]
  have hslots : heap0.vectors[0]? = some [some (.leaf ⟨key, value⟩)] := by
    simp [heap0]
  have hread : runHamt (readNode 0) heap0 =
      (.ok ⟨0, u32 (2 ^ x)⟩, heap0) := by
    simp [runHamt, readNode, hnode, MonadState.get, MonadStateOf.get,
      getThe, liftM, monadLift, MonadLift.monadLift, StateT.map,
      Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
      ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind, StateT.pure,
      StateT.get, Bind.bind, Pure.pure]
  have hdiv : 2 ^ x / 2 ^ x = 1 := Nat.div_self (Nat.pow_pos (by decide))
  have hset : runHamt (isset 0 ⟨x⟩) heap0 = (.ok true, heap0) := by
    simp [runHamt, isset, nodeBitmap, readNode, hnode, shiftRightNat,
      hu32, hdiv, MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
      MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run, ExceptT.bind,
      ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run,
      StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure]
  have hindex : runHamt (entry_index 0 ⟨x⟩) heap0 = (.ok 1, heap0) := by
    simp [runHamt, entry_index, nodeBitmap, readNode, hnode, shiftLeftNat,
      hu32, countOnes_zero, MonadState.get, MonadStateOf.get,
      getThe, liftM, monadLift, MonadLift.monadLift, StateT.map,
      Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
      ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind,
      StateT.pure, StateT.get, Bind.bind, Pure.pure]
  have hsetInline :
      runHamt (isset 0 (BitmapIndex.fromHash (HashState.fromKey ops key))) heap0 =
        (.ok true, heap0) := by
    simpa [HashState.fromKey, BitmapIndex.fromHash, shiftRightNat, x] using hset
  have hindexInline :
      runHamt (entry_index 0 (BitmapIndex.fromHash (HashState.fromKey ops key))) heap0 =
        (.ok 1, heap0) := by
    simpa [HashState.fromKey, BitmapIndex.fromHash, shiftRightNat, x] using hindex
  have hget : runHamt (heapVectorGet 0 1) heap0 =
      (.ok (.leaf ⟨key, value⟩), heap0) := by
    simp [runHamt, heapVectorGet, heapVectorSlots, hslots,
      MonadState.get, MonadStateOf.get, getThe, liftM, monadLift,
      MonadLift.monadLift, StateT.map, Functor.map, ExceptT.run,
      ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get,
      Bind.bind, Pure.pure]
  let pairHash := HashState.fromKey ops key
  let pairBi := BitmapIndex.fromHash pairHash
  let pairResult : PathResult K V := ⟨true, true, 0, 1, pairBi, 0, pairHash⟩
  have hstep :
      runHamt (typedPairPathStep same ops 0 () (0, pairHash, none)) heap0 =
        (.ok (.yield (0, pairHash, some pairResult)), heap0) := by
    dsimp [typedPairPathStep]
    rw [runHamtBindEq]
    rw [hindexInline]
    simp only
    rw [runHamtBindEq]
    rw [hsetInline]
    simp only
    simp only [ite_true]
    rw [runHamtBindEq]
    rw [hread]
    simp only
    dsimp [heapVectorOps]
    rw [runHamtBindEq]
    rw [hget]
    simp [runHamt, ExceptT.pure, StateT.pure, StateT.run, Pure.pure,
      hself, pairHash, pairBi, pairResult, HashState.fromKey,
      BitmapIndex.fromHash]
  have hstep2 :
      runHamt (typedPairPathStep same ops 0 () (0, pairHash, some pairResult)) heap0 =
        (.ok (.done (0, pairHash, some pairResult)), heap0) := by
    simp [runHamt, typedPairPathStep, pairHash, pairResult, ExceptT.pure,
      StateT.pure, StateT.run, Pure.pure]
  have hloop :
      runHamt (Lean.Loop.forIn (m := HamtM K V)
        (β := HAMT K V × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
        (0, pairHash, none) (typedPairPathStep same ops 0)) heap0 =
          (.ok (0, pairHash, some pairResult), heap0) := by
    rw [forInRunEquation, hstep]
    simp only
    exact forInRunEquation (0, pairHash, some pairResult)
      (typedPairPathStep same ops 0) heap0
  have hpath : runHamt (path heapVectorOps same ops 0 (HashState.fromKey ops key)) heap0 =
      (.ok ⟨true, true, 0, 1, BitmapIndex.fromHash (HashState.fromKey ops key), 0,
        HashState.fromKey ops key⟩, heap0) := by
    rw [path.eq_1]
    simp only [Bool.false_eq_true, ite_false]
    simp only [ForIn.forIn]
    change runHamt (do
      let final ← Lean.Loop.forIn (m := HamtM K V)
        (β := HAMT K V × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
        (0, HashState.fromKey ops key, none) (typedPairPathStep same ops 0)
      match final.2.2 with
      | some result => pure result
      | none => throw HamtError.bounds) heap0 = _
    rw [runHamtBindEq]
    rw [hloop]
    simp [runHamt, ExceptT.pure, StateT.pure, StateT.run, Pure.pure,
      pairHash, pairBi, pairResult, HashState.fromKey, BitmapIndex.fromHash]
  have hvalue : runHamt (PathResult.value? heapVectorOps pairResult) heap0 =
      (.ok (some value), heap0) := by
    dsimp [PathResult.value?, pairResult]
    rw [runHamtBindEq]
    rw [hread]
    simp only
    dsimp [heapVectorOps]
    rw [runHamtBindEq]
    rw [hget]
    simp [runHamt, ExceptT.pure, StateT.pure, StateT.run, Pure.pure]
  have houter : runHamt (do
      let result ← path heapVectorOps same ops 0 (HashState.fromKey ops key)
      PathResult.value? heapVectorOps result) heap0 =
      (.ok (some value), heap0) := by
    rw [runHamtBindEq]
    rw [hpath]
    simp only
    exact hvalue
  unfold runPathValue
  rw [houter]

theorem HamtConvertingPairSemantics_proven : HamtConvertingPairSemantics := by
  intro K V Q same ops convert input key value trie heap hconvert hlaw hrun
  exact HamtTypedPairSemantics_proven K V same ops key value trie heap hlaw
    (by simpa [HAMT.convertPair, hconvert] using hrun)

theorem HamtInferredPairSemantics_proven : HamtInferredPairSemantics := by
  intro K V same ops key value trie heap hlaw hrun
  exact HamtTypedPairSemantics_proven K V same ops key value trie heap hlaw
    (by simpa [HAMT.inferPair, HAMT.convertPair] using hrun)

set_option maxHeartbeats 200000

private theorem runHamtPureEq {K V A : Type} (value : A) (heap : HamtHeap K V) :
    runHamt (pure value : HamtM K V A) heap = (.ok value, heap) := Eq.trans rfl rfl

private theorem runHamtGetEq {K V : Type} (heap : HamtHeap K V) :
    runHamt (get : HamtM K V (HamtHeap K V)) heap = (.ok heap, heap) := Eq.trans rfl rfl

private theorem readNodeRunEq {K V : Type} (trie : Nat) (node : HAMTNode K V)
    (heap : HamtHeap K V) (hnode : heap.nodes[trie]? = some node) :
    runHamt (readNode trie) heap = (.ok node, heap) := by
  simp only [readNode, runHamtBindEq, runHamtGetEq, hnode, runHamtPureEq]

private theorem empty_vectorLengthRun {K V : Type} (heap : HamtHeap K V)
    (data : Nat) (slots : List (Option (Entry K V)))
    (hslots : heap.vectors[data]? = some slots) :
    runHamt (heapVectorOps.length data) heap = (.ok slots.length, heap) := by
  simp [runHamt, heapVectorOps, heapVectorLength, heapVectorSlots, hslots,
    MonadState.get, MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
    StateT.map, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get,
    Bind.bind, Pure.pure]

private theorem empty_vectorGetRun {K V : Type} (heap : HamtHeap K V)
    (data : Nat) (beforeSlots rest : List (Option (Entry K V))) (entry : Entry K V)
    (hslots : heap.vectors[data]? = some (beforeSlots ++ some entry :: rest)) :
    runHamt (heapVectorOps.get data (beforeSlots.length + 1)) heap = (.ok entry, heap) := by
  simp [runHamt, heapVectorOps, heapVectorGet, heapVectorSlots, hslots,
    MonadState.get, MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
    StateT.map, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get,
    Bind.bind, Pure.pure, List.getElem?_append]

private theorem empty_islevelRun {K V : Type} (heap : HamtHeap K V)
    (trie : HAMT K V) (node : HAMTNode K V) (hnode : heap.nodes[trie]? = some node) :
    runHamt (islevel_empty trie) heap = (.ok (node.bitmap == 0), heap) := by
  simp [runHamt, islevel_empty, nodeBitmap, readNode, hnode,
    MonadState.get, MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
    StateT.map, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get,
    Bind.bind, Pure.pure]

private theorem heapInvariant_emptyEvaluation {K V : Type} (heap : HamtHeap K V)
    (trie : HAMT K V) (hinv : heapInvariant heap trie) :
    ∃ pairs : List (K × V), heapMap heap trie = some (.ok pairs) ∧
      isemptyHAMT heapVectorOps trie heap = some (.ok pairs.isEmpty, heap) := by
  let nodeMotive : (trie : HAMT K V) → heapInvariant heap trie → Prop :=
    fun current _ => ∃ pairs : List (K × V),
      heapMap heap current = some (.ok pairs) ∧
        isemptyHAMT heapVectorOps current heap = some (.ok pairs.isEmpty, heap)
  let entriesMotive : (slots : List (Option (Entry K V))) →
      heapEntriesInvariant heap slots → Prop :=
    fun slots _ => ∃ pairs : List (K × V),
      heapEntriesMap heap slots = some (.ok pairs) ∧
        ∀ (data : Nat) (beforeSlots : List (Option (Entry K V))),
          heap.vectors[data]? = some (beforeSlots ++ slots) →
          isemptyEntries heapVectorOps data (beforeSlots.length + slots.length)
            (beforeSlots.length + 1) true heap = some (.ok pairs.isEmpty, heap)
  have result : nodeMotive trie hinv := by
    refine heapInvariant.rec (motive_1 := nodeMotive) (motive_2 := entriesMotive)
      ?_ ?_ ?_ ?_ hinv
    · intro current node slots hnode hslots hbitmap hcount hentries ihEntries
      obtain ⟨pairs, hmap, hloop⟩ := ihEntries
      refine ⟨pairs, ?_, ?_⟩
      · simpa only [heapMap.eq_1, hnode, hslots] using hmap
      · rw [isemptyHAMT.eq_1, empty_islevelRun heap current node hnode]
        by_cases hzero : node.bitmap = 0
        · have hlength : slots.length = 0 := by
            rw [← hcount, hzero]
            decide
          have hnil : slots = [] := by simpa using hlength
          subst slots
          rw [heapEntriesMap.eq_1] at hmap
          cases hmap
          simp [hzero]
        · have hfalse : (node.bitmap == 0) = false := by simp [hzero]
          rw [hfalse]
          dsimp only
          rw [readNodeRunEq current node heap hnode]
          dsimp only
          rw [empty_vectorLengthRun heap node.data slots hslots]
          simpa using hloop node.data [] hslots
    · refine ⟨[], ?_, ?_⟩
      · rw [heapEntriesMap.eq_1]
      · intro data beforeSlots hslots
        rw [isemptyEntries.eq_1]
        simp [show ¬ beforeSlots.length + 1 ≤ beforeSlots.length by omega]
    · intro leaf rest hrest ihRest
      obtain ⟨pairs, hmap, hloop⟩ := ihRest
      refine ⟨(leaf.key, leaf.val) :: pairs, ?_, ?_⟩
      · simp [heapEntriesMap.eq_3, hmap]
      · intro data beforeSlots hslots
        have hbound : beforeSlots.length + 1 ≤ beforeSlots.length + (some (.leaf leaf) :: rest).length := by
          simp
        rw [isemptyEntries.eq_1, if_pos (by simp [hbound]),
          empty_vectorGetRun heap data beforeSlots rest (.leaf leaf) hslots]
        change isemptyEntries heapVectorOps data _ _ false heap = some (.ok false, heap)
        rw [isemptyEntries.eq_1]
        simp
    · intro child rest hchild hrest ihChild ihRest
      obtain ⟨childPairs, hchildMap, hchildEmpty⟩ := ihChild
      obtain ⟨restPairs, hrestMap, hrestLoop⟩ := ihRest
      refine ⟨childPairs ++ restPairs, ?_, ?_⟩
      · simp [heapEntriesMap.eq_4, hchildMap, hrestMap]
      · intro data beforeSlots hslots
        have hbound : beforeSlots.length + 1 ≤ beforeSlots.length + (some (.trie child) :: rest).length := by
          simp
        rw [isemptyEntries.eq_1, if_pos (by simp [hbound]),
          empty_vectorGetRun heap data beforeSlots rest (.trie child) hslots]
        dsimp only
        rw [hchildEmpty]
        change isemptyEntries heapVectorOps data _ _ childPairs.isEmpty heap =
          some (.ok (childPairs ++ restPairs).isEmpty, heap)
        have hemptyAppend : (childPairs ++ restPairs).isEmpty =
            (childPairs.isEmpty && restPairs.isEmpty) := by
          cases childPairs <;> rfl
        cases hempty : childPairs.isEmpty with
        | false =>
            rw [isemptyEntries.eq_1]
            simp [hempty, hemptyAppend]
        | true =>
            have hslotsNext : heap.vectors[data]? =
                some ((beforeSlots ++ [some (.trie child)]) ++ rest) := by
              simpa [List.append_assoc] using hslots
            have hnext := hrestLoop data (beforeSlots ++ [some (.trie child)]) hslotsNext
            simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              hempty, hemptyAppend] using hnext
  exact result

theorem HamtEmptyExactlyNoLeaves_proven : HamtEmptyExactlyNoLeaves := by
  intro K V heap trie empty pairs hinv hread hrun
  obtain ⟨actual, hmap, hempty⟩ := heapInvariant_emptyEvaluation heap trie hinv
  have hpairs : actual = pairs :=
    Except.ok.inj (Option.some.inj (hmap.symm.trans hread))
  subst actual
  change isemptyHAMT heapVectorOps trie heap = some (.ok empty, heap) at hrun
  have hresult := congrArg Prod.fst (Option.some.inj (hrun.symm.trans hempty))
  refine ⟨Except.ok.inj hresult, ?_, ?_⟩
  · intro node hnode
    exact congrArg Prod.fst (empty_islevelRun heap trie node hnode)
  · intro leaf
    rfl

end JuliaLean.Proofs.base.hamt


namespace JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean JuliaLean.base.hamt JuliaLean.Proofs.base.hamt

set_option maxRecDepth 2000

private theorem hamtLitNatVal (n : Nat) (h : n < 2 ^ 62) :
    (JInt.lit .i64 (Int.ofNat n)).val = Int.ofNat n := by
  change wrapInt .i64 (Int.ofNat n) = Int.ofNat n
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (n : Int) ∧ (n : Int) ≤ 9223372036854775807
  omega

private theorem hamtAddSmall (n m : Nat) (h : n + m < 2 ^ 62) :
    JuliaLean.base.int.add (JInt.lit .i64 (Int.ofNat n))
      (JInt.lit .i64 (Int.ofNat m)) = JInt.lit .i64 (Int.ofNat (n + m)) := by
  have hn : n < 2 ^ 62 := by omega
  have hm : m < 2 ^ 62 := by omega
  unfold JuliaLean.base.int.add JuliaLean.base.int.add_int
  unfold JuliaLean.C.fromJInt JuliaLean.C.jlAddInt JuliaLean.C.toJInt
  rw [hamtLitNatVal n hn, hamtLitNatVal m hm, ← BitVec.ofInt_add]
  simp only [IntTy.signed, IntTy.bits, if_true]
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by change -9223372036854775808 ≤ (n : Int) + (m : Int); omega)
    (by change (n : Int) + (m : Int) < 9223372036854775808; omega)]
  rfl

private theorem hamtReadNodeRun {K V : Type} (heap : HamtHeap K V)
    (trie : Nat) (node : HAMTNode K V) (hnode : heap.nodes[trie]? = some node) :
    runHamt (readNode trie) heap = (.ok node, heap) := by
  simp only [readNode, runHamt, hnode, MonadState.get, MonadStateOf.get,
    getThe, liftM, monadLift, MonadLift.monadLift, StateT.map, Functor.map,
    ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
    ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get, Bind.bind, Pure.pure]

private theorem hamtVectorLengthRun {K V : Type} (heap : HamtHeap K V)
    (data : Nat) (slots : List (Option (Entry K V)))
    (hslots : heap.vectors[data]? = some slots) :
    runHamt (heapVectorOps.length data) heap = (.ok slots.length, heap) := by
  simp only [runHamt, heapVectorOps, heapVectorLength, heapVectorSlots, hslots,
    MonadState.get, MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
    StateT.map, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get,
    Bind.bind, Pure.pure]

private theorem hamtVectorGetRun {K V : Type} (heap : HamtHeap K V)
    (data : Nat) (beforeSlots rest : List (Option (Entry K V))) (entry : Entry K V)
    (hslots : heap.vectors[data]? = some (beforeSlots ++ some entry :: rest)) :
    runHamt (heapVectorOps.get data (beforeSlots.length + 1)) heap = (.ok entry, heap) := by
  simp [runHamt, heapVectorOps, heapVectorGet, heapVectorSlots, hslots,
    MonadState.get, MonadStateOf.get, getThe, liftM, monadLift, MonadLift.monadLift,
    StateT.map, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.get,
    Bind.bind, Pure.pure, List.getElem?_append]

private theorem hamtLengthEvaluation {K V : Type} (heap : HamtHeap K V)
    (trie : HAMT K V) (hinv : heapInvariant heap trie) :
    ∃ pairs : List (K × V), heapMap heap trie = some (.ok pairs) ∧
      (pairs.length < 2 ^ 62 →
        lengthHAMT heapVectorOps trie heap =
          some (.ok (JInt.lit .i64 (Int.ofNat pairs.length)), heap)) := by
  let nodeMotive : (trie : HAMT K V) → heapInvariant heap trie → Prop :=
    fun current _ => ∃ pairs : List (K × V),
      heapMap heap current = some (.ok pairs) ∧
        (pairs.length < 2 ^ 62 →
          lengthHAMT heapVectorOps current heap =
            some (.ok (JInt.lit .i64 (Int.ofNat pairs.length)), heap))
  let entriesMotive : (slots : List (Option (Entry K V))) →
      heapEntriesInvariant heap slots → Prop :=
    fun slots _ => ∃ pairs : List (K × V),
      heapEntriesMap heap slots = some (.ok pairs) ∧
        ∀ (data : Nat) (beforeSlots : List (Option (Entry K V))) (total : Nat),
          heap.vectors[data]? = some (beforeSlots ++ slots) →
          total + pairs.length < 2 ^ 62 →
          lengthEntries heapVectorOps data (beforeSlots.length + slots.length)
            (beforeSlots.length + 1) (JInt.lit .i64 (Int.ofNat total)) heap =
              some (.ok (JInt.lit .i64 (Int.ofNat (total + pairs.length))), heap)
  have result : nodeMotive trie hinv := by
    refine heapInvariant.rec (motive_1 := nodeMotive) (motive_2 := entriesMotive)
      ?_ ?_ ?_ ?_ hinv
    · intro current node slots hnode hslots hbitmap hcount hentries ihEntries
      obtain ⟨pairs, hmap, hloop⟩ := ihEntries
      refine ⟨pairs, ?_, ?_⟩
      · simpa only [heapMap.eq_1, hnode, hslots] using hmap
      · intro hbound
        rw [lengthHAMT.eq_1, hamtReadNodeRun heap current node hnode]
        dsimp only
        rw [hamtVectorLengthRun heap node.data slots hslots]
        have hzero : JInt.lit .i64 (Int.ofNat 0) = JInt.lit .i64 0 := rfl
        simpa only [List.nil_append, List.length_nil, Nat.zero_add, hzero] using
          hloop node.data [] 0 hslots (by simpa only [Nat.zero_add] using hbound)
    · refine ⟨[], ?_, ?_⟩
      · rw [heapEntriesMap.eq_1]
      · intro data beforeSlots total hslots hbound
        rw [lengthEntries.eq_1, if_neg (by simp only [List.length_nil, Nat.add_zero]; omega)]
        rfl
    · intro leaf rest hrest ihRest
      obtain ⟨pairs, hmap, hloop⟩ := ihRest
      refine ⟨(leaf.key, leaf.val) :: pairs, ?_, ?_⟩
      · rw [heapEntriesMap.eq_3, hmap]
        rfl
      · intro data beforeSlots total hslots hbound
        have hboundStep : beforeSlots.length + 1 ≤ beforeSlots.length +
            (some (.leaf leaf) :: rest).length := by simp only [List.length_cons]; omega
        rw [lengthEntries.eq_1, if_pos hboundStep,
          hamtVectorGetRun heap data beforeSlots rest (.leaf leaf) hslots]
        dsimp only [lengthLeaf]
        rw [hamtAddSmall total 1 (by simp only [List.length_cons] at hbound; omega)]
        have hslots' : heap.vectors[data]? =
            some ((beforeSlots ++ [some (.leaf leaf)]) ++ rest) := by
          simpa only [List.append_assoc, List.singleton_append] using hslots
        have hloop' := hloop data (beforeSlots ++ [some (.leaf leaf)]) (total + 1)
          hslots' (by simp only [List.length_cons] at hbound; omega)
        simpa only [List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1] using hloop'
    · intro child rest hchild hrest ihChild ihRest
      obtain ⟨childPairs, hchildMap, hchildLength⟩ := ihChild
      obtain ⟨restPairs, hrestMap, hrestLoop⟩ := ihRest
      refine ⟨childPairs ++ restPairs, ?_, ?_⟩
      · rw [heapEntriesMap.eq_4, hchildMap, hrestMap]
        rfl
      · intro data beforeSlots total hslots hbound
        have hboundStep : beforeSlots.length + 1 ≤ beforeSlots.length +
            (some (.trie child) :: rest).length := by simp only [List.length_cons]; omega
        rw [lengthEntries.eq_1, if_pos hboundStep,
          hamtVectorGetRun heap data beforeSlots rest (.trie child) hslots]
        dsimp only
        rw [hchildLength (by simp only [List.length_append] at hbound; omega)]
        simp only [Option.bind_some, Bind.bind]
        rw [hamtAddSmall total childPairs.length
          (by simp only [List.length_append] at hbound; omega)]
        have hslots' : heap.vectors[data]? =
            some ((beforeSlots ++ [some (.trie child)]) ++ rest) := by
          simpa only [List.append_assoc, List.singleton_append] using hslots
        have hloop' := hrestLoop data (beforeSlots ++ [some (.trie child)])
          (total + childPairs.length) hslots'
          (by simp only [List.length_append] at hbound; omega)
        simpa only [List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1] using hloop'
  exact result

/-- The bounded finite leaf sequence determines the exact native count. -/
theorem DictscovHamtL243 : JuliaLean.Proofs.base.hamt.Round4.HamtLengthCountsLeavesBounded := by
  intro K V heap trie length pairs hinv hmap hbound hrun
  obtain ⟨found, hfound, hlength⟩ := hamtLengthEvaluation heap trie hinv
  have hpairs : found = pairs := by
    exact Except.ok.inj (Option.some.inj (hfound.symm.trans hmap))
  subst found
  have heq := (hlength hbound).symm.trans hrun
  exact (Except.ok.inj (congrArg Prod.fst (Option.some.inj heq))).symm

end JuliaLean.ChatGPT.Batch4.Group24

namespace JuliaLean.Proofs.base.hamt

open JuliaLean.Registry
def entries : List Entry := [
  { id := "dictscov-hamt-l65", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT{K,V}(data, bitmap) where {K,V}"],
    statement := "The inner constructor shares the supplied mutable data vector, so later writes through that vector are visible through the constructed trie.",
    source := "invariant; base/hamt.jl:65", status := .proven, prop := ``HamtInnerSharesVector, thm := some ``HamtInnerSharesVector_proven },
  { id := "dictscov-hamt-l66", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT{K, V}() where {K, V}"],
    statement := "Each call allocates a distinct root with bitmap zero and a zero-length data vector; mutating one leaves the other root and vector unchanged.",
    source := "HAMT invariant; base/hamt.jl:66", status := .proven, prop := ``HamtEmptyAllocatesIndependently, thm := some ``HamtEmptyAllocatesIndependently_proven },
  { id := "dictscov-hamt-l76", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT{K,V}((k,v)::Pair{K,V}) where {K, V}", "path(trie::HAMT{K,V}, h::HashState, copy=false)"],
    statement := "With reflexive key identity and hashing consistent with identity, typed pair construction lets path resolve the supplied key to its value.",
    source := "HAMT invariant; base/hamt.jl:76-81", status := .proven, prop := ``HamtTypedPairSemantics, thm := some ``HamtTypedPairSemantics_proven },
  { id := "dictscov-hamt-l82", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT{K,V}(kv::Pair) where {K, V}", "path(trie::HAMT{K,V}, h::HashState, copy=false)"],
    statement := "With the same identity/hash law, converting pair construction lets path resolve the converted key to the converted value.",
    source := "constructor invariant; base/hamt.jl:82", status := .proven, prop := ``HamtConvertingPairSemantics, thm := some ``HamtConvertingPairSemantics_proven },
  { id := "dictscov-hamt-l84", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT(pair::Pair{K,V}) where {K, V}", "HAMT{K,V}((k,v)::Pair{K,V}) where {K, V}", "path"],
    statement := "The inferred pair constructor forwards to typed construction, which resolves the supplied key to its value under the identity/hash law.",
    source := "constructor invariant; base/hamt.jl:76-84", status := .proven, prop := ``HamtInferredPairSemantics, thm := some ``HamtInferredPairSemantics_proven },
  { id := "dictscov-hamt-l243", juliaFile := "base/hamt.jl",
    juliaFns := ["Base.length(::Leaf)", "Base.length(trie::HAMT)"],
    statement := "HAMT length returns the wrapping native integer count of leaves across every child node, regardless of tree depth.",
    source := "HAMT invariant; base/hamt.jl:243", status := .todo, prop := ``Round4.HamtLengthCountsLeaves, thm := none },
  { id := "dictscov-hamt-l246", juliaFile := "base/hamt.jl",
    juliaFns := ["Base.isempty(::Leaf)", "Base.isempty(trie::HAMT)", "islevel_empty(trie::HAMT)", "islevel_empty(::Leaf)"],
    statement := "For a valid HAMT, isempty is true exactly when its map has no pairs; islevel_empty is bitmap == 0, and islevel_empty(::Leaf) is false.",
    source := "HAMT invariant; base/hamt.jl:246-251", status := .proven, prop := ``HamtEmptyExactlyNoLeaves, thm := some ``HamtEmptyExactlyNoLeaves_proven },
  { id := "dictscov-hamt-l254", juliaFile := "base/hamt.jl",
    juliaFns := ["Base.iterate(trie::HAMT, state=nothing)"],
    statement := "Iteration yields the finite map’s leaf pairs exactly once in depth-first vector order and resumes after each returned pair.",
    source := "HAMT invariant; base/hamt.jl:253-275", status := .todo, prop := ``HamtIterationExact, thm := none, notes := "No complete exact proof returned. reduced the goal to equality with the unique successful finite leaf list (g13HamtIterationPairsIff and g13HamtReadMapHasUniquePairs); the remaining equality needs a recursion equation for the existing sealed partial iteratorSequence, which the fixed proof interface does not expose." },
]

end JuliaLean.Proofs.base.hamt

namespace JuliaLean.Proofs.base.hamt
open JuliaLean.base.hamt

private inductive CollisionFiniteTrace {S A E : Type} (step : S → Except E (Sum A S)) : S → A → Prop where
  | done {state result} (hstep : step state = .ok (.inl result)) :
      CollisionFiniteTrace step state result
  | next {state nextState result} (hstep : step state = .ok (.inr nextState))
      (rest : CollisionFiniteTrace step nextState result) : CollisionFiniteTrace step state result

private theorem successfulCollisionLoop_hasFiniteTrace {S A E : Type} (step : S → Except E (Sum A S)) :
    ∀ state result, JuliaLean.base.reduce.whileLoop step state = some (.ok result) → CollisionFiniteTrace step state result := by
  apply JuliaLean.base.reduce.whileLoop.fixpoint_induct step
    (fun loop => ∀ state result, loop state = some (.ok result) → CollisionFiniteTrace step state result)
  · refine Lean.Order.admissible_pi_apply
      (fun (state : S) (output : Option (Except E A)) => ∀ result, output = some (.ok result) →
        CollisionFiniteTrace step state result) ?_
    intro state
    exact Lean.Order.admissible_pi
      (fun (output : Option (Except E A)) (result : A) =>
        output = some (.ok result) → CollisionFiniteTrace step state result)
      (fun result => Lean.Order.Option.admissible_eq_some
        (CollisionFiniteTrace step state result) (Except.ok result : Except E A))
  · intro loop ih state result hrun
    cases hstep : step state with
    | error error => simp [hstep] at hrun
    | ok outcome =>
        cases outcome with
        | inl value =>
            have heq : value = result := by simpa [hstep] using hrun
            subst result
            exact .done hstep
        | inr nextState =>
            exact .next hstep (ih nextState result (by simpa [hstep] using hrun))


private theorem runHamtBind_success {K V A B : Type}
    (action : HamtM K V A) (next : A → HamtM K V B)
    (heap heapAfter : HamtHeap K V) (result : B)
    (hrun : runHamt (action >>= next) heap = (.ok result, heapAfter)) :
    ∃ value heap1, runHamt action heap = (.ok value, heap1) ∧
      runHamt (next value) heap1 = (.ok result, heapAfter) := by
  rw [runHamtBindEq] at hrun
  cases hfirst : runHamt action heap with
  | mk outcome heap1 =>
      rw [hfirst] at hrun
      cases outcome with
      | error error => cases hrun
      | ok value => exact ⟨value, heap1, rfl, hrun⟩

private theorem setBitmap_preservesFrame {K V : Type}
    (base heap heapAfter : HamtHeap K V) (trie : Nat)
    (node : HAMTNode K V) (bi : BitmapIndex) (bitmap : BITMAP)
    (hframe : HeapPrefixFrame base heap) (hlengths : HeapLengthsExtend base heap)
    (hnode : heap.nodes[trie]? = some node) (hfresh : base.nodes.length ≤ trie)
    (hrun : runHamt (set! trie bi) heap = (.ok bitmap, heapAfter)) :
    HeapPrefixFrame base heapAfter ∧ HeapLengthsExtend base heapAfter := by
  have hmodel := setRunLocal heap trie node bi hnode
  have hheap := congrArg Prod.snd (hmodel.symm.trans hrun)
  dsimp only at hheap
  rw [← hheap]
  constructor
  · exact heapPrefixFrame_nodeSet hframe trie _ hfresh
  · simpa only [HeapLengthsExtend, List.length_set] using hlengths

private theorem vectorSet_preservesFrame {K V : Type}
    (base heap heapAfter : HamtHeap K V) (data index : Nat)
    (entry : JuliaLean.base.hamt.Entry K V)
    (hframe : HeapPrefixFrame base heap) (hlengths : HeapLengthsExtend base heap)
    (hfresh : base.vectors.length ≤ data)
    (hrun : runHamt (heapVectorOps.set data index entry) heap = (.ok (), heapAfter)) :
    HeapPrefixFrame base heapAfter ∧ HeapLengthsExtend base heapAfter ∧
      heapAfter.nodes = heap.nodes := by
  cases hslots : heap.vectors[data]? with
  | none =>
      change (heapVectorSet data index entry).run heap = _ at hrun
      unfold heapVectorSet at hrun
      rw [runHamtBindLocal, runHamtGetLocal] at hrun
      simp [hslots, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
        ExceptT.lift, StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure,
        throw, throwThe, MonadExceptOf.throw] at hrun
      cases hrun
  | some slots =>
      by_cases hbad : index = 0 ∨ slots.length < index
      · change (heapVectorSet data index entry).run heap = _ at hrun
        unfold heapVectorSet at hrun
        rw [runHamtBindLocal, runHamtGetLocal] at hrun
        simp [hslots, hbad, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
          ExceptT.lift, StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure,
          throw, throwThe, MonadExceptOf.throw] at hrun
        cases hrun
      · have hmodel := heapVectorSetRunLocal heap data index entry slots hslots
          (by omega) (by omega)
        have hheap := congrArg Prod.snd (hmodel.symm.trans hrun)
        dsimp only at hheap
        rw [← hheap]
        refine ⟨heapPrefixFrame_vectorSet hframe data _ hfresh, ?_, rfl⟩
        simpa only [HeapLengthsExtend, List.length_set] using hlengths

private theorem vectorInsert_preservesFrame {K V : Type}
    (base heap heapAfter : HamtHeap K V) (data index : Nat)
    (entry : JuliaLean.base.hamt.Entry K V)
    (hframe : HeapPrefixFrame base heap) (hlengths : HeapLengthsExtend base heap)
    (hfresh : base.vectors.length ≤ data)
    (hrun : runHamt (heapVectorOps.insert data index entry) heap = (.ok (), heapAfter)) :
    HeapPrefixFrame base heapAfter ∧ HeapLengthsExtend base heapAfter ∧
      heapAfter.nodes = heap.nodes := by
  cases hslots : heap.vectors[data]? with
  | none =>
      change (heapVectorInsert data index entry).run heap = _ at hrun
      unfold heapVectorInsert at hrun
      rw [runHamtBindLocal, runHamtGetLocal] at hrun
      simp [hslots, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
        ExceptT.lift, StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure,
        throw, throwThe, MonadExceptOf.throw] at hrun
      cases hrun
  | some slots =>
      by_cases hbad : index = 0 ∨ slots.length + 1 < index
      · change (heapVectorInsert data index entry).run heap = _ at hrun
        unfold heapVectorInsert at hrun
        rw [runHamtBindLocal, runHamtGetLocal] at hrun
        simp [hslots, hbad, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
          ExceptT.lift, StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure,
          throw, throwThe, MonadExceptOf.throw] at hrun
        cases hrun
      · have hmodel := heapVectorInsertRunLocal heap data index entry slots hslots
          (by omega) (by omega)
        have hheap := congrArg Prod.snd (hmodel.symm.trans hrun)
        dsimp only at hheap
        rw [← hheap]
        refine ⟨heapPrefixFrame_vectorSet hframe data _ hfresh, ?_, rfl⟩
        simpa only [HeapLengthsExtend, List.length_set] using hlengths


private abbrev CollisionState (K : Type) :=
  HashState K × HashState K × Nat × BitmapIndex × Bool × Bool

private def CollisionInput (K V : Type) := CollisionState K × HamtHeap K V

private def CollisionInv {K V : Type} (base : HamtHeap K V) : CollisionInput K V → Prop
  | ((_, _, current, _, _, finished), heap) =>
      HeapPrefixFrame base heap ∧ HeapLengthsExtend base heap ∧
      (finished = false → ∃ node, heap.nodes[current]? = some node ∧
        base.nodes.length ≤ current ∧ base.vectors.length ≤ node.data)

private theorem collisionLoop_hasTrace {K V : Type}
    (body : CollisionInput K V → Except (HamtError × HamtHeap K V)
      (Sum (CollisionInput K V) (CollisionInput K V)))
    (initial : CollisionInput K V) (heapAfter : HamtHeap K V) (inserted : Option BITMAP)
    (hrun : (match JuliaLean.base.reduce.whileLoop body initial with
      | none => none
      | some (.error (error, finalHeap)) => some (.error error, finalHeap)
      | some (.ok (_, finalHeap)) => some (.ok none, finalHeap) :
        Option (Except HamtError (Option BITMAP) × HamtHeap K V)) =
        some (.ok inserted, heapAfter)) :
    ∃ finalState, CollisionFiniteTrace body initial (finalState, heapAfter) ∧ inserted = none := by
  cases hloop : JuliaLean.base.reduce.whileLoop body initial with
  | none => simp [hloop] at hrun
  | some outcome =>
      rw [hloop] at hrun
      cases outcome with
      | error errorHeap => cases hrun
      | ok final =>
          rcases final with ⟨finalState, finalHeap⟩
          have heq := Option.some.inj hrun
          have hheap : finalHeap = heapAfter := congrArg Prod.snd heq
          have hinserted : inserted = none := (Except.ok.inj (congrArg Prod.fst heq)).symm
          subst finalHeap
          exact ⟨finalState,
            successfulCollisionLoop_hasFiniteTrace body initial _ hloop, hinserted⟩

private theorem collisionTrace_preservesInvariant {K V : Type}
    (base : HamtHeap K V)
    (body : CollisionInput K V → Except (HamtError × HamtHeap K V)
      (Sum (CollisionInput K V) (CollisionInput K V)))
    (hsafe : ∀ input output, CollisionInv base input → body input = .ok output →
      match output with
      | .inl result => HeapPrefixFrame base result.2 ∧ HeapLengthsExtend base result.2
      | .inr next => CollisionInv base next)
    {initial final : CollisionInput K V}
    (trace : CollisionFiniteTrace body initial final) :
    CollisionInv base initial → HeapPrefixFrame base final.2 ∧ HeapLengthsExtend base final.2 := by
  induction trace with
  | done hstep =>
      intro hinv
      exact hsafe _ _ hinv hstep
  | next hstep rest ih =>
      intro hinv
      exact ih (hsafe _ _ hinv hstep)


private theorem runHamtThrowEq {K V A : Type} (error : HamtError) (heap : HamtHeap K V) :
    runHamt (throw error : HamtM K V A) heap = (.error error, heap) := Eq.trans rfl rfl


private theorem readNode_preservesHeap {K V : Type} (trie : Nat) (heap : HamtHeap K V) :
    (runHamt (readNode trie) heap).2 = heap := by
  unfold readNode
  simp only [runHamtBindEq, runHamtGetEq]
  cases heap.nodes[trie]? <;> simp [runHamtPureEq, runHamtThrowEq]

private theorem vectorGet_preservesHeap {K V : Type} (data index : Nat) (heap : HamtHeap K V) :
    (runHamt (heapVectorOps.get data index) heap).2 = heap := by
  change (runHamt (heapVectorGet data index) heap).2 = heap
  unfold heapVectorGet heapVectorSlots
  cases hslots : heap.vectors[data]? with
  | none => simp only [runHamtBindEq, runHamtGetEq, hslots, runHamtThrowEq]
  | some slots =>
      simp only [runHamtBindEq, runHamtGetEq, hslots, runHamtPureEq]
      by_cases hbad : index = 0
      · simp [hbad, runHamtBindEq, runHamtThrowEq]
      · simp only [hbad, ↓reduceIte]
        cases slots[index - 1]? with
        | none => simp [runHamtThrowEq]
        | some slot => cases slot <;> simp [runHamtThrowEq, runHamtPureEq]

private theorem runHamtBind_preservesHeap {K V A B : Type}
    (action : HamtM K V A) (next : A → HamtM K V B)
    (hfirst : ∀ heap, (runHamt action heap).2 = heap)
    (hnext : ∀ value heap, (runHamt (next value) heap).2 = heap)
    (heap : HamtHeap K V) : (runHamt (action >>= next) heap).2 = heap := by
  rw [runHamtBindEq]
  cases hrun : runHamt action heap with
  | mk outcome heap1 =>
      have hheap : heap1 = heap := by simpa only [hrun] using hfirst heap
      cases outcome with
      | error error => exact hheap
      | ok value => exact (hnext value heap1).trans hheap

private theorem nodeBitmap_preservesHeap {K V : Type} (trie : Nat) (heap : HamtHeap K V) :
    (runHamt (nodeBitmap trie) heap).2 = heap := by
  unfold nodeBitmap
  apply runHamtBind_preservesHeap _ _ (readNode_preservesHeap trie)
  intro value heap
  rw [runHamtPureEq]

private theorem nodeData_preservesHeap {K V : Type} (trie : Nat) (heap : HamtHeap K V) :
    (runHamt (nodeData trie) heap).2 = heap := by
  unfold nodeData
  apply runHamtBind_preservesHeap _ _ (readNode_preservesHeap trie)
  intro value heap
  rw [runHamtPureEq]

private theorem entryIndex_preservesHeap {K V : Type}
    (trie : Nat) (bi : BitmapIndex) (heap : HamtHeap K V) :
    (runHamt (entry_index trie bi) heap).2 = heap := by
  unfold entry_index
  apply runHamtBind_preservesHeap _ _ (nodeBitmap_preservesHeap trie)
  intro value heap
  rw [runHamtPureEq]


private theorem setBitmap_preservesOtherNode {K V : Type}
    (heap heapAfter : HamtHeap K V) (written read : Nat)
    (node : HAMTNode K V) (bi : BitmapIndex) (bitmap : BITMAP)
    (hnode : heap.nodes[written]? = some node) (hne : read ≠ written)
    (hrun : runHamt (set! written bi) heap = (.ok bitmap, heapAfter)) :
    heapAfter.nodes[read]? = heap.nodes[read]? := by
  have hmodel := setRunLocal heap written node bi hnode
  have hheap := congrArg Prod.snd (hmodel.symm.trans hrun)
  dsimp only at hheap
  rw [← hheap]
  simp [List.getElem?_set, hne, Ne.symm hne]

private theorem setBitmap_preservesData {K V : Type}
    (heap heapAfter : HamtHeap K V) (written : Nat)
    (node : HAMTNode K V) (bi : BitmapIndex) (bitmap : BITMAP)
    (hnode : heap.nodes[written]? = some node)
    (hrun : runHamt (set! written bi) heap = (.ok bitmap, heapAfter)) :
    ∃ nodeAfter, heapAfter.nodes[written]? = some nodeAfter ∧ nodeAfter.data = node.data := by
  have hmodel := setRunLocal heap written node bi hnode
  have hheap := congrArg Prod.snd (hmodel.symm.trans hrun)
  dsimp only at hheap
  rw [← hheap]
  refine ⟨{ node with bitmap := u32 (node.bitmap ||| shiftLeftNat 1 bi.x) }, ?_, rfl⟩
  exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp hnode).1

private theorem insertCollision_preservesFrame {K V : Type}
    (ops : HamtObjectIdRuntime K) (present : Bool) (trie index : Nat)
    (bi : BitmapIndex) (hash : HashState K) (value : V)
    (base heap heapAfter : HamtHeap K V) (inserted : Option BITMAP)
    (node : HAMTNode K V)
    (hframe : HeapPrefixFrame base heap) (hlengths : HeapLengthsExtend base heap)
    (hnode : heap.nodes[trie]? = some node)
    (hfreshNode : base.nodes.length ≤ trie) (hfreshData : base.vectors.length ≤ node.data)
    (hrun : runPartialHamt (insert! heapVectorOps ops false present trie index bi hash value) heap =
      some (.ok inserted, heapAfter)) :
    HeapPrefixFrame base heapAfter ∧ HeapLengthsExtend base heapAfter := by
  unfold runPartialHamt insert! at hrun
  simp only [Bool.false_eq_true, ite_false] at hrun
  split at hrun
  · cases hrun
  · rename_i leaf leafHash heap1 hprelude
    generalize hb : (fun (input : CollisionState K × HamtHeap K V) =>
      (_ : Except (HamtError × HamtHeap K V)
        (Sum (CollisionState K × HamtHeap K V) (CollisionState K × HamtHeap K V)))) = body at hrun
    have hex : ∃ finalState, CollisionFiniteTrace body
        ((hash, leafHash, trie, bi, present, false), heap1) (finalState, heapAfter) ∧
        inserted = none := by
      cases hloop : JuliaLean.base.reduce.whileLoop body
          ((hash, leafHash, trie, bi, present, false), heap1) with
      | none => rw [hloop] at hrun; cases hrun
      | some outcome =>
          rw [hloop] at hrun
          cases outcome with
          | error errorHeap => cases hrun
          | ok final =>
              rcases final with ⟨finalState, finalHeap⟩
              have heq := Option.some.inj hrun
              have hheap : finalHeap = heapAfter := congrArg Prod.snd heq
              have hinserted : inserted = none := (Except.ok.inj (congrArg Prod.fst heq)).symm
              subst finalHeap
              exact ⟨finalState, successfulCollisionLoop_hasFiniteTrace body _ _ hloop, hinserted⟩
    obtain ⟨finalState, htrace, hinserted⟩ := hex
    have hpreludeHeap : heap1 = heap := by
      cases present with
      | false =>
          simp only [Bool.not_false, ite_true, runHamtBindEq, runHamtThrowEq] at hprelude
          cases hprelude
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hprelude
          obtain ⟨readValue, readHeap, hread, hrest⟩ :=
            runHamtBind_success _ _ _ _ _ hprelude
          have hreadHeap : readHeap = heap := by
            simpa only [hread] using readNode_preservesHeap trie heap
          subst readHeap
          obtain ⟨entry, getHeap, hget, hrest⟩ :=
            runHamtBind_success _ _ _ _ _ hrest
          have hgetHeap : getHeap = heap := by
            simpa only [hget] using vectorGet_preservesHeap readValue.data index heap
          subst getHeap
          cases entry with
          | trie child =>
              simp only [runHamtBindEq, runHamtThrowEq] at hrest
              cases hrest
          | leaf leafValue =>
              simp only [runHamtBindEq, runHamtPureEq] at hrest
              split at hrest
              · simp only [runHamtBindEq, runHamtThrowEq] at hrest
                cases hrest
              · simpa only [runHamtPureEq] using (congrArg Prod.snd hrest).symm
    subst heap1
    have hinitial : CollisionInv base ((hash, leafHash, trie, bi, present, false), heap) :=
      ⟨hframe, hlengths, fun _ => ⟨node, hnode, hfreshNode, hfreshData⟩⟩
    apply collisionTrace_preservesInvariant base body ?_ htrace hinitial
    intro input output hinv hstep
    rw [← hb] at hstep
    rcases input with ⟨⟨h, oldHash, current, bitmap, isPresent, finished⟩, currentHeap⟩
    dsimp only [CollisionInv] at hinv
    cases finished with
    | true =>
        simp [runHamt, ExceptT.run, ExceptT.pure, ExceptT.mk, StateT.run,
          StateT.pure, Pure.pure] at hstep
        have hout := Except.ok.inj hstep
        rw [← hout]
        exact ⟨hinv.1, hinv.2.1⟩
    | false =>
        obtain ⟨currentNode, hcurrentNode, hfreshCurrent, hfreshCurrentData⟩ :=
          hinv.2.2 rfl
        simp only [Bool.false_eq_true, ite_false] at hstep
        generalize haction :
          runHamt (_ : HamtM K V (ForInStep (CollisionState K))) currentHeap = actionResult at hstep
        rcases actionResult with ⟨stepOutcome, stepHeap⟩
        cases stepOutcome with
        | error error => cases hstep
        | ok stepState =>
            obtain ⟨newTrie, allocHeap, halloc, hrest⟩ :=
              runHamtBind_success _ _ _ _ _ haction
            have hallocEq := (emptyHamtRun currentHeap).symm.trans halloc
            have hnewTrie := Except.ok.inj (congrArg Prod.fst hallocEq)
            have hallocHeap := congrArg Prod.snd hallocEq
            dsimp only at hallocHeap
            subst newTrie
            subst allocHeap
            obtain ⟨readValue, readHeap, hread, hrest⟩ :=
              runHamtBind_success _ _ _ _ _ hrest
            let allocated : HamtHeap K V :=
              { vectors := currentHeap.vectors ++ [[]],
                nodes := currentHeap.nodes ++ [⟨currentHeap.vectors.length, 0⟩] }
            change runHamt (readNode current) allocated = _ at hread
            have hcurrentLt : current < currentHeap.nodes.length :=
              (List.getElem?_eq_some_iff.mp hcurrentNode).1
            have hcurrentAlloc : allocated.nodes[current]? = some currentNode := by
              simpa [allocated, List.getElem?_append, hcurrentLt] using hcurrentNode
            have hreadEq := (readNodeRunEq current currentNode allocated hcurrentAlloc).symm.trans hread
            have hvalue := Except.ok.inj (congrArg Prod.fst hreadEq)
            have hheap := congrArg Prod.snd hreadEq
            dsimp only at hheap
            subst readValue
            subst readHeap
            have hallocFrame : HeapPrefixFrame base allocated := by
              exact heapPrefixFrame_nodeAppend
                (heapPrefixFrame_trans hinv.1 (heapVectorAllocatePrefixFrame currentHeap [])
                  hinv.2.1.1 hinv.2.1.2)
                (heapLengthsExtend_vectorAppend hinv.2.1 []) _
            have hallocLengths : HeapLengthsExtend base allocated :=
              heapLengthsExtend_nodeAppend (heapLengthsExtend_vectorAppend hinv.2.1 []) _
            cases isPresent <;>
              simp only [Bool.false_eq_true, ite_false, ite_true] at hrest
            all_goals
              obtain ⟨slot, slotHeap, hslot, hrest⟩ :=
                runHamtBind_success _ _ _ _ _ hrest
              have hslotHeap : slotHeap = allocated := by
                first
                | simpa only [hslot] using entryIndex_preservesHeap current bitmap allocated
                | simpa only [runHamtPureEq] using (congrArg Prod.snd hslot).symm
              subst slotHeap
              obtain ⟨unit, writeHeap, hwrite, hrest⟩ :=
                runHamtBind_success _ _ _ _ _ hrest
              cases unit
              have hwriteFacts : HeapPrefixFrame base writeHeap ∧ HeapLengthsExtend base writeHeap ∧
                  writeHeap.nodes = allocated.nodes := by
                first
                | exact vectorSet_preservesFrame base allocated writeHeap _ _ _ hallocFrame
                    hallocLengths hfreshCurrentData hwrite
                | exact vectorInsert_preservesFrame base allocated writeHeap _ _ _ hallocFrame
                    hallocLengths hfreshCurrentData hwrite
              have hcurrentWrite : writeHeap.nodes[current]? = some currentNode := by
                rw [hwriteFacts.2.2]
                exact hcurrentAlloc
              obtain ⟨newBitmap, parentHeap, hparent, hrest⟩ :=
                runHamtBind_success _ _ _ _ _ hrest
              have hparentFacts := setBitmap_preservesFrame base writeHeap parentHeap current
                currentNode bitmap newBitmap hwriteFacts.1 hwriteFacts.2.1 hcurrentWrite
                hfreshCurrent hparent
              have hnewWrite : writeHeap.nodes[currentHeap.nodes.length]? =
                  some ⟨currentHeap.vectors.length, 0⟩ := by
                rw [hwriteFacts.2.2]
                simp [allocated, List.getElem?_append]
              have hnewParent : parentHeap.nodes[currentHeap.nodes.length]? =
                  some ⟨currentHeap.vectors.length, 0⟩ := by
                rw [setBitmap_preservesOtherNode writeHeap parentHeap current _
                  currentNode bitmap newBitmap hcurrentWrite (by omega) hparent]
                exact hnewWrite
              split at hrest
              · simp only [runHamtPureEq] at hrest
                cases hrest
                dsimp only at hstep
                have hout := Except.ok.inj hstep
                rw [← hout]
                refine ⟨hparentFacts.1, hparentFacts.2, ?_⟩
                intro _
                exact ⟨_, hnewParent, hinv.2.1.1, hinv.2.1.2⟩
              · obtain ⟨newData, dataHeap, hdata, hrest⟩ :=
                  runHamtBind_success _ _ _ _ _ hrest
                have hdataHeap : dataHeap = parentHeap := by
                  simpa only [hdata] using nodeData_preservesHeap currentHeap.nodes.length parentHeap
                subst dataHeap
                have hdataModel : runHamt (nodeData currentHeap.nodes.length) parentHeap =
                    (.ok currentHeap.vectors.length, parentHeap) := by
                  simp only [nodeData, runHamtBindEq, readNodeRunEq _ _ _ hnewParent, runHamtPureEq]
                have hnewData := Except.ok.inj (congrArg Prod.fst (hdataModel.symm.trans hdata))
                subst newData
                obtain ⟨indexNew, indexHeap, hindexNew, hrest⟩ :=
                  runHamtBind_success _ _ _ _ _ hrest
                have hindexHeap : indexHeap = parentHeap := by
                  simpa only [hindexNew] using
                    entryIndex_preservesHeap currentHeap.nodes.length (BitmapIndex.fromHash (next ops h)) parentHeap
                subst indexHeap
                obtain ⟨unitNew, leafHeap, hleaf, hrest⟩ :=
                  runHamtBind_success _ _ _ _ _ hrest
                cases unitNew
                have hleafFacts := vectorInsert_preservesFrame base parentHeap leafHeap
                  currentHeap.vectors.length indexNew _ hparentFacts.1 hparentFacts.2
                  hinv.2.1.2 hleaf
                have hleafNode : leafHeap.nodes[currentHeap.nodes.length]? =
                    some ⟨currentHeap.vectors.length, 0⟩ := by
                  rw [hleafFacts.2.2]
                  exact hnewParent
                obtain ⟨bitmapNew, newSetHeap, hsetNew, hrest⟩ :=
                  runHamtBind_success _ _ _ _ _ hrest
                have hnewSetFacts := setBitmap_preservesFrame base leafHeap newSetHeap
                  currentHeap.nodes.length _ (BitmapIndex.fromHash (next ops h)) bitmapNew
                  hleafFacts.1 hleafFacts.2.1 hleafNode hinv.2.1.1 hsetNew
                obtain ⟨newNode, hnewNode, hnewNodeData⟩ :=
                  setBitmap_preservesData leafHeap newSetHeap currentHeap.nodes.length _
                    (BitmapIndex.fromHash (next ops h)) bitmapNew hleafNode hsetNew
                obtain ⟨indexOld, oldIndexHeap, hindexOld, hrest⟩ :=
                  runHamtBind_success _ _ _ _ _ hrest
                have holdIndexHeap : oldIndexHeap = newSetHeap := by
                  simpa only [hindexOld] using
                    entryIndex_preservesHeap currentHeap.nodes.length (BitmapIndex.fromHash (next ops oldHash)) newSetHeap
                subst oldIndexHeap
                obtain ⟨unitOld, oldLeafHeap, holdLeaf, hrest⟩ :=
                  runHamtBind_success _ _ _ _ _ hrest
                cases unitOld
                have holdLeafFacts := vectorInsert_preservesFrame base newSetHeap oldLeafHeap
                  currentHeap.vectors.length indexOld _ hnewSetFacts.1 hnewSetFacts.2
                  hinv.2.1.2 holdLeaf
                have holdLeafNode : oldLeafHeap.nodes[currentHeap.nodes.length]? = some newNode := by
                  rw [holdLeafFacts.2.2]
                  exact hnewNode
                obtain ⟨bitmapOld, oldSetHeap, hsetOld, hrest⟩ :=
                  runHamtBind_success _ _ _ _ _ hrest
                have holdSetFacts := setBitmap_preservesFrame base oldLeafHeap oldSetHeap
                  currentHeap.nodes.length newNode (BitmapIndex.fromHash (next ops oldHash)) bitmapOld
                  holdLeafFacts.1 holdLeafFacts.2.1 holdLeafNode hinv.2.1.1 hsetOld
                simp only [runHamtPureEq] at hrest
                cases hrest
                dsimp only at hstep
                have hout := Except.ok.inj hstep
                rw [← hout]
                refine ⟨holdSetFacts.1, holdSetFacts.2, ?_⟩
                intro hfalse
                cases hfalse

private theorem heapPrefixFrame_lengths {K V : Type} {base heap : HamtHeap K V}
    (hframe : HeapPrefixFrame base heap) : HeapLengthsExtend base heap := by
  constructor
  · by_cases h : base.nodes.length ≤ heap.nodes.length
    · exact h
    exfalso
    have hi : heap.nodes.length < base.nodes.length := by omega
    have heq := hframe.1 heap.nodes.length hi
    have hnone : base.nodes[heap.nodes.length]? = none := by simpa using heq
    have := List.getElem?_eq_none_iff.mp hnone
    omega
  · by_cases h : base.vectors.length ≤ heap.vectors.length
    · exact h
    exfalso
    have hi : heap.vectors.length < base.vectors.length := by omega
    have heq := hframe.2 heap.vectors.length hi
    have hnone : base.vectors[heap.vectors.length]? = none := by simpa using heq
    have := List.getElem?_eq_none_iff.mp hnone
    omega

theorem pathCopy_insert_preservesOld {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap heap1 heap2 : HamtHeap K V)
    (trie : HAMT K V) (hash : HashState K) (value : V)
    (result : PathResult K V) (inserted : Option BITMAP) (before : List (K × V))
    (hinv : heapInvariant heap trie) (hread : readMap heap trie = some (.ok before))
    (hpath : runHamt (path heapVectorOps same ops trie hash true) heap = (.ok result, heap1))
    (hinsert : runPartialHamt (insert! heapVectorOps ops result.found result.present result.trie
      result.index result.bi result.hash value) heap1 = some (.ok inserted, heap2)) :
    readMap heap2 trie = some (.ok before) := by
  cases hfound : result.found with
  | true =>
      exact pathCopy_insertFound_preservesOld same ops heap heap1 heap2 trie hash value
        result inserted before hinv hread hpath hfound hinsert
  | false =>
      obtain ⟨hframe, _, _, node, hnode, hfreshNode, hfreshData⟩ :=
        pathCopy_runProperties same ops heap heap1 trie hash result hinv hpath
      rw [hfound] at hinsert
      have hframeAfter := insertCollision_preservesFrame ops result.present result.trie
        result.index result.bi result.hash value heap heap1 heap2 inserted node hframe
        (heapPrefixFrame_lengths hframe) hnode hfreshNode hfreshData hinsert
      exact (heapMap_prefixFrame heap heap2 trie hinv hframeAfter.1).symm.trans hread

theorem persistentInsert_preservesOld {K V : Type} (same : K → K → Bool)
    (ops : HamtObjectIdRuntime K) (heap heapAfter : HamtHeap K V)
    (trie updated : HAMT K V) (key : K) (value : V) (before : List (K × V))
    (hinv : heapInvariant heap trie) (hread : readMap heap trie = some (.ok before))
    (hrun : runPartialHamt (persistentInsert heapVectorOps same ops trie key value) heap =
      some (.ok updated, heapAfter)) :
    readMap heapAfter trie = some (.ok before) := by
  unfold runPartialHamt persistentInsert at hrun
  cases hpath : runHamt (path heapVectorOps same ops trie (HashState.fromKey ops key) true) heap with
  | mk outcome heap1 =>
      rw [hpath] at hrun
      cases outcome with
      | error error => cases hrun
      | ok result =>
          dsimp only at hrun
          cases hinsert : insert! heapVectorOps ops result.found result.present result.trie
              result.index result.bi result.hash value heap1 with
          | none => rw [hinsert] at hrun; cases hrun
          | some outcome =>
              rw [hinsert] at hrun
              rcases outcome with ⟨outcome, heap2⟩
              cases outcome with
              | error error => cases hrun
              | ok inserted =>
                  have hheap : heap2 = heapAfter := congrArg Prod.snd (Option.some.inj hrun)
                  subst heap2
                  exact pathCopy_insert_preservesOld same ops heap heap1 heapAfter trie
                    (HashState.fromKey ops key) value result inserted before hinv hread hpath hinsert

end JuliaLean.Proofs.base.hamt

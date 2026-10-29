import JuliaLean.base.hamt
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.hamt

open JuliaLean.Registry JuliaLean.base.hamt

/-! Finite maps are read from the explicit mutable heap. `HashingLawful` captures
    reflexive identity and the objectid/hash consistency used by Julia’s `===`. -/

def HashingLawful (same : K → K → Bool) (ops : HashFunctions K) : Prop :=
  (∀ key, same key key = true) ∧
  (∀ a b, same a b = true → same b a = true) ∧
  (∀ a b c, same a b = true → same b c = true → same a c = true) ∧
  (∀ a b, same a b = true → ops.objectid a = ops.objectid b ∧
    ∀ seed, ops.hash (ops.objectid a) seed = ops.hash (ops.objectid b) seed)

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
  partial def heapMap (heap : HamtHeap K V) (trie : HAMT K V) : Except HamtError (List (K × V)) := do
    let node ← match heap.nodes[trie]? with
      | some node => pure node
      | none => throw .bounds
    let slots ← match heap.vectors[node.data]? with
      | some slots => pure slots
      | none => throw .bounds
    heapEntriesMap heap slots

  partial def heapEntriesMap (heap : HamtHeap K V) : List (Option (Entry K V)) → Except HamtError (List (K × V))
    | [] => pure []
    | none :: _ => throw .undefinedReference
    | some (.leaf leaf) :: rest => do
        let pairs ← heapEntriesMap heap rest
        pure ((leaf.key, leaf.val) :: pairs)
    | some (.trie child) :: rest => do
        let childPairs ← heapMap heap child
        let restPairs ← heapEntriesMap heap rest
        pure (childPairs ++ restPairs)
end

def readMap (heap : HamtHeap K V) (trie : HAMT K V) : Except HamtError (List (K × V)) :=
  heapMap heap trie

def runPathValue (same : K → K → Bool) (ops : HashFunctions K)
    (heap : HamtHeap K V) (trie : HAMT K V) (key : K) : Option V :=
  let (outcome, _) := runHamt (do
    let result ← path heapVectorOps same ops trie (HashState.fromKey ops key)
    PathResult.value? heapVectorOps result) heap
  match outcome with
  | .ok (some value) => some value
  | _ => none

mutual
  partial def heapInvariant (heap : HamtHeap K V) (trie : HAMT K V) : Prop :=
    match heap.nodes[trie]? with
    | none => False
    | some node =>
        match heap.vectors[node.data]? with
        | none => False
        | some slots => node.bitmap < 2 ^ 32 ∧
            countOnes 32 node.bitmap = slots.length ∧ heapEntriesInvariant heap slots

  partial def heapEntriesInvariant (heap : HamtHeap K V) : List (Option (Entry K V)) → Prop
    | [] => True
    | none :: _ => False
    | some (.leaf _) :: rest => heapEntriesInvariant heap rest
    | some (.trie child) :: rest => heapInvariant heap child ∧ heapEntriesInvariant heap rest
end

def advanceHash (ops : HashFunctions K) : Nat → HashState K → HashState K
  | 0, state => state
  | n + 1, state => advanceHash ops n (next ops state)

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
      trie1 ≠ trie2 ∧ readMap heap2 trie1 = .ok [(key1, value1)] ∧
        readMap heap2 trie2 = .ok [(key2, value2)] ∧
        ∃ n1 n2 slots1 slots2,
          heap2.nodes[trie1]? = some n1 ∧ n1.bitmap = 0 ∧
          heap2.vectors[n1.data]? = some slots1 ∧ slots1.length = 1 ∧
          slots1 = [some (.leaf ⟨key1, value1⟩)] ∧
          heap2.nodes[trie2]? = some n2 ∧ n2.bitmap = 0 ∧
          heap2.vectors[n2.data]? = some slots2 ∧ slots2.length = 1 ∧
          slots2 = [some (.leaf ⟨key2, value2⟩)] ∧
          n1.data ≠ n2.data

def HamtTypedPairSemantics : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HashFunctions K)
    (key : K) (value : V) (trie : HAMT K V) (heap : HamtHeap K V),
    HashingLawful same ops →
    runHamt (HAMT.typedPairConstructor heapVectorOps ops (key, value)) HamtHeap.empty = (.ok trie, heap) →
      runPathValue same ops heap trie key = some value

def HamtConvertingPairSemantics : Prop :=
  ∀ (K V Q : Type) (same : K → K → Bool) (ops : HashFunctions K)
    (convert : Q → K × V) (input : Q) (key : K) (value : V)
    (trie : HAMT K V) (heap : HamtHeap K V),
    convert input = (key, value) → HashingLawful same ops →
    runHamt (HAMT.convertPair heapVectorOps ops convert input) HamtHeap.empty = (.ok trie, heap) →
      runPathValue same ops heap trie key = some value

def HamtInferredPairSemantics : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HashFunctions K)
    (key : K) (value : V) (trie : HAMT K V) (heap : HamtHeap K V),
    HashingLawful same ops →
    runHamt (HAMT.inferPair heapVectorOps ops (key, value)) HamtHeap.empty = (.ok trie, heap) →
      runPathValue same ops heap trie key = some value

def HamtDepthAlignment : Prop :=
  ∀ (K Q : Type) (ops : HashFunctions K) (other : HashState Q) (key : K),
    let state := HashState.fromOtherAtDepth ops other key
    state.key = key ∧ state.depth = other.depth

def HamtHashProgress : Prop :=
  ∀ (K : Type) (ops : HashFunctions K) (key : K),
    let initial := HashState.fromKey ops key
    let state := advanceHash ops 12 initial
    initial.hash = ops.objectid key ∧ initial.shift = 0 ∧
      (∀ n, n ≤ 11 →
        let level := advanceHash ops n initial
        level.depth = n ∧ level.shift = n * BITS_PER_LEVEL ∧ level.hash = initial.hash) ∧
      state.depth = 12 ∧ state.shift = 0 ∧
        state.hash = ops.hash (ops.objectid key) (JInt.wrap .u64 2)

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
  ∀ (K V : Type) (same : K → K → Bool) (ops : HashFunctions K)
    (heap heap1 heap2 : HamtHeap K V) (trie : HAMT K V) (key : K) (value : V)
    (result : PathResult K V) (inserted : Option BITMAP) (before after : List (K × V)),
    HashingLawful same ops → heapInvariant heap trie → readMap heap trie = .ok before →
    finiteMapUnique same before →
    runHamt (path heapVectorOps same ops trie (HashState.fromKey ops key) true) heap = (.ok result, heap1) →
    runHamt (insert! heapVectorOps ops result.found result.present result.trie
      result.index result.bi result.hash value) heap1 = (.ok inserted, heap2) →
      readMap heap2 trie = .ok before ∧ readMap heap2 result.top = .ok after ∧
        finiteLookup same key after = some value

def HamtInsertMapLaws : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HashFunctions K)
    (heap heap' : HamtHeap K V) (trie updated : HAMT K V) (key : K) (value : V)
    (before after : List (K × V)),
    HashingLawful same ops → heapInvariant heap trie → readMap heap trie = .ok before →
    finiteMapUnique same before →
    runHamt (persistentInsert heapVectorOps same ops trie key value) heap = (.ok updated, heap') →
    readMap heap' updated = .ok after →
      finiteLookup same key after = some value ∧
        (∀ other, same other key = false →
          finiteLookup same other after = finiteLookup same other before)

def HamtCopyOnWritePreservesOld : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HashFunctions K)
    (heap heap' : HamtHeap K V) (trie updated : HAMT K V) (key : K) (value : V)
    (before after : List (K × V)),
    HashingLawful same ops → heapInvariant heap trie → readMap heap trie = .ok before →
    finiteMapUnique same before →
    runHamt (persistentInsert heapVectorOps same ops trie key value) heap = (.ok updated, heap') →
    readMap heap' updated = .ok after →
      readMap heap' trie = .ok before ∧ finiteLookup same key after = some value ∧
        (∀ other, same other key = false →
          finiteLookup same other after = finiteLookup same other before)

def HamtInsertReplacesExisting : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HashFunctions K)
    (heap heap1 heap2 : HamtHeap K V) (trie : HAMT K V) (key : K) (oldValue value : V)
    (before : List (K × V)) (result : PathResult K V) (inserted : Option BITMAP),
    HashingLawful same ops → heapInvariant heap trie → readMap heap trie = .ok before →
    finiteMapUnique same before →
    runHamt (path heapVectorOps same ops trie (HashState.fromKey ops key)) heap = (.ok result, heap1) →
    result.found = true → result.present = true →
    (runHamt (PathResult.value? heapVectorOps result) heap1).1 = .ok (some oldValue) →
    runHamt (insert! heapVectorOps ops result.found result.present result.trie
      result.index result.bi result.hash value) heap1 = (.ok inserted, heap2) →
      runPathValue same ops heap2 trie key = some value

def HamtInsertCollisionGrowth : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HashFunctions K)
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
    heapInvariant heap trie → readMap heap trie = .ok before →
    finiteLookup same existingKey before = some oldValue →
    finiteMapUnique same before →
    runPathValue same ops heap trie existingKey = some oldValue →
    runPathValue same ops heap trie key = none →
    runHamt (persistentInsert heapVectorOps same ops trie key value) heap = (.ok updated, heap') →
    readMap heap' updated = .ok after →
      finiteLookup same existingKey after = some oldValue ∧
        finiteLookup same key after = some value

def HamtInsertPreservesBitmapInvariant : Prop :=
  ∀ (K V : Type) (same : K → K → Bool) (ops : HashFunctions K)
    (heap heap' : HamtHeap K V) (trie updated : HAMT K V) (key : K) (value : V),
    HashingLawful same ops → heapInvariant heap trie →
    runHamt (persistentInsert heapVectorOps same ops trie key value) heap = (.ok updated, heap') →
      heapInvariant heap' updated

def HamtLengthCountsLeaves : Prop :=
  ∀ (K V : Type) (heap : HamtHeap K V) (trie : HAMT K V)
    (length : Nat) (pairs : List (K × V)),
    heapInvariant heap trie → readMap heap trie = .ok pairs →
    runHamt (lengthHAMT heapVectorOps trie) heap = (.ok length, heap) → length = pairs.length

def HamtEmptyExactlyNoLeaves : Prop :=
  ∀ (K V : Type) (heap : HamtHeap K V) (trie : HAMT K V)
    (empty : Bool) (pairs : List (K × V)),
    heapInvariant heap trie → readMap heap trie = .ok pairs →
    runHamt (isemptyHAMT heapVectorOps trie) heap = (.ok empty, heap) →
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
    heapInvariant heap trie → iteratorSequence heap trie = readMap heap trie

/-! Nothing to promise: HashState(other::HashState,key)@101 forwards to the typed alignment constructor.
Nothing to promise: Base.:(<<)(v,bi::BitmapIndex)@124 and Base.:(>>)(v,bi::BitmapIndex)@125 forward to generic bit-shift operators. -/



def entries : List Entry := [
  { id := "memsafety-hamt-entry-index", juliaFile := "base/hamt.jl",
    juliaFns := ["path", "insert!", "entry_index", "BitmapIndex(h::HashState)", "isset(trie::HAMT,bi::BitmapIndex)"],
    statement := "For a valid HAMT and present bitmap bit, entry_index is one plus the set-bit count below the bit and lies within the one-based data-vector bounds.",
    source := "HAMT bitmap/data-length invariant at base/hamt.jl:127-140", status := .todo, prop := ``HamtSlotRank, thm := none },
  { id := "dictscov-hamt-l65", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT{K,V}(data, bitmap) where {K,V}"],
    statement := "The inner constructor shares the supplied mutable data vector, so later writes through that vector are visible through the constructed trie.",
    source := "invariant; base/hamt.jl:65", status := .todo, prop := ``HamtInnerSharesVector, thm := none },
  { id := "dictscov-hamt-l66", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT{K, V}() where {K, V}"],
    statement := "Each call allocates a distinct root with bitmap zero and a zero-length data vector; mutating one leaves the other root and vector unchanged.",
    source := "HAMT invariant; base/hamt.jl:66", status := .todo, prop := ``HamtEmptyAllocatesIndependently, thm := none },
  { id := "dictscov-hamt-l69", juliaFile := "base/hamt.jl",
    juliaFns := ["init_hamt(K, V, k, v)"],
    statement := "Each init_hamt call allocates an isolated one-slot data vector with bitmap zero; its slot stores Leaf(k, v) directly.",
    source := "HAMT invariant; base/hamt.jl:69-74", status := .todo, prop := ``HamtInitSingleIsolated, thm := none },
  { id := "dictscov-hamt-l76", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT{K,V}((k,v)::Pair{K,V}) where {K, V}", "path(trie::HAMT{K,V}, h::HashState, copy=false)"],
    statement := "With reflexive key identity and hashing consistent with identity, typed pair construction lets path resolve the supplied key to its value.",
    source := "HAMT invariant; base/hamt.jl:76-81", status := .todo, prop := ``HamtTypedPairSemantics, thm := none },
  { id := "dictscov-hamt-l82", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT{K,V}(kv::Pair) where {K, V}", "path(trie::HAMT{K,V}, h::HashState, copy=false)"],
    statement := "With the same identity/hash law, converting pair construction lets path resolve the converted key to the converted value.",
    source := "constructor invariant; base/hamt.jl:82", status := .todo, prop := ``HamtConvertingPairSemantics, thm := none },
  { id := "dictscov-hamt-l84", juliaFile := "base/hamt.jl",
    juliaFns := ["HAMT(pair::Pair{K,V}) where {K, V}", "HAMT{K,V}((k,v)::Pair{K,V}) where {K, V}", "path"],
    statement := "The inferred pair constructor forwards to typed construction, which resolves the supplied key to its value under the identity/hash law.",
    source := "constructor invariant; base/hamt.jl:76-84", status := .todo, prop := ``HamtInferredPairSemantics, thm := none },
  { id := "dictscov-hamt-l94", juliaFile := "base/hamt.jl",
    juliaFns := ["HashState{K}(@nospecialize(other::HashState), @nospecialize(key)) where {K}"],
    statement := "The depth-aligned HashState constructor preserves the requested key and advances exactly to the other state’s depth.",
    source := "invariant; base/hamt.jl:94-100", status := .todo, prop := ``HamtDepthAlignment, thm := none },
  { id := "dictscov-hamt-l103", juliaFile := "base/hamt.jl",
    juliaFns := ["HashState(key)", "next(h::HashState{K}) where {K}"],
    statement := "The initial state uses objectid(key); repeated next steps advance five-bit chunks, preserve the original hash through shift 55, then rehash when the next shift exceeds 55.",
    source := "HAMT invariant; base/hamt.jl:103-117", status := .todo, prop := ``HamtHashProgress, thm := none },
  { id := "dictscov-hamt-l128", juliaFile := "base/hamt.jl",
    juliaFns := ["set!(trie::HAMT, bi::BitmapIndex)"],
    statement := "After insertion adds a child to data, set! restores bitmap population equal to vector length and preserves all other bits.",
    source := "HAMT invariant; base/hamt.jl:128-131", status := .todo, prop := ``HamtSetBitmapInvariant, thm := none },
  { id := "dictscov-hamt-l133", juliaFile := "base/hamt.jl",
    juliaFns := ["unset!(trie::HAMT, bi::BitmapIndex)"],
    statement := "After removal deletes a child from data, unset! restores bitmap population equal to vector length and preserves all other bits.",
    source := "HAMT invariant; base/hamt.jl:133-136", status := .todo, prop := ``HamtUnsetBitmapInvariant, thm := none },
  { id := "dictscov-hamt-l138", juliaFile := "base/hamt.jl",
    juliaFns := ["BitmapIndex(h::HashState)", "isset(trie::HAMT, bi::BitmapIndex)", "entry_index(trie::HAMT, bi::BitmapIndex)"],
    statement := "BitmapIndex selects the five hash bits at the current shift; isset tests exactly that bit, and entry_index maps a present bit to its one-based vector rank.",
    source := "HAMT bitmap/data invariant; base/hamt.jl:122,127,138-141", status := .todo, prop := ``HamtSlotRank, thm := none },
  { id := "dictscov-hamt-l158", juliaFile := "base/hamt.jl",
    juliaFns := ["path(trie::HAMT{K,V}, h::HashState, copy=false) where {K, V}", "insert!(found, present, trie::HAMT{K,V}, i, bi, h, val)"],
    statement := "For a valid HAMT with unique identity keys, after path(copy=true) and a later insertion into the copied path, the original root still returns its old finite map.",
    source := "path docstring and invariant; base/hamt.jl:147-186", status := .todo, prop := ``HamtPathCopyPreservesMap, thm := none },
  { id := "dictscov-hamt-l243", juliaFile := "base/hamt.jl",
    juliaFns := ["Base.length(::Leaf)", "Base.length(trie::HAMT)"],
    statement := "HAMT length is the total number of leaves across every child node, regardless of tree depth.",
    source := "HAMT invariant; base/hamt.jl:243", status := .todo, prop := ``HamtLengthCountsLeaves, thm := none },
  { id := "dictscov-hamt-l246", juliaFile := "base/hamt.jl",
    juliaFns := ["Base.isempty(::Leaf)", "Base.isempty(trie::HAMT)", "islevel_empty(trie::HAMT)", "islevel_empty(::Leaf)"],
    statement := "For a valid HAMT, isempty is true exactly when its map has no pairs; islevel_empty is bitmap == 0, and islevel_empty(::Leaf) is false.",
    source := "HAMT invariant; base/hamt.jl:246-251", status := .todo, prop := ``HamtEmptyExactlyNoLeaves, thm := none },
  { id := "dictscov-hamt-l254", juliaFile := "base/hamt.jl",
    juliaFns := ["Base.iterate(trie::HAMT, state=nothing)"],
    statement := "Iteration yields the finite map’s leaf pairs exactly once in depth-first vector order and resumes after each returned pair.",
    source := "HAMT invariant; base/hamt.jl:253-275", status := .todo, prop := ``HamtIterationExact, thm := none },
  { id := "hamt-insert-map-laws", juliaFile := "base/hamt.jl",
    juliaFns := ["path(trie::HAMT{K,V}, h::HashState, copy=false)", "insert!(found, present, trie::HAMT{K,V}, i, bi, h, val)"],
    statement := "For a valid HAMT with unique identity keys and identity/hash-consistent operations, successful insertion resolves the inserted value and leaves identity-distinct keys unchanged.",
    source := "path persistence docstring and insert! implementation; base/hamt.jl:146-240", status := .todo,
    prop := ``HamtInsertMapLaws, thm := none },
  { id := "hamt-copy-on-write-map", juliaFile := "base/hamt.jl",
    juliaFns := ["path(trie::HAMT{K,V}, h::HashState, copy=true)", "insert!(found, present, trie::HAMT{K,V}, i, bi, h, val)"],
    statement := "For a valid HAMT with unique identity keys, persistent insertion leaves the old map unchanged, gives the new root the supplied value, and preserves other keys.",
    source := "path persistence docstring; base/hamt.jl:146-186 and 188-240", status := .todo,
    prop := ``HamtCopyOnWritePreservesOld, thm := none },
  { id := "hamt-insert-bitmap-invariant", juliaFile := "base/hamt.jl",
    juliaFns := ["insert!(found, present, trie::HAMT{K,V}, i, bi, h, val)", "set!", "entry_index"],
    statement := "A successful insertion into a valid HAMT preserves bitmap population equal to the data-vector length at every reachable node.",
    source := "bitmap/data invariant comments at base/hamt.jl:128-135 and insert! at 192-240", status := .todo,
    prop := ``HamtInsertPreservesBitmapInvariant, thm := none },
  { id := "hamt-insert-replaces-existing", juliaFile := "base/hamt.jl",
    juliaFns := ["path", "insert!"],
    statement := "For a valid HAMT with unique identity keys, when path finds an existing identity key, insert! replaces its value with the supplied value.",
    source := "insert! replacement branch, base/hamt.jl:192-200", status := .todo,
    prop := ``HamtInsertReplacesExisting, thm := none },
  { id := "hamt-insert-collision-growth", juliaFile := "base/hamt.jl",
    juliaFns := ["path", "insert!"],
    statement := "For a valid HAMT with unique identity keys, when two unequal keys share hash chunks through a prefix and then diverge, collision growth retains both pairs.",
    source := "insert! collision-growth loop, base/hamt.jl:201-239", status := .todo,
    prop := ``HamtInsertCollisionGrowth, thm := none }
]

end JuliaLean.Proofs.base.hamt
